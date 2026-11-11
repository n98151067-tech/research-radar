"""ResearchRadar：追蹤期刊最新文章，依研究興趣用 AI 解析並推薦。

用法（詳見 README.md）：
    python radar.py                         # 跳出選單，選擇要跑的設定檔
    python radar.py --profile steam-ai      # 直接跑某一組設定檔
    python radar.py --all                   # 所有設定檔都跑
    python radar.py --days 30               # 往回抓 30 天
    python radar.py --group SSCI            # 只跑某一類期刊
    python radar.py --rescore steam-ai      # 設定檔改過後重新評分（論文解析不重做）
"""

from __future__ import annotations

import argparse
import atexit
import csv
import datetime as dt
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tomllib
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STATE_FILE = ROOT / "data" / "articles.json"
OUTPUT_DIR = ROOT / "output"
PROFILES_DIR = ROOT / "profiles"

USER_AGENT = "ResearchRadar/0.1 (personal journal alerts)"
FIRST_RUN_DAYS = 30  # 第一次執行往回抓的天數
LATER_RUN_DAYS = 14  # 之後每次執行檢查的天數（已處理過的文章會跳過）

METHOD_CATEGORIES = ["量化研究", "質性研究", "混合方法", "系統性回顧／後設分析", "設計本位研究", "系統開發與評估"]

# 非研究文章：更正、撤稿等，列入 CSV 但不分析也不評分
NON_RESEARCH = re.compile(
    r"^(correction|publisher correction|author correction|retraction|retraction note|retracted|"
    r"erratum|expression of concern|editorial|editor'?s note|withdrawal)\b", re.I)

NOTE_NO_ABSTRACT = "無摘要，僅依標題"
NOTE_NON_RESEARCH = "非研究文章"
NOTE_FAILED = "AI 分析失敗，下次執行會重試"

CSV_COLUMNS = ["星等", "推薦理由", "一句話重點", "標題", "作者", "發表日期", "期刊", "DOI", "連結", "方法類別",
               "研究目的", "研究方法", "主要結果", "研究亮點", "結論", "備註"]

ANALYSIS_SYSTEM = f"""你是一位論文理解專家，專門解析學術論文。
你會收到一篇期刊文章的標題、作者與摘要（有時只有標題）。請用繁體中文回答下列問題：
1. 研究目的
2. 研究方法
3. 主要結果
4. 研究亮點
5. 結論

另外標註方法類別：優先從以下固定類別中選一個：{"、".join(METHOD_CATEGORIES)}。
如果都不適合，請用簡短的文字自行描述（例如「準實驗研究」「個案研究」）。

最後寫「一句話重點」：用一句繁體中文（約 40–70 字）說明這篇文章做了什麼、發現什麼，讓讀者掃過去就能決定要不要細看。

規則：只根據提供的內容回答，不要編造摘要沒有提到的數據或細節。
如果只有標題，請根據標題合理推測，並在每個回答前加上「（依標題推測）」。
每個問題用 1–3 句回答，專有名詞可以保留英文。"""

ANALYSIS_SCHEMA = {
    "type": "object",
    "properties": {
        "method_category": {"type": "string"},
        "purpose": {"type": "string"},
        "method": {"type": "string"},
        "results": {"type": "string"},
        "highlights": {"type": "string"},
        "conclusion": {"type": "string"},
        "tldr": {"type": "string"},
    },
    "required": ["method_category", "purpose", "method", "results", "highlights", "conclusion", "tldr"],
}

# 補產生「一句話重點」：給 v0.1 已解析、還沒有這一項的文章
TLDR_SYSTEM = """你是一位論文理解專家，專門解析學術論文。
你會收到一篇期刊文章的標題、作者與摘要（有時只有標題）。
請用一句繁體中文（約 40–70 字）說明這篇文章做了什麼、發現什麼，讓讀者掃過去就能決定要不要細看。
只根據提供的內容回答，不要編造數據；如果只有標題，句首加上「（依標題推測）」。"""

TLDR_SCHEMA = {"type": "object", "properties": {"tldr": {"type": "string"}}, "required": ["tldr"]}

SCORING_SYSTEM = """你是一位研究助理，幫研究者判斷期刊新文章值不值得讀。
你會收到一或多組研究興趣設定檔，以及一篇文章的標題、作者與摘要（有時只有標題）。
請對每一組設定檔，依下列星等規則給 1–5 顆星，並用繁體中文寫 1–2 句推薦理由，說明這篇文章跟該研究興趣的關聯（或為什麼無關）。

星等規則：
5 = 必讀，跟研究直接相關
4 = 值得細讀
3 = 值得看摘要
2 = 有點相關，看標題就好
1 = 無關

關鍵字只是參考，請依研究內容的實質關聯判斷，不要只看字面是否相同。
大多數文章對特定研究興趣來說只是 1–2 顆星，請保守給分。"""


def scoring_schema(profile_ids: list[str]) -> dict:
    return {
        "type": "object",
        "properties": {"scores": {"type": "array", "items": {
            "type": "object",
            "properties": {
                "profile": {"type": "string", "enum": profile_ids},
                "stars": {"type": "integer", "minimum": 1, "maximum": 5},
                "reason": {"type": "string"},
            },
            "required": ["profile", "stars", "reason"],
        }}},
        "required": ["scores"],
    }


# ---------- 設定 ----------

def load_settings() -> dict:
    with open(ROOT / "settings.toml", "rb") as f:
        return tomllib.load(f)


def load_journals() -> list[dict]:
    with open(ROOT / "journals.toml", "rb") as f:
        return tomllib.load(f)["journal"]


def load_profiles() -> dict[str, dict]:
    profiles = {}
    for path in sorted(PROFILES_DIR.glob("*.toml")):
        with open(path, "rb") as f:
            p = tomllib.load(f)
        p["id"] = path.stem
        p.setdefault("groups", [])
        p.setdefault("keywords", [])
        profiles[p["id"]] = p
    return profiles


def applies(profile: dict, journal: dict) -> bool:
    """設定檔沒有指定期刊分類時套用所有期刊，有指定時只套用標籤相符的期刊。"""
    return not profile["groups"] or bool(set(profile["groups"]) & set(journal.get("tags", [])))


# ---------- 狀態檔 ----------

class State:
    """所有處理過的文章，以 DOI 為索引，存在 data/articles.json。"""

    def __init__(self):
        self.lock = threading.Lock()
        self.articles: dict[str, dict] = {}
        if STATE_FILE.exists():
            self.articles = json.loads(STATE_FILE.read_text(encoding="utf-8"))

    def save(self):
        with self.lock:
            STATE_FILE.parent.mkdir(exist_ok=True)
            tmp = STATE_FILE.with_suffix(".tmp")
            tmp.write_text(json.dumps(self.articles, ensure_ascii=False, indent=1), encoding="utf-8")
            tmp.replace(STATE_FILE)


# ---------- 抓資料 ----------

def http_get(url: str, attempts: int = 3) -> bytes:
    for attempt in range(1, attempts + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as resp:
                return resp.read()
        except (urllib.error.URLError, TimeoutError) as e:
            if attempt == attempts:
                raise
            print(f"  連線失敗（{e}），{5 * attempt} 秒後重試")
            time.sleep(5 * attempt)
    raise AssertionError


def fetch_springer(journal: dict, since: dt.date) -> list[dict]:
    """從 Springer RSS 抓 since 之後線上發表的文章（RSS 依日期由新到舊排列，一頁 20 篇）。"""
    found = []
    for page in range(1, 51):
        url = ("https://link.springer.com/search.rss?" +
               urllib.parse.urlencode({"facet-journal-id": journal["springer_id"],
                                       "sortOrder": "newestFirst", "page": page}))
        items = ET.fromstring(http_get(url)).findall("./channel/item")
        if not items:
            break
        oldest = None
        for item in items:
            date = dt.date.fromisoformat(item.findtext("pubDate", "").strip()[:10])
            oldest = date
            if date < since:
                continue
            desc = item.find("description")
            abstract = " ".join("".join(desc.itertext()).split()) if desc is not None else ""
            found.append({
                "doi": item.findtext("guid", "").strip().lower(),
                "title": " ".join(item.findtext("title", "").split()),
                "date": date.isoformat(),
                "abstract": abstract,
                "link": item.findtext("link", "").strip(),
                "journal": journal["id"],
                "journal_name": journal["name"],
            })
        if oldest and oldest < since:
            break
        time.sleep(1)
    return [a for a in found if a["doi"]]


def fetch_authors(doi: str) -> str:
    """從 Crossref 以 DOI 查作者；查不到時回傳空字串。"""
    try:
        data = json.loads(http_get("https://api.crossref.org/works/" + urllib.parse.quote(doi)))
    except Exception as e:
        print(f"  Crossref 查不到作者（{doi}：{e}）")
        return ""
    names = []
    for a in data["message"].get("author", []):
        name = " ".join(x for x in (a.get("given"), a.get("family")) if x) or a.get("name", "")
        if name:
            names.append(name)
    return "; ".join(names)


SOURCES = {"springer": fetch_springer}


# ---------- Claude ----------

def find_claude(settings: dict) -> str:
    """找到 claude 執行檔。Windows 上 npm 裝的是 claude.cmd，直接呼叫其中的 claude.exe，
    避免 cmd.exe 改動參數裡的引號。"""
    if settings.get("claude_path"):
        return settings["claude_path"]
    found = shutil.which("claude")
    if not found:
        sys.exit("找不到 claude 指令，請先安裝並登入 Claude Code。")
    exe = Path(found).parent / "node_modules" / "@anthropic-ai" / "claude-code" / "bin" / "claude.exe"
    return str(exe) if exe.exists() else found


class Claude:
    def __init__(self, settings: dict):
        self.exe = find_claude(settings)
        self.model = settings["model"]
        self.timeout = settings.get("timeout_seconds", 300)
        self.empty = tempfile.mkdtemp(prefix="researchradar-")  # 在空資料夾執行，不載入任何專案設定
        atexit.register(shutil.rmtree, self.empty, ignore_errors=True)
        # 拿掉 API 金鑰，讓 claude 使用登入帳號的訂閱額度
        self.env = {k: v for k, v in os.environ.items() if k not in ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN")}

    def ask(self, system: str, text: str, schema: dict) -> dict:
        command = [self.exe, "-p", "--model", self.model, "--tools", "", "--setting-sources", "",
                   "--no-session-persistence", "--system-prompt", system,
                   "--output-format", "json", "--json-schema", json.dumps(schema, ensure_ascii=False)]
        last = None
        for attempt in range(1, 3):
            run = subprocess.run(command, input=text, capture_output=True, text=True, encoding="utf-8",
                                 cwd=self.empty, env=self.env, timeout=self.timeout)
            try:
                out = json.loads(run.stdout) if run.stdout.strip() else {}
            except json.JSONDecodeError:
                out = {}
            if run.returncode == 0 and out.get("subtype") == "success" and out.get("structured_output"):
                return out["structured_output"]
            last = str(out.get("result") or run.stderr.strip() or f"exit {run.returncode}")[:300]
        raise RuntimeError(last)


def article_text(a: dict) -> str:
    text = f"標題：{a['title']}\n作者：{a.get('authors') or '（不明）'}\n期刊：{a['journal_name']}\n"
    return text + (f"摘要：{a['abstract']}" if a["abstract"] else "摘要：（無，只有標題）")


def profile_text(p: dict) -> str:
    return (f"<profile id=\"{p['id']}\">\n名稱：{p['name']}\n研究描述：{p['description'].strip()}\n"
            f"關鍵字：{', '.join(p['keywords'])}\n</profile>")


# ---------- 主流程 ----------

def make_rows(state: State, profile: dict, journals: dict[str, dict]) -> list[dict]:
    rows = []
    for a in state.articles.values():
        journal = journals.get(a["journal"])
        if journal is None or not applies(profile, journal):
            continue
        an = a.get("analysis") or {}
        sc = a.get("scores", {}).get(profile["id"]) or {}
        notes = []
        if a.get("non_research"):
            notes.append(NOTE_NON_RESEARCH)
        else:
            if not a["abstract"]:
                notes.append(NOTE_NO_ABSTRACT)
            if not an or not sc:
                notes.append(NOTE_FAILED)
        rows.append({
            "星等": sc.get("stars", ""), "推薦理由": sc.get("reason", ""), "一句話重點": an.get("tldr", ""),
            "標題": a["title"], "作者": a.get("authors", ""), "發表日期": a["date"],
            "期刊": a["journal_name"], "DOI": a["doi"], "連結": a["link"],
            "方法類別": an.get("method_category", ""), "研究目的": an.get("purpose", ""),
            "研究方法": an.get("method", ""), "主要結果": an.get("results", ""),
            "研究亮點": an.get("highlights", ""), "結論": an.get("conclusion", ""),
            "備註": "；".join(notes),
        })
    rows.sort(key=lambda r: (r["發表日期"], r["星等"] or 0), reverse=True)
    return rows


def write_csv(profile: dict, rows: list[dict]) -> Path:
    OUTPUT_DIR.mkdir(exist_ok=True)
    path = OUTPUT_DIR / f"{profile['id']}.csv"
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w", encoding="utf-8-sig", newline="") as f:  # 有 BOM，Excel 才不會亂碼
        writer = csv.DictWriter(f, fieldnames=CSV_COLUMNS)
        writer.writeheader()
        writer.writerows(rows)
    try:
        tmp.replace(path)
    except PermissionError:
        sys.exit(f"無法寫入 {path}：檔案可能正在 Excel 中開啟，請關閉後再執行一次。")
    return path


# ---------- HTML 閱讀報告 ----------

REPORT_CSS = """
:root { --bg:#f6f5f2; --card:#fff; --text:#1f2328; --muted:#636c76; --line:#e3e1dc; --accent:#1a5fb4;
  --s5:#b5470b; --s4:#c27c0e; --s3:#2b7a78; --s2:#8a8f96; --s1:#b4b8bd; --new:#1a7f37; --tldr:#f3efe6; }
@media (prefers-color-scheme: dark) { :root { --bg:#16181b; --card:#1f2227; --text:#e6e6e6; --muted:#9aa3ad;
  --line:#33373d; --accent:#6ea8fe; --s5:#ff8a4c; --s4:#f2b84b; --s3:#5cc8c2; --s2:#8a9099; --s1:#5d636b;
  --new:#3fb950; --tldr:#2a2b26; } }
* { box-sizing:border-box; }
body { margin:0; background:var(--bg); color:var(--text); line-height:1.7;
  font-family:"Microsoft JhengHei","PingFang TC","Noto Sans TC",system-ui,sans-serif; }
main { max-width:860px; margin:0 auto; padding:32px 16px 64px; }
header h1 { font-size:1.6rem; margin:0 0 4px; }
header .sub { color:var(--muted); font-size:.92rem; }
.stats { display:flex; flex-wrap:wrap; gap:8px; margin:16px 0 8px; }
.stats span { background:var(--card); border:1px solid var(--line); border-radius:999px; padding:2px 12px; font-size:.88rem; }
h2 { font-size:1.1rem; margin:36px 0 12px; padding-bottom:6px; border-bottom:2px solid var(--line); }
.card { background:var(--card); border:1px solid var(--line); border-left:5px solid var(--sc); border-radius:10px;
  padding:16px 20px; margin:0 0 14px; }
.card h3 { font-size:1.08rem; margin:0 0 6px; line-height:1.45; }
.card h3 a { color:var(--text); text-decoration:none; }
.card h3 a:hover { color:var(--accent); text-decoration:underline; }
.stars { color:var(--sc); font-size:1.1rem; letter-spacing:1px; }
.badge { display:inline-block; font-size:.75rem; font-weight:bold; color:#fff; background:var(--new);
  border-radius:4px; padding:0 6px; margin-left:8px; vertical-align:middle; }
.tldr { background:var(--tldr); border-radius:6px; padding:8px 12px; margin:10px 0 8px; font-weight:600; }
.reason { margin:0 0 8px; }
.reason b, .label { color:var(--muted); font-weight:normal; font-size:.88rem; }
.meta { color:var(--muted); font-size:.86rem; margin:4px 0 10px; }
.meta a { color:var(--accent); }
dl { margin:8px 0 0; }
dt { font-weight:bold; font-size:.92rem; margin-top:10px; }
dd { margin:2px 0 0; }
details { margin-top:10px; }
summary { cursor:pointer; color:var(--accent); font-size:.9rem; }
.abstract { font-size:.9rem; color:var(--muted); margin:8px 0 0; }
.low { --sc:var(--s2); }
.note { color:var(--muted); font-size:.86rem; }
ul.plain { padding-left:20px; }
"""

STAR_COLORS = {5: "var(--s5)", 4: "var(--s4)", 3: "var(--s3)", 2: "var(--s2)", 1: "var(--s1)"}


def write_report(profile: dict, articles: list[dict], new_dois: set[str], since: dt.date) -> Path:
    """一組設定檔一份 HTML 報告：依星等排序，3 星以上完整顯示，1–2 星的解析收起來。"""
    from html import escape as e

    def stars(n):
        return f'<span class="stars" title="{n} 顆星">{"★" * n}{"☆" * (5 - n)}</span>'

    def analysis_block(a):
        an = a.get("analysis") or {}
        parts = [("研究目的", "purpose"), ("研究方法", "method"), ("主要結果", "results"),
                 ("研究亮點", "highlights"), ("結論", "conclusion")]
        return "<dl>" + "".join(f"<dt>{label}</dt><dd>{e(an.get(k, ''))}</dd>" for label, k in parts) + "</dl>"

    def meta(a):
        an = a.get("analysis") or {}
        items = [e(a.get("authors") or "作者不明"), a["date"]]
        if an.get("method_category"):
            items.append(e(an["method_category"]))
        if not a["abstract"]:
            items.append(NOTE_NO_ABSTRACT)
        items.append(f'<a href="{e(a["link"])}" target="_blank" rel="noopener">原文連結</a>')
        return '<div class="meta">' + "　·　".join(items) + "</div>"

    def card(a):
        sc = a["scores"][profile["id"]]
        n = sc["stars"]
        an = a.get("analysis") or {}
        out = [f'<article class="card" style="--sc:{STAR_COLORS[n]}">',
               f'<h3><a href="{e(a["link"])}" target="_blank" rel="noopener">{e(a["title"])}</a></h3>',
               "<div>" + stars(n) + ('<span class="badge">新</span>' if a["doi"] in new_dois else "") + "</div>"]
        if an.get("tldr"):
            out.append(f'<div class="tldr">{e(an["tldr"])}</div>')
        out.append(f'<p class="reason"><b>推薦理由：</b>{e(sc["reason"])}</p>')
        if n >= 3:
            out += [meta(a), analysis_block(a)]
        else:
            out.append(f"<details><summary>完整解析</summary>{meta(a)}{analysis_block(a)}</details>")
        if a["abstract"]:
            out.append(f'<details><summary>英文原文摘要</summary><p class="abstract">{e(a["abstract"])}</p></details>')
        out.append("</article>")
        return "\n".join(out)

    scored = [a for a in articles if not a.get("non_research") and profile["id"] in a.get("scores", {})]
    scored.sort(key=lambda a: (a["scores"][profile["id"]]["stars"], a["date"]), reverse=True)
    pending = [a for a in articles if not a.get("non_research") and profile["id"] not in a.get("scores", {})]
    other = sorted((a for a in articles if a.get("non_research")), key=lambda a: a["date"], reverse=True)

    high = [a for a in scored if a["scores"][profile["id"]]["stars"] >= 3]
    low = [a for a in scored if a["scores"][profile["id"]]["stars"] < 3]
    today = dt.date.today()
    body = [f"<header><h1>{e(profile['name'])}</h1>",
            f'<div class="sub">ResearchRadar 閱讀報告　·　設定檔 {e(profile["id"])}　·　'
            f"收錄 {since} 至 {today} 線上發表的文章　·　產生於 {dt.datetime.now():%Y-%m-%d %H:%M}</div>",
            '<div class="stats">'
            f"<span>共 {len(articles)} 篇</span><span>本次新增 {sum(a['doi'] in new_dois for a in articles)} 篇</span>"
            f"<span>3 星以上 {len(high)} 篇</span><span>1–2 星 {len(low)} 篇</span></div>",
            f'<details><summary>研究描述</summary><p class="note">{e(profile["description"].strip())}</p>'
            f'<p class="note">關鍵字：{e(", ".join(profile["keywords"]))}</p></details></header>']
    body.append(f"<h2>值得閱讀（3 星以上，{len(high)} 篇）</h2>")
    body += [card(a) for a in high] or ['<p class="note">這段期間沒有 3 星以上的文章。</p>']
    body.append(f"<h2>其他文章（1–2 星，{len(low)} 篇）</h2>")
    body += [card(a) for a in low] or ['<p class="note">沒有。</p>']
    if pending:
        body.append(f"<h2>尚未評分（{len(pending)} 篇）</h2>")
        body.append('<p class="note">AI 分析失敗，下次執行會重試。</p><ul class="plain">' + "".join(
            f'<li><a href="{e(a["link"])}" target="_blank" rel="noopener">{e(a["title"])}</a>（{a["date"]}）</li>'
            for a in pending) + "</ul>")
    if other:
        body.append(f"<h2>非研究文章（{len(other)} 篇）</h2>")
        body.append('<ul class="plain">' + "".join(
            f'<li><a href="{e(a["link"])}" target="_blank" rel="noopener">{e(a["title"])}</a>（{a["date"]}）</li>'
            for a in other) + "</ul>")

    html = (f'<!doctype html>\n<html lang="zh-Hant"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width, initial-scale=1">'
            f"<title>{e(profile['name'])}｜{today}</title><style>{REPORT_CSS}</style></head>"
            f"<body><main>{''.join(body)}</main></body></html>\n")
    OUTPUT_DIR.mkdir(exist_ok=True)
    path = OUTPUT_DIR / f"{today}_{profile['id']}.html"
    path.write_text(html, encoding="utf-8")
    return path


def choose_profiles(profiles: dict[str, dict]) -> list[str]:
    """沒有指定設定檔時的編號選單。"""
    ids = list(profiles)
    print("請選擇要跑的設定檔（輸入編號，多組用逗號分隔，例如 1,3）：")
    for i, pid in enumerate(ids, 1):
        print(f"  {i}. {pid}　{profiles[pid]['name']}")
    while True:
        try:
            answer = input("> ")
        except EOFError:
            sys.exit("沒有選擇設定檔。非互動執行時請加 --profile <代號> 或 --all。")
        picks = [x.strip() for x in answer.replace("，", ",").split(",") if x.strip()]
        if picks and all(x.isdigit() and 1 <= int(x) <= len(ids) for x in picks):
            return [ids[int(x) - 1] for x in dict.fromkeys(picks)]
        print(f"請輸入 1–{len(ids)} 的編號。")


def main():
    for stream in (sys.stdout, sys.stderr):
        stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(description="ResearchRadar：期刊新文章 AI 推薦")
    ap.add_argument("--days", type=int, help=f"往回抓幾天（第一次預設 {FIRST_RUN_DAYS}，之後預設 {LATER_RUN_DAYS}）")
    ap.add_argument("--profile", action="append", help="只跑這組設定檔（可重複指定）；不指定時跳出選單")
    ap.add_argument("--all", action="store_true", help="所有設定檔都跑")
    ap.add_argument("--no-open", action="store_true", help="跑完不要自動打開報告")
    ap.add_argument("--group", action="append", help="只跑有這個標籤的期刊（可重複指定）")
    ap.add_argument("--rescore", metavar="PROFILE", action="append",
                    help="重新評分這組設定檔的所有文章（論文解析不重做），不抓新文章")
    args = ap.parse_args()

    settings = load_settings()
    journals = load_journals()
    profiles = load_profiles()
    state = State()

    for name in (args.profile or []) + (args.rescore or []):
        if name not in profiles:
            sys.exit(f"找不到設定檔 {name}，可用的有：{', '.join(profiles)}")
    if args.group:
        journals = [j for j in journals if set(args.group) & set(j.get("tags", []))]
        if not journals:
            sys.exit(f"沒有期刊帶有標籤 {', '.join(args.group)}")
    if args.rescore:
        chosen = args.rescore
    elif args.all:
        chosen = list(profiles)
    elif args.profile:
        chosen = args.profile
    else:
        chosen = choose_profiles(profiles)
    profiles = {k: v for k, v in profiles.items() if k in chosen}
    print(f"設定檔：{', '.join(profiles)}")
    journal_map = {j["id"]: j for j in journals}

    days = args.days or (LATER_RUN_DAYS if state.articles else FIRST_RUN_DAYS)
    since = dt.date.today() - dt.timedelta(days=days)
    new_dois: set[str] = set()

    # 1. 抓新文章
    if not args.rescore:
        for journal in journals:
            print(f"抓取 {journal['name']}（{since} 之後）")
            fetched = SOURCES[journal["source"]](journal, since)
            new = [a for a in fetched if a["doi"] not in state.articles]
            print(f"  找到 {len(fetched)} 篇，其中 {len(new)} 篇是新的")
            for a in new:
                a["authors"] = fetch_authors(a["doi"])
                a["non_research"] = bool(NON_RESEARCH.match(a["title"]))
                a["analysis"] = None
                a["scores"] = {}
                state.articles[a["doi"]] = a
                new_dois.add(a["doi"])
                time.sleep(0.2)
        state.save()

    # 2. 找出要交給 AI 的工作
    claude = Claude(settings)
    rescore = set(args.rescore or [])
    analyze, tldr, score = [], [], []
    for a in state.articles.values():
        journal = journal_map.get(a["journal"])
        if journal is None or a.get("non_research"):
            continue
        if not a.get("analysis") and not rescore:
            analyze.append(a)
        elif a.get("analysis") and not a["analysis"].get("tldr"):
            tldr.append(a)
        todo = [p for p in profiles.values() if applies(p, journal)
                and (p["id"] in rescore or p["id"] not in a.get("scores", {}))]
        if todo:
            score.append((a, todo))

    def do_analysis(a):
        a["analysis"] = claude.ask(ANALYSIS_SYSTEM, article_text(a), ANALYSIS_SCHEMA)

    def do_tldr(a):
        a["analysis"]["tldr"] = claude.ask(TLDR_SYSTEM, article_text(a), TLDR_SCHEMA)["tldr"]

    def do_scoring(a, todo):
        text = "\n\n".join(profile_text(p) for p in todo) + "\n\n<article>\n" + article_text(a) + "\n</article>"
        result = claude.ask(SCORING_SYSTEM, text, scoring_schema([p["id"] for p in todo]))
        for s in result["scores"]:
            a.setdefault("scores", {})[s["profile"]] = {"stars": s["stars"], "reason": s["reason"]}

    jobs = [("解析", a, lambda a=a: do_analysis(a)) for a in analyze]
    jobs += [("補一句話重點", a, lambda a=a: do_tldr(a)) for a in tldr]
    jobs += [("評分", a, lambda a=a, t=t: do_scoring(a, t)) for a, t in score]
    if jobs:
        print(f"AI 分析：{len(analyze)} 篇解析、{len(tldr)} 篇補一句話重點、{len(score)} 篇評分"
              f"（模型 {settings['model']}）")
        failed = 0
        with ThreadPoolExecutor(max_workers=settings.get("workers", 4)) as pool:
            futures = {pool.submit(fn): (kind, a) for kind, a, fn in jobs}
            for n, fut in enumerate(as_completed(futures), 1):
                kind, a = futures[fut]
                try:
                    fut.result()
                    print(f"  [{n}/{len(jobs)}] {kind}完成：{a['title'][:50]}")
                except Exception as e:
                    failed += 1
                    print(f"  [{n}/{len(jobs)}] {kind}失敗：{a['title'][:50]}（{e}）")
                state.save()
        if failed:
            print(f"有 {failed} 項失敗，下次執行會自動重試。")
    else:
        print("沒有需要 AI 處理的文章。")

    # 3. 輸出 CSV 與 HTML 報告
    all_journals = {j["id"]: j for j in load_journals()}  # CSV 收錄所有期刊，不受 --group 影響
    reports = []
    for profile in profiles.values():
        rows = make_rows(state, profile, all_journals)
        path = write_csv(profile, rows)
        print(f"輸出 {path.relative_to(ROOT)}：{len(rows)} 篇")
        # 報告收錄這次抓取區間內的文章
        in_range = [a for a in state.articles.values()
                    if a["journal"] in journal_map and applies(profile, journal_map[a["journal"]])
                    and a["date"] >= since.isoformat()]
        path = write_report(profile, in_range, new_dois, since)
        high = sum(1 for a in in_range if a.get("scores", {}).get(profile["id"], {}).get("stars", 0) >= 3)
        print(f"輸出 {path.relative_to(ROOT)}：{len(in_range)} 篇，3 星以上 {high} 篇")
        reports.append(path)
    if not args.no_open:
        for path in reports:
            webbrowser.open(path.as_uri())


if __name__ == "__main__":
    main()
