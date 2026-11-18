#!/usr/bin/env python3
"""SeeCode — термінальний чат у стилі Claude Code, але з оком замість маскота.

Запуск:
    python seecode.py

SeeCode збирає інформацію з кількох сайтів і складає власну відповідь. Ключі не потрібні.
Тільки стандартна бібліотека Python, нічого ставити не треба.
"""
import ast
import html as _html
import json
import math
import operator
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import urllib.parse
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from html.parser import HTMLParser

try:
    import readline  # noqa: F401  (історія та редагування рядка)
except ImportError:
    pass

VERSION = "0.1.0"

# ---------- кольори ----------
RESET = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"
ACCENT = (245, 245, 245)  # білий — тіло ока
WHITE = (0, 0, 0)         # чорний — око всередині
PUPIL = (245, 245, 245)   # біла зіниця (щоб було видно на чорному)


def fg(c):
    return f"\033[38;2;{c[0]};{c[1]};{c[2]}m"


def bg(c):
    return f"\033[48;2;{c[0]};{c[1]};{c[2]}m"


ACC = fg(ACCENT)

# ---------- піксельне око (11 x 8) ----------
# '#' — контур/тіло, 'w' — біле, 'p' — зіниця, '.' — порожньо
EYE = [
    "...#####...",
    ".#########.",
    "####www####",
    "###wwpww###",
    "###wwpww###",
    "####www####",
    ".#########.",
    "...#####...",
]
PALETTE = {"#": ACCENT, "w": WHITE, "p": PUPIL}


def render_eye():
    """Півблоки ▀: один рядок терміналу = два піксельні рядки."""
    lines = []
    for y in range(0, len(EYE), 2):
        top, bot = EYE[y], EYE[y + 1]
        line = ""
        for t, b in zip(top, bot):
            tc, bc = PALETTE.get(t), PALETTE.get(b)
            if tc and bc:
                line += fg(tc) + bg(bc) + "▀"
            elif tc:
                line += RESET + fg(tc) + "▀"
            elif bc:
                line += RESET + fg(bc) + "▄"
            else:
                line += RESET + " "
        lines.append(line + RESET)
    return lines


# ---------- малювання рамок ----------
def strip_ansi(s):
    out, i = "", 0
    while i < len(s):
        if s[i] == "\033":
            while i < len(s) and s[i] != "m":
                i += 1
            i += 1
        else:
            out += s[i]
            i += 1
    return out


def box(lines, width, color=ACC):
    top = color + "╭" + "─" * (width - 2) + "╮" + RESET
    bot = color + "╰" + "─" * (width - 2) + "╯" + RESET
    body = []
    for ln in lines:
        pad = width - 4 - len(strip_ansi(ln))
        body.append(color + "│" + RESET + " " + ln + " " * max(pad, 0) + " " + color + "│" + RESET)
    return "\n".join([top, *body, bot])


def welcome():
    eye = render_eye()
    # око зліва, текст справа по центру висоти ока
    content = {
        1: f"{ACC}✻{RESET} {BOLD}Welcome to SeeCode!{RESET}",
        2: f"  {DIM}/help for help, /status for your current setup{RESET}",
    }
    print()
    for i, e in enumerate(eye):
        print("  " + e + "  " + content.get(i, ""))
    print()


# ---------- спінер ----------
class Spinner:
    FRAMES = "✻✽✶✳✢·"
    WORDS = ["Seeing", "Looking", "Gazing", "Blinking", "Observing"]

    def __init__(self):
        self._stop = threading.Event()
        self._t = None

    def _run(self):
        i, start = 0, time.time()
        while not self._stop.is_set():
            f = self.FRAMES[i % len(self.FRAMES)]
            word = self.WORDS[(i // 8) % len(self.WORDS)]
            sec = int(time.time() - start)
            sys.stdout.write(f"\r{ACC}{f} {word}…{RESET} {DIM}({sec}s · esc to interrupt){RESET}\033[K")
            sys.stdout.flush()
            i += 1
            time.sleep(0.12)

    def __enter__(self):
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()
        return self

    def __exit__(self, *a):
        self._stop.set()
        self._t.join()
        sys.stdout.write("\r\033[K")
        sys.stdout.flush()


# ---------- бекенд: "розум" SeeCode ----------
# Збирає інформацію з кількох сайтів (Wikipedia + пошук DuckDuckGo і знайдені
# сторінки), відбирає найрелевантніші речення, прибирає повтори і складає
# з них власну коротку відповідь із переліком джерел.
UA = {"User-Agent": "Mozilla/5.0 (compatible; SeeCode/" + VERSION + ")"}
STOP = set("""
що таке це як чому де коли хто який яка яке які такий така таке такі
та і й або але в у на з із до по за про від для не ні чи ж б би
мені тобі нам вам мені скажи розкажи поясни поясніть дай знайди знаєш
можеш будь ласка означає значить такоє
the a an is are was were of to in and or what who how why when where does do
did tell me about explain please
""".split())
BAD_DOMAINS = ("duckduckgo.com", "facebook.com", "instagram.com", "tiktok.com",
               "youtube.com", "youtu.be", "twitter.com", "x.com", "pinterest.")


_HTTP_CACHE = {}          # url+limit -> (час, текст); повторні питання не б'ють мережу
_HTTP_TTL, _HTTP_MAX = 300, 64


def http_get(url, timeout=8, limit=600_000):
    key = (url, limit)
    hit = _HTTP_CACHE.get(key)
    if hit and time.time() - hit[0] < _HTTP_TTL:
        return hit[1]
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        raw = r.read(limit)
        charset = r.headers.get_content_charset() or "utf-8"
    text = raw.decode(charset, errors="replace")
    if len(_HTTP_CACHE) >= _HTTP_MAX:
        _HTTP_CACHE.pop(next(iter(_HTTP_CACHE)))
    _HTTP_CACHE[key] = (time.time(), text)
    return text


def stem(w):
    """Грубий корінь слова (щоб "око/ока/оком", "рогівка/рогівки" збігалися)."""
    w = w.lower()
    n = len(w)
    return w[:max(2, n - 1)] if n <= 4 else w[:min(n - 2, 7)]


def keywords(text):
    words = re.findall(r"[\w'’-]+", text.lower())
    return [w for w in words if w not in STOP and len(w) > 1]


def clean_text(s):
    s = re.sub(r"\[[^\]]{0,20}\]", "", s)      # [1], [edit] ...
    s = re.sub(r"\s+", " ", s).strip()
    return s


def split_sentences(text):
    parts = re.split(r"(?<=[.!?…])\s+(?=[A-ZА-ЯІЇЄҐ0-9\"«„])", text)
    return [p.strip() for p in parts if p.strip()]


def shorten(s, limit=280):
    if len(s) <= limit:
        return s
    cut = s[:limit]
    for sep in ("; ", ", ", " "):
        i = cut.rfind(sep)
        if i > limit * 0.5:
            return cut[:i].rstrip(",;:") + "…"
    return cut + "…"


def domain(url):
    d = urllib.parse.urlparse(url).netloc.lower()
    return d[4:] if d.startswith("www.") else d


class _Paras(HTMLParser):
    SKIP = {"script", "style", "nav", "footer", "header", "aside", "noscript", "form"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.paras, self._buf, self._in_p, self._skip = [], [], False, 0

    def _flush(self):
        if self._in_p:
            t = clean_text(" ".join(self._buf))
            if len(t) > 60:
                self.paras.append(t)
        self._buf, self._in_p = [], False

    def handle_starttag(self, tag, attrs):
        if tag in self.SKIP:
            self._skip += 1
        elif tag == "p" and not self._skip:
            self._flush()
            self._in_p = True

    def handle_endtag(self, tag):
        if tag in self.SKIP:
            self._skip = max(0, self._skip - 1)
        elif tag == "p":
            self._flush()

    def handle_data(self, data):
        if self._in_p and not self._skip:
            self._buf.append(data)


def page_paragraphs(url):
    try:
        p = _Paras()
        p.feed(http_get(url))
        p._flush()
        return p.paras[:40]
    except Exception:  # noqa: BLE001
        return []


def _wiki_api(lang, **params):
    params.update(action="query", format="json", redirects=1)
    url = f"https://{lang}.wikipedia.org/w/api.php?" + urllib.parse.urlencode(params)
    return json.loads(http_get(url)).get("query", {}).get("pages", {})


def _wiki_pages(pages, lang):
    out = []
    for p in pages.values():
        views = sum(v for v in (p.get("pageviews") or {}).values() if v)
        ext = clean_text(p.get("extract", ""))
        head = ext[:200]
        disamb = ("disambiguation" in (p.get("pageprops") or {})
                  or "може означати" in head or "may refer to" in head)
        if ext and not disamb:
            out.append({"title": p.get("title", ""), "url": p.get("fullurl", ""),
                        "views": views, "text": ext, "lang": lang})
    return out


def wiki_best(query, lang):
    """Обирає з Вікіпедії статтю, що найкраще відповідає запиту.
    Якщо слово багатозначне (око = орган / вежа / ...), перемагає найпопулярніша
    стаття з точною назвою. Повертає (url, [абзаци]) із довшим текстом статті."""
    common = dict(prop="extracts|info|pageviews|pageprops", exintro=1, explaintext=1,
                  inprop="url", pvipdays=30, ppprop="disambiguation")
    def fetch(**kw):
        try:
            return _wiki_pages(_wiki_api(lang, **common, **kw), lang)
        except Exception:  # noqa: BLE001
            return []

    with ThreadPoolExecutor(max_workers=2) as ex:      # точний збіг назви + пошук — одночасно
        f_exact = ex.submit(fetch, titles=query, exlimit=1)
        f_search = ex.submit(fetch, generator="search", gsrsearch=query, gsrlimit=6, exlimit=6)
        cands = f_exact.result() + f_search.result()
    seen, uniq = set(), []
    for c in cands:
        if c["url"] not in seen:
            seen.add(c["url"])
            uniq.append(c)
    if not uniq:
        return None
    q = query.lower().strip()

    def rank(ic):
        i, c = ic
        t = re.sub(r"\s*\(.*?\)", "", c["title"]).lower().strip()
        tr = 2 if t == q else (1 if t and (q in t or t in q) else 0)
        return (tr, c["views"] if tr == 2 else 0, -i)

    best = max(enumerate(uniq), key=rank)[1]
    paras = [best["text"]]
    try:
        pages = _wiki_api(lang, titles=best["title"], prop="extracts",
                          explaintext=1, exchars=6000)
        ext = next(iter(pages.values())).get("extract", "")
        long_paras = [clean_text(x) for x in ext.split("\n")
                      if len(x) > 60 and not x.lstrip().startswith("=")]
        if long_paras:
            paras = long_paras
    except Exception:  # noqa: BLE001
        pass
    return (best["url"], paras)


def web_links(query, n=5):
    try:
        page = http_get("https://html.duckduckgo.com/html/?q=" + urllib.parse.quote(query))
    except Exception:  # noqa: BLE001
        return []
    links = []
    for href in re.findall(r'class="result__a"[^>]*href="([^"]+)"', page):
        href = _html.unescape(href)
        m = re.search(r"uddg=([^&]+)", href)
        url = urllib.parse.unquote(m.group(1)) if m else href
        if url.startswith("//"):
            url = "https:" + url
        if not url.startswith("http") or any(b in domain(url) for b in BAD_DOMAINS):
            continue
        if domain(url) not in [domain(u) for u in links]:
            links.append(url)
        if len(links) >= n:
            break
    return links


def web_links_lite(query, n=5):
    """Запасний пошук (легка версія DuckDuckGo), якщо основна не відповіла."""
    try:
        page = http_get("https://lite.duckduckgo.com/lite/?q=" + urllib.parse.quote(query))
    except Exception:  # noqa: BLE001
        return []
    links = []
    for href in re.findall(r"<a[^>]*href=[\"']([^\"']+)[\"'][^>]*class=[\"']result-link", page):
        href = _html.unescape(href)
        m = re.search(r"uddg=([^&]+)", href)
        url = urllib.parse.unquote(m.group(1)) if m else href
        if url.startswith("//"):
            url = "https:" + url
        if url.startswith("http") and not any(b in domain(url) for b in BAD_DOMAINS):
            if domain(url) not in [domain(u) for u in links]:
                links.append(url)
        if len(links) >= n:
            break
    return links


def gather(query):
    """Повертає список джерел [(url, [абзаци])]: спершу найкраща стаття
    Вікіпедії, далі звичайні сайти з пошуку."""
    cyr = bool(re.search(r"[А-Яа-яІіЇїЄєҐґ]", query))
    langs = ["uk"] if cyr else ["en"]
    with ThreadPoolExecutor(max_workers=8) as ex:
        wiki_f = [ex.submit(wiki_best, query, lg) for lg in langs]
        links_f = ex.submit(web_links, query)
        sources = [w for w in (f.result() for f in wiki_f) if w]
        links = [u for u in links_f.result() if "wikipedia.org" not in u]
        if not links:
            links = [u for u in web_links_lite(query) if "wikipedia.org" not in u]
        page_f = [(u, ex.submit(page_paragraphs, u)) for u in links]
        for u, f in page_f:
            paras = f.result()
            if paras:
                sources.append((u, paras))
    return sources


def jaccard(a, b):
    a, b = set(a), set(b)
    return len(a & b) / len(a | b) if a and b else 0.0


def select_sentences(query, sources):
    """Відбирає факти (речення) з джерел.
    Головне джерело (стаття Вікіпедії) задає тему; речення з інших сайтів
    беруться лише якщо стосуються тієї ж теми."""
    kws = [stem(w) for w in keywords(query)]
    vocab = set()
    if sources:
        for sent in split_sentences(" ".join(sources[0][1][:3])):
            vocab |= {stem(w) for w in keywords(sent) if len(w) > 3}
        vocab -= set(kws)

    cands = []  # (score, source_idx, pos, sentence)
    for si, (url, paras) in enumerate(sources):
        pos = 0
        for para in paras:
            for sent in split_sentences(para):
                pos += 1
                if not (40 <= len(sent) <= 600) or sent.count("|") or "©" in sent:
                    continue
                words = re.findall(r"[\w'’-]+", sent.lower())
                hit = len({k for k in kws if any(w.startswith(k) for w in words)})
                if kws and hit == 0:
                    continue
                if si > 0 and len({stem(w) for w in words if len(w) > 3} & vocab) < 2:
                    continue  # не про ту саму тему, що головне джерело
                score = (hit / len(kws) if kws else 0.3) + max(0, 0.3 - pos * 0.03)
                if si == 0:
                    score += 0.1
                cands.append((score, si, pos, sent))
    cands.sort(key=lambda c: -c[0])

    chosen, per_src = [], {}
    for score, si, pos, sent in cands:
        if len(chosen) >= 6 or per_src.get(si, 0) >= 3:
            continue
        toks = keywords(sent)
        if any(jaccard(toks, keywords(c[3])) > 0.5 for c in chosen):
            continue
        chosen.append((score, si, pos, sent))
        per_src[si] = per_src.get(si, 0) + 1
    chosen.sort(key=lambda c: (c[1], c[2]))   # порядок: джерело → позиція в тексті
    return chosen


def used_domains(chosen, sources):
    used = []
    for c in chosen:
        d = domain(sources[c[1]][0])
        if d not in used:
            used.append(d)
    return used


def compose(query, sources, chosen=None):
    """Запасний варіант без генерації: склеює відібрані речення."""
    chosen = chosen if chosen is not None else select_sentences(query, sources)
    if not chosen:
        return None
    main, extra = chosen[:2], chosen[2:]
    lines = [" ".join(shorten(c[3]) for c in main)]
    if extra:
        lines.append("")
        lines.append(f"{DIM}Додатково:{RESET}")
        lines += [f"  – {shorten(c[3], 220)}" for c in extra]
    lines.append("")
    lines.append(f"{DIM}Джерела: {', '.join(used_domains(chosen, sources))}{RESET}")
    return "\n".join(lines)


LLM_URL = "https://text.pollinations.ai/openai"   # безкоштовно, без ключа
WRITER_PROMPT = (
    "Ти — SeeCode, асистент із пошуку. Користувач поставив питання, нижче — факти, "
    "зібрані з кількох сайтів. Напиши власну зв'язну відповідь 3–6 речень тією "
    "самою мовою, що й питання. Формулюй своїми словами: не копіюй речення з фактів "
    "дослівно, об'єднуй факти з різних джерел, прибирай повтори. Використовуй лише "
    "наведені факти, нічого не вигадуй. Якщо фактів недостатньо — так і скажи. "
    "Без вступів і без списку джерел."
)


def llm(messages, timeout=45):
    """Один виклик безкоштовної моделі (без ключа). Повертає текст."""
    body = json.dumps({"model": "openai", "messages": messages}).encode("utf-8")
    req = urllib.request.Request(LLM_URL, data=body,
                                 headers={**UA, "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        data = json.loads(r.read().decode("utf-8"))
    text = data["choices"][0]["message"]["content"].strip()
    # прибрати можливу рекламу сервісу
    text = "\n".join(l for l in text.splitlines() if "pollinations" not in l.lower()).strip()
    if len(text) < 2:
        raise ValueError("порожня відповідь")
    return text


def write_answer(query, chosen, extra=None):
    """Просить модель сформулювати відповідь на основі зібраних фактів."""
    facts = "\n".join(f"- {shorten(c[3], 400)}" for c in chosen)
    if extra:
        facts += "\n" + "\n".join(f"- (з бази Seecer, англ.) {e}" for e in extra)
    return llm([
        {"role": "system", "content": WRITER_PROMPT},
        {"role": "user", "content": f"Питання: {query}\n\nФакти:\n{facts}"},
    ])


# ---------- звичайна розмова ----------
CHAT_PROMPT = (
    "Ти — SeeCode, дружній співрозмовник із піксельним оком замість обличчя. "
    "Спілкуйся невимушено, коротко (1–4 речення), тією мовою, якою пише користувач. "
    "Не вигадуй фактів; якщо не знаєш — скажи прямо."
)
CHAT_RE = re.compile(
    r"^(привіт|привіт[а-яі]*|вітаю|хай|здоров[а-яі]*|добр[а-яі]+ (ранку|день|вечір)|"
    r"hello|hi|hey|ку|йо|"
    r"як (справи|ти|життя|настрій|діла)|як ся маєш|що (нового|робиш|твориш)|"
    r"хто ти|ти хто|як тебе (звати|звуть)|"
    r"дякую|дяк[а-яі]*|спасибі|thanks|thank you|"
    r"бувай|па-?па|до побачення|па|"
    r"ок|окей|добре|ясно|зрозуміло|круто|класно|супер|ладно|ну|так|ні|ага|лол|хах[а-яі]*)\b",
    re.IGNORECASE)
QUESTION_RE = re.compile(
    r"^(що|хто|де|коли|чому|навіщо|як|яким|яка|який|яке|які|скільки|куди|звідки|чи|"
    r"поясни|розкажи|знайди|опиши|порівняй|покажи|"
    r"what|who|where|when|why|how|which|explain|tell|find|describe)\b",
    re.IGNORECASE)


def wants_search(text):
    """Фактичне питання → шукаємо в інтернеті; решта → просто розмова."""
    t = text.strip()
    if CHAT_RE.match(t):
        return False
    if t.lower().startswith(("/search ", "/find ")):
        return True
    return bool(QUESTION_RE.match(t) or "?" in t) and len(keywords(t)) >= 1


CANNED = (
    (re.compile(r"^(привіт|вітаю|хай|здоров|hello|hi|hey|ку|йо)", re.I), "Привіт! Чим можу допомогти?"),
    (re.compile(r"^(дякую|дяк|спасибі|thanks)", re.I), "Будь ласка!"),
    (re.compile(r"^(бувай|па|до побачення)", re.I), "Бувай! 👁"),
)


def chat_reply(history):
    msgs = [{"role": "system", "content": CHAT_PROMPT}]
    for m in history[-12:]:
        msgs.append({"role": m["role"], "content": strip_ansi(m["content"])})
    try:
        return llm(msgs)
    except Exception:  # noqa: BLE001
        text = history[-1]["content"].strip()
        for rx, reply in CANNED:
            if rx.match(text):
                return reply
        return "Зараз не можу нормально відповісти (немає зв'язку з моделлю). Постав фактичне питання — я пошукаю в інтернеті."


# ---------- генерація коду у файл ----------
HERE = os.path.dirname(os.path.abspath(__file__))


def _pick_dir(name):
    """Папка поруч зі скриптом (або в домашній чи тимчасовій, якщо туди не можна писати)."""
    for base in (HERE, os.path.expanduser("~"), tempfile.gettempdir()):
        d = os.path.join(base, name)
        try:
            os.makedirs(d, exist_ok=True)
            probe = os.path.join(d, ".write_test")
            with open(probe, "w") as f:
                f.write("ok")
            os.remove(probe)
            return d
        except OSError:
            continue
    return os.getcwd()


class LazyDir(os.PathLike):
    """Шлях, який обирається і створюється лише при першому використанні."""

    def __init__(self, name):
        self.name, self._path = name, None

    def __fspath__(self):
        if self._path is None:
            self._path = _pick_dir(self.name)
        return self._path

    def __str__(self):
        return self._path or os.path.join(HERE, self.name)


FILES_DIR = LazyDir("seecode_files")
CODE_PROMPT = (
    "Ти — старший інженер-програміст (staff-рівня). Пиши код так, ніби його одразу випустять у продакшн.\n"
    "Вимоги до коду:\n"
    "- повний і робочий з першого запуску; жодних TODO, заглушок, `...` чи псевдокоду;\n"
    "- лише стандартна бібліотека, якщо користувач не просив інше;\n"
    "- чітка структура: константи, функції/класи з короткими docstring, точка входу `main()` і "
    "`if __name__ == \"__main__\":`;\n"
    "- обробка помилок і некоректного вводу, граничні випадки; без зайвого глобального стану;\n"
    "- зрозумілі імена, type hints (для Python), коментарі мовою користувача лише там, де логіка неочевидна;\n"
    "- зручність: для консольних програм — підказки, меню, зрозумілі повідомлення про помилки, "
    "коректний вихід по Ctrl+C; для ігор — керування, рахунок, перезапуск.\n"
    "Формат відповіді СУВОРО: перший рядок `FILENAME: <ім'я файлу з розширенням>`, далі ОДИН блок коду "
    "в ``` ```. Після блоку — не більше одного короткого речення."
)
CODE_INTENT_RE = re.compile(
    r"(напиши|створи|згенеруй|зроби|накодь|write|create|generate|make)\b.*"
    r"(код|скрипт|програм|файл|функці|клас|гру|бот|сайт|script|code|program|file|"
    r"function|class|game|bot|app)", re.IGNORECASE | re.DOTALL)
EXT_HINTS = (
    (re.compile(r"\.py\b", re.I), ".py"),
    (re.compile(r"\.js\b", re.I), ".js"),
    (re.compile(r"\.html?\b", re.I), ".html"),
    (re.compile(r"\.css\b", re.I), ".css"),
    (re.compile(r"\.java\b", re.I), ".java"),
    (re.compile(r"\.cpp\b", re.I), ".cpp"),
    (re.compile(r"\.bat\b", re.I), ".bat"),
)


def wants_code(text):
    t = text.strip().lower()
    return t.startswith(("/code ", "/file ")) or bool(CODE_INTENT_RE.search(text))


def pick_ext(text):
    """Завжди TXT; інше розширення — лише якщо користувач явно написав, напр. «.py»."""
    for rx, ext in EXT_HINTS:
        if rx.search(text):
            return ext
    return ".txt"


def safe_name(name, ext):
    name = os.path.basename(name.strip().strip("`'\""))
    name = re.sub(r"[^\w.\-]", "_", name)[:60] or "code"
    base = os.path.splitext(name)[0] or "code"
    name = base + ext
    path = os.path.join(FILES_DIR, name)
    n = 1
    while os.path.exists(path):          # не перезаписуємо існуючі файли
        path = os.path.join(FILES_DIR, f"{base}_{n}{ext}")
        n += 1
    return path


LAST_FILE = {"path": None}
CHAT_CODE_LINES = 120        # скільки рядків коду показувати прямо в чаті


def code_block(code, limit=CHAT_CODE_LINES):
    """Код прямо в чаті: з відступом і лінійкою ліворуч (легко виділити й скопіювати)."""
    lines = code.splitlines()
    shown = lines[:limit]
    out = [f"{DIM}│{RESET} {l}" for l in shown]
    if len(lines) > limit:
        out.append(f"{DIM}│ … ще {len(lines) - limit} рядків — напиши /show, щоб побачити весь код{RESET}")
    return "\n".join(out)


def file_card(path, n_lines):
    """«Вкладення» в чаті: назва, розмір, де лежить і що з ним можна зробити."""
    LAST_FILE["path"] = path
    cols = shutil.get_terminal_size((80, 24)).columns
    maxw = min(cols, 100) - 4
    shown = path if len(path) <= maxw else "…" + path[-(maxw - 1):]
    size = os.path.getsize(path)
    size_s = f"{size} Б" if size < 1024 else f"{size / 1024:.1f} КБ"
    rows = [f"{ACC}▤{RESET} {BOLD}{os.path.basename(path)}{RESET}",
            f"{DIM}{n_lines} рядків · {size_s}{RESET}",
            f"{DIM}{shown}{RESET}",
            f"{DIM}/open — відкрити файл · /folder — показати в папці · /show — весь код{RESET}"]
    w = min(cols - 1, max(len(strip_ansi(r)) for r in rows) + 4)
    return box(rows, w)


def open_path(path, select=False):
    """Відкриває файл (або показує його в папці) у системі користувача."""
    try:
        if os.name == "nt":
            if select:
                subprocess.Popen(["explorer", f"/select,{path}"])
            else:
                os.startfile(path)  # noqa: S606
        elif sys.platform == "darwin":
            subprocess.Popen(["open", "-R", path] if select else ["open", path])
        else:
            subprocess.Popen(["xdg-open", os.path.dirname(path) if select else path])
        return True
    except Exception:  # noqa: BLE001
        return False


def file_command(cmd):
    path = LAST_FILE["path"]
    if not path or not os.path.isfile(path):
        return "Ще немає створеного файлу. Попроси мене написати код, наприклад: «напиши код калькулятора»."
    if cmd == "/show":
        with open(path, encoding="utf-8", errors="replace") as f:
            code = f.read()
        return code_block(code, limit=10**9) + "\n\n" + file_card(path, len(code.splitlines()))
    ok = open_path(path, select=(cmd == "/folder"))
    return (f"Відкриваю: {path}" if ok else
            f"Не вдалося відкрити автоматично. Файл тут:\n{path}")


def generate_code_file(task, history):
    ext = pick_ext(task)
    if task.lower().startswith(("/code ", "/file ")):
        task = task.split(" ", 1)[1]
    try:
        spec = llm_retry([{"role": "system", "content": ARCHITECT_PROMPT},
                          {"role": "user", "content": task}], tries=2).strip()
    except Exception:  # noqa: BLE001
        spec = ""
    brief = f"Завдання: {task}\n\n" + (f"Технічний план (дотримуйся його):\n{spec}\n" if spec else "")
    msgs = [{"role": "system", "content": CODE_PROMPT + f" Розширення файлу: {ext}."},
            {"role": "user", "content": brief}]
    try:
        raw = llm_code(msgs)
    except Exception:  # noqa: BLE001
        return "Не вдалося згенерувати код — немає зв'язку з моделлю. Спробуй ще раз пізніше."
    m = re.search(r"FILENAME:\s*(\S+)", raw)
    fence = re.search(r"```[\w+#.-]*\n(.*?)(?:```|\Z)", raw, re.S)
    code = fence.group(1) if fence else re.sub(r"FILENAME:.*\n?", "", raw, count=1)
    code = code.strip("\n")
    note = raw[fence.end():].strip() if fence else ""
    if not code.strip():
        return "Модель не повернула код. Спробуй описати завдання докладніше."
    os.makedirs(FILES_DIR, exist_ok=True)
    path = safe_name(m.group(1) if m else "code", ext)
    with open(path, "w", encoding="utf-8") as f:
        f.write(code + "\n")
    lines = code.splitlines()
    out = f"Готово, ось твій скрипт:\n\n{code_block(code)}\n\n{file_card(path, len(lines))}"
    if note:
        out += f"\n\n{note}"
    return out


# ---------- рій SeeCode: 5 груп агентів ----------
# Генерують → шукають помилки → виправляють → тестують → перевіряють якість.
# У чаті видно кожного агента: ● зелений — працює, ● червоний — знайшов помилку,
# ● сірий — закінчив роботу, ● темний — ще чекає своєї черги.
WORKERS_PER_STAGE = int(os.environ.get("SEECODE_WORKERS", "20"))    # агентів у кожній групі
SWARM_PARALLEL = int(os.environ.get("SEECODE_PARALLEL", "10"))      # скільки одночасно звертаються до моделі
# (назва групи, кількість агентів; None = WORKERS_PER_STAGE)
STAGES = (
    ("Проєктують", 1),
    ("Генерують", None),
    ("Шукають помилки", None),
    ("Виправляють", None),
    ("Тестують", None),
    ("Доводять до ладу", None),
    ("Перевіряють якість", None),
    ("Полірують", 1),
)
S_PLAN, S_GEN, S_FIND, S_FIX, S_TEST, S_REPAIR, S_QA, S_POLISH = range(8)
QUEUED, RUNNING, FOUND, DONE, OK, SKIPPED = 0, 1, 2, 3, 4, 5
DOT_COLOR = {QUEUED: (70, 70, 70), RUNNING: (60, 200, 90), FOUND: (235, 64, 64),
             DONE: (140, 140, 140), OK: (80, 230, 130), SKIPPED: (90, 90, 90)}
DOT_CHAR = {OK: "✔", SKIPPED: "–"}

# код, який не можна запускати на комп'ютері користувача під час тестів
DANGEROUS_RE = re.compile(
    r"os\s*\.\s*(system|remove|rmdir|unlink|popen|rename|removedirs|kill|exec\w*|spawn\w*|environ)"
    r"|shutil|subprocess|socket|urllib|requests|http\.|ctypes|\beval\s*\(|\bexec\s*\("
    r"|__import__|importlib|\bopen\s*\(|pathlib|tempfile|sys\s*\.\s*exit|\binput\s*\(")

FIND_FOCUS = (
    "синтаксис, типи та імпорти",
    "логіку та граничні випадки",
    "обробку помилок і некоректного вводу",
    "безпеку та витоки ресурсів",
    "відповідність коду початковому завданню і плану",
)

ARCHITECT_PROMPT = (
    "Ти — архітектор ПЗ. Склади короткий технічний план для завдання користувача, мовою користувача, "
    "до 25 рядків, БЕЗ коду: 1) мета в одному реченні; 2) ключові вимоги (5–8 пунктів, "
    "включно з неочевидними, які користувач не згадав, але очікує); 3) структура коду: "
    "функції/класи та їх відповідальність; 4) граничні випадки й обробка помилок; "
    "5) як перевірити, що все працює."
)


def llm_retry(msgs, tries=3, timeout=90):
    last = None
    for k in range(tries):
        try:
            return llm(msgs, timeout=timeout)
        except Exception as e:  # noqa: BLE001
            last = e
            time.sleep(1.5 * (k + 1))
    raise last


def llm_code(msgs, timeout=120):
    """Відповідь із кодом; якщо модель обірвалась посеред блока коду — просить продовжити."""
    raw = llm_retry(msgs, timeout=timeout)
    for _ in range(3):
        if raw.count("```") % 2 == 0:
            break
        more = llm_retry(msgs + [
            {"role": "assistant", "content": raw},
            {"role": "user", "content": "Відповідь обірвалась. Продовжуй РІВНО з місця обриву: без повторів, "
                                        "без вступу, без нового заголовка. Заверши код і закрий блок ```."}],
            timeout=timeout)
        if more.lstrip().startswith("```"):             # модель знову відкрила блок — прибираємо
            more = more.lstrip().split("\n", 1)[1] if "\n" in more.lstrip() else ""
        # обрив на межі рядка → новий рядок; обрив посеред рядка → дописуємо впритул
        raw = (raw + more.lstrip("\n")) if raw.endswith("\n") else (raw + more)
    if raw.count("```") % 2 == 1:
        raw += "\n```"
    return raw


def parse_code_reply(raw):
    """(мова, код, ім'я файлу) з відповіді моделі."""
    name = re.search(r"FILENAME:\s*(\S+)", raw)
    fence = re.search(r"```([\w+#.-]*)\n(.*?)(?:```|\Z)", raw, re.S)
    if fence:
        return fence.group(1).lower(), fence.group(2).strip("\n"), name.group(1) if name else None
    code = re.sub(r"FILENAME:.*\n?", "", raw, count=1).strip("\n")
    return "", code, name.group(1) if name else None


def py_error(code):
    try:
        compile(code, "<script>", "exec")
        return None
    except SyntaxError as e:
        return f"SyntaxError: {e.msg} (рядок {e.lineno})"
    except Exception as e:  # noqa: BLE001
        return str(e)


def pick_median(codes, is_py):
    """Із кількох варіантів бере «середній» за довжиною серед робочих."""
    ok = [c for c in codes if c and c.strip()]
    if is_py:
        ok = [c for c in ok if not py_error(c)] or ok
    ok.sort(key=len)
    return ok[len(ok) // 2] if ok else None


def run_test_snippet(code, snippet, timeout=10):
    """Реально запускає перевірки (assert) проти коду в ізольованій тимчасовій папці."""
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "cut.py"), "w", encoding="utf-8") as f:
            f.write(code + "\n")
        with open(os.path.join(d, "t.py"), "w", encoding="utf-8") as f:
            f.write("import sys, os\nsys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))\n"
                    "from cut import *\n\n" + snippet + "\n")
        try:
            p = subprocess.run([sys.executable, "-I", "t.py"], cwd=d, capture_output=True,
                               text=True, timeout=timeout, stdin=subprocess.DEVNULL)
        except subprocess.TimeoutExpired:
            return False, "тест завис (>10с)"
        if p.returncode != 0:
            tail = [l for l in p.stderr.strip().splitlines() if l.strip()]
            return False, " | ".join(tail[-3:])[:300] or "помилка"
        return True, ""


class Swarm:
    def __init__(self, task, n):
        self.task, self.n = task, n
        self.state = [[QUEUED] * (c or n) for _, c in STAGES]
        self.failed = [0] * len(STAGES)        # скільки агентів не змогли зв'язатися з моделлю
        self.lock = threading.Lock()
        self.active = -1
        self.start = time.time()
        self.cancel = threading.Event()
        self.stop_draw = threading.Event()
        self.lines = 0

    # ----- малювання -----
    def render(self):
        with self.lock:
            rows = [list(r) for r in self.state]
        total = sum(len(r) for r in rows)
        out = [f"{ACC}✻{RESET} {BOLD}SeeCode Swarm{RESET} {DIM}· {total} агентів · "
               f"{int(time.time() - self.start)}s{RESET}", ""]
        for si, (label, _) in enumerate(STAGES):
            row = rows[si]
            dots = "".join(fg(DOT_COLOR[v]) + DOT_CHAR.get(v, "●") for v in row) + RESET
            finished = sum(1 for v in row if v in (FOUND, DONE, OK, SKIPPED))
            errs = sum(1 for v in row if v == FOUND)
            mark = f"{ACC}▸{RESET}" if si == self.active else " "
            extra = f" {fg(DOT_COLOR[FOUND])}!{errs}{RESET}" if errs else ""
            out.append(f"{mark} {label:<19} {dots} {DIM}{finished}/{len(row)}{RESET}{extra}")
        legend = (f"{fg(DOT_COLOR[RUNNING])}●{RESET}{DIM} працює   "
                  f"{fg(DOT_COLOR[FOUND])}●{RESET}{DIM} знайшов помилку   "
                  f"{fg(DOT_COLOR[DONE])}●{RESET}{DIM} завершив   "
                  f"{fg(DOT_COLOR[OK])}✔{RESET}{DIM} усе гаразд   "
                  f"{fg(DOT_COLOR[QUEUED])}●{RESET}{DIM} чекає{RESET}")
        return out + ["", legend]

    def draw(self):
        lines = self.render()
        buf = f"\033[{self.lines}A" if self.lines else ""
        buf += "".join("\r" + l + "\033[K\n" for l in lines)
        sys.stdout.write(buf)
        sys.stdout.flush()
        self.lines = len(lines)

    def _draw_loop(self):
        while not self.stop_draw.is_set():
            self.draw()
            time.sleep(0.15)

    # ----- виконання групи -----
    def run_stage(self, si, job):
        """job(i) -> (результат, чи_знайдено_проблему). Повертає список результатів."""
        self.active = si
        count = len(self.state[si])
        results = [None] * count

        def worker(i):
            if self.cancel.is_set():
                return
            with self.lock:
                self.state[si][i] = RUNNING
            try:
                res, bad = job(i)
                results[i] = res
                val = FOUND if bad else DONE
            except Exception:  # noqa: BLE001
                val = FOUND
                with self.lock:
                    self.failed[si] += 1
            with self.lock:
                self.state[si][i] = val

        with ThreadPoolExecutor(max_workers=SWARM_PARALLEL) as ex:
            list(ex.map(worker, range(count)))
        return results

    def finalize(self):
        """Усе готово: чисті агенти світяться зеленою галочкою, червоні лишаються червоними."""
        with self.lock:
            for row in self.state:
                for i, v in enumerate(row):
                    if v == DONE:
                        row[i] = OK

    def skip_stage(self, si):
        self.active = si
        with self.lock:
            self.state[si] = [SKIPPED] * len(self.state[si])

    # ----- сам конвеєр -----
    def run(self):
        task, n = self.task, self.n
        ext = pick_ext(task)
        pyhint = bool(re.search(r"python|пайтон|\.py\b", task, re.I))
        report = []

        # 0. проєктують: технічний план
        def plan(i):
            return llm_retry([{"role": "system", "content": ARCHITECT_PROMPT},
                              {"role": "user", "content": task}]).strip(), False

        spec = (self.run_stage(S_PLAN, plan)[0] or "")
        if spec:
            report.append("складено технічний план")
        brief = f"Завдання: {task}\n\n" + (f"Технічний план (дотримуйся його):\n{spec}\n" if spec else "")

        # 1. генерують
        def gen(i):
            msgs = [{"role": "system", "content": CODE_PROMPT + f" Розширення файлу: {ext}. "
                     f"Ти варіант №{i + 1} з {n}: зроби рішення повним, акуратним і робочим."},
                    {"role": "user", "content": brief}]
            lang, code, fname = parse_code_reply(llm_code(msgs))
            return (lang, code, fname), not code.strip()

        cands = [c for c in self.run_stage(S_GEN, gen) if c and c[1].strip()]
        if not cands:
            return None, "Жоден агент не зміг згенерувати код — немає зв'язку з моделлю."
        langs = Counter(c[0] for c in cands if c[0])
        lang = langs.most_common(1)[0][0] if langs else ""
        is_py = lang in ("python", "py", "python3") or pyhint
        fname = Counter(c[2] for c in cands if c[2]).most_common(1)
        fname = fname[0][0] if fname else "code"
        code = pick_median([c[1] for c in cands], is_py)

        # 2. шукають помилки
        def find(i):
            err = py_error(code) if is_py else None
            msgs = [{"role": "system", "content":
                     "Ти — суворий ревʼюер коду. Знайди РЕАЛЬНІ помилки, що ламають роботу або "
                     "дають неправильний результат, і невиконані вимоги з плану. Відповідь: або одне слово "
                     "OK, або до 5 рядків формату `BUG: <де і що не так>`. Нічого зайвого."},
                    {"role": "user", "content": f"{brief}\nЗвертай увагу на: "
                     f"{FIND_FOCUS[i % len(FIND_FOCUS)]}.\n"
                     + (f"Компілятор: {err}\n" if err else "") + f"\nКод:\n{code}"}]
            bugs = re.findall(r"^\s*BUG:\s*(.+)$", llm_retry(msgs), re.M)
            return bugs, bool(bugs)

        raw_bugs = [b for r in self.run_stage(S_FIND, find) if r for b in r]
        err = py_error(code) if is_py else None
        if err:
            raw_bugs.insert(0, err)
        bugs, seen = [], set()
        for b in raw_bugs:
            key = re.sub(r"\W+", "", b.lower())[:50]
            if key not in seen:
                seen.add(key)
                bugs.append(b.strip())
        bugs = bugs[:12]

        # 3. виправляють
        if bugs:
            listing = "\n".join(f"- {b}" for b in bugs)

            def fix(i):
                msgs = [{"role": "system", "content": CODE_PROMPT},
                        {"role": "user", "content": f"{brief}\nВиправ код. Знайдені помилки:\n{listing}\n\n"
                         f"Поверни ПОВНИЙ виправлений код в одному блоці ```, нічого не скорочуй.\n\nКод:\n{code}"}]
                _, fixed, _ = parse_code_reply(llm_code(msgs))
                bad = (not fixed.strip()) or bool(is_py and py_error(fixed))
                return fixed, bad

            fixed = [c for c in self.run_stage(S_FIX, fix) if c]
            code = pick_median(fixed, is_py) or code
        else:
            self.skip_stage(S_FIX)
        report.insert(0, f"знайдено помилок: {len(bugs)}" + (" — виправлено" if bugs else ""))

        # 4. тестують
        runnable = is_py and not py_error(code) and not DANGEROUS_RE.search(code)
        snip_results = []     # (код_тесту, пройшов, повідомлення)

        def test(i):
            if runnable:
                msgs = [{"role": "system", "content":
                         "Ти — тестувальник Python. Код доступний як модуль `cut` і вже імпортований "
                         "(`from cut import *`). Напиши 3–6 перевірок на assert для його функцій. "
                         "Без input, файлів, мережі та нескінченних циклів. Лише код у блоці ```. "
                         "Якщо функцій для перевірки немає — відповідай NOTESTABLE."},
                        {"role": "user", "content": f"{brief}\nКод:\n{code}"}]
                raw = llm_retry(msgs)
                if "NOTESTABLE" in raw:
                    return "skip", False
                _, snippet, _ = parse_code_reply(raw)
                if not snippet.strip() or DANGEROUS_RE.search(snippet) or py_error(snippet):
                    return "skip", False
                ok, msg = run_test_snippet(code, snippet)
                with self.lock:
                    snip_results.append((snippet, ok, msg))
                return ("pass", False) if ok else (f"fail[run]: {msg}", True)
            msgs = [{"role": "system", "content":
                     "Ти — тестувальник. Подумки виконай код на 2–3 різних вхідних наборах і "
                     "відповідай ОДНИМ рядком: `PASS` або `FAIL: <причина>`."},
                    {"role": "user", "content": f"{brief}\nКод:\n{code}"}]
            ans = llm_retry(msgs).strip()
            if ans.upper().startswith("FAIL"):
                return "fail: " + ans[4:].lstrip(": ").strip(), True
            return "pass (мислено)", False

        tests = [t for t in self.run_stage(S_TEST, test) if t]
        t_skip = sum(1 for t in tests if t == "skip")
        run_fails = [t for t in tests if t.startswith("fail[run]")]
        mental_fails = [t for t in tests if t.startswith("fail:")]

        # 5. доводять до ладу: ремонт за РЕАЛЬНИМИ помилками запуску
        repaired = None
        if run_fails and snip_results:
            bad_sn = [s for s in snip_results if not s[1]][:3]
            good_sn = [s for s in snip_results if s[1]][:2]
            verify = bad_sn + good_sn
            errors = "\n".join(f"- {m}" for _, _, m in bad_sn)
            tests_text = "\n\n".join(s for s, _, _ in bad_sn)

            def repair(i):
                msgs = [{"role": "system", "content": CODE_PROMPT},
                        {"role": "user", "content": f"{brief}\nКод падає на перевірках. Реальні помилки "
                         f"запуску:\n{errors}\n\nПеревірки, які мають пройти:\n{tests_text}\n\n"
                         f"Знайди причину й виправ КОД (а не тести). Поверни ПОВНИЙ код у блоці ```.\n\n"
                         f"Код:\n{code}"}]
                _, cand, _ = parse_code_reply(llm_code(msgs))
                if not cand.strip() or py_error(cand) or DANGEROUS_RE.search(cand):
                    return (cand, False), True
                passed = all(run_test_snippet(cand, sn)[0] for sn, _, _ in verify)
                return (cand, passed), not passed

            results = [r for r in self.run_stage(S_REPAIR, repair) if r]
            good = [c for c, ok in results if ok]
            if good:
                repaired = pick_median(good, True)
                code = repaired
        else:
            self.skip_stage(S_REPAIR)

        # підсумок тестів — по остаточному коду
        if runnable and snip_results:
            final_ok = sum(1 for sn, _, _ in snip_results if run_test_snippet(code, sn)[0])
            summary = f"тести (реальний запуск): {final_ok} з {len(snip_results)} пройшли"
            if repaired:
                summary += " — після автоматичного ремонту"
        else:
            summary = ("тести: код перевірено «подумки» (його не можна безпечно запускати)"
                       if tests else "тести: не виконувались")
        if mental_fails:
            summary += f"; {len(mental_fails)} агентів сумніваються"
        report.append(summary)

        # 6. перевіряють якість
        def qa(i):
            msgs = [{"role": "system", "content":
                     "Ти — контролер якості коду. Оціни код за шкалою 1–10 (коректність, повнота "
                     "щодо завдання і плану, читабельність, обробка помилок). Відповідь двома рядками: "
                     "`SCORE: <число>` і `NOTE: <одне речення — головне КОНКРЕТНЕ зауваження, що саме "
                     "змінити>`."},
                    {"role": "user", "content": f"{brief}\nРезультати тестів: {summary}\n\nКод:\n{code}"}]
            raw = llm_retry(msgs)
            m = re.search(r"SCORE:\s*(\d+(?:[.,]\d+)?)", raw)
            note = re.search(r"NOTE:\s*(.+)", raw)
            if not m:
                raise ValueError("без оцінки")
            score = float(m.group(1).replace(",", "."))
            return (score, note.group(1).strip() if note else ""), score < 7

        scores = [q for q in self.run_stage(S_QA, qa) if q]
        avg = sum(s for s, _ in scores) / len(scores) if scores else 0
        notes = []
        for s, nt in sorted(scores, key=lambda x: x[0]):
            if nt and nt not in notes and s < 9:
                notes.append(nt)

        # 7. полірують: застосовують зауваження, але лише якщо нічого не зламано
        polished = False
        if notes:
            todo = "\n".join(f"- {x}" for x in notes[:5])

            def polish(i):
                msgs = [{"role": "system", "content": CODE_PROMPT},
                        {"role": "user", "content": f"{brief}\nПокращ код за зауваженнями контролерів якості:\n"
                         f"{todo}\n\nНічого не ламай і не скорочуй функціонал. Поверни ПОВНИЙ код у блоці ```.\n\n"
                         f"Код:\n{code}"}]
                _, cand, _ = parse_code_reply(llm_code(msgs))
                ok = bool(cand.strip()) and 0.6 * len(code) <= len(cand) <= 2.5 * len(code)
                if ok and is_py:
                    ok = not py_error(cand)
                if ok and runnable and not DANGEROUS_RE.search(cand):
                    ok = all(run_test_snippet(cand, sn)[0] for sn, _, _ in snip_results[:4])
                elif ok and runnable:
                    ok = False
                return cand if ok else None, not ok

            res = self.run_stage(S_POLISH, polish)[0]
            if res:
                code, polished = res, True
        else:
            self.skip_stage(S_POLISH)
        self.active = -1

        report.append(f"якість: {avg:.1f}/10" if scores else "якість: не оцінено")
        if polished:
            report.append("застосовано зауваження контролерів якості")
        elif notes:
            report.append("зауваження контролерів не застосовано (поліровка ламала тести)")
        unreachable = sum(self.failed)
        if unreachable:
            report.append(f"{unreachable} агентів не змогли зв'язатися з моделлю")
        return (code, fname, ext), {"report": report, "notes": [] if polished else notes[:3],
                                    "tests_failed": [] if (repaired or not run_fails) else run_fails}


def swarm_build(task):
    """Запускає рій і малює його в чаті. Повертає (результат, звіт); результат None — помилка (звіт = текст)."""
    sw = Swarm(task, WORKERS_PER_STAGE)
    drawer = threading.Thread(target=sw._draw_loop, daemon=True)
    drawer.start()
    try:
        result, info = sw.run()
        if result is not None:
            sw.finalize()
    except KeyboardInterrupt:
        sw.cancel.set()
        result, info = None, "Перервано."
    except Exception as e:  # noqa: BLE001
        result, info = None, f"Помилка рою: {e}"
    finally:
        sw.stop_draw.set()
        drawer.join()
        sw.draw()
    print()
    return result, info


def run_swarm(task):
    """Запускає рій і зберігає готовий скрипт файлом."""
    if task.lower().startswith("/swarm "):
        task = task.split(" ", 1)[1]
    result, info = swarm_build(task)
    if result is None:
        return info
    code, fname, ext = result
    try:
        os.makedirs(FILES_DIR, exist_ok=True)
        path = safe_name(fname, ext)
        with open(path, "w", encoding="utf-8") as f:
            f.write(code.rstrip("\n") + "\n")
    except OSError as e:
        return f"Скрипт готовий, але не вдалося зберегти файл ({e}). Ось код:\n\n{code}"
    lines = code.splitlines()
    out = ["Готово, ось твій скрипт:", "", code_block(code), "",
           f"{DIM}Звіт рою:{RESET}"] + [f"  {DIM}– {r}{RESET}" for r in info["report"]]
    if info["tests_failed"]:
        out.append(f"  {fg(DOT_COLOR[FOUND])}! частина тестів упала — перевір скрипт вручну{RESET}")
    for nt in info["notes"]:
        out.append(f"  {DIM}· зауваження: {nt}{RESET}")
    out += ["", file_card(path, len(lines))]
    return "\n".join(out)


def wants_swarm(text):
    t = text.strip().lower()
    if t.startswith("/swarm "):
        return True
    return (not t.startswith(("/code ", "/file "))) and bool(CODE_INTENT_RE.search(text))


# ---------- математика: база знань Seecer-DataBase + точний калькулятор ----------
# База (5 текстових файлів) тільки ЧИТАЄТЬСЯ як текст і ніколи не виконується.
DATA_DIR = LazyDir("seecode_data")
MATH_FILES = (
    "010101_math_knowledge.txt",
    "100101_math_knowledge.txt",
    "110101_math_knowledge.txt",
    "1000101_math_knowledge.txt",
    "1010101_math_knowledge.txt",
)
MATH_MIRRORS = (
    "https://raw.githubusercontent.com/dagamestl228-spec/Seecer-DataBase/refs/heads/main/{f}",
    "https://github.com/dagamestl228-spec/Seecer-DataBase/raw/main/{f}",
    "https://cdn.jsdelivr.net/gh/dagamestl228-spec/Seecer-DataBase@main/{f}",
)
MATH = {"loaded": False, "concepts": [], "ex": [], "files": 0, "tried": 0.0}
_math_lock = threading.Lock()
EX_PREFIXES = ("Example", "Problem", "Dataset", "Derivative example", "Integral example",
               "Limit example", "Probability example")


# ----- завантаження бази -----
def _read_local(name):
    for d in (DATA_DIR, HERE):
        path = os.path.join(d, name)
        if os.path.isfile(path):
            try:
                with open(path, encoding="utf-8", errors="replace") as f:
                    text = f.read()
                if "CONCEPT:" in text[:300000]:
                    return text
            except OSError:
                pass
    return None


def _download(name):
    last = None
    for tpl in MATH_MIRRORS:
        try:
            req = urllib.request.Request(tpl.format(f=name), headers={"User-Agent": "Mozilla/5.0 SeeCode/" + VERSION})
            chunks = []
            with urllib.request.urlopen(req, timeout=40) as r:
                while True:
                    b = r.read(262144)
                    if not b:
                        break
                    chunks.append(b)
            text = b"".join(chunks).decode("utf-8", errors="replace")
            if len(text) < 1000 or "CONCEPT:" not in text[:300000]:
                raise ValueError("файл має неочікуваний вигляд")
            try:
                tmp = os.path.join(DATA_DIR, name + ".part")
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(text)
                os.replace(tmp, os.path.join(DATA_DIR, name))
            except OSError:
                pass
            return text
        except Exception as e:  # noqa: BLE001
            last = e
    return None


def get_math_file(name):
    return _read_local(name) or _download(name)


def parse_math(text, concepts, examples, seen):
    topic, cur = "", None
    for ln in text.splitlines():
        s = ln.strip()
        if not s:
            continue
        if s.startswith("TOPIC:"):
            topic = s[6:].strip()
        elif s.startswith("CONCEPT:"):
            cur = [s[8:].strip(), "", topic]
        elif s.startswith("EXPLANATION:") and cur is not None:
            cur[1] = s[12:].strip()
            key = (cur[0], cur[1])
            if key not in seen:
                seen.add(key)
                concepts.append(cur)
            cur = None
        elif s.startswith(EX_PREFIXES):
            examples.append(s)


def ensure_math_loaded(verbose=False):
    """Завантажує й розбирає базу один раз. Повторна спроба — не частіше, ніж раз на 2 хвилини."""
    with _math_lock:
        if MATH["loaded"] or time.time() - MATH["tried"] < 120:
            return MATH["loaded"]
        MATH["tried"] = time.time()
        done = [0]
        texts = {}

        def job(name):
            texts[name] = get_math_file(name)
            done[0] += 1

        if verbose:
            sys.stdout.write(f"\r{DIM}  Готую математичну базу… 0/{len(MATH_FILES)}{RESET}\033[K")
            sys.stdout.flush()
        threads = [threading.Thread(target=job, args=(n,), daemon=True) for n in MATH_FILES]
        for t in threads:
            t.start()
        while any(t.is_alive() for t in threads):
            if verbose:
                sys.stdout.write(f"\r{DIM}  Готую математичну базу… {done[0]}/{len(MATH_FILES)}{RESET}\033[K")
                sys.stdout.flush()
            time.sleep(0.1)
        concepts, examples, seen = [], [], set()
        for name in MATH_FILES:
            if texts.get(name):
                parse_math(texts[name], concepts, examples, seen)
                MATH["files"] += 1
        texts.clear()
        if concepts or examples:
            MATH.update(concepts=concepts, ex=examples, loaded=True)
        if verbose:
            msg = (f"математична база: файлів {MATH['files']}/{len(MATH_FILES)}, понять {len(concepts)}, "
                   f"прикладів {len(examples)}" if MATH["loaded"]
                   else "математична база недоступна — рахую без неї")
            sys.stdout.write(f"\r{DIM}  {msg}{RESET}\033[K\n")
            sys.stdout.flush()
        return MATH["loaded"]


# ----- пошук у базі -----
UA_EN = (
    (r"прост", "prime"), (r"дріб|дроб", "fraction"), (r"відсот|процент", "percent"),
    (r"натуральн", "natural"), (r"\bціл", "integer"), (r"ірраціональн", "irrational"),
    (r"(?<!ір)раціональн", "rational"), (r"дільн|подільн", "divisib"),
    (r"нсд|найбільший спільний", "gcd greatest common"), (r"нск|найменше спільне", "lcm least common"),
    (r"розв['’ʼ]яж|\bsolve\b", "solve"), (r"змінн", "variable"), (r"рівнянн", "equation"), (r"квадратн", "quadratic"),
    (r"функці", "function"), (r"логарифм", "logarithm"), (r"степін|степен", "exponent power"),
    (r"корін|корен", "root"), (r"нерівност", "inequalit"), (r"похідн", "derivative"),
    (r"інтеграл", "integral"), (r"границ|ліміт", "limit"), (r"вектор", "vector"),
    (r"матриц", "matrix"), (r"трикутник", "triangle"), (r"прямокутник", "rectangle"),
    (r"\bкруг|\bколо|кола\b", "circle"), (r"площ", "area"), (r"периметр", "perimeter"),
    (r"об['’ʼ]єм", "volume"), (r"піфагор", "pythagorean"), (r"\bкут", "angle"),
    (r"середн", "mean average"), (r"медіан", "median"), (r"\bмод[аиуі]\b", "mode"),
    (r"дисперс", "variance"), (r"стандартн", "standard deviation"), (r"ймовірн", "probability"),
    (r"статистик", "statistics"), (r"розмах", "range"), (r"додав|плюс|сума|складан", "addition"),
    (r"множенн|помнож", "multiplication"), (r"віднімання|різниц", "subtraction"),
    (r"діленн|ділити", "division"), (r"послідовн", "sequence"), (r"ряд\b|ряди", "series"),
    (r"комбінатор|перестанов", "combinatorics permutation"), (r"факторіал", "factorial"),
    (r"тригонометр|синус|косинус|тангенс", "trigonometry sine cosine tangent"),
    (r"десятков", "decimal"), (r"\bчисл", "number"),
)
EN_STOP = {"the", "what", "how", "why", "are", "was", "does", "for", "and", "with", "from",
           "this", "that", "find", "solve", "calculate", "compute", "tell", "about", "explain"}


def kb_terms(q):
    t = q.lower()
    terms = []
    for pat, eng in UA_EN:
        if re.search(pat, t):
            terms += eng.split()
    terms += [w for w in re.findall(r"[a-z]{3,}", t) if w not in EN_STOP and w not in ("sqrt",)]
    seen, out = set(), []
    for w in terms:
        if w not in seen:
            seen.add(w)
            out.append(w)
    return out


def kb_lookup(q):
    """(концепти, приклади) з бази, найближчі до питання."""
    terms = kb_terms(q)
    concepts, examples = [], []
    if terms:
        scored = []
        for name, expl, topic in MATH["concepts"]:
            nl, el = name.lower(), expl.lower()
            sc = sum(3 if t in nl else (1 if t in el else 0) for t in terms)
            if sc >= 2:
                scored.append((sc, name, expl))
        scored.sort(key=lambda x: -x[0])
        concepts = [(n, e) for _, n, e in scored[:3]]

    q_low = q.lower().replace(",", ".")
    nums = re.findall(r"(?<![\w.])\d+(?:\.\d+)?", q_low)
    pows = re.findall(r"x\s*\^\s*\d+", q_low)
    must = [p.replace(" ", "") for p in pows] + nums[:3]
    kinds = [t for t in terms if t in ("derivative", "integral", "limit", "probability", "area", "perimeter",
                                       "equation", "mean", "median", "mode", "range", "addition", "subtraction",
                                       "multiplication", "division", "quadratic", "dataset", "solve")]
    if kinds:
        hits = []
        kind = kinds[0]
        kind_cap = kind.capitalize()          # «Derivative example», «Solve …» — без копії в нижньому регістрі
        for i, line in enumerate(MATH["ex"]):
            if all(m in line for m in must) and (kind in line or kind_cap in line):
                hits.append(i)
                if len(hits) >= 4000:
                    break
        ranked = []
        for i in hits:
            low = MATH["ex"][i].lower()
            sc = sum(1 for t in terms if t in low)
            for pw in pows:
                pw = pw.replace(" ", "")
                if re.search(re.escape(pw) + r"(?!\d)", low):
                    sc += 3
                if re.search(r"(?:=|of)\s*" + re.escape(pw) + r"(?!\d)", low):
                    sc += 2
            for n in nums:   # число як окремий токен
                if re.search(r"(?<![\d.])" + re.escape(n) + r"(?![\d])", low):
                    sc += 2
            ranked.append((sc, -len(low), i))
        ranked.sort(reverse=True)
        examples = [MATH["ex"][i] for _, _, i in ranked[:3]]
    return concepts, examples


# ----- безпечний калькулятор -----
_BIN = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
        ast.Div: operator.truediv, ast.FloorDiv: operator.floordiv, ast.Mod: operator.mod,
        ast.Pow: operator.pow}
_FUNCS = {"sqrt": math.sqrt, "abs": abs, "sin": math.sin, "cos": math.cos, "tan": math.tan,
          "log": math.log10, "ln": math.log}
_CONST = {"pi": math.pi, "e": math.e}


def safe_eval(expr, x=None):
    if len(expr) > 200:
        raise ValueError("вираз задовгий")
    tree = ast.parse(expr.strip(), mode="eval")

    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and type(n.value) in (int, float):
            return n.value
        if isinstance(n, ast.Name):
            if n.id == "x" and x is not None:
                return x
            if n.id in _CONST:
                return _CONST[n.id]
            raise ValueError("невідома змінна")
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.UAdd, ast.USub)):
            v = ev(n.operand)
            return v if isinstance(n.op, ast.UAdd) else -v
        if isinstance(n, ast.BinOp) and type(n.op) in _BIN:
            a, b = ev(n.left), ev(n.right)
            if isinstance(n.op, ast.Pow):
                if abs(b) > 1000:
                    raise ValueError("завеликий степінь")
                if isinstance(a, int) and isinstance(b, int) and b > 0 and a.bit_length() * b > 20000:
                    raise ValueError("завелике число")
            return _BIN[type(n.op)](a, b)
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in _FUNCS
                and len(n.args) == 1 and not n.keywords):
            return _FUNCS[n.func.id](ev(n.args[0]))
        raise ValueError("недозволений вираз")

    return ev(tree)


def fmt_num(v):
    if isinstance(v, complex):
        return str(v)
    if isinstance(v, float):
        if v != v or v in (float("inf"), float("-inf")):
            return str(v)
        if v.is_integer() and abs(v) < 1e15:
            return str(int(v))
        return f"{v:.10g}"
    return str(v)


_WORD_OPS = (
    (r"(\d+(?:\.\d+)?)\s*%\s*(?:від|of)\s*(\d+(?:\.\d+)?)", r"(\1/100*\2)"),
    (r"(?:корінь квадратний з|квадратний корінь з|корінь з|корінь із|square root of)\s*(\d+(?:\.\d+)?)", r"sqrt(\1)"),
    (r"√\s*\(", "sqrt("), (r"√\s*(\d+(?:\.\d+)?)", r"sqrt(\1)"),
    (r"\bплюс\b|\bplus\b", "+"), (r"\bмінус\b|\bminus\b", "-"),
    (r"помножити на|помножене на|множити на|\btimes\b|multiplied by", "*"),
    (r"поділити на|поділене на|розділити на|ділене на|divided by", "/"),
    (r"в степені|у степені|до степеня|to the power of", "**"),
    (r"в квадраті|squared", "**2"), (r"в кубі|cubed", "**3"),
    (r"\^", "**"), (r"[×·]", "*"), (r"÷", "/"),
)
_EXPR_RE = re.compile(r"(?:\d+(?:\.\d+)?|\bsqrt\b|\babs\b|\bsin\b|\bcos\b|\btan\b|\blog\b|\bln\b|\bpi\b|\*\*|[+\-*/%()]|\s)+")
_DATE_RE = re.compile(r"\d{1,4}-\d{1,2}-\d{1,4}")


def normalize_math(q):
    t = q.lower()
    t = re.sub(r"(?<=\d),(?=\d)", ".", t)
    for pat, rep in _WORD_OPS:
        t = re.sub(pat, rep, t)
    return t


def find_expression(q):
    t = normalize_math(q)
    best = None
    for m in _EXPR_RE.finditer(t):
        c = m.group().strip()
        c = c.strip("+*/% \t").rstrip("-").strip()
        if not c or not re.search(r"\d", c) or _DATE_RE.search(c):
            continue
        if not re.search(r"\*\*|[+\-*/%]|sqrt|abs|sin|cos|tan|log|ln", c):
            continue
        try:
            ast.parse(c, mode="eval")
        except SyntaxError:
            continue
        if best is None or len(c) > len(best):
            best = c
    return best


def solve_equation(q):
    t = normalize_math(q)
    if t.count("=") != 1 or "x" not in t:
        return None
    left, right = t.split("=")
    run = re.compile(r"(?:\d+(?:\.\d+)?|x|\*\*|[+\-*/()]|\s)+")
    ls = [m.group().strip() for m in run.finditer(left) if m.group().strip()]
    rs = [m.group().strip() for m in run.finditer(right) if m.group().strip()]
    if not ls or not rs:
        return None
    L, R = ls[-1], rs[0]

    def prep(s):
        s = re.sub(r"(\d|\))\s*x", r"\1*x", s)
        return re.sub(r"x\s*(\d|\()", r"x*\1", s)

    L, R = prep(L), prep(R)
    try:
        f = lambda v: safe_eval(L, v) - safe_eval(R, v)   # noqa: E731
        f0, f1, fm, f2, f3 = f(0), f(1), f(-1), f(2), f(3)
    except Exception:  # noqa: BLE001
        return None
    a = (f1 - 2 * f0 + fm) / 2
    b = (f1 - fm) / 2
    c = f0
    tol = 1e-9 * (1 + abs(f0) + abs(f3))
    if abs(f2 - (4 * a + 2 * b + c)) > tol or abs(f3 - (9 * a + 3 * b + c)) > tol:
        return None   # не поліном степеня ≤ 2
    head = f"Рівняння: {L} = {R}".replace("**", "^")
    if abs(a) < 1e-12:
        if abs(b) < 1e-12:
            return head + ("\nРозв'язок: будь-яке x" if abs(c) < 1e-12 else "\nРозв'язків немає")
        return head + f"\nРозв'язок: x = {fmt_num(-c / b)}"
    d = b * b - 4 * a * c
    steps = f"{head}\nПриведене до вигляду ax²+bx+c=0: a={fmt_num(a)}, b={fmt_num(b)}, c={fmt_num(c)}, D={fmt_num(d)}"
    if d > 1e-12:
        r1, r2 = (-b - math.sqrt(d)) / (2 * a), (-b + math.sqrt(d)) / (2 * a)
        return steps + f"\nРозв'язок: x₁ = {fmt_num(min(r1, r2))}, x₂ = {fmt_num(max(r1, r2))}"
    if abs(d) <= 1e-12:
        return steps + f"\nРозв'язок: x = {fmt_num(-b / (2 * a))}"
    return steps + "\nДійсних коренів немає (D < 0)"


def special_math(q):
    t = q.lower().replace(",", ".")
    nums = [float(x) for x in re.findall(r"(?<![\w.])-?\d+(?:\.\d+)?", t)]
    ints = [int(n) for n in nums if n == int(n)]
    if re.search(r"нсд|найбільший спільний|gcd", t) and len(ints) >= 2:
        return f"НСД({', '.join(map(str, ints))}) = {math.gcd(*ints)}"
    if re.search(r"нск|найменше спільне|lcm", t) and len(ints) >= 2:
        return f"НСК({', '.join(map(str, ints))}) = {math.lcm(*ints)}"
    m = re.search(r"(\d+)\s*!", t) or re.search(r"факторіал\w*\s*(?:числа\s*)?(\d+)", t)
    if m and int(m.group(1)) <= 500:
        n = int(m.group(1))
        v = str(math.factorial(n))
        return f"{n}! = {v if len(v) <= 60 else v[:30] + '…(' + str(len(v)) + ' цифр)'}"
    if re.search(r"прост\w+\s+(?:чи\w*\s+)?(?:число|ли)|чи\s+(?:є\s+)?(?:число\s+)?\d+\s+прост|is\s+\d+\s+prime|"
                 r"чи\s+просте", t) and ints and 1 < ints[0] < 10**12:
        n = ints[0]
        div = next((d for d in range(2, int(math.isqrt(n)) + 1) if n % d == 0), None)
        return f"{n} — просте число" if div is None else f"{n} — не просте число (ділиться на {div})"
    if re.search(r"середн|медіан|розмах|\bмод[аиуі]\b|\bmean\b|\bmedian\b|\bmode\b", t) and len(nums) >= 2:
        import statistics
        parts = [f"дані: {', '.join(fmt_num(n) for n in nums)}",
                 f"середнє = {fmt_num(statistics.mean(nums))}",
                 f"медіана = {fmt_num(statistics.median(nums))}",
                 f"розмах = {fmt_num(max(nums) - min(nums))}"]
        modes = statistics.multimode(nums)
        if len(modes) < len(set(nums)):
            parts.append("мода = " + ", ".join(fmt_num(m) for m in modes))
        return "; ".join(parts)
    return None


def _strip_outer(e):
    if e.startswith("(") and e.endswith(")"):
        depth = 0
        for i, ch in enumerate(e):
            depth += ch == "("
            depth -= ch == ")"
            if depth == 0 and i < len(e) - 1:
                return e
        return e[1:-1]
    return e


def compute_math(q):
    """Точний результат, обчислений програмою (не моделлю). None — якщо нічого рахувати."""
    for fn in (special_math, solve_equation):
        try:
            r = fn(q)
        except Exception:  # noqa: BLE001
            r = None
        if r:
            return r
    expr = find_expression(q)
    if expr:
        try:
            val = safe_eval(expr)
            return f"{_strip_outer(expr).replace('**', '^')} = {fmt_num(val)}"
        except ZeroDivisionError:
            return f"{expr.replace('**', '^')} — ділення на нуль"
        except Exception:  # noqa: BLE001
            return None
    return None


MATH_WORDS = re.compile(
    r"обчисли|порахуй|пораху\w+|скільки буде|скільки дорівнює|розв['’ʼ]яж\w*|рівнянн|похідн|інтеграл|"
    r"границ[яіюе]|ліміт|площа\s+(?:прямокутн|трикутн|круга|кола|квадрата)|периметр|"
    r"середнє\s+(?:арифметичне|значення)|середнє\s+[\d(-]|медіан|дисперс|ймовірність|прості числа|просте число|"
    r"чи\s+(?:є\s+)?(?:число\s+)?\d+\s+прост|дріб|відсотк|процент|нсд|нск|найбільший спільний|"
    r"квадратн\w+\s+рівнянн|теорема піфагора|піфагор|факторіал|логарифм|"
    r"\b(?:derivative|integral|solve|calculate|compute|probability|prime|fraction|equation|median)\b",
    re.IGNORECASE)


def wants_math(text):
    t = text.strip()
    if t.lower().startswith("/math "):
        return True
    if MATH_WORDS.search(t):
        return True
    if len(t) <= 150 and not t.startswith("/"):
        expr = find_expression(t)
        if expr and len(re.findall(r"\d+(?:\.\d+)?", expr)) >= 2:
            return True
    return False


MATH_PROMPT = (
    "Ти — SeeCode, математичний помічник. Відповідай мовою питання, коротко й покроково "
    "(3–8 речень), формули пиши простим текстом (степінь — ^). Рядок «Обчислено програмою» — "
    "точний результат: використовуй його без змін і не перераховуй інакше. «Довідка з бази» — "
    "англійські матеріали: перекажи їх своїми словами, не копіюй. Якщо бази недостатньо — "
    "відповідай із загальних знань, але не вигадуй чисел."
)


def math_answer(query, history):
    q = query[6:].strip() if query.lower().startswith("/math ") else query
    computed = compute_math(q)
    concepts, examples = kb_lookup(q) if MATH["loaded"] else ([], [])
    ref = [f"- {n}: {e}" for n, e in concepts] + [f"- {ex}" for ex in examples]
    user = f"Питання: {q}\n"
    if computed:
        user += f"\nОбчислено програмою:\n{computed}\n"
    if ref:
        user += "\nДовідка з бази:\n" + "\n".join(ref) + "\n"
    try:
        text = llm([{"role": "system", "content": MATH_PROMPT}, {"role": "user", "content": user}])
        if computed and computed.split("=")[-1].strip() not in text and "\n" not in computed:
            text += f"\n\n{computed}"
        src = f"\n\n{DIM}Джерела: Seecer-DataBase (математика) + точний розрахунок{RESET}" if ref else ""
        return text + src
    except Exception:  # noqa: BLE001
        out = []
        if computed:
            out.append(computed)
        if ref:
            out.append(f"{DIM}З бази знань (англ.):{RESET}")
            out += [f"  {r}" for r in ref]
        if not out:
            return "Не зміг порахувати це без зв'язку з моделлю. Спробуй записати як вираз, напр. 12*(3+4)."
        return "\n".join(out)


# ---------- інші предмети з Seecer-DataBase ----------
# Файли великі (по ~25 МБ) і здебільшого складаються з шаблонних «карток».
# Тому їх читають ПОТОКОМ: беруться лише унікальні твердження («Core concept» /
# «CONCEPT»+«EXPLANATION»), а читання зупиняється, коли нове перестає зʼявлятися.
# Результат кешується в seecode_data/subject_<назва>.json — повторно не качається.
SUBJECTS = {
    "biology": {
        "label": "біологія",
        "files": [f"BIOLOGY_part_0{i}.txt" for i in range(1, 6)],
        "rx": r"біолог|клітин|днк|рнк|геном|організм|еволюці|екосистем|фотосинтез|генетик|біосфер|"
              r"мітоз|мейоз|ферментів|бактері|вірус|хромосом|\bbiology\b|\bcell\b|\bdna\b",
    },
    "chemistry": {
        "label": "хімія",
        "files": ["CHEMISTRY_part_01.txt", "CHEMISTRY_part_02-1.txt", "CHEMISTRY_part_03.txt",
                  "CHEMISTRY_part_04.txt", "CHEMISTRY_part_05.txt"],
        "rx": r"хімі|атом\w*|молекул|хімічн|кислот|оксид|періодичн\w+ (?:таблиц|систем)|валентн|"
              r"ізотоп|розчин|\bchemistry\b|\batom\b|\bmolecule\b",
    },
    "physics": {
        "label": "фізика",
        "files": [f"PHYSICS_part_0{i}.txt" for i in range(1, 6)],
        "rx": r"фізик|ньютон|гравітац|кінематик|термодинам|електричн|електромагніт|імпульс|"
              r"прискоренн|\bphysics\b|\bnewton\b|\bvelocity\b",
    },
    "languages": {
        "label": "іноземні мови та лінгвістика",
        "files": [f"FOREIGN_LANGUAGES_AND_LINGUISTICS_part_0{i}.txt" for i in range(1, 6)],
        "rx": r"іноземн\w+ мов|англійськ|німецьк|французьк|іспанськ|лінгвіст|фонетик|граматик|"
              r"\blinguistics\b|\bgrammar\b|\bphonetics\b",
    },
    "programming": {
        "label": "програмування",
        "files": [f"PROGRAMMING_part_0{i}.txt" for i in range(1, 6)],
        "rx": r"програмув|алгоритм|структур\w+ даних|\bpython\b|пайтон|javascript|\bcss\b|\bhtml\b|\bsql\b|"
              r"\bgit\b|\bapi\b|linux|\bооп\b|компілятор|кібербезпек|багатопоточ|машинн\w+ навчанн|"
              r"\bprogramming\b|\balgorithm\b",
    },
    "ukrainian": {
        "label": "українська мова та література",
        "files": [f"UKRAINIAN_LANGUAGE_AND_LITERATURE_part_0{i}.txt" for i in range(1, 6)],
        "rx": r"українськ\w+ (?:мов|літератур)|літератур|правопис|орфограф|синтаксис|морфологі|"
              r"фразеолог|стилістик|шевченк|франко|леся українка|орфоепі",
    },
}
SUBJ_STATE = {k: {"loaded": False, "facts": [], "topics": [], "read": 0, "tried": 0.0} for k in SUBJECTS}
SUBJ_MAX_BYTES = 40_000_000      # стеля на один предмет, якщо контент справді різноманітний
SUBJ_STALE_BYTES = 2_000_000     # скільки читати без нових тверджень, перш ніж зупинитись
_subj_lock = threading.Lock()


def detect_subject(text):
    t = text.lower()
    for key, info in SUBJECTS.items():
        if re.search(info["rx"], t):
            return key
    return None


class CardParser:
    """Потоковий розбір: вирізає унікальні Core concept / CONCEPT+EXPLANATION."""

    def __init__(self, facts, topics):
        self.facts, self.topics = facts, topics
        self.topic, self.concept = "", None

    def feed(self, text):
        added = 0
        for ln in text.splitlines():
            s = ln.strip()
            if s.startswith("Topic:"):
                self.topic = s[6:].strip()
                if self.topic and self.topic not in self.topics:
                    self.topics.append(self.topic)
            elif s.startswith(("Core concept:", "Core explanation:")):
                f = s.split(":", 1)[1].strip()
                if s.startswith("Core explanation:") and self.topic:   # тут пояснення відповідає темі
                    f = f"{self.topic}: {f}"
                if f and f not in self.facts:
                    self.facts.append(f)
                    added += 1
            elif s.startswith("CONCEPT:"):
                self.concept = s[8:].strip()
            elif s.startswith("EXPLANATION:") and self.concept:
                f = f"{self.concept}: {s[12:].strip()}"
                self.concept = None
                if f not in self.facts:
                    self.facts.append(f)
                    added += 1
        return added


def _stream_file(name, parser, progress=None):
    """Читає файл потоком. Повертає (нових_тверджень, прочитано_байт, насичено) або None, якщо жодне дзеркало не відповіло."""
    last = None
    for tpl in MATH_MIRRORS:
        read, new, since_new, buf, saturated = 0, 0, 0, b"", False
        try:
            req = urllib.request.Request(tpl.format(f=name), headers={"User-Agent": "Mozilla/5.0 SeeCode/" + VERSION})
            with urllib.request.urlopen(req, timeout=40) as r:
                while True:
                    chunk = r.read(262144)
                    if not chunk:
                        break
                    read += len(chunk)
                    buf += chunk
                    nl = buf.rfind(b"\n")
                    if nl < 0:
                        continue
                    text, buf = buf[:nl].decode("utf-8", errors="replace"), buf[nl + 1:]
                    added = parser.feed(text)
                    new += added
                    since_new = 0 if added else since_new + len(chunk)
                    if progress:
                        progress(read)
                    if since_new > SUBJ_STALE_BYTES or read > SUBJ_MAX_BYTES:
                        saturated = True
                        break
            if read == 0:
                raise ValueError("порожня відповідь")
            return new, read, saturated
        except Exception as e:  # noqa: BLE001
            last = e
    return None


def _subj_cache_path(key):
    return os.path.join(DATA_DIR, f"subject_{key}.json")


def ensure_subject_loaded(key, verbose=False):
    st = SUBJ_STATE[key]
    with _subj_lock:
        if st["loaded"] or time.time() - st["tried"] < 120:
            return st["loaded"]
        st["tried"] = time.time()
        label = SUBJECTS[key]["label"]
        try:                                   # кеш із попереднього запуску
            with open(_subj_cache_path(key), encoding="utf-8") as f:
                data = json.load(f)
            st.update(facts=data["facts"], topics=data["topics"], read=data.get("read", 0), loaded=True)
            return True
        except (OSError, ValueError, KeyError):
            pass
        facts, topics = [], []
        parser = CardParser(facts, topics)
        total, parts_ok = 0, 0
        files = SUBJECTS[key]["files"]
        for i, name in enumerate(files, 1):
            def prog(read, i=i):
                if verbose:
                    sys.stdout.write(f"\r{DIM}  Готую базу «{label}»… частина {i}/{len(files)}, "
                                     f"{(total + read) / 1e6:.1f} МБ, унікальних тверджень: {len(facts)}{RESET}\033[K")
                    sys.stdout.flush()
            res = _stream_file(name, parser, prog)
            if res is None:
                if parts_ok == 0 and i == 1:
                    continue          # перша частина не відкрилась — пробуємо наступну
                break
            new, read, saturated = res
            total += read
            parts_ok += 1
            if new == 0 or saturated:  # нове перестало зʼявлятися → решта частин — повтори
                break
        if parts_ok:
            st.update(facts=facts, topics=topics, read=total, loaded=True)
            try:
                tmp = _subj_cache_path(key) + ".part"
                with open(tmp, "w", encoding="utf-8") as f:
                    json.dump({"facts": facts, "topics": topics, "read": total}, f, ensure_ascii=False)
                os.replace(tmp, _subj_cache_path(key))
            except OSError:
                pass
        if verbose:
            if st["loaded"]:
                msg = (f"база «{label}»: прочитано {total / 1e6:.1f} МБ, унікальних тверджень: {len(facts)} "
                       f"(решта файлів — повтори, тому не качав)")
            else:
                msg = f"база «{label}» недоступна — відповідаю без неї"
            sys.stdout.write(f"\r{DIM}  {msg}{RESET}\033[K\n")
            sys.stdout.flush()
        return st["loaded"]


def en_keywords(q):
    """3–8 англійських ключових слів: через модель, а якщо її нема — зі словника математики."""
    try:
        raw = llm([{"role": "system", "content": "Відповідай ТІЛЬКИ англійськими ключовими словами через кому "
                    "(3–8 слів), без пояснень."}, {"role": "user", "content": q}], timeout=20)
        words = [w.strip().lower() for w in re.split(r"[,\n]", raw) if 2 < len(w.strip()) < 30]
        if words:
            return words[:8]
    except Exception:  # noqa: BLE001
        pass
    return kb_terms(q)


def subject_reference(q, key):
    """Твердження з бази предмета, які стосуються питання (або [])."""
    st = SUBJ_STATE[key]
    if not st["loaded"] or not st["facts"]:
        return []
    kws = [w[:5] for phrase in en_keywords(q) for w in phrase.split() if len(w) > 2]
    if not kws:
        return []
    out = []
    for f in st["facts"]:
        low = f.lower()
        if any(k in low for k in kws):
            out.append(f)
    return out[:3]


def ask_model(history):
    users = [m["content"] for m in history if m["role"] == "user"]
    query = users[-1]
    if wants_code(query):
        return generate_code_file(query, history)
    if wants_math(query):
        return math_answer(query, history)
    if not wants_search(query):
        return chat_reply(history)
    if query.lower().startswith(("/search ", "/find ")):
        query = query.split(" ", 1)[1]
    # уточнення типу "а ще?" / "а він де?" — додаємо попередню тему
    if len(keywords(query)) <= 1 and len(users) > 1:
        query = users[-2] + " " + query
    search_q = " ".join(keywords(query)) or query
    try:
        sources = gather(search_q)
    except Exception as e:  # noqa: BLE001
        return f"Помилка пошуку: {e}"
    if not sources:
        return "Не вдалося дістатися до сайтів. Перевір інтернет і спробуй ще раз."
    chosen = select_sentences(search_q, sources)
    if not chosen:
        return "Нічого певного не знайшов за цим запитом. Спробуй сформулювати інакше."
    subj = detect_subject(query)
    extra = subject_reference(query, subj) if subj else []
    try:
        text = write_answer(query, chosen, extra)
        used = used_domains(chosen, sources) + (["Seecer-DataBase"] if extra else [])
        return f"{text}\n\n{DIM}Джерела: {', '.join(used)}{RESET}"
    except Exception:  # noqa: BLE001
        # якщо генерація недоступна — запасний варіант зі складених речень
        return compose(search_q, sources, chosen)


# ---------- АГЕНТ: сам планує й виконує задачі інструментами ----------
# Модель отримує ціль і по кроках викликає інструменти (файли, запуск коду, пошук, обчислення,
# рій). Бачить результат кожного кроку й продовжує, поки не завершить.
# Безпека: файли — лише в робочій папці seecode_workspace; запуск коду й команд — тільки з
# підтвердження користувача; небезпечні команди блокуються; є ліміт кроків; Ctrl+C зупиняє.
AGENT_DIR = LazyDir("seecode_workspace")
AGENT_MAX_STEPS = int(os.environ.get("SEECODE_AGENT_STEPS", "25"))
AGENT_OBS_LIMIT = 2500        # скільки символів результату інструмента бачить модель
AGENT_CTX_LIMIT = 18000       # ліміт контексту агента (символів), старі кроки стискаються
AGENT_STATE = {"on": False, "auto_python": os.environ.get("SEECODE_AGENT_AUTO") == "1", "memory": []}

SHELL_BLOCK = re.compile(
    r"\brm\s+-[a-z]*[rf][a-z]*\s+(/|~|\$HOME|%USERPROFILE%|\*)|\bmkfs\b|\bdd\s+if=|>\s*/dev/sd|:\(\)\s*\{"
    r"|\bshutdown\b|\breboot\b|\bformat\s+[a-z]:|\bdel\s+/[sqf]|\brd\s+/s|\brmdir\s+/s|\breg\s+(delete|add)"
    r"|\bdiskpart\b|\bcipher\s+/w|(curl|wget|iwr|invoke-webrequest)[^|;&]*\|\s*(sh|bash|zsh|iex|powershell)"
    r"|\bchmod\s+-R\s+777\s+/|\bsudo\b|\bnet\s+user\b|\bschtasks\b|\bpowershell\b.*-enc", re.I)

AGENT_TOOLS_DOC = """\
list_files   {"path": "."}                                  — показати файли робочої папки
read_file    {"path": "a.py", "start": 1, "end": 200}       — прочитати рядки файлу
write_file   {"path": "a.py"}                               — створити/перезаписати файл; ВМІСТ напиши ПІСЛЯ JSON в окремому блоці ```
edit_file    {"path": "a.py", "old": "...", "new": "..."}   — замінити унікальний фрагмент у файлі
run_python   {"path": "a.py", "args": "", "timeout": 30}    — запустити Python-скрипт (користувач підтверджує)
run_shell    {"command": "...", "timeout": 30}              — команда терміналу (користувач підтверджує)
web_search   {"query": "..."}                               — знайти в інтернеті й зібрати факти
fetch_url    {"url": "https://..."}                         — прочитати текст веб-сторінки
calculate    {"expression": "2x+3=11"}                      — точні обчислення, рівняння, статистика
knowledge    {"query": "..."}                               — база знань Seecer (математика, біологія, програмування…)
build_script {"task": "...", "filename": "x.py"}            — великий складний скрипт через рій із 100 агентів (повільно!)
ask_user     {"question": "..."}                            — запитати користувача, якщо бракує даних"""

AGENT_SYSTEM = (
    "Ти — SeeCode Agent: автономний помічник, що САМ виконує завдання інструментами в робочій папці "
    "користувача. Спілкуйся мовою користувача (за замовчуванням українською).\n\n"
    "ФОРМАТ. Кожна твоя відповідь — РІВНО ОДИН JSON-обʼєкт і більше нічого:\n"
    '{"thought": "коротко: що робиш і навіщо", "tool": "імʼя_інструмента", "args": {...}}\n'
    'Коли завдання виконано: {"final": "підсумок: що зроблено, де файли, як запустити"}\n'
    "Єдиний виняток: для write_file вміст файлу пиши ПІСЛЯ JSON в окремому блоці ``` (не в JSON).\n\n"
    "ПРАВИЛА:\n"
    "1. На першому кроці в thought склади короткий план із 2–5 пунктів.\n"
    "2. Один інструмент за крок. Дочекайся результату й уважно прочитай його, перш ніж діяти далі.\n"
    "3. Код: write_file → run_python → перевір результат. Якщо помилка — прочитай її, виправ "
    "(edit_file або write_file) і запусти знову. Не оголошуй «готово», поки не перевірив.\n"
    "4. Не вигадуй результатів і фактів — бери їх з інструментів. Не вгадуй вміст файлів — читай.\n"
    "5. Усі файли — у робочій папці, шляхи відносні (напр. game.py, data/notes.txt).\n"
    "6. Якщо бракує даних — ask_user. Якщо щось неможливо — final із чесним поясненням.\n"
    "7. Не повторюй однакові дії. Будь лаконічним. Для звичайного скрипта обирай write_file, "
    "build_script — лише для справді великого й складного.\n\n"
    "ІНСТРУМЕНТИ:\n" + AGENT_TOOLS_DOC + "\n\n"
    "ПРИКЛАД write_file (JSON, а далі блок із вмістом):\n"
    '{"thought": "створюю скрипт", "tool": "write_file", "args": {"path": "hello.py"}}\n'
    "```python\nprint('привіт')\n```"
)


class ToolError(Exception):
    """Помилка інструмента — текст повертається моделі як результат."""


# ----- безпечні шляхи -----
def ws_path(p):
    root = os.path.realpath(os.fspath(AGENT_DIR))
    p = str(p or ".").replace("\\", "/")
    full = os.path.realpath(os.path.join(root, p))
    if full != root and not full.startswith(root + os.sep):
        raise ToolError(f"шлях «{p}» поза робочою папкою — це заборонено")
    return full


def ws_rel(full):
    root = os.path.realpath(os.fspath(AGENT_DIR))
    return os.path.relpath(full, root).replace(os.sep, "/")


def _clip(text, limit=AGENT_OBS_LIMIT):
    text = text.strip("\n")
    if len(text) <= limit:
        return text
    half = limit // 2
    return text[:half] + f"\n… [обрізано {len(text) - limit} символів] …\n" + text[-half:]


def _int(v, default, lo, hi):
    try:
        return max(lo, min(hi, int(v)))
    except (TypeError, ValueError):
        return default


# ----- інструменти -----
def tool_list_files(args, body=None):
    root = ws_path(args.get("path", "."))
    if not os.path.isdir(root):
        raise ToolError("це не папка або її нема")
    out, count = [], 0
    base_depth = root.rstrip(os.sep).count(os.sep)
    for cur, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if not d.startswith("."))
        if cur.count(os.sep) - base_depth >= 3:
            dirs[:] = []
        for fn in sorted(files):
            if fn.startswith("."):
                continue
            full = os.path.join(cur, fn)
            out.append(f"{ws_rel(full)}  ({os.path.getsize(full)} Б)")
            count += 1
            if count >= 200:
                return "\n".join(out) + "\n… (показано 200 файлів)"
    return "\n".join(out) or "(папка порожня)"


def tool_read_file(args, body=None):
    full = ws_path(args.get("path"))
    if not os.path.isfile(full):
        raise ToolError("файлу нема")
    if os.path.getsize(full) > 1_000_000:
        raise ToolError("файл завеликий (>1 МБ)")
    with open(full, encoding="utf-8", errors="replace") as f:
        lines = f.read().splitlines()
    start = _int(args.get("start"), 1, 1, max(1, len(lines)))
    end = _int(args.get("end"), start + 199, start, start + 399)
    chunk = lines[start - 1:end]
    head = f"{ws_rel(full)} — рядки {start}–{start + len(chunk) - 1} із {len(lines)}"
    return head + "\n" + "\n".join(f"{start + i:>4}│ {l}" for i, l in enumerate(chunk))


AGENT_TOUCHED = []     # файли, створені/змінені агентом у поточному завданні


def tool_write_file(args, body=None):
    content = args.get("content")
    if content is None:
        content = body
    if content is None:
        raise ToolError("немає вмісту: напиши його після JSON в блоці ```")
    if len(content) > 500_000:
        raise ToolError("вміст завеликий (>500 КБ)")
    full = ws_path(args.get("path"))
    if os.path.isdir(full) or full == os.path.realpath(os.fspath(AGENT_DIR)):
        raise ToolError("це папка")
    os.makedirs(os.path.dirname(full), exist_ok=True)
    existed = os.path.isfile(full)
    if existed:
        shutil.copyfile(full, full + ".bak")            # резервна копія перед перезаписом
    with open(full, "w", encoding="utf-8", newline="\n") as f:
        f.write(content.rstrip("\n") + "\n")
    if full not in AGENT_TOUCHED:
        AGENT_TOUCHED.append(full)
    n = len(content.splitlines())
    return f"{'Перезаписано' if existed else 'Створено'} {ws_rel(full)} ({n} рядків)"


def tool_edit_file(args, body=None):
    full = ws_path(args.get("path"))
    old, new = args.get("old"), args.get("new")
    if not os.path.isfile(full):
        raise ToolError("файлу нема")
    if not old or new is None:
        raise ToolError("потрібні поля old і new")
    with open(full, encoding="utf-8") as f:
        text = f.read()
    n = text.count(old)
    if n == 0:
        raise ToolError("фрагмент old не знайдено — прочитай файл і скопіюй точно")
    if n > 1:
        raise ToolError(f"фрагмент old зустрічається {n} разів — додай більше контексту")
    shutil.copyfile(full, full + ".bak")
    with open(full, "w", encoding="utf-8", newline="\n") as f:
        f.write(text.replace(old, new, 1))
    if full not in AGENT_TOUCHED:
        AGENT_TOUCHED.append(full)
    return f"Змінено {ws_rel(full)}"


def _decode(b):
    for enc in ("utf-8", sys.stdout.encoding or "utf-8", "cp1251"):
        try:
            return b.decode(enc)
        except (UnicodeDecodeError, LookupError):
            continue
    return b.decode("utf-8", errors="replace")


def _run_proc(cmd, shell, timeout):
    env = dict(os.environ, PYTHONIOENCODING="utf-8", PYTHONUNBUFFERED="1")
    try:
        p = subprocess.run(cmd, shell=shell, cwd=os.path.realpath(os.fspath(AGENT_DIR)), stdin=subprocess.DEVNULL,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, env=env)
    except subprocess.TimeoutExpired as e:
        out = _decode(e.stdout or b"")
        return f"ТАЙМАУТ ({timeout} с) — процес зупинено\n{_clip(out, 1500)}"
    return f"код виходу: {p.returncode}\n{_clip(_decode(p.stdout), 2500) or '(виводу немає)'}"


def tool_run_python(args, body=None):
    full = ws_path(args.get("path"))
    if not os.path.isfile(full):
        raise ToolError("файлу нема")
    import shlex
    extra = shlex.split(str(args.get("args") or ""), posix=(os.name != "nt"))
    return _run_proc([sys.executable, full] + extra, False, _int(args.get("timeout"), 30, 1, 120))


def tool_run_shell(args, body=None):
    cmd = str(args.get("command") or "").strip()
    if not cmd:
        raise ToolError("порожня команда")
    return _run_proc(cmd, True, _int(args.get("timeout"), 30, 1, 120))


def tool_calculate(args, body=None):
    q = str(args.get("expression") or args.get("query") or "")
    r = compute_math(q)
    if not r:
        raise ToolError("не вдалося обчислити — запиши як вираз або рівняння з x")
    return r


def tool_web_search(args, body=None):
    q = str(args.get("query") or "").strip()
    if not q:
        raise ToolError("порожній запит")
    search_q = " ".join(keywords(q)) or q
    sources = gather(search_q)
    if not sources:
        return "Нічого не знайдено (можливо, немає інтернету)."
    chosen = select_sentences(search_q, sources)
    facts = [f"- {shorten(c[3], 300)}" for c in chosen[:7]]
    urls = [u for u, _ in sources[:5]]
    return ("\n".join(facts) or "Підходящих речень не знайдено.") + "\nДжерела: " + ", ".join(urls)


def _public_url(url):
    import ipaddress
    import socket
    u = urllib.parse.urlparse(url)
    if u.scheme not in ("http", "https") or not u.hostname:
        raise ToolError("дозволені лише адреси http(s)://")
    try:
        infos = socket.getaddrinfo(u.hostname, None)
    except OSError:
        raise ToolError("адресу не вдалося визначити")
    for info in infos:
        ip = ipaddress.ip_address(info[4][0])
        if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved or ip.is_multicast:
            raise ToolError("локальні та приватні адреси заборонені")


def tool_fetch_url(args, body=None):
    url = str(args.get("url") or "").strip()
    _public_url(url)
    try:
        text = http_get(url, timeout=12, limit=400_000)
    except Exception as e:  # noqa: BLE001
        raise ToolError(f"не вдалося завантажити: {e}")
    if "<html" in text[:3000].lower() or "<p" in text[:6000].lower():
        p = _Paras()
        p.feed(text)
        p._flush()
        text = "\n".join(p.paras) or clean_text(re.sub(r"<[^>]+>", " ", text))
    return _clip(text, 3000)


def tool_knowledge(args, body=None):
    q = str(args.get("query") or "").strip()
    parts = []
    if wants_math(q):
        ensure_math_loaded(False)
        if MATH["loaded"]:
            concepts, examples = kb_lookup(q)
            parts += [f"- {n}: {e}" for n, e in concepts] + [f"- {ex}" for ex in examples]
    sub = detect_subject(q)
    if sub:
        ensure_subject_loaded(sub, False)
        parts += [f"- {f}" for f in subject_reference(q, sub)]
    return "\n".join(parts) or "У базі нічого не знайдено за цим запитом."


def tool_ask_user(args, body=None):
    q = str(args.get("question") or "").strip() or "?"
    print(f"    {fg((235, 180, 60))}? {q}{RESET}")
    try:
        ans = input("      > ").strip()
    except EOFError:
        ans = ""
    return f"Відповідь користувача: {ans or '(порожньо)'}"


def tool_build_script(args, body=None):
    task = str(args.get("task") or "").strip()
    if not task:
        raise ToolError("немає опису завдання")
    result, info = swarm_build(task)
    if result is None:
        raise ToolError(str(info))
    code, fname, ext = result
    name = str(args.get("filename") or "").strip() or (os.path.splitext(fname)[0] + ext)
    full = ws_path(name)
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w", encoding="utf-8", newline="\n") as f:
        f.write(code.rstrip("\n") + "\n")
    if full not in AGENT_TOUCHED:
        AGENT_TOUCHED.append(full)
    return f"Рій створив {ws_rel(full)} ({len(code.splitlines())} рядків). Звіт: " + "; ".join(info["report"])


# імʼя → (функція, чи показувати «зайнятість», що підтверджувати)
AGENT_TOOLS = {
    "list_files": (tool_list_files, False),
    "read_file": (tool_read_file, False),
    "write_file": (tool_write_file, False),
    "edit_file": (tool_edit_file, False),
    "run_python": (tool_run_python, True),
    "run_shell": (tool_run_shell, True),
    "calculate": (tool_calculate, False),
    "web_search": (tool_web_search, True),
    "fetch_url": (tool_fetch_url, True),
    "knowledge": (tool_knowledge, True),
    "build_script": (tool_build_script, False),
    "ask_user": (tool_ask_user, False),
}


# ----- підтвердження небезпечних дій -----
def agent_confirm(kind, detail, allow_always=False, view=None):
    opts = "[y] так   [n] ні" + ("   [a] завжди для Python" if allow_always else "") + \
           ("   [v] показати код" if view else "")
    while True:
        try:
            ans = input(f"    {fg((235, 180, 60))}? Дозволити {kind}: {detail}{RESET}\n"
                        f"      {DIM}{opts}{RESET} > ").strip().lower()
        except EOFError:
            return False
        if ans in ("y", "yes", "т", "так", "д", "да"):
            return True
        if allow_always and ans in ("a", "завжди"):
            AGENT_STATE["auto_python"] = True
            return True
        if view and ans in ("v", "код"):
            print(view() + "\n")
            continue
        return False        # n, порожньо або щось інше — безпечна відмова


def _needs_confirm(tool, args):
    """None — можна одразу; інакше (вид дії, опис, чи є «завжди», показувач коду)."""
    if tool == "run_python":
        if AGENT_STATE["auto_python"]:
            return None
        path = args.get("path")

        def view():
            full = ws_path(path)
            with open(full, encoding="utf-8", errors="replace") as f:
                return code_block(f.read(), 60)

        return ("запуск Python", f"{path} {args.get('args') or ''}".strip(), True, view)
    if tool == "run_shell":
        return ("команди", str(args.get("command")), False, None)
    if tool == "build_script":
        return ("рій із ~100 запитів до моделі", str(args.get("task"))[:80], False, None)
    return None


# ----- розбір відповіді моделі -----
_FENCE_RE = re.compile(r"```([\w+#.-]*)[ \t]*\n(.*?)(?:```|\Z)", re.S)


def _first_json(text):
    dec = json.JSONDecoder()
    for m in re.finditer(r"\{", text):
        try:
            obj, _ = dec.raw_decode(text[m.start():])
        except ValueError:
            continue
        if isinstance(obj, dict):
            return obj
    return None


def parse_agent_reply(raw):
    """→ (дія: dict | None, вміст_блока_коду | None)."""
    fences = [(m.group(1).lower(), m.group(2)) for m in _FENCE_RE.finditer(raw)]
    head = _FENCE_RE.sub("", raw)
    obj = _first_json(head)
    used = None
    if obj is None:                                  # JSON міг бути в блоці ```json
        for i, (lang, c) in enumerate(fences):
            if lang in ("json", ""):
                obj = _first_json(c)
                if obj is not None:
                    used = i
                    break
    if obj is None:
        return None, None
    body = next((c for i, (lang, c) in enumerate(fences) if i != used and lang != "json"), None)
    if body is not None:
        body = body.strip("\n")
    return obj, body


def normalize_action(obj):
    """→ ('final', текст) | ('tool', імʼя, args) | None."""
    if obj.get("final") is not None:
        return ("final", str(obj["final"]))
    tool = obj.get("tool") or obj.get("action") or obj.get("name")
    if not isinstance(tool, str):
        return None
    args = obj.get("args", obj.get("arguments"))
    if not isinstance(args, dict):
        args = {k: v for k, v in obj.items() if k not in ("thought", "tool", "action", "name", "args", "arguments")}
    return ("tool", tool.strip(), args)


# ----- вивід кроків -----
def _short(v, n=70):
    s = str(v).replace("\n", " ")
    return s if len(s) <= n else s[:n - 1] + "…"


def _fmt_args(args):
    return ", ".join(f"{k}={_short(v, 40)}" for k, v in args.items() if k != "content")


def _print_result(text, ok=True):
    cols = shutil.get_terminal_size((80, 24)).columns - 8
    lines = [l for l in text.splitlines() if l.strip()] or ["(порожньо)"]
    color = DIM if ok else fg(DOT_COLOR[FOUND])
    for i, l in enumerate(lines[:6]):
        print(f"    {color}{'⎿' if i == 0 else ' '} {l[:cols]}{RESET}")
    if len(lines) > 6:
        print(f"    {DIM}  … ще {len(lines) - 6} рядків{RESET}")


def _build_context(system, goal_msg, steps_log, recent, state):
    """Складає повідомлення для моделі; старі кроки стискає в короткий підсумок (він лишається назавжди)."""
    total = sum(len(m["content"]) for m in recent) + len(system) + len(goal_msg["content"])
    if total > AGENT_CTX_LIMIT and len(recent) > 8:
        recent = recent[-8:]
        state["cut"] = True
    msgs = [{"role": "system", "content": system}, goal_msg]
    if state["cut"]:
        older = steps_log[:max(0, len(steps_log) - len(recent) // 2)]
        msgs.append({"role": "user", "content":
                     "Стислий підсумок ранніх кроків (деталі втрачено):\n" + "\n".join(older)[-3500:]})
    return msgs + recent, recent


def agent_think(msgs):
    with Spinner():
        return llm_retry(msgs, tries=3, timeout=90)


def agent_run(goal):
    """Автономний цикл: думає → викликає інструмент → дивиться на результат → … → final."""
    del AGENT_TOUCHED[:]
    try:
        os.makedirs(AGENT_DIR, exist_ok=True)
        listing = tool_list_files({})
    except OSError as e:
        return f"Не вдалося створити робочу папку: {e}"
    mem = "".join(f"- {g} → {f}\n" for g, f in AGENT_STATE["memory"][-3:])
    goal_msg = {"role": "user", "content":
                f"ЦІЛЬ: {goal}\n\nРобоча папка ({AGENT_DIR}) містить:\n{listing}\n"
                + (f"\nПопередні завдання цієї сесії:\n{mem}" if mem else "")
                + "\nПочинай: один JSON на відповідь."}
    print(f"{ACC}◈{RESET} {BOLD}Агент{RESET} {DIM}· ціль: {_short(goal, 80)} · макс. {AGENT_MAX_STEPS} кроків · "
          f"Ctrl+C — зупинити{RESET}\n")
    recent, steps_log, ctx = [], [], {"cut": False}
    invalid = repeats = steps = 0
    last_sig = None
    final = None
    try:
        while steps < AGENT_MAX_STEPS and final is None:
            msgs, recent = _build_context(AGENT_SYSTEM, goal_msg, steps_log, recent, ctx)
            try:
                raw = agent_think(msgs)
            except Exception as e:  # noqa: BLE001
                return f"Агент зупинився: немає зв'язку з моделлю ({e})."
            obj, body = parse_agent_reply(raw)
            act = normalize_action(obj) if obj else None
            if act is None:
                invalid += 1
                if invalid >= 3:
                    return "Агент зупинився: модель тричі відповіла не в потрібному форматі. Спробуй сформулювати ціль простіше."
                recent += [{"role": "assistant", "content": _clip(raw, 800)},
                           {"role": "user", "content": 'ПОМИЛКА ФОРМАТУ. Відповідай РІВНО ОДНИМ JSON: '
                            '{"thought": "...", "tool": "...", "args": {...}} або {"final": "..."}.'}]
                continue
            invalid = 0
            if obj.get("thought"):
                print(f"  {DIM}✻ {_short(obj['thought'], 200)}{RESET}")
            if act[0] == "final":
                final = act[1]
                break
            _, tool, args = act
            steps += 1
            sig = (tool, json.dumps(args, sort_keys=True, ensure_ascii=False, default=str))
            repeats = repeats + 1 if sig == last_sig else 0
            last_sig = sig
            print(f"  {ACC}▸ {tool}{RESET} {DIM}{_fmt_args(args)}{RESET}")
            if repeats >= 3:
                return "Агент зупинився: застряг, повторюючи одну й ту саму дію. Уточни ціль або розбий її на частини."
            obs, ok = agent_exec(tool, args, body)
            _print_result(obs, ok)
            if repeats >= 1:
                obs += "\n\n[УВАГА: ти повторюєш ту саму дію. Зміни підхід або заверши через final.]"
            shown = dict(obj)
            if tool == "write_file" and body is not None:
                shown["args"] = dict(args, content=f"<{len(body.splitlines())} рядків записано>")
            steps_log.append(f"{steps}. {tool}({_short(_fmt_args(args), 60)}) → {_short(obs, 90)}")
            recent += [{"role": "assistant", "content": json.dumps(shown, ensure_ascii=False)[:1500]},
                       {"role": "user", "content": f"РЕЗУЛЬТАТ {tool} ({'успіх' if ok else 'ПОМИЛКА'}):\n{_clip(obs)}"}]
    except KeyboardInterrupt:
        print(f"\n  {DIM}⏹ зупинено користувачем{RESET}")
        final = "Агента зупинено (Ctrl+C)."
    if final is None:
        final = (f"Досягнуто ліміту в {AGENT_MAX_STEPS} кроків. Зроблене лишилось у робочій папці; "
                 f"напиши «продовжуй», щоб піти далі.")
    AGENT_STATE["memory"].append((_short(goal, 80), _short(final, 160)))
    out = [final]
    for full in AGENT_TOUCHED[-3:]:
        if os.path.isfile(full):
            with open(full, encoding="utf-8", errors="replace") as f:
                n = len(f.read().splitlines())
            out += ["", file_card(full, n)]
    return "\n".join(out)


def agent_exec(tool, args, body):
    """Виконує один інструмент: (текст_результату, успіх)."""
    if tool not in AGENT_TOOLS:
        return f"Невідомий інструмент «{tool}». Доступні: {', '.join(AGENT_TOOLS)}", False
    func, busy = AGENT_TOOLS[tool]
    try:
        if tool == "run_shell" and SHELL_BLOCK.search(str(args.get("command", ""))):
            raise ToolError("ця команда заблокована як небезпечна")
        need = _needs_confirm(tool, args)
        if need and not agent_confirm(*need):
            return "Користувач ВІДХИЛИВ цю дію. Не повторюй її; запропонуй інший шлях або заверши.", False
        if busy:
            with Spinner():
                return func(args, body), True
        return func(args, body), True
    except ToolError as e:
        return f"ПОМИЛКА: {e}", False
    except KeyboardInterrupt:
        raise
    except Exception as e:  # noqa: BLE001
        return f"ПОМИЛКА: {type(e).__name__}: {e}", False


AGENT_HELP = f"""{BOLD}Режим агента{RESET}
  /agent <ціль>   агент сам виконає завдання (файли, запуск коду, пошук, обчислення)
  /agent on|off   увімкнути/вимкнути режим: кожне повідомлення стає ціллю
  /workspace      відкрити робочу папку агента ({AGENT_DIR})
Файли агент створює лише в робочій папці. Запуск коду й команд — тільки після твого «y»."""


# ---------- поле вводу ----------
def read_prompt():
    w = min(shutil.get_terminal_size((80, 24)).columns, 76)
    print(ACC + "╭" + "─" * (w - 2) + "╮" + RESET)
    print(ACC + "│" + RESET + " > " + " " * (w - 5) + ACC + "│" + RESET)
    print(ACC + "╰" + "─" * (w - 2) + "╯" + RESET)
    hint = "◈ режим агента (/agent off — вимкнути)" if AGENT_STATE["on"] else "? for shortcuts"
    print(f"  {DIM}{hint}{RESET}", end="")
    sys.stdout.write("\033[2A\r\033[4C")  # курсор у рамку після "> "
    sys.stdout.flush()
    try:
        text = input()
    except BaseException:
        sys.stdout.write("\033[2B\r")  # вийти нижче рамки
        raise
    # після Enter курсор на нижній межі: піднімаємось на верх рамки
    # і стираємо рамку з підказкою — на екрані лишається тільки "> текст"
    sys.stdout.write("\033[2A\r\033[J")
    sys.stdout.flush()
    return text.strip()


HELP = f"""{BOLD}Команди:{RESET}
  /help     цей список
  /status   поточні налаштування
  напиши код …   запускає рій із 100 агентів (генерація, пошук помилок,
                 виправлення, тести, перевірка якості) і дає готовий файл
  /code …   швидка генерація одним агентом у файл
  /math …   математика: точний розрахунок + база знань (напр. 2x+3=11, 15% від 200)
  /open     відкрити останній створений файл
  /folder   показати його в папці      /show   вивести весь код у чат
  /agent …  АГЕНТ: сам виконає завдання (файли, запуск коду, пошук); /agent on|off, /workspace
  /clear    очистити розмову
  /eye      показати око
  /exit     вийти (також Ctrl+D)"""


def main():
    os.system("cls" if os.name == "nt" else "clear")
    welcome()
    history = []
    while True:
        try:
            text = read_prompt()
        except (EOFError, KeyboardInterrupt):
            print(f"\n{DIM}Bye! 👁{RESET}")
            break
        if not text:
            continue
        print(f"{DIM}> {text}{RESET}\n")
        if text in ("/exit", "/quit"):
            print(f"{DIM}Bye! 👁{RESET}")
            break
        if text == "/help":
            print(HELP + "\n")
            continue
        if text == "/status":
            mb = (f"{MATH['files']}/{len(MATH_FILES)} файлів, {len(MATH['concepts'])} понять, "
                  f"{len(MATH['ex'])} прикладів" if MATH["loaded"] else "ще не завантажена (завантажиться при першому питанні)")
            print(f"  version: {VERSION}\n  cwd:     {os.getcwd()}\n  sources: Wikipedia + DuckDuckGo + знайдені сайти\n"
                  f"  math:    {mb}\n  files:   {FILES_DIR}\n  agent:   "
                  f"{'увімкнений' if AGENT_STATE['on'] else 'вимкнений'} · папка {AGENT_DIR}")
            for k, info in SUBJECTS.items():
                stt = SUBJ_STATE[k]
                print(f"  {info['label']}: " + (f"{len(stt['facts'])} унікальних тверджень" if stt["loaded"]
                                                else "ще не завантажена"))
            print()
            continue
        if text == "/clear":
            history.clear()
            os.system("cls" if os.name == "nt" else "clear")
            welcome()
            continue
        if text in ("/open", "/folder", "/show"):
            print(file_command(text) + "\n")
            continue
        if text == "/eye":
            print("\n".join(render_eye()) + "\n")
            continue
        if text == "/workspace":
            ok = open_path(os.fspath(AGENT_DIR))
            print((f"Відкриваю: {AGENT_DIR}" if ok else f"Робоча папка агента: {AGENT_DIR}") + "\n")
            continue
        goal = None
        m_agent = re.match(r"^/agent(?:\s+(.*))?$", text, re.S | re.I)
        if m_agent:
            rest = (m_agent.group(1) or "").strip()
            if rest.lower() in ("on", "увімк", "вкл"):
                AGENT_STATE["on"] = True
                print(f"  Режим агента увімкнено: кожне повідомлення — ціль. Вимкнути: /agent off\n")
                continue
            if rest.lower() in ("off", "вимк", "викл"):
                AGENT_STATE["on"] = False
                print("  Режим агента вимкнено.\n")
                continue
            if not rest:
                print(AGENT_HELP + "\n")
                continue
            goal = rest
        elif AGENT_STATE["on"] and not text.startswith("/"):
            goal = text

        history.append({"role": "user", "content": text})
        try:
            if goal:
                answer = agent_run(goal)
            elif wants_swarm(text):
                answer = run_swarm(text)       # рій малює себе сам
            else:
                if wants_math(text):
                    ensure_math_loaded(verbose=True)   # перше питання: завантажити базу
                elif not wants_code(text) and wants_search(text):
                    sub = detect_subject(text)
                    if sub:
                        ensure_subject_loaded(sub, verbose=True)
                with Spinner():
                    answer = ask_model(history)
        except Exception:  # noqa: BLE001
            answer = "Сталася помилка, але програма працює далі:\n" + traceback.format_exc()
        history.append({"role": "assistant", "content": answer})
        print(f"{ACC}●{RESET} {answer}\n")


if __name__ == "__main__":
    try:
        main()
    except Exception:  # noqa: BLE001
        traceback.print_exc()
        input("\nСталася помилка. Натисни Enter, щоб закрити…")
