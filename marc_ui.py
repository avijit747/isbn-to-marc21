import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json
import re
from datetime import datetime
from pathlib import Path
import threading
import os

# =========================
# SPEED/UX TUNING
# =========================
UI_UPDATE_EVERY = 500
WRITE_FLUSH_EVERY = 1000

cancel_flag = False
worker_thread = None

# ============================================================
# Precompiled regex
# ============================================================
RE_ISBN = re.compile(r"[^0-9Xx]")
RE_YEAR = re.compile(r"(19|20)\d{2}")
RE_SPACES = re.compile(r"\s+")
RE_AND = re.compile(r"\s+\band\b\s+", re.I)
RE_ROLE = re.compile(r"\b(co-?author|author|co-?editor|editor)\s*:\s*", re.I)
RE_SPLIT_NAMES = re.compile(r"\s*;\s*")
RE_HONORIFIC = re.compile(r"\b(dr\.?|prof\.?|mr\.?|mrs\.?|ms\.?|sir)\b", re.I)
RE_CO_PREFIX = re.compile(r"^\s*co-?\s*[:\-]?\s*", re.I)

# Corporate/body hints (for 110/710 and to avoid casing institutions)
RE_CORP_HINT = re.compile(
    r"\b(university|college|institute|department|faculty|school|"
    r"ministry|government|govt|director|office|committee|society|"
    r"research|centre|center|board|authority|mission|project|"
    r"p\.?\s*o\.?|post office|district|pin\s*code|p\.?s\.?|"
    r"road|street|lane|sector|block|nagar|bazar|post|police station|"
    r"ltd|pvt|private|limited|inc|llp|company|co\.)\b",
    re.I,
)

# Edition patterns (from Book Title)
RE_ED_PAREN = re.compile(r"\(\s*(?:edition|ed\.?)\s*[:\-]?\s*([^)]+)\)", re.I)
RE_ED_PAREN_NUM = re.compile(
    r"\(\s*([0-9]+(?:st|nd|rd|th))\s*(?:ed\.?|edition)\b[^)]*\)",
    re.I,
)
RE_ED_INLINE = re.compile(r"\b([0-9]+(?:st|nd|rd|th))\s*(?:ed\.?|edition)\b", re.I)
RE_ED_REV = re.compile(
    r"\b(revised|rev\.?|updated|enlarged|expanded)\s*(?:ed\.?|edition)\b",
    re.I,
)
RE_ED_TAIL = re.compile(
    r"\s*[,;:\-–—]\s*(?:[0-9]+(?:st|nd|rd|th)\s*(?:ed\.?|edition)|"
    r"(?:revised|rev\.?|updated|enlarged|expanded)\s*(?:ed\.?|edition))\s*$",
    re.I,
)

# 245 enhancements
RE_TITLE_AUTHOR = re.compile(r"(?:^|[\s/;,:-])author\s*[:\-]\s*(.+)$", re.I)
RE_VOL_PAREN = re.compile(r"\(\s*(?:vol(?:ume)?\.?)\s*([0-9]+)\s*\)", re.I)
RE_VOL_INLINE = re.compile(r"(?:^|[\s,;:-])(?:vol(?:ume)?\.?)\s*([0-9]+)\b", re.I)

# Part/Book/Module patterns -> 245 $n (NOT series)
RE_PART_CHUNK = re.compile(
    r"^\s*(part|book|module|unit|section|semester|term|year)\s*[-\.]?\s*"
    r"([0-9]+|[ivxlcdm]+)\b",
    re.I,
)
RE_PART_PAREN = re.compile(
    r"\(\s*(part|book|module|unit|section|semester|term|year)\s*[-\.]?\s*"
    r"([0-9]+|[ivxlcdm]+)\s*\)",
    re.I,
)
RE_PART_INLINE = re.compile(
    r"(?:^|[\s,;:-])(part|book|module|unit|section|semester|term|year)\s*"
    r"[-\.]?\s*([0-9]+|[ivxlcdm]+)\b",
    re.I,
)

# Responsibility label cleanup
RE_RESP_LABELS = re.compile(
    r"^\s*(author|authors|editor|editors|edited\s+by|by)\s*[:\-]?\s*",
    re.I,
)

# ============================================================
# SERIES DETECTION
# ============================================================
RE_SERIES_EXPLICIT = re.compile(
    r"[\(\[\{]?\s*series\s*[:\-]\s*([^)\]\}]+)[\)\]\}]?",
    re.I,
)
RE_TRAIL_PAREN = re.compile(r"\s*[\(\[]\s*([^\)\]]{3,160})\s*[\)\]]\s*$")
RE_TRAIL_DASH_SER = re.compile(r"\s*(?:--|—|–|-)\s*([^—–-]{3,160})\s*$")

RE_SER_NUM = re.compile(
    r"(?:^|[\s;:,])("
    r"(?:v\.?\s*\d+|vol\.?\s*\d+|volume\s*\d+|no\.?\s*\d+|nr\.?\s*\d+|"
    r"ser\.?\s*[^;,:]+|"
    r"\d{4}/\d+)"
    r")\s*$",
    re.I,
)

RE_ISSN_LABELED = re.compile(r"\bISSN\s*(\d{4}-\d{3}[\dXx])\b", re.I)

RE_NOT_SERIES = re.compile(
    r"\b(edition|ed\.|revised|rev\.?|updated|enlarged|expanded|"
    r"vol\.|volume|vol\s*\d+|"
    r"author|editor|by)\b",
    re.I,
)

SERIES_KEYWORDS = re.compile(
    r"\b(series|studies|monographs?|bulletin|report|pamphlet|paperbacks?|"
    r"discussion paper|working paper|annual|census|map|archives|clinic|"
    r"university bulletin|department of|geological survey|"
    r"engineering experiment station)\b",
    re.I,
)

RE_ROMAN_ONLY = re.compile(r"^(?=[IVXLCDM]+$)[IVXLCDM]{1,8}\.?$", re.I)
RE_DIGITS_ONLY = re.compile(r"^\d{1,4}\.?$")
RE_V_BAD = re.compile(r"^(parts?|series)\.?$", re.I)

# Publisher normalization constraints for 264 $b
RE_HAS_DIGIT = re.compile(r"\d")
RE_HAS_SYMBOL = re.compile(r"[^A-Za-z\s\.]")  # allow letters, spaces, dots only

# ============================================================
# Helpers
# ============================================================
def today_YYMMDD():
    return datetime.now().strftime("%y%m%d")


def _pd():
    import pandas as pd
    return pd


def normalize_spaces(s: str) -> str:
    return RE_SPACES.sub(" ", (s or "").strip())


def clean_isbn(isbn):
    if _pd().isna(isbn):
        return ""
    s = str(isbn).strip()
    if re.fullmatch(r"\d+\.0", s):
        s = s[:-2]
    return RE_ISBN.sub("", s)


def extract_year_from_pub_date(pub_date_str: str) -> str:
    s = (pub_date_str or "").strip()
    m = RE_YEAR.search(s)
    return m.group() if m else "    "


def _ends_with_terminal_punct(s: str) -> bool:
    s = (s or "").rstrip()
    return bool(s) and s[-1] in ".!?"


def build_008(year, lang, place_code="ii "):
    date_entered = today_YYMMDD()
    y = year if re.fullmatch(r"(19|20)\d{2}", str(year)) else "    "
    l = lang if re.fullmatch(r"[a-z]{3}", str(lang)) else "und"
    pc = (place_code + "   ")[:3]
    s = (
        f"{date_entered}"
        f"s"
        f"{y}"
        f"    "
        f"{pc}"
        + (" " * 17)
        + f"{l}"
        + (" " * 2)
    )
    return (s + (" " * 40))[:40]


def encode_marc_record(rec_lines):
    leader_template = "00000nam a2200000 a 4500"
    fields = []
    for line in rec_lines:
        line = line.rstrip("\n")
        if not line:
            continue
        if line.startswith("=LDR"):
            leader_template = line[6:].strip() or leader_template
            continue
        if not line.startswith("=") or len(line) < 5:
            continue
        tag = line[1:4]
        if tag.startswith("00"):
            data = line[6:]
            field_data = data.encode("utf-8") + b"\x1e"
        else:
            ind1 = line[6] if len(line) > 6 else " "
            ind2 = line[7] if len(line) > 7 else " "
            ind1 = " " if ind1 == "\\" else ind1
            ind2 = " " if ind2 == "\\" else ind2
            data = line[8:]
            data_bytes = (ind1 + ind2 + data.replace("$", "\x1f")).encode("utf-8")
            field_data = data_bytes + b"\x1e"
        fields.append((tag, field_data))

    directory = b""
    content = b""
    offset = 0
    for tag, field_data in fields:
        length = len(field_data)
        directory += f"{tag}{length:04d}{offset:05d}".encode("ascii")
        content += field_data
        offset += length

    base_address = 24 + len(directory) + 1
    record_length = base_address + len(content) + 1
    leader = leader_template[:24].ljust(24)
    leader = f"{record_length:05d}" + leader[5:12] + f"{base_address:05d}" + leader[17:24]
    return leader.encode("ascii") + directory + b"\x1e" + content + b"\x1d"


def mrk_record_text(rec_lines):
    out = []
    for line in rec_lines:
        if line is None:
            continue
        out.append(line.rstrip("\n"))
    return "\n".join(out) + "\n\n"


# ============================================================
# Language normalization
# ============================================================
DEFAULT_LANG_MAP = {
    "english": "eng",
    "french": "fre",
    "hindi": "hin",
    "marathi": "mar",
    "bengali": "ben",
    "urdu": "urd",
    "tamil": "tam",
    "telugu": "tel",
    "kannada": "kan",
    "malayalam": "mal",
    "gujarati": "guj",
    "punjabi": "pan",
    "odia": "ori",
    "oriya": "ori",
    "assamese": "asm",
    "sanskrit": "san",
    "nepali": "nep",
    "kashmiri": "kas",
    "konkani": "kok",
    "manipuri": "mni",
}


def _load_iso_639_2_language_map() -> dict:
    iso_path = Path("/usr/share/iso-codes/json/iso_639-2.json")
    if not iso_path.exists():
        return {}
    try:
        data = json.loads(iso_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    lang_map = {}
    for entry in data.get("639-2", []):
        name = (entry.get("name") or "").strip().lower()
        if not name:
            continue
        code = entry.get("bibliographic") or entry.get("alpha_3")
        if code:
            lang_map[name] = code.lower()
    return lang_map


LANG_MAP = {
    **DEFAULT_LANG_MAP,
    **_load_iso_639_2_language_map(),
}


def normalize_language(lang):
    if _pd().isna(lang) or not str(lang).strip():
        return "und"
    s = str(lang).strip().lower()
    if len(s) == 3 and s.isalpha():
        if s == "fra":
            return "fre"
        return s
    return LANG_MAP.get(s, "und")


# ============================================================
# Title casing (safer, improved for "mostly caps" titles)
# ============================================================
MINOR_WORDS = {"and", "or", "the", "a", "an", "in", "on", "for", "of", "to", "by", "at", "with"}


def smart_title_case(title: str) -> str:
    t = normalize_spaces(title)
    if not t:
        return ""
    if not re.search(r"[A-Za-z]", t):
        return t
    words = t.lower().split()
    out = []
    for i, w in enumerate(words):
        if w in MINOR_WORDS and i != 0:
            out.append(w)
        else:
            out.append(w.capitalize())
    return " ".join(out)


def maybe_title_case(title: str) -> str:
    """
    Normalise title ONLY when it is fully upper/lower OR mostly uppercase.
    """
    t = normalize_spaces(title)
    if not t:
        return ""
    letters = re.findall(r"[A-Za-z]", t)
    if not letters:
        return t

    upper = sum(1 for c in letters if c.isupper())
    ratio = upper / len(letters)

    if ratio >= 0.60:  # mostly caps
        return smart_title_case(t)

    if all(c.islower() for c in letters):
        return smart_title_case(t)

    return t


def normalize_title_punct(title: str) -> str:
    t = normalize_spaces(title)
    if not t:
        return ""
    t = re.sub(r",\s*,", ",", t)
    t = re.sub(r"\s*,\s*,\s*", ", ", t)
    t = re.sub(r"\s*\(\s*", "(", t)
    t = re.sub(r"\s*\)\s*", ")", t)
    t = re.sub(r",\s*,", ",", t)
    t = re.sub(r"\s*,\s*$", "", t)
    return normalize_spaces(t)


# ============================================================
# Edition (250) — ONLY from Book Title
# ============================================================
def normalize_edition_text(ed: str) -> str:
    ed = normalize_spaces(ed)
    if not ed:
        return ""
    ed = re.sub(r"^(edition|ed\.?)\s*[:\-]?\s*", "", ed, flags=re.I).strip()
    if re.fullmatch(r"\d+\.?", ed):
        return ""
    if not re.search(r"[A-Za-z]", ed):
        return ""
    if re.fullmatch(r"\d+(st|nd|rd|th)", ed, flags=re.I):
        ed = ed.lower() + " edition"
    if re.search(r"\bed\.?\b", ed, flags=re.I) and "edition" not in ed.lower():
        ed = re.sub(r"\bed\.?\b", "edition", ed, flags=re.I)
    return ed.strip()


def extract_edition_from_title(title_raw: str) -> str:
    t = normalize_spaces(title_raw)
    if not t:
        return ""
    if not re.search(r"\b(ed\.?|edition|revised|rev\.?|updated|enlarged|expanded)\b", t, re.I):
        return ""

    m = RE_ED_PAREN.search(t)
    if m:
        return normalize_edition_text(m.group(1))

    m = RE_ED_PAREN_NUM.search(t)
    if m:
        m2 = re.search(r"([0-9]+(?:st|nd|rd|th))", m.group(0), re.I)
        if m2:
            return normalize_edition_text(m2.group(1) + " edition")

    m = RE_ED_INLINE.search(t)
    if m:
        return normalize_edition_text(m.group(0))

    m = RE_ED_REV.search(t)
    if m:
        return normalize_edition_text(m.group(0))

    return ""


def remove_edition_from_title(title_raw: str) -> str:
    t = normalize_spaces(title_raw)
    if not t:
        return ""
    t = RE_ED_PAREN.sub("", t)
    t = RE_ED_PAREN_NUM.sub("", t)
    t = RE_ED_TAIL.sub("", t)
    return normalize_spaces(t)


# ============================================================
# Part number normalization for 245 $n
# ============================================================
def normalize_part_number(label, num):
    label = label.strip().capitalize()
    if re.fullmatch(r"[ivxlcdm]+", str(num), flags=re.I):
        num = str(num).upper()
    return f"{label} {num}"


# ============================================================
# Series extraction (returns series_title, series_numbering, labeled_issn)
# ============================================================
def _series_candidate_ok(series_a: str, series_v: str) -> bool:
    sa = normalize_spaces(series_a).strip(" .;:,")
    sv = normalize_spaces(series_v).strip(" .;:,")
    if not sa:
        return False
    if RE_ROMAN_ONLY.fullmatch(sa):
        return False
    if RE_DIGITS_ONLY.fullmatch(sa):
        return False
    if len(sa) < 3:
        return False
    if not re.search(r"[A-Za-z]", sa):
        return False
    if sv and RE_V_BAD.fullmatch(sv):
        return False
    return True


def extract_series_from_title(title_raw: str):
    t = normalize_spaces(title_raw)
    if not t:
        return "", "", ""

    m = RE_SERIES_EXPLICIT.search(t)
    if m:
        ser = normalize_spaces(m.group(1)).strip(" .;:,")
        if RE_PART_CHUNK.match(ser):
            return "", "", ""
        issn = RE_ISSN_LABELED.search(ser).group(1) if RE_ISSN_LABELED.search(ser) else ""
        ser = RE_ISSN_LABELED.sub("", ser).strip(" .;:,")
        v = ""
        mv = RE_SER_NUM.search(ser)
        if mv:
            v = normalize_spaces(mv.group(1)).strip(" .;:,")
            ser = normalize_spaces(ser[: mv.start()]).strip(" .;:,")
        has_kw = bool(SERIES_KEYWORDS.search(ser))
        has_num = bool(v or RE_SER_NUM.search(ser))
        has_issn = bool(issn)
        if ser and not RE_NOT_SERIES.search(ser) and (has_kw or has_num or has_issn) and _series_candidate_ok(ser, v):
            return ser, v, issn

    mp = RE_TRAIL_PAREN.search(t)
    if mp:
        inside = normalize_spaces(mp.group(1)).strip(" .;:,")
        if RE_PART_CHUNK.match(inside):
            return "", "", ""
        if not RE_NOT_SERIES.search(inside):
            has_kw = bool(SERIES_KEYWORDS.search(inside))
            has_num = bool(RE_SER_NUM.search(inside))
            has_issn = bool(RE_ISSN_LABELED.search(inside))
            if has_kw or has_num or has_issn:
                issn = RE_ISSN_LABELED.search(inside).group(1) if RE_ISSN_LABELED.search(inside) else ""
                inside2 = RE_ISSN_LABELED.sub("", inside).strip(" .;:,")
                if ";" in inside2:
                    left, right = [x.strip() for x in inside2.split(";", 1)]
                    ser = left.strip(" .;:,")
                    v = right.strip(" .;:,")
                    if _series_candidate_ok(ser, v):
                        return ser, v, issn
                mv = RE_SER_NUM.search(inside2)
                if mv:
                    v = normalize_spaces(mv.group(1)).strip(" .;:,")
                    ser = normalize_spaces(inside2[: mv.start()]).strip(" .;:,")
                    if _series_candidate_ok(ser, v):
                        return ser, v, issn
                if _series_candidate_ok(inside2, ""):
                    return inside2.strip(" .;:, "), "", issn

    md = RE_TRAIL_DASH_SER.search(t)
    if md:
        cand = normalize_spaces(md.group(1)).strip(" .;:,")
        if RE_PART_CHUNK.match(cand):
            return "", "", ""
        if cand and not RE_NOT_SERIES.search(cand):
            has_kw = bool(SERIES_KEYWORDS.search(cand))
            has_num = bool(RE_SER_NUM.search(cand))
            has_issn = bool(RE_ISSN_LABELED.search(cand))
            if has_kw or has_num or has_issn:
                issn = RE_ISSN_LABELED.search(cand).group(1) if RE_ISSN_LABELED.search(cand) else ""
                cand2 = RE_ISSN_LABELED.sub("", cand).strip(" .;:,")
                if ";" in cand2:
                    left, right = [x.strip() for x in cand2.split(";", 1)]
                    if _series_candidate_ok(left, right):
                        return left.strip(" .;:,"), right.strip(" .;:,"), issn
                mv = RE_SER_NUM.search(cand2)
                if mv:
                    v = normalize_spaces(mv.group(1)).strip(" .;:,")
                    ser = normalize_spaces(cand2[: mv.start()]).strip(" .;:,")
                    if _series_candidate_ok(ser, v):
                        return ser, v, issn
                if _series_candidate_ok(cand2, ""):
                    return cand2, "", issn

    return "", "", ""


def remove_series_from_title(title_raw: str) -> str:
    t = normalize_spaces(title_raw)
    if not t:
        return ""
    t2 = RE_SERIES_EXPLICIT.sub("", t).strip(" ,;:-–—")
    t2 = RE_TRAIL_PAREN.sub("", t2).strip(" ,;:-–—")
    t2 = RE_TRAIL_DASH_SER.sub("", t2).strip(" ,;:-–—")
    return normalize_spaces(t2)


# ============================================================
# Responsibility cleanup (for 245 $c) + name-case normalisation (ONLY $c)
# ============================================================
def clean_resp_text(s: str) -> str:
    s = normalize_spaces(s)
    if not s:
        return ""
    s = RE_RESP_LABELS.sub("", s)
    s = re.sub(r"\b(author|authors|editor|editors)\s*[:\-]\s*", "", s, flags=re.I)
    s = RE_CO_PREFIX.sub("", s)
    s = re.sub(r"\bco-?\s*(authors?|editors?)\b", "", s, flags=re.I)
    s = re.sub(r"\bco-?\s*[:\-]\s*", "", s, flags=re.I)
    s = RE_HONORIFIC.sub("", s)

    s = re.sub(r"\s*,\s*,\s*", ", ", s)
    s = re.sub(r"\s*,\s*\.", ".", s)
    s = re.sub(r"\s*,\s*$", "", s)
    s = re.sub(r"\s*,\s*", ", ", s)
    s = re.sub(r"\s+,", ",", s)
    s = re.sub(r",{2,}", ",", s)

    # remove standalone dots but keep initials like "R. B."
    s = re.sub(r"(?<![A-Z])\.(?!\s*[A-Z])", " ", s)
    return normalize_spaces(s).strip(" .;/")


def looks_corporate(name: str) -> bool:
    s = normalize_spaces(name).lower()
    if not s:
        return False
    if s.count(",") >= 3:
        return True
    return bool(RE_CORP_HINT.search(s))


def normalize_245c_personal_names(text: str) -> str:
    """
    Apply ONLY to 245 $c:
    - Convert ALL-CAPS personal names to proper case
    - Preserve mixed case
    - Do NOT touch acronyms/institutions/corporate bodies
    """
    text = normalize_spaces(text)
    if not text:
        return ""

    # Split but keep delimiters
    parts = re.split(r"(\s*;\s*|\s*,\s*)", text)

    for i in range(0, len(parts), 2):
        seg = parts[i].strip()
        if not seg:
            continue

        if looks_corporate(seg):
            continue

        letters_only = re.sub(r"[^A-Za-z]", "", seg)
        if not letters_only:
            continue

        if not letters_only.isupper():
            continue

        words = seg.split()
        fixed = []
        for w in words:
            if re.fullmatch(r"(?:[A-Z]\.){1,4}", w):
                fixed.append(w.upper())
                continue
            w_letters = re.sub(r"[^A-Za-z]", "", w)
            if w_letters.isupper() and len(w_letters) <= 3:
                fixed.append(w.upper())
                continue
            fixed.append(w.capitalize())

        parts[i] = " ".join(fixed)

    return "".join(parts)


# ============================================================
# Contributors (100/110/700/710)
# ============================================================
HONORIFICS = {"mr.": "Mr.", "mrs.": "Mrs.", "ms.": "Ms.", "dr.": "Dr.", "prof.": "Prof.", "sir": "Sir"}
SUFFIXES = {"jr.": "Jr.", "sr.": "Sr.", "iii": "III", "ii": "II"}


def strip_role_words(s: str) -> str:
    s = normalize_spaces(s)
    if not s:
        return ""
    s = re.sub(r"\b(editors?|authors?)\b", "", s, flags=re.I)
    s = re.sub(r"\bedited\s+by\b", "", s, flags=re.I)
    s = re.sub(r"\bcompiled\s+by\b", "", s, flags=re.I)
    s = re.sub(r"\btranslated\s+by\b", "", s, flags=re.I)
    s = re.sub(r"\bco-?\s*(authors?|editors?)\b", "", s, flags=re.I)
    s = RE_CO_PREFIX.sub("", s)
    s = re.sub(r"\bco-?\s*[:\-]\s*", "", s, flags=re.I)
    return normalize_spaces(s).strip(" ,;:-")


def strip_honorifics(s: str) -> str:
    cleaned = RE_HONORIFIC.sub("", s)
    cleaned = re.sub(r"\s*,\s*,\s*", ", ", cleaned)
    cleaned = re.sub(r"\s*,\s*\.", ",", cleaned)
    cleaned = re.sub(r"\s*,\s*", ", ", cleaned)
    cleaned = re.sub(r"\s+,", ",", cleaned)
    return normalize_spaces(cleaned).strip(" ,;:-")


def parse_personal_name(name):
    name = strip_role_words(name)
    name = strip_honorifics(name)
    name = normalize_spaces(name).strip(" ,;")
    if not name:
        return "", "", ""
    if not re.search(r"[A-Za-z]", name):
        return name, "", ""
    name = re.sub(r"\(.*?\)", "", name).strip()
    parts = name.split()

    honorific = ""
    suffix = ""

    while parts and parts[0].lower() in HONORIFICS:
        honorific = HONORIFICS[parts[0].lower()]
        parts = parts[1:]

    while parts and parts[-1].lower().strip(".") in SUFFIXES:
        key = parts[-1].lower().strip(".")
        suffix = (SUFFIXES[key] + (" " + suffix if suffix else "")).strip()
        parts = parts[:-1]

    if not parts:
        return "", honorific, suffix

    joined = " ".join(parts)
    if "," in joined:
        last, first = [p.strip() for p in joined.split(",", 1)]
        main = f"{last.title()}, {first}"
    else:
        last = parts[-1].title()
        firsts = parts[:-1]
        firsts = [w.upper() if len(w) == 1 else w.capitalize() for w in firsts]
        main = f"{last}, {' '.join(firsts)}".strip()

    return main, honorific, suffix


def format_relator(role: str) -> str:
    if not role:
        return ""
    role = role.strip().lower()
    if role in {"author", "editor"}:
        return role
    return role


def clean_name_token(token: str) -> str:
    token = normalize_spaces(token)
    token = re.sub(r"\b\.\b", "", token)
    token = re.sub(r",\s*\.", ",", token)
    token = re.sub(r"\s*,\s*", ", ", token)
    token = re.sub(r"\s+,", ",", token)
    return token.strip(" ,;")


def build_personal_name_field(tag: str, name: str, role: str):
    relator = format_relator(role)
    cleaned_name = clean_name_token(name)
    line = f"={tag}  1\\$a{cleaned_name}"
    if relator:
        line += f"$e{relator}"
    if not _ends_with_terminal_punct(line):
        line += "."
    return line + "\n"


def build_corporate_name_field(tag: str, name: str, role: str):
    relator = format_relator(role)
    corp = normalize_spaces(name).strip(" ,;")
    line = f"={tag}  2\\$a{corp}"
    if relator:
        line += f"$e{relator}"
    if not _ends_with_terminal_punct(line):
        line += "."
    return line + "\n"


def split_on_honorifics(text: str):
    if len(RE_HONORIFIC.findall(text)) <= 1:
        return [text]
    parts = [
        p.strip()
        for p in re.split(r"\s+(?=(dr\.|prof\.|mr\.|mrs\.|ms\.|sir)\b)", text, flags=re.I)
        if p.strip()
    ]
    merged = []
    i = 0
    while i < len(parts):
        part = parts[i]
        if RE_HONORIFIC.fullmatch(part) and i + 1 < len(parts):
            merged.append(f"{part} {parts[i + 1]}".strip())
            i += 2
        else:
            merged.append(part)
            i += 1
    return merged


def split_on_initial_sequences(text: str):
    pattern = re.compile(r"(?:[A-Z]\.\s*){1,3}[A-Z][a-z]+(?:\s+[A-Z][a-z]+)?")
    matches = [m.group(0).strip() for m in pattern.finditer(text)]
    if len(matches) >= 2:
        return matches
    if text.count(",") >= 2:
        parts = [p.strip() for p in text.split(",") if p.strip()]
        if len(parts) >= 3:
            return parts
    return [text]


def split_on_surname_initial_block(text: str):
    m = re.match(r"^([A-Z][a-z]+)\s+((?:[A-Z]\.\s*){1,3}[A-Z][a-z]+)$", text.strip())
    if m:
        return [m.group(1), m.group(2)]
    return [text]


def split_on_commas_as_people(text: str):
    if text.count(",") < 2:
        return [text]
    parts = [p.strip() for p in text.split(",") if p.strip()]
    if len(parts) >= 4 and len(parts) % 2 == 0 and all(len(parts[i].split()) == 1 for i in range(0, len(parts), 2)):
        grouped = []
        for i in range(0, len(parts), 2):
            grouped.append(f"{parts[i]}, {parts[i + 1]}")
        return grouped
    if len(parts) >= 3 and sum(1 for p in parts if " " in p) >= 2:
        return parts
    return [text]


def split_names(raw: str):
    s = normalize_spaces(raw)
    if not s:
        return []

    s = re.sub(r"\bco-?\s*[:\-]\s*", "", s, flags=re.I)
    s = re.sub(r"\s*,\s*,\s*", ";", s)

    if ";" in s:
        return [p.strip() for p in RE_SPLIT_NAMES.split(s) if p.strip()]

    if "&" in s or RE_AND.search(s):
        s = s.replace("&", ";")
        s = RE_AND.sub(";", s)
        return [p.strip() for p in RE_SPLIT_NAMES.split(s) if p.strip()]

    if s.count(",") >= 2:
        parts = [p.strip() for p in s.split(",") if p.strip()]
        if len(parts) >= 4 and len(parts) % 2 == 0 and all(len(parts[i].split()) == 1 for i in range(0, len(parts), 2)):
            grouped = [f"{parts[i]}, {parts[i + 1]}" for i in range(0, len(parts), 2)]
            return [clean_name_token(x) for x in grouped if x]
        if len(parts) >= 3 and sum(1 for p in parts if " " in p) >= 2:
            return [clean_name_token(p) for p in parts if p]

    expanded = []
    for chunk in split_on_honorifics(s):
        for piece in split_on_surname_initial_block(chunk):
            expanded.extend(split_on_initial_sequences(piece))

    cleaned = []
    for token in expanded:
        cleaned.extend(split_on_commas_as_people(token))
    return [clean_name_token(p) for p in cleaned if p]


def extract_contributors(author_editor_raw: str):
    s = normalize_spaces(author_editor_raw)
    if not s:
        return [], []

    s = strip_role_words(s)
    s = strip_honorifics(s)

    matches = list(RE_ROLE.finditer(s))
    authors, editors = [], []

    if not matches:
        tokens = [strip_role_words(normalize_spaces(x)).strip(" ,;") for x in split_names(s)]
        authors = [t for t in tokens if t]
        return authors, editors

    spans = []
    for i, m in enumerate(matches):
        role = m.group(1).lower().replace("-", "")
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(s) else len(s)
        spans.append((role, s[start:end]))

    for role, chunk in spans:
        parts = [strip_role_words(normalize_spaces(x)).strip(" ,;") for x in split_names(chunk)]
        parts = [p for p in parts if p]
        if "editor" in role:
            editors.extend(parts)
        else:
            authors.extend(parts)

    return authors, editors


# ============================================================
# 245 helpers + enhanced builder
# ============================================================
_INITIAL_ARTICLES = [
    "a","an","the","le","la","les","l'","un","une","des","der","die","das",
    "ein","eine","einer","eines","einem","einen","el","los","las","una",
    "unos","unas","il","lo","i","gli"
]


def _extract_medium(title: str):
    t = normalize_spaces(title)
    if not t:
        return t, ""
    m = re.search(r"\s(\[[^\]]+\])", t)
    if not m:
        return t, ""
    medium = m.group(1).strip()
    t2 = (t[: m.start(1)] + t[m.end(1):]).strip()
    return normalize_spaces(t2), medium


def _split_title_a_b(title: str):
    t = normalize_spaces(title)
    if not t:
        return "", "", ""

    if " /" in t:
        t = t.split(" /", 1)[0].strip()
    elif "/" in t and re.search(r"\s/\s", t):
        t = re.split(r"\s/\s", t, maxsplit=1)[0].strip()

    colon_pos = t.find(":")
    eq_pos = t.find("=")

    cut = None
    delim = ""
    if colon_pos != -1 and (eq_pos == -1 or colon_pos < eq_pos):
        cut = colon_pos
        delim = ":"
    elif eq_pos != -1:
        cut = eq_pos
        delim = "="

    if cut is None:
        return t.strip(), "", ""

    a = t[:cut].strip()
    b = t[cut + 1:].strip()
    return a, b, delim


def _compute_nonfiling(title_a: str):
    if not title_a:
        return "0"
    t = title_a.lstrip()
    low = t.lower()

    if low.startswith("l'"):
        count = 2
        if len(t) > 2 and t[2] == " ":
            count += 1
        return str(min(count, 9))

    for art in sorted(_INITIAL_ARTICLES, key=len, reverse=True):
        if art == "l'":
            continue
        if low.startswith(art + " "):
            return str(min(len(art) + 1, 9))
    return "0"


def _split_out_author_from_title(title_raw: str):
    t = normalize_spaces(title_raw)
    if not t:
        return "", ""
    m = RE_TITLE_AUTHOR.search(t)
    if not m:
        return t, ""
    author = normalize_spaces(m.group(1)).strip(" .;/")
    t2 = t[: m.start()].strip(" /;,:-")
    return normalize_spaces(t2), author


def _extract_vol_and_part(title_raw: str):
    t = normalize_spaces(title_raw)
    if not t:
        return "", "", ""

    vol_no = ""
    m = RE_VOL_PAREN.search(t)
    if m:
        vol_no = m.group(1)
        t = RE_VOL_PAREN.sub("", t).strip(" .;/,:-")

    if not vol_no:
        m = RE_VOL_INLINE.search(t)
        if m:
            vol_no = m.group(1)
            t = (t[: m.start()] + t[m.end():]).strip(" .;/,:-")

    part_no = ""
    mp = RE_PART_PAREN.search(t)
    if mp:
        part_no = normalize_part_number(mp.group(1), mp.group(2))
        t = RE_PART_PAREN.sub("", t).strip(" .;/,:-")

    if not part_no:
        mp = RE_PART_INLINE.search(t)
        if mp:
            part_no = normalize_part_number(mp.group(1), mp.group(2))
            t = (t[: mp.start()] + t[mp.end():]).strip(" .;/,:-")

    return normalize_spaces(t), vol_no, part_no


def build_245_field_enhanced(title_raw: str, stmt_resp_col: str, has_1xx: bool):
    t1, author_from_title = _split_out_author_from_title(title_raw)
    t2, vol_no, part_no = _extract_vol_and_part(t1)
    t3, medium = _extract_medium(t2)

    a, b, delim = _split_title_a_b(t3)
    if not a:
        a = normalize_spaces(t3)

    ind1 = "1" if has_1xx else "0"
    ind2 = _compute_nonfiling(a)

    parts = [f"=245  {ind1}{ind2}"]

    a_clean = a.strip()
    if (vol_no or part_no) and a_clean and a_clean[-1] not in ".!?":
        a_clean += "."
    parts.append(f"$a{a_clean}")

    if vol_no:
        parts.append(f"$nVol. {vol_no}")
    if part_no:
        parts.append(f"$n{part_no}")

    if medium:
        parts.append(f"$h{medium}")

    if b:
        if delim == "=":
            parts.append(f" =$b{b.strip()}")
        else:
            parts.append(f" :$b{b.strip()}")

    # --- $c only ---
    c_col = clean_resp_text(stmt_resp_col)
    c_title = clean_resp_text(author_from_title)
    if c_title and c_col:
        c_final = c_col if c_title.lower() == c_col.lower() else f"{c_col} ; {c_title}"
    else:
        c_final = c_title or c_col

    if c_final:
        c_final = normalize_245c_personal_names(c_final)  # ONLY affects 245 $c
        parts.append(f" /$c{c_final.strip(' .')}")

    line = "".join(parts).rstrip()
    if not _ends_with_terminal_punct(line):
        line += "."
    return line + "\n"


# ============================================================
# RDA 33X
# ============================================================
def classify_product_form(product_form: str) -> str:
    pf = normalize_spaces(product_form).lower()
    if any(k in pf for k in ["e-book", "ebook", "digital", "online", "download", "electronic", "e-book reader"]):
        return "electronic"
    if "audio" in pf:
        return "audio"
    return "print"


def rda_33x_fields(form_class: str):
    if form_class == "electronic":
        return (
            "=336  \\\\$atext$2rdacontent\n",
            "=337  \\\\$acomputer$2rdamedia\n",
            "=338  \\\\$aonline resource$2rdacarrier\n",
        )
    if form_class == "audio":
        return (
            "=336  \\\\$aspoken word$2rdacontent\n",
            "=337  \\\\$aaudio$2rdamedia\n",
            "=338  \\\\$aonline resource$2rdacarrier\n",
        )
    return (
        "=336  \\\\$atext$2rdacontent\n",
        "=337  \\\\$aunmediated$2rdamedia\n",
        "=338  \\\\$avolume$2rdacarrier\n",
    )


def should_emit_041(language_raw: str, lang_code: str) -> bool:
    if lang_code == "und":
        return False
    raw = normalize_spaces(language_raw).lower()
    if not raw:
        return False
    return bool(re.search(r"[;,/&]|\band\b", raw))


# ============================================================
# Publisher normalization (ONLY 264 $b)
# ============================================================
def normalize_publisher_264b(pub: str) -> str:
    p = normalize_spaces(pub)
    if not p:
        return p

    letters = re.sub(r"[^A-Za-z]", "", p)
    if not letters:
        return p

    if not letters.isupper():
        return p

    if RE_HAS_DIGIT.search(p):
        return p

    if RE_HAS_SYMBOL.search(p):
        return p

    if len(letters) <= 4:
        return p

    words = p.split()
    fixed = []
    for w in words:
        w_letters = re.sub(r"[^A-Za-z]", "", w)
        if w_letters.isupper() and len(w_letters) <= 4:
            fixed.append(w.upper())
        else:
            fixed.append(w.capitalize())
    return " ".join(fixed)


# ============================================================
# Column mapping (YOUR CURRENT HEADERS)
# ============================================================
COLUMN_RENAME = {
    "Book Title": "Book_Title",
    "ISBN": "ISBN",
    "Product Form": "Product_Form",
    "Language": "Language",
    "Applicant Type": "Applicant_Type",
    "Name of Publishing Agency/Publisher": "Publisher_Name",
    "Name of Author/Editor": "Author_Editor",
    "Publication Date": "Publication_Date",
}

REQUIRED_INTERNAL = [
    "Book_Title",
    "ISBN",
    "Product_Form",
    "Language",
    "Applicant_Type",
    "Publisher_Name",
    "Author_Editor",
    "Publication_Date",
]


# ============================================================
# Worker thread
# ============================================================
def _read_input_file(path: str):
    pd = _pd()
    if path.lower().endswith(".csv"):
        return pd.read_csv(path, dtype=str).fillna("")
    return pd.read_excel(path, dtype=str, engine="openpyxl").fillna("")


def convert_worker(input_files, out_base_path, output_dir, single_output, write_mrc, write_mrk, org_code):
    global cancel_flag
    try:
        total = 0
        frames = []
        for path in input_files:
            df = _read_input_file(path)
            df = df.rename(columns={c: COLUMN_RENAME[c] for c in df.columns if c in COLUMN_RENAME})
            missing = [c for c in REQUIRED_INTERNAL if c not in df.columns]
            if missing:
                raise ValueError(f"Missing required column(s) in {path}: " + ", ".join(missing))
            df = df[REQUIRED_INTERNAL]
            frames.append((path, df))
            total += len(df)

        root.after(0, lambda: init_progress(total))

        buf_mrc = []
        processed = 0

        def emit_added_entry(name_str: str, role: str) -> str:
            if looks_corporate(name_str):
                return build_corporate_name_field("710", name_str, role)
            n, _, _ = parse_personal_name(name_str)
            if n:
                return build_personal_name_field("700", n, role)
            return ""

        def write_records(df, f_mrc, f_mrk):
            nonlocal processed, buf_mrc
            for r in df.itertuples(index=False, name=None):
                if cancel_flag:
                    break

                (
                    title_raw,
                    isbn_raw,
                    product_form,
                    language_raw,
                    applicant_type,
                    publisher_raw,
                    author_editor_raw,
                    pub_date_raw,
                ) = r

                edition_stmt = extract_edition_from_title(title_raw)
                series_a, series_v, series_x = extract_series_from_title(title_raw)

                title_for_245 = title_raw
                if edition_stmt:
                    title_for_245 = remove_edition_from_title(title_for_245)
                if series_a:
                    title_for_245 = remove_series_from_title(title_for_245)

                title_for_245 = normalize_title_punct(title_for_245)
                title_for_245 = maybe_title_case(title_for_245)

                isbn = clean_isbn(isbn_raw)
                lang = normalize_language(language_raw)
                year = extract_year_from_pub_date(pub_date_raw)
                authors, editors = extract_contributors(author_editor_raw)

                rec = []
                rec.append("=LDR  00000nam a2200000 a 4500\n")
                rec.append(f"=008  {build_008(year, lang)}\n")
                rec.append(f"=040  \\\\$a{org_code}$beng$eRDA$c{org_code}\n")
                rec.append("=588  \\\\$aDescription based on ISBN registration metadata from isbn.gov.in.\n")

                if isbn:
                    rec.append(f"=020  \\\\$a{isbn}\n")

                has_main = False
                if authors:
                    first_raw = authors[0]
                    if looks_corporate(first_raw):
                        rec.append(build_corporate_name_field("110", first_raw, "author"))
                        has_main = True
                    else:
                        n, _, _ = parse_personal_name(first_raw)
                        if n:
                            rec.append(build_personal_name_field("100", n, "author"))
                            has_main = True
                elif editors:
                    first_raw = editors[0]
                    if looks_corporate(first_raw):
                        rec.append(build_corporate_name_field("110", first_raw, "editor"))
                        has_main = True
                    else:
                        n, _, _ = parse_personal_name(first_raw)
                        if n:
                            rec.append(build_personal_name_field("100", n, "editor"))
                            has_main = True

                rec.append(build_245_field_enhanced(title_for_245, author_editor_raw, has_main))

                if edition_stmt:
                    line = f"=250  \\\\$a{edition_stmt.strip()}"
                    if not _ends_with_terminal_punct(line):
                        line += "."
                    rec.append(line + "\n")

                place_text = "India"
                pub = normalize_spaces(publisher_raw)
                pub = normalize_publisher_264b(pub)
                y_ok = bool(re.fullmatch(r"(19|20)\d{2}", year))

                if not pub:
                    pub = "[publisher not identified]"

                if y_ok:
                    rec.append(f"=264  \\1$a{place_text} :$b{pub},$c{year}.\n")
                else:
                    rec.append(f"=264  \\1$a{place_text} :$b{pub}.\n")

                if series_a:
                    line = f"=490  0\\$a{series_a}"
                    if series_v:
                        line += f"$v{series_v}"
                    if series_x:
                        line += f"$x{series_x}"
                    if not _ends_with_terminal_punct(line):
                        line += "."
                    rec.append(line + "\n")

                if applicant_type:
                    at = normalize_spaces(applicant_type)
                    line = f"=590  \\\\$aISBN applicant type: {at}"
                    if not _ends_with_terminal_punct(line):
                        line += "."
                    rec.append(line + "\n")

                for a in authors[1:]:
                    line = emit_added_entry(a, "author")
                    if line:
                        rec.append(line)

                for e in editors[1:]:
                    line = emit_added_entry(e, "editor")
                    if line:
                        rec.append(line)

                if should_emit_041(language_raw, lang):
                    rec.append(f"=041  0\\$a{lang}\n")

                if product_form:
                    pf = normalize_spaces(product_form)
                    rec.append(f"=655  \\7$a{pf}$2local\n")

                # ✅ 300 REMOVED (no extent data available/reliable)

                form_class = classify_product_form(product_form)
                f336, f337, f338 = rda_33x_fields(form_class)
                rec.append(f336)
                rec.append(f337)
                rec.append(f338)
                rec.append("\n")

                if f_mrk:
                    f_mrk.write(mrk_record_text(rec))

                if f_mrc:
                    buf_mrc.append(encode_marc_record(rec))
                    if len(buf_mrc) % WRITE_FLUSH_EVERY == 0:
                        f_mrc.write(b"".join(buf_mrc))
                        buf_mrc.clear()

                processed += 1
                if processed % UI_UPDATE_EVERY == 0 or processed == total:
                    root.after(0, lambda x=processed, t=total: update_progress(x, t))

        if single_output:
            base = out_base_path
            mrc_path = base + ".mrc" if write_mrc else None
            mrk_path = base + ".mrk" if write_mrk else None

            f_mrc = open(mrc_path, "wb") if mrc_path else None
            f_mrk = open(mrk_path, "w", encoding="utf-8", newline="\n") if mrk_path else None

            try:
                for _, df in frames:
                    if cancel_flag:
                        break
                    write_records(df, f_mrc, f_mrk)

                if f_mrc and buf_mrc and not cancel_flag:
                    f_mrc.write(b"".join(buf_mrc))
                buf_mrc.clear()
            finally:
                if f_mrc:
                    f_mrc.close()
                if f_mrk:
                    f_mrk.close()

        else:
            for path, df in frames:
                if cancel_flag:
                    break
                base_name = os.path.splitext(os.path.basename(path))[0]

                mrc_path = os.path.join(output_dir, f"{base_name}.mrc") if write_mrc else None
                mrk_path = os.path.join(output_dir, f"{base_name}.mrk") if write_mrk else None

                f_mrc = open(mrc_path, "wb") if mrc_path else None
                f_mrk = open(mrk_path, "w", encoding="utf-8", newline="\n") if mrk_path else None

                try:
                    write_records(df, f_mrc, f_mrk)
                    if f_mrc and buf_mrc and not cancel_flag:
                        f_mrc.write(b"".join(buf_mrc))
                    buf_mrc.clear()
                finally:
                    if f_mrc:
                        f_mrc.close()
                    if f_mrk:
                        f_mrk.close()

        root.after(0, lambda: finish_ui(cancelled=cancel_flag))

    except Exception as e:
        root.after(0, lambda msg=str(e): show_error(msg))


# ============================================================
# GUI callbacks
# ============================================================
def init_progress(total):
    progress["maximum"] = total
    progress["value"] = 0
    status_var.set(f"Processing 0/{total} ...")
    btn_convert.config(state="disabled")
    btn_cancel.config(state="normal")


def update_progress(done, total):
    progress["value"] = done
    status_var.set(f"Processed {done}/{total}")


def finish_ui(cancelled=False):
    btn_convert.config(state="normal")
    btn_cancel.config(state="disabled")
    if cancelled:
        status_var.set("Cancelled.")
        messagebox.showinfo("Cancelled", "Conversion cancelled.")
    else:
        status_var.set("Done.")
        messagebox.showinfo("SUCCESS", "Output created successfully.")


def show_error(msg):
    btn_convert.config(state="normal")
    btn_cancel.config(state="disabled")
    status_var.set("Error.")
    messagebox.showerror("ERROR", msg)


def start_convert():
    global cancel_flag, worker_thread
    cancel_flag = False

    org_code = normalize_spaces(org_code_var.get())
    if not org_code:
        messagebox.showerror("ERROR", "Please enter Org code for 040 (e.g., KU).")
        return

    write_mrc = bool(write_mrc_var.get())
    write_mrk = bool(write_mrk_var.get())
    if not (write_mrc or write_mrk):
        messagebox.showerror("ERROR", "Select at least one output format: .mrc and/or .mrk")
        return

    input_files = filedialog.askopenfilenames(filetypes=[("Excel/CSV", "*.xlsx *.csv")])
    if not input_files:
        return

    out_base_path = ""
    output_dir = ""

    if single_output_var.get():
        picked = filedialog.asksaveasfilename(
            defaultextension="",
            filetypes=[("Base name (no extension)", "*.*")],
            title="Choose base output filename (no extension). Example: output_2016_2025",
        )
        if not picked:
            return
        out_base_path = os.path.splitext(picked)[0]
    else:
        output_dir = filedialog.askdirectory()
        if not output_dir:
            return

    worker_thread = threading.Thread(
        target=convert_worker,
        args=(input_files, out_base_path, output_dir, single_output_var.get(), write_mrc, write_mrk, org_code),
        daemon=True,
    )
    worker_thread.start()


def cancel_convert():
    global cancel_flag
    cancel_flag = True
    status_var.set("Cancelling... (will stop shortly)")


# ============================================================
# GUI
# ============================================================
def main():
    global root, progress, status_var, btn_convert, btn_cancel
    global single_output_var, dark_mode_var, write_mrc_var, write_mrk_var, org_code_var

    root = tk.Tk()
    root.title("ISBN to MARC21 Converter")
    root.geometry("1020x430")

    style = ttk.Style()
    style.theme_use("clam")

    dark_mode_var = tk.BooleanVar(value=False)
    single_output_var = tk.BooleanVar(value=True)
    write_mrc_var = tk.BooleanVar(value=True)
    write_mrk_var = tk.BooleanVar(value=True)
    org_code_var = tk.StringVar(value="KU")

    def apply_theme():
        dark = dark_mode_var.get()
        bg = "#1e1e1e" if dark else "#f5f5f5"
        fg = "#f5f5f5" if dark else "#1e1e1e"
        button_bg = "#333333" if dark else "#e0e0e0"
        progress_bg = "#2a2a2a" if dark else "#ffffff"

        root.configure(bg=bg)
        style.configure("TFrame", background=bg)
        style.configure("TLabel", background=bg, foreground=fg)
        style.configure("TButton", background=button_bg, foreground=fg)
        style.map("TButton", background=[("active", button_bg)])
        style.configure("TCheckbutton", background=bg, foreground=fg)
        style.configure("Horizontal.TProgressbar", background="#4caf50", troughcolor=progress_bg)

    frm = ttk.Frame(root, padding=15)
    frm.pack(fill=tk.BOTH, expand=True)

    ttk.Label(frm, text="Excel to MARC21 Converter", font=("Arial", 13, "bold")).pack(anchor="w")

    org_row = ttk.Frame(frm)
    org_row.pack(anchor="w", pady=(8, 0))
    ttk.Label(org_row, text="040 $a / $c Org code:").pack(side="left")
    ttk.Entry(org_row, textvariable=org_code_var, width=12).pack(side="left", padx=8)
    ttk.Label(org_row, text="(Example: KU)").pack(side="left")

    toggle_row = ttk.Frame(frm)
    toggle_row.pack(anchor="w", pady=(10, 0))
    ttk.Checkbutton(toggle_row, text="Dark mode", variable=dark_mode_var, command=apply_theme).pack(side="left")
    ttk.Checkbutton(toggle_row, text="Single output (merge all inputs)", variable=single_output_var).pack(side="left", padx=12)

    fmt_row = ttk.Frame(frm)
    fmt_row.pack(anchor="w", pady=(8, 0))
    ttk.Label(fmt_row, text="Output formats:").pack(side="left")
    ttk.Checkbutton(fmt_row, text=".mrc (binary)", variable=write_mrc_var).pack(side="left", padx=10)
    ttk.Checkbutton(fmt_row, text=".mrk (text)", variable=write_mrk_var).pack(side="left", padx=10)

    btn_row = ttk.Frame(frm)
    btn_row.pack(anchor="w", pady=12)

    btn_convert = ttk.Button(btn_row, text="Start", command=start_convert)
    btn_convert.pack(side="left")

    btn_cancel = ttk.Button(btn_row, text="Stop", command=cancel_convert, state="disabled")
    btn_cancel.pack(side="left", padx=10)

    progress = ttk.Progressbar(frm, length=960, mode="determinate")
    progress.pack(pady=5, anchor="w")

    status_var = tk.StringVar(value="Ready.")
    ttk.Label(frm, textvariable=status_var).pack(anchor="w", pady=(5, 0))

    ttk.Label(
        frm,
        text="Notes: Downloaded the input details from www.isbn.gov.in",
        foreground="gray",
        wraplength=980,
    ).pack(anchor="w", pady=(10, 0))

    apply_theme()
    root.mainloop()


if __name__ == "__main__":
    main()

