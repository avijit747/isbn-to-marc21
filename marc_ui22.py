# marc_ui22.py - v22: rewritten edition (250) rules after the manual audit; otherwise identical to marc_ui21.py
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json
import re
from datetime import datetime
from pathlib import Path
import threading
import os
import time

# =========================
# SPEED/UX TUNING
# =========================
UI_UPDATE_EVERY = 500
WRITE_FLUSH_EVERY = 1000

cancel_flag = False
worker_thread = None

# Shared progress state: the worker thread writes it, the GUI reads it every 250 ms (poll_progress).
PROG = {"phase": "idle", "file_i": 0, "file_n": 0, "file_name": "", "done": 0, "total": 0,
        "t0": 0.0, "t_convert": 0.0, "outputs": []}

# ============================================================
# Precompiled regex
# ============================================================
RE_ISBN = re.compile(r"[^0-9Xx]")
RE_YEAR = re.compile(r"(19|20)\d{2}")
RE_SPACES = re.compile(r"\s+")
RE_AND = re.compile(r"\s+\band\b\s+", re.I)
# Role labels as written in the ISBN portal, e.g. "Editor :", "Co-Editor :", "Authors:"
RE_ROLE = re.compile(r"\b(?:co[-\s]?)?(author|editor)s?\s*:\s*", re.I)
RE_EDITED_BY = re.compile(r"^\s*(?:edited|compiled)\s+by\b", re.I)
RE_SPLIT_NAMES = re.compile(r"\s*;\s*")
# Honorific word plus its optional dot (old pattern left a stray "." behind: "Dr." -> ".")
RE_HONORIFIC = re.compile(r"\b(?:dr|prof|mrs|mr|ms|sir|rev|smt)\b\.?", re.I)
# Split point just before an honorific that starts another person's name
RE_HON_START = re.compile(r"\b(?:dr|prof|mrs|mr|ms|rev|smt)(?:\.|,|\s)", re.I)
RE_HON_SPLIT = re.compile(r"\s*[,;]?\s*(?=\b(?:dr|prof|mrs|mr|ms|rev|smt)(?:\.|,|\s))", re.I)
RE_CO_PREFIX = re.compile(r"^\s*co-?\s*[:\-]?\s*", re.I)

# Corporate/body hints (for 110/710 and to avoid casing institutions)
RE_CORP_HINT = re.compile(
    r"\b(university|college|institute|department|faculty|school|"
    r"ministry|government|govt|director|office|committee|society|"
    r"research|centre|center|board|authority|mission|project|"
    r"post office|district|police station|"
    # Address words (road, lane, post, nagar ...) removed: they are also surnames
    # ("Melville Davisson Post", "Mary E. Bradley Lane").
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
# Valid roman numeral only (so "Mill", "Civil", "Did" are not numbers); the
# lookbehind guarantees at least one character was consumed.
ROMAN = r"(?:m{0,3}(?:cm|cd|d?c{0,3})(?:xc|xl|l?x{0,3})(?:ix|iv|v?i{0,3}))(?<=[ivxlcdmIVXLCDM])(?![A-Za-z])"
RE_ROMAN_FULL = re.compile(r"^" + ROMAN + r"$", re.I)
# Roman numbers outside brackets count only at the end of the title (or before ":" etc.),
# so "The Year I Died" is left alone.
TITLE_END = r"(?=\s*(?:$|[:;=/(\[]))"
RE_VOL_PAREN = re.compile(r"\(\s*(?:vol(?:ume)?\.?)\s*([0-9]+|" + ROMAN + r")\s*\)", re.I)
RE_VOL_INLINE = re.compile(
    r"(?:^|[\s,;:-])(?:vol(?:ume)?\.?)\s*(?:([0-9]+)\b|(" + ROMAN + r")" + TITLE_END + r")",
    re.I,
)

# Part/Book/Module patterns -> 245 $n (NOT series)
RE_PART_CHUNK = re.compile(
    r"^\s*(part|book|module|unit|section|semester|term|year)\s*[-\.]?\s*"
    r"([0-9]{1,3}\b|" + ROMAN + r")",
    re.I,
)
RE_PART_PAREN = re.compile(
    r"\(\s*(part|book|module|unit|section|semester|term|year)\s*[-\.]?\s*"
    r"([0-9]{1,3}|" + ROMAN + r")\s*\)",
    re.I,
)
# Inline part numbers only at the end of the title; 1-3 digits so "Book 2025" is not a part.
RE_PART_INLINE = re.compile(
    r"(?:^|[\s,;:-])(part|book|module|unit|section|semester|term|year)\s*"
    r"[-\.]?\s*([0-9]{1,3}\b|" + ROMAN + r")" + TITLE_END,
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


def build_leader(form_class="print"):
    # 06 type: a = language material, i = nonmusical sound recording
    # 17 encoding level: 7 = minimal (machine-generated from registration data)
    # 18 descriptive form: i = ISBD punctuation included (RDA)
    rtype = "i" if form_class in ("audio", "audio_online") else "a"
    return f"00000n{rtype}m a22000007i 4500"


def build_008(year, lang, place_code="ii ", form_class="print"):
    date_entered = today_YYMMDD()
    if re.fullmatch(r"(19|20)\d{2}", str(year)):
        date_type, y = "s", year
    else:
        date_type, y = "n", "uuuu"  # date unknown
    l = lang if re.fullmatch(r"[a-z]{3}", str(lang)) else "und"
    pc = (place_code + "   ")[:3]

    # 008/18-34 (17 positions, index 0 = position 18)
    mid = [" "] * 17
    online = form_class in ("electronic", "audio_online")
    if form_class in ("audio", "audio_online"):
        mid[0:2] = ["n", "n"]  # 18-19 form of composition: not applicable
        mid[2] = "n"           # 20 format of music: not applicable
    if online:
        mid[5] = "o"           # 23 form of item: online
    s = (
        f"{date_entered}"
        f"{date_type}"
        f"{y}"
        f"    "
        f"{pc}"
        + "".join(mid)
        + f"{l}"
        + " "   # 38 modified record
        + "d"   # 39 cataloging source: other (not a national bibliographic agency)
    )
    return (s + (" " * 40))[:40]


def control_fields_006_007(form_class):
    if form_class == "electronic":
        return (
            "=006  m     o  d        \n",  # computer file aspect: online, document
            "=007  cr |||||||||||\n",     # electronic resource, remote
        )
    if form_class == "audio_online":
        return ("=007  cr |||||||||||\n",)
    if form_class == "audio":
        return ("=007  su |||||||||||\n",)  # sound recording, unspecified carrier
    return ()


def isbn_qualifier(product_form, form_class):
    """Value for 020 $q taken from the ONIX product form."""
    pf = normalize_spaces(product_form).lower()
    if not pf or pf in {"book", "other book format", "other point of sale"}:
        return ""
    if form_class == "electronic":
        return "ebook"
    if form_class in ("audio", "audio_online"):
        return "audiobook"
    if pf == "paperback / softback":
        return "paperback"
    return pf


def sort_fields(rec_lines):
    """Leader first, then fields in tag order (stable), then the record separator."""
    ldr = [l for l in rec_lines if l.startswith("=LDR")]
    body = [l for l in rec_lines if l.startswith("=") and not l.startswith("=LDR")]
    body.sort(key=lambda l: l[1:4])
    return ldr + body + ["\n"]


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
# MARC language codes (ISO 639-2/B) keyed by the English names used in the
# isbn.gov.in "Language" column, including the misspellings seen in the data.
DEFAULT_LANG_MAP = {
    # Indian languages
    "english": "eng", "hindi": "hin", "bengali": "ben", "bangali": "ben", "bangla": "ben",
    "marathi": "mar", "urdu": "urd", "tamil": "tam", "telugu": "tel", "kannada": "kan",
    "malayalam": "mal", "gujarati": "guj", "punjabi": "pan", "panjabi": "pan",
    "odia": "ori", "oriya": "ori", "assamese": "asm", "sanskrit": "san", "nepali": "nep",
    "kashmiri": "kas", "konkani": "kok", "manipuri": "mni", "maithili": "mai",
    "rajasthani": "raj", "bhojpuri": "bho", "santali": "sat", "dogri": "doi",
    "sindhi": "snd", "mizo": "lus", "lushai": "lus", "khasi": "kha", "awadhi": "awa",
    "magahi": "mag", "kurukh": "kru", "pali": "pli", "tibetan": "tib", "bodo": "sit",
    "prakrit languages": "pra", "munda languages": "mun", "bihari languages": "bih",
    "himachali languages": "him", "western pahari languages": "him",
    "indic languages": "inc", "indo-european languages": "ine",
    "sino-tibetan languages": "sit", "dravidian languages": "dra",
    # Special codes
    "multiple languages": "mul", "no linguistic content": "zxx", "undetermined": "und",
    # Other languages present in the 2016-2025 data
    "french": "fre", "arabic": "ara", "spanish": "spa", "german": "ger", "italian": "ita",
    "korean": "kor", "chinese": "chi", "russian": "rus", "portuguese": "por",
    "malay": "may", "hungarian": "hun", "swedish": "swe", "persian": "per", "farsi": "per",
    "sinhala": "sin", "sinhalese": "sin", "norwegian": "nor", "polish": "pol",
    "turkish": "tur", "danish": "dan", "tagalog": "tgl", "filipino": "fil",
    "pilipino": "fil", "japanese": "jpn", "hebrew": "heb", "georgian": "geo",
    "indonesian": "ind", "uzbek": "uzb", "ukrainian": "ukr", "czech": "cze",
    "burmese": "bur", "swahili": "swa", "kazakh": "kaz", "tatar": "tat", "bosnian": "bos",
    "dutch": "dut", "hausa": "hau", "igbo": "ibo", "guarani": "grn", "abkhaz": "abk",
    "greek, ancient (to 1453)": "grc", "greek, modern (1453-)": "gre",
    "english, middle (1100-1500)": "enm", "english, old (ca. 450-1100)": "ang",
    "dutch, middle (ca. 1050-1350)": "dum", "egyptian (ancient)": "egy", "elamite": "elx",
    "occitan (post 1500)": "oci",
}


def _lang_key(name: str) -> str:
    return normalize_spaces(str(name).replace("\u2019", "'")).lower()


def _load_iso_639_2_language_map() -> dict:
    # Optional full ISO 639-2 table: put iso_639-2.json (Debian iso-codes format)
    # next to this script on Windows; the Linux system copy is used if present.
    candidates = [
        Path(__file__).with_name("iso_639-2.json"),
        Path("/usr/share/iso-codes/json/iso_639-2.json"),
    ]
    iso_path = next((p for p in candidates if p.exists()), None)
    if iso_path is None:
        return {}
    try:
        data = json.loads(iso_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    lang_map = {}
    for entry in data.get("639-2", []):
        name = _lang_key(entry.get("name") or "")
        code = entry.get("bibliographic") or entry.get("alpha_3")
        if not name or not code:
            continue
        # "Filipino; Pilipino" -> both names and the full string
        for alias in [name] + [a.strip() for a in name.split(";")]:
            if alias:
                lang_map.setdefault(alias, code.lower())
    return lang_map


# v22: ISO 639-2/B codes for further language names found in the registration data. v21 took these from an
# optional iso_639-2.json; built in here so that the output is the same on Windows and Linux.
EXTRA_ISO_LANG_MAP = {
    'achinese': 'ace',
    'acoli': 'ach',
    'adangme': 'ada',
    'afar': 'aar',
    'afrikaans': 'afr',
    'afro-asiatic languages': 'afa',
    'akan': 'aka',
    'albanian': 'alb',
    'aleut': 'ale',
    'algonquian languages': 'alg',
    'amharic': 'amh',
    'angika': 'anp',
    'apache languages': 'apa',
    'aragonese': 'arg',
    'arapaho': 'arp',
    'arawak': 'arw',
    'armenian': 'arm',
    'artificial languages': 'art',
    'asturian; bable; leonese; asturleonese': 'ast',
    'austronesian languages': 'map',
    'avaric': 'ava',
    'avestan': 'ave',
    'aymara': 'aym',
    'azerbaijani': 'aze',
    'balinese': 'ban',
    'baltic languages': 'bat',
    'baluchi': 'bal',
    'bambara': 'bam',
    'bamileke languages': 'bai',
    'banda languages': 'bad',
    'basa': 'bas',
    'bashkir': 'bak',
    'basque': 'baq',
    'beja; bedawiyet': 'bej',
    'belarusian': 'bel',
    'bemba': 'bem',
    'berber languages': 'ber',
    'bikol': 'bik',
    'blin; bilin': 'byn',
    'braj': 'bra',
    'breton': 'bre',
    'bulgarian': 'bul',
    'buriat': 'bua',
    'catalan': 'cat',
    'caucasian languages': 'cau',
    'cebuano': 'ceb',
    'central american indian languages': 'cai',
    'chagatai': 'chg',
    'chamorro': 'cha',
    'chechen': 'che',
    'chibcha': 'chb',
    'chichewa; chewa; nyanja': 'nya',
    'chuvash': 'chv',
    'corsican': 'cos',
    'creoles and pidgins, french-based': 'cpf',
    'crimean turkish; crimean tatar': 'crh',
    'croatian': 'hrv',
    'cushitic languages': 'cus',
    'dakota': 'dak',
    'dargwa': 'dar',
    'delaware': 'del',
    'dinka': 'din',
    'divehi; dhivehi; maldivian': 'div',
    'dogrib': 'dgr',
    'duala': 'dua',
    'dyula': 'dyu',
    'dzongkha': 'dzo',
    'eastern frisian': 'frs',
    'efik': 'efi',
    'ekajuk': 'eka',
    'erzya': 'myv',
    'esperanto': 'epo',
    'estonian': 'est',
    'fang': 'fan',
    'fanti': 'fat',
    'faroese': 'fao',
    'fijian': 'fij',
    'finnish': 'fin',
    'friulian': 'fur',
    'galibi carib': 'car',
    'galician': 'glg',
    'ganda': 'lug',
    'german, middle high (ca. 1050-1500)': 'gmh',
    'german, old high (ca. 750-1050)': 'goh',
    'germanic languages': 'gem',
    'gilbertese': 'gil',
    'gondi': 'gon',
    'gorontalo': 'gor',
    'gothic': 'got',
    'grebo': 'grb',
    "gwich'in": 'gwi',
    'haida': 'hai',
    'hawaiian': 'haw',
    'herero': 'her',
    'hiligaynon': 'hil',
    'hiri motu': 'hmo',
    'hittite': 'hit',
    'hmong; mong': 'hmn',
    'iban': 'iba',
    'icelandic': 'ice',
    'inari sami': 'smn',
    'interlingua (international auxiliary language association)': 'ina',
    'inuktitut': 'iku',
    'iranian languages': 'ira',
    'irish': 'gle',
    'javanese': 'jav',
    'kabyle': 'kab',
    'kalâtdlisut; greenlandic': 'kal',
    'kamba': 'kam',
    'kanuri': 'kau',
    'karelian': 'krl',
    'kashubian': 'csb',
    'kawi': 'kaw',
    'kinyarwanda': 'kin',
    'kirghiz; kyrgyz': 'kir',
    'komi': 'kom',
    'kurdish': 'kur',
    'ladino': 'lad',
    'land dayak languages': 'day',
    'latin': 'lat',
    'latvian': 'lav',
    'limburgish': 'lim',
    'lingala': 'lin',
    'lithuanian': 'lit',
    'luba-katanga': 'lub',
    'lunda': 'lun',
    'luo (kenya and tanzania)': 'luo',
    'luxembourgish; letzeburgesch': 'ltz',
    'macedonian': 'mac',
    'madurese': 'mad',
    'makasar': 'mak',
    'malagasy': 'mlg',
    'maltese': 'mlt',
    'mandar': 'mdr',
    'mandingo': 'man',
    'manobo languages': 'mno',
    'manx': 'glv',
    'maori': 'mao',
    'mapudungun; mapuche': 'arn',
    'mari': 'chm',
    'marshallese': 'mah',
    'marwari': 'mwr',
    'masai': 'mas',
    'mayan languages': 'myn',
    "mi'kmaq; micmac": 'mic',
    'moksha': 'mdf',
    'moldavian; moldovan': 'rum',
    'mon-khmer languages': 'mkh',
    'mongolian': 'mon',
    "n'ko": 'nqo',
    'nahuatl languages': 'nah',
    'ndebele, north': 'nde',
    'ndebele, south': 'nbl',
    'neapolitan': 'nap',
    'newari; nepal bhasa': 'new',
    'niger-kordofanian languages': 'nic',
    'niuean': 'niu',
    'nogai': 'nog',
    'north american indian languages': 'nai',
    'nzima': 'nzi',
    'official aramaic; imperial aramaic (700-300 bce)': 'arc',
    'ojibwa': 'oji',
    'oromo': 'orm',
    'ossetian; ossetic': 'oss',
    'otomian languages': 'oto',
    'pahlavi': 'pal',
    'palauan': 'pau',
    'pangasinan': 'pag',
    'papiamento': 'pap',
    'papuan languages': 'paa',
    'philippine languages': 'phi',
    'provençal, old (to 1500); occitan, old (to 1500)': 'pro',
    'pushto; pashto': 'pus',
    'quechua': 'que',
    'romance languages': 'roa',
    'romanian': 'rum',
    'romansh': 'roh',
    'romany': 'rom',
    'rundi': 'run',
    'salishan languages': 'sal',
    'samaritan aramaic': 'sam',
    'sami languages': 'smi',
    'samoan': 'smo',
    'sandawe': 'sad',
    'sango': 'sag',
    'sardinian': 'srd',
    'sasak': 'sas',
    'scottish gaelic': 'gla',
    'serbian': 'srp',
    'shan': 'shn',
    'shona': 'sna',
    'sichuan yi; nuosu': 'iii',
    'sicilian': 'scn',
    'sign languages': 'sgn',
    'slavic languages': 'sla',
    'slovak': 'slo',
    'slovenian': 'slv',
    'somali': 'som',
    'southern altai': 'alt',
    'southern sami': 'sma',
    'sranan tongo': 'srn',
    'sukuma': 'suk',
    'sundanese': 'sun',
    'susu': 'sus',
    'swazi; swati': 'ssw',
    'syriac': 'syr',
    'tahitian': 'tah',
    'tai languages': 'tai',
    'tajik; tajiki persian': 'tgk',
    'tamashek': 'tmh',
    'tetum': 'tet',
    'thai': 'tha',
    'tsonga': 'tso',
    'udmurt': 'udm',
    'uncoded languages': 'mis',
    'venda': 'ven',
    'vietnamese': 'vie',
    'wakashan languages': 'wak',
    'welsh': 'wel',
}

LANG_MAP = {
    **_load_iso_639_2_language_map(),
    **EXTRA_ISO_LANG_MAP,
    **DEFAULT_LANG_MAP,
}


def normalize_language(lang):
    if _pd().isna(lang) or not str(lang).strip():
        return "und"
    s = _lang_key(lang)
    if s in LANG_MAP:
        return LANG_MAP[s]
    if len(s) == 3 and s.isalpha():
        if s == "fra":
            return "fre"
        return s
    # "Filipino; Pilipino", "Dari; Afghan Persian": try each alias
    for alias in s.split(";"):
        code = LANG_MAP.get(alias.strip())
        if code:
            return code
    return "und"


# ============================================================
# Title casing (safer, improved for "mostly caps" titles)
# ============================================================
MINOR_WORDS = {"and", "or", "the", "a", "an", "in", "on", "for", "of", "to", "by", "at", "with"}


# Upper-case tokens kept as acronyms when the source has them in capitals.
# Ambiguous English words (IT, US, AM, NET, GATE) are deliberately left out.
ACRONYMS = {
    "ISC", "ICSE", "CBSE", "NCERT", "UPSC", "SSC", "NEET", "JEE", "IIT", "AI", "UGC",
    "GK", "MBA", "BBA", "BCA", "MCA", "BSC", "MSC", "BCOM", "MCOM", "NEP", "CUET",
    "RRB", "IAS", "PCS", "TET", "CTET", "PSC", "BPSC", "MPSC", "UPPSC", "RPSC", "KVS",
    "NVS", "DSSSB", "NDA", "CDS", "PHP", "HTML", "SQL", "CSS", "USA", "UK", "UN",
    "COVID", "DNA", "RNA", "ICT", "IPR", "GST", "NGO", "CSR", "HRM", "ML", "IOT",
    "LLB", "LLM",
}


def _case_piece(p: str, is_first: bool) -> str:
    m = re.match(r"^([^A-Za-z0-9]*)(.*?)([^A-Za-z0-9]*)$", p)
    pre, core, post = m.group(1), m.group(2), m.group(3)
    if not core or re.search(r"\d", core) or not re.search(r"[A-Za-z]", core):
        return p
    if core.isupper() and (core in ACRONYMS or RE_ROMAN_FULL.fullmatch(core)):
        return pre + core + post
    low = core.lower()
    if low in MINOR_WORDS and not is_first:
        return pre + low + post
    return pre + low[:1].upper() + low[1:] + post


def smart_title_case(title: str) -> str:
    t = normalize_spaces(title)
    if not t:
        return ""
    if not re.search(r"[A-Za-z]", t):
        return t
    out = []
    for i, w in enumerate(t.split()):
        pieces = w.split("-")
        out.append("-".join(_case_piece(p, i == 0 and j == 0) for j, p in enumerate(pieces)))
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
    t = re.sub(r"\(\s+", "(", t)
    t = re.sub(r"\s+\)", ")", t)
    t = re.sub(r"(?<=[^\s(\[/-])\(", " (", t)
    t = re.sub(r"\)(?=[^\s.,;:)\]])", ") ", t)
    t = re.sub(r",\s*,", ",", t)
    t = re.sub(r"\s*,\s*$", "", t)
    return normalize_spaces(t)


# ============================================================
# Edition (250) — ONLY from Book Title  (rewritten in v22)
# ============================================================
# The ISBN portal appends "(Edition1)", "(Edition 2)", "(EditionFirst Edition)", "(Edition2023)" to titles.
# RDA 250 is made only for a 2nd or later edition, or for a descriptive edition ("Revised edition").
# v22 changes (from the manual audit of 400 records):
#   * "1st Edition", "First Edition", "IST EDITION", "I" -> no 250 (v21 copied them into 250);
#   * a year in the edition field ("2023") -> no 250 (v21 wrote "2023 edition");
#   * ordinal words ("Second", "Fourth") and editions stated in the title text are recognised,
#     and the title text wins over a portal value of 1; the statement is removed from the title proper.
# Set True to emit "1st edition" for first editions.
EMIT_NUMERIC_FIRST_EDITION = False

ED_WORD_ORD = {
    "first": 1, "second": 2, "third": 3, "fourth": 4, "fifth": 5, "sixth": 6, "seventh": 7, "eighth": 8,
    "ninth": 9, "tenth": 10, "eleventh": 11, "twelfth": 12, "thirteenth": 13, "fourteenth": 14,
    "fifteenth": 15, "sixteenth": 16, "seventeenth": 17, "eighteenth": 18, "nineteenth": 19, "twentieth": 20,
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
    "ist": 1, "frist": 1, "fist": 1,          # frequent typing errors for "1st" / "first"
}
_ED_ORD_WORDS = "|".join(sorted(ED_WORD_ORD, key=len, reverse=True))
_ED_WORD = r"(?:edition|edn\.?|ed\.?)"
# the portal suffix "(Edition...)"; the last one in the title is used
RE_ED_PORTAL = re.compile(r"\(\s*edition\s*[:\-]?\s*([^()]*)\)", re.I)
# an edition statement written in the title text: "5th Edition", "Fourth Edition", "2nd edn"
RE_ED_TEXT = re.compile(
    r"(?<![\w])(?:(\d{1,2})\s*(?:st|nd|rd|th)|(" + _ED_ORD_WORDS + r"))\s+" + _ED_WORD + r"(?![\w])", re.I)
RE_ED_TEXT_REV = re.compile(
    r"(?<![\w])(revised(?:\s+and\s+enlarged)?|enlarged|updated|expanded)\s+" + _ED_WORD + r"(?![\w])", re.I)
RE_ED_TEXT_STRIP = re.compile(
    r"\s*[,;:\-–—]?\s*\(?\s*(?:\d{1,2}\s*(?:st|nd|rd|th)|(?:" + _ED_ORD_WORDS + r"))\s+" + _ED_WORD
    + r"\s*\)?(?![\w])", re.I)
# descriptive editions that are worth a 250 when the portal value gives no number
RE_ED_QUALIFIER = re.compile(
    r"(?:revised(?: and enlarged)?|enlarged|updated|expanded|abridged|unabridged|illustrated|"
    r"annotated|international|student|indian|new)", re.I)
_ROMAN_VAL = {"i": 1, "v": 5, "x": 10, "l": 50, "c": 100, "d": 500, "m": 1000}


def _ordinal(n: int) -> str:
    if 10 <= n % 100 <= 20:
        return f"{n}th"
    return str(n) + {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")


def _roman_value(s: str):
    s = s.lower()
    if not s or not re.fullmatch(r"m{0,3}(cm|cd|d?c{0,3})(xc|xl|l?x{0,3})(ix|iv|v?i{0,3})", s):
        return None
    total = 0
    for i, ch in enumerate(s):
        v = _ROMAN_VAL[ch]
        nxt = _ROMAN_VAL[s[i + 1]] if i + 1 < len(s) else 0
        total += -v if v < nxt else v
    return total or None


def parse_edition_value(v: str):
    """Classify the value of the portal suffix: ('num', n), ('num_rev', n), ('year', y), ('text', s) or (None, None)."""
    v = normalize_spaces(v).strip(" .,-:;")
    if not v:
        return None, None
    v2 = re.sub(r"(?<![\w])" + _ED_WORD + r"(?![\w])", " ", v, flags=re.I)
    v2 = re.sub(r"\b(19|20)\d{2}(?:\s*[-–/]\s*\d{2,4})?\b", " ", v2)          # years and "2016-17"
    v2 = re.sub(r"\b(?:jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\b", " ", v2, flags=re.I)
    v2 = normalize_spaces(v2).strip(" .,-:;")
    if not v2:
        y = re.search(r"\b(19|20)\d{2}\b", v)
        return ("year", y.group(0)) if y else (None, None)
    m = re.fullmatch(r"(\d{1,3})\s*(?:st|nd|rd|th)?", v2, re.I)
    if m:
        return "num", int(m.group(1))
    if v2.lower() in ED_WORD_ORD:
        return "num", ED_WORD_ORD[v2.lower()]
    r = _roman_value(v2)
    if r:
        return "num", r
    revised = bool(re.search(r"\brevised\b", v2, re.I))
    # a number inside a longer value: "Revised 2nd Edition", "Second Revised Edition", "2nd Edition 5th Semester"
    m = re.search(r"(?<![\w])(?:(\d{1,2})\s*(?:st|nd|rd|th)|(" + _ED_ORD_WORDS + r"))(?![\w])", v2, re.I)
    if m:
        n = int(m.group(1)) if m.group(1) else ED_WORD_ORD[m.group(2).lower()]
        return ("num_rev" if revised else "num"), n
    m = re.search(r"(?<![\w])(\d{1,2})(?![\w])", v2) if revised else None   # "15 Revised"
    if m:
        return "num_rev", int(m.group(1))
    if re.search(r"[A-Za-z]", v2):
        return "text", v2
    return None, None


def extract_edition_from_title(title_raw: str) -> str:
    t = normalize_spaces(title_raw)
    if not t:
        return ""
    portals = list(RE_ED_PORTAL.finditer(t))
    portal = portals[-1] if portals else None
    kind, val = parse_edition_value(portal.group(1)) if portal else (None, None)
    body = (t[:portal.start()] + " " + t[portal.end():]) if portal else t
    m = RE_ED_TEXT.search(body)
    text_n = (int(m.group(1)) if m.group(1) else ED_WORD_ORD[m.group(2).lower()]) if m else None
    rev = RE_ED_TEXT_REV.search(body)
    # an explicit statement in the title text wins over a portal value of 1, a year or nothing
    if text_n and not (kind in ("num", "num_rev") and val and val >= 2):
        kind, val = "num", text_n
    if kind == "num_rev" and val:
        return f"{_ordinal(val)} revised edition" if val >= 2 else "Revised edition"
    if kind == "num" and val:
        if val >= 2:
            return f"{_ordinal(val)} edition"
        if val == 1 and EMIT_NUMERIC_FIRST_EDITION:
            return "1st edition"
    if kind == "text" and RE_ED_QUALIFIER.fullmatch(val):
        return f"{val} edition"
    if rev:
        return rev.group(0)
    return ""                                   # first edition, a year, or no usable edition


def remove_edition_from_title(title_raw: str) -> str:
    t = normalize_spaces(title_raw)
    if not t:
        return ""
    t = RE_ED_PAREN.sub("", t)
    t = RE_ED_PAREN_NUM.sub("", t)
    t = RE_ED_TAIL.sub("", t)
    t = RE_ED_TEXT_STRIP.sub("", t)             # v22: "..., Fourth Edition", "... 5th Edition ..."
    return normalize_spaces(t).strip(" ,;:-")


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
    # A comma-separated list of people is NOT a corporate body; rely on keywords only.
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


def _tidy_name(name: str) -> str:
    name = re.sub(r'[`"\u201c\u201d]', "", name)
    name = re.sub(r"(?<!\S)\.(?=[A-Za-z]\b)", "", name)  # ".T" -> "T"
    name = re.sub(r"\.(?=[A-Za-z])", ". ", name)  # "B.A.Patil" -> "B. A. Patil"
    return normalize_spaces(name).strip(" ,;:-")


def _is_initial(w: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z]\.?", w))


def _fmt_initial(w: str) -> str:
    return w[0].upper() + "."


def _fix_case(w: str) -> str:
    # Only re-case ALL-CAPS / all-lower words; keep "McDonald", "DeSouza" as given
    if w.isupper() or w.islower():
        return "-".join(p[:1].upper() + p[1:].lower() for p in w.split("-"))
    return w


def _fmt_forename(w: str) -> str:
    return _fmt_initial(w) if _is_initial(w) else _fix_case(w)


def parse_personal_name(name):
    name = strip_role_words(name)
    name = _tidy_name(name)
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
        main = f"{_fix_case(last)}, {' '.join(_fmt_forename(w) for w in first.split())}".strip(" ,")
        return main, honorific, suffix

    # Trailing initials (South Indian style "Arivanantham T."): the name words are
    # the entry element and the initials follow -> "Arivanantham, T."
    k = len(parts)
    while k > 0 and _is_initial(parts[k - 1]):
        k -= 1
    if 0 < k < len(parts):
        head = " ".join(_fix_case(w) for w in parts[:k])
        main = f"{head}, {' '.join(_fmt_initial(w) for w in parts[k:])}"
    elif k == 0:
        main = " ".join(_fmt_initial(w) for w in parts)
    else:
        last = _fix_case(parts[-1])
        firsts = [_fmt_forename(w) for w in parts[:-1]]
        main = f"{last}, {' '.join(firsts)}" if firsts else last

    return main, honorific, suffix


def display_name(token: str) -> str:
    """Natural-order name for 245 $c (role words and honorifics removed)."""
    t = strip_honorifics(_tidy_name(strip_role_words(token)))
    return normalize_spaces(re.sub(r"\(\s*\)", "", t)).strip(" ,;")  # "Dr. (Mrs.)" -> "()"


def format_relator(role: str) -> str:
    if not role:
        return ""
    role = role.strip().lower()
    if role in {"author", "editor"}:
        return role
    return role


def clean_name_token(token: str) -> str:
    token = normalize_spaces(token)
    token = re.sub(r"\.(?=[A-Za-z])", ". ", token)  # keep initials: "B.A" -> "B. A", not "BA"
    token = re.sub(r",\s*\.", ",", token)
    token = re.sub(r"\s*,\s*", ", ", token)
    token = re.sub(r"\s+,", ",", token)
    return token.strip(" ,;")


def build_personal_name_field(tag: str, name: str, role: str):
    relator = format_relator(role)
    cleaned_name = clean_name_token(name)
    line = f"={tag}  1\\$a{cleaned_name}"
    if relator:
        line += f",$e{relator}"  # "Patil, B. A.,$eauthor."
    if not _ends_with_terminal_punct(line):
        line += "."
    return line + "\n"


def build_corporate_name_field(tag: str, name: str, role: str):
    relator = format_relator(role)
    corp = normalize_spaces(name).strip(" ,;")
    line = f"={tag}  2\\$a{corp}"
    if relator:
        line += f",$e{relator}"
    if not _ends_with_terminal_punct(line):
        line += "."
    return line + "\n"


def split_on_honorifics(text: str):
    # "Dr. A Rao Dr. B Sen" -> ["Dr. A Rao", "Dr. B Sen"]
    if len(RE_HON_START.findall(text)) <= 1:
        return [text]
    parts = [p.strip(" ,;") for p in RE_HON_SPLIT.split(text)]
    return [p for p in parts if re.search(r"\w", RE_HONORIFIC.sub("", p))]


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

    # Split on ";", "&", "and" first, then split each piece again so a comma list
    # before "&" ("A Rao, B Sen, C Das & D Roy") is not kept as one name.
    if ";" in s or "&" in s or RE_AND.search(s):
        s = RE_AND.sub(";", s.replace("&", ";"))
        out = []
        for p in RE_SPLIT_NAMES.split(s):
            if p.strip():
                out.extend(split_names(p))
        return out

    if s.count(",") >= 2:
        parts = [p.strip() for p in s.split(",") if p.strip()]
        if len(parts) >= 4 and len(parts) % 2 == 0 and all(len(parts[i].split()) == 1 for i in range(0, len(parts), 2)):
            grouped = [f"{parts[i]}, {parts[i + 1]}" for i in range(0, len(parts), 2)]
            return [clean_name_token(x) for x in grouped if x]
        if len(parts) >= 3 and sum(1 for p in parts if " " in p) >= 2:
            return [clean_name_token(p) for p in parts if p]

    expanded = []
    for chunk in split_on_honorifics(s):
        # "Remy T. Francis" is ONE person: no surname/initials split here
        expanded.extend(split_on_initial_sequences(chunk))

    cleaned = []
    for token in expanded:
        cleaned.extend(split_on_commas_as_people(token))
    return [clean_name_token(p) for p in cleaned if p]


def extract_contributors(author_editor_raw: str):
    s = normalize_spaces(author_editor_raw)
    if not s:
        return [], []
    s = re.sub(r"\.(?=[A-Za-z])", ". ", s)

    # Find role labels BEFORE removing role words (v19 removed them first, so
    # "Editor :" was never seen and every editor was coded as author).
    spans = []
    matches = list(RE_ROLE.finditer(s))
    if matches:
        if matches[0].start() > 0:
            spans.append(("author", s[: matches[0].start()]))
        for i, m in enumerate(matches):
            end = matches[i + 1].start() if i + 1 < len(matches) else len(s)
            spans.append((m.group(1).lower(), s[m.end():end]))
    elif RE_EDITED_BY.match(s):
        spans.append(("editor", RE_EDITED_BY.sub("", s)))
    else:
        spans.append(("author", s))

    authors, editors = [], []
    for role, chunk in spans:
        for x in split_names(strip_role_words(chunk)):
            p = strip_role_words(normalize_spaces(x)).strip(" ,;:")
            if not re.search(r"\w", RE_HONORIFIC.sub("", p)):
                continue
            (editors if role == "editor" else authors).append(p)
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
            vol_no = m.group(1) or m.group(2)
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

    if RE_ROMAN_FULL.fullmatch(vol_no or ""):
        vol_no = vol_no.upper()
    return normalize_spaces(t), vol_no, part_no


def build_245_field_enhanced(title_raw: str, stmt_resp_col: str, has_1xx: bool, resp_is_clean: bool = False):
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
    c_col = stmt_resp_col if resp_is_clean else clean_resp_text(stmt_resp_col)
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
    online_kw = ["digital", "online", "download", "electronic"]
    # Audio first: "Downloadable and online audio file" is audio, not an e-book
    if "audio" in pf:
        return "audio_online" if any(k in pf for k in online_kw) else "audio"
    if any(k in pf for k in ["e-book", "ebook"] + online_kw):
        return "electronic"
    return "print"


def rda_33x_fields(form_class: str):
    if form_class == "electronic":
        return (
            "=336  \\\\$atext$2rdacontent\n",
            "=337  \\\\$acomputer$2rdamedia\n",
            "=338  \\\\$aonline resource$2rdacarrier\n",
        )
    if form_class == "audio_online":
        # Downloadable audio: media is "computer", carrier "online resource"
        return (
            "=336  \\\\$aspoken word$2rdacontent\n",
            "=337  \\\\$acomputer$2rdamedia\n",
            "=338  \\\\$aonline resource$2rdacarrier\n",
        )
    if form_class == "audio":
        # Physical audio of unknown carrier (ONIX "Audio", "Audiobook player")
        return (
            "=336  \\\\$aspoken word$2rdacontent\n",
            "=337  \\\\$aaudio$2rdamedia\n",
            "=338  \\\\$aunspecified$2rdacarrier\n",
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
        PROG.update(phase="reading", file_n=len(input_files), file_i=0, done=0, total=0,
                    t0=time.time(), outputs=[])
        for k, path in enumerate(input_files, 1):
            if cancel_flag:
                break
            PROG.update(file_i=k, file_name=os.path.basename(path))
            df = _read_input_file(path)
            df = df.rename(columns={c: COLUMN_RENAME[c] for c in df.columns if c in COLUMN_RENAME})
            missing = [c for c in REQUIRED_INTERNAL if c not in df.columns]
            if missing:
                raise ValueError(f"Missing required column(s) in {path}: " + ", ".join(missing))
            df = df[REQUIRED_INTERNAL]
            frames.append((path, df))
            total += len(df)

        PROG.update(phase="converting", total=total, done=0, file_i=0, t_convert=time.time())

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

                # Always strip edition text from the title, even when no 250 is made
                title_for_245 = remove_edition_from_title(title_raw)
                if series_a:
                    title_for_245 = remove_series_from_title(title_for_245)

                title_for_245 = normalize_title_punct(title_for_245)
                title_for_245 = maybe_title_case(title_for_245)

                isbn = clean_isbn(isbn_raw)
                lang = normalize_language(language_raw)
                year = extract_year_from_pub_date(pub_date_raw)
                authors, editors = extract_contributors(author_editor_raw)

                form_class = classify_product_form(product_form)

                rec = []
                rec.append(f"=LDR  {build_leader(form_class)}\n")
                rec.append(f"=008  {build_008(year, lang, form_class=form_class)}\n")
                for f in control_fields_006_007(form_class):
                    rec.append(f)
                rec.append(f"=040  \\\\$a{org_code}$beng$erda$c{org_code}\n")
                rec.append("=588  \\\\$aDescription based on ISBN registration metadata from isbn.gov.in.\n")

                if isbn:
                    # Product form goes to 020 $q (it describes the carrier, not the genre: no 655)
                    q = isbn_qualifier(product_form, form_class)
                    rec.append(f"=020  \\\\$a{isbn}" + (f"$q{q}" if q else "") + "\n")

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
                # Editor-only works get no 1XX (RDA: title main entry); editors go to 700.

                resp_parts = []
                if authors:
                    resp_parts.append(", ".join(display_name(a) for a in authors))
                if editors:
                    resp_parts.append("edited by " + ", ".join(display_name(e) for e in editors))
                resp = " ; ".join(p for p in resp_parts if p.strip())
                rec.append(build_245_field_enhanced(title_for_245, resp, has_main, resp_is_clean=True))

                if edition_stmt:
                    line = f"=250  \\\\$a{edition_stmt.strip()}"
                    if not _ends_with_terminal_punct(line):
                        line += "."
                    rec.append(line + "\n")

                # Place is not in the ISBN data; supplied from the agency's country -> bracketed (RDA 2.8.2.6)
                place_text = "[India]"
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
                    # ISBD order: $a title ,$x ISSN ;$v numbering
                    line = f"=490  0\\$a{series_a}"
                    if series_x:
                        line += f",$x{series_x}"
                    if series_v:
                        line += f" ;$v{series_v}"
                    if not _ends_with_terminal_punct(line):
                        line += "."
                    rec.append(line + "\n")

                if applicant_type:
                    at = normalize_spaces(applicant_type)
                    line = f"=590  \\\\$aISBN applicant type: {at}"
                    if not _ends_with_terminal_punct(line):
                        line += "."
                    rec.append(line + "\n")

                for a in (authors[1:] if has_main else authors):
                    line = emit_added_entry(a, "author")
                    if line:
                        rec.append(line)

                for e in editors:
                    line = emit_added_entry(e, "editor")
                    if line:
                        rec.append(line)

                if should_emit_041(language_raw, lang):
                    rec.append(f"=041  0\\$a{lang}\n")

                # ✅ 300 REMOVED (no extent data available/reliable)

                f336, f337, f338 = rda_33x_fields(form_class)
                rec.append(f336)
                rec.append(f337)
                rec.append(f338)
                rec = sort_fields(rec)

                if f_mrk:
                    f_mrk.write(mrk_record_text(rec))

                if f_mrc:
                    buf_mrc.append(encode_marc_record(rec))
                    if len(buf_mrc) % WRITE_FLUSH_EVERY == 0:
                        f_mrc.write(b"".join(buf_mrc))
                        buf_mrc.clear()

                processed += 1
                PROG["done"] = processed

        if single_output:
            base = out_base_path
            mrc_path = base + ".mrc" if write_mrc else None
            mrk_path = base + ".mrk" if write_mrk else None

            f_mrc = open(mrc_path, "wb") if mrc_path else None
            f_mrk = open(mrk_path, "w", encoding="utf-8", newline="\n") if mrk_path else None

            PROG["outputs"] = [x for x in (mrc_path, mrk_path) if x]
            try:
                for k, (path, df) in enumerate(frames, 1):
                    if cancel_flag:
                        break
                    PROG.update(file_i=k, file_name=os.path.basename(path))
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
            for k, (path, df) in enumerate(frames, 1):
                if cancel_flag:
                    break
                PROG.update(file_i=k, file_name=os.path.basename(path))
                base_name = os.path.splitext(os.path.basename(path))[0]

                mrc_path = os.path.join(output_dir, f"{base_name}.mrc") if write_mrc else None
                mrk_path = os.path.join(output_dir, f"{base_name}.mrk") if write_mrk else None

                f_mrc = open(mrc_path, "wb") if mrc_path else None
                f_mrk = open(mrk_path, "w", encoding="utf-8", newline="\n") if mrk_path else None
                PROG["outputs"].extend(x for x in (mrc_path, mrk_path) if x)

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

        PROG["phase"] = "cancelled" if cancel_flag else "done"
        root.after(0, lambda: finish_ui(cancelled=cancel_flag))

    except Exception as e:
        PROG["phase"] = "error"
        root.after(0, lambda msg=str(e): show_error(msg))


# ============================================================
# GUI callbacks
# ============================================================
def _hms(sec):
    sec = int(max(0, sec))
    return f"{sec // 3600}:{sec % 3600 // 60:02d}:{sec % 60:02d}"


def _set_busy(busy):
    state = "disabled" if busy else "normal"
    btn_convert.config(state=state)
    btn_upload.config(state=state)
    btn_clear.config(state=state)
    btn_cancel.config(state="normal" if busy else "disabled")


def poll_progress():
    """Refresh the progress bar and status line from PROG; reschedules itself while the worker runs."""
    ph = PROG["phase"]
    if ph == "reading":
        n = max(PROG["file_n"], 1)
        done_files = max(PROG["file_i"] - 1, 0)
        progress.config(mode="determinate", maximum=n, value=done_files)
        pct_var.set(f"{100 * done_files / n:.0f}%")
        status_var.set(f"Step 1 of 2 - reading input file {PROG['file_i']} of {PROG['file_n']}: "
                       f"{PROG['file_name']}   (elapsed {_hms(time.time() - PROG['t0'])})")
    elif ph == "converting":
        done, total = PROG["done"], max(PROG["total"], 1)
        el = time.time() - PROG["t_convert"]
        rate = done / el if el > 0 else 0
        eta = (total - done) / rate if rate > 0 else 0
        progress.config(mode="determinate", maximum=total, value=done)
        pct_var.set(f"{100 * done / total:.1f}%")
        status_var.set(f"Step 2 of 2 - converting record {done:,} of {PROG['total']:,}  |  file "
                       f"{PROG['file_i']} of {PROG['file_n']}: {PROG['file_name']}  |  {rate:,.0f} records/s  |  "
                       f"elapsed {_hms(el)}  |  remaining about {_hms(eta) if done else '--:--:--'}")
    if ph in ("reading", "converting") or (worker_thread is not None and worker_thread.is_alive()):
        root.after(250, poll_progress)


def finish_ui(cancelled=False):
    _set_busy(False)
    total_time = _hms(time.time() - PROG["t0"])
    if cancelled:
        status_var.set(f"Cancelled after {PROG['done']:,} records ({total_time}).")
        messagebox.showinfo("Cancelled", "Conversion cancelled. The output files are incomplete.")
        return
    progress.config(maximum=max(PROG["total"], 1), value=PROG["total"])
    pct_var.set("100%")
    status_var.set(f"Done: {PROG['done']:,} records converted in {total_time}.")
    outs = "\n".join(PROG["outputs"][:8]) + ("\n..." if len(PROG["outputs"]) > 8 else "")
    messagebox.showinfo("SUCCESS", f"{PROG['done']:,} records converted in {total_time}.\n\nOutput:\n{outs}")


def show_error(msg):
    _set_busy(False)
    status_var.set("Error - see message.")
    messagebox.showerror("ERROR", msg)


def refresh_file_list():
    file_list.delete(0, tk.END)
    for pth in selected_files:
        file_list.insert(tk.END, pth)
    files_var.set(f"{len(selected_files)} file(s) selected" if selected_files
                  else "No files selected - click Upload files...")


def upload_files():
    picked = filedialog.askopenfilenames(title="Select ISBN Excel/CSV files",
                                         filetypes=[("Excel/CSV", "*.xlsx *.csv"), ("All files", "*.*")])
    for pth in picked:
        if pth not in selected_files:
            selected_files.append(pth)
    refresh_file_list()


def clear_files():
    selected_files.clear()
    refresh_file_list()


def start_convert():
    global cancel_flag, worker_thread
    cancel_flag = False

    if not selected_files:
        messagebox.showerror("ERROR", "No input files. Click 'Upload files...' to select the Excel/CSV files first.")
        return

    org_code = normalize_spaces(org_code_var.get())
    if not org_code:
        messagebox.showerror("ERROR", "Please enter Org code for 040 (e.g., KU).")
        return

    write_mrc = bool(write_mrc_var.get())
    write_mrk = bool(write_mrk_var.get())
    if not (write_mrc or write_mrk):
        messagebox.showerror("ERROR", "Select at least one output format: .mrc and/or .mrk")
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
        output_dir = filedialog.askdirectory(title="Choose the output folder")
        if not output_dir:
            return

    PROG.update(phase="reading", file_i=1, file_n=len(selected_files), file_name="", done=0, total=0,
                t0=time.time(), outputs=[])
    _set_busy(True)
    progress.config(value=0)
    pct_var.set("0%")
    worker_thread = threading.Thread(
        target=convert_worker,
        args=(list(selected_files), out_base_path, output_dir, single_output_var.get(), write_mrc, write_mrk,
              org_code),
        daemon=True,
    )
    worker_thread.start()
    root.after(250, poll_progress)


def cancel_convert():
    global cancel_flag
    cancel_flag = True
    status_var.set("Cancelling... (will stop shortly)")


# ============================================================
# GUI
# ============================================================
def main():
    global root, progress, status_var, btn_convert, btn_cancel, btn_upload, btn_clear
    global single_output_var, dark_mode_var, write_mrc_var, write_mrk_var, org_code_var
    global file_list, files_var, pct_var, selected_files
    selected_files = []

    root = tk.Tk()
    root.title("Excel to MARC21 Converter (v22)")
    root.geometry("1020x600")
    root.minsize(860, 560)

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
        file_list.configure(bg=progress_bg, fg=fg, selectbackground="#4caf50")

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

    # --- input files
    up_row = ttk.Frame(frm)
    up_row.pack(anchor="w", pady=(12, 0), fill="x")
    btn_upload = ttk.Button(up_row, text="Upload files...", command=upload_files)
    btn_upload.pack(side="left")
    btn_clear = ttk.Button(up_row, text="Clear list", command=clear_files)
    btn_clear.pack(side="left", padx=10)
    files_var = tk.StringVar(value="No files selected - click Upload files...")
    ttk.Label(up_row, textvariable=files_var).pack(side="left", padx=10)

    list_frame = ttk.Frame(frm)
    list_frame.pack(anchor="w", pady=(6, 0), fill="x")
    file_list = tk.Listbox(list_frame, height=6, width=150, activestyle="none")
    sb = ttk.Scrollbar(list_frame, orient="vertical", command=file_list.yview)
    file_list.configure(yscrollcommand=sb.set)
    file_list.pack(side="left", fill="x", expand=True)
    sb.pack(side="left", fill="y")

    # --- start / stop
    btn_row = ttk.Frame(frm)
    btn_row.pack(anchor="w", pady=12)

    btn_convert = ttk.Button(btn_row, text="Start", command=start_convert)
    btn_convert.pack(side="left")

    btn_cancel = ttk.Button(btn_row, text="Stop", command=cancel_convert, state="disabled")
    btn_cancel.pack(side="left", padx=10)

    # --- progress
    prog_row = ttk.Frame(frm)
    prog_row.pack(anchor="w", pady=5, fill="x")
    progress = ttk.Progressbar(prog_row, length=900, mode="determinate")
    progress.pack(side="left", fill="x", expand=True)
    pct_var = tk.StringVar(value="0%")
    ttk.Label(prog_row, textvariable=pct_var, width=7, anchor="e").pack(side="left", padx=(8, 0))

    status_var = tk.StringVar(value="Ready. Click 'Upload files...' to choose the input files, then Start.")
    ttk.Label(frm, textvariable=status_var, wraplength=980).pack(anchor="w", pady=(5, 0))

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
