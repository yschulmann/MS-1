#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
קטלוג ספרים - גרסה 3 (גרסה גנרית)
פייתון + SQLite, עם ממשק בסגנון חיפוש מודרני ומצב מנהל מלא.

הרצה:               python book_catalog.py
בדיקה עצמית:        python book_catalog.py --selftest
אפשרויות:           --port 8765   --browser (פתיחה בדפדפן במקום בחלון)
איפוס סיסמת מנהל:   python book_catalog.py --reset-password
התאמה לספרייה:      python book_catalog.py --embed profile.json my_catalog.py

הקובץ הזה גנרי: אין בו שם של ספרייה, מיקומים או נתונים. את הפרטים מקבלים באחת משלוש דרכים:
  1. פרופיל מוטמע - השורה PROFILE_B64 שלמטה (ממלאים אותה דרך builder.html או --embed).
  2. קובץ profile.json שמונח ליד קובץ התוכנה.
  3. אשף הגדרה ראשונית שנפתח בהפעלה הראשונה, אם אין פרופיל.
מבנה הפרופיל מתואר ב-AGENT.md.

דרישות: פייתון 3.8 ומעלה. החבילה pywebview (חלון עצמאי) מומלצת אך לא חובה -
בלעדיה התוכנה נפתחת בדפדפן. אין צורך בשום חבילה אחרת (גם לא לייצוא Excel).
התוכנה מרימה שרת מקומי במחשב שלך בלבד (127.0.0.1).
הנתונים וההגדרות נשמרים בקובץ catalog.db שבתיקיית הנתונים הקבועה (APPDATA).
"""
import base64
import csv
try:
    import webview
except ImportError:
    webview = None
import copy
import datetime as dt
import glob
import hashlib
import hmac
import io
import json
import os
import re
import secrets
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
import zipfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, quote, urlparse
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape as xml_escape


# ---- פרופיל הספרייה (שם, מיקומים, עיצוב...) ----
# השורה הבאה היא המקום היחיד שמשתנה בין התקנה להתקנה: JSON של הפרופיל, מקודד ב-base64 (UTF-8).
PROFILE_B64 = ""
PROFILE_LINE = re.compile(r'^PROFILE_B64 = "([A-Za-z0-9+/=]*)"[ \t]*\r?$', re.M)


def _program_dir():
    return os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False) else __file__))


def load_profile():
    """הפרופיל המוטמע, ומעליו profile.json שליד קובץ התוכנה (אם קיים). פרופיל פגום = בלי פרופיל."""
    prof = {}
    if PROFILE_B64:
        try:
            prof = json.loads(base64.b64decode(PROFILE_B64).decode("utf-8"))
        except Exception:
            prof = {}
    try:
        with io.open(os.path.join(_program_dir(), "profile.json"), encoding="utf-8-sig") as f:
            extra = json.load(f)
        if isinstance(extra, dict):
            prof = {**(prof if isinstance(prof, dict) else {}), **extra}
    except Exception:
        pass
    return prof if isinstance(prof, dict) else {}


def embed_profile(source, profile):
    """מחזיר את קוד התוכנה כשהפרופיל מוטמע בו (profile=None משאיר את הקוד גנרי)."""
    if not PROFILE_LINE.search(source):
        raise ValueError("הקובץ אינו קובץ של תוכנת הקטלוג (חסרה השורה PROFILE_B64)")
    b64 = base64.b64encode(json.dumps(profile, ensure_ascii=False).encode("utf-8")).decode("ascii") if profile else ""
    return PROFILE_LINE.sub(lambda m: 'PROFILE_B64 = "%s"' % b64, source, count=1)


PROFILE = load_profile()


def _stable_app_dir():
    """תיקיית נתונים קבועה בפרופיל המשתמש - לא תלויה באיפה קובץ התוכנה עצמו יושב,
    כדי שהקטלוג לא 'ישכח' נתונים כשמריצים עותק/גרסה אחרת של קובץ התוכנה."""
    base = os.environ.get("APPDATA") or os.path.expanduser("~")
    # app_id בפרופיל = תיקיית נתונים נפרדת, כדי ששתי ספריות במחשב אחד לא יתערבבו
    name = re.sub(r'[\\/:*?"<>|\x00-\x1f]', "", str(PROFILE.get("app_id") or "")).strip(" .")[:60]
    d = os.path.join(base, name or "קטלוג ספרים")
    os.makedirs(d, exist_ok=True)
    return d


APP_DIR = _stable_app_dir()
DB_PATH = os.path.join(APP_DIR, "catalog.db")
BACKUP_DIR = os.path.join(APP_DIR, "backups")

# מיגרציה חד-פעמית: אם יש catalog.db ישן ליד קובץ התוכנה הנוכחי (מגרסה קודמת של התוכנה
# ששמרה שם), והתיקייה הקבועה החדשה עדיין ריקה - מעתיקים אוטומטית כדי לא לאבד נתונים קיימים.
_OLD_DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "catalog.db")
if os.path.exists(_OLD_DB) and not os.path.exists(DB_PATH):
    try:
        shutil.copy2(_OLD_DB, DB_PATH)
    except Exception:
        pass
CAPACITY = 50000
DEFAULT_PORT = 8765

# ---- עדכוני גרסה (אופליין) ----
APP_VERSION = "3.0"
# תיקיית העדכונים: מניחים בה קובץ גרסה חדשה (py או exe). אפשר לשנות אותה במצב מנהל.
UPDATE_DIR = os.path.join(APP_DIR, "updates")
UPDATE_MAX_BYTES = 300 * 1024 * 1024  # הגנה: לא מעתיקים קובץ גדול מזה
SETTINGS_PATH = os.path.join(APP_DIR, "settings.json")


def _read_settings():
    try:
        with io.open(SETTINGS_PATH, encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def load_update_dir():
    """תיקיית העדכונים שהמשתמש בחר (נשמרת ב-settings.json), או ברירת המחדל."""
    d = str(_read_settings().get("update_dir") or "").strip()
    return d or UPDATE_DIR


def save_update_dir(path):
    """שומר את תיקיית העדכונים שנבחרה. ריק / ברירת המחדל = מוחק את ההגדרה."""
    d = _read_settings()
    if path and os.path.normcase(os.path.abspath(path)) != os.path.normcase(os.path.abspath(UPDATE_DIR)):
        d["update_dir"] = path
    else:
        d.pop("update_dir", None)
    tmp = SETTINGS_PATH + ".tmp"
    with io.open(tmp, "w", encoding="utf-8") as f:
        json.dump(d, f, ensure_ascii=False, indent=2)
    os.replace(tmp, SETTINGS_PATH)


# בגרסה הגנרית אין מיקומים מוגדרים מראש: הם מגיעים מהפרופיל, מאשף ההגדרה או ממצב מנהל.
# כל מיקום: שם, טווח מדפים (ממדף-עד מדף) ו/או אות - מדף שכתובה בו האות שייך למיקום הזה.

TEXT_FIELDS = ["title", "first_name", "last_name", "volume", "subject", "topics", "content",
               "cond", "location", "publisher", "pub_place", "pub_year", "notes",
               "label", "annex_of", "annex_vol"]
# שדה -> עמודה מנורמלת לחיפוש
FIELD_NORM = {
    "title": "title_norm", "first_name": "n_first_name", "last_name": "n_last_name",
    "volume": "n_volume", "subject": "n_subject", "topics": "n_topics", "content": "n_content",
    "publisher": "n_publisher", "pub_place": "n_pub_place", "pub_year": "n_pub_year",
    "notes": "n_notes", "label": "n_label", "annex_of": "n_annex_of",
}
SEARCH_COLS = {**FIELD_NORM, "all": "search", "author": "author_norm"}
PUBLIC_COLS = ["id"] + TEXT_FIELDS + ["shelf", "shelf_sub", "parent_id", "added", "updated"]

# שדות הספר: (מפתח, כותרת ברירת מחדל). הכותרות ניתנות לשינוי במצב מנהל.
FIELD_DEFS = [
    ("label", "תווית"), ("title", "שם הספר"), ("first_name", "שם פרטי"), ("last_name", "שם משפחה"),
    ("volume", "כרך"), ("subject", "נושא"), ("topics", "נושאים (היררכיה)"), ("content", "תוכן"),
    ("cond", "מצב"), ("location", "מיקום"), ("shelf", "מדף"), ("publisher", "מוציא לאור"),
    ("pub_place", "מקום הוצאה"), ("pub_year", "שנת הדפסה"), ("notes", "הערות"),
    ("annex_of", "נספח לספר"), ("annex_vol", "כרך הספר הראשי"),
]
FIELD_KEYS = [k for k, _ in FIELD_DEFS]
# עמודות הקובץ (CSV / Excel). "מס'" ו"מס' הספר הראשי" קושרים נספח לספר הראשי שלו בצורה חד-משמעית.
CSV_COLUMNS = [("מס'", "id")] + [(h, k) for k, h in FIELD_DEFS] + [("מס' הספר הראשי", "parent_id")]
CSV_ALIASES = {"מצב גופני": "cond", "שם משפחה ": "last_name", "תוית": "label", "תויית": "label",
               "נספח לספר...": "annex_of", "נספח לספר (שם הספר הראשי)": "annex_of",
               "תיאור הכרך": "annex_vol", "מספר": "id", "מס": "id"}

_NIQQUD = re.compile(r"[֑-ׇ]")
_QUOTES = re.compile(r"[\"'״׳`]")
_SHELF_RE = re.compile(r"^(\d{1,3})\s*[-–—־]?\s*([A-Za-zא-ת]{0,3})$")
_XML_BAD = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f]")


def norm(s):
    """נרמול לחיפוש: בלי ניקוד ומרכאות, אותיות קטנות."""
    return _QUOTES.sub("", _NIQQUD.sub("", str(s or ""))).lower().strip()


def like_escape(s):
    return s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


def now():
    return dt.datetime.now().isoformat(timespec="seconds")


def parse_shelf(raw):
    """'101' -> (101,''), '101-א' / '101 א' / '101א' -> (101,'א'), ריק -> (None,'')."""
    s = str(raw if raw is not None else "").strip()
    if not s:
        return None, ""
    s = _QUOTES.sub("", s)
    m = _SHELF_RE.match(s)
    if not m or not 1 <= int(m.group(1)) <= 999:
        raise ValueError("מדף: מספר שלם בין 1 ל-999, ואפשר להוסיף אות, למשל 101-א")
    return int(m.group(1)), m.group(2).upper()


def shelf_label(num, sub):
    if num is None:
        return ""
    return f"{num}-{sub}" if sub else str(num)


class NotFound(Exception):
    pass


class Forbidden(Exception):
    pass


# =====================================================================
#                     הגדרות (הכול ניתן לשינוי במצב מנהל)
# =====================================================================
THEME_PRESETS = {
    "parchment": {"name": "קלף ויין", "colors": {
        "bg": "#F5EEDC", "panel": "#FFFDF6", "fg": "#1C150E", "muted": "#5A4C39", "line": "#C9B88F",
        "accent": "#6B1322", "accent_fg": "#FFF8E6", "gold": "#A87A1C", "link": "#5A0E1B",
        "mark": "#F6DC83", "chip": "#EADFC2"}},
    "royal": {"name": "תכלת וזהב", "colors": {
        "bg": "#F3F0E6", "panel": "#FFFFFF", "fg": "#0E172B", "muted": "#434F68", "line": "#BFC6D6",
        "accent": "#13264A", "accent_fg": "#FFF6DC", "gold": "#B38A2A", "link": "#13264A",
        "mark": "#FBE28F", "chip": "#E3E6EE"}},
    "forest": {"name": "ירוק עתיק", "colors": {
        "bg": "#F2EFE2", "panel": "#FFFEF8", "fg": "#14180F", "muted": "#4A5140", "line": "#BEC2A6",
        "accent": "#1E4A37", "accent_fg": "#FBF6E2", "gold": "#A57C22", "link": "#173B2C",
        "mark": "#F3DF8C", "chip": "#E2E3CF"}},
    "night": {"name": "לילה (כהה)", "colors": {
        "bg": "#14110D", "panel": "#201A14", "fg": "#F5ECDA", "muted": "#C3B499", "line": "#54473A",
        "accent": "#E3B656", "accent_fg": "#1A130A", "gold": "#E3B656", "link": "#F2CF80",
        "mark": "#6A4E12", "chip": "#2E261D"}},
    "contrast": {"name": "ניגודיות גבוהה", "colors": {
        "bg": "#FFFFFF", "panel": "#FFFFFF", "fg": "#000000", "muted": "#2B2B2B", "line": "#000000",
        "accent": "#00205B", "accent_fg": "#FFFFFF", "gold": "#7A5200", "link": "#00205B",
        "mark": "#FFE066", "chip": "#EDEDED"}},
}
FONT_CHOICES = {
    "frank": {"name": "פרנק-ריהל (ספרי קודש)",
              "css": '"Frank Ruhl Libre","FrankRuehl","Frank Ruehl CLM","David Libre","David","Times New Roman",serif'},
    "david": {"name": "דוד", "css": '"David Libre","David","David CLM","FrankRuehl","Times New Roman",serif'},
    "narkis": {"name": "נרקיסים", "css": '"Narkisim","Narkis Block","David","Times New Roman",serif'},
    "segoe": {"name": "Segoe / Arial (נקי)", "css": '"Segoe UI","Arial","Noto Sans Hebrew",sans-serif'},
    "tahoma": {"name": "Tahoma", "css": '"Tahoma","Segoe UI","Arial",sans-serif'},
    "guttman": {"name": "גוטמן / מרים", "css": '"Guttman Yad-Brush","Miriam","Miriam CLM","Arial",sans-serif'},
}
# הרשאות למי שאינו מנהל: (מפתח, תיאור, ברירת מחדל)
PERM_DEFS = [
    ("search_adv", "חיפוש מתקדם", True),
    ("search_types", "בחירת סוג חיפוש", True),
    ("change_view", "בחירת תצוגת התוצאות", True),
    ("change_sort", "שינוי מיון ומספר תוצאות בעמוד", True),
    ("view_details", "פתיחת כרטיס ספר מלא", True),
    ("browse_locations", "דפדוף לפי מיקום ומדף", True),
    ("show_count", "הצגת מספר הספרים בקטלוג", True),
    ("export_csv", "ייצוא ל-CSV", True),
    ("export_xlsx", "ייצוא ל-Excel", True),
    ("add", "הוספת ספרים", False),
    ("edit", "עריכת ספרים", False),
    ("delete", "מחיקת ספרים", False),
    ("bulk", "עריכה ומחיקה מרובה (בתצוגת טבלה)", False),
    ("import", "ייבוא מקובץ", False),
    ("backup", "שמירת גיבוי", False),
    ("restore", "שחזור מגיבוי", False),
    ("locations", "ניהול מיקומים ומדפים", False),
    ("values", "ניהול רשימות ערכים (נושאים, הוצאות...)", False),
    ("update", "עדכון גרסה", False),
    ("quit", "סגירת התוכנה", True),
]
VIEW_NAMES = {"cards": "כרטיסים", "list": "רשימה", "table": "טבלה", "grid": "אריחים"}
SORT_NAMES = {"relevance": "הכי מתאים", "title": "שם הספר", "author": "מחבר (משפחה)", "shelf": "מדף",
              "location": "מיקום", "subject": "נושא", "topics": "נושאים (היררכיה)",
              "publisher": "מוציא לאור", "added": "נוסף לאחרונה"}


def default_config():
    def fld(key, label):
        return {"label": label,
                "card": key not in ("annex_vol",),
                "table": key in ("label", "title", "first_name", "last_name", "volume", "subject",
                                 "location", "shelf", "annex_of"),
                "adv": key not in ("annex_vol", "cond", "location", "shelf"),
                "form": True, "public": True, "export": True}
    return {
        "texts": {
            "app_title": "קטלוג ספרים", "window_title": "קטלוג ספרים",
            "tagline": "",
            "search_placeholder": "חיפוש בקטלוג…", "btn_search": "חיפוש", "btn_adv": "חיפוש מתקדם",
            "btn_add": "ספר חדש", "home_types_caption": "במה לחפש?", "home_locations_caption": "דפדוף לפי מיקום",
            "empty_title": "לא נמצאו ספרים התואמים לחיפוש",
            "empty_hint": "בדוק את האיות, נסה מילים אחרות, או חפש ב״הכל״.",
            "annex_caption": "נספחים הכרוכים בספר זה", "annex_badge": "נספח", "footer": "",
        },
        "logo": {"emoji": "📚", "use_image": False, "show_title": True},
        "splash": {"enabled": False, "seconds": 3, "fit": "cover", "click_to_close": True,
                   "bg": "#000000", "caption": ""},
        "theme": {
            "preset": "parchment", "colors": dict(THEME_PRESETS["parchment"]["colors"]),
            "font_title": "frank", "font_body": "segoe", "font_size": 16, "radius": 10,
            "ornaments": True, "density": "normal", "results_width": 980,
        },
        "search": {
            "types": [
                {"id": "all", "label": "הכל", "fields": ["all"], "on": True},
                {"id": "title", "label": "שם הספר", "fields": ["title"], "on": True},
                {"id": "author", "label": "מחבר", "fields": ["author"], "on": True},
                {"id": "subject", "label": "נושא", "fields": ["subject", "topics"], "on": True},
                {"id": "content", "label": "תוכן", "fields": ["content"], "on": True},
                {"id": "annex", "label": "נספחים", "fields": ["annex_of"], "on": True},
                {"id": "publisher", "label": "הוצאה ושנה", "fields": ["publisher", "pub_place", "pub_year"], "on": True},
                {"id": "shelf", "label": "מדף", "fields": ["shelf"], "on": True},
                {"id": "label", "label": "תווית", "fields": ["label"], "on": False},
                {"id": "notes", "label": "הערות", "fields": ["notes"], "on": False},
            ],
            "default_type": "all", "types_on_home": True,
            "live": True, "group_annexes": True, "page_size": 20, "page_sizes": [10, 20, 50, 100],
            "default_sort": "relevance", "default_dir": "asc", "highlight": True,
        },
        "results": {"default_view": "cards", "views": ["cards", "list", "table", "grid"],
                    "snippet_len": 200, "show_topics": True, "show_timing": True},
        "home": {"show_locations": True, "show_count": True, "show_capacity_bar": False},
        "fields": {k: fld(k, h) for k, h in FIELD_DEFS},
        "conditions": [
            {"name": "חדש", "color": "#1F7A3A"}, {"name": "טוב", "color": "#2E6F8E"},
            {"name": "בינוני", "color": "#8A6D00"}, {"name": "דורש תיקון", "color": "#A61C1C"},
        ],
        "locations": {"auto": True},
        "perms": {k: d for k, _, d in PERM_DEFS},
        "admin": {"timeout_min": 30},
        "general": {"capacity": CAPACITY, "backup_keep": 14, "auto_backup": True,
                    "window_w": 1200, "window_h": 820, "maximized": True,
                    "update_check_min": 15, "confirm_quit": True},
    }


def starter_books():
    """קטלוג בסיסי לבחירה בהתקנה חדשה: ספרי היסוד שיש כמעט בכל ספרייה תורנית.
    אפשר למחוק או לערוך כל ספר אחר כך; מדף ומיקום נשארים ריקים למילוי."""
    out = []

    def add(title, volumes, subject, topic="", first="", last=""):
        for v in volumes:
            out.append({"title": title, "volume": v, "subject": subject, "first_name": first, "last_name": last,
                        "topics": (topic + " > " + v) if topic else ""})
    add("חומש", ["בראשית", "שמות", "ויקרא", "במדבר", "דברים"], "תורה", "תנ''ך > תורה")
    add("מקראות גדולות", ["בראשית", "שמות", "ויקרא", "במדבר", "דברים"], "תורה", "תנ''ך > תורה")
    add("תנ''ך", ["נביאים ראשונים", "נביאים אחרונים", "כתובים"], "נ''ך", "תנ''ך")
    add("משניות", ["זרעים", "מועד", "נשים", "נזיקין", "קדשים", "טהרות"], "משנה", "משנה")
    add("תלמוד בבלי", ["ברכות", "שבת", "עירובין", "פסחים", "שקלים", "יומא", "סוכה", "ביצה", "ראש השנה", "תענית",
                       "מגילה", "מועד קטן", "חגיגה", "יבמות", "כתובות", "נדרים", "נזיר", "סוטה", "גיטין",
                       "קידושין", "בבא קמא", "בבא מציעא", "בבא בתרא", "סנהדרין", "מכות", "שבועות",
                       "עבודה זרה", "הוריות", "זבחים", "מנחות", "חולין", "בכורות", "ערכין", "תמורה",
                       "כריתות", "מעילה", "נדה"], "ש''ס", "מסכתות > בבלי")
    add("משנה תורה", ["מדע", "אהבה", "זמנים", "נשים", "קדושה", "הפלאה", "זרעים", "עבודה", "קרבנות", "טהרה",
                      "נזיקין", "קנין", "משפטים", "שופטים"], "רמב''ם", "רמב''ם", "רבי משה בן מימון", "")
    add("טור", ["אורח חיים", "יורה דעה", "אבן העזר", "חושן משפט"], "הלכה", "טור", "רבי יעקב בן אשר", "")
    add("שולחן ערוך", ["אורח חיים", "יורה דעה", "אבן העזר", "חושן משפט"], "הלכה", "שולחן ערוך", "רבי יוסף", "קארו")
    add("משנה ברורה", ["חלק א", "חלק ב", "חלק ג", "חלק ד", "חלק ה", "חלק ו"], "הלכה", "",
        "רבי ישראל מאיר הכהן", "מראדין")
    return out


def profile_config(p):
    """הופך פרופיל להגדרות: השדות הקצרים (name, tagline, emoji, preset, conditions) ומעליהם config."""
    if not isinstance(p, dict):
        return {}
    c = copy.deepcopy(p.get("config")) if isinstance(p.get("config"), dict) else {}
    texts = c.setdefault("texts", {}) if isinstance(c.get("texts", {}), dict) else {}
    name = str(p.get("name") or "").strip()
    if name:
        texts.setdefault("app_title", name)
        texts.setdefault("window_title", name)
    if p.get("tagline") is not None:
        texts.setdefault("tagline", str(p["tagline"]))
    if p.get("emoji"):
        c.setdefault("logo", {}).setdefault("emoji", str(p["emoji"]))
    if p.get("preset") in THEME_PRESETS:
        th = c.setdefault("theme", {})
        th.setdefault("preset", p["preset"])
        th.setdefault("colors", dict(THEME_PRESETS[p["preset"]]["colors"]))
    if isinstance(p.get("conditions"), list) and p["conditions"]:
        palette = ["#1F7A3A", "#2E6F8E", "#8A6D00", "#B45F06", "#A61C1C", "#5B5B5B"]
        c.setdefault("conditions", [x if isinstance(x, dict) else {"name": str(x), "color": palette[i % len(palette)]}
                                    for i, x in enumerate(p["conditions"])])
    return c


def merge_config(base, over):
    """ממזג הגדרות שמורות על ברירות המחדל: מפתחות חדשים מקבלים ברירת מחדל, וערך מסוג שגוי נדחה."""
    if not isinstance(over, dict):
        return base
    out = {}
    for k, v in base.items():
        if k not in over:
            out[k] = v
            continue
        o = over[k]
        if isinstance(v, dict):
            out[k] = merge_config(v, o) if isinstance(o, dict) else v
        elif isinstance(v, bool):
            out[k] = bool(o) if isinstance(o, (bool, int)) else v
        elif isinstance(v, int):
            try:
                out[k] = int(o)
            except (TypeError, ValueError):
                out[k] = v
        elif isinstance(v, list):
            out[k] = o if isinstance(o, list) else v
        else:
            out[k] = str(o) if isinstance(o, (str, int, float)) else v
    return out


# =====================================================================
#                    Excel (xlsx) בלי חבילות חיצוניות
# =====================================================================
def _col_name(i):
    s = ""
    i += 1
    while i:
        i, r = divmod(i - 1, 26)
        s = chr(65 + r) + s
    return s


def make_xlsx(headers, rows, sheet_name="קטלוג", widths=None, header_color="6B1322"):
    """בונה קובץ xlsx: שורת כותרת מודגשת וקפואה, סינון אוטומטי, גיליון מימין לשמאל."""
    def cell(ref, v, style):
        if v is None or v == "":
            return ""
        if isinstance(v, bool):
            v = "כן" if v else "לא"
        if isinstance(v, int):
            return f'<c r="{ref}" s="{style}"><v>{v}</v></c>'
        t = xml_escape(_XML_BAD.sub("", str(v)))
        return f'<c r="{ref}" s="{style}" t="inlineStr"><is><t xml:space="preserve">{t}</t></is></c>'

    n = len(headers)
    out = ['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
           '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
           '<sheetViews><sheetView rightToLeft="1" workbookViewId="0">'
           '<pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" state="frozen"/>'
           '</sheetView></sheetViews><sheetFormatPr defaultRowHeight="15"/><cols>']
    for i in range(n):
        w = (widths or [])[i] if widths and i < len(widths) else 18
        out.append(f'<col min="{i + 1}" max="{i + 1}" width="{w}" customWidth="1"/>')
    out.append('</cols><sheetData><row r="1" ht="22" customHeight="1">')
    out.extend(cell(f"{_col_name(i)}1", h, 1) for i, h in enumerate(headers))
    out.append("</row>")
    rn = 1
    for row in rows:
        rn += 1
        out.append(f'<row r="{rn}">')
        out.extend(cell(f"{_col_name(i)}{rn}", v, 2) for i, v in enumerate(row))
        out.append("</row>")
    out.append(f'</sheetData><autoFilter ref="A1:{_col_name(max(n, 1) - 1)}{max(rn, 1)}"/></worksheet>')
    styles = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
              '<styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
              '<fonts count="2"><font><sz val="11"/><name val="Arial"/></font>'
              '<font><b/><sz val="11"/><color rgb="FFFFFFFF"/><name val="Arial"/></font></fonts>'
              '<fills count="3"><fill><patternFill patternType="none"/></fill>'
              '<fill><patternFill patternType="gray125"/></fill>'
              f'<fill><patternFill patternType="solid"><fgColor rgb="FF{header_color}"/></patternFill></fill></fills>'
              '<borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders>'
              '<cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs>'
              '<cellXfs count="3"><xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/>'
              '<xf numFmtId="0" fontId="1" fillId="2" borderId="0" xfId="0" applyFont="1" applyFill="1" applyAlignment="1">'
              '<alignment horizontal="center" vertical="center" readingOrder="2"/></xf>'
              '<xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0" applyAlignment="1">'
              '<alignment vertical="top" readingOrder="2"/></xf></cellXfs></styleSheet>')
    name = xml_escape(re.sub(r"[\[\]:*?/\\]", " ", sheet_name)[:31] or "Sheet1", {'"': "&quot;"})
    files = {
        "[Content_Types].xml": '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
        '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
        '<Default Extension="xml" ContentType="application/xml"/>'
        '<Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
        '<Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
        '<Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>'
        '</Types>',
        "_rels/.rels": '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/>'
        '</Relationships>',
        "xl/workbook.xml": '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
        'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
        f'<sheets><sheet name="{name}" sheetId="1" r:id="rId1"/></sheets></workbook>',
        "xl/_rels/workbook.xml.rels": '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/>'
        '<Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/>'
        '</Relationships>',
        "xl/styles.xml": styles,
        "xl/worksheets/sheet1.xml": "".join(out),
    }
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for fn, content in files.items():
            z.writestr(fn, content)
    return buf.getvalue()


def read_xlsx(data):
    """קורא את הגיליון הראשון של קובץ xlsx. מחזיר רשימת שורות (כל שורה - רשימת מחרוזות)."""
    ns = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    try:
        z = zipfile.ZipFile(io.BytesIO(data))
    except zipfile.BadZipFile:
        raise ValueError("הקובץ אינו קובץ Excel (xlsx) תקין")
    names = z.namelist()
    shared = []
    if "xl/sharedStrings.xml" in names:
        for si in ET.fromstring(z.read("xl/sharedStrings.xml")).iter(ns + "si"):
            shared.append("".join(t.text or "" for t in si.iter(ns + "t")))
    sheets = sorted((n for n in names if re.fullmatch(r"xl/worksheets/sheet\d+\.xml", n)),
                    key=lambda n: int(re.findall(r"\d+", n)[-1]))
    if not sheets:
        raise ValueError("לא נמצא גיליון בקובץ ה-Excel")
    rows = []
    for _, row in ET.iterparse(z.open(sheets[0])):
        if row.tag != ns + "row":
            continue
        vals = []
        for c in row.iter(ns + "c"):
            ref = c.get("r") or ""
            col = 0
            for ch in ref:
                if ch.isalpha():
                    col = col * 26 + (ord(ch.upper()) - 64)
            col = (col - 1) if col else len(vals)
            t = c.get("t")
            v = c.find(ns + "v")
            if t == "s":
                val = shared[int(v.text)] if v is not None and v.text else ""
            elif t == "inlineStr":
                val = "".join(x.text or "" for x in c.iter(ns + "t"))
            else:
                val = (v.text or "") if v is not None else ""
                if re.fullmatch(r"-?\d+\.0+", val):
                    val = val.split(".")[0]
            while len(vals) < col:
                vals.append("")
            vals.append(val)
        rows.append(vals)
        row.clear()
    return rows


# =====================================================================
#                           שכבת הנתונים
# =====================================================================
class Catalog:
    def __init__(self, path=DB_PATH, profile=None):
        """profile: פרופיל הספרייה. ברירת המחדל - הפרופיל של קובץ התוכנה (רק למסד הראשי)."""
        self.path = path
        self._file_profile = (PROFILE if path == DB_PATH else {}) if profile is None else profile
        self._profile = self._defaults = None
        self.con = sqlite3.connect(path, check_same_thread=False)
        self.con.row_factory = sqlite3.Row
        self.lock = threading.RLock()
        self._cfg = None
        self._rules = None
        self._init_schema()

    # ---------- סכמה ומיגרציה ----------
    def _init_schema(self):
        self._cfg = self._rules = self._profile = self._defaults = None
        norm_cols = ",\n".join(f"{c} TEXT NOT NULL DEFAULT ''"
                               for c in FIELD_NORM.values() if c != "title_norm")
        self.con.executescript(f"""
        CREATE TABLE IF NOT EXISTS books(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            title TEXT NOT NULL,
            first_name TEXT NOT NULL DEFAULT '',
            last_name TEXT NOT NULL DEFAULT '',
            volume TEXT NOT NULL DEFAULT '',
            subject TEXT NOT NULL DEFAULT '',
            topics TEXT NOT NULL DEFAULT '',
            content TEXT NOT NULL DEFAULT '',
            cond TEXT NOT NULL DEFAULT '',
            location TEXT NOT NULL DEFAULT '',
            shelf INTEGER CHECK (shelf IS NULL OR (shelf BETWEEN 1 AND 999)),
            shelf_sub TEXT NOT NULL DEFAULT '',
            publisher TEXT NOT NULL DEFAULT '',
            pub_place TEXT NOT NULL DEFAULT '',
            pub_year TEXT NOT NULL DEFAULT '',
            notes TEXT NOT NULL DEFAULT '',
            label TEXT NOT NULL DEFAULT '',
            annex_of TEXT NOT NULL DEFAULT '',
            annex_vol TEXT NOT NULL DEFAULT '',
            parent_id INTEGER,
            added TEXT, updated TEXT,
            title_norm TEXT NOT NULL DEFAULT '',
            author_norm TEXT NOT NULL DEFAULT '',
            search TEXT NOT NULL DEFAULT '',
            {norm_cols}
        );
        CREATE TABLE IF NOT EXISTS locations(
            name TEXT PRIMARY KEY,
            pos INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS assets(name TEXT PRIMARY KEY, mime TEXT NOT NULL, data BLOB NOT NULL,
                                          updated TEXT);
        """)
        # מיגרציה מגרסאות קודמות
        have = {r[1] for r in self.con.execute("PRAGMA table_info(books)")}
        needed = {"shelf_sub": "TEXT NOT NULL DEFAULT ''", "publisher": "TEXT NOT NULL DEFAULT ''",
                  "pub_place": "TEXT NOT NULL DEFAULT ''", "pub_year": "TEXT NOT NULL DEFAULT ''",
                  "topics": "TEXT NOT NULL DEFAULT ''", "label": "TEXT NOT NULL DEFAULT ''",
                  "annex_of": "TEXT NOT NULL DEFAULT ''", "annex_vol": "TEXT NOT NULL DEFAULT ''",
                  "parent_id": "INTEGER"}
        needed.update({c: "TEXT NOT NULL DEFAULT ''" for c in FIELD_NORM.values()
                       if c != "title_norm"})
        missing = [c for c in needed if c not in have]
        for c in missing:
            self.con.execute(f"ALTER TABLE books ADD COLUMN {c} {needed[c]}")
        lhave = {r[1] for r in self.con.execute("PRAGMA table_info(locations)")}
        new_rules = "shelf_from" not in lhave
        for c, t in (("shelf_from", "INTEGER"), ("shelf_to", "INTEGER"), ("letter", "TEXT NOT NULL DEFAULT ''")):
            if c not in lhave:
                self.con.execute(f"ALTER TABLE locations ADD COLUMN {c} {t}")
        self.con.commit()
        if missing:
            self._reindex()
        self.con.executescript("""
        CREATE INDEX IF NOT EXISTS ix_title ON books(title_norm);
        CREATE INDEX IF NOT EXISTS ix_author ON books(author_norm);
        CREATE INDEX IF NOT EXISTS ix_subject ON books(subject);
        CREATE INDEX IF NOT EXISTS ix_topics ON books(topics);
        CREATE INDEX IF NOT EXISTS ix_loc_shelf ON books(location, shelf, shelf_sub);
        CREATE INDEX IF NOT EXISTS ix_parent ON books(parent_id);
        """)
        # הפרופיל של קובץ התוכנה נשמר במסד, כדי שיישאר גם אחרי עדכון לקובץ גנרי
        first_profile = bool(self._file_profile) and not self._get_setting("profile")
        if first_profile:
            self._set_setting("profile", self._file_profile)
        rules = self._profile_rules(self.profile)
        if self.con.execute("SELECT COUNT(*) FROM locations").fetchone()[0] == 0:
            for i, (name, a, b, letter) in enumerate(rules):
                self.con.execute("INSERT INTO locations(name,pos,shelf_from,shelf_to,letter) VALUES(?,?,?,?,?)",
                                 (name, i, a, b, letter))
        elif new_rules and rules:
            # מסד מגרסה קודמת: קובעים את טווחי המדפים למיקומים שבפרופיל ומעדכנים את מיקומי הספרים
            for i, (name, a, b, letter) in enumerate(rules):
                if self.con.execute("SELECT 1 FROM locations WHERE name=?", (name,)).fetchone():
                    self.con.execute("UPDATE locations SET shelf_from=?,shelf_to=?,letter=? WHERE name=?",
                                     (a, b, letter, name))
                else:
                    self.con.execute(
                        "INSERT INTO locations(name,pos,shelf_from,shelf_to,letter) VALUES(?,?,?,?,?)",
                        (name, self._next_pos(), a, b, letter))
            self.con.commit()
            self.apply_location_rules()
            self.con.execute("DELETE FROM locations WHERE shelf_from IS NULL AND letter='' AND name NOT IN "
                             "(SELECT DISTINCT location FROM books)")
        self.con.commit()
        if first_profile and self._file_profile.get("starter") and self.count() == 0:
            self.add_starter()             # הפרופיל ביקש להתחיל עם הקטלוג הבסיסי

    def add_starter(self):
        """מוסיף את הקטלוג הבסיסי (ספרי היסוד). מחזיר כמה ספרים נוספו."""
        return self._import(iter(starter_books()), "add")["imported"]

    def close(self):
        self.con.close()

    # ---------- הגדרות ----------
    def _get_setting(self, key, default=None):
        row = self.con.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
        if not row:
            return default
        try:
            return json.loads(row[0])
        except ValueError:
            return default

    def _set_setting(self, key, value):
        with self.con:
            if value is None:
                self.con.execute("DELETE FROM settings WHERE key=?", (key,))
            else:
                self.con.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",
                                 (key, json.dumps(value, ensure_ascii=False)))

    # ---------- פרופיל הספרייה ----------
    @property
    def profile(self):
        if self._profile is None:
            p = self._get_setting("profile") or self._file_profile or {}
            self._profile = p if isinstance(p, dict) else {}
        return self._profile

    @classmethod
    def _profile_rules(cls, profile):
        """המיקומים שבפרופיל כרשימת (שם, ממדף, עד מדף, אות). שורה לא תקינה מדולגת."""
        out, seen = [], set()
        for l in profile.get("locations") or []:
            if not isinstance(l, dict):
                continue
            name = str(l.get("name") or "").strip()
            if not name or name in seen:
                continue
            try:
                a, b, letter = cls._rule(l)
            except ValueError:
                a = b = None
                letter = ""
            seen.add(name)
            out.append((name, a, b, letter))
        return out

    def defaults(self):
        """ברירות המחדל של ההתקנה הזו: ההגדרות הגנריות, ומעליהן הפרופיל."""
        if self._defaults is None:
            d = merge_config(default_config(), profile_config(self.profile))
            try:
                self._validate_config(d)
            except ValueError:
                d = default_config()
            self._defaults = d
        return copy.deepcopy(self._defaults)

    def needs_setup(self):
        """התקנה חדשה בלי פרופיל ובלי נתונים: בהפעלה הראשונה נפתח אשף ההגדרה."""
        return not (self.profile or self._get_setting("setup_done") or self.has_password()
                    or self._get_setting("config") or self.count())

    def apply_setup(self, d, password=None):
        """שומר את תשובות אשף ההגדרה כפרופיל הספרייה (שם, משפט, ערכת צבעים, מיקומים) וסיסמת מנהל."""
        prof = {}
        if not d.get("skip"):
            for k, n in (("name", 60), ("tagline", 200), ("emoji", 8)):
                v = str(d.get(k) or "").strip()[:n]
                if v:
                    prof[k] = v
            if d.get("preset") in THEME_PRESETS:
                prof["preset"] = d["preset"]
            locs = []
            for l in d.get("locations") or []:
                name = str((l or {}).get("name") or "").strip() if isinstance(l, dict) else ""
                if not name:
                    continue
                a, b, letter = self._rule(l)          # שגיאה בטווח עוצרת את האשף עם הסבר
                locs.append({"name": name, "shelf_from": a, "shelf_to": b, "letter": letter})
            if len({l["name"] for l in locs}) != len(locs):
                raise ValueError("יש שני מיקומים באותו שם")
            if locs:
                prof["locations"] = locs
            if password:
                self.set_password(password)
        if prof:
            self._set_setting("profile", prof)
        self._set_setting("setup_done", True)
        self._profile = self._defaults = self._cfg = self._rules = None
        if d.get("starter") and not d.get("skip") and self.count() == 0:
            self.add_starter()
        known = set(self.locations())
        with self.con:
            for name, a, b, letter in self._profile_rules(prof):
                if name not in known:
                    self.con.execute("INSERT INTO locations(name,pos,shelf_from,shelf_to,letter) VALUES(?,?,?,?,?)",
                                     (name, self._next_pos(), a, b, letter))
        return prof

    @property
    def cfg(self):
        if self._cfg is None:
            self._cfg = merge_config(self.defaults(), self._get_setting("config", {}))
        return self._cfg

    def save_config(self, new):
        if not isinstance(new, dict):
            raise ValueError("הגדרות לא תקינות")
        cfg = merge_config(self.defaults(), merge_config_keep(self.cfg, new))
        self._validate_config(cfg)
        self._set_setting("config", cfg)
        self._cfg = None
        return self.cfg

    def reset_config(self, section=None):
        if section:
            cfg = copy.deepcopy(self.cfg)
            d = self.defaults()
            if section not in d:
                raise ValueError("אין קטגוריית הגדרות כזו")
            cfg[section] = d[section]
        else:
            cfg = self.defaults()
        self._set_setting("config", cfg)
        self._cfg = None
        return self.cfg

    @staticmethod
    def _validate_config(cfg):
        seen, types = set(), []
        for t in cfg["search"]["types"]:
            if not isinstance(t, dict):
                continue
            tid = re.sub(r"[^A-Za-z0-9_]", "", str(t.get("id") or "")) or ("t%d" % (len(types) + 1))
            while tid in seen:
                tid += "x"
            seen.add(tid)
            fields = [f for f in (t.get("fields") or []) if f in SEARCH_COLS or f == "shelf"]
            label = str(t.get("label") or "").strip()[:40]
            if not label or not fields:
                continue
            types.append({"id": tid, "label": label, "fields": fields, "on": bool(t.get("on", True))})
        if not any(t["on"] for t in types):
            raise ValueError("חייב להישאר לפחות סוג חיפוש פעיל אחד")
        cfg["search"]["types"] = types
        if cfg["search"]["default_type"] not in {t["id"] for t in types if t["on"]}:
            cfg["search"]["default_type"] = next(t["id"] for t in types if t["on"])
        cfg["search"]["page_size"] = max(1, min(200, cfg["search"]["page_size"]))
        sizes = sorted({max(1, min(200, int(x))) for x in cfg["search"]["page_sizes"]
                        if str(x).strip().isdigit()}) or [20]
        cfg["search"]["page_sizes"] = sizes
        views = [v for v in cfg["results"]["views"] if v in VIEW_NAMES] or ["cards"]
        cfg["results"]["views"] = views
        if cfg["results"]["default_view"] not in views:
            cfg["results"]["default_view"] = views[0]
        if cfg["search"]["default_sort"] not in SORT_NAMES:
            cfg["search"]["default_sort"] = "relevance"
        conds = []
        for c in cfg["conditions"]:
            name = str((c or {}).get("name") if isinstance(c, dict) else c or "").strip()
            color = str((c or {}).get("color") or "") if isinstance(c, dict) else ""
            if name and name not in [x["name"] for x in conds]:
                conds.append({"name": name, "color": color if re.fullmatch(r"#[0-9A-Fa-f]{6}", color) else "#5B5B5B"})
        cfg["conditions"] = conds
        for k, v in list(cfg["theme"]["colors"].items()):
            if not re.fullmatch(r"#[0-9A-Fa-f]{6}", str(v)):
                cfg["theme"]["colors"][k] = THEME_PRESETS["parchment"]["colors"][k]
        cfg["theme"]["font_size"] = max(12, min(24, cfg["theme"]["font_size"]))
        cfg["theme"]["radius"] = max(0, min(28, cfg["theme"]["radius"]))
        cfg["theme"]["results_width"] = max(640, min(2400, cfg["theme"]["results_width"]))
        cfg["splash"]["seconds"] = max(1, min(60, cfg["splash"]["seconds"]))
        cfg["general"]["capacity"] = max(100, cfg["general"]["capacity"])
        cfg["general"]["backup_keep"] = max(1, min(365, cfg["general"]["backup_keep"]))
        cfg["admin"]["timeout_min"] = max(1, min(24 * 60, cfg["admin"]["timeout_min"]))
        for k, d in cfg["fields"].items():
            d["label"] = str(d.get("label") or "").strip()[:40] or dict(FIELD_DEFS)[k]

    # ---------- סיסמת מנהל ----------
    @staticmethod
    def _hash(pw, salt):
        return hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), salt, 120000).hex()

    def has_password(self):
        return bool(self._get_setting("admin_pw"))

    def set_password(self, pw):
        pw = str(pw or "")
        if len(pw) < 4:
            raise ValueError("הסיסמה חייבת להכיל לפחות 4 תווים")
        salt = os.urandom(16)
        self._set_setting("admin_pw", {"salt": salt.hex(), "hash": self._hash(pw, salt)})

    def check_password(self, pw):
        rec = self._get_setting("admin_pw")
        if not rec:
            return False
        try:
            good = self._hash(str(pw or ""), bytes.fromhex(rec["salt"]))
        except (KeyError, ValueError):
            return False
        return hmac.compare_digest(good, rec.get("hash", ""))

    def clear_password(self):
        self._set_setting("admin_pw", None)

    # ---------- קבצים מצורפים להגדרות (סמל, תמונת פתיחה, לוגו) ----------
    ASSET_TYPES = {"icon": (2 * 1024 * 1024, ("image/x-icon",)),
                   "splash": (25 * 1024 * 1024, ("image/png", "image/jpeg", "image/gif", "image/webp", "image/bmp")),
                   "logo": (5 * 1024 * 1024, ("image/png", "image/jpeg", "image/gif", "image/webp",
                                              "image/svg+xml", "image/x-icon"))}

    @staticmethod
    def sniff_image(data):
        if data[:4] == b"\x00\x00\x01\x00":
            return "image/x-icon"
        if data[:8] == b"\x89PNG\r\n\x1a\n":
            return "image/png"
        if data[:3] == b"\xff\xd8\xff":
            return "image/jpeg"
        if data[:6] in (b"GIF87a", b"GIF89a"):
            return "image/gif"
        if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
            return "image/webp"
        if data[:2] == b"BM":
            return "image/bmp"
        return ""

    def set_asset(self, name, data):
        if name not in self.ASSET_TYPES:
            raise ValueError("סוג קובץ לא מוכר")
        limit, mimes = self.ASSET_TYPES[name]
        if not data:
            raise ValueError("הקובץ ריק")
        if len(data) > limit:
            raise ValueError("הקובץ גדול מדי (עד %d MB)" % (limit // (1024 * 1024)))
        mime = self.sniff_image(data)
        if mime not in mimes:
            if name == "icon":
                raise ValueError("יש לבחור קובץ סמל מסוג ICO")
            raise ValueError("יש לבחור קובץ תמונה (PNG / JPG / GIF / WEBP)")
        with self.con:
            self.con.execute("INSERT OR REPLACE INTO assets(name,mime,data,updated) VALUES(?,?,?,?)",
                             (name, mime, sqlite3.Binary(data), now()))

    def get_asset(self, name):
        row = self.con.execute("SELECT mime,data FROM assets WHERE name=?", (name,)).fetchone()
        return (row[0], bytes(row[1])) if row else None

    def delete_asset(self, name):
        with self.con:
            self.con.execute("DELETE FROM assets WHERE name=?", (name,))

    def asset_stamps(self):
        return {r[0]: r[1] for r in self.con.execute("SELECT name,updated FROM assets")}

    # ---------- הכנת רשומה ----------
    @staticmethod
    def _norm_cols(r):
        out = {"title_norm": norm(r["title"]),
               "author_norm": norm(r["last_name"] + " " + r["first_name"])}
        for f, c in FIELD_NORM.items():
            if c != "title_norm":
                out[c] = norm(r[f])
        out["search"] = norm(" ".join(
            [r[f] for f in ("title", "first_name", "last_name", "volume", "subject", "topics",
                            "content", "publisher", "pub_place", "pub_year", "notes", "location", "cond",
                            "annex_of")]
            + [shelf_label(r.get("shelf"), r.get("shelf_sub", ""))]))
        return out

    def _prep(self, d, strict=True):
        r = {k: str(d.get(k) if d.get(k) is not None else "").strip() for k in TEXT_FIELDS}
        if not r["title"]:
            raise ValueError("חסר שם ספר")
        raw, sub = d.get("shelf"), d.get("shelf_sub") or ""
        if isinstance(raw, int) and sub:
            raw = f"{raw}-{sub}"
        try:
            r["shelf"], r["shelf_sub"] = parse_shelf(raw)
        except ValueError:
            if strict:
                raise
            r["shelf"], r["shelf_sub"] = None, ""
        if self.cfg["locations"]["auto"]:
            loc = self.locate(r["shelf"], r["shelf_sub"])
            if loc:
                r["location"] = loc
        r.update(self._norm_cols(r))
        return r

    def _reindex(self, where="", params=()):
        rows = self.con.execute("SELECT * FROM books " + where, params).fetchall()
        with self.con:
            for row in rows:
                d = dict(row)
                r = {k: d[k] for k in TEXT_FIELDS}
                r["shelf"], r["shelf_sub"] = d["shelf"], d["shelf_sub"] or ""
                cols = self._norm_cols(r)
                sets = ",".join(f"{c}=:{c}" for c in cols)
                self.con.execute(f"UPDATE books SET {sets} WHERE id=:id", {**cols, "id": d["id"]})

    # ---------- פעולות על ספרים ----------
    @staticmethod
    def _public(row):
        d = {k: row[k] for k in PUBLIC_COLS}
        d["shelf_text"] = shelf_label(d["shelf"], d["shelf_sub"])
        return d

    def _parent_for(self, r, d, self_id=None):
        """מחזיר את מזהה הספר הראשי של נספח: לפי בחירה מפורשת, ואם אין - לפי שם הספר הראשי."""
        if not r["annex_of"]:
            return None
        pid = d.get("parent_id")
        try:
            pid = int(pid) if pid not in (None, "") else None
        except (TypeError, ValueError):
            pid = None
        if pid and pid != self_id:
            row = self.con.execute("SELECT title_norm FROM books WHERE id=?", (pid,)).fetchone()
            if row and row[0] == norm(r["annex_of"]):
                return pid
        return self._guess_parent(r["annex_of"], r["shelf"], r["annex_vol"], self_id)

    def _guess_parent(self, annex_of, shelf, annex_vol, self_id=None):
        c = self.con.execute("SELECT id, shelf, volume, annex_of FROM books WHERE title_norm=? AND id<>?",
                             (norm(annex_of), self_id or -1)).fetchall()
        for test in (lambda x: x["shelf"] == shelf, lambda x: x["volume"] == (annex_vol or ""),
                     lambda x: not x["annex_of"]):
            if len(c) <= 1:
                break
            c = [x for x in c if test(x)] or c
        return c[0]["id"] if len(c) == 1 else None

    def add(self, d):
        r = self._prep(d)
        r["added"] = r["updated"] = now()
        r["parent_id"] = self._parent_for(r, d)
        with self.con:
            cur = self.con.execute(
                f"INSERT INTO books({','.join(r)}) VALUES({','.join(':' + k for k in r)})", r)
        return cur.lastrowid

    def update(self, book_id, d):
        old = self.get(book_id)
        if not old:
            raise NotFound()
        r = self._prep(d)
        r["updated"] = now()
        r["id"] = book_id
        r["parent_id"] = self._parent_for(r, d, book_id)
        sets = ",".join(f"{k}=:{k}" for k in r if k != "id")
        with self.con:
            self.con.execute(f"UPDATE books SET {sets} WHERE id=:id", r)
            if old["title"] != r["title"]:      # שם הספר הראשי השתנה - מעדכנים את הנספחים שלו
                self.con.execute("UPDATE books SET annex_of=? WHERE parent_id=?", (r["title"], book_id))
        if old["title"] != r["title"]:
            self._reindex("WHERE parent_id=?", (book_id,))

    def delete(self, ids):
        with self.con:
            self.con.executemany("UPDATE books SET parent_id=NULL WHERE parent_id=?", [(i,) for i in ids])
            self.con.executemany("DELETE FROM books WHERE id=?", [(i,) for i in ids])

    def get(self, book_id):
        row = self.con.execute("SELECT * FROM books WHERE id=?", (book_id,)).fetchone()
        return self._public(row) if row else None

    def get_full(self, book_id):
        """ספר עם הנספחים שלו ועם הספר הראשי שלו (אם הוא נספח)."""
        b = self.get(book_id)
        if not b:
            return None
        b["annexes"] = self.annexes_of([book_id]).get(book_id, [])
        b["parent"] = self.get(b["parent_id"]) if b["parent_id"] else None
        return b

    def annexes_of(self, ids):
        out = {}
        ids = list(ids)
        for i in range(0, len(ids), 500):
            chunk = ids[i:i + 500]
            for row in self.con.execute(
                    f"SELECT {','.join(PUBLIC_COLS)} FROM books WHERE parent_id IN ({','.join('?' * len(chunk))}) "
                    "ORDER BY title_norm, id", chunk):
                out.setdefault(row["parent_id"], []).append(self._public(row))
        return out

    def find_duplicate(self, d, exclude_id=None):
        try:
            r = self._prep(d)
        except ValueError:
            return None
        row = self.con.execute(
            "SELECT * FROM books WHERE title_norm=? AND author_norm=? AND volume=? AND id<>?",
            (r["title_norm"], r["author_norm"], r["volume"], exclude_id or -1)).fetchone()
        return self._public(row) if row else None

    def count(self):
        return self.con.execute("SELECT COUNT(*) FROM books").fetchone()[0]

    def bulk_set(self, ids, field, value):
        """קובע ערך אחד בשדה אחד להרבה ספרים."""
        if field not in TEXT_FIELDS + ["shelf"] or field in ("title", "annex_of", "annex_vol"):
            raise ValueError("אי אפשר לשנות את השדה הזה בעריכה מרובה")
        n = 0
        for i in ids:
            b = self.get(int(i))
            if not b:
                continue
            b["shelf"] = b["shelf_text"]
            b.pop("shelf_sub", None)
            b[field] = value
            self.update(b["id"], b)
            n += 1
        return n

    def rename_value(self, field, old, new):
        """מחליף ערך בכל הספרים (למשל איחוד שני נושאים). מחזיר כמה ספרים עודכנו."""
        if field not in ("subject", "publisher", "pub_place", "pub_year", "cond", "label",
                         "first_name", "last_name", "volume"):
            raise ValueError("אי אפשר לנהל ערכים בשדה הזה")
        new = str(new or "").strip()
        with self.con:
            cur = self.con.execute(f"UPDATE books SET {field}=?, updated=? WHERE {field}=?", (new, now(), old))
        self._reindex(f"WHERE {field}=?", (new,))
        return cur.rowcount

    def value_counts(self, field, limit=5000):
        if field not in TEXT_FIELDS:
            raise ValueError("שדה לא מוכר")
        return [{"value": r[0], "count": r[1]} for r in self.con.execute(
            f"SELECT {field}, COUNT(*) FROM books GROUP BY {field} ORDER BY COUNT(*) DESC, {field} LIMIT ?",
            (limit,))]

    # ---------- חיפוש ----------
    def _type_fields(self, f):
        """השדות שבהם מחפשים: לפי סוג החיפוש שהוגדר (type), או לפי שדה בודד (field)."""
        tid = f.get("type")
        if tid:
            for t in self.cfg["search"]["types"]:
                if t["id"] == tid:
                    return list(t["fields"])
        return [f.get("field") or "all"]

    def _where(self, f):
        w, p = [], []
        fields = self._type_fields(f)
        q = norm(f.get("q", ""))
        if q and fields == ["shelf"]:
            num, sub = parse_shelf(f.get("q"))
            w.append("shelf=?"); p.append(num)
            if sub:
                w.append("shelf_sub=?"); p.append(sub)
        elif q:
            cols = [SEARCH_COLS[x] for x in fields if x in SEARCH_COLS] or ["search"]
            for word in q.split():
                pat = "%" + like_escape(word) + "%"
                w.append("(" + " OR ".join(f"{c} LIKE ? ESCAPE '\\'" for c in cols) + ")")
                p.extend([pat] * len(cols))
        for fld, c in FIELD_NORM.items():
            for word in norm(f.get(fld, "")).split():
                w.append(f"{c} LIKE ? ESCAPE '\\'")
                p.append("%" + like_escape(word) + "%")
        if f.get("location"):
            w.append("location=?"); p.append(f["location"])
        if f.get("cond"):
            w.append("cond=?"); p.append(f["cond"])
        if f.get("annex") == "1":
            w.append("annex_of<>''")
        elif f.get("annex") == "0":
            w.append("annex_of=''")
        if f.get("ids"):
            try:
                ids = [int(x) for x in str(f["ids"]).split(",") if x.strip()][:5000]
            except ValueError:
                raise ValueError("רשימת ספרים לא תקינה")
            w.append(f"id IN ({','.join('?' * len(ids))})"); p.extend(ids)
        if str(f.get("shelf", "")).strip():
            num, sub = parse_shelf(f["shelf"])
            w.append("shelf=?"); p.append(num)
            if sub:
                w.append("shelf_sub=?"); p.append(sub)
        for key, op in (("shelf_from", ">="), ("shelf_to", "<=")):
            v = str(f.get(key, "")).strip()
            if v:
                try:
                    w.append(f"shelf{op}?"); p.append(int(v))
                except ValueError:
                    raise ValueError("טווח המדפים חייב להיות מספרים")
        return (" WHERE " + " AND ".join(w)) if w else "", p

    def _relevance_sql(self, f):
        """כשיש טקסט חופשי (q) - דירוג לפי דיוק ההתאמה: שם מדויק > שם מתחיל ב... >
        שם מכיל > נושא/תת-נושא > מחבר > כרך > כל השאר. מחזיר (ביטוי CASE, פרמטרים) או (None, [])."""
        qn = norm(f.get("q", "")).strip()
        if not qn:
            return None, []
        esc = like_escape(qn)
        fields = self._type_fields(f)
        if fields == ["shelf"]:
            return None, []
        if "all" in fields:
            case = ("CASE "
                     "WHEN title_norm=? THEN 0 "
                     "WHEN title_norm LIKE ?||'%' ESCAPE '\\' THEN 1 "
                     "WHEN title_norm LIKE '%'||?||'%' ESCAPE '\\' THEN 2 "
                     "WHEN n_subject LIKE '%'||?||'%' ESCAPE '\\' "
                       "OR n_topics LIKE '%'||?||'%' ESCAPE '\\' THEN 3 "
                     "WHEN author_norm LIKE '%'||?||'%' ESCAPE '\\' THEN 4 "
                     "WHEN n_volume LIKE '%'||?||'%' ESCAPE '\\' THEN 5 "
                     "ELSE 6 END")
            return case, [qn, esc, esc, esc, esc, esc, esc]
        target = SEARCH_COLS.get(fields[0], "search")
        case = (f"CASE WHEN {target}=? THEN 0 "
                f"WHEN {target} LIKE ?||'%' ESCAPE '\\' THEN 1 "
                f"WHEN {target} LIKE '%'||?||'%' ESCAPE '\\' THEN 2 "
                f"ELSE 3 END")
        return case, [qn, esc, esc]

    @staticmethod
    def _order(sort, direction, idcol="id"):
        d = "DESC" if direction == "desc" else "ASC"
        shelf = f"(shelf IS NULL), shelf {d}, shelf_sub {d}"
        table = {
            "title": f"title_norm {d}",
            "author": f"author_norm {d}, title_norm",
            "shelf": f"{shelf}, title_norm",
            "location": f"location {d}, {shelf}, title_norm",
            "subject": f"subject {d}, title_norm",
            "topics": f"topics {d}, title_norm",
            "publisher": f"n_publisher {d}, title_norm",
            "added": f"added {d}",
        }
        return " ORDER BY " + table.get(sort, table["title"]) + ", " + idcol

    def query(self, f, limit=20, offset=0, group=False):
        """group=True: נספח שנמצא בחיפוש מוצג בתוך הספר הראשי שלו (ולא כתוצאה נפרדת)."""
        where, p = self._where(f)
        sort = f.get("sort")
        rel_case, rel_params = (None, [])
        if not sort or sort == "relevance":
            rel_case, rel_params = self._relevance_sql(f)
        d = "DESC" if f.get("dir") == "desc" else "ASC"
        cols = ",".join(PUBLIC_COLS)
        if group:
            total = self.con.execute(
                "SELECT COUNT(DISTINCT COALESCE(parent_id,id)) FROM books" + where, p).fetchone()[0]
            order = (f" ORDER BY rel ASC, title_norm {d}, m.id" if rel_case
                     else self._order(sort if sort != "relevance" else "title", f.get("dir"), "m.id"))
            sql = (f"WITH hits AS (SELECT id AS hid, COALESCE(parent_id,id) AS gid, "
                   f"{rel_case or '0'} AS r0 FROM books{where}) "
                   f"SELECT {','.join('m.' + c for c in PUBLIC_COLS)}, MIN(h.r0) AS rel, "
                   f"GROUP_CONCAT(h.hid) AS hit_ids FROM hits h JOIN books m ON m.id=h.gid "
                   f"GROUP BY h.gid" + order)
            params = rel_params + p
        else:
            total = self.con.execute("SELECT COUNT(*) FROM books" + where, p).fetchone()[0]
            if rel_case:
                order = f" ORDER BY {rel_case} ASC, title_norm {d}, id"
            else:
                order = self._order(sort if sort != "relevance" else "title", f.get("dir"))
            sql = f"SELECT {cols} FROM books" + where + order
            params = p + rel_params
        if limit is not None:
            sql += " LIMIT ? OFFSET ?"
            params = params + [limit, offset]
        raw = self.con.execute(sql, params).fetchall()
        rows = [self._public(r) for r in raw]
        if group:
            ann = self.annexes_of([r["id"] for r in rows])
            for r, src in zip(rows, raw):
                hits = {int(x) for x in str(src["hit_ids"] or "").split(",") if x}
                r["hit_self"] = r["id"] in hits
                r["annexes"] = ann.get(r["id"], [])
                for a in r["annexes"]:
                    a["hit"] = a["id"] in hits
        return rows, total

    def distinct(self, col, limit=3000):
        return [r[0] for r in self.con.execute(
            f"SELECT DISTINCT {col} FROM books WHERE {col}<>'' ORDER BY {col} LIMIT ?", (limit,))]

    def meta(self):
        cfg = self.cfg
        return {
            "count": self.count(), "capacity": cfg["general"]["capacity"],
            "conditions": [c["name"] for c in cfg["conditions"]],
            "annex_count": self.con.execute("SELECT COUNT(*) FROM books WHERE annex_of<>''").fetchone()[0],
            "locations": self.location_list(),
            "subjects": self.distinct("subject"), "topics_list": self.distinct("topics"),
            "labels": self.distinct("label"),
            "db_path": self.path, "version": APP_VERSION,
            "publishers": self.distinct("publisher"),
            "places": self.distinct("pub_place"),
        }

    # ---------- מיקומים ----------
    def locations(self):
        return [r[0] for r in self.con.execute("SELECT name FROM locations ORDER BY pos, name")]

    def location_counts(self):
        counts = {r[0]: r[1] for r in self.con.execute(
            "SELECT location, COUNT(*) FROM books GROUP BY location")}
        return [(name, counts.get(name, 0)) for name in self.locations()]

    def location_list(self):
        counts = dict(self.location_counts())
        return [{"name": r["name"], "count": counts.get(r["name"], 0), "shelf_from": r["shelf_from"],
                 "shelf_to": r["shelf_to"], "letter": r["letter"] or ""}
                for r in self.con.execute("SELECT * FROM locations ORDER BY pos, name")]

    def locate(self, shelf, sub=""):
        """המיקום של מדף לפי הכללים: קודם אות, ואחר כך טווח מספרים."""
        if shelf is None:
            return None
        if self._rules is None:
            self._rules = [(r["name"], r["shelf_from"], r["shelf_to"], r["letter"] or "")
                           for r in self.con.execute("SELECT * FROM locations ORDER BY pos, name")]
        for name, _, _, letter in self._rules:
            if letter and any(ch in (sub or "") for ch in letter):
                return name
        for name, a, b, _ in self._rules:
            if a is not None and b is not None and a <= shelf <= b:
                return name
        return None

    def apply_location_rules(self):
        """מעדכן את המיקום של כל הספרים לפי מספר המדף. מחזיר כמה ספרים השתנו."""
        self._rules = None
        changed = []
        for row in self.con.execute("SELECT id, shelf, shelf_sub, location FROM books WHERE shelf IS NOT NULL"):
            loc = self.locate(row["shelf"], row["shelf_sub"])
            if loc and loc != row["location"]:
                changed.append((loc, row["id"]))
        with self.con:
            self.con.executemany("UPDATE books SET location=? WHERE id=?", changed)
        for i in range(0, len(changed), 500):
            ids = [c[1] for c in changed[i:i + 500]]
            self._reindex(f"WHERE id IN ({','.join('?' * len(ids))})", ids)
        return len(changed)

    def _next_pos(self):
        return self.con.execute("SELECT COALESCE(MAX(pos),0)+1 FROM locations").fetchone()[0]

    @staticmethod
    def _rule(d):
        def num(v):
            v = str(v if v is not None else "").strip()
            if not v:
                return None
            if not v.isdigit() or not 1 <= int(v) <= 999:
                raise ValueError("טווח מדפים: מספרים בין 1 ל-999")
            return int(v)
        a, b = num(d.get("shelf_from")), num(d.get("shelf_to"))
        if (a is None) != (b is None):
            raise ValueError("יש למלא גם 'ממדף' וגם 'עד מדף' (או להשאיר את שניהם ריקים)")
        if a is not None and a > b:
            raise ValueError("'ממדף' חייב להיות קטן מ'עד מדף'")
        letter = re.sub(r"[^A-Za-zא-ת]", "", str(d.get("letter") or "")).upper()[:6]
        return a, b, letter

    def add_location(self, name, rule=None):
        name = (name or "").strip()
        if not name:
            raise ValueError("שם מיקום ריק")
        if name in self.locations():
            raise ValueError("המיקום כבר קיים")
        a, b, letter = self._rule(rule or {})
        with self.con:
            self.con.execute("INSERT INTO locations(name,pos,shelf_from,shelf_to,letter) VALUES(?,?,?,?,?)",
                             (name, self._next_pos(), a, b, letter))
        self._rules = None

    def rename_location(self, old, new, rule=None):
        new = (new or "").strip()
        if not new:
            raise ValueError("שם מיקום ריק")
        if new != old and new in self.locations():
            raise ValueError("כבר קיים מיקום בשם הזה")
        with self.con:
            if rule is not None:
                a, b, letter = self._rule(rule)
                self.con.execute("UPDATE locations SET shelf_from=?,shelf_to=?,letter=? WHERE name=?",
                                 (a, b, letter, old))
            self.con.execute("UPDATE locations SET name=? WHERE name=?", (new, old))
            self.con.execute("UPDATE books SET location=? WHERE location=?", (new, old))
        self._rules = None
        if new != old:
            self._reindex("WHERE location=?", (new,))

    def order_locations(self, names):
        with self.con:
            for i, n in enumerate(names):
                self.con.execute("UPDATE locations SET pos=? WHERE name=?", (i, n))
        self._rules = None

    def delete_location(self, name):
        n = self.con.execute("SELECT COUNT(*) FROM books WHERE location=?", (name,)).fetchone()[0]
        if n:
            raise ValueError(f"במיקום הזה יש {n} ספרים. יש להעביר אותם קודם למיקום אחר.")
        with self.con:
            self.con.execute("DELETE FROM locations WHERE name=?", (name,))
        self._rules = None

    # ---------- ייצוא: CSV ו-Excel ----------
    def _export_columns(self, cols=None, public_only=False):
        """רשימת (כותרת, מפתח) לייצוא, לפי כותרות השדות שהוגדרו."""
        fields = self.cfg["fields"]
        out = []
        for head, key in CSV_COLUMNS:
            if key in fields:
                if public_only and not fields[key]["public"]:
                    continue
                if cols is None and not fields[key]["export"]:
                    continue
                head = fields[key]["label"]
            if cols is not None and key not in cols:
                continue
            out.append((head, key))
        return out

    @staticmethod
    def _export_value(r, k):
        if k == "shelf":
            return r["shelf_text"]
        v = r.get(k)
        return "" if v is None else v

    def export_csv(self, rows, cols=None, public_only=False):
        columns = self._export_columns(cols, public_only)
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow([h for h, _ in columns])
        for r in rows:
            w.writerow([self._export_value(r, k) for _, k in columns])
        return ("﻿" + buf.getvalue()).encode("utf-8")

    def export_xlsx(self, rows, cols=None, public_only=False):
        columns = self._export_columns(cols, public_only)
        wide = {"title": 34, "content": 60, "topics": 46, "notes": 30, "annex_of": 30, "first_name": 24,
                "last_name": 18, "subject": 18, "publisher": 20, "id": 8, "parent_id": 14, "label": 8,
                "shelf": 8, "volume": 14, "cond": 14, "location": 14}
        accent = self.cfg["theme"]["colors"]["accent"].lstrip("#").upper()
        if sum(int(accent[i:i + 2], 16) for i in (0, 2, 4)) > 420:   # צבע בהיר מדי לכותרת לבנה
            accent = "3A2A1A"
        data = ([self._export_value(r, k) for _, k in columns] for r in rows)
        return make_xlsx([h for h, _ in columns], data, self.cfg["texts"]["app_title"],
                         [wide.get(k, 16) for _, k in columns], accent)

    # ---------- ייבוא: CSV ו-Excel ----------
    def _keymap(self):
        keymap = {h: k for h, k in CSV_COLUMNS}
        keymap.update(CSV_ALIASES)
        keymap.update({d["label"]: k for k, d in self.cfg["fields"].items()})
        return keymap

    def import_csv(self, data, replace=False, mode=None):
        """מחזיר dict עם imported / updated / skipped / bad_shelf."""
        for enc in ("utf-8-sig", "cp1255"):
            try:
                text = data.decode(enc)
                break
            except UnicodeDecodeError:
                continue
        else:
            raise ValueError("קידוד הקובץ לא נתמך. שמור כ-CSV UTF-8.")
        first = text.split("\n", 1)[0]
        delim = max([",", ";", "\t"], key=first.count)
        keymap = self._keymap()
        dicts = ({keymap[h.strip()]: v for h, v in row.items() if h and h.strip() in keymap}
                 for row in csv.DictReader(io.StringIO(text), delimiter=delim))
        return self._import(dicts, mode or ("replace" if replace else "add"))

    def import_xlsx(self, data, mode="add"):
        rows = read_xlsx(data)
        while rows and not any(str(c).strip() for c in rows[0]):
            rows.pop(0)
        if not rows:
            raise ValueError("הגיליון ריק")
        keymap = self._keymap()
        head = [keymap.get(str(h).strip()) for h in rows[0]]
        if "title" not in head:
            raise ValueError("לא נמצאה עמודת 'שם הספר' בשורת הכותרת של הגיליון")
        dicts = ({k: (row[i] if i < len(row) else "") for i, k in enumerate(head) if k}
                 for row in rows[1:])
        return self._import(dicts, mode)

    def import_file(self, data, mode="add"):
        if data[:2] == b"PK":
            return self.import_xlsx(data, mode)
        return self.import_csv(data, mode=mode)

    def _import(self, dicts, mode="add"):
        """mode: add = הוספה, replace = החלפת כל הקטלוג, update = עדכון ספרים קיימים והוספת החדשים."""
        if mode not in ("add", "replace", "update"):
            raise ValueError("אופן ייבוא לא מוכר")
        imported = updated = skipped = bad_shelf = 0
        batch = []
        for d in dicts:
            num, pnum = str(d.pop("id", "") or "").strip(), str(d.pop("parent_id", "") or "").strip()
            try:
                r = self._prep(d, strict=False)
            except ValueError:
                if any(str(v or "").strip() for v in d.values()):
                    skipped += 1
                continue
            if str(d.get("shelf") or "").strip() and r["shelf"] is None:
                bad_shelf += 1
            batch.append((r, num, pnum))
        key = lambda r: (r["title_norm"], r["author_norm"], r["volume"], r["shelf"], r["shelf_sub"])
        stamp = now()
        by_num, new_ids, pending = {}, [], []
        with self.con:
            if mode == "replace":
                self.con.execute("DELETE FROM books")
            existing = {}
            if mode == "update":
                for row in self.con.execute(
                        "SELECT id,title_norm,author_norm,volume,shelf,shelf_sub FROM books"):
                    existing.setdefault(key(row), row["id"])
            ins_cols = None
            for r, num, pnum in batch:
                bid = existing.get(key(r)) if mode == "update" else None
                if bid:
                    sets = {k: v for k, v in r.items() if k in TEXT_FIELDS and v != ""}
                    sets["updated"] = stamp
                    self.con.execute(f"UPDATE books SET {','.join(k + '=:' + k for k in sets)} WHERE id=:id",
                                     {**sets, "id": bid})
                    updated += 1
                    new_ids.append(bid)
                else:
                    r["added"] = r["updated"] = stamp
                    if ins_cols is None:
                        ins_cols = list(r)
                    bid = self.con.execute(
                        f"INSERT INTO books({','.join(ins_cols)}) VALUES({','.join(':' + c for c in ins_cols)})",
                        r).lastrowid
                    imported += 1
                    if mode == "update":
                        existing[key(r)] = bid
                if num:
                    by_num.setdefault(num, bid)
                if r["annex_of"]:
                    pending.append((bid, pnum, r))
            # קישור נספחים לספר הראשי: קודם לפי המספר שבקובץ, ואם אין - לפי שם הספר, המדף והכרך
            for bid, pnum, r in pending:
                pid = by_num.get(pnum) if pnum else None
                if not pid or pid == bid:
                    pid = self._guess_parent(r["annex_of"], r["shelf"], r["annex_vol"], bid)
                self.con.execute("UPDATE books SET parent_id=? WHERE id=?", (pid, bid))
            known = set(self.locations())
            for r, _, _ in batch:
                loc = r["location"]
                if loc and loc not in known:
                    self.con.execute("INSERT INTO locations(name,pos) VALUES(?,?)",
                                     (loc, self._next_pos()))
                    known.add(loc)
        self._rules = None
        if updated:
            for i in range(0, len(new_ids), 500):
                ids = new_ids[i:i + 500]
                self._reindex(f"WHERE id IN ({','.join('?' * len(ids))})", ids)
        return {"imported": imported, "updated": updated, "skipped": skipped, "bad_shelf": bad_shelf}

    # ---------- גיבוי ושחזור ----------
    def backup_to(self, path):
        dest = sqlite3.connect(path)
        try:
            self.con.backup(dest)
        finally:
            dest.close()

    def backup_bytes(self):
        fd, tmp = tempfile.mkstemp(suffix=".db")
        os.close(fd)
        try:
            self.backup_to(tmp)
            with open(tmp, "rb") as f:
                return f.read()
        finally:
            os.remove(tmp)

    def restore_from(self, path, keep_settings=False):
        """מחליף את הקטלוג בגיבוי. keep_settings=True: ההגדרות והסיסמה הנוכחיות נשארות."""
        keep = None
        if keep_settings:
            keep = (self.con.execute("SELECT key,value FROM settings").fetchall(),
                    self.con.execute("SELECT name,mime,data,updated FROM assets").fetchall())
            keep = ([tuple(r) for r in keep[0]], [tuple(r) for r in keep[1]])
        src = sqlite3.connect(path)
        try:
            ok = src.execute("SELECT name FROM sqlite_master WHERE name='books'").fetchone()
            if not ok:
                raise ValueError("הקובץ אינו גיבוי תקין של הקטלוג")
            src.backup(self.con)
        except sqlite3.DatabaseError:
            raise ValueError("הקובץ אינו גיבוי תקין של הקטלוג")
        finally:
            src.close()
        self._init_schema()
        if keep:
            with self.con:
                self.con.execute("DELETE FROM settings")
                self.con.execute("DELETE FROM assets")
                self.con.executemany("INSERT INTO settings(key,value) VALUES(?,?)", keep[0])
                self.con.executemany("INSERT INTO assets(name,mime,data,updated) VALUES(?,?,?,?)", keep[1])
            self._cfg = self._profile = self._defaults = None

    def auto_backup(self, keep=None):
        """גיבוי אוטומטי אחד ליום; נשמרים keep האחרונים."""
        if not self.cfg["general"]["auto_backup"]:
            return
        keep = keep or self.cfg["general"]["backup_keep"]
        os.makedirs(BACKUP_DIR, exist_ok=True)
        target = os.path.join(BACKUP_DIR, f"catalog-{dt.date.today().isoformat()}.db")
        if not os.path.exists(target):
            self.backup_to(target)
        for old in sorted(glob.glob(os.path.join(BACKUP_DIR, "catalog-*.db")))[:-keep]:
            try:
                os.remove(old)
            except OSError:
                pass


def merge_config_keep(base, over):
    """ממזג שינוי חלקי (over) לתוך ההגדרות הנוכחיות (base): מילונים ממוזגים לעומק, השאר מוחלף."""
    if not isinstance(base, dict) or not isinstance(over, dict):
        return over
    out = dict(base)
    for k, v in over.items():
        out[k] = merge_config_keep(base.get(k), v) if isinstance(v, dict) and isinstance(base.get(k), dict) else v
    return out


# =====================================================================
#                           עדכוני גרסה
# =====================================================================
# איך זה עובד: הדרך הפשוטה - במצב מנהל > עדכון גרסה > "בחירת קובץ גרסה חדשה": בוחרים את קובץ
# התוכנה החדש (py, או exe בגרסה המהודרת) והתוכנה מתקינה אותו ונפתחת מחדש.
# לחלופין מניחים את הקובץ בתיקיית העדכונים (UPDATE_DIR): התוכנה מזהה לבד קובץ עם מספר גרסה גבוה
# יותר (ב-py לפי השורה APP_VERSION שבקובץ, ב-exe לפי המספר שבשם הקובץ, למשל BookCatalog-3.1.exe).
# אפשר גם לצרף קובץ version.json (גרסה, שם קובץ, sha256, הערות) - ואז הוא הקובע.
# בהתקנה התוכנה מעתיקה את הקובץ, מאמתת טביעת אצבע (SHA-256), מחליפה את עצמה ונפתחת מחדש.
# אין שום גישה לאינטרנט. הקבצים בתיקיית העדכונים לא נמחקים ולא משתנים.
# הנתונים (catalog.db) נמצאים ב-APPDATA, ולכן החלפת הקובץ לא נוגעת בהם.
RUN = {"srv": None, "cat": None, "window": None, "restart": False}


def parse_version(s):
    """'1.5' / 'v1.10.2' -> (1, 10, 2). משווים כמספרים ולא כטקסט (1.10 גדול מ-1.9)."""
    nums = re.findall(r"\d+", str(s or ""))
    if not nums:
        raise ValueError("מספר גרסה לא תקין")
    return tuple(int(n) for n in nums)


def version_gt(a, b):
    ta, tb = parse_version(a), parse_version(b)
    n = max(len(ta), len(tb))
    return ta + (0,) * (n - len(ta)) > tb + (0,) * (n - len(tb))


def _friendly(e):
    """הודעת שגיאה קריאה למשתמש."""
    if isinstance(e, PermissionError):
        return ("אין הרשאה להחליף את קובץ התוכנה (ייתכן שהיא נמצאת בתיקייה מוגנת, כמו Program Files). "
                "אפשר להעתיק את הגרסה החדשה ידנית במקום הקובץ הישן.")
    if isinstance(e, FileNotFoundError):
        return "תיקיית העדכונים או קובץ העדכון לא נמצאו."
    if isinstance(e, OSError):
        return ("לא ניתן להשלים את ההתקנה (ייתכן שאנטי-וירוס חוסם את הקובץ החדש, או שאין מקום בדיסק). "
                "אפשר להעתיק את הגרסה החדשה ידנית במקום הקובץ הישן.")
    return str(e) or e.__class__.__name__


class Updater:
    """בדיקת עדכונים מתיקייה מקומית, העתקה, אימות והחלפת קובץ ה-exe.

    ההחלפה: ב-Windows אי אפשר למחוק או לדרוס קובץ שרץ, אבל אפשר לשנות את שמו. לכן הקובץ
    הנוכחי מקבל סיומת .old, הקובץ החדש נכנס במקומו, והתוכנה נפתחת מחדש (השאריות נמחקות
    בהפעלה הבאה). אם משהו נכשל באמצע - הקובץ הקודם חוזר למקומו."""

    def __init__(self, update_dir=None, version=None, exe_path=None, frozen=None,
                 before_install=None, on_restart=None, script_path=None):
        self.dir = UPDATE_DIR if update_dir is None else update_dir
        self.version = version or APP_VERSION
        self.frozen = bool(getattr(sys, "frozen", False)) if frozen is None else frozen
        # הקובץ שמוחלף בעדכון: ה-exe בגרסה המהודרת, או קובץ ה-py כשמריצים מפייתון
        self.exe_path = exe_path or (sys.executable if self.frozen else (script_path or ""))
        self.kind = os.path.splitext(self.exe_path)[1].lower() or (".exe" if self.frozen else ".py")
        self.before_install = before_install
        self.on_restart = on_restart or request_restart
        self.retry_tries, self.retry_delay = 10, 0.5
        self.lock = threading.RLock()
        self.state = "idle"        # idle | checking | downloading | installing | restarting
        self.latest = None         # פרטי הגרסה החדשה (אם יש), אחרת None
        self.progress = 0
        self.check_error = ""
        self.install_error = ""
        self.last_check = 0.0
        if self.dir:
            try:
                os.makedirs(self.dir, exist_ok=True)   # שהתיקייה תהיה קיימת וקלה למצוא
            except OSError:
                pass

    # ---------- מצב ----------
    def can_install(self):
        """התקנה אוטומטית אפשרית כשידוע איזה קובץ להחליף, והעדכון הוא מאותו סוג (py / exe)."""
        if not self.exe_path:
            return False
        m = self.latest
        return not m or m["file"].lower().endswith(self.kind)

    def status(self):
        with self.lock:
            m = self.latest or {}
            return {
                "enabled": bool(self.dir), "dir": self.dir, "default_dir": UPDATE_DIR, "current": self.version, "state": self.state,
                "available": bool(self.latest), "latest": m.get("version", ""),
                "notes": m.get("notes", ""), "progress": self.progress,
                "can_install": self.can_install(), "has_page": bool(self.dir), "kind": self.kind,
                "check_error": self.check_error, "install_error": self.install_error,
                "checked": bool(self.last_check),
            }

    def set_dir(self, path):
        """מחליף את תיקיית העדכונים. ריק = ברירת המחדל. מחזיר את הנתיב שנקבע."""
        path = str(path or "").strip().strip('"')
        path = os.path.abspath(os.path.expanduser(path)) if path else UPDATE_DIR
        with self.lock:
            if self.state != "idle":
                raise ValueError("אי אפשר להחליף תיקייה בזמן בדיקה או עדכון. נסה שוב בעוד רגע.")
        try:
            os.makedirs(path, exist_ok=True)
        except OSError:
            raise ValueError("לא ניתן להשתמש בתיקייה הזו (אין הרשאה או שהנתיב אינו תקין).")
        if not os.path.isdir(path):
            raise ValueError("הנתיב שהוזן אינו תיקייה.")
        with self.lock:
            self.dir = path
            self.latest = None
            self.check_error = self.install_error = ""
            self.last_check = 0.0
        return path

    def open_folder(self):
        """פותח את תיקיית העדכונים בסייר הקבצים."""
        if not self.dir:
            raise ValueError("תיקיית העדכונים לא הוגדרה")
        os.makedirs(self.dir, exist_ok=True)
        if hasattr(os, "startfile"):
            os.startfile(self.dir)
        elif sys.platform == "darwin":
            subprocess.Popen(["open", self.dir])
        else:
            subprocess.Popen(["xdg-open", self.dir])

    # ---------- בדיקה ----------
    def check_async(self, force=False):
        with self.lock:
            if not self.dir or self.state != "idle":
                return False
            self.state = "checking"
            self.check_error = ""
            if force:
                self.install_error = ""
        threading.Thread(target=self._check, daemon=True).start()
        return True

    def _check(self):
        try:
            m = self.read_manifest()
            with self.lock:
                self.latest = m if (m and version_gt(m["version"], self.version)) else None
                self.last_check = time.time()
        except Exception as e:
            with self.lock:
                self.latest = None
                self.check_error = _friendly(e)
        finally:
            with self.lock:
                self.state = "idle"

    def read_manifest(self):
        """קורא את version.json מתיקיית העדכונים. אין קובץ = אין עדכון (לא שגיאה)."""
        os.makedirs(self.dir, exist_ok=True)
        path = os.path.join(self.dir, "version.json")
        if not os.path.exists(path):
            return self._scan()
        if os.path.getsize(path) > 256 * 1024:
            raise ValueError("קובץ המידע על הגרסה גדול מדי")
        with open(path, "rb") as f:
            try:
                data = json.loads(f.read().decode("utf-8-sig"))
            except ValueError:
                raise ValueError("קובץ המידע על הגרסה (version.json) פגום")
        return self._validate(data)

    @staticmethod
    def file_version(path):
        """מספר הגרסה של קובץ עדכון: ב-py מתוך השורה APP_VERSION, ב-exe מתוך שם הקובץ."""
        if path.lower().endswith(".py"):
            try:
                with open(path, "rb") as f:
                    head = f.read(400 * 1024).decode("utf-8", "replace")
            except OSError:
                return ""
            m = re.search(r"^APP_VERSION\s*=\s*[\"']([^\"']+)[\"']", head, re.M)
            return m.group(1) if m else ""
        m = re.search(r"(\d+(?:[._]\d+)*)\.[A-Za-z]+$", os.path.basename(path))
        return m.group(1).replace("_", ".") if m else ""

    def _scan(self):
        """בלי version.json: מחפש בתיקייה את קובץ התוכנה עם מספר הגרסה הגבוה ביותר."""
        best = None
        for n in sorted(os.listdir(self.dir)):
            p = os.path.join(self.dir, n)
            if not n.lower().endswith(self.kind) or not os.path.isfile(p):
                continue
            ver = self.file_version(p)
            try:
                if ver and (best is None or version_gt(ver, best[0])):
                    best = (ver, n, p)
            except ValueError:
                continue
        if not best or not version_gt(best[0], self.version):
            return None
        ver, n, p = best
        h = hashlib.sha256()
        with open(p, "rb") as f:
            for chunk in iter(lambda: f.read(256 * 1024), b""):
                h.update(chunk)
        return {"version": ver, "sha256": h.hexdigest(), "file": n, "path": p,
                "size": os.path.getsize(p), "notes": ""}

    def publish_file(self, name, data, version=""):
        """שומר קובץ גרסה חדשה שנבחר מתוך התוכנה בתיקיית העדכונים, עם version.json מתאים.
        מחזיר את מספר הגרסה של הקובץ."""
        name = os.path.basename(str(name or "").replace("\\", "/")).strip()
        if not name.lower().endswith(self.kind):
            raise ValueError("יש לבחור קובץ %s של הגרסה החדשה" % self.kind.lstrip("."))
        if not data:
            raise ValueError("הקובץ ריק")
        if len(data) > UPDATE_MAX_BYTES:
            raise ValueError("קובץ העדכון גדול מדי")
        with self.lock:
            if self.state != "idle":
                raise ValueError("עדכון אחר נמצא בתהליך. נסה שוב בעוד רגע.")
        os.makedirs(self.dir, exist_ok=True)
        path = os.path.join(self.dir, name)
        with open(path + ".tmp", "wb") as f:
            f.write(data)
        os.replace(path + ".tmp", path)
        ver = str(version or "").strip() or self.file_version(path)
        if not ver:
            raise ValueError("לא ניתן לזהות את מספר הגרסה של הקובץ. ב-exe יש לכלול אותו בשם הקובץ, "
                             "למשל BookCatalog-3.1.exe")
        parse_version(ver)
        manifest = {"version": ver, "file": name, "sha256": hashlib.sha256(data).hexdigest(),
                    "size": len(data), "notes": ""}
        with open(os.path.join(self.dir, "version.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f, ensure_ascii=False, indent=2)
        return ver

    def _validate(self, m):
        if not isinstance(m, dict):
            raise ValueError("קובץ המידע על הגרסה אינו תקין")
        ver = str(m.get("version", "")).strip()
        parse_version(ver)
        sha = str(m.get("sha256", "")).strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", sha):
            raise ValueError("בקובץ המידע חסרה טביעת אצבע (sha256) תקינה")
        # שם הקובץ בלבד, בלי נתיב: מונע יציאה מתיקיית העדכונים
        name = os.path.basename(str(m.get("file") or m.get("url") or "").replace("\\", "/").strip()) \
            or "BookCatalog-%s.exe" % ver
        if not name.lower().endswith((".exe", ".py")):
            raise ValueError("שם קובץ העדכון בקובץ המידע חייב להסתיים ב-exe או ב-py")
        path = os.path.join(self.dir, name)
        notes = m.get("notes", "")
        if isinstance(notes, list):
            notes = "\n".join(str(x) for x in notes)
        size = m.get("size")
        size = size if isinstance(size, int) and not isinstance(size, bool) and size > 0 else 0
        info = {"version": ver, "sha256": sha, "file": name, "path": path, "size": size,
                "notes": str(notes or "").strip()[:2000]}
        if version_gt(ver, self.version) and not os.path.isfile(path):
            raise ValueError("קובץ העדכון %s לא נמצא בתיקיית העדכונים. יש להעתיק אליה גם אותו." % name)
        return info

    # ---------- התקנה ----------
    def apply_async(self):
        with self.lock:
            if not self.latest or self.state != "idle":
                return False
            self.state = "downloading"
            self.progress = 0
            self.install_error = ""
        threading.Thread(target=self._apply, daemon=True).start()
        return True

    def _apply(self):
        try:
            if not self.can_install():
                raise RuntimeError("קובץ העדכון אינו מתאים לאופן שבו התוכנה רצה כעת (py / exe). "
                                   "אפשר להחליף את קובץ התוכנה ידנית.")
            if self.before_install:
                try:
                    self.before_install()       # גיבוי הנתונים לפני העדכון
                except Exception:
                    pass
            self.install()
        except Exception as e:
            with self.lock:
                self.state = "idle"
                self.install_error = _friendly(e)
            return
        with self.lock:
            self.state = "restarting"
        self.on_restart()

    def install(self):
        """מעתיק, מאמת ומחליף את קובץ ה-exe. לא מפעיל מחדש."""
        m = self.latest
        if not m:
            raise ValueError("אין עדכון זמין")
        exe = self.exe_path
        part = exe + ".part"
        try:
            self._copy(m, part)
            with self.lock:
                self.state = "installing"
                self.progress = 100
            self._carry_profile(exe, part)
            self._swap(exe, part)
        finally:
            if os.path.exists(part):
                try:
                    os.remove(part)
                except OSError:
                    pass

    @staticmethod
    def _carry_profile(current, new):
        """עדכון מקובץ py גנרי: הפרופיל שמוטמע בקובץ המותקן מועתק לקובץ החדש, כדי ששם הספרייה
        ותיקיית הנתונים לא ישתנו. אם בקובץ החדש כבר מוטמע פרופיל - הוא נשאר."""
        if not current.lower().endswith(".py"):
            return
        try:
            with io.open(current, encoding="utf-8") as f:
                old = PROFILE_LINE.search(f.read())
            with io.open(new, encoding="utf-8", newline="") as f:
                src = f.read()
            cur = PROFILE_LINE.search(src)
            if old and old.group(1) and cur and not cur.group(1):
                with io.open(new, "w", encoding="utf-8", newline="") as f:
                    f.write(PROFILE_LINE.sub(lambda m: old.group(0).rstrip("\r"), src, count=1))
        except (OSError, UnicodeDecodeError):
            pass

    def _copy(self, m, dest):
        """מעתיק את קובץ העדכון (המקור נשאר שלם בתיקיית העדכונים) ומאמת אותו תוך כדי."""
        h = hashlib.sha256()
        got = 0
        total = os.path.getsize(m["path"]) or m["size"]
        with open(m["path"], "rb") as r, open(dest, "wb") as f:
            while True:
                chunk = r.read(256 * 1024)
                if not chunk:
                    break
                got += len(chunk)
                if got > UPDATE_MAX_BYTES:
                    raise ValueError("קובץ העדכון גדול מהצפוי")
                h.update(chunk)
                f.write(chunk)
                if total:
                    with self.lock:
                        self.progress = min(99, got * 100 // total)
        if m["size"] and got != m["size"]:
            raise ValueError("גודל קובץ העדכון שונה מהצפוי. העדכון בוטל.")
        if h.hexdigest() != m["sha256"]:
            raise ValueError("אימות קובץ העדכון נכשל (טביעת האצבע שונה; ייתכן שההעתקה לתיקייה לא הושלמה). העדכון בוטל.")
        with open(dest, "rb") as f:
            if m["file"].lower().endswith(".py"):
                src = f.read()
                try:
                    compile(src.decode("utf-8-sig"), m["file"], "exec")
                except (SyntaxError, UnicodeDecodeError, ValueError):
                    raise ValueError("קובץ העדכון אינו קובץ תוכנה תקין (שגיאת תחביר). העדכון בוטל.")
                if b"APP_VERSION" not in src:
                    raise ValueError("קובץ העדכון אינו קובץ של תוכנת הקטלוג. העדכון בוטל.")
            elif f.read(2) != b"MZ":
                raise ValueError("קובץ העדכון אינו קובץ הפעלה של Windows. העדכון בוטל.")

    def _retry(self, fn):
        """אנטי-וירוס עלול לנעול קובץ חדש לרגע קצר, לכן מנסים כמה פעמים."""
        for i in range(self.retry_tries):
            try:
                return fn()
            except OSError:
                if i == self.retry_tries - 1:
                    raise
                time.sleep(self.retry_delay)

    def _swap(self, exe, part):
        old = exe + ".old"
        if os.path.exists(old):
            try:
                os.remove(old)
            except OSError:
                old = f"{exe}.{int(time.time())}.old"
        self._retry(lambda: os.replace(exe, old))       # שינוי שם של קובץ שרץ מותר ב-Windows
        try:
            self._retry(lambda: os.replace(part, exe))
        except Exception:
            try:
                os.replace(old, exe)                    # מחזירים את הגרסה הקודמת למקומה
            except OSError:
                pass
            raise


def browse_folder(start=""):
    """פותח את חלון בחירת התיקייה של Windows. מחזיר את הנתיב שנבחר, או ריק אם בוטל."""
    win = RUN.get("window")
    if win is None:
        raise ValueError("בחירת תיקייה בחלון אפשרית רק בחלון התוכנה. אפשר להקליד את הנתיב ידנית.")
    kind = getattr(getattr(webview, "FileDialog", None), "FOLDER", None) or webview.FOLDER_DIALOG
    res = win.create_file_dialog(kind, directory=start if start and os.path.isdir(start) else "")
    if not res:
        return ""
    return res[0] if isinstance(res, (list, tuple)) else str(res)


def _backup_before_update(cat):
    os.makedirs(BACKUP_DIR, exist_ok=True)
    with cat.lock:
        cat.backup_to(os.path.join(BACKUP_DIR, "before-update.db"))


def _restart_env(env=None):
    """סביבה נקייה להפעלה מחדש. PyInstaller (onefile): בלי האיפוס הזה העותק החדש ינסה
    להשתמש בקבצים הזמניים של העותק הישן, שנמחקים ברגע שהוא נסגר."""
    out = {k: v for k, v in (os.environ if env is None else env).items()
           if not k.startswith("_PYI") and k != "_MEIPASS2"}
    out["PYINSTALLER_RESET_ENVIRONMENT"] = "1"
    return out


def relaunch():
    """מפעיל עותק חדש ועצמאי של התוכנה (נקרא רק אחרי שהקובץ הוחלף)."""
    exe = sys.executable
    cmd = [exe] + sys.argv[1:]
    if not getattr(sys, "frozen", False):           # הרצה מקובץ py: מפעילים שוב את אותו קובץ
        cmd = [exe, os.path.abspath(sys.argv[0])] + sys.argv[1:]
    env = _restart_env()
    kw = {}
    if sys.platform == "win32":
        kw["creationflags"] = 0x00000008 | 0x00000200   # DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP
    subprocess.Popen(cmd, env=env, cwd=os.path.dirname(cmd[1] if len(cmd) > 1 and cmd[1].endswith(".py")
                                                       else exe) or None, close_fds=True, **kw)


def request_restart():
    """נקרא אחרי שהקובץ הוחלף: סוגר את החלון, ו-main() מפעיל את הגרסה החדשה."""
    RUN["restart"] = True
    try:
        if RUN["window"] is None:
            raise RuntimeError("no window")
        RUN["window"].destroy()
    except Exception:
        # אי אפשר לסגור את החלון בצורה מסודרת - סוגרים את המסד בעצמנו ויוצאים
        try:
            RUN["cat"].close()
        except Exception:
            pass
        relaunch()
        os._exit(0)


def cleanup_update_leftovers(exe_path=None):
    """מוחק שאריות של עדכון קודם (קבצי .old ו-.part ליד ה-exe). מנסה כמה פעמים, כי
    התוכנה הישנה אולי עדיין בתהליך סגירה."""
    exe = exe_path or (sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__))
    if not exe:
        return
    d, base = os.path.split(exe)

    def work():
        for _ in range(8):
            left = False
            try:
                names = os.listdir(d)
            except OSError:
                return
            for n in names:
                if n.startswith(base + ".") and (n.endswith(".old") or n.endswith(".part")):
                    try:
                        os.remove(os.path.join(d, n))
                    except OSError:
                        left = True
            if not left:
                return
            time.sleep(3)
    threading.Thread(target=work, daemon=True).start()


def save_dialog(filename, file_type):
    """פותח חלון 'שמירה בשם' של Windows. מחזיר את הנתיב שנבחר, או ריק אם בוטל."""
    win = RUN.get("window")
    kind = getattr(getattr(webview, "FileDialog", None), "SAVE", None) or webview.SAVE_DIALOG
    try:
        res = win.create_file_dialog(kind, save_filename=filename, file_types=(file_type,))
    except (TypeError, ValueError):
        res = win.create_file_dialog(kind, save_filename=filename)
    if not res:
        return ""
    return res[0] if isinstance(res, (list, tuple)) else str(res)


def open_path(path):
    """פותח קובץ או תיקייה בתוכנת ברירת המחדל של המחשב."""
    if hasattr(os, "startfile"):
        os.startfile(path)
    elif sys.platform == "darwin":
        subprocess.Popen(["open", path])
    else:
        subprocess.Popen(["xdg-open", path])


def apply_window_icon(cat, title=None, wait=True):
    """קובע את סמל החלון (ICO שנבחר במצב מנהל). ב-Windows בלבד; כישלון אינו עוצר את התוכנה."""
    try:
        asset = cat.get_asset("icon")
        if not asset or sys.platform != "win32" or RUN.get("window") is None:
            return False
        path = os.path.join(APP_DIR, "app.ico")
        with open(path, "wb") as f:
            f.write(asset[1])
        import ctypes
        from ctypes import wintypes
        u = ctypes.windll.user32
        u.FindWindowW.restype = wintypes.HWND
        u.FindWindowW.argtypes = [wintypes.LPCWSTR, wintypes.LPCWSTR]
        u.LoadImageW.restype = wintypes.HANDLE
        u.LoadImageW.argtypes = [wintypes.HINSTANCE, wintypes.LPCWSTR, wintypes.UINT, ctypes.c_int,
                                 ctypes.c_int, wintypes.UINT]
        u.SendMessageW.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
        title = title or RUN.get("title") or ""
        hwnd = None
        for _ in range(40 if wait else 1):
            hwnd = u.FindWindowW(None, title)
            if hwnd:
                break
            time.sleep(0.25)
        if not hwnd:
            return False
        for which, size in ((1, 0), (0, 16)):                 # ICON_BIG, ICON_SMALL
            h = u.LoadImageW(None, path, 1, size, size, 0x10 | (0x40 if not size else 0))
            if h:
                u.SendMessageW(hwnd, 0x80, which, h)          # WM_SETICON
        return True
    except Exception:
        return False


# =====================================================================
#                              השרת
# =====================================================================
class Sessions:
    """כניסות מנהל פעילות (בזיכרון בלבד; נסגרות עם סגירת התוכנה או אחרי זמן ללא פעילות)."""

    def __init__(self):
        self.tokens = {}
        self.lock = threading.Lock()

    def create(self, minutes):
        tok = secrets.token_urlsafe(24)
        with self.lock:
            self.tokens[tok] = time.time() + minutes * 60
        return tok

    def check(self, tok, minutes):
        if not tok:
            return False
        with self.lock:
            exp = self.tokens.get(tok)
            if not exp:
                return False
            if exp < time.time():
                self.tokens.pop(tok, None)
                return False
            self.tokens[tok] = time.time() + minutes * 60
            return True

    def drop(self, tok=None):
        with self.lock:
            if tok is None:
                self.tokens.clear()
            else:
                self.tokens.pop(tok, None)


SEARCH_FIELD_CHOICES = [("all", "כל השדות"), ("author", "מחבר (פרטי + משפחה)")] + \
    [(k, h) for k, h in FIELD_DEFS if k in FIELD_NORM] + [("shelf", "מדף (מספר מדויק)")]
FILE_ROUTES = ("/api/export", "/api/export.csv", "/api/export.xlsx", "/api/backup")


class Handler(BaseHTTPRequestHandler):
    server_version = "BookCatalog/3"
    admin = False

    def log_message(self, *a):
        pass

    # ---------- עזרים ----------
    def _send(self, code, body, ctype, extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, code=200):
        self._send(code, json.dumps(obj, ensure_ascii=False), "application/json; charset=utf-8")

    def _body(self):
        n = int(self.headers.get("Content-Length") or 0)
        if n > 500 * 1024 * 1024:
            raise ValueError("הקובץ גדול מדי")
        return self.rfile.read(n) if n else b""

    def _jbody(self):
        try:
            d = json.loads(self._body().decode("utf-8") or "{}")
        except ValueError:
            raise ValueError("בקשה לא תקינה")
        if not isinstance(d, dict):
            raise ValueError("בקשה לא תקינה")
        return d

    def _allowed(self):
        port = self.server.server_address[1]
        hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
        if self.headers.get("Host") not in hosts:
            return False
        origin = self.headers.get("Origin")
        return not origin or origin in {f"http://{h}" for h in hosts}

    def _can(self, perm):
        return self.admin or bool(self.server.cat.cfg["perms"].get(perm))

    def _need(self, perm=None):
        """perm=None: מנהל בלבד. אחרת: מנהל, או שהמנהל התיר את הפעולה לכולם."""
        if not (self.admin if perm is None else self._can(perm)):
            raise Forbidden()

    def _strip(self, rows):
        """מסיר ממי שאינו מנהל שדות שהמנהל הגדיר כמוסתרים."""
        if self.admin:
            return rows
        hidden = [k for k, d in self.server.cat.cfg["fields"].items() if not d["public"]]
        if hidden:
            for r in rows:
                for k in hidden:
                    if k in r:
                        r[k] = ""
                if "shelf" in hidden:
                    r["shelf_text"] = ""
                    r["shelf_sub"] = ""
                    r["shelf"] = None
                for a in r.get("annexes") or []:
                    self._strip([a])
                if r.get("parent"):
                    self._strip([r["parent"]])
        return rows

    def _boot(self, cat):
        with cat.lock:
            return {
                "cfg": cat.cfg, "admin": self.admin, "has_password": cat.has_password(),
                "version": APP_VERSION, "assets": cat.asset_stamps(),
                "presets": THEME_PRESETS, "fonts": FONT_CHOICES,
                "perm_defs": [[k, t] for k, t, _ in PERM_DEFS],
                "field_defs": FIELD_DEFS, "views": VIEW_NAMES, "sorts": SORT_NAMES,
                "search_fields": SEARCH_FIELD_CHOICES, "windowed": RUN.get("window") is not None,
                "defaults": cat.defaults(), "needs_setup": cat.needs_setup(),
            }

    def _handle(self, method):
        if not self._allowed():
            return self._send(403, "forbidden", "text/plain")
        url = urlparse(self.path)
        qs = {k: v[0] for k, v in parse_qs(url.query, keep_blank_values=True).items()}
        cat = self.server.cat
        try:
            if url.path == "/" and method == "GET":
                boot = json.dumps(self._boot(cat), ensure_ascii=False).replace("</", "<\\/")
                return self._send(200, PAGE.replace("__BOOT__", boot), "text/html; charset=utf-8")
            if method == "GET" and (url.path.startswith("/asset/") or url.path == "/favicon.ico"):
                name = "icon" if url.path == "/favicon.ico" else url.path[len("/asset/"):]
                with cat.lock:
                    a = cat.get_asset(name)
                if not a:
                    return self._send(404, "not found", "text/plain")
                return self._send(200, a[1], a[0])
            if not url.path.startswith("/api/"):
                return self._send(404, "not found", "text/plain")
            self.token = self.headers.get("X-Token") or qs.pop("t", "")
            with cat.lock:
                self.admin = self.server.sessions.check(self.token, cat.cfg["admin"]["timeout_min"])
            if url.path.startswith("/api/update/"):  # בלי נעילת מסד הנתונים: העתקה יכולה להימשך
                return self._update_api(method, url.path, qs)
            if url.path.startswith("/api/admin/"):
                return self._admin_api(cat, method, url.path)
            if url.path in FILE_ROUTES:
                return self._files_api(cat, method, url.path, qs)
            with cat.lock:
                self._api(cat, method, url.path, qs)
        except NotFound:
            self._json({"error": "הספר לא נמצא"}, 404)
        except Forbidden:
            self._json({"error": "הפעולה הזו מותרת רק במצב מנהל", "forbidden": True}, 403)
        except ValueError as e:
            self._json({"error": str(e)}, 400)
        except sqlite3.IntegrityError as e:
            self._json({"error": f"שגיאת נתונים: {e}"}, 400)
        except Exception as e:  # noqa
            self._json({"error": f"שגיאה פנימית: {e}"}, 500)

    # ---------- מצב מנהל ----------
    def _admin_api(self, cat, method, path):
        if method != "POST":
            return self._json({"error": "לא נמצא"}, 404)
        d = self._jbody()
        sess = self.server.sessions
        if path == "/api/admin/logout":
            sess.drop(self.token)
            return self._json({"ok": True})
        if path == "/api/admin/wizard":       # אשף ההגדרה הראשונית (רק בהתקנה חדשה וריקה)
            with cat.lock:
                if not cat.needs_setup():
                    raise Forbidden()
                pw = str(d.get("password") or "")
                cat.apply_setup(d, pw or None)
                minutes = cat.cfg["admin"]["timeout_min"]
                self.admin = bool(pw) and not d.get("skip")
                tok = sess.create(minutes) if self.admin else ""
                return self._json({**self._boot(cat), "token": tok})
        if path == "/api/admin/setup":        # קביעת סיסמה ראשונה
            with cat.lock:
                if cat.has_password():
                    raise ValueError("כבר נקבעה סיסמת מנהל")
                cat.set_password(d.get("password"))
                minutes = cat.cfg["admin"]["timeout_min"]
            return self._json({"token": sess.create(minutes)})
        if path == "/api/admin/login":
            with cat.lock:
                ok = cat.check_password(d.get("password"))
                minutes = cat.cfg["admin"]["timeout_min"]
            if not ok:
                time.sleep(0.6)               # מאט ניסיונות ניחוש
                raise ValueError("סיסמה שגויה")
            return self._json({"token": sess.create(minutes)})
        if path == "/api/admin/password":
            self._need()
            with cat.lock:
                if not cat.check_password(d.get("old")):
                    time.sleep(0.6)
                    raise ValueError("הסיסמה הנוכחית שגויה")
                cat.set_password(d.get("new"))
            sess.drop()
            with cat.lock:
                minutes = cat.cfg["admin"]["timeout_min"]
            return self._json({"token": sess.create(minutes)})
        self._json({"error": "לא נמצא"}, 404)

    # ---------- עדכוני גרסה ----------
    def _update_api(self, method, path, qs):
        up = getattr(self.server, "updater", None)
        if up is None:
            return self._json({"error": "לא נמצא"}, 404)
        route = (method, path)
        if route == ("GET", "/api/update/status"):
            return self._json(up.status())
        self._need("update")
        if route == ("POST", "/api/update/check"):
            up.check_async(force=qs.get("force") == "1")
            return self._json(up.status())
        if route == ("POST", "/api/update/apply"):
            ok = up.apply_async()
            return self._json({**up.status(), "ok": ok})
        if route == ("POST", "/api/update/upload"):
            ver = up.publish_file(qs.get("name", ""), self._body(), qs.get("version", ""))
            up.check_async(force=True)
            for _ in range(100):
                if up.state != "checking":
                    break
                time.sleep(0.05)
            return self._json({**up.status(), "uploaded": ver})
        if route == ("POST", "/api/update/dir"):
            path = up.set_dir(self._jbody().get("dir", ""))
            save_update_dir(path)
            up.check_async(force=True)
            return self._json(up.status())
        if route == ("POST", "/api/update/browse"):
            return self._json({"dir": browse_folder(up.dir)})
        if route == ("POST", "/api/update/open"):
            up.open_folder()
            return self._json({"ok": True})
        self._json({"error": "לא נמצא"}, 404)

    # ---------- ייצוא וגיבוי (קבצים) ----------
    def _files_api(self, cat, method, path, qs):
        """GET = הורדה רגילה (דפדפן). POST = חלון 'שמירה בשם' של התוכנה, והקובץ נכתב ישירות לדיסק."""
        if method not in ("GET", "POST"):
            return self._json({"error": "לא נמצא"}, 404)
        today = dt.date.today().isoformat()
        if path == "/api/backup":
            self._need("backup")
            name, ctype, desc = f"catalog-backup-{today}.db", "application/octet-stream", "Backup (*.db)"
        else:
            fmt = "xlsx" if path.endswith(".xlsx") else "csv" if path.endswith(".csv") else qs.get("fmt", "csv")
            if fmt not in ("csv", "xlsx"):
                raise ValueError("סוג קובץ לא נתמך")
            self._need("export_" + fmt)
            name = f"catalog-{today}.{fmt}"
            ctype, desc = (("text/csv; charset=utf-8", "CSV (*.csv)") if fmt == "csv" else
                           ("application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", "Excel (*.xlsx)"))
        windowed = RUN.get("window") is not None and RUN.get("srv") is self.server
        if method == "POST" and not windowed:
            return self._json({"download": True})
        with cat.lock:
            if path == "/api/backup":
                data = cat.backup_bytes()
            else:
                cols = [c for c in qs.get("cols", "").split(",") if c] or None
                rows, _ = cat.query(qs, None)
                self._strip(rows)
                data = (cat.export_xlsx if fmt == "xlsx" else cat.export_csv)(rows, cols, not self.admin)
        if method == "GET":
            return self._send(200, data, ctype, {"Content-Disposition": f'attachment; filename="{name}"'})
        dest = save_dialog(name, desc)
        if not dest:
            return self._json({"cancelled": True})
        ext = os.path.splitext(name)[1]
        if not dest.lower().endswith(ext):
            dest += ext
        try:
            with open(dest, "wb") as f:
                f.write(data)
        except PermissionError:
            raise ValueError("לא ניתן לשמור: הקובץ פתוח בתוכנה אחרת (למשל ב-Excel), או שאין הרשאת כתיבה לתיקייה.")
        except OSError as e:
            raise ValueError("השמירה נכשלה: %s" % e)
        self.server.saved.add(dest)
        self._json({"saved": dest})

    # ---------- שאר ה-API ----------
    def _api(self, cat, method, path, qs):
        route = (method, path)
        cfg = cat.cfg
        if route == ("GET", "/api/boot"):
            return self._json(self._boot(cat))
        if route == ("GET", "/api/meta"):
            return self._json(cat.meta())
        if route == ("GET", "/api/search"):
            size = max(1, min(int(qs.get("size") or cfg["search"]["page_size"]), 200))
            page = max(1, int(qs.get("page") or 1))
            group = cfg["search"]["group_annexes"] and qs.get("group") != "0"
            t0 = time.perf_counter()
            rows, total = cat.query(qs, size, (page - 1) * size, group=group)
            if not group:
                ann = cat.annexes_of([r["id"] for r in rows])
                for r in rows:
                    r["annexes"] = ann.get(r["id"], [])
            return self._json({"rows": self._strip(rows), "total": total, "page": page, "size": size,
                               "grouped": bool(group),
                               "ms": round((time.perf_counter() - t0) * 1000)})
        if route == ("GET", "/api/book"):
            b = cat.get_full(int(qs.get("id", 0)))
            if not b:
                raise NotFound()
            return self._json(self._strip([b])[0])
        if route in (("POST", "/api/book"), ("PUT", "/api/book")):
            self._need("edit" if method == "PUT" else "add")
            d = self._jbody()
            bid = int(qs["id"]) if method == "PUT" else None
            cat._prep(d)  # בדיקת תקינות לפני כפילויות
            if not d.get("force"):
                dup = cat.find_duplicate(d, bid)
                if dup:
                    return self._json({"error": "dup", "dup": dup}, 409)
            if bid:
                cat.update(bid, d)
            else:
                bid = cat.add(d)
            self._touch(cat)
            return self._json({"id": bid})
        if route == ("DELETE", "/api/book"):
            self._need("delete")
            cat.delete([int(qs["id"])])
            self._touch(cat)
            return self._json({"ok": True})
        if route == ("POST", "/api/books/bulk"):
            self._need("bulk")
            d = self._jbody()
            ids = [int(x) for x in (d.get("ids") or [])][:5000]
            if not ids:
                raise ValueError("לא נבחרו ספרים")
            if d.get("action") == "delete":
                self._need("delete")
                cat.delete(ids)
                n = len(ids)
            elif d.get("action") == "set":
                self._need("edit")
                n = cat.bulk_set(ids, str(d.get("field") or ""), d.get("value", ""))
            else:
                raise ValueError("פעולה לא מוכרת")
            self._touch(cat)
            return self._json({"count": n})
        # ----- מיקומים -----
        if route == ("POST", "/api/location"):
            self._need("locations")
            d = self._jbody()
            cat.add_location(d.get("name"), d)
            return self._json({"ok": True})
        if route == ("PUT", "/api/location"):
            self._need("locations")
            d = self._jbody()
            cat.rename_location(qs["name"], d.get("name"), d if "shelf_from" in d or "letter" in d else None)
            return self._json({"ok": True})
        if route == ("DELETE", "/api/location"):
            self._need("locations")
            cat.delete_location(qs["name"])
            return self._json({"ok": True})
        if route == ("POST", "/api/locations/order"):
            self._need("locations")
            cat.order_locations([str(x) for x in self._jbody().get("names") or []])
            return self._json({"ok": True})
        if route == ("POST", "/api/locations/apply"):
            self._need("locations")
            n = cat.apply_location_rules()
            self._touch(cat)
            return self._json({"changed": n})
        # ----- רשימות ערכים -----
        if route == ("GET", "/api/values"):
            self._need("values")
            return self._json({"values": cat.value_counts(qs.get("field", ""))})
        if route == ("POST", "/api/values"):
            self._need("values")
            d = self._jbody()
            n = cat.rename_value(str(d.get("field") or ""), str(d.get("old") or ""), d.get("new"))
            self._touch(cat)
            return self._json({"count": n})
        # ----- ייבוא ושחזור -----
        if route == ("POST", "/api/import"):
            self._need("import")
            mode = qs.get("mode") or ("replace" if qs.get("replace") == "1" else "add")
            if mode == "replace":
                self._need("delete")
            if mode == "replace" and cfg["general"]["auto_backup"]:
                os.makedirs(BACKUP_DIR, exist_ok=True)
                cat.backup_to(os.path.join(BACKUP_DIR, "before-import.db"))
            res = cat.import_file(self._body(), mode)
            self._touch(cat)
            return self._json(res)
        if route == ("POST", "/api/restore"):
            self._need("restore")
            fd, tmp = tempfile.mkstemp(suffix=".db")
            try:
                with os.fdopen(fd, "wb") as f:
                    f.write(self._body())
                cat.restore_from(tmp, keep_settings=qs.get("keep") != "0")
            finally:
                os.remove(tmp)
            return self._json({"ok": True})
        # ----- הגדרות (מנהל בלבד) -----
        if route == ("PUT", "/api/config"):
            self._need()
            cat.save_config(self._jbody())
            return self._json(self._boot(cat))
        if route == ("POST", "/api/config/reset"):
            self._need()
            cat.reset_config(qs.get("section") or None)
            return self._json(self._boot(cat))
        if route == ("POST", "/api/asset"):
            self._need()
            cat.set_asset(qs.get("name", ""), self._body())
            if qs.get("name") == "icon":
                threading.Thread(target=apply_window_icon, args=(cat, None, False), daemon=True).start()
            return self._json(self._boot(cat))
        if route == ("DELETE", "/api/asset"):
            self._need()
            cat.delete_asset(qs.get("name", ""))
            return self._json(self._boot(cat))
        if route == ("POST", "/api/open-path"):
            d = self._jbody()
            p = str(d.get("path") or "")
            if p not in self.server.saved:      # רק קבצים שהתוכנה עצמה שמרה זה עתה
                raise Forbidden()
            open_path(os.path.dirname(p) if d.get("folder") else p)
            return self._json({"ok": True})
        if route == ("POST", "/api/quit"):
            self._need("quit")
            self._json({"ok": True})
            srv = self.server

            def stop():
                time.sleep(0.2)
                win = RUN.get("window")
                if win is not None and RUN.get("srv") is srv:
                    try:
                        win.destroy()
                        return
                    except Exception:
                        pass
                srv.shutdown()
            threading.Thread(target=stop, daemon=True).start()
            return
        self._json({"error": "לא נמצא"}, 404)

    @staticmethod
    def _touch(cat):
        try:
            cat.auto_backup()
        except Exception:
            pass

    def do_GET(self): self._handle("GET")
    def do_POST(self): self._handle("POST")
    def do_PUT(self): self._handle("PUT")
    def do_DELETE(self): self._handle("DELETE")


def make_server(cat, port, updater=None):
    srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    srv.daemon_threads = True
    srv.cat = cat
    srv.updater = updater
    srv.sessions = Sessions()
    srv.saved = set()
    return srv


# =====================================================================
#                              הדף
# =====================================================================
PAGE = r"""<!doctype html>
<html lang="he" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>קטלוג ספרים</title>
<link rel="icon" id="favicon" href="data:,">
<script>const B=__BOOT__;</script>
<style>
/* כל הצבעים, הגופנים והמידות מגיעים מההגדרות (מצב מנהל > עיצוב) דרך המשתנים שלמטה */
:root{
  --bg:#F5EEDC;--panel:#FFFDF6;--fg:#1C150E;--muted:#5A4C39;--line:#C9B88F;
  --accent:#6B1322;--accent-fg:#FFF8E6;--gold:#A87A1C;--link:#5A0E1B;--mark:#F6DC83;--chip:#EADFC2;
  --ok:#1F7A3A;--bad:#A61C1C;
  --serif:"Frank Ruhl Libre","FrankRuehl","David","Times New Roman",serif;
  --sans:"Segoe UI",Arial,"Noto Sans Hebrew",sans-serif;
  --fs:16px;--radius:10px;--resw:980px;--pad:1;
  --hover:color-mix(in srgb,var(--chip) 55%,var(--panel));
  --shadow:0 6px 22px color-mix(in srgb,var(--fg) 22%,transparent);
  --soft:color-mix(in srgb,var(--gold) 16%,var(--panel));
}
*{box-sizing:border-box}
html{font-size:var(--fs)}
body{margin:0;background:var(--bg);color:var(--fg);font:1rem/1.6 var(--sans);min-height:100vh}
body.orn{background-image:radial-gradient(color-mix(in srgb,var(--gold) 9%,transparent) 1px,transparent 1.4px);background-size:22px 22px}
button,input,select,textarea{font:inherit;color:inherit}
button{cursor:pointer}
a{color:var(--link);text-decoration:none}
[hidden]{display:none!important}
:focus-visible{outline:3px solid var(--gold);outline-offset:2px}
.btn{border:1.5px solid var(--line);background:var(--panel);border-radius:var(--radius);padding:.5em 1.1em;font-weight:600;transition:border-color .15s,background .15s;white-space:nowrap}
.btn:hover{border-color:var(--accent);background:var(--hover)}
.btn.primary{background:var(--accent);color:var(--accent-fg);border-color:var(--accent)}
.btn.primary:hover{filter:brightness(1.15)}
.btn.gold{background:var(--gold);color:#fff;border-color:var(--gold)}
.btn.danger{color:var(--bad);border-color:color-mix(in srgb,var(--bad) 45%,var(--line))}
.btn.sm{padding:.25em .7em;font-size:.86rem;font-weight:500}
.btn:disabled{opacity:.5;cursor:default}
.icon{border:1.5px solid transparent;background:none;width:2.5em;height:2.5em;border-radius:50%;font-size:1.15rem;color:var(--fg);display:inline-grid;place-items:center}
.icon:hover{background:var(--chip);border-color:var(--line)}
.icon.on{background:var(--accent);color:var(--accent-fg)}
input[type=text],input[type=search],input[type=number],input[type=password],input:not([type]),select,textarea{border:1.5px solid var(--line);border-radius:calc(var(--radius)*.8);padding:.45em .65em;background:var(--panel);outline:0;min-width:0}
input:focus,select:focus,textarea:focus{border-color:var(--accent);box-shadow:0 0 0 3px color-mix(in srgb,var(--gold) 35%,transparent)}
input[type=color]{width:3em;height:2.2em;padding:2px;border:1.5px solid var(--line);border-radius:6px;background:var(--panel)}
input[type=checkbox],input[type=radio]{width:1.1em;height:1.1em;accent-color:var(--accent);vertical-align:-.15em}

/* ----- מסך פתיחה ----- */
#splash{position:fixed;inset:0;z-index:1000;display:grid;place-items:center;background:#000;transition:opacity .6s}
#splash img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover}
#splash .cap{position:relative;color:#fff;font:700 3rem var(--serif);text-shadow:0 2px 14px #000;padding:1em;text-align:center}
#splash.out{opacity:0;pointer-events:none}

/* ----- כותרת / חיפוש ----- */
#top{display:flex;align-items:flex-start;gap:1.1em;padding:.75em 1.6em .4em;border-bottom:2px solid var(--gold);position:sticky;top:0;background:var(--panel);z-index:5;box-shadow:0 2px 0 var(--panel),0 3px 0 var(--line)}
#logo{display:flex;align-items:center;gap:.45em;font:700 1.6rem/1 var(--serif);color:var(--accent);white-space:nowrap;padding-top:.3em}
#logoMark{font-size:1.25em;line-height:1}
#logoMark img{height:1.5em;max-width:6em;object-fit:contain;display:block}
#sbwrap{flex:1;max-width:820px;min-width:0}
#sf{display:flex;align-items:center;gap:.4em;border:2px solid var(--accent);border-radius:2em;padding:.15em .3em .15em 1em;background:var(--panel);height:3em;transition:box-shadow .15s}
#sf:hover,#sf:focus-within{box-shadow:var(--shadow)}
#sf .mag{color:var(--accent);font-size:1.1em}
#q{flex:1;border:0!important;box-shadow:none!important;outline:0;background:none;font-size:1.08rem;min-width:0;height:100%;padding:0 .3em}
#q::-webkit-search-cancel-button,#q::-webkit-search-decoration{-webkit-appearance:none;display:none}
#clr{border:0;background:none;color:var(--muted);font-size:1.1rem;padding:0 .4em}
#sgo{border:0;background:var(--accent);color:var(--accent-fg);border-radius:2em;height:2.4em;padding:0 1.2em;font-weight:700}
#sgo:hover{filter:brightness(1.15)}
#types{display:flex;gap:.2em;flex-wrap:wrap;margin-top:.35em}
#types button{border:0;background:none;padding:.3em .8em;border-bottom:3px solid transparent;color:var(--muted);font-weight:600;border-radius:6px 6px 0 0}
#types button:hover{color:var(--fg);background:var(--hover)}
#types button.on{color:var(--accent);border-bottom-color:var(--accent)}
.sbtns{display:none;justify-content:center;gap:.7em;margin-top:1.4em}
.right{margin-inline-start:auto;display:flex;gap:.45em;align-items:center;position:relative;padding-top:.15em}
#adminTag{background:var(--accent);color:var(--accent-fg);border-radius:1em;padding:.1em .8em;font-size:.82rem;font-weight:700}
#menu{position:absolute;top:3.1em;left:0;background:var(--panel);border:1.5px solid var(--line);border-radius:var(--radius);box-shadow:var(--shadow);min-width:16.5em;padding:.4em 0;z-index:20}
#menu button{display:block;width:100%;text-align:right;border:0;background:none;padding:.55em 1.1em}
#menu button:hover{background:var(--chip)}
#menu hr{border:0;border-top:1.5px solid var(--line);margin:.35em 0}

body.home #top{position:static;border:0;box-shadow:none;background:none;flex-direction:column;align-items:center;gap:0;padding-top:9vh}
body.home #logo{font-size:3.6rem;flex-direction:column;gap:.15em;padding:0}
body.home #logoMark img{height:2.2em;max-width:9em}
body.home #sbwrap{width:min(720px,94vw);flex:none}
body.home #sf{height:3.5em;border-width:2.5px}
body.home #types{justify-content:center;gap:.5em;margin-top:1em}
body.home #types button{border:1.5px solid var(--line);border-radius:2em;background:var(--panel);padding:.3em 1.05em;color:var(--fg)}
body.home #types button.on{background:var(--accent);color:var(--accent-fg);border-color:var(--accent)}
body.home #types.select button{display:none}
body.home .sbtns{display:flex}
body.home .right{position:absolute;top:.9em;left:1.2em}
body.home #advtoggle{display:none}
#typesCap{display:none;text-align:center;color:var(--muted);font-size:.9rem;margin:1.1em 0 -.5em}
body.home #typesCap{display:block}
#tagline{display:none;text-align:center;color:var(--muted);font:1.15rem/1.4 var(--serif);margin:.2em 0 1.2em}
body.home #tagline{display:block}
.divider{display:none;align-items:center;justify-content:center;gap:.7em;color:var(--gold);margin:.5em auto .3em;width:min(420px,80vw)}
.divider::before,.divider::after{content:"";flex:1;height:0;border-top:1.5px solid var(--gold);box-shadow:0 3px 0 -1.5px var(--gold)}
body.home.orn .divider{display:flex}

/* ----- חיפוש מתקדם ----- */
#adv{border-bottom:1.5px solid var(--line);background:var(--soft);padding:1.1em 1.6em}
#adv form{max-width:1100px;margin:auto;display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:.8em}
#adv label,.fgrid label{display:flex;flex-direction:column;font-size:.86rem;font-weight:600;color:var(--muted);gap:.25em}
#adv label>*,.fgrid label>input,.fgrid label>select,.fgrid label>textarea{font-size:1rem;font-weight:400;color:var(--fg)}
#adv .row{grid-column:1/-1;display:flex;gap:.6em;align-items:center}
.pair{display:flex;gap:.4em;align-items:center}

/* ----- דף הבית ----- */
#home{max-width:820px;margin:2em auto;padding:0 1.1em;text-align:center}
.chips{display:flex;flex-wrap:wrap;gap:.6em;justify-content:center;margin:.6em 0 1.5em}
.chip{border:1.5px solid var(--line);background:var(--panel);border-radius:var(--radius);padding:.5em 1.1em;font:600 1.05rem var(--serif);display:flex;flex-direction:column;min-width:8em}
.chip:hover{background:var(--hover);border-color:var(--accent)}
.chip small{color:var(--muted);font:.8rem var(--sans)}
.cap{color:var(--muted);font-size:.9rem}
.bar{width:260px;height:6px;background:var(--chip);border-radius:3px;margin:.6em auto;overflow:hidden}
.bar i{display:block;height:100%;background:var(--gold)}

/* ----- תוצאות ----- */
#res{max-width:var(--resw);margin:0 auto;padding:0 1.5em 2.5em}
#stats{display:flex;align-items:center;gap:.8em;color:var(--muted);font-size:.9rem;padding:.8em 0;flex-wrap:wrap;border-bottom:1.5px solid var(--line)}
#stats .sp{margin-inline-start:auto;display:flex;gap:.5em;align-items:center;flex-wrap:wrap}
#stats select{padding:.2em .4em;font-size:.9rem}
.seg{display:inline-flex;border:1.5px solid var(--line);border-radius:var(--radius);overflow:hidden;background:var(--panel)}
.seg button{border:0;background:none;padding:.25em .75em;font-size:.88rem;font-weight:600;color:var(--fg)}
.seg button+button{border-inline-start:1.5px solid var(--line)}
.seg button.on{background:var(--accent);color:var(--accent-fg)}
#bulk{display:flex;gap:.6em;align-items:center;flex-wrap:wrap;background:var(--soft);border:1.5px solid var(--gold);border-radius:var(--radius);padding:.5em .9em;margin-top:.7em}
.r{display:block;padding:calc(1.1em*var(--pad)) 1.1em;margin:0 -1.1em;border-bottom:1.5px solid var(--line);cursor:pointer;border-inline-start:4px solid transparent;transition:background .12s,border-color .12s}
.r:hover{background:var(--panel);border-inline-start-color:var(--gold)}
.r:last-child{border-bottom:0}
.r .path{font-size:.86rem;color:var(--muted);margin-bottom:.2em;display:flex;gap:.5em;align-items:center;flex-wrap:wrap}
.r .path a{color:var(--muted);font-weight:600}
.r .path a:hover{color:var(--accent);text-decoration:underline}
.r h3{margin:0 0 .15em;font:700 1.45rem/1.3 var(--serif);color:var(--link)}
.r:hover h3 .t{text-decoration:underline;text-decoration-color:var(--gold)}
.r .vol{font:500 .95rem var(--sans);color:var(--muted)}
.r .meta{font-size:.95rem;color:var(--muted);margin-bottom:.25em}
.r .meta b{color:var(--fg);font-weight:700}
.r .snip{margin:.45em 0 0;color:var(--fg);font-size:.98rem;line-height:1.6}
.tags{margin-top:.55em;display:flex;gap:.4em;flex-wrap:wrap}
.tag{font-size:.8rem;border-radius:6px;padding:.12em .7em;background:var(--accent);color:var(--accent-fg);font-weight:600}
.tag.outline{background:var(--chip);color:var(--fg);font-weight:500}
.tag.cond{background:var(--panel);border:1.5px solid var(--line);color:var(--fg);font-weight:500}
.lbl{display:inline-grid;place-items:center;min-width:1.7em;height:1.7em;padding:0 .3em;border:2px solid var(--gold);border-radius:5px;background:var(--panel);color:var(--fg);font:700 .95rem var(--serif)}
.badge{background:var(--gold);color:#fff;border-radius:5px;padding:0 .55em;font-size:.78rem;font-weight:700}
.dot{display:inline-block;width:.6em;height:.6em;border-radius:50%;margin-inline-end:.35em}
mark{background:var(--mark);color:inherit;border-radius:3px;padding:0 2px}
.anx{margin-top:.7em;border:1.5px solid var(--gold);border-radius:var(--radius);background:var(--soft);padding:.45em .8em}
.anx .hd{font-size:.82rem;font-weight:700;color:var(--muted);margin-bottom:.2em}
.anx ul{margin:0;padding:0;list-style:none}
.anx li{padding:.15em 0;font-size:.95rem;display:flex;gap:.45em;align-items:baseline;flex-wrap:wrap}
.anx li a{font:700 1.05rem var(--serif)}
.anx li a:hover{text-decoration:underline}
.anx li.hit{background:color-mix(in srgb,var(--mark) 45%,transparent);margin:0 -.4em;padding:.15em .4em;border-radius:5px}
.anx li small{color:var(--muted)}
.anx .more{border:0;background:none;color:var(--link);font-size:.85rem;font-weight:600;padding:.2em 0;text-decoration:underline}
.found{font-size:.9rem;font-weight:700;color:var(--accent);margin-bottom:.15em}
.parentln{font-size:.92rem;margin-bottom:.2em}
.parentln a{font-weight:700;text-decoration:underline}
#list.v-list .r{padding:.42em 1.1em;display:flex;gap:.8em;align-items:baseline;flex-wrap:wrap}
#list.v-list .r h3{font-size:1.12rem;margin:0}
#list.v-list .r .who{color:var(--fg);font-size:.92rem}
#list.v-list .r .loc{margin-inline-start:auto;color:var(--muted);font-size:.86rem;white-space:nowrap}
#list.v-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(270px,1fr));gap:.9em;padding-top:1em}
#list.v-grid .r{margin:0;border:1.5px solid var(--line);border-top:4px solid var(--accent);border-radius:var(--radius);background:var(--panel);padding:.9em}
#list.v-grid .r:hover{border-color:var(--gold);box-shadow:var(--shadow)}
#list.v-grid .r h3{font-size:1.2rem}
.tblwrap{overflow:auto;margin-top:.8em;border:1.5px solid var(--line);border-radius:var(--radius);background:var(--panel)}
table.t{width:100%;border-collapse:collapse;font-size:.92rem}
table.t th{background:var(--accent);color:var(--accent-fg);padding:.5em .6em;text-align:right;white-space:nowrap;position:sticky;top:0;cursor:pointer;font-weight:700}
table.t td{padding:.4em .6em;border-top:1px solid var(--line);vertical-align:top;max-width:26em}
table.t tr.r2{cursor:pointer}
table.t tr.r2:nth-child(even) td{background:color-mix(in srgb,var(--chip) 35%,var(--panel))}
table.t tr.r2:hover td{background:var(--hover)}
table.t td.ti{font:700 1.05rem var(--serif);color:var(--link)}
.empty{padding:3em .6em;color:var(--muted);text-align:center}
.empty b{color:var(--fg);font:700 1.3rem var(--serif);display:block;margin-bottom:.3em}
#pager{display:flex;gap:.35em;justify-content:center;flex-wrap:wrap;margin-top:1.6em}
#pager button{border:1.5px solid transparent;background:none;min-width:2.4em;height:2.4em;border-radius:1.2em;color:var(--link);font-weight:600;padding:0 .6em}
#pager button:hover{background:var(--chip);border-color:var(--line)}
#pager button.cur{background:var(--accent);color:var(--accent-fg);cursor:default}
#pager button:disabled{color:var(--muted);cursor:default;background:none;border-color:transparent;opacity:.6}

/* ----- חלונות ----- */
dialog{border:2px solid var(--gold);border-radius:calc(var(--radius)*1.3);padding:0;background:var(--panel);color:var(--fg);width:min(800px,95vw);max-height:93vh;box-shadow:var(--shadow)}
dialog::backdrop{background:rgba(20,14,8,.62)}
dialog .in{padding:1.3em 1.5em}
dialog h2{margin:0 0 .8em;font:700 1.55rem var(--serif);color:var(--accent);border-bottom:1.5px solid var(--line);padding-bottom:.35em}
dialog.small{width:min(460px,94vw)}
.fgrid{display:grid;grid-template-columns:1fr 1fr;gap:.8em}
.fgrid .full{grid-column:1/-1}
.fgrid textarea{min-height:5em;resize:vertical}
.hint{font-size:.8rem;color:var(--muted);font-weight:400}
.err{color:var(--bad);min-height:1.3em;margin-top:.5em;font-weight:600}
.acts{display:flex;gap:.5em;margin-top:.9em;flex-wrap:wrap;align-items:center}
.acts .sp{margin-inline-start:auto}
.dl{display:grid;grid-template-columns:max-content 1fr;gap:.35em 1.1em;margin:0}
.dl dt{color:var(--muted);font-weight:700;font-size:.9rem}
.dl dd{margin:0;white-space:pre-wrap;overflow-wrap:anywhere}
#vTitle{font:700 1.9rem/1.25 var(--serif);color:var(--accent);margin:0 0 .1em;border:0;padding:0}
.pick{position:relative}
.pick .dd{position:absolute;inset-inline:0;top:100%;background:var(--panel);border:1.5px solid var(--accent);border-radius:8px;box-shadow:var(--shadow);z-index:5;max-height:15em;overflow:auto}
.pick .dd button{display:block;width:100%;text-align:right;border:0;background:none;padding:.35em .7em;font-weight:400}
.pick .dd button:hover{background:var(--chip)}
#toast{position:fixed;bottom:1.4em;left:1.4em;background:var(--fg);color:var(--bg);padding:.65em 1.1em;border-radius:8px;opacity:0;transition:.25s;pointer-events:none;z-index:2000;max-width:min(560px,90vw);font-weight:600;display:flex;gap:.7em;align-items:center;flex-wrap:wrap}
#toast.on{opacity:1;pointer-events:auto}
#toast button{border:1.5px solid currentColor;background:none;color:inherit;border-radius:6px;padding:.1em .7em;font-weight:700}
footer{text-align:center;color:var(--muted);font-size:.85rem;padding:1.1em}

/* ----- עדכון גרסה ----- */
#updBar{display:flex;flex-wrap:wrap;gap:.5em .9em;align-items:center;justify-content:center;background:var(--mark);color:#1C150E;border-bottom:1.5px solid var(--gold);padding:.55em 1.1em}
#updBar .btn{padding:.2em .9em;font-size:.88rem}
#updBar .bar{width:160px;margin:0}
#updBar details{flex-basis:100%;text-align:center}
#updBar .notes{white-space:pre-line;text-align:right;display:inline-block;margin-top:.4em;max-width:640px;font-size:.88rem}

/* ----- מצב מנהל: הגדרות ----- */
#adm{width:min(1180px,98vw);height:94vh;max-height:94vh}
#adm[open]{display:flex;flex-direction:column}
#admHead{display:flex;align-items:center;gap:.8em;background:var(--accent);color:var(--accent-fg);padding:.7em 1.2em}
#admHead h2{margin:0;border:0;padding:0;color:inherit;flex:1;font-size:1.4rem}
#admHead .btn{background:transparent;color:inherit;border-color:currentColor}
#admBody{display:flex;flex:1;min-height:0}
#admNav{width:14.5em;border-inline-end:1.5px solid var(--line);background:var(--soft);overflow:auto;padding:.5em 0;flex:none}
#admNav button{display:flex;gap:.6em;width:100%;text-align:right;border:0;background:none;padding:.6em 1.1em;font-weight:600;border-inline-start:4px solid transparent}
#admNav button:hover{background:var(--hover)}
#admNav button.on{background:var(--panel);border-inline-start-color:var(--accent);color:var(--accent)}
#admMain{flex:1;overflow:auto;padding:1.2em 1.6em}
#admMain h3{font:700 1.3rem var(--serif);color:var(--accent);margin:0 0 .2em}
#admMain h4{margin:1.5em 0 .5em;font-size:1rem;border-bottom:1.5px solid var(--line);padding-bottom:.2em}
#admMain p.d{color:var(--muted);margin:.1em 0 1em;font-size:.93rem}
#admFoot{display:flex;gap:.6em;align-items:center;border-top:1.5px solid var(--line);padding:.7em 1.2em;background:var(--soft)}
#admFoot .sp{margin-inline-start:auto}
#dirty{color:var(--bad);font-weight:700}
.sg{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:.8em 1.2em;align-items:end}
.sg label,.sl{display:flex;flex-direction:column;gap:.2em;font-size:.88rem;font-weight:600;color:var(--muted)}
.sg label>input,.sg label>select,.sg label>textarea{font-size:1rem;font-weight:400;color:var(--fg)}
.sg label.ck,label.ck{flex-direction:row;align-items:center;gap:.5em;color:var(--fg);font-size:.98rem;font-weight:500;display:flex}
.sg .full{grid-column:1/-1}
.cl{display:flex;align-items:center;gap:.5em}
table.s{border-collapse:collapse;width:100%}
table.s th{font-size:.82rem;color:var(--muted);text-align:right;padding:.3em .4em;border-bottom:1.5px solid var(--line);white-space:nowrap}
table.s td{padding:.3em .4em;border-bottom:1px solid var(--line);vertical-align:middle}
table.s td.c,table.s th.c{text-align:center}
table.s input[type=text],table.s input:not([type]){width:100%}
.presets{display:flex;gap:.7em;flex-wrap:wrap}
.preset{border:2px solid var(--line);border-radius:var(--radius);padding:.5em .7em;background:var(--panel);min-width:8.5em;text-align:center;font-weight:600}
.preset.on{border-color:var(--accent);box-shadow:0 0 0 2px var(--gold)}
.preset i{display:flex;height:1.6em;border-radius:5px;overflow:hidden;margin-bottom:.35em;border:1px solid #0003}
.preset i b{flex:1}
.fchips{display:flex;gap:.3em;flex-wrap:wrap}
.fchips label{border:1.5px solid var(--line);border-radius:1em;padding:0 .6em;font-size:.82rem;cursor:pointer;background:var(--panel);font-weight:500;color:var(--fg)}
.fchips label:has(input:checked){background:var(--accent);color:var(--accent-fg);border-color:var(--accent)}
.fchips input{display:none}
.ctr{display:inline-block;border-radius:5px;padding:0 .6em;font-size:.82rem;font-weight:700;color:#fff}
.prev{border:1.5px dashed var(--line);border-radius:var(--radius);padding:.6em;display:inline-flex;align-items:center;gap:.8em;min-height:3.5em;background:var(--bg)}
.prev img{max-height:6em;max-width:16em;display:block}
.note{background:var(--soft);border:1.5px solid var(--gold);border-radius:var(--radius);padding:.6em .9em;font-size:.93rem;margin:.6em 0}
body.dense{--pad:.6}
body.wide{--pad:1.35}
@media(max-width:760px){.fgrid{grid-template-columns:1fr}#top{flex-wrap:wrap;padding:.6em .9em}#logo{font-size:1.25rem}#admNav{width:9.5em}body.home #logo{font-size:2.5rem}}
@media print{#top,#adv,#pager,#stats .sp,footer,#updBar,#bulk{display:none!important}body{background:#fff}}
</style>
</head>
<body class="home">
<div id="splash" hidden><img alt=""><div class="cap"></div></div>
<div id="updBar" hidden></div>
<header id="top">
  <a id="logo" href="#" title="דף הבית"><span id="logoMark"></span><span id="logoTxt"></span></a>
  <div id="sbwrap">
    <div class="divider">❖</div>
    <p id="tagline"></p>
    <form id="sf" autocomplete="off">
      <span class="mag">🔍</span>
      <input id="q" type="search" aria-label="חיפוש">
      <button type="button" id="clr" hidden aria-label="נקה">✕</button>
      <button type="submit" id="sgo"></button>
    </form>
    <div id="typesCap"></div>
    <div id="types" role="tablist"></div>
    <div class="sbtns">
      <button class="btn" id="advBtn" type="button"></button>
    </div>
  </div>
  <div class="right">
    <button class="btn" id="advtoggle" type="button"></button>
    <button class="btn primary" id="addBtn" type="button"></button>
    <span id="adminTag" hidden>מצב מנהל</span>
    <button class="icon" id="setBtn" type="button" title="הגדרות התוכנה (מנהל)" hidden>⚙</button>
    <button class="icon" id="adminBtn" type="button" title="מצב מנהל">🔒</button>
    <button class="icon" id="menuBtn" type="button" aria-label="תפריט">⋮</button>
    <div id="menu" hidden></div>
  </div>
</header>

<section id="adv" hidden><form id="advForm"></form></section>

<section id="home">
  <div id="homeLocs"><div class="cap" id="homeLocCap"></div><div class="chips" id="homeChips"></div></div>
  <div class="bar" id="homeBarWrap"><i id="homeBar"></i></div>
  <div class="cap" id="homeCount"></div>
</section>

<section id="res" hidden>
  <div id="stats"><span id="statTxt"></span>
    <span class="sp">
      <span class="seg" id="viewSeg"></span>
      <label id="sortWrap">מיון: <select id="sort"></select> <select id="dir"><option value="asc">עולה</option><option value="desc">יורד</option></select></label>
      <label id="sizeWrap">בעמוד: <select id="psize"></select></label>
      <button class="btn sm" id="expBtn" type="button">⬇ ייצוא</button>
    </span></div>
  <div id="bulk" hidden></div>
  <div id="list"></div>
  <nav id="pager"></nav>
</section>
<footer id="foot"></footer>

<!-- כרטיס ספר -->
<dialog id="viewDlg"><div class="in">
  <div id="vBody"></div>
  <div class="acts"><button class="btn primary" id="vEdit" type="button">✎ עריכה</button>
    <button class="btn" id="vShelf" type="button">כל הספרים במדף</button>
    <button class="btn sp" id="vClose" type="button">סגירה</button></div>
</div></dialog>

<!-- עריכת ספר -->
<dialog id="dlg"><div class="in">
  <h2 id="dlgTitle"></h2>
  <div class="fgrid" id="formGrid"></div>
  <datalist id="dl_subject"></datalist><datalist id="dl_topics"></datalist><datalist id="dl_publisher"></datalist><datalist id="dl_pub_place"></datalist><datalist id="dl_label"></datalist>
  <div class="err" id="dlgErr"></div>
  <div class="acts">
    <button class="btn primary" id="saveBtn" type="button">שמירה</button>
    <button class="btn" id="saveAddBtn" type="button">שמירה והוספת ספר נוסף</button>
    <button class="btn" id="cancelBtn" type="button">ביטול</button>
    <button class="btn danger sp" id="delBtn" type="button">מחיקת הספר</button>
  </div>
</div></dialog>

<!-- ייבוא -->
<dialog id="impDlg"><div class="in">
  <h2>ייבוא מקובץ (Excel או CSV)</h2>
  <p class="cap" id="impCols"></p>
  <p><input type="file" id="impFile" accept=".csv,.xlsx,text/csv"></p>
  <p><label class="ck"><input type="radio" name="impMode" value="add" checked> הוספה לקטלוג הקיים</label>
     <label class="ck"><input type="radio" name="impMode" value="update"> עדכון ספרים קיימים (לפי שם, מחבר, כרך ומדף) והוספת החדשים</label>
     <label class="ck"><input type="radio" name="impMode" value="replace"> החלפת כל הקטלוג (מוחק את הקיים!)</label></p>
  <div class="err" id="impErr"></div>
  <div class="acts"><button class="btn primary" id="impGo" type="button">ייבוא</button><button class="btn" id="impCancel" type="button">ביטול</button></div>
</div></dialog>

<!-- ייצוא -->
<dialog id="expDlg"><div class="in">
  <h2>ייצוא הקטלוג</h2>
  <h4 style="margin:.2em 0">סוג הקובץ</h4>
  <div id="expFmt"></div>
  <h4 style="margin:.9em 0 .2em">מה לייצא?</h4>
  <div id="expScope"></div>
  <h4 style="margin:.9em 0 .2em">עמודות <button class="btn sm" id="expAll" type="button">הכל</button> <button class="btn sm" id="expNone" type="button">נקה</button></h4>
  <div class="fchips" id="expCols"></div>
  <div class="err" id="expErr"></div>
  <div class="acts"><button class="btn primary" id="expGo" type="button">ייצוא</button><button class="btn" id="expCancel" type="button">ביטול</button></div>
</div></dialog>

<!-- כניסת מנהל -->
<dialog id="loginDlg" class="small"><div class="in">
  <h2 id="loginTitle">כניסה למצב מנהל</h2>
  <p class="cap" id="loginInfo"></p>
  <div class="fgrid" style="grid-template-columns:1fr">
    <label>סיסמה<input id="lp1" type="password" autocomplete="off"></label>
    <label id="lp2w">אימות הסיסמה<input id="lp2" type="password" autocomplete="off"></label>
  </div>
  <div class="err" id="loginErr"></div>
  <div class="acts"><button class="btn primary" id="loginGo" type="button">כניסה</button><button class="btn" id="loginCancel" type="button">ביטול</button></div>
</div></dialog>

<!-- אשף הגדרה ראשונית (התקנה חדשה בלי פרופיל) -->
<dialog id="wizDlg"><div class="in">
  <h2>ברוכים הבאים — הגדרה ראשונית</h2>
  <p class="cap">כמה פרטים על הספרייה, ואפשר להתחיל. את הכול אפשר לשנות אחר כך במצב מנהל.</p>
  <div class="fgrid">
    <label class="full">שם הספרייה (יופיע ככותרת התוכנה) *<input id="w_name"></label>
    <label class="full">משפט מתחת לכותרת (לא חובה)<input id="w_tagline"></label>
    <label>סימן ליד הכותרת<input id="w_emoji" value="📚"></label>
    <label>ערכת צבעים<select id="w_preset"></select></label>
  </div>
  <h4 style="margin:1em 0 .2em">מיקומים ומדפים (לא חובה)</h4>
  <p class="hint">המיקום של ספר נקבע לפי מספר המדף שלו: לכל מיקום טווח מדפים, או אות שנכתבת ליד מספר המדף.</p>
  <table class="s"><thead><tr><th>שם המיקום</th><th style="width:6.5em">ממדף</th><th style="width:6.5em">עד מדף</th><th style="width:5.5em">אות</th></tr></thead><tbody id="w_locs"></tbody></table>
  <div class="acts" style="margin-top:.4em"><button class="btn sm" id="wizAddLoc" type="button">＋ מיקום נוסף</button></div>
  <h4 style="margin:1em 0 .2em">ספרים</h4>
  <label class="ck"><input type="radio" name="w_start" value="0" checked> להתחיל עם קטלוג ריק</label>
  <label class="ck"><input type="radio" name="w_start" value="1"> להתחיל עם קטלוג בסיסי (חומשים, משניות, ש״ס, רמב״ם, טור ושולחן ערוך, משנה ברורה) — מוחקים מה שלא צריך</label>
  <h4 style="margin:1em 0 .2em">סיסמת מנהל *</h4>
  <div class="fgrid"><label>סיסמה (לפחות 4 תווים)<input id="w_pw" type="password" autocomplete="off"></label><label>אימות הסיסמה<input id="w_pw2" type="password" autocomplete="off"></label></div>
  <div class="err" id="wizErr"></div>
  <div class="acts"><button class="btn primary" id="wizGo" type="button">סיום והתחלה</button><button class="btn sp" id="wizSkip" type="button">דילוג — אגדיר אחר כך</button></div>
</div></dialog>

<!-- הגדרות (מצב מנהל) -->
<dialog id="adm">
  <div id="admHead"><h2>⚙ הגדרות התוכנה — מצב מנהל</h2><button class="btn sm" id="admLock" type="button">🔒 יציאה ממצב מנהל</button><button class="btn sm" id="admX" type="button">✕ סגירה</button></div>
  <div id="admBody"><nav id="admNav"></nav><div id="admMain"></div></div>
  <div id="admFoot"><button class="btn primary" id="admSave" type="button">שמירת השינויים</button>
    <button class="btn" id="admRevert" type="button">ביטול השינויים</button><span id="dirty" hidden>● יש שינויים שלא נשמרו</span>
    <button class="btn sm sp" id="admReset" type="button">איפוס הקטגוריה לברירת המחדל</button></div>
</dialog>
<input type="file" id="restoreFile" accept=".db" hidden>
<input type="file" id="assetFile" hidden>
<input type="file" id="updFile" hidden>
<div id="toast"></div>

<script>
'use strict';
const $=s=>document.querySelector(s), $$=s=>[...document.querySelectorAll(s)];
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const nrm=s=>String(s??'').replace(/[֑-ׇ]/g,'').replace(/["'״׳`]/g,'').toLowerCase();
const clone=o=>JSON.parse(JSON.stringify(o));
const num=n=>Number(n||0).toLocaleString('he');
const store={get(k,d){try{const v=localStorage.getItem('cat.'+k);return v===null?d:JSON.parse(v);}catch(_){return d;}},set(k,v){try{localStorage.setItem('cat.'+k,JSON.stringify(v));}catch(_){}}};
let C=B.cfg, ADMIN=false, TOKEN='';
try{TOKEN=sessionStorage.getItem('cat.tok')||'';}catch(_){}
const FKEYS=B.field_defs.map(f=>f[0]);
const SORT_OF={title:'title',first_name:'author',last_name:'author',shelf:'shelf',location:'location',subject:'subject',topics:'topics',publisher:'publisher'};
const S={meta:null,page:1,size:20,editId:null,started:false,words:[],type:'all',view:'cards',sel:new Set(),last:null,parentId:null,viewId:null,cur:null};
const can=p=>ADMIN||!!C.perms[p];
const fl=k=>C.fields[k]?C.fields[k].label:k;
const T=k=>C.texts[k]||'';
const shows=(k,where)=>C.fields[k]&&C.fields[k][where]&&(ADMIN||C.fields[k].public);

async function api(path,opt){
  opt=opt||{}; opt.headers=Object.assign({},opt.headers||{}); if(TOKEN)opt.headers['X-Token']=TOKEN;
  const r=await fetch(path,opt);
  const ct=r.headers.get('content-type')||'';
  const data=ct.includes('json')?await r.json():await r.text();
  if(!r.ok){
    if(r.status===403&&data&&data.forbidden&&ADMIN){setAdmin(false,'');toast('מצב המנהל ננעל (עבר זמן ללא פעילות). יש להיכנס שוב.');}
    const e=new Error((data&&data.error)||'שגיאה');e.status=r.status;e.data=data;throw e;
  }
  return data;
}
const send=(method,url,obj)=>api(url,{method,headers:{'Content-Type':'application/json'},body:JSON.stringify(obj||{})});
let tt;
function toast(m,actions,ms){
  const t=$('#toast'); t.innerHTML='<span>'+esc(m)+'</span>';
  (actions||[]).forEach(([label,fn])=>{const b=document.createElement('button');b.textContent=label;b.onclick=()=>{fn();t.classList.remove('on');};t.appendChild(b);});
  t.classList.add('on'); clearTimeout(tt); tt=setTimeout(()=>t.classList.remove('on'),ms||(actions?9000:2800));
}

/* ---------- עיצוב וטקסטים (מההגדרות) ---------- */
function applyTheme(c){
  const t=c.theme, r=document.documentElement.style;
  for(const [k,v] of Object.entries(t.colors))r.setProperty('--'+k.replace(/_/g,'-'),v);
  r.setProperty('--serif',(B.fonts[t.font_title]||B.fonts.frank).css);
  r.setProperty('--sans',(B.fonts[t.font_body]||B.fonts.segoe).css);
  r.setProperty('--fs',t.font_size+'px'); r.setProperty('--radius',t.radius+'px'); r.setProperty('--resw',t.results_width+'px');
  document.body.classList.toggle('orn',!!t.ornaments);
  document.body.classList.toggle('dense',t.density==='dense'); document.body.classList.toggle('wide',t.density==='wide');
}
const assetUrl=n=>B.assets[n]?'/asset/'+n+'?v='+encodeURIComponent(B.assets[n]):'';
function applyTexts(c){
  const x=c.texts;
  document.title=x.window_title||x.app_title;
  $('#logoTxt').textContent=c.logo.show_title?x.app_title:'';
  $('#logoMark').innerHTML=c.logo.use_image&&assetUrl('logo')?`<img src="${assetUrl('logo')}" alt="">`:esc(c.logo.emoji);
  $('#tagline').textContent=x.tagline; $('#tagline').style.display=x.tagline?'':'none';
  $('#q').placeholder=x.search_placeholder; $('#sgo').textContent=x.btn_search;
  $('#advBtn').textContent=x.btn_adv; $('#advtoggle').textContent=x.btn_adv; $('#addBtn').textContent='＋ '+x.btn_add;
  $('#typesCap').textContent=x.home_types_caption; $('#homeLocCap').textContent=x.home_locations_caption;
  $('#favicon').href=assetUrl('icon')||'data:,';
}
applyTheme(C);

/* ---------- בנייה לפי ההגדרות וההרשאות ---------- */
const activeTypes=()=>C.search.types.filter(t=>t.on);
function buildTypes(){
  const ts=activeTypes();
  if(!ts.some(t=>t.id===S.type))S.type=C.search.default_type;
  const showT=can('search_types')&&ts.length>1;
  $('#types').hidden=!showT; $('#typesCap').hidden=!showT||!C.search.types_on_home||!T('home_types_caption');
  $('#types').innerHTML=ts.map(t=>`<button type="button" role="tab" data-t="${esc(t.id)}" class="${t.id===S.type?'on':''}">${esc(t.label)}</button>`).join('');
  document.body.classList.toggle('notypeshome',!C.search.types_on_home);
}
function buildAdv(){
  const flds=FKEYS.filter(k=>shows(k,'adv')&&!['cond','location','shelf'].includes(k));
  $('#advForm').innerHTML=flds.map(k=>`<label>${esc(fl(k))}<input id="a_${k}" data-adv="${k}"></label>`).join('')+
   `<label>${esc(fl('location'))}<select id="a_location"></select></label>
    <label>${esc(fl('cond'))}<select id="a_cond"></select></label>
    <label>${esc(fl('shelf'))} מדויק<input id="a_shelf" placeholder="101 או 101-א"></label>
    <label>טווח מדפים<span class="pair"><input id="a_shelf_from" type="number" min="1" max="999" placeholder="מ" style="width:50%"> – <input id="a_shelf_to" type="number" min="1" max="999" placeholder="עד" style="width:50%"></span></label>
    <label>נספחים<select id="a_annex"><option value="">הכל</option><option value="1">רק נספחים</option><option value="0">בלי נספחים</option></select></label>
    <div class="row"><button class="btn primary" type="submit">${esc(T('btn_search'))}</button><button class="btn" type="button" id="advClear">ניקוי הכל</button></div>`;
  $('#advClear').onclick=()=>{clearFilters();run(1);};
}
function buildForm(){
  const order=['title','label','first_name','last_name','volume','subject','topics','publisher','pub_place','pub_year','cond','shelf','location','notes','annex_of','annex_vol','content'];
  const dl={subject:1,topics:1,publisher:1,pub_place:1,label:1};
  $('#formGrid').innerHTML=order.filter(k=>k==='title'||C.fields[k].form).map(k=>{
    const L=esc(fl(k))+(k==='title'?' *':'');
    if(k==='cond'||k==='location')return `<label>${L}<select id="f_${k}"></select>${k==='location'?'<span class="hint" id="locHint"></span>':''}</label>`;
    if(k==='content')return `<label class="full">${L}<textarea id="f_content"></textarea></label>`;
    if(k==='shelf')return `<label>${L}<input id="f_shelf" placeholder="101 או 101-א"><span class="hint">1–999, ואפשר להוסיף אות (101-א). המיקום נקבע לפי המדף.</span></label>`;
    if(k==='annex_of')return `<label class="full">${L}<span class="pick"><input id="f_annex_of" style="width:100%" placeholder="אם הספר הוא נספח הכרוך בספר אחר - הקלד את שם הספר הראשי ובחר מהרשימה"><span class="dd" id="annexDD" hidden></span></span><span class="hint" id="annexHint"></span></label>`;
    return `<label class="${k==='title'||k==='topics'?'full':''}">${L}<input id="f_${k}" ${dl[k]?`list="dl_${k}"`:''}></label>`;
  }).join('');
  const ao=$('#f_annex_of');
  if(ao){
    let at;
    ao.addEventListener('input',()=>{S.parentId=null;$('#annexHint').textContent='';clearTimeout(at);at=setTimeout(annexSuggest,200);});
    ao.addEventListener('blur',()=>setTimeout(()=>{$('#annexDD').hidden=true;},200));
    $('#annexDD').onclick=e=>{const b=e.target.closest('[data-pid]');if(!b)return;ao.value=b.dataset.title;S.parentId=+b.dataset.pid;$('#annexDD').hidden=true;$('#annexHint').textContent='✓ מקושר לספר הראשי';};
  }
  const sh=$('#f_shelf'); if(sh)sh.addEventListener('input',locHint);
  fillSelects();
}
async function annexSuggest(){
  const v=$('#f_annex_of').value.trim(), dd=$('#annexDD'); if(v.length<2){dd.hidden=true;return;}
  try{
    const d=await api('/api/search?field=title&group=0&size=8&q='+encodeURIComponent(v));
    const rows=d.rows.filter(b=>b.id!==S.editId);
    dd.innerHTML=rows.map(b=>`<button type="button" data-pid="${b.id}" data-title="${esc(b.title)}"><b>${esc(b.title)}</b> ${esc(b.volume)} · ${esc([b.first_name,b.last_name].filter(Boolean).join(' '))} · מדף ${esc(b.shelf_text)}</button>`).join('');
    dd.hidden=!rows.length;
  }catch(_){dd.hidden=true;}
}
function locateShelf(text){
  const m=String(text||'').replace(/["'״׳`]/g,'').trim().match(/^(\d{1,3})\s*[-–—־]?\s*([A-Za-zא-ת]{0,3})$/);
  if(!m||!S.meta)return ''; const n=+m[1], sub=m[2]||'';
  for(const l of S.meta.locations)if(l.letter&&[...l.letter].some(ch=>sub.includes(ch)))return l.name;
  for(const l of S.meta.locations)if(l.shelf_from!=null&&l.shelf_to!=null&&n>=l.shelf_from&&n<=l.shelf_to)return l.name;
  return '';
}
function locHint(){
  const h=$('#locHint'), sh=$('#f_shelf'); if(!sh)return;
  const loc=C.locations.auto?locateShelf(sh.value):'';
  if(loc&&$('#f_location'))$('#f_location').value=loc;
  if(h)h.textContent=C.locations.auto?(loc?'נקבע אוטומטית לפי המדף':'אין כלל מיקום למדף הזה - אפשר לבחור ידנית'):'';
}
function buildMenu(){
  const it=[];
  const exp=can('export_csv')||can('export_xlsx');
  if(exp)it.push(['exp','⬇ ייצוא ל-Excel / CSV…']);
  if(can('import'))it.push(['imp','⬆ ייבוא מקובץ…']);
  it.push(['print','🖨 הדפסת התוצאות']);
  if(can('backup')||can('restore'))it.push(['-']);
  if(can('backup'))it.push(['backup','שמירת גיבוי…']);
  if(can('restore'))it.push(['restore','שחזור מגיבוי…']);
  const lim=[]; if(!ADMIN){if(can('locations'))lim.push(['sec:locations','ניהול מיקומים ומדפים']);if(can('values'))lim.push(['sec:values','ניהול רשימות ערכים']);if(can('update'))lim.push(['sec:update','עדכון גרסה…']);}
  if(lim.length)it.push(['-'],...lim);
  it.push(['-']);
  if(ADMIN)it.push(['settings','⚙ הגדרות התוכנה'],['lock','🔒 יציאה ממצב מנהל']); else it.push(['login','🔒 כניסה למצב מנהל']);
  it.push(['about','אודות / איפה נשמרים הנתונים?']);
  if(can('quit'))it.push(['-'],['quit','סגירת התוכנה']);
  $('#menu').innerHTML=it.map(([a,t])=>a==='-'?'<hr>':`<button data-a="${a}">${esc(t)}</button>`).join('');
}
function buildBars(){
  $('#addBtn').hidden=!can('add');
  $('#advBtn').hidden=$('#advtoggle').hidden=!can('search_adv');
  $('#adminTag').hidden=!ADMIN; $('#setBtn').hidden=!ADMIN;
  $('#adminBtn').textContent=ADMIN?'🔓':'🔒'; $('#adminBtn').title=ADMIN?'יציאה ממצב מנהל':'כניסה למצב מנהל'; $('#adminBtn').classList.toggle('on',ADMIN);
  const views=C.results.views; if(!views.includes(S.view)||!can('change_view'))S.view=can('change_view')&&views.includes(store.get('view'))?store.get('view'):C.results.default_view;
  $('#viewSeg').hidden=!can('change_view')||views.length<2;
  $('#viewSeg').innerHTML=views.map(v=>`<button type="button" data-v="${v}" class="${v===S.view?'on':''}">${esc(B.views[v])}</button>`).join('');
  $('#sortWrap').hidden=$('#sizeWrap').hidden=!can('change_sort');
  const keepS=$('#sort').value, keepD=$('#dir').value;
  $('#sort').innerHTML=Object.entries(B.sorts).map(([k,t])=>`<option value="${k}">${esc(t)}</option>`).join('');
  $('#sort').value=keepS&&can('change_sort')?keepS:C.search.default_sort; $('#dir').value=keepD&&can('change_sort')?keepD:C.search.default_dir;
  const sizes=[...new Set([...C.search.page_sizes,C.search.page_size])].sort((a,b)=>a-b);
  $('#psize').innerHTML=sizes.map(n=>`<option>${n}</option>`).join('');
  const ps=can('change_sort')?store.get('size',C.search.page_size):C.search.page_size; S.size=sizes.includes(ps)?ps:C.search.page_size; $('#psize').value=S.size;
  $('#expBtn').hidden=!(can('export_csv')||can('export_xlsx'));
  $('#homeLocs').hidden=!C.home.show_locations||!can('browse_locations');
  $('#homeCount').hidden=!C.home.show_count||!can('show_count'); $('#homeBarWrap').hidden=!C.home.show_capacity_bar||!can('show_count');
}
function fillSelects(){
  const m=S.meta; if(!m)return;
  const locs=m.locations.map(l=>l.name);
  const opt=(a,first)=>(first!==undefined?`<option value="">${first}</option>`:'')+a.map(x=>`<option>${esc(x)}</option>`).join('');
  const keep=id=>{const e=$(id);return e?e.value:'';};
  const kL=keep('#a_location'),kC=keep('#a_cond');
  if($('#a_location')){$('#a_location').innerHTML=opt(locs,'הכל');$('#a_location').value=kL;}
  if($('#a_cond')){$('#a_cond').innerHTML=opt(m.conditions,'הכל');$('#a_cond').value=kC;}
  if($('#f_location'))$('#f_location').innerHTML=opt(locs,'');
  if($('#f_cond'))$('#f_cond').innerHTML=opt(m.conditions,'');
  const dl=(id,a)=>{const e=$(id);if(e)e.innerHTML=a.map(s=>`<option value="${esc(s)}">`).join('');};
  dl('#dl_subject',m.subjects);dl('#dl_topics',m.topics_list);dl('#dl_publisher',m.publishers);dl('#dl_pub_place',m.places);dl('#dl_label',m.labels);
}
async function loadMeta(){
  S.meta=await api('/api/meta'); const m=S.meta;
  fillSelects();
  const rng=l=>[l.shelf_from!=null?`מדפים ${l.shelf_from}–${l.shelf_to}`:'',l.letter?`אות ${l.letter}`:''].filter(Boolean).join(' · ');
  $('#homeChips').innerHTML=m.locations.map(l=>`<button class="chip" data-loc="${esc(l.name)}">${esc(l.name)}<small>${num(l.count)} ספרים${rng(l)?' · '+rng(l):''}</small></button>`).join('');
  if(!m.locations.length)$('#homeLocs').hidden=true; else buildBars();
  $('#homeBar').style.width=Math.min(100,m.count/m.capacity*100)+'%';
  const txt=`${num(m.count)} ספרים בקטלוג`+(m.annex_count?` · מתוכם ${num(m.annex_count)} נספחים`:'');
  $('#homeCount').textContent=txt;
  $('#foot').textContent=[T('footer'),'גרסה '+m.version].filter(Boolean).join(' · ');
}
function rebuild(){
  applyTheme(C); applyTexts(C); buildTypes(); buildAdv(); buildForm(); buildMenu(); buildBars();
  if(S.started)run(S.page,true);
}

/* ---------- חיפוש ---------- */
const advVal=id=>{const e=$('#a_'+id);return e?e.value.trim():'';};
function params(){
  const p=new URLSearchParams(); const q=$('#q').value.trim();
  if(q){p.set('q',q);p.set('type',S.type);}
  if(can('search_adv')||can('browse_locations')){
    $$('#advForm [data-adv]').forEach(e=>{const v=e.value.trim(); if(v)p.set(e.dataset.adv,v);});
    ['location','cond','shelf','shelf_from','shelf_to','annex'].forEach(k=>{const v=advVal(k); if(v)p.set(k,v);});
  }
  return p;
}
function clearFilters(){ $('#advForm').querySelectorAll('input,select').forEach(x=>x.value=''); $('#q').value=''; }
function setMode(started){
  S.started=started;
  document.body.classList.toggle('home',!started);
  $('#home').hidden=started; $('#res').hidden=!started;
  if(!started){$('#adv').hidden=true;S.sel.clear();}
  $('#types').style.display=(!started&&!C.search.types_on_home)?'none':'';
}
let timer,seq=0;
function schedule(){ if(!C.search.live)return; clearTimeout(timer);timer=setTimeout(()=>run(1),240); }
async function run(page,force){
  S.page=page||1;
  const p=params();
  $('#clr').hidden=!$('#q').value;
  const advOn=[...p.keys()].some(k=>!['q','type'].includes(k));
  $('#advtoggle').textContent=T('btn_adv')+(advOn?' •':'');
  if(!force&&!p.toString()){setMode(false);return;}
  setMode(true);
  S.words=C.search.highlight?[...p.entries()].filter(([k])=>!['type','location','cond','shelf','shelf_from','shelf_to','annex'].includes(k))
          .flatMap(([,v])=>nrm(v).split(/\s+/)).filter(Boolean):[];
  S.cur=new URLSearchParams(p);
  p.set('sort',$('#sort').value);p.set('dir',$('#dir').value);p.set('page',S.page);p.set('size',S.size);
  const my=++seq;
  try{
    const d=await api('/api/search?'+p);
    if(my!==seq)return;
    S.last=d; render(d);
  }catch(e){ if(my===seq){$('#list').className='';$('#list').innerHTML=`<div class="empty"><b>${esc(e.message)}</b></div>`;$('#pager').innerHTML='';$('#statTxt').textContent='';} }
}
function hl(text,words){
  words=words||S.words;
  text=String(text??''); if(!words.length)return esc(text);
  const low=nrmKeep(text), rg=[];
  for(const w of words){ if(!w)continue; let i=0; while((i=low.indexOf(w,i))>=0){rg.push([i,i+w.length]);i+=w.length;} }
  if(!rg.length)return esc(text);
  rg.sort((a,b)=>a[0]-b[0]); const m=[rg[0]];
  for(const r of rg.slice(1)){const l=m[m.length-1]; if(r[0]<=l[1])l[1]=Math.max(l[1],r[1]); else m.push(r);}
  let out='',pos=0; for(const [a,b] of m){out+=esc(text.slice(pos,a))+'<mark>'+esc(text.slice(a,b))+'</mark>';pos=b;}
  return out+esc(text.slice(pos));
}
/* כמו nrm אבל שומר על אורך המחרוזת (כדי שמיקומי ההדגשה יתאימו לטקסט המקורי) */
const nrmKeep=s=>String(s).replace(/[֑-ׇ"'״׳`]/g,'\u0001').toLowerCase();
function snippet(t){
  t=String(t||''); if(!t)return ''; const n=C.results.snippet_len, words=S.words;
  const low=nrmKeep(t); let idx=-1;
  for(const w of words){const i=low.indexOf(w); if(i>=0&&(idx<0||i<idx))idx=i;}
  const s=idx>70?idx-45:0; const out=t.slice(s,s+n);
  return (s>0?'… ':'')+hl(out)+(s+n<t.length?' …':'');
}
const condColor=c=>{const x=C.conditions.find(k=>k.name===c);return x?x.color:'var(--muted)';};
const author=b=>[b.first_name,b.last_name].filter(Boolean).join(' ');
const lblBadge=b=>b.label&&shows('label','card')?`<span class="lbl" title="${esc(fl('label'))}">${esc(b.label)}</span>`:'';
function annexBlock(b){
  const a=b.annexes||[]; if(!a.length||!shows('annex_of','card'))return '';
  const hits=a.filter(x=>x.hit), rest=a.filter(x=>!x.hit), keep=Math.max(0,4-hits.length);
  const li=(x,hid)=>`<li class="${x.hit?'hit':''}" ${hid?'hidden':''}>${lblBadge(x)}<a href="#" data-open="${x.id}">${hl(x.title)}</a><small>${hl(author(x))}</small>${x.hit?'<span class="badge">נמצא בחיפוש</span>':''}</li>`;
  const hidden=rest.slice(keep);
  return `<div class="anx"><div class="hd">${esc(T('annex_caption'))} (${a.length})</div><ul>${hits.map(x=>li(x)).join('')}${rest.slice(0,keep).map(x=>li(x)).join('')}${hidden.map(x=>li(x,true)).join('')}</ul>${hidden.length?`<button type="button" class="more" data-more>ועוד ${hidden.length} נספחים…</button>`:''}</div>`;
}
function parentLine(b){
  if(!b.annex_of||!shows('annex_of','card'))return '';
  const name=esc(b.annex_of)+(b.annex_vol?' · '+esc(b.annex_vol):'');
  return `<div class="parentln"><span class="badge">${esc(T('annex_badge'))}</span> ${esc(fl('annex_of'))}: ${b.parent_id?`<a href="#" data-open="${b.parent_id}">${name}</a>`:`<b>${name}</b>`}</div>`;
}
function pathLine(b){
  const where=[]; if(b.location&&shows('location','card'))where.push(`<a href="#" data-loc="${esc(b.location)}">${esc(b.location)}</a>`);
  if(b.shelf_text&&shows('shelf','card'))where.push(`<a href="#" data-loc="${esc(b.location)}" data-shelf="${esc(b.shelf_text)}">${esc(fl('shelf'))} ${esc(b.shelf_text)}</a>`);
  return `<div class="path">${lblBadge(b)}<span>${where.join(' › ')||'ללא מיקום'}</span></div>`;
}
function card(b){
  const au=shows('first_name','card')||shows('last_name','card')?author(b):'';
  const pub=[shows('publisher','card')?b.publisher:'',shows('pub_place','card')?b.pub_place:'',shows('pub_year','card')?b.pub_year:''].filter(Boolean).join(', ');
  const metaParts=[au?`<b>${hl(au)}</b>`:'',pub?hl(pub):''].filter(Boolean);
  const foundIn=S.last&&S.last.grouped&&b.hit_self===false&&(b.annexes||[]).some(x=>x.hit);
  return `<article class="r" data-id="${b.id}">
    ${pathLine(b)}
    ${foundIn?`<div class="found">↳ החיפוש נמצא בנספח הכרוך בספר זה</div>`:''}
    <h3><span class="t">${hl(b.title)}</span> ${b.volume&&shows('volume','card')?`<span class="vol">· ${hl(b.volume)}</span>`:''}</h3>
    ${parentLine(b)}
    ${metaParts.length?`<div class="meta">${metaParts.join(' &nbsp;·&nbsp; ')}</div>`:''}
    ${b.content&&shows('content','card')?`<p class="snip">${snippet(b.content)}</p>`:''}
    <div class="tags">${b.subject&&shows('subject','card')?`<span class="tag">${hl(b.subject)}</span>`:''}
      ${b.topics&&shows('topics','card')&&C.results.show_topics?b.topics.split('|').map(t=>`<span class="tag outline">${hl(t.trim())}</span>`).join(''):''}
      ${b.cond&&shows('cond','card')?`<span class="tag cond"><i class="dot" style="background:${condColor(b.cond)}"></i>${esc(b.cond)}</span>`:''}
      ${b.notes&&shows('notes','card')?`<span class="tag outline">${hl(b.notes)}</span>`:''}</div>
    ${annexBlock(b)}</article>`;
}
function rowLine(b){
  const hits=(b.annexes||[]).filter(x=>x.hit);
  return `<article class="r" data-id="${b.id}">${lblBadge(b)}<h3><span class="t">${hl(b.title)}</span> ${b.volume?`<span class="vol">· ${hl(b.volume)}</span>`:''}</h3>
    <span class="who">${hl(author(b))}</span>${b.annex_of?`<span class="badge">${esc(T('annex_badge'))} · ${esc(b.annex_of)}</span>`:''}
    ${hits.map(x=>`<span class="badge">↳ ${esc(x.title)}</span>`).join('')}${(b.annexes||[]).length&&!hits.length?`<span class="cap">+${b.annexes.length} נספחים</span>`:''}
    <span class="loc">${esc([shows('location','card')?b.location:'',b.shelf_text&&shows('shelf','card')?fl('shelf')+' '+b.shelf_text:''].filter(Boolean).join(' › '))}</span></article>`;
}
function table(rows){
  const cols=FKEYS.filter(k=>shows(k,'table')), bulk=can('bulk');
  const cell=(b,k)=>{
    if(k==='shelf')return esc(b.shelf_text);
    if(k==='title'){const hits=(b.annexes||[]).filter(x=>x.hit);return hl(b.title)+hits.map(x=>`<div class="cap">↳ ${esc(T('annex_badge'))}: ${hl(x.title)}</div>`).join('');}
    if(k==='content')return snippet(b.content);
    return hl(b[k]);
  };
  return `<div class="tblwrap"><table class="t"><thead><tr>${bulk?'<th><input type="checkbox" id="selAll" title="בחירת הכל"></th>':''}${cols.map(k=>`<th data-sort="${SORT_OF[k]||''}">${esc(fl(k))}${SORT_OF[k]&&$('#sort').value===SORT_OF[k]?($('#dir').value==='desc'?' ▼':' ▲'):''}</th>`).join('')}</tr></thead>
   <tbody>${rows.map(b=>`<tr class="r2" data-id="${b.id}">${bulk?`<td><input type="checkbox" data-sel="${b.id}" ${S.sel.has(b.id)?'checked':''}></td>`:''}${cols.map(k=>`<td class="${k==='title'?'ti':''}">${cell(b,k)}</td>`).join('')}</tr>`).join('')}</tbody></table></div>`;
}
function render(d){
  const sec=(d.ms/1000).toFixed(2);
  $('#statTxt').textContent=d.total?`${num(d.total)} תוצאות`+(C.results.show_timing?` (${sec} שניות)`:''):'';
  const L=$('#list'); L.className='v-'+S.view;
  if(!d.rows.length){
    L.className=''; L.innerHTML=`<div class="empty"><b>${esc(T('empty_title'))}</b>${esc(T('empty_hint'))}</div>`;
    $('#pager').innerHTML=''; renderBulk(); return;
  }
  L.innerHTML=S.view==='table'?table(d.rows):d.rows.map(S.view==='list'?rowLine:card).join('');
  const pages=Math.max(1,Math.ceil(d.total/d.size)),c=d.page;
  let a=Math.max(1,c-4),z=Math.min(pages,a+9); a=Math.max(1,z-9);
  let h=`<button ${c<=1?'disabled':''} data-p="${c-1}">→ הקודם</button>`;
  for(let i=a;i<=z;i++)h+=`<button class="${i===c?'cur':''}" data-p="${i}">${i}</button>`;
  h+=`<button ${c>=pages?'disabled':''} data-p="${c+1}">הבא ←</button>`;
  $('#pager').innerHTML=pages>1?h:'';
  renderBulk();
}
function renderBulk(){
  const b=$('#bulk'), n=S.sel.size;
  if(!n||!can('bulk')||S.view!=='table'){b.hidden=true;return;}
  const flds=FKEYS.filter(k=>!['title','annex_of','annex_vol'].includes(k));
  b.hidden=false;
  b.innerHTML=`<b>נבחרו ${num(n)} ספרים</b>`+(can('edit')?`<span>קביעת</span><select id="bkField">${flds.map(k=>`<option value="${k}">${esc(fl(k))}</option>`).join('')}</select><input id="bkVal" placeholder="ערך חדש (ריק = מחיקת הערך)"><button class="btn sm primary" data-b="set">החלה על הנבחרים</button>`:'')+
    ((can('export_csv')||can('export_xlsx'))?'<button class="btn sm" data-b="exp">ייצוא הנבחרים</button>':'')+
    (can('delete')?'<button class="btn sm danger" data-b="del">מחיקת הנבחרים</button>':'')+'<button class="btn sm" data-b="clear">ביטול הבחירה</button>';
}

/* ---------- כרטיס ספר ---------- */
async function openView(id){
  if(!can('view_details')){ if(can('edit'))openEdit(id); return; }
  let b; try{b=await api('/api/book?id='+id);}catch(e){toast(e.message);return;}
  S.viewId=id; S.viewBook=b;
  const rows=FKEYS.filter(k=>!['title','annex_of','annex_vol'].includes(k)&&(ADMIN||C.fields[k].public)).map(k=>{
    const v=k==='shelf'?b.shelf_text:b[k]; if(!v)return '';
    const val=k==='topics'?v.split('|').map(t=>esc(t.trim())).join('<br>'):k==='cond'?`<i class="dot" style="background:${condColor(v)}"></i>${esc(v)}`:k==='label'?`<span class="lbl">${esc(v)}</span>`:esc(v);
    return `<dt>${esc(fl(k))}</dt><dd>${val}</dd>`;}).join('');
  const anx=(b.annexes||[]).length?`<div class="anx"><div class="hd">${esc(T('annex_caption'))} (${b.annexes.length})</div><ul>${b.annexes.map(x=>`<li>${lblBadge(x)}<a href="#" data-open="${x.id}">${esc(x.title)}</a><small>${esc(author(x))}</small></li>`).join('')}</ul></div>`:'';
  $('#vBody').innerHTML=`<h2 id="vTitle">${esc(b.title)} ${b.volume?`<span class="vol" style="font-size:.55em">· ${esc(b.volume)}</span>`:''}</h2>
    ${parentLine(b)}<dl class="dl" style="margin-top:.8em">${rows}</dl>${anx}
    ${ADMIN?`<p class="cap" style="margin:.8em 0 0">מס' ${b.id} · נוסף ${esc((b.added||'').replace('T',' '))} · עודכן ${esc((b.updated||'').replace('T',' '))}</p>`:''}`;
  $('#vEdit').hidden=!can('edit'); $('#vShelf').hidden=!b.shelf_text||!can('browse_locations');
  if(!$('#viewDlg').open)$('#viewDlg').showModal();
}

/* ---------- עריכת ספר ---------- */
const fval=k=>{const e=$('#f_'+k);return e?e.value.trim():undefined;};
async function openEdit(id,prefill){
  S.editId=id||null; $('#dlgErr').textContent=''; S.parentId=null;
  let b=prefill||{};
  if(id){ try{b=await api('/api/book?id='+id);}catch(e){toast(e.message);return;} }
  S.editBook=b; S.parentId=b.parent_id||null;
  $('#dlgTitle').textContent=id?'עריכת ספר':T('btn_add');
  $('#delBtn').style.display=id&&can('delete')?'':'none'; $('#saveAddBtn').style.display=id?'none':'';
  FKEYS.forEach(k=>{const e=$('#f_'+k); if(!e)return;
    const v=k==='shelf'?(b.shelf_text||b.shelf||''):(b[k]??'');
    if(e.tagName==='SELECT'&&v&&![...e.options].some(o=>o.value===v))e.insertAdjacentHTML('beforeend',`<option>${esc(v)}</option>`);
    e.value=v; });
  if($('#annexHint'))$('#annexHint').textContent=b.parent_id?'✓ מקושר לספר הראשי':(b.annex_of?'לא נמצא ספר ראשי בשם הזה בקטלוג (נשמר כטקסט בלבד)':'');
  locHint();
  if($('#viewDlg').open)$('#viewDlg').close();
  if(!$('#dlg').open)$('#dlg').showModal();
  $('#f_title').focus();
}
async function save(again,force){
  const d={}; const src=S.editBook||{};
  FKEYS.forEach(k=>{const v=fval(k); d[k]=v!==undefined?v:(k==='shelf'?(src.shelf_text||''):(src[k]??''));});
  if(S.parentId)d.parent_id=S.parentId;
  if(force)d.force=true;
  if(!d.title){$('#dlgErr').textContent='חסר שם ספר';$('#f_title').focus();return;}
  try{
    if(S.editId) await send('PUT','/api/book?id='+S.editId,d); else await send('POST','/api/book',d);
  }catch(e){
    if(e.status===409){
      const u=e.data.dup;
      if(confirm(`קיים כבר ספר באותו שם, מחבר וכרך (מיקום: ${u.location||'—'}, מדף: ${u.shelf_text||'—'}).\nלשמור בכל זאת?`))return save(again,true);
      return;
    }
    $('#dlgErr').textContent=e.message; return;
  }
  toast(S.editId?'הספר עודכן':'הספר נוסף');
  await loadMeta();
  if(again&&!S.editId){
    ['title','volume','content','notes','label'].forEach(k=>{const e=$('#f_'+k);if(e)e.value='';});
    $('#dlgErr').textContent=''; $('#f_title').focus();
  } else $('#dlg').close();
  if(S.started)run(S.page,true);
}

/* ---------- ייצוא / גיבוי ---------- */
async function saveFile(url,what){
  /* בחלון התוכנה: חלון "שמירה בשם" והקובץ נכתב ישירות. בדפדפן: הורדה רגילה. */
  let r;
  try{r=await api(url,{method:'POST'});}catch(e){toast(e.message);return false;}
  if(r.download){const a=document.createElement('a');a.href=url+(url.includes('?')?'&':'?')+'t='+encodeURIComponent(TOKEN);a.download='';document.body.appendChild(a);a.click();a.remove();toast(what+' - ההורדה החלה');return true;}
  if(r.cancelled)return false;
  if(r.saved)toast(what+' נשמר: '+r.saved,[['פתיחת הקובץ',()=>send('POST','/api/open-path',{path:r.saved}).catch(e=>toast(e.message))],['פתיחת התיקייה',()=>send('POST','/api/open-path',{path:r.saved,folder:true}).catch(e=>toast(e.message))]],15000);
  return true;
}
function openExport(scope){
  const fm=[]; if(can('export_xlsx'))fm.push(['xlsx','Excel (קובץ xlsx מעוצב, נפתח ישירות באקסל)']); if(can('export_csv'))fm.push(['csv','CSV (טקסט מופרד בפסיקים, מתאים לכל תוכנה)']);
  if(!fm.length)return;
  const last=store.get('expFmt','xlsx');
  $('#expFmt').innerHTML=fm.map(([v,t],i)=>`<label class="ck"><input type="radio" name="expF" value="${v}" ${(fm.some(f=>f[0]===last)?v===last:i===0)?'checked':''}> ${t}</label>`).join('');
  const sc=[['all',`כל הקטלוג (${num(S.meta.count)} ספרים)`]];
  if(S.started&&S.last&&S.cur&&S.cur.toString())sc.push(['res',`תוצאות החיפוש הנוכחי (${num(S.last.total)}${S.last.grouped?' ספרים ראשיים, כולל הנספחים שנמצאו':''})`]);
  if(S.sel.size)sc.push(['sel',`הספרים שנבחרו (${num(S.sel.size)})`]);
  scope=sc.some(s=>s[0]===scope)?scope:(sc.length>1?sc[1][0]:'all');
  $('#expScope').innerHTML=sc.map(([v,t])=>`<label class="ck"><input type="radio" name="expS" value="${v}" ${v===scope?'checked':''}> ${t}</label>`).join('');
  const saved=store.get('expCols',null);
  const cols=[['id',"מס' סידורי"],...FKEYS.filter(k=>ADMIN||C.fields[k].public).map(k=>[k,fl(k)]),['parent_id',"מס' הספר הראשי (לקישור נספחים)"]];
  $('#expCols').innerHTML=cols.map(([k,t])=>`<label><input type="checkbox" value="${k}" ${(saved?saved.includes(k):(!C.fields[k]||C.fields[k].export))?'checked':''}>${esc(t)}</label>`).join('');
  $('#expErr').textContent=''; $('#expDlg').showModal();
}
async function doExport(){
  const fmt=(document.querySelector('input[name=expF]:checked')||{}).value, scope=(document.querySelector('input[name=expS]:checked')||{}).value;
  const cols=$$('#expCols input:checked').map(e=>e.value);
  if(!cols.length){$('#expErr').textContent='יש לבחור לפחות עמודה אחת';return;}
  store.set('expFmt',fmt); store.set('expCols',cols);
  let p=new URLSearchParams();
  if(scope==='res'){p=new URLSearchParams(S.cur);p.set('sort',$('#sort').value);p.set('dir',$('#dir').value);}
  if(scope==='sel')p.set('ids',[...S.sel].join(','));
  p.set('fmt',fmt); p.set('cols',cols.join(','));
  $('#expGo').disabled=true;
  const ok=await saveFile('/api/export?'+p,fmt==='xlsx'?'קובץ ה-Excel':'קובץ ה-CSV');
  $('#expGo').disabled=false; if(ok)$('#expDlg').close();
}

/* ---------- מצב מנהל: כניסה ויציאה ---------- */
function setAdmin(on,tok){
  ADMIN=on; TOKEN=tok||''; try{sessionStorage.setItem('cat.tok',TOKEN);}catch(_){}
  buildAdv(); buildForm(); buildMenu(); buildBars(); buildTypes();
  if(!on&&$('#adm').open)$('#adm').close();
  if(S.started)run(S.page,true);
}
function openLogin(){
  const setup=!B.has_password;
  $('#loginTitle').textContent=setup?'קביעת סיסמת מנהל':'כניסה למצב מנהל';
  $('#loginInfo').textContent=setup?'זו הכניסה הראשונה למצב מנהל. יש לקבוע סיסמה (לפחות 4 תווים). במצב מנהל אפשר לשנות כל דבר בתוכנה: עיצוב, טקסטים, חיפוש, מיקומים, הרשאות ועוד.':'יש להקליד את סיסמת המנהל.';
  $('#lp2w').hidden=!setup; $('#loginGo').textContent=setup?'קביעת סיסמה וכניסה':'כניסה';
  $('#lp1').value=$('#lp2').value=''; $('#loginErr').textContent='';
  $('#loginDlg').showModal(); $('#lp1').focus();
}
async function doLogin(){
  const setup=!B.has_password, pw=$('#lp1').value;
  if(setup&&pw!==$('#lp2').value){$('#loginErr').textContent='שתי הסיסמאות אינן זהות';return;}
  try{
    const r=await send('POST',setup?'/api/admin/setup':'/api/admin/login',{password:pw});
    B.has_password=true; $('#loginDlg').close(); setAdmin(true,r.token);
    toast('מצב מנהל פעיל',[['פתיחת ההגדרות',()=>openAdm()]],6000);
  }catch(e){$('#loginErr').textContent=e.message;$('#lp1').select();}
}
async function lock(){ try{await send('POST','/api/admin/logout');}catch(_){} setAdmin(false,''); toast('יצאת ממצב מנהל'); }

/* =====================================================================
                         הגדרות (מצב מנהל)
   W = עותק עבודה של ההגדרות. כל שדה עם data-p="נתיב" נכתב ישר לתוך W,
   והעיצוב/הטקסטים מתעדכנים מיד לתצוגה מקדימה. "שמירה" שולחת את W לשרת.
   ===================================================================== */
let W=null, SEC='general', DIRTY=false;
const getP=(o,p)=>p.split('.').reduce((a,k)=>a==null?a:a[k],o);
function setP(o,p,v){const ks=p.split('.');const last=ks.pop();const t=ks.reduce((a,k)=>a[k],o);t[last]=v;}
const ti=(p,label,hint,cls)=>`<label class="${cls||''}">${esc(label)}<input data-p="${p}" value="${esc(getP(W,p))}">${hint?`<span class="hint">${esc(hint)}</span>`:''}</label>`;
const ni=(p,label,min,max,hint)=>`<label>${esc(label)}<input type="number" data-p="${p}" min="${min}" max="${max}" value="${esc(getP(W,p))}">${hint?`<span class="hint">${esc(hint)}</span>`:''}</label>`;
const ck=(p,label,cls)=>`<label class="ck ${cls||''}"><input type="checkbox" data-p="${p}" ${getP(W,p)?'checked':''}> ${esc(label)}</label>`;
const sel=(p,label,opts)=>`<label>${esc(label)}<select data-p="${p}">${opts.map(([v,t])=>`<option value="${esc(v)}" ${String(getP(W,p))===String(v)?'selected':''}>${esc(t)}</option>`).join('')}</select></label>`;
const col=(p,label)=>`<label>${esc(label)}<span class="cl"><input type="color" data-p="${p}" value="${esc(getP(W,p))}"><input data-p="${p}" value="${esc(getP(W,p))}" style="width:7em" dir="ltr"></span></label>`;
const TXT={app_title:'שם התוכנה (הכותרת בכניסה)',window_title:'כותרת החלון',tagline:'משפט מתחת לכותרת',search_placeholder:'טקסט בתיבת החיפוש',btn_search:'כפתור החיפוש',btn_adv:'כפתור חיפוש מתקדם',btn_add:'כפתור הוספת ספר',home_types_caption:'כיתוב מעל סוגי החיפוש',home_locations_caption:'כיתוב מעל המיקומים',empty_title:'כשאין תוצאות - כותרת',empty_hint:'כשאין תוצאות - הסבר',annex_caption:'כותרת רשימת הנספחים בספר הראשי',annex_badge:'תגית "נספח"',footer:'טקסט בתחתית המסך'};
const COLS={bg:'רקע המסך',panel:'רקע חלוניות וכרטיסים',fg:'טקסט ראשי',muted:'טקסט משני',line:'קווים ומסגרות',accent:'צבע ראשי (כפתורים, כותרות)',accent_fg:'טקסט על הצבע הראשי',gold:'צבע עיטור (זהב)',link:'שמות הספרים בתוצאות',mark:'הדגשת מילות החיפוש',chip:'רקע תגיות'};
function lum(h){const c=[1,3,5].map(i=>parseInt(h.slice(i,i+2),16)/255).map(v=>v<=.03928?v/12.92:Math.pow((v+.055)/1.055,2.4));return .2126*c[0]+.7152*c[1]+.0722*c[2];}
function ratio(a,b){const x=lum(a),y=lum(b);return (Math.max(x,y)+.05)/(Math.min(x,y)+.05);}
function contrastRow(){
  const c=W.theme.colors, pairs=[['טקסט ראשי על הרקע',c.fg,c.bg],['טקסט משני על הרקע',c.muted,c.bg],['טקסט על כרטיסים',c.fg,c.panel],['טקסט על הצבע הראשי',c.accent_fg,c.accent],['שמות הספרים',c.link,c.bg],['טקסט מודגש',c.fg,c.mark]];
  return pairs.map(([t,a,b])=>{let r=1;try{r=ratio(a,b);}catch(_){ } const ok=r>=7?['מצוין','#1F7A3A']:r>=4.5?['טוב','#2E6F8E']:r>=3?['חלש','#B45F06']:['לא קריא','#A61C1C'];
    return `<tr><td>${t}</td><td><span style="background:${esc(b)};color:${esc(a)};padding:.1em .8em;border-radius:5px;border:1px solid #0003">אבגד 123</span></td><td dir="ltr">${r.toFixed(1)} : 1</td><td><span class="ctr" style="background:${ok[1]}">${ok[0]}</span></td></tr>`;}).join('');
}
const upDn=(kind,i,n)=>`<button class="btn sm" data-act="${kind}-up:${i}" ${i===0?'disabled':''} title="למעלה">▲</button> <button class="btn sm" data-act="${kind}-dn:${i}" ${i===n-1?'disabled':''} title="למטה">▼</button>`;

const SECTIONS=[
 {id:'general',icon:'🏷',title:'כללי וטקסטים',keys:['texts','logo','general'],render:()=>`
   <h3>כללי וטקסטים</h3><p class="d">כל הכיתובים שמופיעים בתוכנה. השינוי נראה מיד ברקע, ונשמר בלחיצה על "שמירת השינויים".</p>
   <div class="sg">${Object.keys(TXT).map(k=>ti('texts.'+k,TXT[k],'',['tagline','empty_hint','footer'].includes(k)?'full':'')).join('')}</div>
   <h4>לוגו</h4><div class="sg">${ti('logo.emoji','סימן ליד הכותרת (אימוג׳י או אות)')}${ck('logo.show_title','להציג את שם התוכנה ליד הלוגו')}${ck('logo.use_image','להשתמש בתמונת לוגו (מעלים אותה בקטגוריה "סמל ומסך פתיחה")')}</div>
   <h4>חלון התוכנה</h4><div class="sg">${ni('general.window_w','רוחב החלון (פיקסלים)',640,6000)}${ni('general.window_h','גובה החלון (פיקסלים)',480,4000)}${ck('general.maximized','לפתוח את החלון על כל המסך')}${ck('general.confirm_quit','לשאול לפני סגירת התוכנה')}</div>
   <p class="hint">גודל וכותרת החלון ייכנסו לתוקף בהפעלה הבאה של התוכנה.</p>
   <h4>קטלוג וגיבויים</h4><div class="sg">${ni('general.capacity','קיבולת מתוכננת (מספר ספרים)',100,10000000)}${ck('general.auto_backup','גיבוי אוטומטי יומי')}${ni('general.backup_keep','כמה גיבויים יומיים לשמור',1,365)}${ni('general.update_check_min','בדיקת עדכונים כל כמה דקות',1,1440)}</div>`},
 {id:'design',icon:'🎨',title:'עיצוב',keys:['theme'],render:()=>`
   <h3>עיצוב</h3><p class="d">בחר ערכת צבעים מוכנה, ואז שנה כל צבע, גופן ומידה כרצונך. התצוגה מתעדכנת מיד.</p>
   <h4>ערכות מוכנות</h4><div class="presets">${Object.entries(B.presets).map(([k,p])=>`<button type="button" class="preset ${W.theme.preset===k?'on':''}" data-act="preset:${k}"><i>${['bg','accent','gold','fg'].map(c=>`<b style="background:${p.colors[c]}"></b>`).join('')}</i>${esc(p.name)}</button>`).join('')}</div>
   <h4>צבעים</h4><div class="sg">${Object.keys(COLS).map(k=>col('theme.colors.'+k,COLS[k])).join('')}</div>
   <h4>בדיקת ניגודיות (קריאוּת)</h4><table class="s" id="ctrTbl">${contrastRow()}</table>
   <h4>גופנים ומידות</h4><div class="sg">${sel('theme.font_title','גופן כותרות ושמות ספרים',Object.entries(B.fonts).map(([k,f])=>[k,f.name]))}${sel('theme.font_body','גופן הטקסט הרגיל',Object.entries(B.fonts).map(([k,f])=>[k,f.name]))}
     ${ni('theme.font_size','גודל הטקסט (פיקסלים)',12,24)}${ni('theme.radius','עיגול פינות (פיקסלים)',0,28)}${ni('theme.results_width','רוחב אזור התוצאות (פיקסלים)',640,2400)}
     ${sel('theme.density','צפיפות התוצאות',[['dense','צפוף'],['normal','רגיל'],['wide','מרווח']])}${ck('theme.ornaments','עיטורים (רקע מנוקד וקו מעוטר בדף הבית)')}</div>`},
 {id:'splash',icon:'🖼',title:'סמל ומסך פתיחה',keys:['splash'],render:()=>{
   const pv=(n,empty)=>`<span class="prev">${assetUrl(n)?`<img src="${assetUrl(n)}" alt="">`:`<span class="cap">${empty}</span>`}</span>`;
   return `<h3>סמל ומסך פתיחה</h3><p class="d">קבצים נשמרים מיד עם הבחירה (אין צורך ב"שמירת השינויים").</p>
   <h4>סמל התוכנה (קובץ ICO)</h4><div class="acts">${pv('icon','אין סמל')}<button class="btn" data-act="asset:icon">בחירת קובץ ICO…</button>${assetUrl('icon')?'<button class="btn danger" data-act="asset-del:icon">הסרה</button>':''}</div>
   <p class="hint">הסמל מוצג בחלון התוכנה ובלשונית. אם לא התעדכן מיד בחלון - הוא יופיע בהפעלה הבאה.</p>
   <h4>תמונת לוגו (במקום האימוג׳י שליד הכותרת)</h4><div class="acts">${pv('logo','אין תמונה')}<button class="btn" data-act="asset:logo">בחירת תמונה…</button>${assetUrl('logo')?'<button class="btn danger" data-act="asset-del:logo">הסרה</button>':''}${ck('logo.use_image','להציג את התמונה כלוגו')}</div>
   <h4>מסך פתיחה - תמונה על כל המסך בכניסה לתוכנה</h4><div class="acts">${pv('splash','אין תמונה')}<button class="btn" data-act="asset:splash">בחירת תמונה…</button>${assetUrl('splash')?'<button class="btn danger" data-act="asset-del:splash">הסרה</button>':''}<button class="btn" data-act="splash-test">תצוגה מקדימה</button></div>
   <div class="sg" style="margin-top:.8em">${ck('splash.enabled','להציג מסך פתיחה בכניסה לתוכנה')}${ni('splash.seconds','משך ההצגה (שניות)',1,60)}${sel('splash.fit','התאמת התמונה למסך',[['cover','מילוי כל המסך (חיתוך קל)'],['contain','התמונה כולה (עם שוליים)'],['fill','מתיחה למסך']])}${col('splash.bg','צבע הרקע מאחורי התמונה')}${ck('splash.click_to_close','לחיצה או מקש סוגרים את מסך הפתיחה')}${ti('splash.caption','כיתוב על מסך הפתיחה (לא חובה)')}</div>`;}},
 {id:'search',icon:'🔍',title:'חיפוש',keys:['search'],render:()=>{
   const ts=W.search.types;
   return `<h3>חיפוש</h3><p class="d">סוגי החיפוש מופיעים בכניסה לתוכנה ומתחת לתיבת החיפוש. לכל סוג קובעים שם ובאילו שדות הוא מחפש.</p>
   <h4>סוגי חיפוש</h4><table class="s"><tr><th class="c">פעיל</th><th style="width:11em">שם</th><th>מחפש בשדות</th><th class="c">ברירת מחדל</th><th></th></tr>
   ${ts.map((t,i)=>`<tr><td class="c"><input type="checkbox" data-p="search.types.${i}.on" ${t.on?'checked':''}></td><td><input data-p="search.types.${i}.label" value="${esc(t.label)}"></td>
     <td><span class="fchips">${B.search_fields.map(([k,h])=>`<label><input type="checkbox" data-tf="${i}:${k}" ${t.fields.includes(k)?'checked':''}>${esc(C.fields[k]?fl(k):h)}</label>`).join('')}</span></td>
     <td class="c"><input type="radio" name="defType" data-act="type-def:${i}" ${W.search.default_type===t.id?'checked':''}></td>
     <td style="white-space:nowrap">${upDn('type',i,ts.length)} <button class="btn sm danger" data-act="type-del:${i}">מחיקה</button></td></tr>`).join('')}</table>
   <div class="acts"><button class="btn" data-act="type-add">＋ סוג חיפוש חדש</button></div>
   <h4>התנהגות</h4><div class="sg">${ck('search.types_on_home','להציג את בחירת סוג החיפוש כבר בכניסה לתוכנה')}${ck('search.live','חיפוש תוך כדי הקלדה')}${ck('search.highlight','הדגשת מילות החיפוש בתוצאות')}${ck('search.group_annexes','נספח שנמצא בחיפוש מוצג בתוך הספר הראשי שלו')}
     ${ni('search.page_size','תוצאות בעמוד (ברירת מחדל)',1,200)}<label>אפשרויות "בעמוד" לבחירת המשתמש<input data-list="search.page_sizes" value="${esc(W.search.page_sizes.join(', '))}" dir="ltr"><span class="hint">מספרים מופרדים בפסיק</span></label>
     ${sel('search.default_sort','מיון ברירת מחדל',Object.entries(B.sorts))}${sel('search.default_dir','כיוון המיון',[['asc','עולה'],['desc','יורד']])}</div>`;}},
 {id:'results',icon:'▤',title:'תצוגת התוצאות ודף הבית',keys:['results','home'],render:()=>`
   <h3>תצוגת התוצאות ודף הבית</h3><p class="d">אילו תצוגות זמינות למשתמש, ומה מופיע בדף הבית.</p>
   <h4>תצוגות זמינות</h4><div class="sg">${Object.entries(B.views).map(([k,t])=>`<label class="ck"><input type="checkbox" data-view="${k}" ${W.results.views.includes(k)?'checked':''}> ${esc(t)}</label>`).join('')}</div>
   <div class="sg" style="margin-top:.8em">${sel('results.default_view','תצוגת ברירת המחדל',Object.entries(B.views).filter(([k])=>W.results.views.includes(k)))}${ni('results.snippet_len','אורך קטע התוכן בתוצאה (תווים)',40,2000)}${ck('results.show_topics','להציג את הנושאים ההיררכיים בכרטיס')}${ck('results.show_timing','להציג את זמן החיפוש')}</div>
   <h4>דף הבית</h4><div class="sg">${ck('home.show_locations','כפתורי דפדוף לפי מיקום')}${ck('home.show_count','מספר הספרים בקטלוג')}${ck('home.show_capacity_bar','פס ניצול הקיבולת')}</div>`},
 {id:'fields',icon:'☰',title:'שדות',keys:['fields'],render:()=>`
   <h3>שדות</h3><p class="d">שם כל שדה, והיכן הוא מופיע. "גלוי לכולם" - אם לא מסומן, רק מנהל רואה את השדה.</p>
   <table class="s"><tr><th>שדה</th><th style="width:13em">שם לתצוגה</th><th class="c">בכרטיס התוצאה</th><th class="c">בטבלה</th><th class="c">בחיפוש מתקדם</th><th class="c">בטופס העריכה</th><th class="c">בייצוא</th><th class="c">גלוי לכולם</th></tr>
   ${B.field_defs.map(([k,h])=>`<tr><td class="cap">${esc(h)}</td><td><input data-p="fields.${k}.label" value="${esc(W.fields[k].label)}"></td>${['card','table','adv','form','export','public'].map(a=>`<td class="c"><input type="checkbox" data-p="fields.${k}.${a}" ${W.fields[k][a]?'checked':''} ${k==='title'&&a!=='adv'?'disabled':''}></td>`).join('')}</tr>`).join('')}</table>`},
 {id:'locations',icon:'📍',title:'מיקומים ומדפים',need:'locations',keys:['locations'],render:()=>`
   <h3>מיקומים ומדפים</h3><p class="d">המיקום של כל ספר נקבע לפי מספר המדף שלו. לכל מיקום קובעים טווח מדפים, או אות - מדף שכתובה בו האות (למשל 250-פ) שייך למיקום הזה, גם אם המספר שלו בטווח של מיקום אחר.</p>
   <div id="locBox"><p class="cap">טוען…</p></div>
   ${ADMIN?`<h4>התנהגות</h4>${ck('locations.auto','לקבוע את המיקום אוטומטית לפי המדף (בהוספה, בעריכה ובייבוא)')}`:''}`,after:renderLocs},
 {id:'conds',icon:'●',title:'מצבי ספר',keys:['conditions'],render:()=>`
   <h3>מצבי ספר</h3><p class="d">הרשימה שמופיעה בשדה "${esc(fl('cond'))}", והצבע של כל מצב.</p>
   <table class="s" style="max-width:38em"><tr><th>שם המצב</th><th>צבע</th><th></th></tr>
   ${W.conditions.map((c,i)=>`<tr><td><input data-p="conditions.${i}.name" value="${esc(c.name)}"></td><td><input type="color" data-p="conditions.${i}.color" value="${esc(c.color)}"></td><td style="white-space:nowrap">${upDn('cond',i,W.conditions.length)} <button class="btn sm danger" data-act="cond-del:${i}">מחיקה</button></td></tr>`).join('')}</table>
   <div class="acts"><button class="btn" data-act="cond-add">＋ מצב חדש</button></div>
   <p class="hint">שינוי שם כאן משנה רק את הרשימה. כדי לשנות את הערך בספרים קיימים - "רשימות ערכים".</p>`},
 {id:'values',icon:'🗂',title:'רשימות ערכים',need:'values',keys:[],render:()=>`
   <h3>רשימות ערכים</h3><p class="d">שינוי או איחוד של ערך בכל הספרים בבת אחת (למשל תיקון שם של נושא, או איחוד שני כתיבים של אותה הוצאה).</p>
   <div class="acts"><label class="sl">שדה <select id="valField">${['subject','publisher','pub_place','pub_year','cond','label','last_name','first_name','volume'].map(k=>`<option value="${k}">${esc(fl(k))}</option>`).join('')}</select></label>
   <label class="sl">סינון <input id="valFilter" placeholder="הקלד כדי לסנן…"></label></div>
   <div id="valBox" style="margin-top:.8em"></div>`,after:renderValues},
 {id:'perms',icon:'🛡',title:'הרשאות',keys:['perms'],render:()=>`
   <h3>הרשאות</h3><p class="d">מה מותר למי שאינו במצב מנהל. מה שלא מסומן - זמין רק למנהל (אחרי הקלדת הסיסמה). ההגדרות עצמן פתוחות תמיד רק למנהל.</p>
   <div class="sg">${B.perm_defs.map(([k,t])=>ck('perms.'+k,t)).join('')}</div>
   <div class="acts"><button class="btn sm" data-act="perm-all">סימון הכל</button><button class="btn sm" data-act="perm-none">ניקוי הכל (צפייה וחיפוש בלבד)</button></div>
   <p class="hint">להסתרת שדות מסוימים ממי שאינו מנהל: קטגוריית "שדות" &gt; "גלוי לכולם".</p>`},
 {id:'data',icon:'💾',title:'נתונים: ייבוא, ייצוא וגיבוי',keys:[],render:()=>`
   <h3>נתונים</h3><p class="d">ייבוא וייצוא של הקטלוג (Excel / CSV), גיבוי ושחזור.</p>
   <div class="acts"><button class="btn primary" data-act="do:exp">⬇ ייצוא ל-Excel / CSV…</button><button class="btn" data-act="do:imp">⬆ ייבוא מקובץ…</button></div>
   <h4>גיבוי</h4><div class="acts"><button class="btn" data-act="do:backup">שמירת גיבוי מלא…</button><button class="btn" data-act="do:restore">שחזור מגיבוי…</button></div>
   <p class="hint">הגיבוי כולל את כל הספרים, ההגדרות, הסמל ותמונת הפתיחה. בשחזור - ההגדרות והסיסמה הנוכחיות נשמרות.</p>
   <h4>מיקום הנתונים במחשב</h4><div class="note" dir="ltr" style="text-align:left">${esc(S.meta?S.meta.db_path:'')}</div>
   <p class="hint">קובץ הנתונים נשאר במקום קבוע גם כשמחליפים גרסה. במעבר למחשב אחר: שמירת גיבוי כאן, ושחזור במחשב החדש.</p>`},
 {id:'update',icon:'⟳',title:'עדכון גרסה',need:'update',keys:[],render:()=>`
   <h3>עדכון גרסה</h3><p class="d">הדרך הפשוטה: לוחצים על הכפתור, בוחרים את קובץ הגרסה החדשה - והתוכנה מתקינה אותו ונפתחת מחדש. הנתונים וההגדרות לא נפגעים, ולפני העדכון נשמר גיבוי.</p>
   <div id="updBox"><p class="cap">טוען…</p></div>`,after:renderUpd},
 {id:'security',icon:'🔑',title:'סיסמה ואבטחה',keys:['admin'],render:()=>`
   <h3>סיסמה ואבטחה</h3>
   <h4>החלפת סיסמת המנהל</h4><div class="sg" style="max-width:46em"><label>הסיסמה הנוכחית<input type="password" id="pwOld" autocomplete="off"></label><label>סיסמה חדשה<input type="password" id="pwNew" autocomplete="off"></label><label>אימות הסיסמה החדשה<input type="password" id="pwNew2" autocomplete="off"></label></div>
   <div class="acts"><button class="btn primary" data-act="pw">החלפת הסיסמה</button><span class="err" id="pwErr" style="margin:0"></span></div>
   <h4>נעילה אוטומטית</h4><div class="sg">${ni('admin.timeout_min','יציאה ממצב מנהל אחרי כמה דקות ללא פעילות',1,1440)}</div>
   <div class="note">שכחת את הסיסמה? סגור את התוכנה והפעל אותה פעם אחת עם הפרמטר <b dir="ltr">--reset-password</b> (למשל: <span dir="ltr">python book_catalog.py --reset-password</span>). בכניסה הבאה למצב מנהל תתבקש לקבוע סיסמה חדשה. הנתונים לא נמחקים.</div>`},
];
function visibleSections(){return SECTIONS.filter(s=>ADMIN||(s.need&&can(s.need)));}
function openAdm(sec){
  const vs=visibleSections(); if(!vs.length){openLogin();return;}
  W=clone(C); DIRTY=false; SEC=vs.some(s=>s.id===sec)?sec:(vs.some(s=>s.id===SEC)?SEC:vs[0].id);
  $('#admFoot').hidden=!ADMIN; $('#admLock').hidden=!ADMIN;
  renderAdm(); if(!$('#adm').open)$('#adm').showModal();
}
function renderAdm(){
  const vs=visibleSections();
  $('#admNav').innerHTML=vs.map(s=>`<button type="button" data-sec="${s.id}" class="${s.id===SEC?'on':''}"><span>${s.icon}</span>${esc(s.title)}</button>`).join('');
  const s=SECTIONS.find(x=>x.id===SEC); const top=$('#admMain').scrollTop;
  $('#admMain').innerHTML=s.render(); $('#admMain').scrollTop=top;
  $('#admReset').hidden=!s.keys.length; $('#dirty').hidden=!DIRTY;
  if(s.after)s.after();
}
function dirty(){DIRTY=true;$('#dirty').hidden=false;applyTheme(W);const keep=C;C=W;applyTexts(W);C=keep;}
function closeAdm(){
  if(DIRTY&&!confirm('יש שינויים שלא נשמרו. לסגור בלי לשמור?'))return;
  DIRTY=false; W=null; $('#adm').close(); applyTheme(C); applyTexts(C);
}
async function saveAdm(){
  try{
    const b=await send('PUT','/api/config',W);
    Object.assign(B,b); C=B.cfg; W=clone(C); DIRTY=false; rebuild(); await loadMeta(); renderAdm(); toast('ההגדרות נשמרו');
  }catch(e){toast('השמירה נכשלה: '+e.message);}
}
/* --- מיקומים --- */
async function renderLocs(){
  await loadMeta(); const box=$('#locBox'); if(!box)return; const L=S.meta.locations;
  box.innerHTML=`<table class="s"><tr><th>שם המיקום</th><th style="width:6.5em">ממדף</th><th style="width:6.5em">עד מדף</th><th style="width:6em">אות</th><th>ספרים</th><th></th></tr>
   ${L.map((l,i)=>`<tr data-loc="${esc(l.name)}"><td><input class="ln" value="${esc(l.name)}"></td><td><input class="lf" type="number" min="1" max="999" value="${l.shelf_from??''}"></td><td><input class="lt" type="number" min="1" max="999" value="${l.shelf_to??''}"></td><td><input class="ll" value="${esc(l.letter)}" maxlength="6" style="width:4.5em"></td><td class="cap">${num(l.count)}</td>
     <td style="white-space:nowrap"><button class="btn sm primary" data-act="loc-save">שמירה</button> ${upDn('loc',i,L.length)} <button class="btn sm danger" data-act="loc-del">מחיקה</button></td></tr>`).join('')}
   <tr data-loc=""><td><input class="ln" placeholder="מיקום חדש…"></td><td><input class="lf" type="number" min="1" max="999"></td><td><input class="lt" type="number" min="1" max="999"></td><td><input class="ll" maxlength="6" style="width:4.5em"></td><td></td><td><button class="btn sm primary" data-act="loc-add">＋ הוספה</button></td></tr></table>
   <div class="acts"><button class="btn gold" data-act="loc-apply">עדכון המיקום של כל הספרים לפי המדפים</button><span class="err" id="locErr" style="margin:0"></span></div>
   <p class="hint">אחרי שינוי טווחים - לחץ על "עדכון המיקום של כל הספרים" כדי להחיל אותם על הספרים הקיימים.</p>`;
}
async function locAct(act,tr){
  const err=m=>{const e=$('#locErr');if(e)e.textContent=m;};
  const d=tr?{name:tr.querySelector('.ln').value.trim(),shelf_from:tr.querySelector('.lf').value,shelf_to:tr.querySelector('.lt').value,letter:tr.querySelector('.ll').value.trim()}:{};
  const old=tr?tr.dataset.loc:'';
  try{
    if(act==='loc-add'){if(!d.name)return err('יש להקליד שם למיקום החדש');await send('POST','/api/location',d);toast('המיקום נוסף');}
    if(act==='loc-save'){await send('PUT','/api/location?name='+encodeURIComponent(old),d);toast('המיקום נשמר');}
    if(act==='loc-del'){if(!confirm('למחוק את המיקום "'+old+'"?'))return;await send('DELETE','/api/location?name='+encodeURIComponent(old));}
    if(act==='loc-apply'){if(!confirm('המיקום של כל הספרים יעודכן לפי מספר המדף והכללים שבטבלה. להמשיך?'))return;const r=await send('POST','/api/locations/apply');toast(`עודכן המיקום של ${num(r.changed)} ספרים`);}
    if(act.startsWith('loc-up')||act.startsWith('loc-dn')){const i=+act.split(':')[1],names=S.meta.locations.map(l=>l.name),j=act.startsWith('loc-up')?i-1:i+1;[names[i],names[j]]=[names[j],names[i]];await send('POST','/api/locations/order',{names});}
    await renderLocs(); if(S.started)run(S.page,true);
  }catch(e){err(e.message);}
}
/* --- רשימות ערכים --- */
let VALS=[];
async function renderValues(reload){
  const f=$('#valField'); if(!f)return;
  if(reload!==false){try{VALS=(await api('/api/values?field='+f.value)).values;}catch(e){$('#valBox').innerHTML=`<p class="err">${esc(e.message)}</p>`;return;}}
  const flt=nrm($('#valFilter').value), rows=VALS.filter(v=>!flt||nrm(v.value).includes(flt)).slice(0,400);
  $('#valBox').innerHTML=`<p class="cap">${num(VALS.length)} ערכים שונים${rows.length<VALS.length?` · מוצגים ${rows.length}`:''}</p><table class="s" style="max-width:46em"><tr><th>ערך</th><th>ספרים</th><th></th></tr>${rows.map(v=>`<tr><td>${v.value?esc(v.value):'<span class="cap">(ריק)</span>'}</td><td class="cap">${num(v.count)}</td><td>${v.value?`<button class="btn sm" data-val="${esc(v.value)}">שינוי / איחוד…</button>`:''}</td></tr>`).join('')}</table>`;
}
/* --- עדכון גרסה --- */
async function renderUpd(){
  const box=$('#updBox'); if(!box)return; let s;
  try{s=await api('/api/update/status');}catch(e){box.innerHTML=`<p class="err">${esc(e.message)}</p>`;return;}
  const ext=(s.kind||'.py').replace('.','');
  box.innerHTML=`<div class="note"><b>הגרסה המותקנת: ${esc(s.current)}</b>${s.available?` &nbsp;·&nbsp; גרסה חדשה מוכנה להתקנה: <b>${esc(s.latest)}</b>`:''}${s.check_error?`<br><span class="err">${esc(s.check_error)}</span>`:''}${s.install_error?`<br><span class="err">העדכון נכשל: ${esc(s.install_error)}</span>`:''}</div>
   <div class="acts"><button class="btn primary" data-act="upd-pick">בחירת קובץ גרסה חדשה (${ext})…</button>${s.available&&s.can_install?`<button class="btn gold" data-act="upd-apply">התקנת גרסה ${esc(s.latest)} עכשיו</button>`:''}<button class="btn" data-act="upd-check">בדיקה אם יש עדכון בתיקייה</button></div>
   <h4>תיקיית העדכונים</h4><p class="hint">אפשר גם להניח את קובץ הגרסה החדשה בתיקייה הזו (למשל תיקייה משותפת ברשת) - התוכנה תזהה אותו לבד ותציע לעדכן.</p>
   <div class="acts"><input id="updPath" dir="ltr" style="flex:1;min-width:16em" spellcheck="false" value="${esc(s.dir)}"><button class="btn" data-act="upd-browse">עיון…</button><button class="btn" data-act="upd-open">פתיחת התיקייה</button><button class="btn" data-act="upd-default">ברירת מחדל</button><button class="btn primary" data-act="upd-save">שמירה</button></div>
   <span class="err" id="updErr"></span>`;
  box.dataset.def=s.default_dir; box.dataset.ext=ext;
}
async function updAct(act){
  const err=m=>{const e=$('#updErr');if(e)e.textContent=m;};
  try{
    if(act==='upd-pick'){const f=$('#updFile');f.accept='.'+($('#updBox').dataset.ext||'py');f.click();return;}
    if(act==='upd-apply')return updApply();
    if(act==='upd-check'){U.manual=true;U.hidden='';await send('POST','/api/update/check?force=1');toast('בודק עדכונים…');await updPoll();setTimeout(renderUpd,900);return;}
    if(act==='upd-browse'){const r=await send('POST','/api/update/browse');if(r.dir)$('#updPath').value=r.dir;return;}
    if(act==='upd-default'){$('#updPath').value=$('#updBox').dataset.def;return;}
    if(act==='upd-open'||act==='upd-save'){await send('POST','/api/update/dir',{dir:$('#updPath').value});if(act==='upd-open')await send('POST','/api/update/open');else toast('תיקיית העדכונים נשמרה');setTimeout(renderUpd,600);}
  }catch(e){err(e.message);}
}
async function updApply(){
  if(!confirm('העדכון יתקין את הגרסה החדשה, יסגור את התוכנה ויפתח אותה מחדש.\nהנתונים וההגדרות לא ייפגעו, ולפני העדכון נשמר גיבוי.\n\nלהמשיך?'))return;
  try{updRender(await send('POST','/api/update/apply'));updPoll();}catch(err){toast(err.message);}
}

/* ---------- אירועי ההגדרות ---------- */
function bindAdm(){
  $('#admNav').onclick=e=>{const b=e.target.closest('[data-sec]');if(b){SEC=b.dataset.sec;$('#admMain').scrollTop=0;renderAdm();}};
  $('#admX').onclick=closeAdm; $('#admLock').onclick=()=>{if(DIRTY&&!confirm('יש שינויים שלא נשמרו. לצאת בלי לשמור?'))return;DIRTY=false;applyTheme(C);applyTexts(C);lock();};
  $('#adm').addEventListener('cancel',e=>{e.preventDefault();closeAdm();});
  $('#admSave').onclick=saveAdm;
  $('#admRevert').onclick=()=>{W=clone(C);DIRTY=false;applyTheme(C);applyTexts(C);renderAdm();};
  $('#admReset').onclick=()=>{const s=SECTIONS.find(x=>x.id===SEC);if(!confirm('להחזיר את כל ההגדרות בקטגוריה "'+s.title+'" לברירת המחדל?'))return;s.keys.forEach(k=>W[k]=clone(B.defaults[k]));dirty();renderAdm();};
  const M=$('#admMain');
  const onInput=e=>{
    const t=e.target;
    if(t.id==='valFilter')return renderValues(false);
    if(t.id==='valField')return renderValues();
    if(t.dataset.p){
      let v=t.type==='checkbox'?t.checked:t.type==='number'?(t.value===''?0:Number(t.value)):t.value;
      setP(W,t.dataset.p,v); dirty();
      if(t.dataset.p.startsWith('theme.colors.')){W.theme.preset='custom';$$(`#admMain [data-p="${t.dataset.p}"]`).forEach(x=>{if(x!==t&&/^#[0-9a-fA-F]{6}$/.test(v))x.value=v;});const c=$('#ctrTbl');if(c)c.innerHTML=contrastRow();}
      return;
    }
    if(t.dataset.tf){const [i,k]=t.dataset.tf.split(':');const f=W.search.types[+i].fields;const at=f.indexOf(k);if(t.checked&&at<0)f.push(k);if(!t.checked&&at>=0)f.splice(at,1);return dirty();}
    if(t.dataset.list){setP(W,t.dataset.list,t.value.split(/[,\s]+/).map(Number).filter(n=>n>0));return dirty();}
    if(t.dataset.view){const v=W.results.views,k=t.dataset.view,at=v.indexOf(k);if(t.checked&&at<0)v.push(k);if(!t.checked&&at>=0)v.splice(at,1);if(!v.length){v.push(k);t.checked=true;}if(!v.includes(W.results.default_view))W.results.default_view=v[0];dirty();if(e.type==='change')renderAdm();}
  };
  M.addEventListener('input',onInput); M.addEventListener('change',onInput);
  M.addEventListener('click',async e=>{
    const v=e.target.closest('[data-val]');
    if(v){const old=v.dataset.val,f=$('#valField').value;const nv=prompt(`ערך חדש במקום "${old}" בשדה ${fl(f)}.\nאם הערך החדש כבר קיים - שני הערכים יאוחדו.`,old);if(nv===null||nv.trim()===old)return;
      try{const r=await send('POST','/api/values',{field:f,old,new:nv.trim()});toast(`עודכנו ${num(r.count)} ספרים`);await loadMeta();renderValues();if(S.started)run(S.page,true);}catch(err){toast(err.message);}return;}
    const b=e.target.closest('[data-act]'); if(!b)return;
    const [act,arg]=b.dataset.act.split(':'); const i=+arg;
    const move=(arr,up)=>{const j=up?i-1:i+1;[arr[i],arr[j]]=[arr[j],arr[i]];dirty();renderAdm();};
    if(act==='preset'){W.theme.preset=arg;W.theme.colors=clone(B.presets[arg].colors);dirty();return renderAdm();}
    if(act==='type-add'){W.search.types.push({id:'t'+Date.now().toString(36),label:'חיפוש חדש',fields:['all'],on:true});dirty();return renderAdm();}
    if(act==='type-del'){if(W.search.types.length<2)return toast('חייב להישאר סוג חיפוש אחד לפחות');W.search.types.splice(i,1);dirty();return renderAdm();}
    if(act==='type-up'||act==='type-dn')return move(W.search.types,act==='type-up');
    if(act==='type-def'){W.search.default_type=W.search.types[i].id;W.search.types[i].on=true;dirty();return renderAdm();}
    if(act==='cond-add'){W.conditions.push({name:'מצב חדש',color:'#5B5B5B'});dirty();return renderAdm();}
    if(act==='cond-del'){W.conditions.splice(i,1);dirty();return renderAdm();}
    if(act==='cond-up'||act==='cond-dn')return move(W.conditions,act==='cond-up');
    if(act==='perm-all'||act==='perm-none'){Object.keys(W.perms).forEach(k=>W.perms[k]=act==='perm-all'||['search_adv','search_types','change_view','change_sort','view_details','browse_locations','show_count','quit'].includes(k));dirty();return renderAdm();}
    if(act==='asset'){S.assetName=arg;const f=$('#assetFile');f.accept=arg==='icon'?'.ico':'image/*';f.click();return;}
    if(act==='asset-del'){if(!confirm('להסיר את הקובץ?'))return;try{const r=await api('/api/asset?name='+arg,{method:'DELETE'});B.assets=r.assets;applyTexts(W);renderAdm();}catch(err){toast(err.message);}return;}
    if(act==='splash-test')return showSplash(W,true);
    if(act==='do'){ if(arg==='exp')openExport('all'); if(arg==='imp')openImport(); if(arg==='backup')saveFile('/api/backup','הגיבוי'); if(arg==='restore')$('#restoreFile').click(); return; }
    if(act==='pw'){const er=$('#pwErr');er.textContent='';if($('#pwNew').value!==$('#pwNew2').value){er.textContent='שתי הסיסמאות החדשות אינן זהות';return;}
      try{const r=await send('POST','/api/admin/password',{old:$('#pwOld').value,new:$('#pwNew').value});TOKEN=r.token;try{sessionStorage.setItem('cat.tok',TOKEN);}catch(_){ }$('#pwOld').value=$('#pwNew').value=$('#pwNew2').value='';toast('הסיסמה הוחלפה');}catch(err){er.textContent=err.message;}return;}
    if(act.startsWith('loc-'))return locAct(b.dataset.act,b.closest('tr'));
    if(act.startsWith('upd-'))return updAct(act);
  });
  $('#assetFile').onchange=async e=>{
    const f=e.target.files[0]; e.target.value=''; if(!f)return;
    try{const r=await api('/api/asset?name='+S.assetName,{method:'POST',body:await f.arrayBuffer()});B.assets=r.assets;
      if(S.assetName==='logo'&&W){W.logo.use_image=true;dirty();}
      if(S.assetName==='splash'&&W&&!W.splash.enabled){W.splash.enabled=true;dirty();}
      applyTexts(W||C);renderAdm();toast('הקובץ נשמר');}catch(err){toast(err.message);}
  };
  $('#updFile').onchange=async e=>{
    const f=e.target.files[0]; e.target.value=''; if(!f)return;
    try{
      toast('מעלה את קובץ הגרסה…');
      let url='/api/update/upload?name='+encodeURIComponent(f.name), r;
      try{r=await api(url,{method:'POST',body:await f.arrayBuffer()});}
      catch(err){ if(!/מספר הגרסה/.test(err.message))throw err; const v=prompt('מהו מספר הגרסה של הקובץ? (למשל 3.1)'); if(!v)return; r=await api(url+'&version='+encodeURIComponent(v),{method:'POST',body:await f.arrayBuffer()}); }
      await renderUpd(); updRender(r);
      if(r.available&&r.can_install)updApply();
      else if(r.available)toast('הקובץ נשמר בתיקיית העדכונים, אך אי אפשר להתקין אותו אוטומטית כאן.');
      else toast(r.check_error||`הקובץ שנבחר הוא גרסה ${r.uploaded}, והגרסה המותקנת היא ${r.current} - אין מה לעדכן.`,null,7000);
    }catch(err){toast(err.message,null,7000);}
  };
}

/* ---------- מסך פתיחה ---------- */
function showSplash(c,force){
  const sp=c.splash, el=$('#splash'), url=assetUrl('splash');
  if(!url||(!sp.enabled&&!force))return;
  if(!force){try{if(sessionStorage.getItem('cat.splash'))return;sessionStorage.setItem('cat.splash','1');}catch(_){}}
  const img=el.querySelector('img'); img.src=url; img.style.objectFit=sp.fit; el.style.background=sp.bg;
  el.querySelector('.cap').textContent=sp.caption||''; el.classList.remove('out'); el.hidden=false;
  const close=()=>{el.classList.add('out');setTimeout(()=>{el.hidden=true;},650);document.removeEventListener('keydown',key);};
  const key=()=>{if(sp.click_to_close||force)close();};
  el.onclick=key; document.addEventListener('keydown',key);
  setTimeout(close,Math.max(1,sp.seconds)*1000);
}

/* ---------- אשף הגדרה ראשונית ---------- */
function openWizard(){
  $('#w_preset').innerHTML=Object.entries(B.presets).map(([k,p])=>`<option value="${k}">${esc(p.name)}</option>`).join('');
  $('#w_preset').value=C.theme.preset in B.presets?C.theme.preset:'parchment';
  const row=()=>$('#w_locs').insertAdjacentHTML('beforeend','<tr><td><input class="ln"></td><td><input class="lf" type="number" min="1" max="999"></td><td><input class="lt" type="number" min="1" max="999"></td><td><input class="ll" maxlength="6" style="width:4.5em"></td></tr>');
  $('#w_locs').innerHTML=''; row(); row();
  $('#wizAddLoc').onclick=row;
  $('#w_preset').onchange=()=>{const t=clone(C);t.theme.colors=clone(B.presets[$('#w_preset').value].colors);applyTheme(t);};
  $('#w_name').oninput=()=>{$('#logoTxt').textContent=$('#w_name').value||T('app_title');};
  $('#wizDlg').addEventListener('cancel',e=>e.preventDefault());
  $('#wizGo').onclick=()=>wizSubmit(false); $('#wizSkip').onclick=()=>wizSubmit(true);
  $('#wizDlg').showModal(); $('#w_name').focus();
}
async function wizSubmit(skip){
  const er=$('#wizErr'); er.textContent=''; let body={skip:true};
  if(!skip){
    body={name:$('#w_name').value.trim(),tagline:$('#w_tagline').value.trim(),emoji:$('#w_emoji').value.trim(),preset:$('#w_preset').value,password:$('#w_pw').value,starter:document.querySelector('input[name=w_start]:checked').value==='1',
      locations:$$('#w_locs tr').map(tr=>({name:tr.querySelector('.ln').value.trim(),shelf_from:tr.querySelector('.lf').value,shelf_to:tr.querySelector('.lt').value,letter:tr.querySelector('.ll').value.trim()})).filter(l=>l.name)};
    if(!body.name){er.textContent='יש להקליד את שם הספרייה';$('#w_name').focus();return;}
    if(body.password.length<4){er.textContent='יש לקבוע סיסמת מנהל (לפחות 4 תווים)';$('#w_pw').focus();return;}
    if(body.password!==$('#w_pw2').value){er.textContent='שתי הסיסמאות אינן זהות';return;}
  }
  try{
    const r=await send('POST','/api/admin/wizard',body);
    Object.assign(B,r); C=B.cfg; $('#wizDlg').close();
    if(r.token)setAdmin(true,r.token);
    rebuild(); await loadMeta();
    toast(skip?'אפשר להגדיר את הספרייה בכל עת: כפתור המנעול > מצב מנהל':'הספרייה הוגדרה. כעת אפשר לייבא קטלוג או להוסיף ספרים.',skip?null:[['ייבוא מקובץ',()=>openImport()]],9000);
  }catch(e){er.textContent=e.message;applyTheme(C);}
}

/* ---------- ייבוא ---------- */
function openImport(){
  $('#impCols').textContent='שורת הכותרת בקובץ קובעת את העמודות: '+FKEYS.map(fl).join(', ')+". מספיקה עמודה אחת - "+fl('title')+". העמודות \"מס'\" ו\"מס' הספר הראשי\" (אם קיימות) קושרות נספח לספר הראשי שלו.";
  $('#impErr').textContent=''; $('#impFile').value=''; $('#impDlg').showModal();
}

/* ---------- אירועים ---------- */
function bind(){
  $('#q').addEventListener('input',schedule);
  $('#sf').addEventListener('submit',e=>{e.preventDefault();run(1,true);});
  $('#clr').onclick=()=>{$('#q').value='';$('#q').focus();run(1);};
  $('#types').onclick=e=>{const b=e.target.closest('[data-t]');if(!b)return;S.type=b.dataset.t;store.set('type',S.type);buildTypes();$('#q').focus();if($('#q').value.trim())run(1,true);};
  $('#advBtn').onclick=()=>{setMode(true);$('#adv').hidden=false;const f=$('#advForm input');if(f)f.focus();run(1,true);};
  $('#advtoggle').onclick=()=>{$('#adv').hidden=!$('#adv').hidden;if(!$('#adv').hidden){const f=$('#advForm input');if(f)f.focus();}};
  $('#advForm').addEventListener('submit',e=>{e.preventDefault();run(1,true);});
  $('#advForm').addEventListener('input',e=>{if(e.target.tagName==='SELECT')run(1,true);});
  $('#logo').onclick=e=>{e.preventDefault();clearFilters();run(1);$('#q').focus();};
  $('#sort').onchange=$('#dir').onchange=()=>run(1,true);
  $('#psize').onchange=()=>{S.size=+$('#psize').value;store.set('size',S.size);run(1,true);};
  $('#viewSeg').onclick=e=>{const b=e.target.closest('[data-v]');if(!b)return;S.view=b.dataset.v;store.set('view',S.view);buildBars();if(S.last)render(S.last);};
  $('#expBtn').onclick=()=>openExport(S.sel.size?'sel':'res');
  $('#homeChips').onclick=e=>{const b=e.target.closest('[data-loc]');if(b){$('#a_location').value=b.dataset.loc;$('#sort').value='shelf';run(1,true);}};
  $('#list').onclick=e=>{
    const more=e.target.closest('[data-more]');
    if(more){e.stopPropagation();more.parentElement.querySelectorAll('li[hidden]').forEach(x=>x.hidden=false);more.remove();return;}
    const op=e.target.closest('[data-open]');
    if(op){e.preventDefault();e.stopPropagation();openView(+op.dataset.open);return;}
    const a=e.target.closest('a[data-loc]');
    if(a&&can('browse_locations')){e.preventDefault();e.stopPropagation();
      clearFilters();$('#a_location').value=a.dataset.loc; $('#a_shelf').value=a.dataset.shelf||''; $('#sort').value='shelf';run(1,true);return;}
    if(a){e.preventDefault();}
    if(e.target.id==='selAll'){const on=e.target.checked;$$('#list [data-sel]').forEach(c=>{c.checked=on;on?S.sel.add(+c.dataset.sel):S.sel.delete(+c.dataset.sel);});renderBulk();return;}
    const sc=e.target.closest('[data-sel]');
    if(sc){sc.checked?S.sel.add(+sc.dataset.sel):S.sel.delete(+sc.dataset.sel);renderBulk();return;}
    if(e.target.closest('td')&&e.target.closest('td').querySelector('[data-sel]'))return;
    const th=e.target.closest('th[data-sort]');
    if(th){ if(!th.dataset.sort||!can('change_sort'))return; if($('#sort').value===th.dataset.sort)$('#dir').value=$('#dir').value==='asc'?'desc':'asc'; else{$('#sort').value=th.dataset.sort;$('#dir').value='asc';} run(1,true);return;}
    const r=e.target.closest('[data-id]'); if(r){e.preventDefault();openView(+r.dataset.id);}
  };
  $('#bulk').onclick=async e=>{
    const a=(e.target.closest('[data-b]')||{dataset:{}}).dataset.b; if(!a)return; const ids=[...S.sel];
    if(a==='clear'){S.sel.clear();if(S.last)render(S.last);return;}
    if(a==='exp')return openExport('sel');
    try{
      if(a==='del'){if(!confirm(`למחוק ${ids.length} ספרים? אי אפשר לבטל את הפעולה (אפשר לשחזר מגיבוי).`))return;const r=await send('POST','/api/books/bulk',{ids,action:'delete'});toast(`נמחקו ${num(r.count)} ספרים`);}
      if(a==='set'){const f=$('#bkField').value,v=$('#bkVal').value.trim();if(!confirm(`לקבוע בשדה "${fl(f)}" את הערך "${v}" ב-${ids.length} ספרים?`))return;const r=await send('POST','/api/books/bulk',{ids,action:'set',field:f,value:v});toast(`עודכנו ${num(r.count)} ספרים`);}
      S.sel.clear(); await loadMeta(); run(S.page,true);
    }catch(err){toast(err.message);}
  };
  $('#pager').onclick=e=>{const b=e.target.closest('[data-p]');if(b&&!b.disabled){run(+b.dataset.p,true);window.scrollTo(0,0);}};
  $('#addBtn').onclick=()=>openEdit(null,{location:advVal('location'),shelf:store.get('lastShelf','')});
  $('#saveBtn').onclick=()=>{store.set('lastShelf',fval('shelf')||'');save(false);}; $('#saveAddBtn').onclick=()=>{store.set('lastShelf',fval('shelf')||'');save(true);};
  $('#cancelBtn').onclick=()=>$('#dlg').close();
  $('#delBtn').onclick=async()=>{
    if(!confirm('למחוק את הספר "'+$('#f_title').value+'"?'))return;
    try{await api('/api/book?id='+S.editId,{method:'DELETE'}); $('#dlg').close(); toast('הספר נמחק'); await loadMeta(); if(S.started)run(S.page,true);}catch(err){$('#dlgErr').textContent=err.message;}
  };
  $('#dlg').addEventListener('keydown',e=>{if(e.key==='Enter'&&e.target.tagName==='INPUT'&&$('#annexDD')&&$('#annexDD').hidden!==false){e.preventDefault();save(false);}});
  $('#vClose').onclick=()=>$('#viewDlg').close();
  $('#vEdit').onclick=()=>openEdit(S.viewId);
  $('#vShelf').onclick=()=>{const b=S.viewBook;$('#viewDlg').close();clearFilters();$('#a_shelf').value=b.shelf_text;$('#sort').value='title';run(1,true);};
  $('#vBody').onclick=e=>{const op=e.target.closest('[data-open]');if(op){e.preventDefault();openView(+op.dataset.open);}};
  // מנהל
  $('#adminBtn').onclick=()=>ADMIN?lock():openLogin();
  $('#setBtn').onclick=()=>openAdm();
  $('#loginGo').onclick=doLogin; $('#loginCancel').onclick=()=>$('#loginDlg').close();
  $('#loginDlg').addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();doLogin();}});
  // תפריט
  $('#menuBtn').onclick=e=>{e.stopPropagation();$('#menu').hidden=!$('#menu').hidden;};
  document.addEventListener('click',()=>{$('#menu').hidden=true;});
  $('#menu').onclick=async e=>{
    const a=e.target.dataset.a; if(!a)return; $('#menu').hidden=true;
    if(a==='exp')openExport(S.started?'res':'all');
    if(a==='imp')openImport();
    if(a==='print')window.print();
    if(a==='backup')saveFile('/api/backup','הגיבוי');
    if(a==='restore')$('#restoreFile').click();
    if(a==='settings')openAdm();
    if(a.startsWith('sec:'))openAdm(a.slice(4));
    if(a==='login')openLogin();
    if(a==='lock')lock();
    if(a==='about')alert(`${T('app_title')} · גרסה ${B.version}\n\nקובץ הנתונים נשמר תמיד כאן, קבוע, לא משנה איזו גרסה מריצים:\n${S.meta.db_path||''}\n\nבמעבר למחשב אחר: שמירת גיבוי, ושחזור במחשב החדש.`);
    if(a==='quit'&&(!C.general.confirm_quit||confirm('לסגור את התוכנה?'))){
      try{await send('POST','/api/quit');}catch(_){} document.body.innerHTML='<p style="padding:40px;font-size:20px">התוכנה נסגרה. אפשר לסגור את החלון.</p>';}
  };
  $('#impCancel').onclick=()=>$('#impDlg').close();
  $('#impGo').onclick=async()=>{
    const f=$('#impFile').files[0]; if(!f){$('#impErr').textContent='יש לבחור קובץ';return;}
    const mode=document.querySelector('input[name=impMode]:checked').value;
    if(mode==='replace'&&!confirm('פעולה זו תמחק את כל הקטלוג הנוכחי ותחליף אותו בקובץ. (לפני כן נשמר גיבוי אוטומטי.) להמשיך?'))return;
    $('#impGo').disabled=true; $('#impErr').textContent='מייבא… (קובץ גדול עשוי לקחת כדקה)';
    try{
      const r=await api('/api/import?mode='+mode,{method:'POST',body:await f.arrayBuffer()});
      $('#impDlg').close(); await loadMeta(); run(1);
      toast(`יובאו ${num(r.imported)} ספרים`+(r.updated?` · עודכנו ${num(r.updated)}`:'')+(r.skipped?` · דולגו ${r.skipped} שורות בלי שם ספר`:'')+(r.bad_shelf?` · ${r.bad_shelf} מדפים לא תקינים נשארו ריקים`:''),null,8000);
    }catch(e){$('#impErr').textContent=e.message;}
    $('#impGo').disabled=false;
  };
  $('#expCancel').onclick=()=>$('#expDlg').close(); $('#expGo').onclick=doExport;
  $('#expAll').onclick=()=>$$('#expCols input').forEach(c=>c.checked=true); $('#expNone').onclick=()=>$$('#expCols input').forEach(c=>c.checked=false);
  $('#restoreFile').onchange=async e=>{
    const f=e.target.files[0]; e.target.value=''; if(!f)return;
    if(!confirm('כל הספרים בקטלוג יוחלפו בגיבוי שנבחר (ההגדרות והסיסמה הנוכחיות נשמרות). להמשיך?'))return;
    try{await api('/api/restore',{method:'POST',body:await f.arrayBuffer()}); await loadMeta(); run(1); toast('הקטלוג שוחזר');}catch(err){alert(err.message);}
  };
  document.addEventListener('keydown',e=>{
    if(e.key==='/'&&!/INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName)&&!document.querySelector('dialog[open]')){e.preventDefault();$('#q').focus();}
  });
  bindAdm();
}

/* ---------- עדכוני גרסה (פס עליון) ---------- */
const U={timer:null,manual:false,hidden:'',last:null};
function updRender(s){
  U.last=s;
  const bar=$('#updBar');
  if(!s.enabled||!can('update')){bar.hidden=true;return;}
  const show=h=>{bar.innerHTML=h;bar.hidden=false;};
  if(s.state==='downloading')return show(`<span>⬇ מעתיק את גרסה ${esc(s.latest)}…</span><div class="bar"><i style="width:${s.progress}%"></i></div><small>${s.progress}%</small>`);
  if(s.state==='installing')return show(`<span>מתקין את גרסה ${esc(s.latest)}…</span>`);
  if(s.state==='restarting'){setTimeout(()=>location.reload(),4000);return show('<span>העדכון הותקן. התוכנה נפתחת מחדש…</span>');}
  if(s.install_error){
    if(U.hidden==='e:'+s.install_error){bar.hidden=true;return;}
    return show(`<span>העדכון נכשל: ${esc(s.install_error)}</span>`+(s.has_page?'<button class="btn" data-u="page">פתיחת תיקיית העדכונים</button>':'')+'<button class="btn" data-u="hide">סגירה</button>');
  }
  if(s.available&&U.hidden!=='v:'+s.latest){
    const notes=s.notes?`<details><summary>מה חדש בגרסה?</summary><div class="notes">${esc(s.notes)}</div></details>`:'';
    return show(`<span>🔔 גרסה חדשה זמינה: <b>${esc(s.latest)}</b> <small>(הגרסה שלך: ${esc(s.current)})</small></span>`+
      (s.can_install?'<button class="btn primary" data-u="apply">עדכון עכשיו</button>':'<button class="btn primary" data-u="page">פתיחת תיקיית העדכונים</button>')+
      '<button class="btn" data-u="hide">לא עכשיו</button>'+notes);
  }
  bar.hidden=true;
}
async function updPoll(){
  clearTimeout(U.timer);
  let s; try{s=await api('/api/update/status');}catch(_){return;}
  updRender(s);
  if(['checking','downloading','installing'].includes(s.state)){U.timer=setTimeout(updPoll,700);return;}
  if(U.manual){
    U.manual=false;
    if(!s.enabled)toast('תיקיית העדכונים לא הוגדרה');
    else if(s.check_error)toast('לא ניתן לבדוק עדכונים כרגע: '+s.check_error,null,7000);
    else if(!s.available)toast('לא נמצאה גרסה חדשה בתיקיית העדכונים. הגרסה שלך: '+s.current,null,6000);
  }
}
async function updStart(){ if(can('update')){try{await send('POST','/api/update/check');}catch(_){}} updPoll(); }
$('#updBar').onclick=async e=>{
  const a=e.target.dataset.u; if(!a)return;
  if(a==='hide'){const s=U.last||{};U.hidden=s.install_error?'e:'+s.install_error:'v:'+s.latest;$('#updBar').hidden=true;}
  if(a==='page'){try{await send('POST','/api/update/open');}catch(err){toast(err.message);}}
  if(a==='apply')updApply();
};

/* ---------- הפעלה ---------- */
(async function init(){
  S.type=activeTypes().some(t=>t.id===store.get('type'))&&can('search_types')?store.get('type'):C.search.default_type;
  S.view=C.results.default_view;
  showSplash(C);
  bind();
  if(TOKEN){try{const b=await api('/api/boot');Object.assign(B,b);C=B.cfg;ADMIN=!!b.admin;if(!ADMIN)TOKEN='';}catch(_){TOKEN='';}}
  applyTexts(C); buildTypes(); buildAdv(); buildForm(); buildMenu(); buildBars(); setMode(false);
  await loadMeta(); $('#q').focus();
  if(B.needs_setup)openWizard();
  updStart(); setInterval(updStart,Math.max(1,C.general.update_check_min)*60000);
})();

</script>
</body>
</html>
"""


# =====================================================================
#                              הרצה
# =====================================================================
def open_existing(port):
    try:
        with urllib.request.urlopen(f"http://127.0.0.1:{port}/api/meta", timeout=1.5) as r:
            return r.status == 200
    except Exception:
        return False


def _open_window(cat, url):
    """פותח את חלון התוכנה (pywebview). חוזר כשהחלון נסגר."""
    g = cat.cfg["general"]
    title = cat.cfg["texts"]["window_title"] or "קטלוג ספרים"
    RUN["title"] = title
    try:
        webview.settings["ALLOW_DOWNLOADS"] = True      # גיבוי למקרה שהורדה רגילה תידרש
    except Exception:
        pass
    kw = dict(width=max(640, g["window_w"]), height=max(480, g["window_h"]))
    try:
        RUN["window"] = webview.create_window(title, url, maximized=bool(g["maximized"]), **kw)
    except TypeError:                                    # גרסה ישנה של pywebview
        RUN["window"] = webview.create_window(title, url, **kw)
    icon = None
    asset = cat.get_asset("icon")
    if asset:
        icon = os.path.join(APP_DIR, "app.ico")
        try:
            with open(icon, "wb") as f:
                f.write(asset[1])
        except OSError:
            icon = None
    threading.Thread(target=apply_window_icon, args=(cat, title), daemon=True).start()
    try:
        webview.start(icon=icon) if icon else webview.start()
    except TypeError:
        webview.start()


def main():
    for s in (sys.stdout, sys.stderr):
        try:
            s.reconfigure(errors="replace")
        except Exception:
            pass

    if "--selftest" in sys.argv:
        sys.exit(selftest())

    if "--embed" in sys.argv:       # python book_catalog.py --embed profile.json out.py
        i = sys.argv.index("--embed")
        with io.open(sys.argv[i + 1], encoding="utf-8-sig") as f:
            prof = json.load(f)
        with io.open(os.path.abspath(__file__), encoding="utf-8", newline="") as f:
            src = f.read()
        with io.open(sys.argv[i + 2], "w", encoding="utf-8", newline="") as f:
            f.write(embed_profile(src, prof))
        print("נוצר:", sys.argv[i + 2])
        return

    if "--reset-password" in sys.argv:
        cat = Catalog()
        cat.clear_password()
        cat.close()
        print("סיסמת המנהל אופסה. בכניסה הבאה למצב מנהל תתבקש לקבוע סיסמה חדשה.")
        return

    port = DEFAULT_PORT
    if "--port" in sys.argv:
        port = int(sys.argv[sys.argv.index("--port") + 1])
    use_window = webview is not None and "--browser" not in sys.argv and "--no-browser" not in sys.argv

    def show(url):
        if use_window:
            webview.create_window("קטלוג ספרים", url, width=1100, height=800)
            webview.start()
        elif "--no-browser" not in sys.argv:
            import webbrowser
            webbrowser.open(url)

    cat = Catalog()
    frozen = bool(getattr(sys, "frozen", False))
    update_dir = load_update_dir()
    if "--update-dir" in sys.argv:  # תיקיית עדכונים אחרת, רק להרצה הזו (למשל לבדיקות)
        update_dir = sys.argv[sys.argv.index("--update-dir") + 1]
    updater = Updater(update_dir=update_dir, before_install=lambda: _backup_before_update(cat),
                      script_path=None if frozen else os.path.abspath(__file__))
    srv = None

    for p in range(port, port + 11):
        try:
            srv = make_server(cat, p, updater)
            port = p
            break
        except OSError:
            if open_existing(p):
                print(f"Catalog is already running: http://127.0.0.1:{p}")
                cat.close()
                show(f"http://127.0.0.1:{p}")
                return

    if not srv:
        print("Could not find a free port.")
        return

    url = f"http://127.0.0.1:{port}"
    print(f"Book catalog is running at {url}")
    print(f"הנתונים נשמרים כאן (קבוע, לא משתנה בין גרסאות): {DB_PATH}")

    RUN.update(srv=srv, cat=cat)
    cleanup_update_leftovers()  # מוחק שאריות מעדכון קודם
    try:
        cat.auto_backup()
    except Exception:
        pass

    t = threading.Thread(target=srv.serve_forever, daemon=True)
    t.start()

    if use_window:
        _open_window(cat, url)          # חוזר כשהחלון נסגר
    else:
        if webview is None and "--browser" not in sys.argv and "--no-browser" not in sys.argv:
            print("החבילה pywebview לא מותקנת - התוכנה נפתחת בדפדפן. (להתקנה: pip install pywebview)")
        show(url)
        try:
            while t.is_alive():         # עד "סגירת התוכנה" מהתפריט, או Ctrl+C
                t.join(0.5)
        except KeyboardInterrupt:
            pass

    # סגירה מסודרת של התוכנה
    try:
        srv.shutdown()
    except Exception:
        pass
    srv.server_close()
    with cat.lock:
        cat.close()

    # אחרי עדכון: מפעילים את הגרסה החדשה
    if RUN["restart"]:
        relaunch()


# =====================================================================
#                           בדיקה עצמית
# =====================================================================
TEST_PROFILE = {"name": "ספריית בדיקה", "tagline": "משפט בדיקה", "locations": [
    {"name": "אולם א", "shelf_from": 1, "shelf_to": 399}, {"name": "אולם ב", "shelf_from": 400, "shelf_to": 700},
    {"name": "ארכיון", "shelf_from": 900, "shelf_to": 999}, {"name": "מסדרון", "letter": "פ"}]}
DEFAULT_LOCATIONS = [l["name"] for l in TEST_PROFILE["locations"]]
CONDITIONS = ["חדש", "טוב", "בינוני", "דורש תיקון"]


def selftest():
    import random
    tmp = tempfile.mkdtemp()
    cat = Catalog(os.path.join(tmp, "t.db"), profile=TEST_PROFILE)
    cat.save_config({"perms": {k: True for k, _, _ in PERM_DEFS}})   # הבדיקות הישנות: הכול פתוח
    first = ["משה", "אברהם", "יצחק", "יעקב", "שמואל", "דוד", "חיים", "יוסף"]
    last = ["כהן", "לוי", "פרידמן", "גולדברג", "רוזנברג", "אברמוביץ", "שפירא", "קליין"]
    subj = ["הלכה", "גמרא", "מוסר", "מחשבה", "היסטוריה", "פרשנות", "חסידות", "שו\"ת"]
    pubs = ["מוסד הרב קוק", "הוצאת פלדהיים", "הוצאת ספרים", "מכון ירושלים"]
    random.seed(1)
    t = time.time()
    batch = []
    for i in range(50000):
        d = dict(title=f"ספר מספר {i} {random.choice(subj)}", first_name=random.choice(first),
                 last_name=random.choice(last), volume=f"כרך {i % 7}", subject=random.choice(subj),
                 content="תוכן הספר " * 3, cond=random.choice(CONDITIONS),
                 location=random.choice(DEFAULT_LOCATIONS),
                 shelf=f"{random.randint(1, 999)}" + random.choice(["", "", "-א", "-ב"]),
                 publisher=random.choice(pubs), pub_place="ירושלים", pub_year=str(random.randint(1950, 2024)))
        r = cat._prep(d)
        r["added"] = r["updated"] = now()
        batch.append(r)
    with cat.con:
        cols = list(batch[0])
        cat.con.executemany(
            f"INSERT INTO books({','.join(cols)}) VALUES({','.join(':' + c for c in cols)})", batch)
    print(f"Insert 50,000: {time.time() - t:.2f}s")

    def timed(label, f, **kw):
        t0 = time.time()
        rows, total = cat.query(f, **kw)
        print(f"{label}: {total} results, {(time.time() - t0) * 1000:.0f} ms")
        return rows, total
    timed("all-field word", {"q": "גולדברג"})
    timed("multi-word", {"q": "משה כהן הלכה"})
    timed("first name only", {"q": "משה", "field": "first_name"})
    rows, total = timed("last name only", {"q": "כהן", "field": "last_name"})
    assert all(r["last_name"] == "כהן" for r in rows)
    timed("adv boxes", {"first_name": "משה", "last_name": "כהן", "subject": "הלכה"})
    timed("publisher+year", {"publisher": "פלדהיים", "pub_year": "1999"})
    rows, total = timed("exact shelf 101-א", {"shelf": "101-א"})
    assert all(r["shelf"] == 101 and r["shelf_sub"] == "א" for r in rows)
    r1, t1 = timed("shelf 101 (incl. splits)", {"shelf": "101"})
    assert all(r["shelf"] == 101 for r in r1)
    timed("shelf range+location", {"location": "אולם א", "shelf_from": "100", "shelf_to": "120"})
    timed("sort by author (page 500)", {"sort": "author"}, offset=10000)
    rows, _ = timed("sort by shelf", {"sort": "shelf"}, limit=3000)
    order = [(r["shelf"], r["shelf_sub"]) for r in rows]
    assert order == sorted(order), "shelf order"

    # פיצול מדף וסדר מיון
    for s in ("101", "101-א", "101 ב", "101ג"):
        cat.add(dict(title="בדיקת מדף " + s, shelf=s, location="ארכיון"))
    got, _ = cat.query({"q": "בדיקת מדף", "sort": "shelf"})
    assert [r["shelf_text"] for r in got] == ["101", "101-א", "101-ב", "101-ג"], got
    for bad in ("0", "1000", "abc", "101-אבגד", "-5"):
        try:
            cat.add(dict(title="x", shelf=bad))
            raise SystemExit("accepted bad shelf " + bad)
        except ValueError:
            pass
    assert cat.find_duplicate(dict(title="בדיקת מדף 101"))

    # CSV הלוך וחזור
    rows, _ = cat.query({}, None)
    data = cat.export_csv(rows)
    res = cat.import_csv(data, replace=True)
    assert res["imported"] == cat.count() == 50004, res
    assert cat.query({"shelf": "101-ב"})[1] > 0
    # CSV מגרסה 1 ("מצב גופני", בלי עמודות חדשות) ופסיק-נקודה
    old = "שם הספר;שם משפחה;מצב גופני;מדף\nספר ישן;כהן;טוב;7\n".encode("utf-8")
    assert cat.import_csv(old)["imported"] == 1
    assert cat.query({"q": "ספר ישן"})[0][0]["cond"] == "טוב"
    cat.rename_location("ארכיון", "ארכיון ראשי")
    assert cat.query({"q": "ארכיון ראשי"})[1] > 0
    cat.backup_to(os.path.join(tmp, "b.db"))
    cat.restore_from(os.path.join(tmp, "b.db"))
    assert cat.count() == 50005

    # מיגרציה מגרסה 1
    v1 = os.path.join(tmp, "v1.db")
    c = sqlite3.connect(v1)
    c.executescript("""CREATE TABLE books(id INTEGER PRIMARY KEY AUTOINCREMENT,title TEXT NOT NULL,
      first_name TEXT NOT NULL DEFAULT '',last_name TEXT NOT NULL DEFAULT '',volume TEXT NOT NULL DEFAULT '',
      subject TEXT NOT NULL DEFAULT '',content TEXT NOT NULL DEFAULT '',cond TEXT NOT NULL DEFAULT '',
      location TEXT NOT NULL DEFAULT '',shelf INTEGER,notes TEXT NOT NULL DEFAULT '',added TEXT,updated TEXT,
      title_norm TEXT NOT NULL DEFAULT '',author_norm TEXT NOT NULL DEFAULT '',search TEXT NOT NULL DEFAULT '');
      CREATE TABLE locations(name TEXT PRIMARY KEY,pos INTEGER NOT NULL DEFAULT 0);
      INSERT INTO books(title,first_name,last_name,shelf,location) VALUES('ספר מגרסה ראשונה','דוד','לוי',5,'אולם א');""")
    c.commit(); c.close()
    mig = Catalog(v1)
    assert mig.query({"q": "דוד", "field": "first_name"})[1] == 1
    assert mig.query({"shelf": "5"})[1] == 1
    mig.close()

    # בדיקת HTTP מקצה לקצה
    srv = make_server(cat, 0)
    port = srv.server_address[1]
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    base = f"http://127.0.0.1:{port}"

    def call(method, path, body=None, headers=None):
        req = urllib.request.Request(base + path, method=method, data=body, headers=headers or {})
        try:
            with urllib.request.urlopen(req) as r:
                return r.status, r.read()
        except urllib.error.HTTPError as e:
            return e.code, e.read()
    st, body = call("GET", "/")
    assert st == 200 and "קטלוג ספרים".encode() in body
    st, body = call("GET", "/api/search?q=" + urllib.request.quote("משה") + "&field=first_name&size=5")
    j = json.loads(body)
    assert st == 200 and len(j["rows"]) == 5 and j["total"] > 100
    payload = json.dumps(dict(title="ספר דרך HTTP", shelf="300-ד", location="מסדרון")).encode()
    st, body = call("POST", "/api/book", payload, {"Content-Type": "application/json"})
    assert st == 200, body
    st, body = call("POST", "/api/book", payload, {"Content-Type": "application/json"})
    assert st == 409
    st, body = call("POST", "/api/book", json.dumps(dict(title="x", shelf="9999")).encode())
    assert st == 400 and "מדף" in json.loads(body)["error"]
    st, body = call("GET", "/api/search?shelf=300-%D7%93")
    assert json.loads(body)["total"] == 1
    st, body = call("GET", "/api/export.csv?shelf=300")
    assert "300-ד".encode() in body
    st, _ = call("POST", "/api/book", payload, {"Origin": "http://evil.example"})
    assert st == 403, st
    st, _ = call("GET", "/api/meta", headers={"Host": "evil.example"})
    assert st == 403, st
    print("HTTP end-to-end OK")
    srv.shutdown()
    selftest_v3(tmp)
    selftest_generic(tmp)
    selftest_update()
    print("ALL TESTS PASSED")
    cat.close()
    shutil.rmtree(tmp, ignore_errors=True)
    return 0


def selftest_v3(tmp):
    """בדיקות לגרסה 3: מיקום לפי מדף, נספחים, Excel, מצב מנהל והרשאות, עדכון מקובץ py."""
    cat = Catalog(os.path.join(tmp, "v3.db"), profile=TEST_PROFILE)
    # --- מיקום לפי מדף ---
    for shelf, want in (("5", "אולם א"), ("399", "אולם א"), ("400", "אולם ב"), ("700", "אולם ב"),
                        ("950", "ארכיון"), ("250-פ", "מסדרון"), ("950פ", "מסדרון")):
        bid = cat.add(dict(title="מיקום " + shelf, shelf=shelf, location="משהו אחר"))
        assert cat.get(bid)["location"] == want, (shelf, cat.get(bid)["location"])
    bid = cat.add(dict(title="בלי כלל", shelf="800", location="מחסן"))
    assert cat.get(bid)["location"] == "מחסן"
    cat.rename_location("אולם א", "אולם א", {"shelf_from": "1", "shelf_to": "300", "letter": ""})
    cat.add_location("אולם", {"shelf_from": "301", "shelf_to": "399"})
    assert cat.apply_location_rules() == 1 and cat.query({"location": "אולם"})[1] == 1
    for bad in ({"shelf_from": "5"}, {"shelf_from": "9", "shelf_to": "3"}, {"shelf_from": "0", "shelf_to": "3"}):
        try:
            cat.add_location("רע", bad)
            raise SystemExit("accepted bad rule")
        except ValueError:
            pass
    # --- נספחים: מוצגים בתוך הספר הראשי ---
    main = cat.add(dict(title="אבני מלואים", last_name="הלר", shelf="277"))
    other = cat.add(dict(title="אבני מלואים", last_name="אחר", shelf="120"))
    a1 = cat.add(dict(title="ברכת שמעון", last_name="שניאורסון", shelf="277", label="א", annex_of="אבני מלואים"))
    a2 = cat.add(dict(title="גליונות ברוך טעם", shelf="277", label="א", annex_of="אבני מלואים"))
    lone = cat.add(dict(title="נספח יתום", annex_of="ספר שלא קיים"))
    assert cat.get(a1)["parent_id"] == main and cat.get(a2)["parent_id"] == main and other != main
    assert cat.get(lone)["parent_id"] is None
    rows, total = cat.query({"q": "ברכת שמעון"}, group=True)
    assert total == 1 and rows[0]["id"] == main and rows[0]["hit_self"] is False, rows
    assert [(a["id"], a["hit"]) for a in rows[0]["annexes"]] == [(a1, True), (a2, False)]
    rows, total = cat.query({"q": "ברכת שמעון"})
    assert total == 1 and rows[0]["id"] == a1                       # בלי קיבוץ: הנספח עצמו
    rows, total = cat.query({"q": "אבני מלואים", "type": "annex"}, group=True)
    assert total == 1 and rows[0]["id"] == main
    assert cat.query({"q": "277", "type": "shelf"})[1] == 3
    assert cat.query({"q": "הלר שניאורסון", "type": "author"})[1] == 0
    assert cat.query({"annex": "1"})[1] == 3 and cat.query({"q": "א", "type": "label"})[1] == 2
    cat.update(main, dict(title="אבני מילואים", last_name="הלר", shelf="277"))
    assert cat.get(a1)["annex_of"] == "אבני מילואים" and cat.query({"annex_of": "מילואים"})[1] == 2
    full = cat.get_full(main)
    assert len(full["annexes"]) == 2 and cat.get_full(a1)["parent"]["id"] == main
    # --- Excel ו-CSV הלוך וחזור, כולל קישור הנספחים לפי המספרים שבקובץ ---
    before = cat.count()
    rows, _ = cat.query({}, None)
    for blob in (cat.export_xlsx(rows), cat.export_csv(rows)):
        c2 = Catalog(os.path.join(tmp, "x%d.db" % len(blob)))
        res = c2.import_file(blob, "replace")
        assert res["imported"] == before and c2.count() == before, res
        r2, t2 = c2.query({"q": "ברכת שמעון"}, group=True)
        assert t2 == 1 and r2[0]["title"] == "אבני מילואים" and r2[0]["last_name"] == "הלר", r2
        assert c2.query({"annex": "1"})[1] == 3 and c2.query({"location": "מסדרון"})[1] == 2
        res = c2.import_file(blob, "update")
        assert res["imported"] == 0 and res["updated"] == before and c2.count() == before, res
        c2.close()
    sheet = read_xlsx(make_xlsx(["א", "ב"], [["טקסט <&> \"x\"", 7], ["", "שורה\nשנייה"]]))
    assert sheet == [["א", "ב"], ["טקסט <&> \"x\"", "7"], ["", "שורה\nשנייה"]], sheet
    assert cat.bulk_set([a1, a2], "cond", "תקין") == 2 and cat.get(a2)["cond"] == "תקין"
    assert cat.rename_value("cond", "תקין", "טוב מאוד") == 2 and cat.query({"cond": "טוב מאוד"})[1] == 2
    cat.delete([main])
    assert cat.get(a1)["parent_id"] is None and cat.get(a1)["annex_of"] == "אבני מילואים"
    # --- הגדרות ---
    cfg = cat.save_config({"texts": {"app_title": "ספריית הישיבה"}, "theme": {"font_size": 99, "colors": {"bg": "zzz"}},
                           "nonsense": 1})
    assert cfg["texts"]["app_title"] == "ספריית הישיבה" and cfg["theme"]["font_size"] == 24
    assert cfg["theme"]["colors"]["bg"] == THEME_PRESETS["parchment"]["colors"]["bg"] and "nonsense" not in cfg
    assert cfg["texts"]["tagline"] and Catalog(cat.path).cfg["texts"]["app_title"] == "ספריית הישיבה"
    try:
        cat.save_config({"search": {"types": []}})
        raise SystemExit("accepted no search types")
    except ValueError:
        pass
    # --- מצב מנהל והרשאות דרך השרת ---
    srv = make_server(cat, 0)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    base = f"http://127.0.0.1:{srv.server_address[1]}"

    def call(method, path, obj=None, tok="", raw=None):
        data = raw if raw is not None else (json.dumps(obj).encode() if obj is not None else None)
        req = urllib.request.Request(base + path, method=method, data=data, headers={"X-Token": tok} if tok else {})
        try:
            with urllib.request.urlopen(req) as r:
                body = r.read()
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read() or b"{}")
        return 200, (json.loads(body) if body[:1] in (b"{", b"[") else body)
    book = dict(title="ספר חדש", shelf="12")
    assert call("POST", "/api/book", book)[0] == 403                 # בלי מנהל: אין הוספה
    assert call("PUT", "/api/config", {"texts": {"app_title": "x"}})[0] == 403
    assert call("POST", "/api/import?mode=replace", raw=b"x")[0] == 403 and cat.count() == before - 1
    assert call("GET", "/api/backup")[0] == 403 and call("POST", "/api/admin/login", {"password": "1234"})[0] == 400
    assert call("POST", "/api/admin/setup", {"password": "12"})[0] == 400
    st, j = call("POST", "/api/admin/setup", {"password": "סוד1234"})
    assert st == 200 and j["token"]
    tok = j["token"]
    assert call("POST", "/api/admin/setup", {"password": "אחרת1"})[0] == 400     # כבר נקבעה סיסמה
    assert call("POST", "/api/book", book, tok)[0] == 200 and call("POST", "/api/book", book, "bad-token")[0] == 403
    st, j = call("PUT", "/api/config", {"perms": {"add": True}, "fields": {"notes": {"public": False}}}, tok)
    assert st == 200 and j["admin"] is True and j["cfg"]["perms"]["add"] is True
    st, j = call("POST", "/api/book", dict(title="ספר עם הערה", notes="סודי", shelf="13"))
    assert st == 200                                                 # המנהל התיר הוספה לכולם
    nid = j["id"]
    assert call("GET", f"/api/book?id={nid}")[1]["notes"] == "" and call("GET", f"/api/book?id={nid}", tok=tok)[1]["notes"] == "סודי"
    st, body = call("GET", "/api/export?fmt=csv")
    assert st == 200 and "סודי".encode() not in body and "ספר עם הערה".encode() in body
    st, body = call("GET", "/api/export?fmt=xlsx&cols=title,shelf&t=" + tok)
    assert st == 200 and read_xlsx(body)[0] == ["שם הספר", "מדף"]
    assert call("POST", "/api/export?fmt=xlsx")[1] == {"download": True}       # בלי חלון: הורדה רגילה
    st, j = call("GET", "/api/search?q=" + quote("ברכת שמעון"))
    assert st == 200 and j["grouped"] and j["total"] == 1
    ico = b"\x00\x00\x01\x00" + b"\x00" * 40
    assert call("POST", "/api/asset?name=icon", raw=b"not an icon", tok=tok)[0] == 400
    assert call("POST", "/api/asset?name=icon", raw=ico)[0] == 403
    st, j = call("POST", "/api/asset?name=icon", raw=ico, tok=tok)
    assert st == 200 and "icon" in j["assets"] and call("GET", "/favicon.ico")[1] == ico
    assert call("POST", "/api/admin/password", {"old": "לא נכון", "new": "חדשה12"}, tok)[0] == 400
    st, j = call("POST", "/api/admin/password", {"old": "סוד1234", "new": "חדשה12"}, tok)
    assert st == 200 and call("PUT", "/api/config", {}, tok)[0] == 403        # הכניסה הישנה בוטלה
    assert call("POST", "/api/admin/login", {"password": "חדשה12"})[0] == 200
    assert call("POST", "/api/admin/logout", {}, j["token"])[0] == 200
    assert call("PUT", "/api/config", {"texts": {"app_title": "x"}}, j["token"])[0] == 403
    srv.shutdown()
    # --- גיבוי ושחזור שומרים על ההגדרות והסיסמה ---
    bak = os.path.join(tmp, "old.db")
    Catalog(bak).close()
    cat.restore_from(bak, keep_settings=True)
    assert cat.count() == 0 and cat.check_password("חדשה12") and cat.cfg["texts"]["app_title"] == "ספריית הישיבה"
    cat.clear_password()
    assert not cat.has_password()
    cat.close()
    # --- עדכון מקובץ py: זיהוי גרסה מתוך הקובץ, התקנה, ודחיית קובץ פגום ---
    appdir, site = os.path.join(tmp, "pyapp"), os.path.join(tmp, "pyupd")
    os.makedirs(appdir)
    script = os.path.join(appdir, "book_catalog.py")
    with open(script, "w", encoding="utf-8") as f:
        f.write('APP_VERSION = "3.0"\n')
    restarts = []
    up = Updater(update_dir=site, version="3.0", script_path=script, frozen=False,
                 on_restart=lambda: restarts.append(1))

    def settle():
        t0 = time.time()
        while up.state not in ("idle", "restarting"):
            assert time.time() - t0 < 15
            time.sleep(0.02)
        return up.status()
    new = 'APP_VERSION = "3.1"\nprint("שלום")\n'.encode("utf-8")
    with open(os.path.join(site, "קטלוג חדש.py"), "wb") as f:
        f.write(new)
    with open(os.path.join(site, "old.py"), "w", encoding="utf-8") as f:
        f.write('APP_VERSION = "2.0"\n')
    up.check_async(True)
    s = settle()
    assert s["available"] and s["latest"] == "3.1" and s["can_install"] and s["kind"] == ".py", s
    assert up.apply_async()
    settle()
    time.sleep(0.1)
    with open(script, "rb") as f:
        assert f.read() == new and restarts == [1]
    up = Updater(update_dir=site, version="3.1", script_path=script, frozen=False, on_restart=lambda: restarts.append(1))
    assert up.publish_file("bad.py", b'APP_VERSION = "9.0"\ndef (:\n') == "9.0"
    up.check_async(True)
    assert settle()["available"]
    up.apply_async()
    s = settle()
    assert "תחביר" in s["install_error"] and len(restarts) == 1, s
    with open(script, "rb") as f:
        assert f.read() == new
    try:
        up.publish_file("x.exe", b"MZ")
        raise SystemExit("accepted exe for py app")
    except ValueError:
        pass
    print("Version 3 features OK")


def selftest_generic(tmp):
    """הגרסה הגנרית: בלי פרופיל אין שם ואין מיקומים; אשף ההגדרה; הטמעת פרופיל בקובץ התוכנה."""
    g = Catalog(os.path.join(tmp, "generic.db"))
    assert g.needs_setup() and g.locations() == [] and g.profile == {}
    assert g.cfg["texts"]["app_title"] == "קטלוג ספרים" and g.cfg["texts"]["tagline"] == ""
    srv = make_server(g, 0)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    base = f"http://127.0.0.1:{srv.server_address[1]}"

    def call(method, path, obj=None, tok=""):
        req = urllib.request.Request(base + path, method=method, headers={"X-Token": tok} if tok else {},
                                     data=json.dumps(obj).encode() if obj is not None else None)
        try:
            with urllib.request.urlopen(req) as r:
                return 200, json.loads(r.read())
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read() or b"{}")
    assert call("GET", "/api/boot")[1]["needs_setup"] is True
    books = starter_books()
    assert len(books) == 84 and all(b["title"] and b["volume"] for b in books)
    assert len({(b["title"], b["volume"]) for b in books}) == len(books)
    answers = {"name": "בית המדרש הגדול", "tagline": "ספרייה תורנית", "preset": "royal", "password": "abcd1", "starter": True,
               "locations": [{"name": "אולם ראשי", "shelf_from": "1", "shelf_to": "500"},
                             {"name": "מרתף", "letter": "מ"}, {"name": ""}]}
    bad = dict(answers, locations=[{"name": "רע", "shelf_from": "9", "shelf_to": "2"}])
    assert call("POST", "/api/admin/wizard", bad)[0] == 400 and g.needs_setup()
    st, j = call("POST", "/api/admin/wizard", answers)
    assert st == 200 and j["token"] and j["admin"] and not j["needs_setup"], j
    assert j["cfg"]["texts"]["app_title"] == "בית המדרש הגדול" and j["cfg"]["texts"]["tagline"] == "ספרייה תורנית"
    assert j["cfg"]["theme"]["colors"] == THEME_PRESETS["royal"]["colors"]
    assert j["defaults"]["texts"]["app_title"] == "בית המדרש הגדול"            # איפוס חוזר לפרופיל, לא לגנרי
    assert call("POST", "/api/admin/wizard", answers)[0] == 403                 # האשף רץ פעם אחת בלבד
    assert call("PUT", "/api/config", {"texts": {"footer": "x"}}, j["token"])[0] == 200
    assert g.locations() == ["אולם ראשי", "מרתף"] and g.check_password("abcd1")
    assert g.count() == 84 and g.query({"q": "בבא מציעא"})[1] == 1 and g.query({"q": "קארו", "type": "author"})[1] == 4
    g.delete([r["id"] for r in g.query({}, None)[0]])
    assert g.get(g.add(dict(title="א", shelf="12")))["location"] == "אולם ראשי"
    assert g.get(g.add(dict(title="ב", shelf="12-מ")))["location"] == "מרתף"
    assert g.get(g.add(dict(title="ג", shelf="700")))["location"] == ""
    srv.shutdown()
    g.close()
    g = Catalog(os.path.join(tmp, "generic.db"))                               # נשמר להפעלה הבאה
    assert g.cfg["texts"]["app_title"] == "בית המדרש הגדול" and not g.needs_setup()
    g.close()
    s2 = Catalog(os.path.join(tmp, "skip.db"))
    s2.apply_setup({"skip": True, "starter": True, "name": "לא אמור להישמר"}, "abcd1")
    assert not s2.needs_setup() and s2.profile == {} and not s2.has_password() and s2.count() == 0
    s3 = Catalog(os.path.join(tmp, "starter.db"), profile=dict(TEST_PROFILE, starter=True))
    assert s3.count() == 84 and not s3.needs_setup()
    s3.delete([r["id"] for r in s3.query({}, None)[0]])
    s3.close()
    s3 = Catalog(os.path.join(tmp, "starter.db"), profile=dict(TEST_PROFILE, starter=True))
    assert s3.count() == 0                                                       # ספרים שנמחקו לא חוזרים
    s3.close()
    s2.close()
    # --- פרופיל מוטמע בקובץ התוכנה ---
    with io.open(os.path.abspath(__file__), encoding="utf-8", newline="") as f:
        src = f.read()
    generic = embed_profile(src, None)
    custom = embed_profile(generic, TEST_PROFILE)
    compile(custom, "custom.py", "exec")
    assert custom != generic and embed_profile(custom, None) == generic
    got = json.loads(base64.b64decode(PROFILE_LINE.search(custom).group(1)).decode("utf-8"))
    assert got == TEST_PROFILE and PROFILE_LINE.search(generic).group(1) == ""
    cfg = merge_config(default_config(), profile_config(
        {"name": "ישיבה", "preset": "night", "conditions": ["חדש", "ישן"], "config": {"texts": {"app_title": "גובר"}}}))
    assert cfg["texts"]["app_title"] == "גובר" and cfg["texts"]["window_title"] == "ישיבה"
    assert cfg["theme"]["colors"]["bg"] == THEME_PRESETS["night"]["colors"]["bg"]
    assert [c["name"] for c in cfg["conditions"]] == ["חדש", "ישן"]
    try:
        embed_profile("print(1)", TEST_PROFILE)
        raise SystemExit("embedded into a foreign file")
    except ValueError:
        pass
    # --- עדכון לקובץ גנרי שומר על הפרופיל המוטמע ---
    cur, new = os.path.join(tmp, "cur.py"), os.path.join(tmp, "new.py")
    for path, text in ((cur, custom), (new, generic)):
        with io.open(path, "w", encoding="utf-8", newline="") as f:
            f.write(text)
    Updater._carry_profile(cur, new)
    with io.open(new, encoding="utf-8", newline="") as f:
        assert f.read() == custom
    print("Generic edition OK")


def selftest_update():
    """בדיקות למנגנון העדכונים (אופליין): השוואת גרסאות, אימות, החלפת קובץ, שחזור לגרסה קודמת, ו-API."""
    tmp = tempfile.mkdtemp()
    site = os.path.join(tmp, "updates")      # תיקיית העדכונים (נוצרת אוטומטית על ידי Updater)
    appdir = os.path.join(tmp, "app")
    os.makedirs(appdir)

    # --- השוואת גרסאות וסביבת הפעלה מחדש ---
    assert version_gt("1.10", "1.9") and version_gt("v2", "1.99.9") and version_gt("1.5.1", "1.5")
    assert not version_gt("1.5", "1.5.0") and not version_gt("1.4", "1.5")
    for bad in ("", "abc", None):
        try:
            parse_version(bad)
            raise SystemExit("accepted bad version")
        except ValueError:
            pass
    env = _restart_env({"_PYI_ARCHIVE_FILE": "a", "_PYI_APPLICATION_HOME_DIR": "b", "_MEIPASS2": "c",
                        "PATH": "p", "APPDATA": "d"})
    assert env == {"PATH": "p", "APPDATA": "d", "PYINSTALLER_RESET_ENVIRONMENT": "1"}, env

    payload = b"MZ" + os.urandom(400000)
    sha = hashlib.sha256(payload).hexdigest()
    fake = b"not an exe" * 1000

    def publish(**over):
        """כותב version.json בתיקיית העדכונים (כמו ש-build_release.py מכין)."""
        m = {"version": "9.9", "file": "BookCatalog-9.9.exe", "sha256": sha, "size": len(payload),
             "notes": ["תיקון א", "תיקון ב"]}
        m.update(over)
        with open(os.path.join(site, "version.json"), "w", encoding="utf-8") as f:
            json.dump(m, f, ensure_ascii=False)

    def wait(cond, what, timeout=15):
        t0 = time.time()
        while not cond():
            assert time.time() - t0 < timeout, "timeout: " + what
            time.sleep(0.05)

    exe = os.path.join(appdir, "Catalog.exe")
    OLD = b"MZ-old-version"

    def fresh():
        for n in os.listdir(appdir):
            os.remove(os.path.join(appdir, n))
        with open(exe, "wb") as f:
            f.write(OLD)
        calls = {"restart": 0, "backup": 0}

        def on_restart():
            calls["restart"] += 1

        def before():
            calls["backup"] += 1
        up = Updater(update_dir=site, version="1.5", exe_path=exe, frozen=True,
                     before_install=before, on_restart=on_restart)
        up.retry_delay = 0.01
        return up, calls

    def check(up):
        up.check_async(True)
        wait(lambda: up.state == "idle", "check")
        return up.status()

    def content():
        with open(exe, "rb") as f:
            return f.read()

    # --- התיקייה נוצרת, ובלי קבצים אין עדכון ואין שגיאה ---
    up, calls = fresh()
    assert os.path.isdir(site)
    s = check(up)
    assert s["enabled"] and s["dir"] == site and not s["available"] and not s["check_error"], s

    with open(os.path.join(site, "BookCatalog-9.9.exe"), "wb") as f:
        f.write(payload)
    with open(os.path.join(site, "notexe.exe"), "wb") as f:
        f.write(fake)

    # --- בדיקת גרסה ---
    publish()
    up, calls = fresh()
    s = check(up)
    assert s["available"] and s["latest"] == "9.9" and not s["check_error"], s
    assert s["notes"] == "תיקון א\nתיקון ב" and s["can_install"]
    publish(version="1.5")
    assert not check(fresh()[0])["available"]                    # אותה גרסה - אין עדכון
    publish(version="1.4")
    assert not check(fresh()[0])["available"]                    # גרסה ישנה יותר - אין עדכון
    for over, word in (({"sha256": "xyz"}, "sha256"), ({"file": "missing.exe"}, "לא נמצא"),
                       ({"file": "update.txt"}, "exe"), ({"version": "abc"}, "גרסה")):
        publish(**over)
        s = check(fresh()[0])
        assert not s["available"] and word in s["check_error"], (over, s)
    with open(os.path.join(site, "version.json"), "w", encoding="utf-8") as f:
        f.write("{ not json")
    s = check(fresh()[0])
    assert not s["available"] and "version.json" in s["check_error"], s
    publish(file="../../BookCatalog-9.9.exe")                    # נתיב בשם הקובץ: נחתך לשם בלבד
    up, _ = fresh()
    s = check(up)
    assert s["available"] and os.path.dirname(up.latest["path"]) == site, s
    off = Updater(update_dir="", version="1.5")
    assert off.check_async(True) is False and off.status()["enabled"] is False

    # --- התקנה מוצלחת: הקובץ מועתק, והמקור בתיקיית העדכונים נשאר שלם ---
    publish()
    up, calls = fresh()
    check(up)
    assert up.apply_async()
    wait(lambda: calls["restart"] == 1, "restart")
    assert content() == payload
    with open(exe + ".old", "rb") as f:
        assert f.read() == OLD
    assert not os.path.exists(exe + ".part") and calls["backup"] == 1
    assert up.status()["state"] == "restarting"
    with open(os.path.join(site, "BookCatalog-9.9.exe"), "rb") as f:
        assert f.read() == payload
    cleanup_update_leftovers(exe)
    wait(lambda: not os.path.exists(exe + ".old"), "cleanup .old")

    # --- כשלים: הקובץ הישן נשאר שלם ואין שאריות ---
    for over, word in (({"sha256": "0" * 64}, "אימות"), ({"size": len(payload) + 1}, "גודל"),
                       ({"file": "notexe.exe", "sha256": hashlib.sha256(fake).hexdigest(), "size": 0}, "הפעלה")):
        publish(**over)
        up, calls = fresh()
        check(up)
        up.apply_async()
        wait(lambda: up.state == "idle", "failed apply " + str(over))
        s = up.status()
        assert word in s["install_error"] and calls["restart"] == 0, (over, s)
        assert content() == OLD and os.listdir(appdir) == ["Catalog.exe"], os.listdir(appdir)

    # --- נכשלת ההחלפה בשלב השני: חוזרים לגרסה הקודמת ---
    publish()
    up, calls = fresh()
    check(up)
    real_replace = os.replace

    def flaky(a, b):
        if str(a).endswith(".part"):
            raise PermissionError("locked")
        return real_replace(a, b)
    os.replace = flaky
    try:
        up.apply_async()
        wait(lambda: up.state == "idle", "rollback")
    finally:
        os.replace = real_replace
    assert content() == OLD and os.listdir(appdir) == ["Catalog.exe"], os.listdir(appdir)
    assert "הרשאה" in up.status()["install_error"] and calls["restart"] == 0

    # --- הרצה מקובץ py (לא exe): בלי התקנה אוטומטית ---
    up = Updater(update_dir=site, version="1.5", frozen=False)
    s = check(up)
    assert s["available"] and not s["can_install"]
    up.apply_async()
    wait(lambda: up.state == "idle", "not frozen")
    assert up.status()["install_error"]

    # --- דרך ה-API של השרת, כולל הגנה מפני אתרים זרים ---
    tcat = Catalog(os.path.join(tmp, "u.db"))
    tcat.save_config({"perms": {"update": True}})
    up, calls = fresh()
    srv = make_server(tcat, 0, up)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    api_base = f"http://127.0.0.1:{srv.server_address[1]}"

    def call(method, path, headers=None):
        req = urllib.request.Request(api_base + path, method=method,
                                     data=b"{}" if method == "POST" else None, headers=headers or {})
        try:
            with urllib.request.urlopen(req) as r:
                return r.status, json.loads(r.read())
        except urllib.error.HTTPError as e:
            return e.code, e.read()
    st, j = call("GET", "/api/update/status")
    assert st == 200 and j["current"] == "1.5" and j["enabled"] and not j["available"]
    st, j = call("POST", "/api/update/apply")
    assert st == 200 and j["ok"] is False            # עדיין לא נבדק - אין עדכון זמין
    call("POST", "/api/update/check?force=1")
    wait(lambda: up.state == "idle", "api check")
    st, j = call("GET", "/api/update/status")
    assert j["available"] and j["latest"] == "9.9"
    st, _ = call("POST", "/api/update/apply", {"Origin": "http://evil.example"})
    assert st == 403 and calls["restart"] == 0       # אתר זר לא יכול להפעיל עדכון
    st, j = call("POST", "/api/update/apply")
    assert st == 200 and j["ok"] is True
    wait(lambda: calls["restart"] == 1, "api apply")
    assert content() == payload
    st, j = call("GET", "/api/meta")
    assert st == 200 and j["version"] == APP_VERSION
    # --- החלפת תיקיית העדכונים מתוך התוכנה (והיא נשמרת) ---
    global SETTINGS_PATH
    real_settings = SETTINGS_PATH
    SETTINGS_PATH = os.path.join(tmp, "settings.json")
    try:
        other = os.path.join(tmp, "other updates")
        up2, _ = fresh()
        up2.dir = site
        srv2 = make_server(tcat, 0, up2)
        threading.Thread(target=srv2.serve_forever, daemon=True).start()
        b2 = f"http://127.0.0.1:{srv2.server_address[1]}"

        def post(path, obj, headers=None):
            req = urllib.request.Request(b2 + path, method="POST", data=json.dumps(obj).encode(),
                                         headers=headers or {})
            try:
                with urllib.request.urlopen(req) as r:
                    return r.status, json.loads(r.read())
            except urllib.error.HTTPError as e:
                raw = e.read()
                return e.code, (json.loads(raw) if raw[:1] == b"{" else raw)
        st, j = post("/api/update/dir", {"dir": other})
        assert st == 200 and j["dir"] == os.path.abspath(other) and os.path.isdir(other), (st, j)
        assert load_update_dir() == os.path.abspath(other)               # נשמר להפעלות הבאות
        wait(lambda: up2.state == "idle", "dir check")
        assert not up2.status()["available"]                              # בתיקייה החדשה אין קבצים
        st, j = post("/api/update/dir", {"dir": os.path.join(site, "BookCatalog-9.9.exe")})
        assert st == 400, (st, j)                                         # קובץ במקום תיקייה
        st, _ = post("/api/update/dir", {"dir": site}, {"Origin": "http://evil.example"})
        assert st == 403 and up2.dir == os.path.abspath(other)
        st, j = post("/api/update/dir", {"dir": ""})                      # ריק = ברירת מחדל
        assert st == 200 and j["dir"] == UPDATE_DIR or j["dir"] == os.path.abspath(UPDATE_DIR), j
        assert load_update_dir() == UPDATE_DIR and "update_dir" not in _read_settings()
        st, j = post("/api/update/browse", {})                            # בלי חלון (בדיקה) - שגיאה מסודרת
        assert st == 400, (st, j)
        srv2.shutdown()
    finally:
        SETTINGS_PATH = real_settings
        shutil.rmtree(UPDATE_DIR, ignore_errors=True) if UPDATE_DIR.startswith(tmp) else None
    srv.shutdown()
    tcat.close()
    shutil.rmtree(tmp, ignore_errors=True)
    print("Update mechanism OK")


if __name__ == "__main__":
    main()
