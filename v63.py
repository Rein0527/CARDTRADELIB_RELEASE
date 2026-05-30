from __future__ import annotations

import base64
import csv
import hashlib
import hmac
import json
import mimetypes
import platform
import re
import shutil
import sys
import time
import uuid
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from html import unescape as html_unescape
from html.parser import HTMLParser
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import quote, urlencode, urljoin
from urllib.request import Request, urlopen

from PySide6.QtCore import Qt, QThread, QTimer, QUrl, Signal, QSize
from PySide6.QtGui import QDesktopServices, QPixmap, QIcon
from PySide6.QtWidgets import (
    QApplication,
    QAbstractItemView,
    QCheckBox,
    QComboBox,
    QDialog,
    QDialogButtonBox,
    QDoubleSpinBox,
    QProgressDialog,
    QFileDialog,
    QFormLayout,
    QGridLayout,
    QGroupBox,
    QHBoxLayout,
    QHeaderView,
    QInputDialog,
    QLabel,
    QLineEdit,
    QListWidget,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QScrollArea,
    QSpinBox,
    QTableWidget,
    QTableWidgetItem,
    QTabWidget,
    QTreeWidget,
    QTreeWidgetItem,
    QTextEdit,
    QVBoxLayout,
    QWidget,
)


def setup_stable_table_columns(table: QTableWidget, widths: dict[int, int]) -> None:
    header = table.horizontalHeader()
    header.setStretchLastSection(False)
    header.setCascadingSectionResizes(False)
    header.setSectionsMovable(False)
    for col in range(table.columnCount()):
        header.setSectionResizeMode(col, QHeaderView.Interactive)
        if col in widths:
            table.setColumnWidth(col, widths[col])
    table.setHorizontalScrollMode(QAbstractItemView.ScrollPerPixel)


def checkable_row_item(text: str, record_id: str, checked: bool = False) -> QTableWidgetItem:
    item = QTableWidgetItem(text)
    item.setData(Qt.UserRole, record_id)
    item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
    item.setCheckState(Qt.CheckState.Checked if checked else Qt.CheckState.Unchecked)
    return item


def checked_record_ids_from_table(table: QTableWidget) -> list[str]:
    ids: list[str] = []
    for row in range(table.rowCount()):
        item = table.item(row, 0)
        if item and item.checkState() == Qt.CheckState.Checked:
            record_id = clean_text(str(item.data(Qt.UserRole)))
            if record_id:
                ids.append(record_id)
    return ids


APP_TITLE = "卡片庫存紀錄系統"
DEFAULT_CATEGORIES = ["球員卡(籃)", "球員卡(其他)", "MTG", "寶可夢", "GA", "迪士尼", "海賊王"]
DEFAULT_BUY_METHODS = ["團拆", "自己開", "尬包", "代售"]



SCRYFALL_SETS_API_URL = "https://api.scryfall.com/sets"
SCRYFALL_SEARCH_URL = "https://api.scryfall.com/cards/search"
SCRYFALL_SITE_SETS_URL = "https://scryfall.com/sets?lang=zht"
SCRYFALL_SITE_SEARCH_URL = "https://scryfall.com/search"
SCRYFALL_PAGE_SIZE = 20
SCRYFALL_MAX_CARDS = 500
SCRYFALL_FORMATS = ["", "Commander", "Standard", "Pioneer", "Modern", "Legacy", "Vintage", "Pauper", "Brawl"]
SCRYFALL_COLORS = ["", "White", "Blue", "Black", "Red", "Green", "Colorless", "Multicolor"]
SCRYFALL_RARITIES = ["", "Mythic", "Rare", "Uncommon", "Common", "Special", "Bonus"]
SCRYFALL_TYPES = ["", "Artifact", "Battle", "Creature", "Enchantment", "Instant", "Kindred", "Land", "Legendary", "Planeswalker", "Sorcery"]
SCRYFALL_LANGUAGES = [
    ("全部語言", ""),
    ("English", "en"),
    ("繁體中文", "zht"),
    ("簡體中文", "zhs"),
    ("日本語", "ja"),
    ("한국어", "ko"),
    ("Español", "es"),
    ("Français", "fr"),
    ("Deutsch", "de"),
    ("Italiano", "it"),
    ("Português", "pt"),
    ("Русский", "ru"),
]

# 保留舊變數名稱讓下方 UI 程式可以最小幅度沿用；實際來源已改成 Scryfall。
CARDKINGDOM_PAGE_SIZE = SCRYFALL_PAGE_SIZE
CARDKINGDOM_FORMATS = SCRYFALL_FORMATS
CARDKINGDOM_COLORS = SCRYFALL_COLORS
CARDKINGDOM_RARITIES = SCRYFALL_RARITIES
CARDKINGDOM_TYPES = SCRYFALL_TYPES


def clean_text(value: str) -> str:
    return re.sub(r"\s+", " ", str(value or "")).strip()


def http_json(url: str, timeout: int = 45) -> Any:
    request = Request(
        url,
        headers={
            "User-Agent": "CardInventory/1.0 (local desktop inventory app; contact: local-user)",
            "Accept": "application/json,*/*;q=0.8",
        },
    )
    with urlopen(request, timeout=timeout) as response:
        charset = response.headers.get_content_charset() or "utf-8"
        return json.loads(response.read().decode(charset, errors="replace"))


def get_any(data: dict[str, Any], *names: str, default: Any = "") -> Any:
    for name in names:
        if name in data and data[name] not in (None, ""):
            return data[name]
    return default


def to_float(value: Any) -> float:
    try:
        if value is None or value == "":
            return 0.0
        return float(str(value).replace("$", "").replace(",", ""))
    except Exception:
        return 0.0


def to_int(value: Any) -> int:
    try:
        if value is None or value == "":
            return 0
        return int(float(str(value).replace(",", "")))
    except Exception:
        return 0


def scryfall_sets_cache_path() -> Path:
    return CONFIG_DIR / "scryfall_sets_cache.json"


def scryfall_custom_sets_path() -> Path:
    return CONFIG_DIR / "scryfall_custom_sets.json"


def normalize_scryfall_set(raw: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": str(raw.get("id", "")).strip(),
        "code": clean_text(str(raw.get("code", ""))).lower(),
        "name": clean_text(str(raw.get("name", ""))),
        "set_type": clean_text(str(raw.get("set_type", ""))),
        "card_count": to_int(raw.get("card_count", 0)),
        "released_at": clean_text(str(raw.get("released_at", ""))),
        "scryfall_uri": clean_text(str(raw.get("scryfall_uri", ""))),
        "uri": clean_text(str(raw.get("uri", ""))),
        "icon_svg_uri": clean_text(str(raw.get("icon_svg_uri", ""))),
        "parent_set_code": clean_text(str(raw.get("parent_set_code", ""))).lower(),
        "block": clean_text(str(raw.get("block", ""))),
        "block_code": clean_text(str(raw.get("block_code", ""))).lower(),
        "custom": bool(raw.get("custom", False)),
    }


def make_custom_scryfall_set(code: str, name: str) -> dict[str, Any]:
    code = clean_text(code).lower()
    name = clean_text(name) or code.upper()
    return {
        "id": f"custom-{code}",
        "code": code,
        "name": name,
        "set_type": "custom",
        "card_count": 0,
        "released_at": "",
        "scryfall_uri": f"https://scryfall.com/sets/{code}",
        "uri": "",
        "icon_svg_uri": "",
        "parent_set_code": "",
        "block": "",
        "block_code": "",
        "custom": True,
    }


def load_custom_scryfall_sets() -> list[dict[str, Any]]:
    path = scryfall_custom_sets_path()
    if not path.exists():
        return []
    try:
        with path.open("r", encoding="utf-8") as f:
            payload = json.load(f)
    except Exception:
        return []

    raw_items = payload.get("data", payload) if isinstance(payload, dict) else payload
    custom_sets: list[dict[str, Any]] = []
    if isinstance(raw_items, list):
        for raw in raw_items:
            if isinstance(raw, dict):
                item = normalize_scryfall_set({**raw, "custom": True})
                if item["code"] and item["name"]:
                    custom_sets.append(item)
    return custom_sets


def save_custom_scryfall_sets(custom_sets: list[dict[str, Any]]) -> None:
    cleaned: dict[str, dict[str, Any]] = {}
    for raw in custom_sets:
        item = normalize_scryfall_set({**raw, "custom": True})
        if item["code"] and item["name"]:
            cleaned[item["code"]] = item
    payload = {
        "updated_at": now_text(),
        "data": sorted(cleaned.values(), key=lambda x: (str(x.get("name", "")).lower(), str(x.get("code", "")))),
    }
    path = scryfall_custom_sets_path()
    tmp = path.with_suffix(".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
    tmp.replace(path)


def add_custom_scryfall_set(code: str, name: str) -> dict[str, Any]:
    item = make_custom_scryfall_set(code, name)
    custom_sets = [s for s in load_custom_scryfall_sets() if s.get("code") != item["code"]]
    custom_sets.append(item)
    save_custom_scryfall_sets(custom_sets)
    return item


def merge_scryfall_sets(official_sets: list[dict[str, Any]], custom_sets: list[dict[str, Any]]) -> list[dict[str, Any]]:
    merged: dict[str, dict[str, Any]] = {}
    for raw in official_sets:
        item = normalize_scryfall_set(raw)
        if item["code"] and item["name"]:
            merged[item["code"]] = item
    for raw in custom_sets:
        item = normalize_scryfall_set({**raw, "custom": True})
        if item["code"] and item["name"] and item["code"] not in merged:
            merged[item["code"]] = item
    return list(merged.values())


def scryfall_set_label(item: dict[str, Any]) -> str:
    name = clean_text(str(item.get("name", "")))
    code = clean_text(str(item.get("code", ""))).upper()
    released_at = clean_text(str(item.get("released_at", "")))
    custom = bool(item.get("custom", False))
    custom_text = "｜自訂" if custom else ""
    date_text = f"｜{released_at}" if released_at else ""
    return f"{name} ({code}){date_text}{custom_text}" if code else name


def load_scryfall_sets_local_only() -> tuple[list[dict[str, Any]], dict[str, Any], str]:
    path = scryfall_sets_cache_path()
    official_sets: list[dict[str, Any]] = []
    downloaded_at = ""
    if path.exists():
        try:
            with path.open("r", encoding="utf-8") as f:
                cache = json.load(f)
            downloaded_at = str(cache.get("downloaded_at", "")) if isinstance(cache, dict) else ""
            data = cache.get("data", []) if isinstance(cache, dict) else []
            if isinstance(data, list):
                for raw in data:
                    if isinstance(raw, dict):
                        item = normalize_scryfall_set(raw)
                        if item["code"] and item["name"]:
                            official_sets.append(item)
        except Exception:
            official_sets = []
            downloaded_at = ""

    custom_sets = load_custom_scryfall_sets()
    merged_sets = merge_scryfall_sets(official_sets, custom_sets)
    meta = {
        "downloaded_at": downloaded_at,
        "total_sets": len(merged_sets),
        "official_sets": len(official_sets),
        "custom_sets": len(custom_sets),
    }
    return merged_sets, meta, "cache" if official_sets else "custom"


def download_scryfall_sets() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    payload = http_json(SCRYFALL_SETS_API_URL, timeout=45)
    raw_sets = payload.get("data", []) if isinstance(payload, dict) else []
    official_sets: list[dict[str, Any]] = []
    if isinstance(raw_sets, list):
        for raw in raw_sets:
            if isinstance(raw, dict):
                item = normalize_scryfall_set(raw)
                if item["code"] and item["name"]:
                    official_sets.append(item)

    custom_sets = load_custom_scryfall_sets()
    merged_sets = merge_scryfall_sets(official_sets, custom_sets)
    cache = {
        "downloaded_at": now_text(),
        "source_url": SCRYFALL_SETS_API_URL,
        "total_sets": len(merged_sets),
        "official_sets": len(official_sets),
        "custom_sets": len(custom_sets),
        "data": official_sets,
    }
    path = scryfall_sets_cache_path()
    tmp = path.with_suffix(".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(cache, f, ensure_ascii=False, indent=2)
    tmp.replace(path)
    return merged_sets, {"downloaded_at": cache["downloaded_at"], "total_sets": len(merged_sets), "official_sets": len(official_sets), "custom_sets": len(custom_sets)}


def load_scryfall_sets_cache() -> tuple[list[dict[str, Any]], dict[str, Any], str]:
    path = scryfall_sets_cache_path()
    if not path.exists():
        custom_sets = load_custom_scryfall_sets()
        if custom_sets:
            sets, meta, source = load_scryfall_sets_local_only()
            return sets, meta, source
        sets, meta = download_scryfall_sets()
        return sets, meta, "downloaded"

    sets, meta, source = load_scryfall_sets_local_only()
    return sets, meta, source


def load_or_refresh_scryfall_sets_cache(refresh: bool) -> tuple[list[dict[str, Any]], dict[str, Any], str]:
    if refresh:
        sets, meta = download_scryfall_sets()
        return sets, meta, "downloaded"
    return load_scryfall_sets_cache()


def looks_like_scryfall_set_code(value: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9]{2,6}", value.strip()))


def find_scryfall_set_codes(edition: str, sets: list[dict[str, Any]], limit: int = 12) -> list[str]:
    value = clean_text(edition).lower()
    if not value:
        return []

    code_matches = [str(s.get("code", "")).lower() for s in sets if str(s.get("code", "")).lower() == value]
    if code_matches:
        return sorted(set(code_matches))[:limit]

    exact_name = [str(s.get("code", "")).lower() for s in sets if str(s.get("name", "")).lower() == value]
    if exact_name:
        return sorted(set(exact_name))[:limit]

    contains_name = [str(s.get("code", "")).lower() for s in sets if value in str(s.get("name", "")).lower()]
    if contains_name:
        return sorted(set(contains_name))[:limit]

    if looks_like_scryfall_set_code(value):
        return [value]
    return []


def safe_scryfall_text(value: str) -> str:
    return value.replace('"', '\\"').strip()


def build_scryfall_query(filters: dict[str, str], sets: list[dict[str, Any]] | None = None) -> str:
    sets = sets or []
    parts: list[str] = ["game:paper"]
    name = filters.get("name", "").strip()
    edition = filters.get("edition", "").strip()
    set_code = filters.get("set_code", "").strip().lower()
    fmt = filters.get("format", "").strip().lower()
    color = filters.get("color", "").strip()
    rarity = filters.get("rarity", "").strip().lower()
    card_type = filters.get("type", "").strip().lower()
    language = filters.get("language", "").strip().lower()

    if name:
        parts.append(f'name:"{safe_scryfall_text(name)}"')

    if set_code:
        parts.append(f"set:{set_code}")
    elif edition:
        codes = find_scryfall_set_codes(edition, sets)
        if len(codes) == 1:
            parts.append(f"set:{codes[0]}")
        elif len(codes) > 1:
            parts.append("(" + " or ".join(f"set:{code}" for code in codes) + ")")

    format_map = {
        "commander": "f:commander",
        "standard": "f:standard",
        "pioneer": "f:pioneer",
        "modern": "f:modern",
        "legacy": "f:legacy",
        "vintage": "f:vintage",
        "pauper": "f:pauper",
        "brawl": "f:brawl",
    }
    if fmt in format_map:
        parts.append(format_map[fmt])

    color_map = {
        "White": "c:w",
        "Blue": "c:u",
        "Black": "c:b",
        "Red": "c:r",
        "Green": "c:g",
        "Colorless": "c=0",
        "Multicolor": "c>=2",
    }
    if color in color_map:
        parts.append(color_map[color])

    rarity_map = {
        "mythic": "r:mythic",
        "rare": "r:rare",
        "uncommon": "r:uncommon",
        "common": "r:common",
        "special": "r:special",
        "bonus": "r:bonus",
    }
    if rarity in rarity_map:
        parts.append(rarity_map[rarity])

    if card_type:
        parts.append(f"t:{card_type}")

    if language:
        parts.append(f"lang:{language}")

    return " ".join(parts)


def build_scryfall_site_url(filters: dict[str, str], sets: list[dict[str, Any]] | None = None) -> str:
    query = build_scryfall_query(filters, sets or [])
    if query == "game:paper":
        return SCRYFALL_SITE_SETS_URL
    site_lang = filters.get("language", "").strip().lower() or "zht"
    params = {"as": "grid", "order": "name", "lang": site_lang, "q": query}
    return f"{SCRYFALL_SITE_SEARCH_URL}?{urlencode(params)}"


# 保留舊函式名稱，讓 UI method 不需要大幅重命名。
def build_cardkingdom_url(filters: dict[str, str]) -> str:
    try:
        sets, _, _ = load_scryfall_sets_local_only()
    except Exception:
        sets = []
    return build_scryfall_site_url(filters, sets)


def card_image_url_from_scryfall(card: dict[str, Any]) -> str:
    image_uris = card.get("image_uris") if isinstance(card.get("image_uris"), dict) else {}
    for key in ["normal", "large", "small", "png"]:
        value = str(image_uris.get(key, ""))
        if value:
            return value
    faces = card.get("card_faces")
    if isinstance(faces, list):
        for face in faces:
            if not isinstance(face, dict):
                continue
            image_uris = face.get("image_uris") if isinstance(face.get("image_uris"), dict) else {}
            for key in ["normal", "large", "small", "png"]:
                value = str(image_uris.get(key, ""))
                if value:
                    return value
    return ""


def oracle_text_from_scryfall(card: dict[str, Any]) -> str:
    printed_text = clean_text(str(card.get("printed_text", "")))
    oracle = clean_text(str(card.get("oracle_text", "")))
    if printed_text and oracle and printed_text != oracle:
        return f"{printed_text}\n\nOracle: {oracle}"
    if printed_text:
        return printed_text
    if oracle:
        return oracle

    faces = card.get("card_faces")
    if isinstance(faces, list):
        parts = []
        for face in faces:
            if not isinstance(face, dict):
                continue
            face_name = clean_text(str(face.get("printed_name", "") or face.get("name", "")))
            face_text = clean_text(str(face.get("printed_text", "") or face.get("oracle_text", "")))
            if face_name and face_text:
                parts.append(f"{face_name}: {face_text}")
            elif face_text:
                parts.append(face_text)
        return " // ".join(parts)
    return ""


def colors_text_from_scryfall(card: dict[str, Any]) -> str:
    colors = card.get("colors")
    if not isinstance(colors, list) or not colors:
        faces = card.get("card_faces")
        collected: list[str] = []
        if isinstance(faces, list):
            for face in faces:
                if isinstance(face, dict) and isinstance(face.get("colors"), list):
                    for color in face.get("colors", []):
                        if color not in collected:
                            collected.append(str(color))
        colors = collected
    if not colors:
        return "Colorless"
    return "".join(str(c) for c in colors)


def prices_summary_from_scryfall(card: dict[str, Any]) -> str:
    prices = card.get("prices") if isinstance(card.get("prices"), dict) else {}
    parts: list[str] = []
    for label, key, prefix in [
        ("USD", "usd", "$"),
        ("USD Foil", "usd_foil", "$"),
        ("USD Etched", "usd_etched", "$"),
        ("EUR", "eur", "€"),
        ("EUR Foil", "eur_foil", "€"),
        ("MTGO", "tix", ""),
    ]:
        value = prices.get(key)
        if value not in (None, ""):
            try:
                formatted = f"{prefix}{float(value):,.2f}" if prefix else f"{float(value):,.2f}"
            except Exception:
                formatted = f"{prefix}{value}"
            parts.append(f"{label} {formatted}")
    return " | ".join(parts) if parts else "無價格資料"


def legalities_summary_from_scryfall(card: dict[str, Any]) -> str:
    legalities = card.get("legalities") if isinstance(card.get("legalities"), dict) else {}
    formats = ["standard", "pioneer", "modern", "commander", "legacy", "vintage", "pauper"]
    legal = [fmt for fmt in formats if str(legalities.get(fmt, "")).lower() == "legal"]
    return ", ".join(legal) if legal else "-"


def scryfall_language_label(code: str) -> str:
    code = clean_text(code).lower()
    for label, lang_code in SCRYFALL_LANGUAGES:
        if lang_code == code:
            return f"{label} ({code})" if code else label
    return code or "-"


def normalize_scryfall_card(card: dict[str, Any]) -> dict[str, Any]:
    printed_name = clean_text(str(card.get("printed_name", "")))
    english_name = clean_text(str(card.get("name", "")))
    display_name = printed_name or english_name
    if printed_name and english_name and printed_name != english_name:
        display_name = f"{printed_name} / {english_name}"

    return {
        "name": display_name,
        "english_name": english_name,
        "printed_name": printed_name,
        "edition": clean_text(str(card.get("set_name", ""))),
        "set_code": clean_text(str(card.get("set", ""))).upper(),
        "rarity": clean_text(str(card.get("rarity", ""))).title(),
        "collector": clean_text(str(card.get("collector_number", ""))),
        "type": clean_text(str(card.get("printed_type_line", "") or card.get("type_line", ""))),
        "oracle_type": clean_text(str(card.get("type_line", ""))),
        "colors": colors_text_from_scryfall(card),
        "price": prices_summary_from_scryfall(card),
        "text": oracle_text_from_scryfall(card),
        "url": clean_text(str(card.get("scryfall_uri", ""))),
        "image_url": card_image_url_from_scryfall(card),
        "source_url": clean_text(str(card.get("uri", ""))),
        "scryfall_id": clean_text(str(card.get("id", ""))),
        "lang": clean_text(str(card.get("lang", ""))),
        "lang_label": scryfall_language_label(str(card.get("lang", ""))),
        "released_at": clean_text(str(card.get("released_at", ""))),
        "layout": clean_text(str(card.get("layout", ""))),
        "legalities": legalities_summary_from_scryfall(card),
    }


def search_scryfall_cards(filters: dict[str, str], refresh_cache: bool = False, max_cards: int = SCRYFALL_MAX_CARDS) -> dict[str, Any]:
    sets, sets_meta, sets_source = load_or_refresh_scryfall_sets_cache(refresh_cache)
    query = build_scryfall_query(filters, sets)
    web_url = build_scryfall_site_url(filters, sets)

    params = {
        "q": query,
        "unique": "prints",
        "order": "name",
        "include_extras": "false",
        "include_multilingual": "true",
        "include_variations": "true",
    }
    url = f"{SCRYFALL_SEARCH_URL}?{urlencode(params)}"
    api_first_url = url
    results: list[dict[str, Any]] = []
    total_cards = 0
    truncated = False

    while url and len(results) < max_cards:
        try:
            payload = http_json(url, timeout=60)
        except HTTPError as exc:
            if exc.code == 404:
                # Scryfall /cards/search 使用 404 表示查無符合條件的卡，這不是程式錯誤。
                break
            raise
        if not isinstance(payload, dict):
            break
        if not total_cards:
            total_cards = to_int(payload.get("total_cards", 0))
        for raw in payload.get("data", []):
            if not isinstance(raw, dict):
                continue
            results.append(normalize_scryfall_card(raw))
            if len(results) >= max_cards:
                truncated = True
                break
        if not payload.get("has_more") or len(results) >= max_cards:
            truncated = bool(payload.get("has_more")) or truncated
            break
        url = str(payload.get("next_page", ""))
        # Scryfall API 文件建議限制請求頻率，這裡保守放慢連續分頁請求。
        time.sleep(0.55)

    return {
        "results": results,
        "total_cards": total_cards or len(results),
        "returned_cards": len(results),
        "truncated": truncated,
        "query": query,
        "sets_count": len(sets),
        "sets_meta": sets_meta,
        "sets_source": sets_source,
        "api_url": api_first_url,
        "web_url": web_url,
    }


# 保留舊函式名稱，實際上已改查 Scryfall。
def search_cardkingdom_pricelist(filters: dict[str, str], refresh_cache: bool = False) -> dict[str, Any]:
    return search_scryfall_cards(filters, refresh_cache)


class ScryfallSearchWorker(QThread):
    completed = Signal(object, str, str)

    def __init__(self, filters: dict[str, str], refresh_cache: bool = False, parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.filters = dict(filters)
        self.refresh_cache = refresh_cache

    def run(self) -> None:
        try:
            payload = search_scryfall_cards(self.filters, self.refresh_cache)
            self.completed.emit(payload, "", str(payload.get("web_url", "")))
        except Exception as exc:
            self.completed.emit({"results": []}, str(exc), build_cardkingdom_url(self.filters))

def app_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


BASE_DIR = app_dir()
CONFIG_DIR = BASE_DIR / "config"
CONFIG_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = CONFIG_DIR / "card_inventory.json"
LEGACY_DB_PATH = BASE_DIR / "card_inventory.json"
RUTEN_SECRET_PATH = CONFIG_DIR / "ruten_api_secrets.json"
RUTEN_BATCH_FAILURE_PATH = CONFIG_DIR / "ruten_last_batch_failures.json"
RUTEN_OPERATION_LOG_PATH = CONFIG_DIR / "ruten_operation_log.json"
LICENSE_STATE_PATH = CONFIG_DIR / "license_state.json"
LICENSE_SERVER_CONFIG_PATH = CONFIG_DIR / "license_server.json"
IMAGE_DIR = BASE_DIR / "card_images"

LICENSE_APP_ID = "CARDTRADELIB"
LICENSE_FORMAT_PREFIX = "CARDTRADELIB-LIC.v1"
LICENSE_OFFLINE_GRACE_HOURS = 24
LICENSE_API_VERSION = "v63"
LICENSE_STATE_HMAC_SECRET = "CARDTRADELIB-v63-local-state-signature-2026-05-30"
LICENSE_PUBLIC_E = 65537
LICENSE_PUBLIC_N = int(
    "a85dca9e58c7e414fc8e2a7ea168b054640b16697879524af07ecb6ab3ce6de6cc53edc082fb04b14ebf83a9d198a3852f4b0ec9d0a54edad16c8677262c29d4a141d075f0556d8fcac2c066f0b09e9fe01173a6ec15c036cba1303768bde5555b4346f238ae3c18dcfb370c124cb6f1a9128597052a5e628a1d060dcc7a5de871d97ea9c11f3e8f265bffdae30118302c356cd66ecc7d865fe14ed8e3a36a97186c388cc0b5876927611f9397fcbc2faeb006deb7a3ccc9c5950f1b55a5b1fee37598d661487c859aa69c98f0f77c4c9a2b5bd29264aef17abd4c55cc7f27001f1fc037a9d2baa68f2bb1cc37ebb5016d1211cfd0dad59e9411471e5b31df87",
    16,
)
LICENSE_SHA256_DER_PREFIX = bytes.fromhex("3031300d060960864801650304020105000420")
NETWORK_TIME_URLS = [
    "https://www.google.com/generate_204",
    "https://www.cloudflare.com/",
    "https://www.microsoft.com/",
]


def now_text() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def money(value: float) -> str:
    return f"{float(value):,.0f}"


def percent(value: float) -> str:
    return f"{value:.2f}%"


def b64url_encode(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).decode("ascii").rstrip("=")


def b64url_decode(text: str) -> bytes:
    value = clean_text(str(text))
    value += "=" * ((4 - len(value) % 4) % 4)
    return base64.urlsafe_b64decode(value.encode("ascii"))


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def iso_utc(dt: datetime) -> str:
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_utc_datetime(value: Any) -> datetime | None:
    text = clean_text(str(value))
    if not text:
        return None
    try:
        if text.endswith("Z"):
            text = text[:-1] + "+00:00"
        dt = datetime.fromisoformat(text)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except Exception:
        return None


def machine_id_hash() -> str:
    raw = "|".join([
        platform.node(),
        sys.platform,
        platform.machine(),
        str(uuid.getnode()),
    ])
    return hashlib.sha256(raw.encode("utf-8", errors="ignore")).hexdigest()


def mask_license_key(key: str) -> str:
    cleaned = normalize_license_key(key)
    if len(cleaned) <= 24:
        return cleaned[:8] + "..." if cleaned else ""
    return cleaned[:22] + "..." + cleaned[-10:]


def normalize_license_key(key: str) -> str:
    return clean_text(str(key)).replace("\n", "").replace("\r", "").replace(" ", "")

def license_key_hash_value(key: str) -> str:
    return hashlib.sha256(normalize_license_key(key).encode("utf-8")).hexdigest()


def load_license_server_settings() -> dict[str, Any]:
    default = {"server_url": ""}
    if not LICENSE_SERVER_CONFIG_PATH.exists():
        return default
    try:
        with LICENSE_SERVER_CONFIG_PATH.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
        if isinstance(data, dict):
            default.update(data)
    except Exception:
        pass
    default["server_url"] = clean_text(str(default.get("server_url", ""))).rstrip("/")
    return default


def save_license_server_settings(settings: dict[str, Any]) -> None:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    data = {"server_url": clean_text(str(settings.get("server_url", ""))).rstrip("/")}
    with LICENSE_SERVER_CONFIG_PATH.open("w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, indent=2)


def license_state_signature_data(state: dict[str, Any]) -> str:
    fields = {
        "license_key_hash": state.get("license_key_hash", ""),
        "license_type": state.get("license_type", ""),
        "days": state.get("days", ""),
        "machine_id": state.get("machine_id", ""),
        "activated_at": state.get("activated_at", ""),
        "expires_at": state.get("expires_at", ""),
        "last_server_check_at": state.get("last_server_check_at", ""),
        "status": state.get("status", ""),
    }
    payload = state.get("license_payload") if isinstance(state.get("license_payload"), dict) else {}
    fields["license_id"] = payload.get("license_id", state.get("license_id", ""))
    fields["customer"] = payload.get("customer", "")
    return json.dumps(fields, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def sign_license_state(state: dict[str, Any]) -> str:
    return hmac.new(
        LICENSE_STATE_HMAC_SECRET.encode("utf-8"),
        license_state_signature_data(state).encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()


def attach_license_state_signature(state: dict[str, Any]) -> dict[str, Any]:
    if isinstance(state, dict):
        state["state_signature"] = sign_license_state(state)
    return state


def verify_license_state_signature(state: dict[str, Any]) -> bool:
    if not isinstance(state, dict) or not state:
        return False
    signature = clean_text(str(state.get("state_signature", "")))
    if not signature:
        return False
    expected = sign_license_state({k: v for k, v in state.items() if k != "state_signature"})
    return hmac.compare_digest(signature, expected)


def call_license_server(action: str, payload: dict[str, Any], timeout: int = 12) -> tuple[bool, str, dict[str, Any]]:
    settings = load_license_server_settings()
    server_url = clean_text(str(settings.get("server_url", ""))).rstrip("/")
    if not server_url:
        return False, "尚未設定授權伺服器網址。請先在『啟用/關於』填入 Google Apps Script Web App URL。", {}
    action_name = action.lstrip("/")
    if "script.google.com/macros/" in server_url and "/exec" in server_url:
        sep = "&" if "?" in server_url else "?"
        url = f"{server_url}{sep}action={quote(action_name)}"
    else:
        url = f"{server_url}/{action_name}"
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    try:
        request = Request(
            url,
            data=body,
            headers={"Content-Type": "application/json", "User-Agent": "CardTradeLib-License/1.0"},
            method="POST",
        )
        with urlopen(request, timeout=timeout) as response:
            raw = response.read().decode("utf-8", errors="replace")
        data = json.loads(raw) if raw.strip() else {}
        if not isinstance(data, dict):
            return False, "授權伺服器回應格式錯誤。", {}
        if bool(data.get("ok")):
            return True, clean_text(str(data.get("message", "授權伺服器驗證成功。"))), data
        return False, clean_text(str(data.get("message", "授權伺服器拒絕此授權。"))), data
    except HTTPError as exc:
        try:
            raw = exc.read().decode("utf-8", errors="replace")
            data = json.loads(raw) if raw.strip() else {}
            msg = clean_text(str(data.get("message", raw))) if isinstance(data, dict) else raw
        except Exception:
            msg = str(exc)
        return False, f"授權伺服器錯誤：{msg}", {}
    except Exception as exc:
        return False, f"無法連線授權伺服器：{exc}", {}


def rsa_verify_sha256(message: bytes, signature: bytes) -> bool:
    key_size = (LICENSE_PUBLIC_N.bit_length() + 7) // 8
    if len(signature) != key_size:
        return False
    sig_int = int.from_bytes(signature, "big")
    block = pow(sig_int, LICENSE_PUBLIC_E, LICENSE_PUBLIC_N).to_bytes(key_size, "big")
    digest = hashlib.sha256(message).digest()
    digest_info = LICENSE_SHA256_DER_PREFIX + digest
    expected_padding_len = key_size - len(digest_info) - 3
    if expected_padding_len < 8:
        return False
    expected = b"\x00\x01" + (b"\xff" * expected_padding_len) + b"\x00" + digest_info
    return hmac.compare_digest(block, expected)


def decode_license_key(key: str) -> dict[str, Any]:
    cleaned = normalize_license_key(key)
    prefix = LICENSE_FORMAT_PREFIX + "."
    if not cleaned.startswith(prefix):
        raise ValueError("金鑰格式錯誤。")
    body = cleaned[len(prefix):]
    parts = body.split(".")
    if len(parts) != 2:
        raise ValueError("金鑰格式錯誤。")
    payload_b64, sig_b64 = parts
    signed_message = f"{prefix}{payload_b64}".encode("utf-8")
    signature = b64url_decode(sig_b64)
    if not rsa_verify_sha256(signed_message, signature):
        raise ValueError("金鑰簽章驗證失敗，可能不是有效金鑰或內容被修改。")
    try:
        payload = json.loads(b64url_decode(payload_b64).decode("utf-8"))
    except Exception as exc:
        raise ValueError(f"金鑰內容無法解析：{exc}") from exc
    if payload.get("app") != LICENSE_APP_ID:
        raise ValueError("金鑰不屬於本程式。")
    license_type = clean_text(str(payload.get("license_type", ""))).lower()
    if license_type not in ("trial", "pro"):
        raise ValueError("金鑰類型不正確。")
    days = to_int(payload.get("days", 0))
    if license_type == "trial" and days != 7:
        raise ValueError("試用版金鑰天數不正確。")
    if license_type == "pro" and days != 30:
        raise ValueError("正式版金鑰天數不正確。")
    return payload


def fetch_network_time(timeout: int = 5) -> tuple[datetime | None, str]:
    errors: list[str] = []
    for url in NETWORK_TIME_URLS:
        for method in ("HEAD", "GET"):
            try:
                request = Request(url, headers={"User-Agent": "CardTradeLib-License/1.0"}, method=method)
                with urlopen(request, timeout=timeout) as response:
                    date_header = response.headers.get("Date", "")
                    if date_header:
                        dt = parsedate_to_datetime(date_header)
                        if dt.tzinfo is None:
                            dt = dt.replace(tzinfo=timezone.utc)
                        return dt.astimezone(timezone.utc), url
                    errors.append(f"{url} 沒有回傳 Date header")
            except Exception as exc:
                errors.append(f"{url} {method}: {exc}")
    return None, "；".join(errors[-3:])


def load_license_state() -> dict[str, Any]:
    if not LICENSE_STATE_PATH.exists():
        return {}
    try:
        with LICENSE_STATE_PATH.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def save_license_state(state: dict[str, Any]) -> None:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    if isinstance(state, dict) and state:
        attach_license_state_signature(state)
    with LICENSE_STATE_PATH.open("w", encoding="utf-8") as fh:
        json.dump(state, fh, ensure_ascii=False, indent=2)


def activate_license_key(key: str) -> tuple[bool, str, dict[str, Any]]:
    try:
        payload = decode_license_key(key)
    except Exception as exc:
        return False, str(exc), {}
    license_type = clean_text(str(payload.get("license_type", ""))).lower()
    days = 7 if license_type == "trial" else 30
    key_hash = license_key_hash_value(key)
    current_machine = machine_id_hash()
    request_payload = {
        "license_id": clean_text(str(payload.get("license_id", ""))),
        "license_key_hash": key_hash,
        "machine_id_hash": current_machine,
        "app_id": LICENSE_APP_ID,
        "app_version": LICENSE_API_VERSION,
    }
    ok, message, response = call_license_server("activate", request_payload, timeout=15)
    if not ok:
        return False, message, {}
    activated_at = clean_text(str(response.get("activated_at", "")))
    expires_at = clean_text(str(response.get("expires_at", "")))
    server_time = clean_text(str(response.get("server_time", ""))) or activated_at
    if not parse_utc_datetime(expires_at) or not parse_utc_datetime(server_time):
        return False, "授權伺服器回傳時間格式錯誤。", {}
    state = {
        "status": "active",
        "license_payload": payload,
        "license_key_hash": key_hash,
        "license_key_mask": mask_license_key(key),
        "license_type": license_type,
        "days": days,
        "machine_id": current_machine,
        "activated_at": activated_at,
        "expires_at": expires_at,
        "last_server_check_at": server_time,
        "last_network_source": load_license_server_settings().get("server_url", "Google Sheet License Server"),
        "last_local_check_at": iso_utc(utc_now()),
        "last_error": "",
        "server_status": clean_text(str(response.get("status", "active"))),
    }
    save_license_state(state)
    label = "試用版" if license_type == "trial" else "正式版"
    return True, f"啟用成功：{label}，有效至 {expires_at}。", state

def evaluate_license(use_network: bool = False) -> dict[str, Any]:
    state = load_license_state()
    result = {
        "ok": False,
        "status": "inactive",
        "label": "未啟用",
        "message": "尚未輸入啟用金鑰。",
        "state": state,
        "now": None,
    }
    if not state:
        return result
    if not verify_license_state_signature(state):
        result.update({"status": "tampered", "label": "授權資料被修改", "message": "授權狀態檔簽章不正確，可能被複製或手動修改。"})
        return result
    if state.get("machine_id") and state.get("machine_id") != machine_id_hash():
        result.update({"status": "machine_mismatch", "label": "裝置不符", "message": "此授權狀態不屬於目前電腦。"})
        return result
    expires_at = parse_utc_datetime(state.get("expires_at"))
    last_server = parse_utc_datetime(state.get("last_server_check_at"))
    last_local = parse_utc_datetime(state.get("last_local_check_at"))
    now_local = utc_now()
    if not expires_at or not last_server:
        result.update({"status": "invalid", "label": "授權資料異常", "message": "授權狀態檔缺少必要欄位。"})
        return result
    if last_local and now_local + timedelta(minutes=10) < last_local:
        result.update({"status": "time_error", "label": "系統時間異常", "message": "偵測到本機時間倒退，請校正系統時間並重新驗證授權。"})
        state["status"] = "time_error"
        state["last_error"] = result["message"]
        save_license_state(state)
        return result
    network_now = None
    network_source = ""
    if use_network:
        payload = state.get("license_payload", {}) if isinstance(state.get("license_payload"), dict) else {}
        ok, server_message, response = call_license_server("verify", {
            "license_id": clean_text(str(payload.get("license_id", ""))),
            "license_key_hash": clean_text(str(state.get("license_key_hash", ""))),
            "machine_id_hash": machine_id_hash(),
            "app_id": LICENSE_APP_ID,
            "app_version": LICENSE_API_VERSION,
        }, timeout=15)
        if ok:
            server_time_text = clean_text(str(response.get("server_time", "")))
            server_expires_text = clean_text(str(response.get("expires_at", state.get("expires_at", ""))))
            server_time = parse_utc_datetime(server_time_text)
            server_expires = parse_utc_datetime(server_expires_text)
            if server_time is not None:
                network_now = server_time
                state["last_server_check_at"] = iso_utc(server_time)
                last_server = server_time
            if server_expires is not None:
                state["expires_at"] = iso_utc(server_expires)
                expires_at = server_expires
            state["status"] = clean_text(str(response.get("status", "active"))) or "active"
            state["last_network_source"] = load_license_server_settings().get("server_url", "Google Sheet License Server")
            state["last_error"] = ""
        else:
            state["last_error"] = server_message
            if "已過期" in server_message or "expired" in server_message.lower():
                state["status"] = "expired"
            elif "其他電腦" in server_message or "machine" in server_message.lower():
                state["status"] = "machine_mismatch"
    effective_now = network_now or now_local
    if clean_text(str(state.get("status", ""))) in {"machine_mismatch", "disabled"}:
        msg = state.get("last_error") or "授權伺服器拒絕此授權。"
        save_license_state(state)
        result.update({"status": state.get("status", "invalid"), "label": "授權驗證失敗", "message": msg})
        return result
    if network_now is None:
        grace_until = last_server + timedelta(hours=LICENSE_OFFLINE_GRACE_HOURS)
        if now_local > grace_until:
            msg = f"超過 {LICENSE_OFFLINE_GRACE_HOURS} 小時未成功連網驗證，請連網後按『立即驗證授權』。"
            state["status"] = "needs_network"
            state["last_local_check_at"] = iso_utc(now_local)
            state["last_error"] = msg
            save_license_state(state)
            result.update({"status": "needs_network", "label": "需要連網驗證", "message": msg})
            return result
    if effective_now > expires_at:
        state["status"] = "expired"
        state["last_local_check_at"] = iso_utc(now_local)
        save_license_state(state)
        result.update({"status": "expired", "label": "已過期", "message": f"授權已於 {iso_utc(expires_at)} 到期。", "now": iso_utc(effective_now)})
        return result
    state["status"] = "active"
    state["last_local_check_at"] = iso_utc(now_local)
    save_license_state(state)
    remaining = expires_at - effective_now
    remaining_days = max(0, remaining.days)
    license_type = clean_text(str(state.get("license_type", ""))).lower()
    type_label = "試用版" if license_type == "trial" else "正式版"
    result.update({
        "ok": True,
        "status": "active",
        "label": "已啟用",
        "message": f"{type_label}授權有效，剩餘約 {remaining_days} 天，到期：{iso_utc(expires_at)}。",
        "state": state,
        "now": iso_utc(effective_now),
    })
    return result


PAYMENT_REQUIRED_LOGISTIC_CODES = {
    "SEVEN", "FAMI", "HILIFE", "MAPLE", "POST", "ISLAND", "SELF",
    "POST_IBOX", "TCAT", "R_POSTCOD", "HOUSE", "REFRIGERATED",
}
COD_TO_PREPAID_LOGISTIC = {
    "SEVEN_COD": "SEVEN",
    "FAMI_COD": "FAMI",
    "HILIFE_COD": "HILIFE",
    "F2F": "SELF",
}

RUTEN_LOGISTIC_LABELS = {
    "SEVEN_COD": "7-11 取貨付款",
    "SEVEN": "7-11 純取貨",
    "FAMI_COD": "全家取貨付款",
    "FAMI": "全家純取貨",
    "HILIFE_COD": "萊爾富取貨付款",
    "HILIFE": "萊爾富純取貨",
    "MAPLE": "便利帶隔日配",
    "POST": "郵寄寄送",
    "ISLAND": "離島寄送",
    "SELF": "面交",
    "F2F": "面交取貨付款",
}

RUTEN_PAYMENT_LABELS = {
    "PP_PI": "Pi 拍錢包支付連",
    "PP_CRD": "PChomePay 信用卡一次付清",
    "PP_CRD_N3": "PChomePay 信用卡3期",
    "PP_CRD_N6": "PChomePay 信用卡6期",
    "PP_CRD_N12": "PChomePay 信用卡12期",
    "PAYLINK": "PChomePay 現金/ATM/餘額",
    "ATM": "銀行或郵局轉帳",
    "PS": "郵局無摺存款",
}

RUTEN_TW_LOCATION_OPTIONS = [
    ("台北市", "01"),
    ("基隆市", "02"),
    ("新北市", "03"),
    ("宜蘭縣", "04"),
    ("新竹市", "05"),
    ("新竹縣", "06"),
    ("桃園市", "07"),
    ("苗栗縣", "08"),
    ("台中市", "09"),
    ("彰化縣", "10"),
    ("南投縣", "11"),
    ("嘉義市", "12"),
    ("嘉義縣", "13"),
    ("雲林縣", "14"),
    ("台南市", "15"),
    ("高雄市", "16"),
    ("屏東縣", "17"),
    ("台東縣", "18"),
    ("花蓮縣", "19"),
    ("澎湖縣", "20"),
    ("金門縣", "21"),
    ("連江縣", "22"),
]
DEFAULT_RUTEN_LOCATION_CODE = "03"


def normalize_ruten_location_code(value: Any) -> str:
    text = clean_text(str(value))
    if text.isdigit() and len(text) == 1:
        return text.zfill(2)
    return text


def ruten_location_label(code: Any) -> str:
    code_text = normalize_ruten_location_code(code)
    for label, value in RUTEN_TW_LOCATION_OPTIONS:
        if value == code_text:
            return label
    return code_text or "未設定"


def setup_ruten_location_combo(combo: QComboBox, current_code: Any) -> None:
    combo.clear()
    for label, code in RUTEN_TW_LOCATION_OPTIONS:
        combo.addItem(label, code)
    current = normalize_ruten_location_code(current_code) or DEFAULT_RUTEN_LOCATION_CODE
    if current and combo.findData(current) < 0:
        combo.addItem(f"自訂/已儲存：{current}", current)
    idx = combo.findData(current)
    if idx < 0:
        idx = combo.findData(DEFAULT_RUTEN_LOCATION_CODE)
    if idx >= 0:
        combo.setCurrentIndex(idx)


def default_ruten_settings() -> dict[str, Any]:
    return {
        "api_host": "https://partner.ruten.com.tw",
        "api_key": "",
        "secret_key": "",
        "salt_key": "",
        "signature_base": "full_url",
        "order_status": "All",
        "auto_apply_orders": False,
        "auto_order_check": False,
        "auto_order_minutes": 5,
        "auto_apply_order_statuses": ["ToBeConfirmed", "ReadyToShip", "Shipped"],
        "auto_restore_cancelled_orders": True,
        "auto_push_after_order_apply": False,
        "auto_push_local_changes": False,
        "auto_offline_zero_stock": False,
        "auto_online_positive_stock": False,
        "last_api_status": "未測試",
        "last_product_api_status": "未測試",
        "last_order_api_status": "未測試",
        "last_success_at": "",
        "last_failure_at": "",
        "last_error": "",
        "last_order_check_at": "",
        "last_order_success_at": "",
        "last_order_failure_at": "",
        "last_order_error": "",
        "last_remote_import_at": "",
        "create_class_id": "",
        "create_class_presets": [
            {"label": "玩具公仔 -> 紙牌遊戲 -> 魔法風雲會", "class_id": "000500140010"},
        ],
        "create_store_class_id": "",
        "create_condition": 1,
        "create_stock_status": "3DAY",
        "create_location_type": 1,
        "create_location": DEFAULT_RUTEN_LOCATION_CODE,
        "create_location_user_selected": False,
        "create_shipping_setting": 1,
        "default_logistic_info": [],
        "default_payment_info": [],
        "default_logistic_combine": True,
        "last_logistic_api_status": "未測試",
        "last_logistic_check_at": "",
        "last_logistic_error": "",
        "auto_upload_scryfall_image_on_create": True,
        "last_image_upload_at": "",
        "last_image_upload_error": "",
    }


def ruten_default_logistic_payload(settings: dict[str, Any]) -> dict[str, Any]:
    raw_logistics = settings.get("default_logistic_info")
    if not isinstance(raw_logistics, list):
        raw_logistics = []
    logistic_info: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in raw_logistics:
        if not isinstance(row, dict):
            continue
        logistic_id = clean_text(str(row.get("logistic_id", ""))).upper()
        if not logistic_id or logistic_id in seen:
            continue
        fee = max(0, to_int(row.get("shipping_fee", 0)))
        logistic_info.append({"logistic_id": logistic_id, "shipping_fee": fee})
        seen.add(logistic_id)

    raw_payments = settings.get("default_payment_info")
    if raw_payments is None:
        raw_payments = []
    elif not isinstance(raw_payments, list):
        raw_payments = []
    payment_info: list[str] = []
    for payment in raw_payments:
        payment_id = clean_text(str(payment)).upper()
        if payment_id and payment_id not in payment_info:
            payment_info.append(payment_id)

    existing_logistics = {str(row.get("logistic_id", "")).upper() for row in logistic_info}
    has_payment_required_logistic = any(code in PAYMENT_REQUIRED_LOGISTIC_CODES for code in existing_logistics)
    if payment_info and not has_payment_required_logistic:
        extra_rows: list[dict[str, Any]] = []
        for row in logistic_info:
            code = str(row.get("logistic_id", "")).upper()
            prepaid_code = COD_TO_PREPAID_LOGISTIC.get(code)
            if prepaid_code and prepaid_code not in existing_logistics:
                extra_rows.append({"logistic_id": prepaid_code, "shipping_fee": max(0, to_int(row.get("shipping_fee", 0)))})
                existing_logistics.add(prepaid_code)
        logistic_info.extend(extra_rows)

    if not payment_info and any(str(row.get("logistic_id", "")).upper() in PAYMENT_REQUIRED_LOGISTIC_CODES for row in logistic_info):
        payment_info = ["PAYLINK"]

    return {
        "logistic_info": logistic_info,
        "payment_info": payment_info,
        "combine": bool(settings.get("default_logistic_combine", True)),
    }


def ruten_extract_logistic_payload(payload: Any) -> dict[str, Any]:
    if not isinstance(payload, dict):
        return {}
    candidates: list[Any] = [payload.get("data"), payload]
    for data in candidates:
        if not isinstance(data, dict):
            continue
        nested = data
        for key in ("setting", "default", "logistic_default", "default_logistic", "shipping_setting"):
            if isinstance(nested.get(key), dict):
                nested = nested.get(key)
                break
        logistic_info = nested.get("logistic_info") or nested.get("logistics") or nested.get("shipping_info")
        payment_info = nested.get("payment_info") or nested.get("payments") or nested.get("payment")
        combine = nested.get("combine", nested.get("is_combine", nested.get("combine_shipping", True)))
        if isinstance(logistic_info, list) or isinstance(payment_info, list):
            result: dict[str, Any] = {}
            if isinstance(logistic_info, list):
                cleaned_logistics: list[dict[str, Any]] = []
                for row in logistic_info:
                    if isinstance(row, dict):
                        logistic_id = clean_text(str(ruten_pick(row, "logistic_id", "id", "code", default=""))).upper()
                        if logistic_id:
                            cleaned_logistics.append({
                                "logistic_id": logistic_id,
                                "shipping_fee": max(0, to_int(ruten_pick(row, "shipping_fee", "fee", "freight", default=0))),
                            })
                if cleaned_logistics:
                    result["default_logistic_info"] = cleaned_logistics
            if isinstance(payment_info, list):
                cleaned_payments: list[str] = []
                for row in payment_info:
                    payment_id = clean_text(str(row if not isinstance(row, dict) else ruten_pick(row, "payment_id", "id", "code", default=""))).upper()
                    if payment_id and payment_id not in cleaned_payments:
                        cleaned_payments.append(payment_id)
                if cleaned_payments:
                    result["default_payment_info"] = cleaned_payments
            result["default_logistic_combine"] = bool(combine)
            return result
    return {}


def ruten_logistic_settings_summary(settings: dict[str, Any]) -> str:
    payload = ruten_default_logistic_payload(settings)
    logistics = payload.get("logistic_info", []) if isinstance(payload, dict) else []
    payments = payload.get("payment_info", []) if isinstance(payload, dict) else []
    lines = ["目前露天新增商品預設檔："]
    lines.append("\n運送方式：")
    if logistics:
        for row in logistics:
            if isinstance(row, dict):
                code = clean_text(str(row.get("logistic_id", ""))).upper()
                label = RUTEN_LOGISTIC_LABELS.get(code, code or "未知物流")
                fee = max(0, to_int(row.get("shipping_fee", 0)))
                lines.append(f"- {label}（{code}），運費 {fee}")
    else:
        lines.append("- 未設定")
    lines.append("\n付款方式：")
    if payments:
        for payment in payments:
            code = clean_text(str(payment)).upper()
            label = RUTEN_PAYMENT_LABELS.get(code, code or "未知付款")
            lines.append(f"- {label}（{code}）")
    else:
        lines.append("- 無 / 只使用取貨付款類物流")
    lines.append(f"\n合併運費：{'開啟' if bool(payload.get('combine', True)) else '關閉'}")
    return "\n".join(lines)


def normalize_ruten_class_id(value: Any) -> str:
    return re.sub(r"\D", "", str(value or "")).strip()


def ruten_class_preset_default() -> list[dict[str, str]]:
    return [
        {"label": "玩具公仔 -> 紙牌遊戲 -> 魔法風雲會", "class_id": "000500140010"},
    ]


def normalize_ruten_class_preset(row: Any) -> dict[str, str] | None:
    if not isinstance(row, dict):
        return None
    class_id = normalize_ruten_class_id(row.get("class_id", row.get("id", row.get("code", ""))))
    if not class_id:
        return None
    label = clean_text(str(row.get("label", row.get("name", ""))))
    if not label:
        label = class_id
    return {"label": label, "class_id": class_id}


def ruten_class_presets(settings: dict[str, Any]) -> list[dict[str, str]]:
    raw_presets = settings.get("create_class_presets")
    presets: list[dict[str, str]] = []
    seen: set[str] = set()
    if isinstance(raw_presets, list):
        for row in raw_presets:
            preset = normalize_ruten_class_preset(row)
            if not preset:
                continue
            class_id = preset["class_id"]
            if class_id in seen:
                continue
            presets.append(preset)
            seen.add(class_id)
    for row in ruten_class_preset_default():
        preset = normalize_ruten_class_preset(row)
        if preset and preset["class_id"] not in seen:
            presets.append(preset)
            seen.add(preset["class_id"])
    return presets


def format_ruten_class_preset(row: dict[str, Any]) -> str:
    label = clean_text(str(row.get("label", "")))
    class_id = normalize_ruten_class_id(row.get("class_id", ""))
    if label and label != class_id:
        return f"{label} : {class_id}"
    return class_id


def parse_ruten_class_input(value: Any) -> tuple[str, str]:
    text = clean_text(str(value or ""))
    if not text:
        return "", ""
    if "：" in text:
        left, right = text.rsplit("：", 1)
        class_id = normalize_ruten_class_id(right)
        if class_id:
            return clean_text(left), class_id
    if ":" in text:
        left, right = text.rsplit(":", 1)
        class_id = normalize_ruten_class_id(right)
        if class_id:
            return clean_text(left), class_id
    class_id = normalize_ruten_class_id(text)
    label = clean_text(re.sub(r"[0-9\s:：]+$", "", text))
    if label == class_id:
        label = ""
    return label, class_id


def add_or_update_ruten_class_preset(settings_or_presets: Any, label: str, class_id: str) -> list[dict[str, str]]:
    class_id = normalize_ruten_class_id(class_id)
    label = clean_text(label) or class_id
    if not class_id:
        return ruten_class_presets(settings_or_presets) if isinstance(settings_or_presets, dict) else []
    if isinstance(settings_or_presets, dict):
        presets = ruten_class_presets(settings_or_presets)
    elif isinstance(settings_or_presets, list):
        presets = [p for p in (normalize_ruten_class_preset(row) for row in settings_or_presets) if p]
    else:
        presets = []
    updated = False
    for row in presets:
        if row.get("class_id") == class_id:
            row["label"] = label
            updated = True
            break
    if not updated:
        presets.append({"label": label, "class_id": class_id})
    return presets


def setup_ruten_class_combo(combo: QComboBox, presets: list[dict[str, str]], current_class_id: Any) -> None:
    current = normalize_ruten_class_id(current_class_id)
    combo.clear()
    for preset in presets:
        class_id = normalize_ruten_class_id(preset.get("class_id", ""))
        if not class_id:
            continue
        combo.addItem(format_ruten_class_preset(preset), class_id)
    if current and combo.findData(current) < 0:
        combo.addItem(current, current)
    idx = combo.findData(current)
    if idx >= 0:
        combo.setCurrentIndex(idx)
    elif combo.count() > 0:
        combo.setCurrentIndex(0)


def default_ruten_item_fields() -> dict[str, Any]:
    return {
        "enabled": True,
        "item_id": "",
        "spec_id": "",
        "custom_no": "",
        "title": "",
        "price": 0,
        "status": "not_bound",
        "listing_qty": 1,
        "remote_stock": "",
        "auto_restock": False,
        "restock_target": 1,
        "description": "",
        "class_id": "",
        "store_class_id": "",
        "condition": 1,
        "stock_status": "3DAY",
        "location_type": 1,
        "location": DEFAULT_RUTEN_LOCATION_CODE,
        "match_status": "未配對",
        "match_note": "",
        "last_sync_at": "",
        "last_order_at": "",
        "image_uploaded_at": "",
        "image_upload_error": "",
        "last_error": "",
    }


def ruten_listing_qty(record: dict[str, Any]) -> int:
    ruten = ensure_ruten_item_fields(record)
    local_qty = max(0, to_int(record.get("quantity", 0)))
    raw_qty = to_int(ruten.get("listing_qty", 0))
    if raw_qty <= 0:
        remote_qty = to_int(ruten.get("remote_stock", 0))
        raw_qty = remote_qty if remote_qty > 0 else min(local_qty, 1)
    if local_qty <= 0:
        return 0
    return max(0, min(raw_qty, local_qty))


def set_ruten_listing_qty(record: dict[str, Any], qty: int) -> int:
    ruten = ensure_ruten_item_fields(record)
    local_qty = max(0, to_int(record.get("quantity", 0)))
    final_qty = max(0, min(int(qty or 0), local_qty))
    ruten["listing_qty"] = final_qty
    return final_qty


def ruten_pairing_status(record: dict[str, Any]) -> str:
    ruten = ensure_ruten_item_fields(record)
    item_id = clean_text(str(ruten.get("item_id", "")))
    custom_no = clean_text(str(ruten.get("custom_no", "")))
    status = clean_text(str(ruten.get("match_status", "")))
    if item_id and status not in {"衝突", "疑似配對"}:
        return "已配對"
    if item_id:
        return status or "已配對"
    if custom_no:
        return "待查ID"
    return "未配對"


def ensure_ruten_settings(db: dict[str, Any]) -> dict[str, Any]:
    current = db.get("ruten_settings")
    if not isinstance(current, dict):
        current = {}
    merged = default_ruten_settings()
    merged.update(current)
    # 舊版程式把 05 寫死成預設所在地；若使用者尚未明確設定過，就改回較合理的預設並讓使用者可在設定頁調整。
    if not bool(current.get("create_location_user_selected", False)) and normalize_ruten_location_code(merged.get("create_location", "")) == "05":
        merged["create_location"] = DEFAULT_RUTEN_LOCATION_CODE
    merged["create_location"] = normalize_ruten_location_code(merged.get("create_location", DEFAULT_RUTEN_LOCATION_CODE)) or DEFAULT_RUTEN_LOCATION_CODE
    db["ruten_settings"] = merged
    return merged


def make_ruten_custom_no(record: dict[str, Any]) -> str:
    code = clean_text(str(record.get("set_code", ""))).upper()
    collector = clean_text(str(record.get("collector", ""))).upper()
    lang = clean_text(str(record.get("lang", ""))).upper()
    rid = clean_text(str(record.get("id", "")))[:8].upper()
    parts = ["MTG", code or "SET", collector or "NO", lang or "LANG", rid or uuid.uuid4().hex[:8].upper()]
    return sanitize_ruten_custom_no("-".join(parts))


def make_ruten_title(record: dict[str, Any]) -> str:
    name = clean_text(str(record.get("name", "")))
    edition = clean_text(str(record.get("edition", "")))
    set_code = clean_text(str(record.get("set_code", ""))).upper()
    collector = clean_text(str(record.get("collector", "")))
    rarity = clean_text(str(record.get("rarity", "")))
    title = " ".join(part for part in [name, edition or set_code, collector, rarity] if part)
    return sanitize_ruten_title(title)


def sanitize_ruten_title(value: Any) -> str:
    return clean_text(str(value)).replace("\\", "/")[:130]


def sanitize_ruten_custom_no(value: Any) -> str:
    text = clean_text(str(value)).replace(" ", "-")[:100]
    cleaned = "".join(ch for ch in text if 33 <= ord(ch) <= 126)
    return cleaned[:100]


def make_ruten_item_web_url(item_id: Any) -> str:
    text = clean_text(str(item_id))
    if not text:
        return ""
    if text.lower().startswith(("http://", "https://")):
        return text
    match = re.search(r"\d{8,}", text)
    if not match:
        return ""
    return f"https://www.ruten.com.tw/item/show?{match.group(0)}"


def simple_html_escape(value: Any) -> str:
    return (
        str(value or "")
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


RUTEN_DESCRIPTION_LABELS = ["卡名", "英文名", "系列", "系列代碼", "Collector", "稀有度", "語言", "類型", "備註"]


def normalize_ruten_description_lines(text: Any) -> str:
    raw = str(text or "")
    if not raw.strip():
        return ""
    raw = re.sub(r"(?i)<\s*br\s*/?\s*>", "\n", raw)
    raw = re.sub(r"(?i)</\s*(p|div|li|tr|h[1-6])\s*>", "\n", raw)
    raw = re.sub(r"(?is)<[^>]+>", "", raw)
    raw = html_unescape(raw)
    raw = raw.replace("\r\n", "\n").replace("\r", "\n").strip()
    if not raw:
        return ""
    if "\n" not in raw:
        for label in RUTEN_DESCRIPTION_LABELS[1:]:
            raw = re.sub(rf"\s+({re.escape(label)}：)", r"\n\1", raw)
    lines = [line.strip() for line in raw.split("\n") if line.strip()]
    return "\n".join(lines)


def ruten_description_for_api(text: Any) -> str:
    plain = normalize_ruten_description_lines(text)
    if not plain:
        return ""
    return "<br>".join(simple_html_escape(line) for line in plain.split("\n"))


def make_ruten_description(record: dict[str, Any]) -> str:
    rows = []
    fields = [
        ("卡名", record.get("name", "")),
        ("英文名", record.get("english_name", "") or record.get("name", "")),
        ("系列", record.get("edition", "") or record.get("set_code", "")),
        ("系列代碼", record.get("set_code", "")),
        ("Collector", record.get("collector", "")),
        ("稀有度", record.get("rarity", "")),
        ("語言", record.get("lang_label", "") or record.get("lang", "")),
        ("類型", record.get("type", "") or record.get("oracle_type", "")),
        ("備註", record.get("note", "")),
    ]
    for label, value in fields:
        value_text = clean_text(str(value))
        if value_text:
            rows.append(f"{label}：{value_text}")
    return "\n".join(rows) or "MTG 單卡。"


def guess_ruten_price(record: dict[str, Any]) -> int:
    ruten = record.get("ruten") if isinstance(record.get("ruten"), dict) else {}
    price = to_int(ruten.get("price", 0))
    if price > 0:
        return price
    return max(0, to_int(record.get("price", 0)))


def ensure_ruten_item_fields(record: dict[str, Any]) -> dict[str, Any]:
    current = record.get("ruten")
    if not isinstance(current, dict):
        current = {}
    merged = default_ruten_item_fields()
    merged.update(current)
    if not clean_text(str(merged.get("custom_no", ""))):
        merged["custom_no"] = make_ruten_custom_no(record)
    if not clean_text(str(merged.get("title", ""))):
        merged["title"] = make_ruten_title(record)
    if to_int(merged.get("price", 0)) <= 0:
        guessed = to_int(record.get("ruten_price", 0)) or to_int(record.get("price", 0))
        merged["price"] = max(0, guessed)
    local_qty = max(0, to_int(record.get("quantity", 0)))
    if to_int(merged.get("listing_qty", 0)) <= 0:
        remote_qty = max(0, to_int(merged.get("remote_stock", 0)))
        merged["listing_qty"] = remote_qty if remote_qty > 0 else min(local_qty, 1)
    merged["listing_qty"] = max(0, min(to_int(merged.get("listing_qty", 0)), local_qty if local_qty > 0 else to_int(merged.get("listing_qty", 0))))
    if to_int(merged.get("restock_target", 0)) <= 0:
        merged["restock_target"] = max(1, to_int(merged.get("listing_qty", 1)) or 1)
    if clean_text(str(merged.get("item_id", ""))) and clean_text(str(merged.get("match_status", ""))) in {"", "未配對"}:
        merged["match_status"] = "已配對"
    record["ruten"] = merged
    return merged


def ruten_response_ok(payload: Any) -> bool:
    return isinstance(payload, dict) and str(payload.get("status", "")).lower() == "success"


RUTEN_ERROR_HINTS = {
    "20005": "傳入參數格式錯誤，請檢查露天商品ID、分類ID、數量或欄位格式。",
    "200005": "傳入參數格式錯誤，請檢查露天商品ID、分類ID、數量或欄位格式。",
    "211101": "新增商品預設檔未設定，請先在程式內設定物流/付款預設檔。",
    "211106": "物流與付款方式不相容：純取貨/郵寄需要搭配付款方式；取貨付款不應只搭先付款。",
    "211006": "物流與付款方式不相容：請重新勾選物流/付款組合。",
    "401": "API 驗證失敗，請檢查 API Key、Secret Key、Salt Key 或簽章模式。",
    "403": "API 權限不足，請確認露天是否已開通商品/訂單 API 權限。",
    "404": "找不到指定露天商品，請確認商品ID是否正確。",
    "NON_JSON": "露天回傳內容不是 JSON，可能是伺服器暫時異常或權限頁面。",
}


def translate_ruten_error(code: Any = "", message: Any = "") -> str:
    code_text = clean_text(str(code))
    msg_text = clean_text(str(message))
    hint = RUTEN_ERROR_HINTS.get(code_text, "")
    if not hint:
        combined = f"{code_text} {msg_text}"
        for known_code, known_hint in RUTEN_ERROR_HINTS.items():
            if known_code and known_code in combined:
                hint = known_hint
                break
    if code_text and code_text.lower() != "none" and msg_text:
        return f"{code_text} {msg_text}" + (f"｜{hint}" if hint else "")
    if msg_text:
        return msg_text + (f"｜{hint}" if hint and hint not in msg_text else "")
    if code_text and code_text.lower() != "none":
        return f"{code_text}" + (f"｜{hint}" if hint else "")
    return hint or "未知錯誤"


def ruten_response_message(payload: Any) -> str:
    if isinstance(payload, dict):
        err = clean_text(str(payload.get("error_msg", "")))
        code = clean_text(str(payload.get("error_code", "")))
        if err or (code and code.lower() != "none"):
            return translate_ruten_error(code, err)
        return clean_text(str(payload.get("status", ""))) or "OK"
    return translate_ruten_error("", payload)


def ruten_timestamp_text(value: Any) -> str:
    try:
        timestamp = int(float(str(value)))
        if timestamp <= 0:
            return ""
        return datetime.fromtimestamp(timestamp).strftime("%Y-%m-%d %H:%M:%S")
    except Exception:
        return clean_text(str(value))


def ruten_pick(data: Any, *keys: str, default: Any = "") -> Any:
    if not isinstance(data, dict):
        return default
    for key in keys:
        if key in data and data[key] not in (None, ""):
            return data[key]
    return default


def ruten_as_list(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, list):
        return [item for item in value if isinstance(item, dict)]
    if isinstance(value, dict):
        return [value]
    return []


def ruten_product_list_items(payload: Any) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        return []
    data = payload.get("data")
    if isinstance(data, list):
        return ruten_as_list(data)
    if not isinstance(data, dict):
        return []
    for key in ("items", "item_list", "product_list", "products", "list", "rows", "data"):
        value = data.get(key)
        if isinstance(value, list):
            return ruten_as_list(value)
    return []


def ruten_product_total(payload: Any, fallback: int = 0) -> int:
    if not isinstance(payload, dict):
        return fallback
    data = payload.get("data")
    if isinstance(data, dict):
        for key in ("total", "total_count", "count", "item_count"):
            if key in data:
                total = to_int(data.get(key))
                if total > 0:
                    return total
    return fallback


def ruten_flatten_product_data(data: Any) -> dict[str, Any]:
    if not isinstance(data, dict):
        return {}
    result = dict(data)
    for key in ("item", "product", "product_info", "item_info", "detail"):
        nested = data.get(key)
        if isinstance(nested, dict):
            merged = dict(nested)
            for sub_key, sub_value in result.items():
                if sub_value not in (None, ""):
                    merged[sub_key] = sub_value
            result = merged
    return result


def normalize_external_image_url(value: Any) -> str:
    text = html_unescape(clean_text(str(value or "")))
    if not text:
        return ""
    text = text.replace("\\/", "/")
    text = re.sub(r"\s+", "", text)
    if text.startswith("//"):
        text = "https:" + text
    if text.startswith("http://") or text.startswith("https://"):
        return text
    if text.startswith("/"):
        return urljoin("https://www.ruten.com.tw", text)
    return ""


def is_likely_ruten_product_image_url(url: str) -> bool:
    lower = clean_text(url).lower()
    if not lower.startswith(("http://", "https://")):
        return False
    reject_tokens = (
        "favicon", "logo", "icon", "sprite", "loading", "transparent", "spacer",
        "avatar", "profile", "banner", "ad_", "ads", "analytics", "pixel", "blank",
        "default", "noimage", "no_image", "no-photo", "nophoto",
    )
    if any(token in lower for token in reject_tokens):
        return False
    accept_tokens = (
        ".jpg", ".jpeg", ".png", ".webp", ".gif",
        "image", "img", "pic", "photo", "goods", "item", "product", "rimg", "ruten",
    )
    return any(token in lower for token in accept_tokens)


def ruten_image_url_score(url: str) -> int:
    lower = clean_text(url).lower()
    score = 0
    if any(host in lower for host in ("ruten", "rimg.com.tw", "image.ruten", "img.ruten", "goods.ruten")):
        score += 80
    if any(token in lower for token in ("goods", "item", "product")):
        score += 30
    if any(token in lower for token in ("image", "img", "pic", "photo")):
        score += 20
    if re.search(r"\.(jpg|jpeg|png|webp)(\?|$)", lower):
        score += 25
    if "thumb" in lower or "small" in lower or "resize" in lower:
        score -= 10
    return score


def ruten_best_image_url(urls: list[str]) -> str:
    seen: set[str] = set()
    candidates: list[str] = []
    for raw in urls:
        url = normalize_external_image_url(raw)
        if not url or url in seen:
            continue
        seen.add(url)
        if is_likely_ruten_product_image_url(url):
            candidates.append(url)
    if not candidates:
        return ""
    return sorted(candidates, key=ruten_image_url_score, reverse=True)[0]


def ruten_collect_image_urls(value: Any, depth: int = 0) -> list[str]:
    if depth > 7:
        return []
    urls: list[str] = []
    if isinstance(value, str):
        text = html_unescape(value).replace("\\/", "/")
        normalized = normalize_external_image_url(text)
        if normalized:
            urls.append(normalized)
        for match in re.findall(r"https?:\/\/[^\s'\"<>\)]+", text):
            urls.append(normalize_external_image_url(match))
        for match in re.findall(r"//[^\s'\"<>\)]+", text):
            urls.append(normalize_external_image_url(match))
        return [url for url in urls if url]
    if isinstance(value, list):
        for item in value:
            urls.extend(ruten_collect_image_urls(item, depth + 1))
        return urls
    if isinstance(value, dict):
        preferred_keys = (
            "image_url", "img_url", "pic_url", "picture_url", "photo_url", "cover_url",
            "main_image", "main_img", "main_photo", "item_image", "item_img", "item_photo",
            "goods_image", "goods_img", "product_image", "product_img", "thumbnail", "thumb",
            "image", "img", "pic", "picture", "photo", "url", "src", "content",
            "images", "imgs", "pics", "pictures", "photos", "image_list", "photo_list", "media",
        )
        for key in preferred_keys:
            if key in value:
                urls.extend(ruten_collect_image_urls(value.get(key), depth + 1))
        for key, nested in value.items():
            key_text = str(key).lower()
            if any(token in key_text for token in ("image", "img", "pic", "photo", "media", "thumb")):
                urls.extend(ruten_collect_image_urls(nested, depth + 1))
        return urls
    return []


def ruten_extract_image_url(value: Any, depth: int = 0) -> str:
    return ruten_best_image_url(ruten_collect_image_urls(value, depth))


def extract_ruten_public_image_urls_from_html(html: str, base_url: str) -> list[str]:
    urls: list[str] = []
    raw = html_unescape(str(html or "")).replace("\\/", "/")
    meta_patterns = (
        r'<meta[^>]+(?:property|name)=["\'](?:og:image|twitter:image|twitter:image:src)["\'][^>]+content=["\']([^"\']+)["\']',
        r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+(?:property|name)=["\'](?:og:image|twitter:image|twitter:image:src)["\']',
        r'<link[^>]+rel=["\']image_src["\'][^>]+href=["\']([^"\']+)["\']',
    )
    for pattern in meta_patterns:
        for match in re.findall(pattern, raw, flags=re.IGNORECASE):
            urls.append(urljoin(base_url, match))
    attr_pattern = r'(?:src|data-src|data-original|data-lazy|data-url|content|href)=["\']([^"\']+)["\']'
    for match in re.findall(attr_pattern, raw, flags=re.IGNORECASE):
        urls.append(urljoin(base_url, match))
    for match in re.findall(r'https?://[^\s"\'<>\)]+', raw):
        urls.append(match)
    for match in re.findall(r'//[^\s"\'<>\)]+', raw):
        urls.append("https:" + match)
    return [normalize_external_image_url(urljoin(base_url, url)) for url in urls if normalize_external_image_url(urljoin(base_url, url))]


_RUTEN_PUBLIC_IMAGE_CACHE: dict[str, str] = {}


def fetch_ruten_public_product_image_url(item_id: Any) -> str:
    item_text = clean_text(str(item_id))
    if not item_text:
        return ""
    if item_text in _RUTEN_PUBLIC_IMAGE_CACHE:
        return _RUTEN_PUBLIC_IMAGE_CACHE[item_text]
    url = make_ruten_item_web_url(item_text)
    if not url:
        _RUTEN_PUBLIC_IMAGE_CACHE[item_text] = ""
        return ""
    try:
        req = Request(url, headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) CardInventory/1.0 RutenImageFallback",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        })
        with urlopen(req, timeout=20) as resp:
            charset = resp.headers.get_content_charset() or "utf-8"
            html = resp.read().decode(charset, errors="replace")
        image_url = ruten_best_image_url(extract_ruten_public_image_urls_from_html(html, url))
    except Exception:
        image_url = ""
    _RUTEN_PUBLIC_IMAGE_CACHE[item_text] = image_url
    return image_url


def normalize_ruten_status(status: Any) -> str:
    text = clean_text(str(status)).lower()
    if text in ("", "undefined", "none", "null", "nan", "-", "--"):
        return "unknown"
    mapping = {
        "on": "on",
        "online": "online",
        "selling": "on",
        "sell": "on",
        "selling_now": "on",
        "出售中": "on",
        "上架中": "on",
        "off": "off",
        "offline": "offline",
        "close": "off",
        "closed": "off",
        "已下架": "off",
        "下架": "off",
        "out": "out",
        "out_of_stock": "out",
        "soldout": "out",
        "sold_out": "out",
        "缺貨": "out",
        "售完": "out",
    }
    return mapping.get(text, text or "unknown")


def is_unknown_ruten_status(status: Any) -> bool:
    return normalize_ruten_status(status) == "unknown"


def first_valid_ruten_status(data: Any, default: Any = "unknown") -> str:
    if isinstance(data, dict):
        for key in (
            "__query_status",
            "status",
            "item_status",
            "product_status",
            "sale_status",
            "selling_status",
            "goods_status",
            "state",
        ):
            if key in data:
                normalized = normalize_ruten_status(data.get(key))
                if normalized != "unknown":
                    return normalized
    return normalize_ruten_status(default)


def ruten_extract_spec_rows(data: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("spec_info", "spec_list", "specs", "spec", "sku_list", "skus"):
        rows = data.get(key)
        if isinstance(rows, list):
            return ruten_as_list(rows)
    return []


def ruten_remote_entries(summary: dict[str, Any], detail: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    base = dict(summary)
    detail_flat = ruten_flatten_product_data(detail or {})
    base.update({k: v for k, v in detail_flat.items() if v not in (None, "")})

    item_id = clean_text(str(ruten_pick(base, "item_id", "id", "product_id", "rt_item_id")))
    title = clean_text(str(ruten_pick(base, "name", "item_name", "title", "product_name")))
    status = first_valid_ruten_status(base, default=base.get("__query_status", "unknown"))
    base_qty = to_int(ruten_pick(base, "qty", "stock", "quantity", "item_qty", "remain_qty", default=0))
    base_price = to_int(ruten_pick(base, "price", "sell_price", "item_price", "discount_price", "original_price", default=0))
    base_custom_no = clean_text(str(ruten_pick(base, "custom_no", "seller_custom_no", "seller_item_no", "outer_id")))
    base_spec_id = clean_text(str(ruten_pick(base, "spec_id", "sku_id", "option_id")))
    base_description = normalize_ruten_description_lines(ruten_pick(base, "description", "item_description", "desc", default=""))
    base_class_id = normalize_ruten_class_id(ruten_pick(base, "class_id", "category_id", default=""))
    base_store_class_id = clean_text(str(ruten_pick(base, "store_class_id", "seller_class_id", default="")))
    base_condition = to_int(ruten_pick(base, "condition", default=0))
    base_stock_status = clean_text(str(ruten_pick(base, "stock_status", default="")))
    base_location_type = to_int(ruten_pick(base, "location_type", default=0))
    base_location = normalize_ruten_location_code(ruten_pick(base, "location", default=""))
    base_image_url = ruten_extract_image_url(base)

    entries: list[dict[str, Any]] = []
    specs = ruten_extract_spec_rows(base)
    if specs:
        for spec in specs:
            spec_id = clean_text(str(ruten_pick(spec, "spec_id", "id", "sku_id", "option_id", default=base_spec_id)))
            spec_name = clean_text(str(ruten_pick(spec, "spec_name", "name", "title", "option_name")))
            custom_no = clean_text(str(ruten_pick(spec, "custom_no", "seller_custom_no", "seller_item_no", "outer_id", default=base_custom_no)))
            qty = to_int(ruten_pick(spec, "qty", "stock", "quantity", "item_qty", "remain_qty", default=base_qty))
            price = to_int(ruten_pick(spec, "price", "sell_price", "item_price", "discount_price", "original_price", default=base_price))
            entry_title = title
            if spec_name and spec_name not in entry_title:
                entry_title = f"{title} / {spec_name}" if title else spec_name
            entries.append({
                "item_id": item_id,
                "spec_id": spec_id,
                "custom_no": custom_no,
                "title": entry_title,
                "status": status,
                "qty": qty,
                "price": price,
                "description": base_description,
                "class_id": base_class_id,
                "store_class_id": base_store_class_id,
                "condition": base_condition,
                "stock_status": base_stock_status,
                "location_type": base_location_type,
                "location": base_location,
                "image_url": base_image_url,
                "raw": {"summary": summary, "detail": detail_flat, "spec": spec},
            })
    else:
        entries.append({
            "item_id": item_id,
            "spec_id": base_spec_id,
            "custom_no": base_custom_no,
            "title": title,
            "status": status,
            "qty": base_qty,
            "price": base_price,
            "description": base_description,
            "class_id": base_class_id,
            "store_class_id": base_store_class_id,
            "condition": base_condition,
            "stock_status": base_stock_status,
            "location_type": base_location_type,
            "location": base_location,
            "image_url": base_image_url,
            "raw": {"summary": summary, "detail": detail_flat},
        })
    return [entry for entry in entries if entry.get("item_id")]


def parse_mtg_fields_from_ruten_custom_no(custom_no: str) -> dict[str, str]:
    text = clean_text(custom_no).upper()
    if not text:
        return {}
    parts = [part for part in re.split(r"[|/\\\-\s]+", text) if part]
    if len(parts) < 3 or parts[0] != "MTG":
        return {}
    result: dict[str, str] = {}
    if len(parts) > 1 and parts[1] not in {"SET", "NONE", "NA", "N/A"}:
        result["set_code"] = parts[1]
        result["edition"] = parts[1]
    if len(parts) > 2 and parts[2] not in {"NO", "NONE", "NA", "N/A"}:
        result["collector"] = parts[2]
    if len(parts) > 3 and parts[3] not in {"LANG", "NONE", "NA", "N/A"}:
        result["lang"] = parts[3].lower()
        result["lang_label"] = scryfall_language_label(result["lang"])
    return result


def parse_mtg_fields_from_ruten_description(description: Any) -> dict[str, str]:
    text = normalize_ruten_description_lines(description)
    result: dict[str, str] = {}
    if not text:
        return result
    key_map = {
        "卡名": "name",
        "英文名": "english_name",
        "系列": "edition",
        "系列代碼": "set_code",
        "collector": "collector",
        "稀有度": "rarity",
        "語言": "lang_label",
        "類型": "type",
    }
    for raw_line in text.splitlines():
        line = clean_text(raw_line)
        if not line:
            continue
        match = re.match(r"^([^:：]{1,20})\s*[:：]\s*(.+)$", line, flags=re.IGNORECASE)
        if not match:
            continue
        raw_key = clean_text(match.group(1))
        value = clean_text(match.group(2))
        mapped = key_map.get(raw_key) or key_map.get(raw_key.lower())
        if mapped and value:
            result[mapped] = value
    if result.get("set_code"):
        result["set_code"] = clean_text(result["set_code"]).upper()
    lang_value = result.get("lang_label", "")
    lang_match = re.search(r"\(([a-z]{2,3})\)", lang_value, flags=re.IGNORECASE)
    if lang_match:
        result["lang"] = lang_match.group(1).lower()
    elif lang_value.lower() in {"english", "en"}:
        result["lang"] = "en"
    return result


def scryfall_card_by_set_collector(set_code: str, collector: str, lang: str = "") -> dict[str, Any] | None:
    set_code = clean_text(set_code).lower()
    collector = clean_text(collector)
    lang = clean_text(lang).lower() or "en"
    if not set_code or not collector:
        return None
    candidates = []
    if lang:
        candidates.append(f"https://api.scryfall.com/cards/{quote(set_code)}/{quote(collector)}/{quote(lang)}")
    candidates.append(f"https://api.scryfall.com/cards/{quote(set_code)}/{quote(collector)}")
    for url in candidates:
        try:
            req = Request(url, headers={"User-Agent": "CardInventory/1.0 RutenImportScryfall"})
            with urlopen(req, timeout=20) as resp:
                payload = json.loads(resp.read().decode("utf-8"))
            if isinstance(payload, dict) and payload.get("object") == "card":
                return payload
        except Exception:
            continue
    return None


def scryfall_lookup_card_for_ruten_import(fields: dict[str, str]) -> dict[str, Any] | None:
    set_code = clean_text(fields.get("set_code", ""))
    collector = clean_text(fields.get("collector", ""))
    lang = clean_text(fields.get("lang", ""))
    card = scryfall_card_by_set_collector(set_code, collector, lang)
    if card:
        return card

    name = clean_text(fields.get("english_name", "") or fields.get("name", ""))
    if not name:
        return None
    filters = {"name": name, "set_code": set_code, "language": lang}
    try:
        data = search_scryfall_cards(filters, refresh_cache=False, max_cards=1)
        cards = data.get("cards") if isinstance(data, dict) else []
        if isinstance(cards, list) and cards:
            return cards[0]
    except Exception:
        return None
    return None


def apply_scryfall_card_to_imported_record(record: dict[str, Any], card: dict[str, Any]) -> bool:
    normalized = normalize_scryfall_card(card)
    changed = False
    for key in (
        "name", "english_name", "printed_name", "edition", "set_code", "rarity",
        "collector", "type", "oracle_type", "colors", "text", "url", "image_url",
        "source_url", "scryfall_id", "lang", "lang_label", "released_at", "layout", "legalities",
    ):
        value = normalized.get(key, "")
        if value and (not clean_text(str(record.get(key, ""))) or str(record.get("source", "")) == "ruten"):
            if record.get(key) != value:
                record[key] = value
                changed = True
    return changed


def enrich_ruten_import_record_with_scryfall(record: dict[str, Any], entry: dict[str, Any]) -> bool:
    fields: dict[str, str] = {}
    fields.update(parse_mtg_fields_from_ruten_custom_no(str(entry.get("custom_no", ""))))
    fields.update(parse_mtg_fields_from_ruten_description(entry.get("description", "")))
    title = clean_text(str(entry.get("title", "")))
    if title and not fields.get("name") and len(title) <= 120:
        fields["name"] = title

    changed = False
    ruten = ensure_ruten_item_fields(record)

    # 露天原商品圖備援：先從 API 回傳資料抓圖，抓不到時再讀公開商品頁的 og:image / 圖片網址。
    remote_image_url = ruten_extract_image_url(entry)
    if not remote_image_url:
        remote_image_url = fetch_ruten_public_product_image_url(entry.get("item_id", ""))
    if remote_image_url:
        ruten["remote_image_url"] = remote_image_url
        if not clean_text(str(record.get("image_url", ""))):
            record["image_url"] = remote_image_url
            ruten["image_source"] = "露天原商品圖"
            changed = True

    card = scryfall_lookup_card_for_ruten_import(fields)
    if not card:
        if remote_image_url:
            ruten["image_upload_error"] = ""
            ruten["match_note"] = "未能從 Scryfall 辨識卡圖，已改用露天原商品圖。"
            if changed:
                record["updated_at"] = now_text()
            return changed
        if not clean_text(str(record.get("image_url", ""))):
            ruten["image_upload_error"] = "反向匯入未能從商品資料辨識 Scryfall 卡圖，也沒有取得露天原商品圖"
        return changed

    changed = apply_scryfall_card_to_imported_record(record, card) or changed
    if clean_text(str(record.get("image_url", ""))):
        ruten["image_upload_error"] = ""
    if changed:
        ruten["match_note"] = "已依露天商品說明 / 自用料號自動補齊 Scryfall 卡片資料與卡圖。"
        record["updated_at"] = now_text()
    return changed


def make_mtg_inventory_item_from_ruten(entry: dict[str, Any]) -> dict[str, Any]:
    title = clean_text(str(entry.get("title", "")))
    item_id = clean_text(str(entry.get("item_id", "")))
    custom_no = clean_text(str(entry.get("custom_no", "")))
    parsed = parse_mtg_fields_from_ruten_custom_no(custom_no)
    parsed.update(parse_mtg_fields_from_ruten_description(entry.get("description", "")))
    name = parsed.get("name") or parsed.get("english_name") or title or f"露天商品 {item_id}"
    qty = max(0, to_int(entry.get("qty", 0)))
    price = max(0, to_int(entry.get("price", 0)))

    record = {
        "id": uuid.uuid4().hex,
        "source": "ruten",
        "quantity": qty,
        "name": name,
        "english_name": parsed.get("english_name", ""),
        "printed_name": parsed.get("printed_name", ""),
        "edition": parsed.get("edition", ""),
        "set_code": parsed.get("set_code", ""),
        "rarity": parsed.get("rarity", ""),
        "collector": parsed.get("collector", ""),
        "type": parsed.get("type", ""),
        "oracle_type": "",
        "colors": "",
        "lang": parsed.get("lang", ""),
        "lang_label": parsed.get("lang_label", ""),
        "price": str(price) if price > 0 else "",
        "text": "",
        "url": "",
        "image_url": ruten_extract_image_url(entry),
        "source_url": "",
        "scryfall_id": "",
        "released_at": "",
        "layout": "",
        "legalities": "",
        "note": "露天反向匯入，請確認 MTG卡名、Set、Collector、語言與卡況。",
        "ruten": default_ruten_item_fields(),
        "created_at": now_text(),
        "updated_at": now_text(),
    }
    ruten = ensure_ruten_item_fields(record)
    ruten.update({
        "enabled": True,
        "item_id": item_id,
        "spec_id": clean_text(str(entry.get("spec_id", ""))),
        "custom_no": custom_no or make_ruten_custom_no(record),
        "title": title or name,
        "price": price,
        "description": normalize_ruten_description_lines(entry.get("description", "")),
        "status": normalize_ruten_status(entry.get("status", "unknown")),
        "listing_qty": qty,
        "remote_stock": qty,
        "match_status": "待確認",
        "match_note": "露天反向匯入，請確認是否對應正確 MTG 庫存。",
        "last_sync_at": now_text(),
        "last_error": "",
    })
    return record




def migrate_legacy_config_files() -> None:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    legacy_pairs = [
        (LEGACY_DB_PATH, DB_PATH),
        (BASE_DIR / "scryfall_sets_cache.json", CONFIG_DIR / "scryfall_sets_cache.json"),
        (BASE_DIR / "scryfall_custom_sets.json", CONFIG_DIR / "scryfall_custom_sets.json"),
    ]
    for src, dst in legacy_pairs:
        try:
            if src.exists() and not dst.exists():
                shutil.copy2(src, dst)
        except Exception:
            pass


def load_ruten_secrets() -> dict[str, Any]:
    if not RUTEN_SECRET_PATH.exists():
        return {}
    try:
        with RUTEN_SECRET_PATH.open("r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def save_ruten_secrets(settings: dict[str, Any]) -> None:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    data = {
        "api_key": clean_text(str(settings.get("api_key", ""))),
        "secret_key": clean_text(str(settings.get("secret_key", ""))),
        "salt_key": clean_text(str(settings.get("salt_key", ""))),
        "updated_at": now_text(),
    }
    tmp_path = RUTEN_SECRET_PATH.with_suffix(".tmp")
    with tmp_path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    tmp_path.replace(RUTEN_SECRET_PATH)


def merge_ruten_secrets_into_db(db: dict[str, Any]) -> None:
    settings = ensure_ruten_settings(db)
    file_secrets = load_ruten_secrets()
    old_has_secret = any(clean_text(str(settings.get(key, ""))) for key in ("api_key", "secret_key", "salt_key"))
    if file_secrets:
        for key in ("api_key", "secret_key", "salt_key"):
            if file_secrets.get(key):
                settings[key] = file_secrets.get(key, "")
    elif old_has_secret:
        save_ruten_secrets(settings)


def db_without_ruten_secrets(db: dict[str, Any]) -> dict[str, Any]:
    try:
        safe_db = json.loads(json.dumps(db, ensure_ascii=False))
    except Exception:
        safe_db = dict(db)
    settings = safe_db.get("ruten_settings")
    if isinstance(settings, dict):
        for key in ("api_key", "secret_key", "salt_key"):
            settings.pop(key, None)
    return safe_db



def update_ruten_pairing_conflicts(db: dict[str, Any]) -> None:
    seen: dict[tuple[str, str], dict[str, Any]] = {}
    for record in db.get("mtg_inventory", []):
        ruten = ensure_ruten_item_fields(record)
        item_id = clean_text(str(ruten.get("item_id", "")))
        spec_id = clean_text(str(ruten.get("spec_id", "")))
        if not item_id:
            continue
        key = (item_id, spec_id)
        if key in seen:
            ruten["match_status"] = "衝突"
            ruten["match_note"] = "有其他 MTG庫存使用相同露天商品ID / 規格ID，請手動確認。"
            other_ruten = ensure_ruten_item_fields(seen[key])
            other_ruten["match_status"] = "衝突"
            other_ruten["match_note"] = "有其他 MTG庫存使用相同露天商品ID / 規格ID，請手動確認。"
        else:
            seen[key] = record
            if ruten.get("match_status") in ("", "未配對"):
                ruten["match_status"] = "已配對"
                ruten["match_note"] = "已綁定露天商品ID。"

def make_default_db() -> dict[str, Any]:
    return {
        "categories": DEFAULT_CATEGORIES[:],
        "buy_methods": DEFAULT_BUY_METHODS[:],
        "cards": [],
        "sales": [],
        "mtg_inventory": [],
        "ruten_settings": default_ruten_settings(),
        "ruten_notifications": [],
        "ruten_order_processing": {},
    }


def load_db() -> dict[str, Any]:
    migrate_legacy_config_files()
    if not DB_PATH.exists():
        db = make_default_db()
        merge_ruten_secrets_into_db(db)
        return db

    try:
        with DB_PATH.open("r", encoding="utf-8") as f:
            db = json.load(f)
    except Exception:
        backup_path = DB_PATH.with_suffix(f".broken_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
        shutil.copy2(DB_PATH, backup_path)
        QMessageBox.warning(
            None,
            "JSON 讀取失敗",
            f"原本的 card_inventory.json 無法讀取，已備份成：\n{backup_path}\n\n系統會先建立新的空資料庫。",
        )
        return make_default_db()

    db.setdefault("categories", DEFAULT_CATEGORIES[:])
    db.setdefault("buy_methods", DEFAULT_BUY_METHODS[:])
    db.setdefault("cards", [])
    db.setdefault("sales", [])
    db.setdefault("mtg_inventory", [])
    db.setdefault("ruten_notifications", [])
    db.setdefault("ruten_order_processing", {})
    if not isinstance(db.get("ruten_order_processing"), dict):
        db["ruten_order_processing"] = {}
    ensure_ruten_settings(db)
    merge_ruten_secrets_into_db(db)

    for record in db.get("mtg_inventory", []):
        ensure_ruten_item_fields(record)
    update_ruten_pairing_conflicts(db)

    for category in DEFAULT_CATEGORIES:
        if category not in db["categories"]:
            db["categories"].append(category)
    for method in DEFAULT_BUY_METHODS:
        if method not in db["buy_methods"]:
            db["buy_methods"].append(method)

    # 舊版資料相容：舊版只有 grade_company/grade_score 二選一；
    # 新版 PSA 與 BGS 是兩組獨立欄位。
    for record in list(db.get("cards", [])) + list(db.get("sales", [])):
        legacy_company = str(record.get("grade_company", "無"))
        legacy_score = str(record.get("grade_score", "")).strip()

        if "psa_enabled" not in record:
            record["psa_enabled"] = legacy_company == "PSA"
        if "psa_score" not in record:
            record["psa_score"] = legacy_score if legacy_company == "PSA" else ""

        if "bgs_enabled" not in record:
            record["bgs_enabled"] = legacy_company == "BGS"
        if "bgs_score" not in record:
            record["bgs_score"] = legacy_score if legacy_company == "BGS" else ""

    return db


def save_db(db: dict[str, Any]) -> None:
    IMAGE_DIR.mkdir(parents=True, exist_ok=True)
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    settings = db.get("ruten_settings")
    if isinstance(settings, dict) and any(clean_text(str(settings.get(key, ""))) for key in ("api_key", "secret_key", "salt_key")):
        save_ruten_secrets(settings)
    tmp_path = DB_PATH.with_suffix(".tmp")
    with tmp_path.open("w", encoding="utf-8") as f:
        json.dump(db_without_ruten_secrets(db), f, ensure_ascii=False, indent=2)
    tmp_path.replace(DB_PATH)


def copy_image_to_library(source_path: str) -> str:
    if not source_path:
        return ""

    src = Path(source_path)
    if not src.exists():
        return ""

    IMAGE_DIR.mkdir(parents=True, exist_ok=True)
    suffix = src.suffix.lower() or ".jpg"
    dst_name = f"{uuid.uuid4().hex}{suffix}"
    dst = IMAGE_DIR / dst_name
    shutil.copy2(src, dst)
    return str(Path("card_images") / dst_name)


def absolute_image_path(relative_or_abs: str) -> Path:
    if not relative_or_abs:
        return Path()
    path = Path(relative_or_abs)
    if path.is_absolute():
        return path
    return BASE_DIR / path


def load_image_preview(label: QLabel, image_path: str, empty_text: str = "無圖片") -> None:
    label.setAlignment(Qt.AlignCenter)
    label.setMinimumSize(180, 180)
    label.setStyleSheet("border: 1px solid #888; background: #fafafa; color: #666;")

    path = absolute_image_path(image_path)
    if not image_path or not path.exists():
        label.setPixmap(QPixmap())
        label.setText(empty_text)
        return

    pixmap = QPixmap(str(path))
    if pixmap.isNull():
        label.setPixmap(QPixmap())
        label.setText("圖片讀取失敗")
        return

    label.setText("")
    label.setPixmap(pixmap.scaled(220, 220, Qt.KeepAspectRatio, Qt.SmoothTransformation))



def ruten_upload_cache_dir() -> Path:
    path = IMAGE_DIR / "ruten_upload"
    path.mkdir(parents=True, exist_ok=True)
    return path


def local_card_image_candidate(record: dict[str, Any]) -> Path | None:
    image_path = clean_text(str(record.get("image_path", "")))
    if image_path:
        path = absolute_image_path(image_path)
        if path.exists() and path.is_file():
            return path
    return None


def infer_image_extension(content_type: str, url: str = "") -> str:
    content_type = clean_text(content_type).lower().split(";", 1)[0]
    if content_type in {"image/jpeg", "image/jpg"}:
        return ".jpg"
    if content_type == "image/png":
        return ".png"
    lower_url = url.lower().split("?", 1)[0]
    for ext in (".jpg", ".jpeg", ".png"):
        if lower_url.endswith(ext):
            return ext
    return ".jpg"


def download_record_image_for_ruten(record: dict[str, Any]) -> Path | None:
    image_url = clean_text(str(record.get("image_url", "")))
    if not image_url:
        return None
    cache_dir = ruten_upload_cache_dir()
    key_source = clean_text(str(record.get("scryfall_id", ""))) or clean_text(str(record.get("id", ""))) or image_url
    key = hashlib.sha1(key_source.encode("utf-8", errors="ignore")).hexdigest()[:16]
    request = Request(image_url, headers={"User-Agent": "CardInventory/1.0 RutenImageUpload"})
    with urlopen(request, timeout=30) as response:
        content_type = response.headers.get("Content-Type", "")
        data = response.read()
    ext = infer_image_extension(content_type, image_url)
    if ext.lower() not in {".jpg", ".jpeg", ".png"}:
        raise RuntimeError("露天圖片只支援 JPG/JPEG/PNG，Scryfall 圖片格式不支援。")
    path = cache_dir / f"{key}{ext}"
    path.write_bytes(data)
    return path


def prepare_ruten_image_file(record: dict[str, Any]) -> Path | None:
    source = local_card_image_candidate(record)
    if source is None:
        source = download_record_image_for_ruten(record)
    if source is None or not source.exists():
        return None

    ext = source.suffix.lower()
    if ext not in {".jpg", ".jpeg", ".png"}:
        raise RuntimeError("露天圖片只支援 JPG/JPEG/PNG。")

    if source.stat().st_size <= 2 * 1024 * 1024:
        return source

    pixmap = QPixmap(str(source))
    if pixmap.isNull():
        raise RuntimeError("圖片超過 2MB，且無法重新壓縮。")
    max_side = 800
    if pixmap.width() > max_side or pixmap.height() > max_side:
        pixmap = pixmap.scaled(max_side, max_side, Qt.KeepAspectRatio, Qt.SmoothTransformation)
    cache_dir = ruten_upload_cache_dir()
    out = cache_dir / f"{source.stem}_ruten.jpg"
    for quality in (92, 85, 78, 70, 62):
        if pixmap.save(str(out), "JPG", quality) and out.exists() and out.stat().st_size <= 2 * 1024 * 1024:
            return out
    raise RuntimeError("圖片超過露天 2MB 限制，重新壓縮後仍然太大。")




def card_thumbnail_cache_path(record: dict[str, Any]) -> Path:
    source = clean_text(str(record.get("scryfall_id", ""))) or clean_text(str(record.get("id", ""))) or clean_text(str(record.get("image_url", ""))) or clean_text(str(record.get("name", "")))
    key = hashlib.sha1(source.encode("utf-8", errors="ignore")).hexdigest()[:20] if source else uuid.uuid4().hex[:20]
    path = IMAGE_DIR / "thumbnails" / f"{key}.jpg"
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def load_card_pixmap_for_record(record: dict[str, Any], max_width: int = 72, max_height: int = 96, allow_remote: bool = True) -> QPixmap:
    source = local_card_image_candidate(record)
    if source is not None:
        pixmap = QPixmap(str(source))
        if not pixmap.isNull():
            return pixmap.scaled(max_width, max_height, Qt.KeepAspectRatio, Qt.SmoothTransformation)

    cache_path = card_thumbnail_cache_path(record)
    if cache_path.exists():
        pixmap = QPixmap(str(cache_path))
        if not pixmap.isNull():
            return pixmap.scaled(max_width, max_height, Qt.KeepAspectRatio, Qt.SmoothTransformation)

    image_url = clean_text(str(record.get("image_url", "")))
    if allow_remote and image_url:
        request = Request(image_url, headers={"User-Agent": "CardInventory/1.0 (local desktop inventory app)"})
        with urlopen(request, timeout=8) as response:
            data = response.read()
        pixmap = QPixmap()
        if pixmap.loadFromData(data) and not pixmap.isNull():
            scaled = pixmap.scaled(max_width, max_height, Qt.KeepAspectRatio, Qt.SmoothTransformation)
            scaled.save(str(cache_path), "JPG", 88)
            return scaled

    return QPixmap()


def make_card_thumbnail_label(record: dict[str, Any], max_width: int = 64, max_height: int = 88) -> QLabel:
    label = QLabel("無圖")
    label.setAlignment(Qt.AlignCenter)
    label.setMinimumSize(max_width + 8, max_height + 8)
    label.setStyleSheet("border: 1px solid #555; background: #222; color: #aaa;")
    try:
        pixmap = load_card_pixmap_for_record(record, max_width, max_height, allow_remote=True)
        if not pixmap.isNull():
            label.setText("")
            label.setPixmap(pixmap)
    except Exception:
        label.setText("載入失敗")
    return label





class CardGridTile(QWidget):
    def __init__(self, record: dict[str, Any], title: str, subtitle: str, on_click: object, checked: bool = False, selected: bool = False, parent: QWidget | None = None):
        super().__init__(parent)
        self._on_click = on_click
        self._selected = bool(selected)
        self.setObjectName("CardGridTileSelected" if self._selected else "CardGridTile")
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setMinimumWidth(180)
        self.setMaximumWidth(210)
        self.setStyleSheet("""
            QWidget#CardGridTile {
                border: 1px solid #444;
                border-radius: 7px;
                background: #2a2a2a;
            }
            QWidget#CardGridTileSelected {
                border: 4px solid #4da3ff;
                border-radius: 9px;
                background: #20364f;
            }
            QWidget#CardGridTile QLabel, QWidget#CardGridTileSelected QLabel {
                border: none;
                background: transparent;
                color: #eee;
            }
        """)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(6)
        if self._selected:
            selected_label = QLabel("目前選取")
            selected_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            selected_label.setStyleSheet("color: #8ecbff; font-weight: bold; background: transparent;")
            layout.addWidget(selected_label)
        image = make_card_thumbnail_label(record, 160, 224)
        image.setMinimumSize(168, 232)
        title_label = QLabel(title or "未命名")
        title_label.setWordWrap(True)
        title_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        subtitle_label = QLabel(subtitle or "")
        subtitle_label.setWordWrap(True)
        subtitle_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        subtitle_label.setStyleSheet("color: #bbb;")
        layout.addWidget(image)
        layout.addWidget(title_label)
        layout.addWidget(subtitle_label)
        if checked:
            mark = QLabel("✓ 已勾選")
            mark.setAlignment(Qt.AlignmentFlag.AlignCenter)
            mark.setStyleSheet("color: #8fd18f; font-weight: bold; background: transparent;")
            layout.addWidget(mark)

    def mousePressEvent(self, event: object) -> None:
        if callable(self._on_click):
            self._on_click()
        super().mousePressEvent(event)


def clear_qt_layout(layout: QGridLayout) -> None:
    while layout.count():
        item = layout.takeAt(0)
        widget = item.widget()
        if widget is not None:
            widget.deleteLater()
        child = item.layout()
        if child is not None:
            clear_qt_layout(child)  # type: ignore[arg-type]

def load_card_record_preview(label: QLabel, record: dict[str, Any] | None, empty_text: str = "無圖片") -> None:
    label.setAlignment(Qt.AlignCenter)
    label.setMinimumSize(180, 240)
    label.setStyleSheet("border: 1px solid #888; background: #fafafa; color: #666;")
    if not record:
        label.setPixmap(QPixmap())
        label.setText(empty_text)
        return
    try:
        pixmap = load_card_pixmap_for_record(record, 220, 300, allow_remote=True)
        if pixmap.isNull():
            raise RuntimeError("圖片資料無法載入")
        label.setText("")
        label.setPixmap(pixmap)
    except Exception:
        label.setPixmap(QPixmap())
        label.setText("圖片載入失敗")


def card_grade_text(card: dict[str, Any]) -> str:
    # PSA / BGS 是獨立標籤，不是單選欄位。
    # 同時保留舊版 grade_company/grade_score 的讀取相容性。
    legacy_company = str(card.get("grade_company", "無"))
    legacy_score = str(card.get("grade_score", "")).strip()

    psa_enabled = bool(card.get("psa_enabled", False)) or legacy_company == "PSA"
    bgs_enabled = bool(card.get("bgs_enabled", False)) or legacy_company == "BGS"
    psa_score = str(card.get("psa_score", legacy_score if legacy_company == "PSA" else "")).strip()
    bgs_score = str(card.get("bgs_score", legacy_score if legacy_company == "BGS" else "")).strip()

    parts = []
    if psa_enabled:
        parts.append(f"PSA {psa_score}" if psa_score else "PSA")
    if bgs_enabled:
        parts.append(f"BGS {bgs_score}" if bgs_score else "BGS")

    return " / ".join(parts) if parts else "無"


def card_unit_cost(card: dict[str, Any]) -> float:
    qty = int(card.get("buy_quantity", 0) or 0)
    total = float(card.get("buy_total", 0) or 0)
    if qty <= 0:
        return 0.0
    return total / qty


def sale_profit(card: dict[str, Any], qty: int, sell_total: float, fee_total: float) -> tuple[float, float, float]:
    buy_cost = card_unit_cost(card) * qty
    profit = sell_total - buy_cost - fee_total
    roi = (profit / buy_cost * 100.0) if buy_cost > 0 else 0.0
    return buy_cost, profit, roi


class CategoryDialog(QDialog):
    def __init__(self, categories: list[str], used_categories: set[str], parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.setWindowTitle("編輯分類")
        self.resize(420, 420)

        self.categories = categories[:]
        self.used_categories = used_categories
        self.rename_map: dict[str, str] = {}

        self.list_widget = QListWidget()
        self.add_edit = QLineEdit()
        self.add_edit.setPlaceholderText("輸入新分類名稱")

        add_btn = QPushButton("新增")
        rename_btn = QPushButton("重新命名")
        remove_btn = QPushButton("移除")

        add_btn.clicked.connect(self.add_category)
        rename_btn.clicked.connect(self.rename_category)
        remove_btn.clicked.connect(self.remove_category)

        input_row = QHBoxLayout()
        input_row.addWidget(self.add_edit, 1)
        input_row.addWidget(add_btn)

        action_row = QHBoxLayout()
        action_row.addWidget(rename_btn)
        action_row.addWidget(remove_btn)
        action_row.addStretch(1)

        button_box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        button_box.accepted.connect(self.accept)
        button_box.rejected.connect(self.reject)

        layout = QVBoxLayout(self)
        layout.addWidget(QLabel("分類清單："))
        layout.addWidget(self.list_widget, 1)
        layout.addLayout(input_row)
        layout.addLayout(action_row)
        layout.addWidget(QLabel("注意：已被庫存使用的分類不能直接移除；可以改名，系統會同步更新既有庫存。"))
        layout.addWidget(button_box)

        self.refresh_list()

    def refresh_list(self) -> None:
        self.list_widget.clear()
        self.list_widget.addItems(self.categories)

    def add_category(self) -> None:
        name = self.add_edit.text().strip()
        if not name:
            QMessageBox.warning(self, "無法新增", "請輸入分類名稱。")
            return
        if name in self.categories:
            QMessageBox.warning(self, "無法新增", "這個分類已經存在。")
            return
        self.categories.append(name)
        self.add_edit.clear()
        self.refresh_list()

    def selected_category(self) -> str:
        item = self.list_widget.currentItem()
        return item.text() if item else ""

    def rename_category(self) -> None:
        old_name = self.selected_category()
        if not old_name:
            QMessageBox.warning(self, "無法改名", "請先選擇一個分類。")
            return

        new_name, ok = QInputDialog.getText(self, "重新命名分類", "新分類名稱：", text=old_name)
        if not ok:
            return
        new_name = new_name.strip()
        if not new_name:
            QMessageBox.warning(self, "無法改名", "分類名稱不可空白。")
            return
        if new_name != old_name and new_name in self.categories:
            QMessageBox.warning(self, "無法改名", "這個分類已經存在。")
            return

        idx = self.categories.index(old_name)
        self.categories[idx] = new_name

        for original, current in list(self.rename_map.items()):
            if current == old_name:
                self.rename_map[original] = new_name
        if old_name not in self.rename_map:
            self.rename_map[old_name] = new_name

        self.refresh_list()
        self.list_widget.setCurrentRow(idx)

    def remove_category(self) -> None:
        name = self.selected_category()
        if not name:
            QMessageBox.warning(self, "無法移除", "請先選擇一個分類。")
            return

        protected = set(self.used_categories)
        for original, current in self.rename_map.items():
            if original in self.used_categories:
                protected.add(current)

        if name in protected:
            QMessageBox.warning(self, "無法移除", "這個分類已經有庫存紀錄使用，請先改名或清空相關庫存後再移除。")
            return

        if len(self.categories) <= 1:
            QMessageBox.warning(self, "無法移除", "至少需要保留一個分類。")
            return

        if QMessageBox.question(self, "確認移除", f"確定要移除分類「{name}」？") != QMessageBox.Yes:
            return

        self.categories.remove(name)
        self.refresh_list()

    def accept(self) -> None:
        cleaned = []
        for category in self.categories:
            category = category.strip()
            if category and category not in cleaned:
                cleaned.append(category)
        if not cleaned:
            QMessageBox.warning(self, "無法儲存", "至少需要一個分類。")
            return
        self.categories = cleaned
        super().accept()


class ScryfallCustomSetsDialog(QDialog):
    def __init__(self, custom_sets: list[dict[str, Any]], parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.setWindowTitle("管理自訂系列")
        self.resize(560, 460)

        self.custom_sets: list[dict[str, Any]] = []
        for raw in custom_sets:
            item = normalize_scryfall_set({**raw, "custom": True})
            if not item["code"] or not item["name"]:
                continue
            item["_origin_code"] = item["code"]
            item["_origin_name"] = item["name"]
            self.custom_sets.append(item)

        self.visible_sets: list[dict[str, Any]] = []
        self.inventory_update_map: dict[str, dict[str, str]] = {}

        self.list_widget = QListWidget()
        self.list_widget.itemDoubleClicked.connect(lambda _item: self.edit_custom_set())

        add_btn = QPushButton("新增")
        edit_btn = QPushButton("修改")
        remove_btn = QPushButton("移除")
        add_btn.clicked.connect(self.add_custom_set)
        edit_btn.clicked.connect(self.edit_custom_set)
        remove_btn.clicked.connect(self.remove_custom_set)

        action_row = QHBoxLayout()
        action_row.addWidget(add_btn)
        action_row.addWidget(edit_btn)
        action_row.addWidget(remove_btn)
        action_row.addStretch(1)

        button_box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        button_box.button(QDialogButtonBox.Ok).setText("儲存")
        button_box.button(QDialogButtonBox.Cancel).setText("取消")
        button_box.accepted.connect(self.accept)
        button_box.rejected.connect(self.reject)

        note = QLabel(
            "這裡只管理你手動新增的自訂系列；Scryfall 官方系列清單不能在本機修改。\n"
            "若修改 Set Code，已使用舊 Set Code 的 MTG庫存也會同步更新。"
        )
        note.setWordWrap(True)

        layout = QVBoxLayout(self)
        layout.addWidget(QLabel("自訂系列清單："))
        layout.addWidget(self.list_widget, 1)
        layout.addLayout(action_row)
        layout.addWidget(note)
        layout.addWidget(button_box)

        self.refresh_list()

    def refresh_list(self, selected_code: str = "") -> None:
        self.visible_sets = sorted(
            self.custom_sets,
            key=lambda x: (str(x.get("name", "")).lower(), str(x.get("code", "")).lower()),
        )
        self.list_widget.clear()
        target_row = -1
        for row, item in enumerate(self.visible_sets):
            label = f"{item.get('name', '')} ({str(item.get('code', '')).upper()})"
            self.list_widget.addItem(label)
            if selected_code and str(item.get("code", "")).lower() == selected_code.lower():
                target_row = row
        if target_row >= 0:
            self.list_widget.setCurrentRow(target_row)

    def selected_set(self) -> dict[str, Any] | None:
        row = self.list_widget.currentRow()
        if row < 0 or row >= len(self.visible_sets):
            return None
        return self.visible_sets[row]

    def validate_code_name(self, code: str, name: str, editing_item: dict[str, Any] | None = None) -> tuple[str, str] | None:
        code = clean_text(code).lower()
        name = clean_text(name)
        if not re.fullmatch(r"[a-z0-9]{2,8}", code):
            QMessageBox.warning(self, "無法儲存系列", "系列代碼只可使用英數字，長度建議 2～8 碼。")
            return None
        if not name:
            QMessageBox.warning(self, "無法儲存系列", "系列名稱不可空白。")
            return None
        for item in self.custom_sets:
            if editing_item is not None and item is editing_item:
                continue
            if str(item.get("code", "")).lower() == code:
                QMessageBox.warning(self, "無法儲存系列", "這個 Set Code 已經存在於自訂系列。")
                return None
        return code, name

    def add_custom_set(self) -> None:
        code, ok = QInputDialog.getText(self, "新增系列", "系列代碼 / Set Code：\n例如 STH、FIN、EOE")
        if not ok:
            return
        name, ok = QInputDialog.getText(self, "新增系列", "系列名稱 / Set Name：", text=clean_text(code).upper())
        if not ok:
            return
        validated = self.validate_code_name(code, name)
        if not validated:
            return
        code, name = validated
        item = make_custom_scryfall_set(code, name)
        item["_origin_code"] = ""
        item["_origin_name"] = ""
        self.custom_sets.append(item)
        self.refresh_list(selected_code=code)

    def edit_custom_set(self) -> None:
        item = self.selected_set()
        if not item:
            QMessageBox.warning(self, "無法修改", "請先選擇一個自訂系列。")
            return
        old_code = str(item.get("code", "")).lower()
        old_name = str(item.get("name", ""))

        new_code, ok = QInputDialog.getText(self, "修改系列", "系列代碼 / Set Code：", text=old_code.upper())
        if not ok:
            return
        new_name, ok = QInputDialog.getText(self, "修改系列", "系列名稱 / Set Name：", text=old_name)
        if not ok:
            return
        validated = self.validate_code_name(new_code, new_name, editing_item=item)
        if not validated:
            return
        code, name = validated
        item.update(make_custom_scryfall_set(code, name))
        item["_origin_code"] = item.get("_origin_code") or old_code
        item["_origin_name"] = item.get("_origin_name") or old_name
        self.refresh_list(selected_code=code)

    def remove_custom_set(self) -> None:
        item = self.selected_set()
        if not item:
            QMessageBox.warning(self, "無法移除", "請先選擇一個自訂系列。")
            return
        if QMessageBox.question(
            self,
            "確認移除",
            f"確定要移除自訂系列？\n\n{item.get('name', '')} ({str(item.get('code', '')).upper()})\n\n"
            "已經存在於 MTG庫存的卡片資料不會被刪除。",
        ) != QMessageBox.Yes:
            return
        self.custom_sets.remove(item)
        self.refresh_list()

    def accept(self) -> None:
        cleaned_by_code: dict[str, dict[str, Any]] = {}
        self.inventory_update_map = {}

        for raw in self.custom_sets:
            item = normalize_scryfall_set({**raw, "custom": True})
            code = str(item.get("code", "")).lower()
            name = str(item.get("name", ""))
            if not code or not name:
                continue
            if code in cleaned_by_code:
                QMessageBox.warning(self, "無法儲存", f"自訂系列代碼重複：{code.upper()}")
                return

            origin_code = str(raw.get("_origin_code", code)).lower()
            origin_name = str(raw.get("_origin_name", name))
            if origin_code and (origin_code != code or origin_name != name):
                self.inventory_update_map[origin_code] = {
                    "new_code": code,
                    "new_name": name,
                    "old_name": origin_name,
                }
            cleaned_by_code[code] = item

        self.custom_sets = sorted(cleaned_by_code.values(), key=lambda x: (str(x.get("name", "")).lower(), str(x.get("code", ""))))
        super().accept()



class ScryfallSetTreeDialog(QDialog):
    CHILD_SUFFIX_CANDIDATES = [
        (" Commander Tokens", " Commander"),
        (" Eternal Tokens", " Eternal"),
        (" Eternal Front Cards", " Eternal"),
        (" Commander Promos", " Commander"),
        (" Commander", ""),
        (" Tokens", ""),
        (" Promos", ""),
        (" Promo", ""),
        (" Art Series", ""),
        (" Source Material", ""),
        (" Mystical Archive", ""),
        (" Minigames", ""),
        (" Extras", ""),
        (" Front Cards", ""),
        (" Eternal", ""),
    ]

    def __init__(self, sets: list[dict[str, Any]], current_code: str = "", parent: QWidget | None = None):
        super().__init__(parent)
        self.setWindowTitle("選擇 Scryfall 系列")
        self.resize(760, 680)
        self.sets = [normalize_scryfall_set(item) for item in sets if isinstance(item, dict)]
        self.current_code = clean_text(current_code).lower()
        self.selected_code = ""
        self.selected_label = "全部系列"
        self._set_icon_cache: dict[str, QIcon] = {}


        root = QVBoxLayout(self)
        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("搜尋系列名稱 / Set Code / 日期，例如：Marvel、MSC、2026")
        self.search_edit.textChanged.connect(self.populate_tree)
        root.addWidget(self.search_edit)

        tree_tools = QHBoxLayout()
        self.expand_all_btn = QPushButton("展開全部")
        self.expand_all_btn.clicked.connect(self.tree_expand_all)
        self.collapse_all_btn = QPushButton("收合全部")
        self.collapse_all_btn.clicked.connect(self.tree_collapse_all)
        self.cache_icons_btn = QPushButton("下載/更新系列圖標")
        self.cache_icons_btn.clicked.connect(self.cache_set_icons)
        tree_tools.addWidget(self.expand_all_btn)
        tree_tools.addWidget(self.collapse_all_btn)
        tree_tools.addWidget(self.cache_icons_btn)
        tree_tools.addStretch(1)
        root.addLayout(tree_tools)

        self.tree = QTreeWidget()
        self.tree.setColumnCount(3)
        self.tree.setHeaderLabels(["系列", "代碼", "發售日"])
        self.tree.setAlternatingRowColors(True)
        self.tree.setRootIsDecorated(True)
        self.tree.setItemsExpandable(True)
        self.tree.setIndentation(26)
        self.tree.setIconSize(QSize(18, 18))
        self.tree.itemDoubleClicked.connect(self.accept_current_item)
        self.tree.itemSelectionChanged.connect(self.update_selected_from_tree)
        root.addWidget(self.tree, 1)

        hint = QLabel("系列會依 Scryfall 類似方式分層：主系列底下會展開 Commander、Tokens、Promos、Art Series 等子系列；圖標只讀取本機快取，不會在開啟視窗時下載；雙擊或按確定套用。")
        hint.setWordWrap(True)
        root.addWidget(hint)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept_current_item)
        buttons.rejected.connect(self.reject)
        root.addWidget(buttons)

        self.populate_tree()

    def tree_expand_all(self) -> None:
        if hasattr(self, "tree"):
            self.tree.expandAll()

    def tree_collapse_all(self) -> None:
        if not hasattr(self, "tree"):
            return
        self.tree.collapseAll()
        if self.tree.topLevelItemCount() > 0:
            self.tree.topLevelItem(0).setExpanded(False)

    def _matches_filter(self, item: dict[str, Any], text: str) -> bool:
        if not text:
            return True
        haystack = " ".join([
            str(item.get("name", "")),
            str(item.get("code", "")),
            str(item.get("released_at", "")),
            str(item.get("set_type", "")),
            str(item.get("block", "")),
        ]).lower()
        return text.lower() in haystack

    def _set_icon_cache_dir(self) -> Path:
        path = CONFIG_DIR / "scryfall_set_icons"
        path.mkdir(parents=True, exist_ok=True)
        return path

    def _lighten_svg_icon(self, svg_text: str) -> str:
        text = svg_text
        text = re.sub(r'fill="[^"]*"', 'fill="#d8d8d8"', text, flags=re.IGNORECASE)
        text = re.sub(r"fill='[^']*'", "fill='#d8d8d8'", text, flags=re.IGNORECASE)
        text = re.sub(r'stroke="[^"]*"', 'stroke="#d8d8d8"', text, flags=re.IGNORECASE)
        text = re.sub(r"stroke='[^']*'", "stroke='#d8d8d8'", text, flags=re.IGNORECASE)
        if "fill=" not in text[:300].lower():
            text = re.sub(r"<svg([^>]*)>", r'<svg\1 fill="#d8d8d8">', text, count=1, flags=re.IGNORECASE)
        return text

    def _set_icon_for_item(self, item: dict[str, Any]) -> QIcon:
        """Return cached set icon only.

        The tree must open instantly.  Do not download icons here, because doing
        hundreds of network requests while building the dialog freezes the UI.
        Use cache_set_icons() when the user explicitly wants to download/update
        the icon cache.
        """
        code = clean_text(str(item.get("code", ""))).lower()
        if not code:
            return QIcon()
        if code in self._set_icon_cache:
            return self._set_icon_cache[code]

        icon_path = self._set_icon_cache_dir() / f"{code}.svg"
        icon = QIcon(str(icon_path)) if icon_path.exists() else QIcon()
        self._set_icon_cache[code] = icon
        return icon

    def _download_set_icon(self, item: dict[str, Any], overwrite: bool = False) -> bool:
        code = clean_text(str(item.get("code", ""))).lower()
        icon_uri = clean_text(str(item.get("icon_svg_uri", "")))
        if not code or not icon_uri:
            return False
        icon_path = self._set_icon_cache_dir() / f"{code}.svg"
        if icon_path.exists() and not overwrite:
            return True
        try:
            request = Request(
                icon_uri,
                headers={
                    "User-Agent": "CardInventory/1.0 (local desktop inventory app; contact: local-user)",
                    "Accept": "image/svg+xml,*/*;q=0.8",
                },
            )
            with urlopen(request, timeout=8) as response:
                svg_text = response.read().decode("utf-8", errors="replace")
            if "<svg" not in svg_text.lower():
                return False
            icon_path.write_text(self._lighten_svg_icon(svg_text), encoding="utf-8")
            return True
        except Exception:
            return False

    def cache_set_icons(self) -> None:
        items = [item for item in self.sets if clean_text(str(item.get("code", ""))) and clean_text(str(item.get("icon_svg_uri", "")))]
        if not items:
            QMessageBox.information(self, "系列圖標", "目前沒有可下載的系列圖標資料。")
            return

        missing_count = 0
        icon_dir = self._set_icon_cache_dir()
        for item in items:
            code = clean_text(str(item.get("code", ""))).lower()
            if code and not (icon_dir / f"{code}.svg").exists():
                missing_count += 1

        overwrite = False
        if missing_count == 0:
            reply = QMessageBox.question(
                self,
                "系列圖標",
                "系列圖標已經有快取。是否重新下載更新？",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No,
            )
            if reply != QMessageBox.Yes:
                return
            overwrite = True

        progress = QProgressDialog("正在下載系列圖標...", "取消", 0, len(items), self)
        progress.setWindowTitle("快取系列圖標")
        progress.setWindowModality(Qt.WindowModal)
        progress.setMinimumDuration(0)

        ok_count = 0
        fail_count = 0
        for index, item in enumerate(items, start=1):
            if progress.wasCanceled():
                break
            name = clean_text(str(item.get("name", item.get("code", ""))))
            progress.setLabelText(f"正在下載系列圖標...\n{name}")
            QApplication.processEvents()
            if self._download_set_icon(item, overwrite=overwrite):
                ok_count += 1
            else:
                fail_count += 1
            progress.setValue(index)

        progress.close()
        self._set_icon_cache.clear()
        self.populate_tree()
        QMessageBox.information(self, "系列圖標", f"系列圖標快取完成。\n成功：{ok_count}\n失敗：{fail_count}")

    def _make_tree_item(self, item: dict[str, Any]) -> QTreeWidgetItem:
        code = clean_text(str(item.get("code", ""))).lower()
        name = clean_text(str(item.get("name", ""))) or code.upper()
        released_at = clean_text(str(item.get("released_at", "")))
        set_type = clean_text(str(item.get("set_type", "")))
        custom = "｜自訂" if item.get("custom") else ""
        display_name = f"{name}{custom}"
        tree_item = QTreeWidgetItem([display_name, code.upper(), released_at])
        icon = self._set_icon_for_item(item)
        if not icon.isNull():
            tree_item.setIcon(0, icon)
        tree_item.setData(0, Qt.UserRole, code)
        tree_item.setData(0, Qt.UserRole + 1, scryfall_set_label(item))
        tooltip_lines = [name]
        if set_type:
            tooltip_lines.append(f"Type：{set_type}")
        if code:
            tooltip_lines.append(f"Code：{code.upper()}")
        if released_at:
            tooltip_lines.append(f"Released：{released_at}")
        tree_item.setToolTip(0, "\n".join(tooltip_lines))
        return tree_item

    @staticmethod
    def _norm_name(value: str) -> str:
        return re.sub(r"\s+", " ", clean_text(value)).strip().lower()

    def _infer_parent_code(
        self,
        item: dict[str, Any],
        items_by_code: dict[str, dict[str, Any]],
        name_to_code: dict[str, str],
    ) -> str:
        code = clean_text(str(item.get("code", ""))).lower()
        parent_code = clean_text(str(item.get("parent_set_code", ""))).lower()
        if parent_code and parent_code in items_by_code and parent_code != code:
            return parent_code

        name = clean_text(str(item.get("name", "")))
        if not name:
            return ""

        candidates: list[str] = []
        if name.lower().startswith("alchemy: "):
            candidates.append(name.split(":", 1)[1].strip())

        for suffix, replacement_suffix in self.CHILD_SUFFIX_CANDIDATES:
            if name.endswith(suffix):
                base = name[: -len(suffix)].strip()
                if replacement_suffix:
                    candidates.append((base + replacement_suffix).strip())
                candidates.append(base)

        # Code-based fallback used by many Scryfall companion sets, such as T + set for tokens and P + set for promos.
        code_candidates: list[str] = []
        for prefix in ("t", "p"):
            if code.startswith(prefix) and code[1:] in items_by_code:
                code_candidates.append(code[1:])
        if code.endswith("c") and code[:-1] in items_by_code:
            code_candidates.append(code[:-1])

        for candidate_code in code_candidates:
            if candidate_code and candidate_code != code:
                return candidate_code

        for candidate in candidates:
            candidate_code = name_to_code.get(self._norm_name(candidate), "")
            if candidate_code and candidate_code != code:
                return candidate_code
        return ""

    def _has_matching_descendant(
        self,
        code: str,
        children: dict[str, list[str]],
        items_by_code: dict[str, dict[str, Any]],
        filter_text: str,
        memo: dict[str, bool],
    ) -> bool:
        if code in memo:
            return memo[code]
        item = items_by_code.get(code, {})
        matched = self._matches_filter(item, filter_text)
        for child_code in children.get(code, []):
            if self._has_matching_descendant(child_code, children, items_by_code, filter_text, memo):
                matched = True
                break
        memo[code] = matched
        return matched

    def _would_create_cycle(self, code: str, parent_code: str, parent_map: dict[str, str]) -> bool:
        cursor = parent_code
        visited = {code}
        while cursor:
            if cursor in visited:
                return True
            visited.add(cursor)
            cursor = parent_map.get(cursor, "")
        return False

    def populate_tree(self) -> None:
        filter_text = clean_text(self.search_edit.text()).lower() if hasattr(self, "search_edit") else ""
        self.tree.clear()

        all_item = QTreeWidgetItem(["全部系列", "", ""])
        all_item.setData(0, Qt.UserRole, "")
        all_item.setData(0, Qt.UserRole + 1, "全部系列")
        all_item.setFirstColumnSpanned(True)
        self.tree.addTopLevelItem(all_item)

        items_by_code: dict[str, dict[str, Any]] = {}
        for item in self.sets:
            code = clean_text(str(item.get("code", ""))).lower()
            if code:
                items_by_code[code] = item

        name_to_code: dict[str, str] = {}
        for code, item in items_by_code.items():
            norm = self._norm_name(str(item.get("name", "")))
            if norm and norm not in name_to_code:
                name_to_code[norm] = code

        parent_map: dict[str, str] = {}
        for code, item in items_by_code.items():
            inferred = self._infer_parent_code(item, items_by_code, name_to_code)
            if inferred and inferred in items_by_code and inferred != code:
                parent_map[code] = inferred

        # Remove accidental cycles caused by loose name heuristics.
        for code, parent_code in list(parent_map.items()):
            if self._would_create_cycle(code, parent_code, parent_map):
                parent_map.pop(code, None)

        children: dict[str, list[str]] = {}
        top_codes: list[str] = []
        for code in items_by_code:
            parent_code = parent_map.get(code, "")
            if parent_code:
                children.setdefault(parent_code, []).append(code)
            else:
                top_codes.append(code)

        def sort_key_code(code: str) -> tuple[str, str]:
            item = items_by_code.get(code, {})
            return (str(item.get("released_at", "")), str(item.get("name", "")).lower())

        top_codes.sort(key=sort_key_code, reverse=True)
        for code_list in children.values():
            code_list.sort(key=sort_key_code, reverse=True)

        selected_item: QTreeWidgetItem | None = all_item if not self.current_code else None
        match_memo: dict[str, bool] = {}

        def add_node(code: str, parent_node: QTreeWidgetItem | None) -> QTreeWidgetItem | None:
            if filter_text and not self._has_matching_descendant(code, children, items_by_code, filter_text, match_memo):
                return None
            item = items_by_code.get(code)
            if not item:
                return None
            node = self._make_tree_item(item)
            if parent_node is None:
                self.tree.addTopLevelItem(node)
            else:
                parent_node.addChild(node)
            nonlocal selected_item
            if code == self.current_code:
                selected_item = node
            for child_code in children.get(code, []):
                add_node(child_code, node)
            if node.childCount() > 0:
                node.setExpanded(True)
            return node

        for code in top_codes:
            add_node(code, None)

        self.tree.resizeColumnToContents(0)
        self.tree.resizeColumnToContents(1)
        if selected_item is not None:
            self.tree.setCurrentItem(selected_item)
            self.tree.scrollToItem(selected_item)
        elif self.tree.topLevelItemCount() > 0:
            self.tree.setCurrentItem(self.tree.topLevelItem(0))

    def update_selected_from_tree(self) -> None:
        item = self.tree.currentItem()
        if item is None:
            return
        self.selected_code = clean_text(str(item.data(0, Qt.UserRole)))
        self.selected_label = clean_text(str(item.data(0, Qt.UserRole + 1))) or "全部系列"

    def accept_current_item(self, *_args: Any) -> None:
        self.update_selected_from_tree()
        self.accept()


class InventoryEditDialog(QDialog):
    def __init__(
        self,
        card: dict[str, Any],
        categories: list[str],
        buy_methods: list[str],
        parent: QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        self.setWindowTitle("修改庫存內容")
        self.resize(760, 560)

        self.card = card
        self.categories = categories
        self.buy_methods = buy_methods
        self.selected_new_image_path = ""
        self.clear_image_requested = False

        root = QHBoxLayout(self)

        form_group = QGroupBox("庫存資料")
        form = QFormLayout(form_group)

        self.name_edit = QLineEdit(str(card.get("name", "")))

        self.category_combo = QComboBox()
        self.category_combo.addItems(categories)
        current_category = str(card.get("category", ""))
        if current_category and current_category not in categories:
            self.category_combo.addItem(current_category)
        if current_category:
            self.category_combo.setCurrentText(current_category)

        self.psa_check = QCheckBox("鑑定卡(PSA)")
        self.psa_check.setChecked(bool(card.get("psa_enabled", False)) or str(card.get("grade_company", "無")) == "PSA")
        self.psa_score_edit = QLineEdit(str(card.get("psa_score", card.get("grade_score", "") if str(card.get("grade_company", "無")) == "PSA" else "")).strip())
        self.psa_score_edit.setPlaceholderText("PSA 分數")

        self.bgs_check = QCheckBox("鑑定卡(BGS)")
        self.bgs_check.setChecked(bool(card.get("bgs_enabled", False)) or str(card.get("grade_company", "無")) == "BGS")
        self.bgs_score_edit = QLineEdit(str(card.get("bgs_score", card.get("grade_score", "") if str(card.get("grade_company", "無")) == "BGS" else "")).strip())
        self.bgs_score_edit.setPlaceholderText("BGS 分數")

        grade_row = QGridLayout()
        grade_row.addWidget(self.psa_check, 0, 0)
        grade_row.addWidget(self.psa_score_edit, 0, 1)
        grade_row.addWidget(self.bgs_check, 1, 0)
        grade_row.addWidget(self.bgs_score_edit, 1, 1)

        self.buy_quantity_spin = QSpinBox()
        self.buy_quantity_spin.setRange(1, 999_999)
        self.buy_quantity_spin.setValue(max(1, int(card.get("buy_quantity", 1) or 1)))

        self.remaining_quantity_spin = QSpinBox()
        self.remaining_quantity_spin.setRange(0, 999_999)
        self.remaining_quantity_spin.setValue(max(0, int(card.get("remaining_quantity", 0) or 0)))

        self.buy_total_spin = QDoubleSpinBox()
        self.buy_total_spin.setRange(0, 999_999_999)
        self.buy_total_spin.setDecimals(0)
        self.buy_total_spin.setSingleStep(100)
        self.buy_total_spin.setPrefix("NT$ ")
        self.buy_total_spin.setValue(float(card.get("buy_total", 0) or 0))

        self.buy_method_combo = QComboBox()
        self.buy_method_combo.addItems(buy_methods)
        current_method = str(card.get("buy_method", ""))
        if current_method and current_method not in buy_methods:
            self.buy_method_combo.addItem(current_method)
        if current_method:
            self.buy_method_combo.setCurrentText(current_method)

        self.note_edit = QTextEdit()
        self.note_edit.setPlainText(str(card.get("note", "")))
        self.note_edit.setFixedHeight(120)

        self.image_preview = QLabel("無圖片")
        self.image_preview.setMinimumSize(220, 220)
        load_image_preview(self.image_preview, str(card.get("image_path", "")))

        choose_image_btn = QPushButton("更換圖片")
        choose_image_btn.clicked.connect(self.choose_image)
        clear_image_btn = QPushButton("清除圖片")
        clear_image_btn.clicked.connect(self.clear_image)
        image_row = QHBoxLayout()
        image_row.addWidget(choose_image_btn)
        image_row.addWidget(clear_image_btn)
        image_row.addStretch(1)

        button_box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        button_box.button(QDialogButtonBox.Ok).setText("儲存修改")
        button_box.button(QDialogButtonBox.Cancel).setText("取消")
        button_box.accepted.connect(self.accept)
        button_box.rejected.connect(self.reject)

        form.addRow("卡片名稱：", self.name_edit)
        form.addRow("分類：", self.category_combo)
        form.addRow("鑑定標籤：", grade_row)
        form.addRow("原始買入數量：", self.buy_quantity_spin)
        form.addRow("目前剩餘庫存：", self.remaining_quantity_spin)
        form.addRow("買入總金額：", self.buy_total_spin)
        form.addRow("買入方式：", self.buy_method_combo)
        form.addRow("圖片：", image_row)
        form.addRow("備註：", self.note_edit)
        form.addRow("", button_box)

        preview_group = QGroupBox("圖片預覽")
        preview_layout = QVBoxLayout(preview_group)
        preview_layout.addWidget(self.image_preview, 1)

        root.addWidget(form_group, 2)
        root.addWidget(preview_group, 1)

    def choose_image(self) -> None:
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            "選擇卡片圖片",
            str(BASE_DIR),
            "圖片檔案 (*.png *.jpg *.jpeg *.bmp *.webp);;所有檔案 (*.*)",
        )
        if not file_path:
            return
        self.selected_new_image_path = file_path
        self.clear_image_requested = False
        load_image_preview(self.image_preview, file_path)

    def clear_image(self) -> None:
        self.selected_new_image_path = ""
        self.clear_image_requested = True
        load_image_preview(self.image_preview, "")

    def accept(self) -> None:
        name = self.name_edit.text().strip()
        buy_quantity = int(self.buy_quantity_spin.value())
        remaining_quantity = int(self.remaining_quantity_spin.value())

        if not name:
            QMessageBox.warning(self, "無法儲存", "卡片名稱不可空白。")
            return
        if remaining_quantity > buy_quantity:
            QMessageBox.warning(self, "無法儲存", "剩餘庫存不可大於原始買入數量。")
            return

        super().accept()

    def values(self) -> dict[str, Any]:
        psa_score = self.psa_score_edit.text().strip()
        bgs_score = self.bgs_score_edit.text().strip()
        psa_enabled = self.psa_check.isChecked() or bool(psa_score)
        bgs_enabled = self.bgs_check.isChecked() or bool(bgs_score)
        if not psa_enabled:
            psa_score = ""
        if not bgs_enabled:
            bgs_score = ""

        return {
            "name": self.name_edit.text().strip(),
            "category": self.category_combo.currentText(),
            "psa_enabled": psa_enabled,
            "psa_score": psa_score,
            "bgs_enabled": bgs_enabled,
            "bgs_score": bgs_score,
            "buy_method": self.buy_method_combo.currentText(),
            "buy_quantity": int(self.buy_quantity_spin.value()),
            "remaining_quantity": int(self.remaining_quantity_spin.value()),
            "buy_total": float(self.buy_total_spin.value()),
            "note": self.note_edit.toPlainText().strip(),
        }



def mtg_inventory_item_from_scryfall(item: dict[str, Any], quantity: int) -> dict[str, Any]:
    return {
        "id": uuid.uuid4().hex,
        "source": "scryfall",
        "quantity": max(0, int(quantity or 0)),
        "name": clean_text(str(item.get("name", ""))),
        "english_name": clean_text(str(item.get("english_name", ""))),
        "printed_name": clean_text(str(item.get("printed_name", ""))),
        "edition": clean_text(str(item.get("edition", ""))),
        "set_code": clean_text(str(item.get("set_code", ""))).upper(),
        "rarity": clean_text(str(item.get("rarity", ""))),
        "collector": clean_text(str(item.get("collector", ""))),
        "type": clean_text(str(item.get("type", ""))),
        "oracle_type": clean_text(str(item.get("oracle_type", ""))),
        "colors": clean_text(str(item.get("colors", ""))),
        "lang": clean_text(str(item.get("lang", ""))).lower(),
        "lang_label": clean_text(str(item.get("lang_label", ""))),
        "price": clean_text(str(item.get("price", ""))),
        "text": str(item.get("text", "")).strip(),
        "url": clean_text(str(item.get("url", ""))),
        "image_url": clean_text(str(item.get("image_url", ""))),
        "source_url": clean_text(str(item.get("source_url", ""))),
        "scryfall_id": clean_text(str(item.get("scryfall_id", ""))),
        "released_at": clean_text(str(item.get("released_at", ""))),
        "layout": clean_text(str(item.get("layout", ""))),
        "legalities": clean_text(str(item.get("legalities", ""))),
        "note": "",
        "ruten": default_ruten_item_fields(),
        "created_at": now_text(),
        "updated_at": now_text(),
    }


def mtg_inventory_match_key(record: dict[str, Any]) -> tuple[str, str, str, str, str]:
    return (
        clean_text(str(record.get("scryfall_id", ""))).lower(),
        clean_text(str(record.get("set_code", ""))).lower(),
        clean_text(str(record.get("collector", ""))).lower(),
        clean_text(str(record.get("lang", ""))).lower(),
        clean_text(str(record.get("name", ""))).lower(),
    )


def natural_sort_key(value: Any) -> tuple[Any, ...]:
    text = clean_text(str(value or "")).lower()
    if not text:
        return ()
    parts = re.split(r"(\d+)", text)
    key: list[Any] = []
    for part in parts:
        if part == "":
            continue
        if part.isdigit():
            key.append((0, int(part)))
        else:
            key.append((1, part))
    return tuple(key)


def collector_number_sort_key(value: Any) -> tuple[Any, ...]:
    text = clean_text(str(value or "")).lower()
    if not text:
        return ((9, ""),)

    # Collector number often looks like 001, 12, 12a, 123★, etc.
    # Sort by numeric prefix first, then by suffix naturally.
    match = re.match(r"^\s*(\d+)(.*)$", text)
    if match:
        return (
            (0, int(match.group(1))),
            (1, natural_sort_key(match.group(2))),
            (2, text),
        )
    return ((1, natural_sort_key(text)), (2, text))


def mtg_price_sort_key(value: Any) -> tuple[Any, ...]:
    text = clean_text(str(value or ""))
    if not text:
        return ((9, 0.0),)
    numbers = re.findall(r"-?\d+(?:\.\d+)?", text.replace(",", ""))
    if numbers:
        try:
            return ((0, float(numbers[0])), (1, text.lower()))
        except Exception:
            pass
    return ((1, natural_sort_key(text)),)


class MTGInventoryEditDialog(QDialog):
    def __init__(self, record: dict[str, Any], parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.setWindowTitle("修改 MTG 庫存")
        self.resize(760, 720)
        self.record = record

        root = QVBoxLayout(self)
        form_group = QGroupBox("MTG 庫存資料")
        form = QFormLayout(form_group)

        self.quantity_spin = QSpinBox()
        self.quantity_spin.setRange(0, 999_999)
        self.quantity_spin.setValue(max(0, int(record.get("quantity", 0) or 0)))

        self.name_edit = QLineEdit(str(record.get("name", "")))
        self.english_name_edit = QLineEdit(str(record.get("english_name", "")))
        self.printed_name_edit = QLineEdit(str(record.get("printed_name", "")))
        self.edition_edit = QLineEdit(str(record.get("edition", "")))
        self.set_code_edit = QLineEdit(str(record.get("set_code", "")))
        self.rarity_edit = QLineEdit(str(record.get("rarity", "")))
        self.collector_edit = QLineEdit(str(record.get("collector", "")))
        self.type_edit = QLineEdit(str(record.get("type", "")))
        self.colors_edit = QLineEdit(str(record.get("colors", "")))
        self.price_edit = QLineEdit(str(record.get("price", "")))
        self.scryfall_id_edit = QLineEdit(str(record.get("scryfall_id", "")))
        self.url_edit = QLineEdit(str(record.get("url", "")))
        self.image_url_edit = QLineEdit(str(record.get("image_url", "")))

        self.language_combo = QComboBox()
        current_lang = clean_text(str(record.get("lang", ""))).lower()
        for label, code in SCRYFALL_LANGUAGES:
            self.language_combo.addItem(label, code)
        if current_lang:
            idx = self.language_combo.findData(current_lang)
            if idx >= 0:
                self.language_combo.setCurrentIndex(idx)
            else:
                self.language_combo.addItem(current_lang, current_lang)
                self.language_combo.setCurrentIndex(self.language_combo.count() - 1)

        self.text_edit = QTextEdit()
        self.text_edit.setPlainText(str(record.get("text", "")))
        self.text_edit.setFixedHeight(90)

        self.note_edit = QTextEdit()
        self.note_edit.setPlainText(str(record.get("note", "")))
        self.note_edit.setFixedHeight(80)

        form.addRow("數量：", self.quantity_spin)
        form.addRow("Card name：", self.name_edit)
        form.addRow("English name：", self.english_name_edit)
        form.addRow("Printed name：", self.printed_name_edit)
        form.addRow("Edition：", self.edition_edit)
        form.addRow("Set Code：", self.set_code_edit)
        form.addRow("Rarity：", self.rarity_edit)
        form.addRow("Collector #：", self.collector_edit)
        form.addRow("Type：", self.type_edit)
        form.addRow("Color：", self.colors_edit)
        form.addRow("Language：", self.language_combo)
        form.addRow("Prices：", self.price_edit)
        form.addRow("Scryfall ID：", self.scryfall_id_edit)
        form.addRow("URL：", self.url_edit)
        form.addRow("Image URL：", self.image_url_edit)
        form.addRow("Text：", self.text_edit)
        form.addRow("備註：", self.note_edit)

        button_box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        button_box.button(QDialogButtonBox.Ok).setText("儲存修改")
        button_box.button(QDialogButtonBox.Cancel).setText("取消")
        button_box.accepted.connect(self.accept)
        button_box.rejected.connect(self.reject)

        root.addWidget(form_group, 1)
        root.addWidget(button_box)

    def accept(self) -> None:
        if not self.name_edit.text().strip():
            QMessageBox.warning(self, "無法儲存", "Card name 不可空白。")
            return
        super().accept()

    def values(self) -> dict[str, Any]:
        lang_code = clean_text(str(self.language_combo.currentData() or "")).lower()
        return {
            "quantity": int(self.quantity_spin.value()),
            "name": self.name_edit.text().strip(),
            "english_name": self.english_name_edit.text().strip(),
            "printed_name": self.printed_name_edit.text().strip(),
            "edition": self.edition_edit.text().strip(),
            "set_code": self.set_code_edit.text().strip().upper(),
            "rarity": self.rarity_edit.text().strip(),
            "collector": self.collector_edit.text().strip(),
            "type": self.type_edit.text().strip(),
            "colors": self.colors_edit.text().strip(),
            "lang": lang_code,
            "lang_label": scryfall_language_label(lang_code),
            "price": self.price_edit.text().strip(),
            "scryfall_id": self.scryfall_id_edit.text().strip(),
            "url": self.url_edit.text().strip(),
            "image_url": self.image_url_edit.text().strip(),
            "text": self.text_edit.toPlainText().strip(),
            "note": self.note_edit.toPlainText().strip(),
        }


class RutenApiClient:
    def __init__(self, settings: dict[str, Any]) -> None:
        self.settings = settings
        self.host = clean_text(str(settings.get("api_host", "https://partner.ruten.com.tw"))).rstrip("/") or "https://partner.ruten.com.tw"
        self.api_key = clean_text(str(settings.get("api_key", "")))
        self.secret_key = clean_text(str(settings.get("secret_key", "")))
        self.salt_key = clean_text(str(settings.get("salt_key", "")))
        self.signature_base = clean_text(str(settings.get("signature_base", "full_url"))) or "full_url"
        self.license_allowed = bool(settings.get("__license_allowed", True))
        self.license_reason = clean_text(str(settings.get("__license_reason", "")))

    def is_ready(self) -> bool:
        return bool(self.license_allowed and self.host and self.api_key and self.secret_key and self.salt_key)

    def assert_ready(self) -> None:
        if not self.license_allowed:
            raise RuntimeError(self.license_reason or "程式尚未啟用，露天同步 / 上架 / 訂單功能已停用。")
        if not (self.host and self.api_key and self.secret_key and self.salt_key):
            raise RuntimeError("露天 API 尚未設定完整：請先填入 API Host、API Key、Secret Key、Salt Key。")

    def build_path(self, path: str, params: dict[str, Any] | None = None) -> str:
        clean_path = path if path.startswith("/") else f"/{path}"
        if params:
            query_items = {k: v for k, v in params.items() if v not in (None, "")}
            if query_items:
                clean_path += "?" + urlencode(query_items)
        return clean_path

    def sign(self, url: str, path_with_query: str, body_text: str, timestamp: str) -> str:
        target = path_with_query if self.signature_base == "path" else url
        raw = f"{self.salt_key}{target}{body_text}{timestamp}"
        return hmac.new(self.secret_key.encode("utf-8"), raw.encode("utf-8"), hashlib.sha256).hexdigest()

    def request(
        self,
        method: str,
        path: str,
        payload: dict[str, Any] | None = None,
        params: dict[str, Any] | None = None,
        timeout: int = 45,
    ) -> Any:
        self.assert_ready()
        method = method.upper()
        path_with_query = self.build_path(path, params)
        url = f"{self.host}{path_with_query}"
        body_text = "" if payload is None else json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
        data = body_text.encode("utf-8") if body_text else None
        timestamp = str(int(time.time()))
        headers = {
            "Content-Type": "application/json",
            "Accept": "application/json",
            "X-RT-Key": self.api_key,
            "X-RT-Timestamp": timestamp,
            "X-RT-Authorization": self.sign(url, path_with_query, body_text, timestamp),
            "User-Agent": "CardInventory/1.0 RutenSync",
        }
        request = Request(url, data=data, headers=headers, method=method)
        try:
            with urlopen(request, timeout=timeout) as response:
                charset = response.headers.get_content_charset() or "utf-8"
                raw = response.read().decode(charset, errors="replace")
        except HTTPError as exc:
            raw = exc.read().decode("utf-8", errors="replace")
            try:
                payload_json = json.loads(raw) if raw else {}
            except Exception:
                payload_json = {"status": "failure", "error_code": str(exc.code), "error_msg": raw or str(exc)}
            return payload_json

        if not raw.strip():
            return {"status": "success", "data": None}
        try:
            return json.loads(raw)
        except Exception:
            return {"status": "failure", "error_code": "NON_JSON", "error_msg": raw, "data": None}

    def create_product(self, payload: dict[str, Any]) -> Any:
        return self.request("POST", "/api/v1/product/item", payload=payload)

    def update_stock(self, item_id: str, qty: int, spec_id: str = "") -> Any:
        if spec_id:
            payload = {"item_id": item_id, "spec_info": [{"spec_id": spec_id, "qty": int(qty)}]}
        else:
            payload = {"item_id": item_id, "qty": int(qty)}
        return self.request("PUT", "/api/v1/product/item/stock", payload=payload)

    def update_price(self, item_id: str, price: int, spec_id: str = "") -> Any:
        if spec_id:
            payload = {"item_id": item_id, "spec_info": [{"spec_id": spec_id, "price": int(price)}]}
        else:
            payload = {"item_id": item_id, "price": int(price)}
        return self.request("PUT", "/api/v1/product/item/price", payload=payload)

    def update_item_info(self, payload: dict[str, Any]) -> Any:
        return self.request("PUT", "/api/v1/product/item/info", payload=payload)

    def set_online(self, item_id: str) -> Any:
        return self.request("PUT", "/api/v1/product/item/online", payload={"item_id": item_id})

    def set_offline(self, item_id: str) -> Any:
        return self.request("PUT", "/api/v1/product/item/offline", payload={"item_id": item_id})

    def get_item(self, item_id: str) -> Any:
        return self.request("GET", f"/api/v1/product/item/{item_id}")

    def list_products(self, status: str = "all", offset: int = 1, limit: int = 9999) -> Any:
        return self.request("GET", "/api/v1/product/list", params={"status": status, "offset": offset, "limit": limit})

    def find_item_id_by_custom_no(self, custom_no: str) -> Any:
        return self.request("GET", "/api/v1/product/item_id", params={"custom_no": custom_no})

    def get_default_logistic(self) -> Any:
        return self.request("GET", "/api/v1/setting/default/logistic")

    def set_default_logistic(self, payload: dict[str, Any]) -> Any:
        return self.request("PUT", "/api/v1/setting/default/logistic", payload=payload)

    def request_multipart(
        self,
        method: str,
        path: str,
        fields: dict[str, Any],
        files: list[tuple[str, Path]],
        timeout: int = 60,
    ) -> Any:
        self.assert_ready()
        method = method.upper()
        path_with_query = self.build_path(path)
        url = f"{self.host}{path_with_query}"
        boundary = f"----CardInventoryRutenBoundary{uuid.uuid4().hex}"
        body_parts: list[bytes] = []
        for key, value in fields.items():
            body_parts.append(f"--{boundary}\r\n".encode("utf-8"))
            body_parts.append(f'Content-Disposition: form-data; name="{key}"\r\n\r\n'.encode("utf-8"))
            body_parts.append(str(value).encode("utf-8"))
            body_parts.append(b"\r\n")
        for field_name, path_obj in files:
            filename = path_obj.name
            mime_type = mimetypes.guess_type(str(path_obj))[0] or "image/jpeg"
            body_parts.append(f"--{boundary}\r\n".encode("utf-8"))
            body_parts.append(f'Content-Disposition: form-data; name="{field_name}"; filename="{filename}"\r\n'.encode("utf-8"))
            body_parts.append(f"Content-Type: {mime_type}\r\n\r\n".encode("utf-8"))
            body_parts.append(path_obj.read_bytes())
            body_parts.append(b"\r\n")
        body_parts.append(f"--{boundary}--\r\n".encode("utf-8"))
        body = b"".join(body_parts)

        body_text_for_signature = json.dumps(fields, ensure_ascii=False, separators=(",", ":"))
        timestamp = str(int(time.time()))
        headers = {
            "Content-Type": f"multipart/form-data; boundary={boundary}",
            "Accept": "application/json",
            "X-RT-Key": self.api_key,
            "X-RT-Timestamp": timestamp,
            "X-RT-Authorization": self.sign(url, path_with_query, body_text_for_signature, timestamp),
            "User-Agent": "CardInventory/1.0 RutenSync",
        }
        request = Request(url, data=body, headers=headers, method=method)
        try:
            with urlopen(request, timeout=timeout) as response:
                charset = response.headers.get_content_charset() or "utf-8"
                raw = response.read().decode(charset, errors="replace")
        except HTTPError as exc:
            raw = exc.read().decode("utf-8", errors="replace")
            try:
                return json.loads(raw) if raw else {"status": "failure", "error_code": str(exc.code), "error_msg": str(exc)}
            except Exception:
                return {"status": "failure", "error_code": str(exc.code), "error_msg": raw or str(exc)}
        if not raw.strip():
            return {"status": "success", "data": None}
        try:
            return json.loads(raw)
        except Exception:
            return {"status": "failure", "error_code": "NON_JSON", "error_msg": raw, "data": None}

    def set_product_images(self, item_id: str, image_paths: list[Path]) -> Any:
        clean_item_id = clean_text(str(item_id))
        if not clean_item_id:
            raise RuntimeError("缺少露天商品ID，無法上傳圖片。")
        if not image_paths:
            raise RuntimeError("沒有可上傳的圖片。")
        files = [(f"images[{index}]", path) for index, path in enumerate(image_paths[:9])]
        return self.request_multipart("POST", "/api/v1/product/item/image", {"item_id": clean_item_id}, files)

    def list_orders(self, order_status: str, start_date: str, end_date: str, page: int = 1, page_size: int = 100) -> Any:
        return self.request(
            "GET",
            "/api/v1/order/list",
            params={
                "order_status": order_status or "All",
                "start_date": start_date,
                "end_date": end_date,
                "page": int(page),
                "page_size": int(page_size),
            },
        )

    def order_detail(self, order_ids: list[str]) -> Any:
        return self.request("POST", "/api/v1/order/detail", payload={"order_id_list": ",".join(order_ids[:30])})


class RutenLogisticDefaultDialog(QDialog):
    LOGISTIC_OPTIONS = [
        ("7-11 取貨付款", "SEVEN_COD", 70, "取貨付款"),
        ("7-11 純取貨", "SEVEN", 70, "先付款後取貨"),
        ("全家取貨付款", "FAMI_COD", 70, "取貨付款"),
        ("全家純取貨", "FAMI", 70, "先付款後取貨"),
        ("萊爾富取貨付款", "HILIFE_COD", 50, "取貨付款"),
        ("萊爾富純取貨", "HILIFE", 50, "先付款後取貨"),
        ("便利帶隔日配", "MAPLE", 70, "先付款宅配"),
        ("郵寄寄送", "POST", 80, "先付款寄送"),
        ("離島寄送", "ISLAND", 100, "先付款寄送"),
        ("面交", "SELF", 0, "買家先付款"),
        ("面交取貨付款", "F2F", 0, "面交時付款"),
    ]
    PAYMENT_OPTIONS = [
        ("Pi 拍錢包支付連", "PP_PI"),
        ("PChomePay支付連 信用卡一次付清", "PP_CRD"),
        ("PChomePay支付連 信用卡3期", "PP_CRD_N3"),
        ("PChomePay支付連 信用卡6期", "PP_CRD_N6"),
        ("PChomePay支付連 信用卡12期", "PP_CRD_N12"),
        ("PChomePay支付連 現金/ATM/餘額", "PAYLINK"),
        ("銀行或郵局轉帳", "ATM"),
        ("郵局無摺存款", "PS"),
    ]
    PAYMENT_REQUIRED_LOGISTICS = PAYMENT_REQUIRED_LOGISTIC_CODES

    def __init__(self, settings: dict[str, Any], parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.setWindowTitle("設定露天物流/付款")
        self.resize(760, 720)
        self.settings = settings

        payload = ruten_default_logistic_payload(settings)
        current_logistics = {
            str(row.get("logistic_id", "")).upper(): max(0, to_int(row.get("shipping_fee", 0)))
            for row in payload.get("logistic_info", [])
            if isinstance(row, dict)
        }
        current_payments = {str(item).upper() for item in payload.get("payment_info", [])}

        root = QVBoxLayout(self)

        logistic_group = QGroupBox("物流方式")
        logistic_grid = QGridLayout(logistic_group)
        logistic_grid.addWidget(QLabel("使用"), 0, 0)
        logistic_grid.addWidget(QLabel("方式"), 0, 1)
        logistic_grid.addWidget(QLabel("運費"), 0, 2)
        logistic_grid.addWidget(QLabel("類型"), 0, 3)
        self.logistic_rows: list[tuple[str, QCheckBox, QSpinBox]] = []
        for row_index, (label, code, default_fee, kind) in enumerate(self.LOGISTIC_OPTIONS, start=1):
            check = QCheckBox()
            check.setChecked(code in current_logistics)
            fee_spin = QSpinBox()
            fee_spin.setRange(0, 9999)
            fee_spin.setValue(current_logistics.get(code, default_fee))
            logistic_grid.addWidget(check, row_index, 0)
            logistic_grid.addWidget(QLabel(f"{label}（{code}）"), row_index, 1)
            logistic_grid.addWidget(fee_spin, row_index, 2)
            logistic_grid.addWidget(QLabel(kind), row_index, 3)
            self.logistic_rows.append((code, check, fee_spin))

        payment_group = QGroupBox("付款方式")
        payment_layout = QVBoxLayout(payment_group)
        payment_hint = QLabel("取貨付款已包含在運送方式裡，不用在付款方式重複勾選。只有純取貨、郵寄、面交等先付款方式才需要勾付款。")
        payment_hint.setWordWrap(True)
        payment_layout.addWidget(payment_hint)
        self.payment_rows: list[tuple[str, QCheckBox]] = []
        for label, code in self.PAYMENT_OPTIONS:
            check = QCheckBox(f"{label}（{code}）")
            check.setChecked(code in current_payments)
            payment_layout.addWidget(check)
            self.payment_rows.append((code, check))

        self.combine_check = QCheckBox("合併運費")
        self.combine_check.setChecked(bool(settings.get("default_logistic_combine", True)))

        hint = QLabel("勾選後會套用成露天新增商品的預設物流與付款方式；之後在程式新增商品上架時會直接使用這組設定。")
        hint.setWordWrap(True)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        self.query_remote_btn = buttons.addButton("查詢目前物流/付款", QDialogButtonBox.ActionRole)
        self.query_remote_btn.clicked.connect(self.query_remote_default)
        buttons.button(QDialogButtonBox.Ok).setText("儲存並套用")
        buttons.button(QDialogButtonBox.Cancel).setText("取消")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        root.addWidget(logistic_group)
        root.addWidget(payment_group)
        root.addWidget(self.combine_check)
        root.addWidget(hint)
        root.addWidget(buttons)

    def apply_settings_to_widgets(self, settings: dict[str, Any]) -> None:
        payload = ruten_default_logistic_payload(settings)
        current_logistics = {
            str(row.get("logistic_id", "")).upper(): max(0, to_int(row.get("shipping_fee", 0)))
            for row in payload.get("logistic_info", [])
            if isinstance(row, dict)
        }
        current_payments = {str(item).upper() for item in payload.get("payment_info", [])}
        for code, check, fee_spin in self.logistic_rows:
            code_upper = str(code).upper()
            check.setChecked(code_upper in current_logistics)
            if code_upper in current_logistics:
                fee_spin.setValue(current_logistics.get(code_upper, int(fee_spin.value())))
        for code, check in self.payment_rows:
            check.setChecked(str(code).upper() in current_payments)
        self.combine_check.setChecked(bool(settings.get("default_logistic_combine", True)))

    def query_remote_default(self) -> None:
        parent = self.parent()
        if parent is None or not hasattr(parent, "ruten_client"):
            QMessageBox.warning(self, "無法查詢", "找不到露天 API 設定。")
            return
        client = parent.ruten_client()
        if not client.is_ready():
            QMessageBox.warning(self, "尚未設定 API", "請先設定露天 API 金鑰後再查詢物流/付款。")
            return
        try:
            response = client.get_default_logistic()
            if not ruten_response_ok(response):
                raise RuntimeError(ruten_response_message(response))
            remote_values = ruten_extract_logistic_payload(response)
            if not remote_values:
                raise RuntimeError("露天沒有回傳可辨識的物流/付款預設檔。")
            self.settings.update(remote_values)
            self.apply_settings_to_widgets(self.settings)
            if hasattr(parent, "db"):
                settings = parent.ruten_settings()
                settings.update(remote_values)
                settings["last_logistic_api_status"] = "正常"
                settings["last_logistic_check_at"] = now_text()
                settings["last_logistic_error"] = ""
                settings["last_product_api_status"] = "正常"
                settings["last_api_status"] = "正常"
                settings["last_success_at"] = now_text()
                settings["last_error"] = ""
                save_db(parent.db)
                if hasattr(parent, "update_ruten_status_label"):
                    parent.update_ruten_status_label()
                if hasattr(parent, "append_ruten_operation_log"):
                    parent.append_ruten_operation_log("查詢物流/付款預設檔", "成功", None, ruten_default_logistic_payload(settings))
            QMessageBox.information(self, "已套用目前物流/付款", ruten_logistic_settings_summary(self.settings))
        except Exception as exc:
            error_text = str(exc)
            if hasattr(parent, "db"):
                settings = parent.ruten_settings()
                settings["last_logistic_api_status"] = "異常"
                settings["last_logistic_check_at"] = now_text()
                settings["last_logistic_error"] = error_text
                settings["last_failure_at"] = now_text()
                settings["last_error"] = error_text
                save_db(parent.db)
                if hasattr(parent, "update_ruten_status_label"):
                    parent.update_ruten_status_label()
                if hasattr(parent, "append_ruten_operation_log"):
                    parent.append_ruten_operation_log("查詢物流/付款預設檔", "失敗", None, {}, error_text)
            QMessageBox.warning(self, "查詢失敗", error_text)

    def accept(self) -> None:
        logistics = self.logistic_info()
        payments = self.payment_info()
        if not logistics:
            QMessageBox.warning(self, "缺少運送方式", "請至少勾選一種運送方式。")
            return
        logistics_need_payment = [
            str(row.get("logistic_id", "")).upper()
            for row in logistics
            if str(row.get("logistic_id", "")).upper() in self.PAYMENT_REQUIRED_LOGISTICS
        ]
        if logistics_need_payment and not payments:
            QMessageBox.warning(self, "缺少付款方式", "你有勾選純取貨、郵寄、離島、便利帶或面交等先付款運送方式，請至少勾選一種付款方式。")
            return
        if payments and not logistics_need_payment:
            QMessageBox.warning(self, "物流與付款不相容", "你目前只勾選取貨付款/面交取貨付款，這類方式不需要付款方式。請取消付款方式，或加選純取貨、郵寄、便利帶、離島、面交等先付款運送方式。")
            return
        super().accept()

    def logistic_info(self) -> list[dict[str, Any]]:
        rows: list[dict[str, Any]] = []
        for code, check, fee_spin in self.logistic_rows:
            if check.isChecked():
                rows.append({"logistic_id": code, "shipping_fee": int(fee_spin.value())})
        return rows

    def payment_info(self) -> list[str]:
        return [code for code, check in self.payment_rows if check.isChecked()]

    def values(self) -> dict[str, Any]:
        return {
            "default_logistic_info": self.logistic_info(),
            "default_payment_info": self.payment_info(),
            "default_logistic_combine": bool(self.combine_check.isChecked()),
        }


class RutenSettingsDialog(QDialog):
    def __init__(self, settings: dict[str, Any], parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.setWindowTitle("露天 API 設定")
        self.resize(720, 420)
        self.settings = settings

        root = QVBoxLayout(self)
        form_group = QGroupBox("OPEN API 金鑰")
        form = QFormLayout(form_group)

        self.host_edit = QLineEdit(str(settings.get("api_host", "https://partner.ruten.com.tw")))
        self.api_key_edit = QLineEdit(str(settings.get("api_key", "")))
        self.secret_key_edit = QLineEdit(str(settings.get("secret_key", "")))
        self.secret_key_edit.setEchoMode(QLineEdit.Password)
        self.salt_key_edit = QLineEdit(str(settings.get("salt_key", "")))
        self.salt_key_edit.setEchoMode(QLineEdit.Password)

        self.signature_base_combo = QComboBox()
        self.signature_base_combo.addItem("官方預設", "full_url")
        self.signature_base_combo.addItem("備用模式", "path")
        idx = self.signature_base_combo.findData(str(settings.get("signature_base", "full_url")))
        if idx >= 0:
            self.signature_base_combo.setCurrentIndex(idx)

        self.default_location_type_combo = QComboBox()
        self.default_location_type_combo.addItem("台灣", 1)
        self.default_location_type_combo.addItem("海外", 2)
        idx = self.default_location_type_combo.findData(to_int(settings.get("create_location_type", 1)) or 1)
        if idx >= 0:
            self.default_location_type_combo.setCurrentIndex(idx)
        self.default_location_combo = QComboBox()
        setup_ruten_location_combo(self.default_location_combo, settings.get("create_location", DEFAULT_RUTEN_LOCATION_CODE))
        self.default_location_custom_edit = QLineEdit(normalize_ruten_location_code(settings.get("create_location", DEFAULT_RUTEN_LOCATION_CODE)))
        self.default_location_custom_edit.setPlaceholderText("海外或自訂代碼才需要填")
        self.default_location_type_combo.currentIndexChanged.connect(self.update_default_location_controls)

        self.auto_apply_orders_check = QCheckBox("有效訂單自動扣本地庫存")
        self.auto_apply_orders_check.setChecked(bool(settings.get("auto_apply_orders", False)))
        self.auto_restore_cancelled_orders_check = QCheckBox("訂單取消時自動補回已扣庫存")
        self.auto_restore_cancelled_orders_check.setChecked(bool(settings.get("auto_restore_cancelled_orders", True)))
        self.auto_push_after_order_apply_check = QCheckBox("訂單扣庫存後自動同步露天庫存")
        self.auto_push_after_order_apply_check.setChecked(bool(settings.get("auto_push_after_order_apply", False)))
        self.auto_push_local_changes_check = QCheckBox("本地 MTG庫存變動後自動同步露天")
        self.auto_push_local_changes_check.setChecked(bool(settings.get("auto_push_local_changes", False)))
        self.auto_offline_zero_stock_check = QCheckBox("露天上架數量為 0 時自動下架露天商品")
        self.auto_offline_zero_stock_check.setChecked(bool(settings.get("auto_offline_zero_stock", False)))
        self.auto_online_positive_stock_check = QCheckBox("露天上架數量大於 0 時自動上架露天商品")
        self.auto_online_positive_stock_check.setChecked(bool(settings.get("auto_online_positive_stock", False)))
        self.auto_order_check = QCheckBox("自動查詢新訂單")
        self.auto_order_check.setChecked(bool(settings.get("auto_order_check", False)))
        self.auto_order_minutes_spin = QSpinBox()
        self.auto_order_minutes_spin.setRange(1, 1440)
        self.auto_order_minutes_spin.setValue(max(1, to_int(settings.get("auto_order_minutes", 5)) or 5))

        location_row = QHBoxLayout()
        location_row.addWidget(self.default_location_combo, 1)
        location_row.addWidget(self.default_location_custom_edit, 1)
        location_widget = QWidget()
        location_widget.setLayout(location_row)

        form.addRow("API Host：", self.host_edit)
        form.addRow("API Key：", self.api_key_edit)
        form.addRow("Secret Key：", self.secret_key_edit)
        form.addRow("Salt Key：", self.salt_key_edit)
        form.addRow("驗證模式：", self.signature_base_combo)
        form.addRow("預設所在地類型：", self.default_location_type_combo)
        form.addRow("預設物品所在地：", location_widget)
        form.addRow("自動查訂單：", self.auto_order_check)
        form.addRow("查詢間隔分鐘：", self.auto_order_minutes_spin)
        form.addRow("訂單扣庫存：", self.auto_apply_orders_check)
        form.addRow("取消補庫存：", self.auto_restore_cancelled_orders_check)
        form.addRow("訂單後同步露天：", self.auto_push_after_order_apply_check)
        form.addRow("本地變動同步露天：", self.auto_push_local_changes_check)
        form.addRow("露天上架數量0自動下架：", self.auto_offline_zero_stock_check)
        form.addRow("露天上架數量>0自動上架：", self.auto_online_positive_stock_check)

        hint = QLabel("API Key / Secret Key / Salt Key 會獨立保存在 config/ruten_api_secrets.json，不會寫入庫存資料 JSON。")
        hint.setWordWrap(True)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.button(QDialogButtonBox.Ok).setText("儲存")
        buttons.button(QDialogButtonBox.Cancel).setText("取消")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        root.addWidget(form_group)
        root.addWidget(hint)
        root.addWidget(buttons)
        self.update_default_location_controls()

    def update_default_location_controls(self) -> None:
        is_tw = int(self.default_location_type_combo.currentData() or 1) == 1
        self.default_location_combo.setEnabled(is_tw)
        self.default_location_custom_edit.setEnabled(not is_tw)

    def selected_default_location(self) -> str:
        if int(self.default_location_type_combo.currentData() or 1) == 1:
            return normalize_ruten_location_code(self.default_location_combo.currentData()) or DEFAULT_RUTEN_LOCATION_CODE
        return normalize_ruten_location_code(self.default_location_custom_edit.text()) or DEFAULT_RUTEN_LOCATION_CODE

    def values(self) -> dict[str, Any]:
        return {
            "api_host": self.host_edit.text().strip().rstrip("/") or "https://partner.ruten.com.tw",
            "api_key": self.api_key_edit.text().strip(),
            "secret_key": self.secret_key_edit.text().strip(),
            "salt_key": self.salt_key_edit.text().strip(),
            "signature_base": str(self.signature_base_combo.currentData() or "full_url"),
            "create_location_type": int(self.default_location_type_combo.currentData() or 1),
            "create_location": self.selected_default_location(),
            "create_location_user_selected": True,
            "auto_order_check": bool(self.auto_order_check.isChecked()),
            "auto_order_minutes": int(self.auto_order_minutes_spin.value()),
            "auto_apply_orders": bool(self.auto_apply_orders_check.isChecked()),
            "auto_restore_cancelled_orders": bool(self.auto_restore_cancelled_orders_check.isChecked()),
            "auto_push_after_order_apply": bool(self.auto_push_after_order_apply_check.isChecked()),
            "auto_push_local_changes": bool(self.auto_push_local_changes_check.isChecked()),
            "auto_offline_zero_stock": bool(self.auto_offline_zero_stock_check.isChecked()),
            "auto_online_positive_stock": bool(self.auto_online_positive_stock_check.isChecked()),
        }


class RutenCreateProductDialog(QDialog):
    def __init__(self, record: dict[str, Any], settings: dict[str, Any], parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.setWindowTitle("建立露天商品")
        self.resize(820, 720)
        self.record = record
        self.settings = settings
        ruten = ensure_ruten_item_fields(record)

        root = QVBoxLayout(self)
        info = QLabel(
            f"MTG庫存：{record.get('name', '')}\n"
            f"Set：{record.get('set_code', record.get('edition', ''))}｜Collector：{record.get('collector', '')}｜本地總庫存：{record.get('quantity', 0)}\n"
            "這是建立新的露天商品；露天上架數量可以小於本地總庫存。"
        )
        info.setWordWrap(True)

        form_group = QGroupBox("新增到露天")
        form = QFormLayout(form_group)

        self.title_edit = QLineEdit(sanitize_ruten_title(ruten.get("title", "") or make_ruten_title(record)))
        self.title_edit.setMaxLength(130)
        self.class_presets = ruten_class_presets(settings)
        self.class_id_combo = QComboBox()
        self.class_id_combo.setEditable(True)
        self.class_id_combo.setInsertPolicy(QComboBox.NoInsert)
        setup_ruten_class_combo(self.class_id_combo, self.class_presets, settings.get("create_class_id", ""))
        if self.class_id_combo.lineEdit():
            self.class_id_combo.lineEdit().setPlaceholderText("選擇常用分類，或貼上分類ID")
        self.store_class_id_edit = QLineEdit(str(settings.get("create_store_class_id", "")))
        self.store_class_id_edit.setPlaceholderText("可空白")

        self.condition_combo = QComboBox()
        for label, value in [
            ("全新", 1),
            ("二手 - 使用不到一週", 2),
            ("二手 - 使用不滿一個月", 3),
            ("二手 - 使用一到三個月", 4),
            ("二手 - 使用未滿半年", 5),
            ("二手 - 使用未滿一年", 6),
            ("二手 - 使用一到二年", 7),
            ("二手 - 使用二到三年", 8),
            ("二手 - 使用三年以上", 9),
        ]:
            self.condition_combo.addItem(label, value)
        idx = self.condition_combo.findData(to_int(settings.get("create_condition", 1)) or 1)
        if idx >= 0:
            self.condition_combo.setCurrentIndex(idx)

        self.stock_status_combo = QComboBox()
        for label, value in [
            ("24小時內出貨", "24H"),
            ("3天內出貨", "3DAY"),
            ("7天內出貨", "7DAY"),
            ("14天內出貨", "14DAY"),
            ("21天內出貨", "21DAY"),
        ]:
            self.stock_status_combo.addItem(label, value)
        idx = self.stock_status_combo.findData(str(settings.get("create_stock_status", "3DAY")))
        if idx >= 0:
            self.stock_status_combo.setCurrentIndex(idx)

        self.location_type_combo = QComboBox()
        self.location_type_combo.addItem("台灣", 1)
        self.location_type_combo.addItem("海外", 2)
        idx = self.location_type_combo.findData(to_int(settings.get("create_location_type", 1)) or 1)
        if idx >= 0:
            self.location_type_combo.setCurrentIndex(idx)
        self.location_combo = QComboBox()
        setup_ruten_location_combo(self.location_combo, settings.get("create_location", DEFAULT_RUTEN_LOCATION_CODE))
        self.location_edit = QLineEdit(normalize_ruten_location_code(settings.get("create_location", DEFAULT_RUTEN_LOCATION_CODE)))
        self.location_edit.setPlaceholderText("海外或自訂代碼才需要填")
        self.location_edit.setMaxLength(30)
        self.location_type_combo.currentIndexChanged.connect(self.update_location_controls)

        self.shipping_setting_combo = QComboBox()
        self.shipping_setting_combo.addItem("使用露天新增商品預設檔", 1)
        self.shipping_setting_combo.setCurrentIndex(0)

        self.price_spin = QSpinBox()
        self.price_spin.setRange(1, 99_999_999)
        default_price = to_int(ruten.get("price", 0)) or to_int(record.get("price", 0)) or 1
        self.price_spin.setValue(max(1, min(99_999_999, default_price)))

        self.qty_spin = QSpinBox()
        self.qty_spin.setRange(1, 99_999)
        default_listing_qty = to_int(ruten.get("listing_qty", 0)) or min(max(1, to_int(record.get("quantity", 0)) or 1), 1)
        self.qty_spin.setValue(max(1, min(99_999, min(default_listing_qty, max(1, to_int(record.get("quantity", 0)) or 1)))))
        self.custom_no_edit = QLineEdit(sanitize_ruten_custom_no(ruten.get("custom_no", "") or make_ruten_custom_no(record)))
        self.custom_no_edit.setMaxLength(100)
        self.description_edit = QTextEdit()
        self.description_edit.setAcceptRichText(False)
        self.description_edit.setPlainText(normalize_ruten_description_lines(make_ruten_description(record)))
        self.description_edit.setMinimumHeight(180)

        class_row = QHBoxLayout()
        class_row.addWidget(self.class_id_combo, 1)
        class_save_btn = QPushButton("新增/更新常用")
        class_save_btn.clicked.connect(self.add_or_update_class_preset)
        class_row.addWidget(class_save_btn)
        class_delete_btn = QPushButton("刪除常用")
        class_delete_btn.clicked.connect(self.delete_class_preset)
        class_row.addWidget(class_delete_btn)
        class_lookup_btn = QPushButton("查分類")
        class_lookup_btn.clicked.connect(lambda _checked=False: QDesktopServices.openUrl(QUrl("https://mass.ruten.com.tw/y/find_class.php")))
        class_row.addWidget(class_lookup_btn)
        class_widget = QWidget()
        class_widget.setLayout(class_row)

        form.addRow("商品標題：", self.title_edit)
        form.addRow("露天分類ID：", class_widget)
        form.addRow("賣場分類ID：", self.store_class_id_edit)
        location_row = QHBoxLayout()
        location_row.addWidget(self.location_combo, 1)
        location_row.addWidget(self.location_edit, 1)
        location_widget = QWidget()
        location_widget.setLayout(location_row)

        form.addRow("商品新舊：", self.condition_combo)
        form.addRow("備貨狀態：", self.stock_status_combo)
        form.addRow("出貨地類型：", self.location_type_combo)
        form.addRow("物品所在地：", location_widget)
        form.addRow("物流收款：", self.shipping_setting_combo)
        form.addRow("售價 NT$：", self.price_spin)
        form.addRow("露天上架數量：", self.qty_spin)
        form.addRow("自用料號：", self.custom_no_edit)
        description_row = QVBoxLayout()
        description_row.addWidget(self.description_edit)
        description_btn_row = QHBoxLayout()
        format_description_btn = QPushButton("整理成分行格式")
        format_description_btn.clicked.connect(self.format_description_lines)
        regenerate_description_btn = QPushButton("重新產生預設說明")
        regenerate_description_btn.clicked.connect(self.regenerate_description)
        description_btn_row.addWidget(format_description_btn)
        description_btn_row.addWidget(regenerate_description_btn)
        description_btn_row.addStretch(1)
        description_row.addLayout(description_btn_row)
        description_widget = QWidget()
        description_widget.setLayout(description_row)
        form.addRow("商品說明：", description_widget)

        hint = QLabel("建立成功後，露天商品ID會自動寫回這筆 MTG庫存；售價只在首次建立時使用，之後以露天端售價為主。")
        hint.setWordWrap(True)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.button(QDialogButtonBox.Ok).setText("建立商品")
        buttons.button(QDialogButtonBox.Cancel).setText("取消")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        root.addWidget(info)
        root.addWidget(form_group, 1)
        root.addWidget(hint)
        root.addWidget(buttons)
        self.update_location_controls()

    def format_description_lines(self) -> None:
        self.description_edit.setPlainText(normalize_ruten_description_lines(self.description_edit.toPlainText()))

    def regenerate_description(self) -> None:
        self.description_edit.setPlainText(normalize_ruten_description_lines(make_ruten_description(self.record)))

    def update_location_controls(self) -> None:
        is_tw = int(self.location_type_combo.currentData() or 1) == 1
        self.location_combo.setEnabled(is_tw)
        self.location_edit.setEnabled(not is_tw)

    def selected_location(self) -> str:
        if int(self.location_type_combo.currentData() or 1) == 1:
            return normalize_ruten_location_code(self.location_combo.currentData()) or DEFAULT_RUTEN_LOCATION_CODE
        return normalize_ruten_location_code(self.location_edit.text()) or DEFAULT_RUTEN_LOCATION_CODE

    def current_class_label_id(self) -> tuple[str, str]:
        label, class_id = parse_ruten_class_input(self.class_id_combo.currentText())
        if not class_id:
            class_id = normalize_ruten_class_id(self.class_id_combo.currentData())
        if not label:
            for preset in self.class_presets:
                if normalize_ruten_class_id(preset.get("class_id", "")) == class_id:
                    label = clean_text(str(preset.get("label", "")))
                    break
        return label, class_id

    def refresh_class_combo(self, current_class_id: str = "") -> None:
        current_text = self.class_id_combo.currentText()
        current = normalize_ruten_class_id(current_class_id) or parse_ruten_class_input(current_text)[1]
        setup_ruten_class_combo(self.class_id_combo, self.class_presets, current)

    def add_or_update_class_preset(self) -> None:
        label, class_id = self.current_class_label_id()
        if not class_id:
            QMessageBox.warning(self, "缺少露天分類ID", "請先輸入或選擇露天分類ID。")
            return
        label_text, ok = QInputDialog.getText(
            self,
            "新增/更新常用分類",
            "分類顯示名稱：",
            text=label or class_id,
        )
        if not ok:
            return
        label_text = clean_text(label_text) or class_id
        self.class_presets = add_or_update_ruten_class_preset(self.class_presets, label_text, class_id)
        self.refresh_class_combo(class_id)

    def delete_class_preset(self) -> None:
        _label, class_id = self.current_class_label_id()
        if not class_id:
            return
        if QMessageBox.question(self, "刪除常用分類", f"要刪除常用分類 {class_id} 嗎？") != QMessageBox.Yes:
            return
        self.class_presets = [row for row in self.class_presets if normalize_ruten_class_id(row.get("class_id", "")) != class_id]
        self.refresh_class_combo("")

    def accept(self) -> None:
        title = sanitize_ruten_title(self.title_edit.text())
        _class_label, class_id = self.current_class_label_id()
        custom_no = sanitize_ruten_custom_no(self.custom_no_edit.text())
        if not title:
            QMessageBox.warning(self, "缺少商品標題", "請輸入商品標題。")
            return
        if not class_id:
            QMessageBox.warning(self, "缺少露天分類ID", "請輸入露天分類ID。")
            return
        if not custom_no:
            QMessageBox.warning(self, "缺少自用料號", "請輸入自用料號。")
            return
        self.title_edit.setText(title)
        self.custom_no_edit.setText(custom_no)
        super().accept()

    def values(self) -> dict[str, Any]:
        store_class_id = self.store_class_id_edit.text().strip()
        payload: dict[str, Any] = {
            "name": sanitize_ruten_title(self.title_edit.text()),
            "class_id": self.current_class_label_id()[1],
            "condition": int(self.condition_combo.currentData() or 1),
            "stock_status": str(self.stock_status_combo.currentData() or "3DAY"),
            "description": normalize_ruten_description_lines(self.description_edit.toPlainText()) or make_ruten_description(self.record),
            "location_type": int(self.location_type_combo.currentData() or 1),
            "location": self.selected_location(),
            "shipping_setting": int(self.shipping_setting_combo.currentData() or 1),
            "has_spec": False,
            "price": int(self.price_spin.value()),
            "qty": int(self.qty_spin.value()),
            "custom_no": sanitize_ruten_custom_no(self.custom_no_edit.text()),
            "is_goods_sale": False,
        }
        if store_class_id:
            payload["store_class_id"] = store_class_id
        return payload

    def default_values(self) -> dict[str, Any]:
        return {
            "create_class_id": self.current_class_label_id()[1],
            "create_class_presets": add_or_update_ruten_class_preset(self.class_presets, self.current_class_label_id()[0], self.current_class_label_id()[1]),
            "create_store_class_id": self.store_class_id_edit.text().strip(),
            "create_condition": int(self.condition_combo.currentData() or 1),
            "create_stock_status": str(self.stock_status_combo.currentData() or "3DAY"),
            "create_location_type": int(self.location_type_combo.currentData() or 1),
            "create_location": self.selected_location(),
            "create_location_user_selected": True,
            "create_shipping_setting": int(self.shipping_setting_combo.currentData() or 1),
        }


class RutenExistingProductEditDialog(QDialog):
    def __init__(self, record: dict[str, Any], settings: dict[str, Any], parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.setWindowTitle("露天商品管理")
        self.resize(780, 720)
        self.record = record
        self.settings = settings
        ruten = ensure_ruten_item_fields(record)
        status = clean_text(str(ruten.get("status", "unknown")))
        local_qty = max(0, to_int(record.get("quantity", 0)))

        root = QVBoxLayout(self)
        info = QLabel(
            f"MTG庫存：{record.get('name', '')}\n"
            f"露天商品ID：{ruten.get('item_id', '')}\n"
            f"本地總庫存：{local_qty}｜露天目前庫存：{ruten.get('remote_stock', '') or '-'}｜露天售價：{to_int(ruten.get('price', 0)) or '-'}\n"
            "這筆商品已經綁定露天商品；這裡可管理露天上架數量，也可更新露天商品標題、說明與自用料號。"
        )
        info.setWordWrap(True)

        form_group = QGroupBox("露天商品管理")
        form = QFormLayout(form_group)

        self.qty_spin = QSpinBox()
        self.qty_spin.setRange(0, 99_999)
        self.qty_spin.setValue(max(0, min(99_999, ruten_listing_qty(record))))

        self.remote_stock_label = QLabel(str(ruten.get("remote_stock", "") or "未取得"))
        self.price_label = QLabel(str(to_int(ruten.get("price", 0)) or "未取得"))

        self.title_edit = QLineEdit(str(ruten.get("title", "") or make_ruten_title(record)))
        self.title_edit.setMaxLength(130)
        self.custom_no_edit = QLineEdit(str(ruten.get("custom_no", "") or make_ruten_custom_no(record)))
        self.custom_no_edit.setMaxLength(100)

        self.auto_restock_check = QCheckBox("賣出後自動補回露天上架數量")
        self.auto_restock_check.setChecked(bool(ruten.get("auto_restock", False)))
        self.restock_target_spin = QSpinBox()
        self.restock_target_spin.setRange(1, 99_999)
        self.restock_target_spin.setValue(max(1, to_int(ruten.get("restock_target", 1)) or max(1, ruten_listing_qty(record) or 1)))

        self.online_check = QCheckBox("同步後設為上架中")
        self.online_check.setChecked(status not in ("online", "on"))

        self.description_edit = QTextEdit()
        self.description_edit.setAcceptRichText(False)
        current_description = normalize_ruten_description_lines(ruten.get("description", "")) or normalize_ruten_description_lines(make_ruten_description(record))
        self.description_edit.setPlainText(current_description)
        self.description_edit.setMinimumHeight(180)

        form.addRow("本地總庫存：", QLabel(str(local_qty)))
        form.addRow("露天目前庫存：", self.remote_stock_label)
        form.addRow("露天售價：", self.price_label)
        form.addRow("露天上架數量：", self.qty_spin)
        form.addRow("自動補貨：", self.auto_restock_check)
        form.addRow("補貨目標數量：", self.restock_target_spin)
        form.addRow("商品標題：", self.title_edit)
        form.addRow("自用料號：", self.custom_no_edit)
        form.addRow("上架狀態：", self.online_check)

        description_row = QVBoxLayout()
        description_row.addWidget(self.description_edit)
        description_btn_row = QHBoxLayout()
        format_description_btn = QPushButton("整理成分行格式")
        format_description_btn.clicked.connect(self.format_description_lines)
        regenerate_description_btn = QPushButton("重新產生預設說明")
        regenerate_description_btn.clicked.connect(self.regenerate_description)
        description_btn_row.addWidget(format_description_btn)
        description_btn_row.addWidget(regenerate_description_btn)
        description_btn_row.addStretch(1)
        description_row.addLayout(description_btn_row)
        description_widget = QWidget()
        description_widget.setLayout(description_row)
        form.addRow("商品說明：", description_widget)

        hint = QLabel("售價以露天端為主。按下更新後會同步露天上架數量，並更新露天商品標題、說明與自用料號；不會改本地總庫存。")
        hint.setWordWrap(True)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.button(QDialogButtonBox.Ok).setText("更新露天商品")
        buttons.button(QDialogButtonBox.Cancel).setText("取消")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        root.addWidget(info)
        root.addWidget(form_group, 1)
        root.addWidget(hint)
        root.addWidget(buttons)

    def format_description_lines(self) -> None:
        self.description_edit.setPlainText(normalize_ruten_description_lines(self.description_edit.toPlainText()))

    def regenerate_description(self) -> None:
        self.description_edit.setPlainText(normalize_ruten_description_lines(make_ruten_description(self.record)))

    def accept(self) -> None:
        title = sanitize_ruten_title(self.title_edit.text())
        custom_no = sanitize_ruten_custom_no(self.custom_no_edit.text())
        if not title:
            QMessageBox.warning(self, "缺少商品標題", "請輸入商品標題。")
            return
        if not custom_no:
            QMessageBox.warning(self, "缺少自用料號", "請輸入自用料號。")
            return
        if int(self.qty_spin.value()) > max(0, to_int(self.record.get("quantity", 0))):
            QMessageBox.warning(self, "露天上架數量過多", "露天上架數量不可大於本地總庫存。")
            return
        self.title_edit.setText(title)
        self.custom_no_edit.setText(custom_no)
        self.description_edit.setPlainText(normalize_ruten_description_lines(self.description_edit.toPlainText()) or make_ruten_description(self.record))
        super().accept()

    def values(self) -> dict[str, Any]:
        ruten = ensure_ruten_item_fields(self.record)
        settings = self.settings or {}
        class_id = normalize_ruten_class_id(ruten.get("class_id", "")) or normalize_ruten_class_id(settings.get("create_class_id", ""))
        return {
            "qty": int(self.qty_spin.value()),
            "title": sanitize_ruten_title(self.title_edit.text()),
            "custom_no": sanitize_ruten_custom_no(self.custom_no_edit.text()),
            "description": normalize_ruten_description_lines(self.description_edit.toPlainText()) or make_ruten_description(self.record),
            "set_online": bool(self.online_check.isChecked()),
            "auto_restock": bool(self.auto_restock_check.isChecked()),
            "restock_target": int(self.restock_target_spin.value()),
            "class_id": class_id,
            "store_class_id": clean_text(str(ruten.get("store_class_id", "") or settings.get("create_store_class_id", ""))),
            "condition": to_int(ruten.get("condition", 0)) or to_int(settings.get("create_condition", 1)) or 1,
            "stock_status": clean_text(str(ruten.get("stock_status", "") or settings.get("create_stock_status", "3DAY"))) or "3DAY",
            "location_type": to_int(ruten.get("location_type", 0)) or to_int(settings.get("create_location_type", 1)) or 1,
            "location": normalize_ruten_location_code(ruten.get("location", "") or settings.get("create_location", DEFAULT_RUTEN_LOCATION_CODE)) or DEFAULT_RUTEN_LOCATION_CODE,
        }


class MainWindow(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.db = load_db()
        save_db(self.db)

        self.selected_add_image_path = ""

        self.setWindowTitle(APP_TITLE)
        self.resize(1280, 820)

        self.tabs = QTabWidget()
        self.setCentralWidget(self.tabs)

        self.add_tab = QWidget()
        self.inventory_tab = QWidget()
        self.sell_tab = QWidget()
        self.report_tab = QWidget()
        self.cardkingdom_tab = QWidget()
        self.mtg_inventory_tab = QWidget()
        self.ruten_tab = QWidget()
        self.about_tab = QWidget()

        self.ck_results: list[dict[str, Any]] = []
        self.ck_current_page = 0
        self.ck_last_url = ""
        self.ck_worker: ScryfallSearchWorker | None = None
        self.scryfall_sets: list[dict[str, Any]] = []

        # MTG 庫存預設依 Collector # 正序排序；點擊表頭可切換正序 / 倒序。
        self.mtg_inventory_sort_column = 5
        self.mtg_inventory_sort_reverse = False
        self.mtg_inventory_checked_ids: set[str] = set()
        self.ruten_checked_ids: set[str] = set()
        self.ruten_current_page = 0
        self._updating_mtg_inventory_table = False
        self._updating_ruten_table = False

        self.tabs.addTab(self.add_tab, "新增庫存")
        self.tabs.addTab(self.inventory_tab, "庫存列表")
        self.tabs.addTab(self.sell_tab, "賣出扣庫存")
        self.tabs.addTab(self.report_tab, "收益紀錄")
        self.tabs.addTab(self.cardkingdom_tab, "Scryfall")
        self.tabs.addTab(self.mtg_inventory_tab, "MTG庫存")
        self.tabs.addTab(self.ruten_tab, "露天賣場")
        self.tabs.addTab(self.about_tab, "啟用/關於")

        self.build_add_tab()
        self.build_inventory_tab()
        self.build_sell_tab()
        self.build_report_tab()
        self.build_cardkingdom_tab()
        self.build_mtg_inventory_tab()
        self.build_ruten_tab()
        self.build_about_tab()
        self.refresh_about_license_status(use_network=False)
        self.update_license_gated_controls()

        self.refresh_all()
        self.ruten_order_timer = QTimer(self)
        self.ruten_order_timer.timeout.connect(self.auto_query_ruten_orders_tick)
        self.restart_ruten_timers()
        self.statusBar().showMessage(f"資料庫：{DB_PATH}")

    def categories(self) -> list[str]:
        return list(self.db.get("categories", DEFAULT_CATEGORIES))

    def buy_methods(self) -> list[str]:
        return list(self.db.get("buy_methods", DEFAULT_BUY_METHODS))

    def refresh_scryfall_set_combo(self, preserve_current: bool = True, show_errors: bool = False) -> None:
        if not hasattr(self, "ck_edition_combo"):
            return

        current_code = str(self.ck_edition_combo.currentData() or "") if preserve_current else ""
        current_text = self.ck_edition_combo.currentText().strip() if preserve_current else ""
        try:
            sets, meta, _source = load_scryfall_sets_local_only()
        except Exception as exc:
            sets = []
            meta = {"downloaded_at": "", "total_sets": 0, "official_sets": 0, "custom_sets": 0}
            if show_errors:
                QMessageBox.warning(self, "系列清單讀取失敗", f"無法讀取 Scryfall 系列清單：\n{exc}")

        self.scryfall_sets = sorted(
            sets,
            key=lambda x: (str(x.get("released_at", "")), str(x.get("name", "")).lower()),
            reverse=True,
        )

        self.ck_edition_combo.blockSignals(True)
        self.ck_edition_combo.clear()
        self.ck_edition_combo.addItem("全部系列", "")
        for item in self.scryfall_sets:
            self.ck_edition_combo.addItem(scryfall_set_label(item), str(item.get("code", "")).lower())

        target_index = 0
        restore_edit_text = ""
        if current_code:
            idx = self.ck_edition_combo.findData(current_code)
            if idx >= 0:
                target_index = idx
            elif current_text and current_text != "全部系列":
                restore_edit_text = current_text
        elif current_text:
            idx = self.ck_edition_combo.findText(current_text)
            if idx >= 0:
                target_index = idx
            elif current_text != "全部系列":
                restore_edit_text = current_text

        if self.ck_edition_combo.count() > 0 and target_index >= 0:
            self.ck_edition_combo.setCurrentIndex(target_index)
        if restore_edit_text:
            self.ck_edition_combo.setEditText(restore_edit_text)
        self.ck_edition_combo.blockSignals(False)

        if hasattr(self, "ck_status_label"):
            downloaded_at = str(meta.get("downloaded_at", ""))
            self.ck_status_label.setToolTip(
                f"系列清單：總數 {meta.get('total_sets', len(self.scryfall_sets))}；"
                f"官方 {meta.get('official_sets', 0)}；自訂 {meta.get('custom_sets', 0)}；"
                f"更新時間 {downloaded_at or '-'}"
            )

    def add_custom_scryfall_set_from_ui(self) -> None:
        code, ok = QInputDialog.getText(self, "新增系列", "系列代碼 / Set Code：\n例如 STH、FIN、EOE")
        if not ok:
            return
        code = clean_text(code).lower()
        if not re.fullmatch(r"[a-z0-9]{2,8}", code):
            QMessageBox.warning(self, "無法新增系列", "系列代碼只可使用英數字，長度建議 2～8 碼。")
            return

        name, ok = QInputDialog.getText(self, "新增系列", "系列名稱 / Set Name：", text=code.upper())
        if not ok:
            return
        name = clean_text(name)
        if not name:
            QMessageBox.warning(self, "無法新增系列", "系列名稱不可空白。")
            return

        try:
            item = add_custom_scryfall_set(code, name)
            self.refresh_scryfall_set_combo(preserve_current=False, show_errors=True)
            idx = self.ck_edition_combo.findData(str(item.get("code", "")))
            if idx >= 0:
                self.ck_edition_combo.setCurrentIndex(idx)
            self.statusBar().showMessage(f"已新增自訂系列：{item.get('name', '')} ({str(item.get('code', '')).upper()})", 5000)
        except Exception as exc:
            QMessageBox.warning(self, "新增系列失敗", f"自訂系列無法儲存：\n{exc}")


    def manage_custom_scryfall_sets_from_ui(self) -> None:
        dialog = ScryfallCustomSetsDialog(load_custom_scryfall_sets(), self)
        if dialog.exec() != QDialog.Accepted:
            return

        try:
            save_custom_scryfall_sets(dialog.custom_sets)
        except Exception as exc:
            QMessageBox.warning(self, "儲存系列失敗", f"自訂系列無法儲存：\n{exc}")
            return

        inventory_changed = False
        for record in self.db.get("mtg_inventory", []):
            old_code = clean_text(str(record.get("set_code", ""))).lower()
            update = dialog.inventory_update_map.get(old_code)
            if not update:
                continue
            record["set_code"] = str(update.get("new_code", old_code)).upper()
            record["edition"] = str(update.get("new_name", record.get("edition", "")))
            record["updated_at"] = now_text()
            inventory_changed = True

        if inventory_changed:
            save_db(self.db)

        self.refresh_scryfall_set_combo(preserve_current=True, show_errors=True)
        if hasattr(self, "refresh_mtg_inventory_filter_options"):
            self.refresh_mtg_inventory_filter_options(preserve_current=True)
        if hasattr(self, "refresh_mtg_inventory_table"):
            self.refresh_mtg_inventory_table()
        self.statusBar().showMessage("自訂系列已更新", 5000)
    def open_scryfall_set_tree_for_search(self) -> None:
        if not hasattr(self, "scryfall_sets") or not self.scryfall_sets:
            self.refresh_scryfall_set_combo(preserve_current=True, show_errors=True)
        current_code = str(self.ck_edition_combo.currentData() or "").strip().lower() if hasattr(self, "ck_edition_combo") else ""
        dialog = ScryfallSetTreeDialog(getattr(self, "scryfall_sets", []), current_code, self)
        if dialog.exec() != QDialog.Accepted:
            return
        code = clean_text(dialog.selected_code).lower()
        if code:
            idx = self.ck_edition_combo.findData(code)
            if idx >= 0:
                self.ck_edition_combo.setCurrentIndex(idx)
            else:
                self.ck_edition_combo.setEditText(code.upper())
        else:
            self.ck_edition_combo.setCurrentIndex(0)

    def open_scryfall_set_tree_for_mtg_inventory(self) -> None:
        try:
            sets, _meta, _source = load_scryfall_sets_local_only()
        except Exception as exc:
            QMessageBox.warning(self, "系列清單讀取失敗", f"無法讀取 Scryfall 系列清單：\n{exc}")
            return
        current_code = str(self.mtg_inventory_edition_filter.currentData() or "").strip().lower() if hasattr(self, "mtg_inventory_edition_filter") else ""
        dialog = ScryfallSetTreeDialog(sets, current_code, self)
        if dialog.exec() != QDialog.Accepted:
            return
        code = clean_text(dialog.selected_code).lower()
        if code:
            idx = self.mtg_inventory_edition_filter.findData(code)
            if idx >= 0:
                self.mtg_inventory_edition_filter.setCurrentIndex(idx)
            else:
                self.mtg_inventory_edition_filter.setEditText(code.upper())
        else:
            self.mtg_inventory_edition_filter.setCurrentIndex(0)
        self.refresh_mtg_inventory_table()

    def build_cardkingdom_tab(self) -> None:
        root = QVBoxLayout(self.cardkingdom_tab)

        search_group = QGroupBox("Scryfall 搜尋")
        form = QGridLayout(search_group)

        self.ck_name_edit = QLineEdit()
        self.ck_name_edit.setPlaceholderText("例如：Mox Diamond / 魔法力鑽石")

        self.ck_edition_combo = QComboBox()
        self.ck_edition_combo.setEditable(True)
        self.ck_edition_combo.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        self.ck_edition_combo.setToolTip("可從系列清單選擇，也可手動輸入系列名稱或 set code。")
        self.ck_tree_edition_btn = QPushButton("系列Tree")
        self.ck_tree_edition_btn.setToolTip("用樹狀清單選擇 Scryfall 系列。")
        self.ck_tree_edition_btn.clicked.connect(self.open_scryfall_set_tree_for_search)
        edition_row = QHBoxLayout()
        edition_row.addWidget(self.ck_edition_combo, 1)
        edition_row.addWidget(self.ck_tree_edition_btn)

        self.ck_format_combo = QComboBox()
        self.ck_format_combo.addItems(["全部"] + [v for v in SCRYFALL_FORMATS if v])
        self.ck_color_combo = QComboBox()
        self.ck_color_combo.addItems(["全部"] + [v for v in SCRYFALL_COLORS if v])
        self.ck_rarity_combo = QComboBox()
        self.ck_rarity_combo.addItems(["全部"] + [v for v in SCRYFALL_RARITIES if v])
        self.ck_type_combo = QComboBox()
        self.ck_type_combo.addItems(["全部"] + [v for v in SCRYFALL_TYPES if v])
        self.ck_language_combo = QComboBox()
        for label, code in SCRYFALL_LANGUAGES:
            self.ck_language_combo.addItem(label, code)
        self.ck_language_combo.setCurrentIndex(0)

        self.ck_search_btn = QPushButton("Search")
        self.ck_search_btn.setMinimumHeight(34)
        self.ck_search_btn.clicked.connect(lambda: self.search_cardkingdom(False))

        self.ck_update_cache_btn = QPushButton("更新系列清單")
        self.ck_update_cache_btn.setMinimumHeight(34)
        self.ck_update_cache_btn.setToolTip("重新下載 Scryfall sets 清單到本機 scryfall_sets_cache.json，用於 Edition 名稱對應。")
        self.ck_update_cache_btn.clicked.connect(self.update_cardkingdom_cache)

        self.ck_open_url_btn = QPushButton("開啟 Scryfall")
        self.ck_open_url_btn.clicked.connect(self.open_cardkingdom_search_url)
        self.ck_open_url_btn.setEnabled(False)

        self.ck_toggle_view_btn = QPushButton("卡圖檢視")
        self.ck_toggle_view_btn.clicked.connect(self.toggle_cardkingdom_view)

        form.addWidget(QLabel("Card name："), 0, 0)
        form.addWidget(self.ck_name_edit, 0, 1)
        form.addWidget(QLabel("系列 / Edition："), 0, 2)
        form.addLayout(edition_row, 0, 3)
        form.addWidget(QLabel("Format："), 1, 0)
        form.addWidget(self.ck_format_combo, 1, 1)
        form.addWidget(QLabel("Color："), 1, 2)
        form.addWidget(self.ck_color_combo, 1, 3)
        form.addWidget(QLabel("Rarity："), 2, 0)
        form.addWidget(self.ck_rarity_combo, 2, 1)
        form.addWidget(QLabel("Type："), 2, 2)
        form.addWidget(self.ck_type_combo, 2, 3)
        form.addWidget(QLabel("Language："), 3, 0)
        form.addWidget(self.ck_language_combo, 3, 1)
        form.addWidget(self.ck_search_btn, 0, 4)
        form.addWidget(self.ck_update_cache_btn, 1, 4)
        form.addWidget(self.ck_open_url_btn, 2, 4)
        form.addWidget(self.ck_toggle_view_btn, 3, 4)

        result_row = QHBoxLayout()

        left = QVBoxLayout()
        self.ck_status_label = QLabel(
            "尚未搜尋。資料來源為 Scryfall API；系列可從清單或系列Tree選擇。"
            "Language 可限制卡片語言；按「更新系列清單」會重新下載 Scryfall sets 清單。"
        )
        self.ck_status_label.setWordWrap(True)

        self.ck_table = QTableWidget(0, 10)
        self.ck_table.setHorizontalHeaderLabels([
            "#",
            "Card name",
            "Edition",
            "Rarity",
            "Collector #",
            "Type",
            "Color",
            "Language",
            "Prices",
            "URL",
        ])
        self.ck_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.ck_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        setup_stable_table_columns(self.ck_table, {
            0: 54,
            1: 260,
            2: 180,
            3: 90,
            4: 90,
            5: 220,
            6: 100,
            7: 110,
            8: 220,
            9: 260,
        })
        self.ck_table.verticalHeader().setVisible(False)
        self.ck_table.itemSelectionChanged.connect(self.on_cardkingdom_selected)

        self.ck_grid_scroll = QScrollArea()
        self.ck_grid_scroll.setWidgetResizable(True)
        self.ck_grid_widget = QWidget()
        self.ck_grid_layout = QGridLayout(self.ck_grid_widget)
        self.ck_grid_layout.setContentsMargins(8, 8, 8, 8)
        self.ck_grid_layout.setSpacing(12)
        self.ck_grid_scroll.setWidget(self.ck_grid_widget)
        self.ck_grid_view_enabled = True
        self.ck_table.hide()
        self.ck_grid_scroll.show()
        self.ck_toggle_view_btn.setText("表格檢視")

        page_row = QHBoxLayout()
        self.ck_prev_btn = QPushButton("上一頁")
        self.ck_next_btn = QPushButton("下一頁")
        self.ck_page_label = QLabel("第 0 / 0 頁")
        self.ck_prev_btn.clicked.connect(self.cardkingdom_prev_page)
        self.ck_next_btn.clicked.connect(self.cardkingdom_next_page)
        self.ck_prev_btn.setEnabled(False)
        self.ck_next_btn.setEnabled(False)
        page_row.addWidget(self.ck_prev_btn)
        page_row.addWidget(self.ck_next_btn)
        page_row.addWidget(self.ck_page_label)
        page_row.addStretch(1)

        left.addWidget(self.ck_status_label)
        left.addWidget(self.ck_table, 1)
        left.addWidget(self.ck_grid_scroll, 1)
        left.addLayout(page_row)

        detail_group = QGroupBox("選取資料")
        detail_layout = QVBoxLayout(detail_group)
        self.ck_image_preview = QLabel("選擇一筆資料可預覽圖片")
        self.ck_detail_label = QLabel("尚未選擇資料")
        self.ck_detail_label.setWordWrap(True)
        self.ck_open_card_btn = QPushButton("開啟卡片頁")
        self.ck_open_card_btn.clicked.connect(self.open_selected_cardkingdom_card)
        self.ck_open_card_btn.setEnabled(False)

        add_to_mtg_row = QHBoxLayout()
        self.ck_add_to_mtg_qty_spin = QSpinBox()
        self.ck_add_to_mtg_qty_spin.setRange(1, 999_999)
        self.ck_add_to_mtg_qty_spin.setValue(1)
        self.ck_add_to_mtg_btn = QPushButton("加入MTG庫存")
        self.ck_add_to_mtg_btn.clicked.connect(self.add_selected_scryfall_to_mtg_inventory)
        self.ck_add_to_mtg_btn.setEnabled(False)
        add_to_mtg_row.addWidget(QLabel("加入數量："))
        add_to_mtg_row.addWidget(self.ck_add_to_mtg_qty_spin)
        add_to_mtg_row.addWidget(self.ck_add_to_mtg_btn, 1)

        detail_layout.addWidget(self.ck_image_preview)
        detail_layout.addWidget(self.ck_detail_label, 1)
        detail_layout.addLayout(add_to_mtg_row)
        detail_layout.addWidget(self.ck_open_card_btn)

        result_row.addLayout(left, 3)
        result_row.addWidget(detail_group, 1)

        root.addWidget(search_group)
        root.addLayout(result_row, 1)
        self.refresh_scryfall_set_combo(preserve_current=False, show_errors=False)

    def cardkingdom_filters(self) -> dict[str, str]:
        def combo_value(combo: QComboBox) -> str:
            value = combo.currentText().strip()
            return "" if value == "全部" else value

        edition_text = self.ck_edition_combo.currentText().strip()
        edition_code = str(self.ck_edition_combo.currentData() or "").strip().lower()
        if edition_text == "全部系列":
            edition_text = ""
            edition_code = ""
        elif edition_code:
            selected_label = self.ck_edition_combo.itemText(self.ck_edition_combo.currentIndex()).strip()
            if edition_text and edition_text != selected_label and edition_text.lower() != edition_code:
                # 使用者在可編輯下拉框手動輸入其他系列名稱時，不沿用原本選項的 set code。
                edition_code = ""

        return {
            "name": self.ck_name_edit.text().strip(),
            "edition": edition_text,
            "set_code": edition_code,
            "format": combo_value(self.ck_format_combo),
            "color": combo_value(self.ck_color_combo),
            "rarity": combo_value(self.ck_rarity_combo),
            "type": combo_value(self.ck_type_combo),
            "language": str(self.ck_language_combo.currentData() or "").strip(),
        }

    def update_cardkingdom_cache(self) -> None:
        self.search_cardkingdom(True)

    def search_cardkingdom(self, refresh_cache: bool = False) -> None:
        if self.ck_worker and self.ck_worker.isRunning():
            QMessageBox.information(self, "搜尋中", "Scryfall 搜尋仍在進行中，請稍候。")
            return

        filters = self.cardkingdom_filters()
        self.ck_results = []
        self.ck_current_page = 0
        self.ck_last_url = build_cardkingdom_url(filters)
        self.ck_open_url_btn.setEnabled(True)
        self.ck_search_btn.setEnabled(False)
        self.ck_update_cache_btn.setEnabled(False)
        action_text = "正在更新 Scryfall 系列清單並搜尋..." if refresh_cache else "正在搜尋 Scryfall API..."
        self.ck_status_label.setText(f"{action_text}\nScryfall 頁面：{self.ck_last_url}")
        self.refresh_cardkingdom_table()

        self.ck_worker = ScryfallSearchWorker(filters, refresh_cache=refresh_cache, parent=self)
        self.ck_worker.completed.connect(self.on_cardkingdom_search_finished)
        self.ck_worker.start()

    def on_cardkingdom_search_finished(self, payload: object, error: str, url: str) -> None:
        self.ck_search_btn.setEnabled(True)
        self.ck_update_cache_btn.setEnabled(True)
        self.ck_last_url = url
        self.ck_open_url_btn.setEnabled(bool(url))

        if error:
            self.ck_results = []
            self.ck_current_page = 0
            self.refresh_cardkingdom_table()
            self.ck_status_label.setText(f"Scryfall 資料讀取失敗：{error}\n網址：{url}")
            QMessageBox.warning(self, "Scryfall 資料讀取失敗", f"無法取得資料：\n{error}\n\n網址：\n{url}")
            return

        data = payload if isinstance(payload, dict) else {"results": []}
        self.ck_results = list(data.get("results", [])) if isinstance(data.get("results", []), list) else []
        self.ck_current_page = 0
        self.refresh_scryfall_set_combo(preserve_current=True, show_errors=False)
        self.refresh_cardkingdom_table()

        sets_meta = data.get("sets_meta", {}) if isinstance(data.get("sets_meta", {}), dict) else {}
        downloaded_at = str(sets_meta.get("downloaded_at", ""))
        source_text = "重新下載" if data.get("sets_source") == "downloaded" else "本機快取/自訂"
        truncated_text = ""
        if data.get("truncated"):
            truncated_text = f"｜結果已達上限 {SCRYFALL_MAX_CARDS} 筆，建議增加 Card name 或 Edition 縮小範圍"

        self.ck_status_label.setText(
            f"搜尋完成：共顯示 {len(self.ck_results)} 筆；Scryfall 回傳總數約 {data.get('total_cards', len(self.ck_results))} 筆。每頁顯示 {SCRYFALL_PAGE_SIZE} 筆{truncated_text}\n"
            f"Scryfall query：{data.get('query', '')}\n"
            f"系列清單：{source_text}｜系列數：{data.get('sets_count', 0)}｜本機更新時間：{downloaded_at or '-'}\n"
            f"Scryfall 頁面：{url}"
        )
        if not self.ck_results:
            QMessageBox.information(self, "沒有結果", "沒有符合條件的 Scryfall 資料。可以放寬搜尋條件再試一次。")

    def refresh_cardkingdom_table(self) -> None:
        total = len(self.ck_results)
        total_pages = max(1, (total + SCRYFALL_PAGE_SIZE - 1) // SCRYFALL_PAGE_SIZE) if total else 0
        if total_pages:
            self.ck_current_page = max(0, min(self.ck_current_page, total_pages - 1))
        else:
            self.ck_current_page = 0

        start = self.ck_current_page * SCRYFALL_PAGE_SIZE
        end = start + SCRYFALL_PAGE_SIZE
        page_items = self.ck_results[start:end]

        self.ck_table.setRowCount(0)
        for row, item in enumerate(page_items):
            self.ck_table.insertRow(row)
            global_index = start + row + 1
            item_no = QTableWidgetItem(str(global_index))
            item_no.setData(Qt.UserRole, global_index - 1)
            self.ck_table.setItem(row, 0, item_no)
            self.ck_table.setItem(row, 1, QTableWidgetItem(str(item.get("name", ""))))
            self.ck_table.setItem(row, 2, QTableWidgetItem(str(item.get("edition", ""))))
            self.ck_table.setItem(row, 3, QTableWidgetItem(str(item.get("rarity", ""))))
            self.ck_table.setItem(row, 4, QTableWidgetItem(str(item.get("collector", ""))))
            self.ck_table.setItem(row, 5, QTableWidgetItem(str(item.get("type", ""))))
            self.ck_table.setItem(row, 6, QTableWidgetItem(str(item.get("colors", ""))))
            self.ck_table.setItem(row, 7, QTableWidgetItem(str(item.get("lang_label", item.get("lang", "")))))
            self.ck_table.setItem(row, 8, QTableWidgetItem(str(item.get("price", ""))))
            self.ck_table.setItem(row, 9, QTableWidgetItem(str(item.get("url", ""))))

        if hasattr(self, "ck_grid_scroll"):
            self.refresh_cardkingdom_grid(page_items, start)

        if total_pages:
            self.ck_page_label.setText(f"第 {self.ck_current_page + 1} / {total_pages} 頁｜共 {total} 筆")
        else:
            self.ck_page_label.setText("第 0 / 0 頁｜共 0 筆")
        self.ck_prev_btn.setEnabled(self.ck_current_page > 0)
        self.ck_next_btn.setEnabled(total_pages > 0 and self.ck_current_page < total_pages - 1)
        self.on_cardkingdom_selected()


    def toggle_cardkingdom_view(self) -> None:
        enabled = not bool(getattr(self, "ck_grid_view_enabled", False))
        self.ck_grid_view_enabled = enabled
        self.ck_table.setVisible(not enabled)
        self.ck_grid_scroll.setVisible(enabled)
        self.ck_toggle_view_btn.setText("表格檢視" if enabled else "卡圖檢視")
        self.refresh_cardkingdom_table()

    def refresh_cardkingdom_grid(self, page_items: list[dict[str, Any]], start_index: int) -> None:
        if not hasattr(self, "ck_grid_layout"):
            return
        clear_qt_layout(self.ck_grid_layout)
        if not bool(getattr(self, "ck_grid_view_enabled", False)):
            return
        columns = 5
        selected_global_index = -1
        current_row = self.ck_table.currentRow() if hasattr(self, "ck_table") else -1
        if current_row >= 0:
            selected_item = self.ck_table.item(current_row, 0)
            if selected_item is not None:
                try:
                    selected_global_index = int(selected_item.data(Qt.UserRole))
                except Exception:
                    selected_global_index = -1
        for offset, item in enumerate(page_items):
            global_index = start_index + offset
            title = str(item.get("name", ""))
            subtitle = "\n".join(part for part in [
                str(item.get("edition", "")),
                f"#{item.get('collector', '')}" if item.get("collector") else "",
                str(item.get("rarity", "")),
            ] if part)
            tile = CardGridTile(item, title, subtitle, lambda idx=global_index: self.select_cardkingdom_grid_item(idx), selected=(global_index == selected_global_index))
            self.ck_grid_layout.addWidget(tile, offset // columns, offset % columns)
        self.ck_grid_layout.setRowStretch((len(page_items) + columns - 1) // columns, 1)

    def select_cardkingdom_grid_item(self, index: int) -> None:
        if index < 0 or index >= len(self.ck_results):
            return
        page = index // SCRYFALL_PAGE_SIZE
        if page != self.ck_current_page:
            self.ck_current_page = page
            self.refresh_cardkingdom_table()
        row = index - self.ck_current_page * SCRYFALL_PAGE_SIZE
        if 0 <= row < self.ck_table.rowCount():
            self.ck_table.selectRow(row)
            self.on_cardkingdom_selected()
            item = self.ck_results[index]
            self.statusBar().showMessage(f"已選取 Scryfall 卡片：{item.get('name', '')}", 4000)
            if bool(getattr(self, "ck_grid_view_enabled", False)):
                page_start = self.ck_current_page * SCRYFALL_PAGE_SIZE
                self.refresh_cardkingdom_grid(self.ck_results[page_start:page_start + SCRYFALL_PAGE_SIZE], page_start)

    def selected_cardkingdom_item(self) -> dict[str, Any] | None:
        row = self.ck_table.currentRow()
        if row < 0:
            return None
        item = self.ck_table.item(row, 0)
        if not item:
            return None
        idx = item.data(Qt.UserRole)
        try:
            return self.ck_results[int(idx)]
        except Exception:
            return None

    def on_cardkingdom_selected(self) -> None:
        item = self.selected_cardkingdom_item()
        if not item:
            self.ck_detail_label.setText("尚未選擇資料")
            self.ck_open_card_btn.setEnabled(False)
            if hasattr(self, "ck_add_to_mtg_btn"):
                self.ck_add_to_mtg_btn.setEnabled(False)
            load_image_preview(self.ck_image_preview, "", "選擇一筆資料可預覽圖片")
            return

        self.ck_open_card_btn.setEnabled(bool(item.get("url")))
        if hasattr(self, "ck_add_to_mtg_btn"):
            self.ck_add_to_mtg_btn.setEnabled(True)
        self.ck_detail_label.setText(
            f"Card name：{item.get('name', '')}\n"
            f"English name：{item.get('english_name', '')}\n"
            f"Printed name：{item.get('printed_name', '')}\n"
            f"Edition：{item.get('edition', '')} ({item.get('set_code', '')})\n"
            f"Rarity：{item.get('rarity', '')}\n"
            f"Collector #：{item.get('collector', '')}\n"
            f"Type：{item.get('type', '')}\n"
            f"Color：{item.get('colors', '')}\n"
            f"Legal：{item.get('legalities', '')}\n"
            f"Price：{item.get('price', '')}\n"
            f"Language：{item.get('lang_label', item.get('lang', ''))}｜Released：{item.get('released_at', '')}\n\n"
            f"Text：{item.get('text', '')}\n\n"
            f"Scryfall ID：{item.get('scryfall_id', '')}\n"
            f"URL：{item.get('url', '')}"
        )
        self.load_remote_cardkingdom_image(str(item.get("image_url", "")))
        if bool(getattr(self, "ck_grid_view_enabled", False)):
            page_start = self.ck_current_page * SCRYFALL_PAGE_SIZE
            self.refresh_cardkingdom_grid(self.ck_results[page_start:page_start + SCRYFALL_PAGE_SIZE], page_start)

    def load_remote_cardkingdom_image(self, image_url: str) -> None:
        self.ck_image_preview.setAlignment(Qt.AlignCenter)
        self.ck_image_preview.setMinimumSize(180, 240)
        self.ck_image_preview.setStyleSheet("border: 1px solid #888; background: #fafafa; color: #666;")
        if not image_url:
            self.ck_image_preview.setPixmap(QPixmap())
            self.ck_image_preview.setText("無圖片")
            return
        try:
            request = Request(image_url, headers={"User-Agent": "CardInventory/1.0 (local desktop inventory app)"})
            with urlopen(request, timeout=10) as response:
                data = response.read()
            pixmap = QPixmap()
            if not pixmap.loadFromData(data):
                raise RuntimeError("圖片資料無法載入")
            self.ck_image_preview.setText("")
            self.ck_image_preview.setPixmap(pixmap.scaled(220, 300, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        except Exception:
            self.ck_image_preview.setPixmap(QPixmap())
            self.ck_image_preview.setText("圖片載入失敗")

    def cardkingdom_prev_page(self) -> None:
        if self.ck_current_page > 0:
            self.ck_current_page -= 1
            self.refresh_cardkingdom_table()

    def cardkingdom_next_page(self) -> None:
        total = len(self.ck_results)
        total_pages = max(1, (total + SCRYFALL_PAGE_SIZE - 1) // SCRYFALL_PAGE_SIZE) if total else 0
        if total_pages and self.ck_current_page < total_pages - 1:
            self.ck_current_page += 1
            self.refresh_cardkingdom_table()

    def open_cardkingdom_search_url(self) -> None:
        if self.ck_last_url:
            QDesktopServices.openUrl(QUrl(self.ck_last_url))

    def open_selected_cardkingdom_card(self) -> None:
        item = self.selected_cardkingdom_item()
        url = str(item.get("url", "")) if item else ""
        if url:
            QDesktopServices.openUrl(QUrl(url))

    def add_selected_scryfall_to_mtg_inventory(self) -> None:
        item = self.selected_cardkingdom_item()
        if not item:
            QMessageBox.warning(self, "無法加入", "請先在 Scryfall 搜尋結果選擇一張卡。")
            return

        qty = int(self.ck_add_to_mtg_qty_spin.value()) if hasattr(self, "ck_add_to_mtg_qty_spin") else 1
        if qty <= 0:
            QMessageBox.warning(self, "無法加入", "加入數量必須大於 0。")
            return

        self.db.setdefault("mtg_inventory", [])
        new_record = mtg_inventory_item_from_scryfall(item, qty)
        new_key = mtg_inventory_match_key(new_record)
        updated_existing = False
        target_record = new_record

        for record in self.db["mtg_inventory"]:
            if mtg_inventory_match_key(record) == new_key:
                record["quantity"] = int(record.get("quantity", 0) or 0) + qty
                # 用最新 Scryfall 搜尋結果更新基本資料，但保留使用者備註。 
                for key, value in new_record.items():
                    if key in {"id", "quantity", "created_at", "note", "ruten"}:
                        continue
                    if value not in (None, ""):
                        record[key] = value
                record["updated_at"] = now_text()
                target_record = record
                updated_existing = True
                break

        if not updated_existing:
            self.db["mtg_inventory"].append(new_record)

        ensure_ruten_item_fields(target_record)
        save_db(self.db)
        self.refresh_mtg_inventory_filter_options()
        self.refresh_mtg_inventory_table()
        if hasattr(self, "refresh_ruten_table"):
            self.refresh_ruten_table()
        if hasattr(self, "refresh_ruten_notifications_table"):
            self.refresh_ruten_notifications_table()
        if hasattr(self, "update_license_gated_controls"):
            self.update_license_gated_controls()
        if updated_existing and hasattr(self, "auto_push_local_ruten_change"):
            self.auto_push_local_ruten_change(target_record, "Scryfall 加入數量")
        self.statusBar().showMessage(
            f"已{'更新' if updated_existing else '加入'} MTG庫存：{target_record.get('name', '')} x {target_record.get('quantity', 0)}",
            5000,
        )
        QMessageBox.information(
            self,
            "完成",
            f"已{'更新既有' if updated_existing else '加入'} MTG庫存：\n"
            f"{target_record.get('name', '')}\n"
            f"本次加入數量：{qty}\n"
            f"目前數量：{target_record.get('quantity', 0)}",
        )

    def build_mtg_inventory_tab(self) -> None:
        root = QVBoxLayout(self.mtg_inventory_tab)

        filter_group = QGroupBox("MTG庫存篩選")
        filter_grid = QGridLayout(filter_group)

        self.mtg_inventory_search_edit = QLineEdit()
        self.mtg_inventory_search_edit.setPlaceholderText("搜尋卡名 / 系列 / 稀有度 / 類型 / 顏色 / 語言 / 價格 / 備註")
        self.mtg_inventory_search_edit.textChanged.connect(self.refresh_mtg_inventory_table)

        self.mtg_inventory_edition_filter = QComboBox()
        self.mtg_inventory_edition_filter.setEditable(True)
        self.mtg_inventory_edition_filter.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        self.mtg_inventory_edition_filter.setToolTip("可選 Scryfall 系列，也可手動輸入 Edition 或 Set Code。")
        self.mtg_inventory_edition_filter.currentTextChanged.connect(self.refresh_mtg_inventory_table)
        self.mtg_inventory_edition_tree_btn = QPushButton("系列Tree")
        self.mtg_inventory_edition_tree_btn.setToolTip("用樹狀清單選擇 Scryfall 系列。")
        self.mtg_inventory_edition_tree_btn.clicked.connect(self.open_scryfall_set_tree_for_mtg_inventory)

        self.mtg_inventory_format_filter = QComboBox()
        self.mtg_inventory_format_filter.addItems(["全部"] + [v for v in SCRYFALL_FORMATS if v])
        self.mtg_inventory_format_filter.currentIndexChanged.connect(self.refresh_mtg_inventory_table)

        self.mtg_inventory_color_filter = QComboBox()
        self.mtg_inventory_color_filter.addItems(["全部"] + [v for v in SCRYFALL_COLORS if v])
        self.mtg_inventory_color_filter.currentIndexChanged.connect(self.refresh_mtg_inventory_table)

        self.mtg_inventory_rarity_filter = QComboBox()
        self.mtg_inventory_rarity_filter.addItems(["全部"] + [v for v in SCRYFALL_RARITIES if v])
        self.mtg_inventory_rarity_filter.currentIndexChanged.connect(self.refresh_mtg_inventory_table)

        self.mtg_inventory_type_filter = QComboBox()
        self.mtg_inventory_type_filter.addItems(["全部"] + [v for v in SCRYFALL_TYPES if v])
        self.mtg_inventory_type_filter.currentIndexChanged.connect(self.refresh_mtg_inventory_table)

        self.mtg_inventory_language_filter = QComboBox()
        self.mtg_inventory_language_filter.addItem("全部語言", "")
        for label, code in SCRYFALL_LANGUAGES:
            if code:
                self.mtg_inventory_language_filter.addItem(label, code)
        self.mtg_inventory_language_filter.currentIndexChanged.connect(self.refresh_mtg_inventory_table)

        self.mtg_inventory_reset_filter_btn = QPushButton("清除篩選")
        self.mtg_inventory_reset_filter_btn.clicked.connect(self.reset_mtg_inventory_filters)

        self.mtg_inventory_open_btn = QPushButton("開啟卡片頁")
        self.mtg_inventory_open_btn.clicked.connect(self.open_selected_mtg_inventory_card)
        self.mtg_inventory_open_btn.setEnabled(False)

        self.mtg_inventory_edit_btn = QPushButton("修改選取MTG庫存")
        self.mtg_inventory_edit_btn.clicked.connect(self.edit_selected_mtg_inventory)

        self.mtg_inventory_delete_btn = QPushButton("刪除選取MTG庫存")
        self.mtg_inventory_delete_btn.clicked.connect(self.delete_selected_mtg_inventory)

        self.mtg_inventory_export_btn = QPushButton("匯出MTG庫存CSV")
        self.mtg_inventory_export_btn.clicked.connect(self.export_mtg_inventory_csv)

        self.mtg_inventory_list_ruten_btn = QPushButton("上架/編輯露天商品")
        self.mtg_inventory_list_ruten_btn.clicked.connect(self.upsert_selected_mtg_inventory_products)

        self.mtg_inventory_jump_ruten_btn = QPushButton("搜尋定位到露天賣場")
        self.mtg_inventory_jump_ruten_btn.clicked.connect(self.jump_selected_mtg_inventory_to_ruten)
        self.mtg_inventory_jump_ruten_btn.setEnabled(False)

        self.mtg_inventory_open_ruten_page_btn = QPushButton("開啟露天商品頁")
        self.mtg_inventory_open_ruten_page_btn.clicked.connect(self.open_selected_mtg_inventory_ruten_pages)
        self.mtg_inventory_open_ruten_page_btn.setEnabled(False)

        self.mtg_inventory_check_visible_btn = QPushButton("勾選目前列表")
        self.mtg_inventory_check_visible_btn.clicked.connect(lambda: self.set_visible_table_checks("mtg", True))
        self.mtg_inventory_clear_checks_btn = QPushButton("清除勾選")
        self.mtg_inventory_clear_checks_btn.clicked.connect(lambda: self.set_visible_table_checks("mtg", False))
        self.mtg_inventory_toggle_view_btn = QPushButton("卡圖檢視")
        self.mtg_inventory_toggle_view_btn.clicked.connect(self.toggle_mtg_inventory_view)

        filter_grid.addWidget(QLabel("搜尋："), 0, 0)
        filter_grid.addWidget(self.mtg_inventory_search_edit, 0, 1, 1, 3)
        filter_grid.addWidget(QLabel("Edition："), 0, 4)
        filter_grid.addWidget(self.mtg_inventory_edition_filter, 0, 5, 1, 2)
        filter_grid.addWidget(self.mtg_inventory_edition_tree_btn, 0, 7)
        filter_grid.addWidget(QLabel("Format："), 1, 0)
        filter_grid.addWidget(self.mtg_inventory_format_filter, 1, 1)
        filter_grid.addWidget(QLabel("Color："), 1, 2)
        filter_grid.addWidget(self.mtg_inventory_color_filter, 1, 3)
        filter_grid.addWidget(QLabel("Rarity："), 1, 4)
        filter_grid.addWidget(self.mtg_inventory_rarity_filter, 1, 5)
        filter_grid.addWidget(QLabel("Type："), 2, 0)
        filter_grid.addWidget(self.mtg_inventory_type_filter, 2, 1)
        filter_grid.addWidget(QLabel("Language："), 2, 2)
        filter_grid.addWidget(self.mtg_inventory_language_filter, 2, 3)
        filter_grid.addWidget(self.mtg_inventory_reset_filter_btn, 2, 4)
        filter_grid.addWidget(self.mtg_inventory_open_btn, 2, 5)
        filter_grid.addWidget(self.mtg_inventory_toggle_view_btn, 2, 6)
        filter_grid.addWidget(self.mtg_inventory_check_visible_btn, 3, 0)
        filter_grid.addWidget(self.mtg_inventory_clear_checks_btn, 3, 1)
        filter_grid.addWidget(self.mtg_inventory_jump_ruten_btn, 3, 2)
        filter_grid.addWidget(self.mtg_inventory_open_ruten_page_btn, 3, 3)
        filter_grid.addWidget(self.mtg_inventory_edit_btn, 3, 4)
        filter_grid.addWidget(self.mtg_inventory_delete_btn, 3, 5)
        filter_grid.addWidget(self.mtg_inventory_list_ruten_btn, 3, 6)
        filter_grid.addWidget(self.mtg_inventory_export_btn, 3, 7)

        self.mtg_inventory_table = QTableWidget(0, 11)
        self.mtg_inventory_table_base_headers = [
            "#",
            "Card name",
            "Edition",
            "Set",
            "Rarity",
            "Collector #",
            "Type",
            "Color",
            "Language",
            "數量",
            "Prices",
        ]
        self.mtg_inventory_table.setHorizontalHeaderLabels(self.mtg_inventory_table_base_headers)
        self.mtg_inventory_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.mtg_inventory_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        mtg_header = self.mtg_inventory_table.horizontalHeader()
        mtg_header.setSectionsClickable(True)
        mtg_header.sectionClicked.connect(self.on_mtg_inventory_header_clicked)
        setup_stable_table_columns(self.mtg_inventory_table, {
            0: 54,
            1: 260,
            2: 180,
            3: 80,
            4: 90,
            5: 90,
            6: 220,
            7: 100,
            8: 110,
            9: 70,
            10: 220,
        })
        self.mtg_inventory_table.verticalHeader().setVisible(False)
        self.mtg_inventory_table.itemSelectionChanged.connect(self.on_mtg_inventory_selected)
        self.mtg_inventory_table.itemChanged.connect(self.on_mtg_inventory_item_changed)
        self.mtg_inventory_table.itemDoubleClicked.connect(lambda _item: self.edit_selected_mtg_inventory())
        self.refresh_mtg_inventory_header_labels()

        self.mtg_inventory_grid_scroll = QScrollArea()
        self.mtg_inventory_grid_scroll.setWidgetResizable(True)
        self.mtg_inventory_grid_widget = QWidget()
        self.mtg_inventory_grid_layout = QGridLayout(self.mtg_inventory_grid_widget)
        self.mtg_inventory_grid_layout.setContentsMargins(8, 8, 8, 8)
        self.mtg_inventory_grid_layout.setSpacing(12)
        self.mtg_inventory_grid_scroll.setWidget(self.mtg_inventory_grid_widget)
        self.mtg_inventory_grid_view_enabled = True
        self.mtg_inventory_table.hide()
        self.mtg_inventory_grid_scroll.show()
        self.mtg_inventory_toggle_view_btn.setText("表格檢視")

        result_row = QHBoxLayout()

        left = QVBoxLayout()
        self.mtg_inventory_status_label = QLabel("MTG庫存尚未載入。選擇一張卡可在右側查看詳細資料。")
        self.mtg_inventory_status_label.setWordWrap(True)
        left.addWidget(self.mtg_inventory_status_label)
        left.addWidget(self.mtg_inventory_table, 1)
        left.addWidget(self.mtg_inventory_grid_scroll, 1)

        detail_group = QGroupBox("選取資料")
        detail_layout = QVBoxLayout(detail_group)
        self.mtg_inventory_image_preview = QLabel("選擇一筆 MTG 庫存可預覽圖片")
        self.mtg_inventory_detail_label = QLabel("尚未選擇 MTG 庫存")
        self.mtg_inventory_detail_label.setWordWrap(True)
        detail_layout.addWidget(self.mtg_inventory_image_preview)
        detail_layout.addWidget(self.mtg_inventory_detail_label, 1)

        result_row.addLayout(left, 3)
        result_row.addWidget(detail_group, 1)

        root.addWidget(filter_group)
        root.addLayout(result_row, 1)
        self.refresh_mtg_inventory_filter_options(preserve_current=False)

    def refresh_mtg_inventory_filter_options(self, preserve_current: bool = True) -> None:
        if not hasattr(self, "mtg_inventory_edition_filter"):
            return

        current_code = str(self.mtg_inventory_edition_filter.currentData() or "") if preserve_current else ""
        current_text = self.mtg_inventory_edition_filter.currentText().strip() if preserve_current else ""

        try:
            sets, _meta, _source = load_scryfall_sets_local_only()
        except Exception:
            sets = []

        official_items = sorted(
            sets,
            key=lambda x: (str(x.get("released_at", "")), str(x.get("name", "")).lower()),
            reverse=True,
        )

        existing_codes = {str(item.get("code", "")).lower() for item in official_items if item.get("code")}
        inventory_items: list[dict[str, Any]] = []
        for record in self.db.get("mtg_inventory", []):
            code = clean_text(str(record.get("set_code", ""))).lower()
            name = clean_text(str(record.get("edition", "")))
            if code and code not in existing_codes:
                inventory_items.append(make_custom_scryfall_set(code, name or code.upper()))
                existing_codes.add(code)

        combined_items = official_items + sorted(
            inventory_items,
            key=lambda x: (str(x.get("name", "")).lower(), str(x.get("code", ""))),
        )

        self.mtg_inventory_edition_filter.blockSignals(True)
        self.mtg_inventory_edition_filter.clear()
        self.mtg_inventory_edition_filter.addItem("全部系列", "")
        for item in combined_items:
            self.mtg_inventory_edition_filter.addItem(scryfall_set_label(item), str(item.get("code", "")).lower())

        target_index = 0
        restore_edit_text = ""
        if current_code:
            idx = self.mtg_inventory_edition_filter.findData(current_code)
            if idx >= 0:
                target_index = idx
            elif current_text and current_text != "全部系列":
                restore_edit_text = current_text
        elif current_text:
            idx = self.mtg_inventory_edition_filter.findText(current_text)
            if idx >= 0:
                target_index = idx
            elif current_text != "全部系列":
                restore_edit_text = current_text

        if self.mtg_inventory_edition_filter.count() > 0:
            self.mtg_inventory_edition_filter.setCurrentIndex(target_index)
        if restore_edit_text:
            self.mtg_inventory_edition_filter.setEditText(restore_edit_text)
        self.mtg_inventory_edition_filter.blockSignals(False)

    def reset_mtg_inventory_filters(self) -> None:
        if hasattr(self, "mtg_inventory_search_edit"):
            self.mtg_inventory_search_edit.clear()
        for attr in [
            "mtg_inventory_edition_filter",
            "mtg_inventory_format_filter",
            "mtg_inventory_color_filter",
            "mtg_inventory_rarity_filter",
            "mtg_inventory_type_filter",
            "mtg_inventory_language_filter",
        ]:
            combo = getattr(self, attr, None)
            if isinstance(combo, QComboBox):
                combo.setCurrentIndex(0)
        self.refresh_mtg_inventory_table()

    def mtg_inventory_filter_text(self, combo: QComboBox, all_labels: set[str] | None = None) -> str:
        all_labels = all_labels or {"全部", "全部系列", "全部語言"}
        value = combo.currentText().strip()
        return "" if value in all_labels else value

    def mtg_inventory_edition_filter_values(self) -> tuple[str, str]:
        if not hasattr(self, "mtg_inventory_edition_filter"):
            return "", ""
        combo = self.mtg_inventory_edition_filter
        edition_text = combo.currentText().strip()
        edition_code = str(combo.currentData() or "").strip().lower()
        if edition_text == "全部系列":
            return "", ""
        if edition_code:
            selected_label = combo.itemText(combo.currentIndex()).strip()
            if edition_text and edition_text != selected_label and edition_text.lower() != edition_code:
                edition_code = ""
        return edition_text, edition_code

    def mtg_color_matches_filter(self, record_colors: str, color_filter: str) -> bool:
        if not color_filter or color_filter == "全部":
            return True

        color_text = clean_text(record_colors)
        lower_text = color_text.lower()
        compact = re.sub(r"[^A-Z]", "", color_text.upper())
        color_letters = {letter for letter in compact if letter in "WUBRG"}

        name_to_code = {
            "White": "W",
            "Blue": "U",
            "Black": "B",
            "Red": "R",
            "Green": "G",
        }
        name_aliases = {
            "White": ["white", "白"],
            "Blue": ["blue", "藍"],
            "Black": ["black", "黑"],
            "Red": ["red", "紅"],
            "Green": ["green", "綠"],
        }

        if color_filter == "Colorless":
            return (not color_letters) or lower_text in {"", "c", "colorless", "無色"}
        if color_filter == "Multicolor":
            return len(color_letters) >= 2

        code = name_to_code.get(color_filter, "")
        if code and code in color_letters:
            return True
        return any(alias in lower_text for alias in name_aliases.get(color_filter, []))

    def mtg_format_matches_filter(self, record: dict[str, Any], format_filter: str) -> bool:
        if not format_filter or format_filter == "全部":
            return True
        legalities = clean_text(str(record.get("legalities", ""))).lower()
        if not legalities or legalities == "-":
            return False
        return format_filter.lower() in {part.strip().lower() for part in re.split(r"[,/|]", legalities)} or format_filter.lower() in legalities

    def mtg_record_matches_current_filters(self, record: dict[str, Any]) -> bool:
        search = self.mtg_inventory_search_edit.text().strip().lower() if hasattr(self, "mtg_inventory_search_edit") else ""
        edition_text, edition_code = self.mtg_inventory_edition_filter_values()
        format_filter = self.mtg_inventory_filter_text(self.mtg_inventory_format_filter) if hasattr(self, "mtg_inventory_format_filter") else ""
        color_filter = self.mtg_inventory_filter_text(self.mtg_inventory_color_filter) if hasattr(self, "mtg_inventory_color_filter") else ""
        rarity_filter = self.mtg_inventory_filter_text(self.mtg_inventory_rarity_filter) if hasattr(self, "mtg_inventory_rarity_filter") else ""
        type_filter = self.mtg_inventory_filter_text(self.mtg_inventory_type_filter) if hasattr(self, "mtg_inventory_type_filter") else ""
        lang_filter = str(self.mtg_inventory_language_filter.currentData() or "").strip().lower() if hasattr(self, "mtg_inventory_language_filter") else ""

        if edition_code and clean_text(str(record.get("set_code", ""))).lower() != edition_code:
            return False
        if edition_text and not edition_code:
            edition_needle = edition_text.lower()
            edition_haystack = " ".join([
                str(record.get("edition", "")),
                str(record.get("set_code", "")),
            ]).lower()
            if edition_needle not in edition_haystack:
                return False

        if lang_filter and clean_text(str(record.get("lang", ""))).lower() != lang_filter:
            return False

        if rarity_filter and clean_text(str(record.get("rarity", ""))).lower() != rarity_filter.lower():
            return False

        if type_filter:
            type_haystack = " ".join([
                str(record.get("type", "")),
                str(record.get("oracle_type", "")),
            ]).lower()
            if type_filter.lower() not in type_haystack:
                return False

        if not self.mtg_color_matches_filter(str(record.get("colors", "")), color_filter):
            return False

        if not self.mtg_format_matches_filter(record, format_filter):
            return False

        ruten = ensure_ruten_item_fields(record)
        haystack = " ".join([
            str(record.get("id", "")),
            str(record.get("name", "")),
            str(record.get("english_name", "")),
            str(record.get("printed_name", "")),
            str(record.get("edition", "")),
            str(record.get("set_code", "")),
            str(record.get("rarity", "")),
            str(record.get("collector", "")),
            str(record.get("type", "")),
            str(record.get("oracle_type", "")),
            str(record.get("colors", "")),
            str(record.get("lang_label", "")),
            str(record.get("legalities", "")),
            str(record.get("price", "")),
            str(record.get("note", "")),
            str(ruten.get("item_id", "")),
            str(ruten.get("spec_id", "")),
            str(ruten.get("custom_no", "")),
            str(ruten.get("title", "")),
        ]).lower()
        if search and search not in haystack:
            return False

        return True

    def get_mtg_inventory_item(self, record_id: str) -> dict[str, Any] | None:
        for record in self.db.get("mtg_inventory", []):
            if record.get("id") == record_id:
                return record
        return None

    def selected_mtg_inventory_id(self) -> str:
        row = self.mtg_inventory_table.currentRow()
        if row < 0:
            return ""
        item = self.mtg_inventory_table.item(row, 0)
        return str(item.data(Qt.UserRole)) if item else ""

    def selected_mtg_inventory_item(self) -> dict[str, Any] | None:
        record_id = self.selected_mtg_inventory_id()
        return self.get_mtg_inventory_item(record_id) if record_id else None

    def checked_mtg_inventory_ids(self) -> list[str]:
        if not hasattr(self, "mtg_inventory_table"):
            return []
        ids = checked_record_ids_from_table(self.mtg_inventory_table)
        self.mtg_inventory_checked_ids = set(ids)
        return ids

    def checked_mtg_inventory_records(self) -> list[dict[str, Any]]:
        records: list[dict[str, Any]] = []
        for record_id in self.checked_mtg_inventory_ids():
            record = self.get_mtg_inventory_item(record_id)
            if record:
                records.append(record)
        return records

    def selected_or_checked_mtg_inventory_records(self) -> list[dict[str, Any]]:
        checked = self.checked_mtg_inventory_records()
        if checked:
            return checked
        record = self.selected_mtg_inventory_item()
        return [record] if record else []

    def on_mtg_inventory_item_changed(self, item: QTableWidgetItem) -> None:
        if bool(getattr(self, "_updating_mtg_inventory_table", False)):
            return
        if item.column() != 0:
            return
        record_id = clean_text(str(item.data(Qt.UserRole)))
        if not record_id:
            return
        if item.checkState() == Qt.CheckState.Checked:
            self.mtg_inventory_checked_ids.add(record_id)
        else:
            self.mtg_inventory_checked_ids.discard(record_id)
        count = len(self.mtg_inventory_checked_ids)
        self.statusBar().showMessage(f"MTG庫存已勾選 {count} 筆" if count else "MTG庫存已清除勾選", 3000)
        if hasattr(self, "mtg_inventory_status_label"):
            records = self.current_mtg_inventory_records()
            total_qty = sum(int(record.get("quantity", 0) or 0) for record in records)
            checked_text = f"，已勾選 {count} 筆" if count else ""
            self.mtg_inventory_status_label.setText(f"共 {len(records)} 筆 MTG 庫存，合計數量 {total_qty}{checked_text}。選擇一張卡可在右側查看詳細資料。")

    def refresh_mtg_inventory_header_labels(self) -> None:
        if not hasattr(self, "mtg_inventory_table") or not hasattr(self, "mtg_inventory_table_base_headers"):
            return

        labels = []
        sort_column = int(getattr(self, "mtg_inventory_sort_column", 5))
        reverse = bool(getattr(self, "mtg_inventory_sort_reverse", False))
        for index, title in enumerate(self.mtg_inventory_table_base_headers):
            if index == sort_column:
                labels.append(f"{title} {'▼' if reverse else '▲'}")
            else:
                labels.append(title)
        self.mtg_inventory_table.setHorizontalHeaderLabels(labels)

    def on_mtg_inventory_header_clicked(self, column: int) -> None:
        if column < 0:
            return

        current_column = int(getattr(self, "mtg_inventory_sort_column", 5))
        if column == current_column:
            self.mtg_inventory_sort_reverse = not bool(getattr(self, "mtg_inventory_sort_reverse", False))
        else:
            self.mtg_inventory_sort_column = column
            self.mtg_inventory_sort_reverse = False

        self.refresh_mtg_inventory_header_labels()
        self.refresh_mtg_inventory_table()

    def mtg_inventory_sort_value(self, record: dict[str, Any], column: int, original_index: int) -> tuple[Any, ...]:
        if column == 0:
            return ((0, original_index),)
        if column == 1:
            return natural_sort_key(record.get("name", ""))
        if column == 2:
            return natural_sort_key(record.get("edition", ""))
        if column == 3:
            return natural_sort_key(record.get("set_code", ""))
        if column == 4:
            rarity_rank = {
                "common": 0,
                "uncommon": 1,
                "rare": 2,
                "mythic": 3,
                "special": 4,
                "bonus": 5,
            }
            rarity = clean_text(str(record.get("rarity", ""))).lower()
            return ((0, rarity_rank.get(rarity, 99)), (1, natural_sort_key(rarity)))
        if column == 5:
            return collector_number_sort_key(record.get("collector", ""))
        if column == 6:
            return natural_sort_key(record.get("type", ""))
        if column == 7:
            colors = clean_text(str(record.get("colors", ""))) or "Colorless"
            return natural_sort_key(colors)
        if column == 8:
            return natural_sort_key(record.get("lang_label", record.get("lang", "")))
        if column == 9:
            return ((0, int(record.get("quantity", 0) or 0)),)
        if column == 10:
            return mtg_price_sort_key(record.get("price", ""))
        return natural_sort_key(record.get("name", ""))

    def sorted_mtg_inventory_records(self, records: list[dict[str, Any]]) -> list[dict[str, Any]]:
        sort_column = int(getattr(self, "mtg_inventory_sort_column", 5))
        reverse = bool(getattr(self, "mtg_inventory_sort_reverse", False))

        indexed_records = list(enumerate(records))
        non_empty: list[tuple[int, dict[str, Any]]] = []
        empty: list[tuple[int, dict[str, Any]]] = []

        def column_text(record: dict[str, Any]) -> str:
            if sort_column == 0:
                return "#"
            if sort_column == 1:
                return clean_text(str(record.get("name", "")))
            if sort_column == 2:
                return clean_text(str(record.get("edition", "")))
            if sort_column == 3:
                return clean_text(str(record.get("set_code", "")))
            if sort_column == 4:
                return clean_text(str(record.get("rarity", "")))
            if sort_column == 5:
                return clean_text(str(record.get("collector", "")))
            if sort_column == 6:
                return clean_text(str(record.get("type", "")))
            if sort_column == 7:
                return clean_text(str(record.get("colors", ""))) or "Colorless"
            if sort_column == 8:
                return clean_text(str(record.get("lang_label", record.get("lang", ""))))
            if sort_column == 9:
                return str(record.get("quantity", 0) or 0)
            if sort_column == 10:
                return clean_text(str(record.get("price", "")))
            return clean_text(str(record.get("name", "")))

        for item in indexed_records:
            _index, record = item
            if column_text(record):
                non_empty.append(item)
            else:
                empty.append(item)

        sorted_items = sorted(
            non_empty,
            key=lambda item: (self.mtg_inventory_sort_value(item[1], sort_column, item[0]), natural_sort_key(item[1].get("name", "")), item[0]),
            reverse=reverse,
        )
        # Empty values remain at the bottom for both ascending and descending sorts.
        sorted_items.extend(sorted(empty, key=lambda item: item[0]))
        return [record for _index, record in sorted_items]

    def current_mtg_inventory_records(self) -> list[dict[str, Any]]:
        records = []
        for record in self.db.get("mtg_inventory", []):
            if self.mtg_record_matches_current_filters(record):
                records.append(record)
        return self.sorted_mtg_inventory_records(records)

    def refresh_mtg_inventory_table(self) -> None:
        if not hasattr(self, "mtg_inventory_table"):
            return

        records = self.current_mtg_inventory_records()

        self._updating_mtg_inventory_table = True
        self.mtg_inventory_table.setRowCount(0)
        total_qty = 0
        try:
            for row, record in enumerate(records):
                total_qty += int(record.get("quantity", 0) or 0)
                self.mtg_inventory_table.insertRow(row)
                record_id = clean_text(str(record.get("id", "")))
                item_no = checkable_row_item(str(row + 1), record_id, record_id in self.mtg_inventory_checked_ids)
                self.mtg_inventory_table.setItem(row, 0, item_no)
                self.mtg_inventory_table.setItem(row, 1, QTableWidgetItem(str(record.get("name", ""))))
                self.mtg_inventory_table.setItem(row, 2, QTableWidgetItem(str(record.get("edition", ""))))
                self.mtg_inventory_table.setItem(row, 3, QTableWidgetItem(str(record.get("set_code", ""))))
                self.mtg_inventory_table.setItem(row, 4, QTableWidgetItem(str(record.get("rarity", ""))))
                self.mtg_inventory_table.setItem(row, 5, QTableWidgetItem(str(record.get("collector", ""))))
                self.mtg_inventory_table.setItem(row, 6, QTableWidgetItem(str(record.get("type", ""))))
                self.mtg_inventory_table.setItem(row, 7, QTableWidgetItem(str(record.get("colors", ""))))
                self.mtg_inventory_table.setItem(row, 8, QTableWidgetItem(str(record.get("lang_label", record.get("lang", "")))))
                self.mtg_inventory_table.setItem(row, 9, QTableWidgetItem(str(record.get("quantity", 0))))
                self.mtg_inventory_table.setItem(row, 10, QTableWidgetItem(str(record.get("price", ""))))
        finally:
            self._updating_mtg_inventory_table = False

        checked_count = len(self.checked_mtg_inventory_records()) if hasattr(self, "mtg_inventory_table") else 0
        checked_text = f"，已勾選 {checked_count} 筆" if checked_count else ""
        summary_text = f"共 {len(records)} 筆 MTG 庫存，合計數量 {total_qty}{checked_text}。選擇一張卡可在右側查看詳細資料。"
        if hasattr(self, "mtg_inventory_status_label"):
            self.mtg_inventory_status_label.setText(summary_text)
        elif hasattr(self, "mtg_inventory_detail_label"):
            self.mtg_inventory_detail_label.setText(summary_text)
        if hasattr(self, "mtg_inventory_grid_scroll"):
            self.refresh_mtg_inventory_grid(records)

    def toggle_mtg_inventory_view(self) -> None:
        enabled = not bool(getattr(self, "mtg_inventory_grid_view_enabled", False))
        self.mtg_inventory_grid_view_enabled = enabled
        self.mtg_inventory_table.setVisible(not enabled)
        self.mtg_inventory_grid_scroll.setVisible(enabled)
        self.mtg_inventory_toggle_view_btn.setText("表格檢視" if enabled else "卡圖檢視")
        self.refresh_mtg_inventory_table()

    def refresh_mtg_inventory_grid(self, records: list[dict[str, Any]]) -> None:
        if not hasattr(self, "mtg_inventory_grid_layout"):
            return
        clear_qt_layout(self.mtg_inventory_grid_layout)
        if not bool(getattr(self, "mtg_inventory_grid_view_enabled", False)):
            return
        columns = 5
        selected_record_id = ""
        current_row = self.mtg_inventory_table.currentRow() if hasattr(self, "mtg_inventory_table") else -1
        if current_row >= 0:
            selected_item = self.mtg_inventory_table.item(current_row, 0)
            if selected_item is not None:
                selected_record_id = clean_text(str(selected_item.data(Qt.UserRole)))
        for index, record in enumerate(records):
            record_id = clean_text(str(record.get("id", "")))
            title = str(record.get("name", ""))
            subtitle = "\n".join(part for part in [
                str(record.get("edition", "")) or str(record.get("set_code", "")),
                f"#{record.get('collector', '')}" if record.get("collector") else "",
                f"庫存：{record.get('quantity', 0)}",
            ] if part)
            tile = CardGridTile(record, title, subtitle, lambda rid=record_id: self.select_mtg_inventory_grid_record(rid), checked=record_id in self.mtg_inventory_checked_ids, selected=(record_id == selected_record_id))
            self.mtg_inventory_grid_layout.addWidget(tile, index // columns, index % columns)
        self.mtg_inventory_grid_layout.setRowStretch((len(records) + columns - 1) // columns, 1)

    def select_mtg_inventory_grid_record(self, record_id: str) -> None:
        if not record_id:
            return
        if self.select_table_row_by_record_id(self.mtg_inventory_table, record_id):
            self.on_mtg_inventory_selected()
            record = self.get_mtg_inventory_item(record_id)
            self.statusBar().showMessage(f"已選取 MTG庫存：{record.get('name', '') if record else record_id}", 4000)
            if bool(getattr(self, "mtg_inventory_grid_view_enabled", False)):
                self.refresh_mtg_inventory_grid(self.current_mtg_inventory_records())

    def on_mtg_inventory_selected(self) -> None:
        record = self.selected_mtg_inventory_item()
        if not record:
            self.mtg_inventory_open_btn.setEnabled(False)
            if hasattr(self, "mtg_inventory_jump_ruten_btn"):
                self.mtg_inventory_jump_ruten_btn.setEnabled(False)
            if hasattr(self, "mtg_inventory_open_ruten_page_btn"):
                self.mtg_inventory_open_ruten_page_btn.setEnabled(False)
            self.mtg_inventory_detail_label.setText("尚未選擇 MTG 庫存")
            load_image_preview(self.mtg_inventory_image_preview, "", "選擇一筆 MTG 庫存可預覽圖片")
            return

        self.mtg_inventory_open_btn.setEnabled(bool(record.get("url")))
        if hasattr(self, "mtg_inventory_jump_ruten_btn"):
            self.mtg_inventory_jump_ruten_btn.setEnabled(True)
        if hasattr(self, "mtg_inventory_open_ruten_page_btn"):
            self.mtg_inventory_open_ruten_page_btn.setEnabled(bool(make_ruten_item_web_url(ensure_ruten_item_fields(record).get("item_id", ""))))
        self.mtg_inventory_detail_label.setText(
            f"Card name：{record.get('name', '')}\n"
            f"English name：{record.get('english_name', '')}\n"
            f"Printed name：{record.get('printed_name', '')}\n"
            f"Edition：{record.get('edition', '')} ({record.get('set_code', '')})\n"
            f"Rarity：{record.get('rarity', '')}｜Collector #：{record.get('collector', '')}\n"
            f"Type：{record.get('type', '')}\n"
            f"Color：{record.get('colors', '')}｜Language：{record.get('lang_label', record.get('lang', ''))}\n"
            f"數量：{record.get('quantity', 0)}\n"
            f"Price：{record.get('price', '')}\n"
            f"Legal：{record.get('legalities', '')}\n"
            f"Released：{record.get('released_at', '')}\n\n"
            f"Text：{record.get('text', '')}\n\n"
            f"備註：{record.get('note', '')}\n"
            f"Scryfall ID：{record.get('scryfall_id', '')}\n"
            f"URL：{record.get('url', '')}"
        )
        self.load_remote_mtg_inventory_image(str(record.get("image_url", "")))
        if bool(getattr(self, "mtg_inventory_grid_view_enabled", False)):
            self.refresh_mtg_inventory_grid(self.current_mtg_inventory_records())

    def load_remote_mtg_inventory_image(self, image_url: str) -> None:
        self.mtg_inventory_image_preview.setAlignment(Qt.AlignCenter)
        self.mtg_inventory_image_preview.setMinimumSize(180, 240)
        self.mtg_inventory_image_preview.setStyleSheet("border: 1px solid #888; background: #fafafa; color: #666;")
        if not image_url:
            self.mtg_inventory_image_preview.setPixmap(QPixmap())
            self.mtg_inventory_image_preview.setText("無圖片")
            return
        try:
            request = Request(image_url, headers={"User-Agent": "CardInventory/1.0 (local desktop inventory app)"})
            with urlopen(request, timeout=10) as response:
                data = response.read()
            pixmap = QPixmap()
            if not pixmap.loadFromData(data):
                raise RuntimeError("圖片資料無法載入")
            self.mtg_inventory_image_preview.setText("")
            self.mtg_inventory_image_preview.setPixmap(pixmap.scaled(220, 300, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        except Exception:
            self.mtg_inventory_image_preview.setPixmap(QPixmap())
            self.mtg_inventory_image_preview.setText("圖片載入失敗")

    def edit_selected_mtg_inventory(self) -> None:
        record = self.selected_mtg_inventory_item()
        if not record:
            QMessageBox.warning(self, "無法修改", "請先選擇一筆 MTG 庫存。")
            return

        dialog = MTGInventoryEditDialog(record, self)
        if dialog.exec() != QDialog.Accepted:
            return

        record.update(dialog.values())
        record["updated_at"] = now_text()
        save_db(self.db)
        ensure_ruten_item_fields(record)
        self.refresh_mtg_inventory_filter_options()
        self.refresh_mtg_inventory_table()
        if hasattr(self, "refresh_ruten_table"):
            self.refresh_ruten_table()
        if hasattr(self, "auto_push_local_ruten_change"):
            self.auto_push_local_ruten_change(record, "MTG庫存修改")
        self.statusBar().showMessage(f"已修改 MTG 庫存：{record.get('name', '')}", 5000)

    def delete_selected_mtg_inventory(self) -> None:
        records = self.selected_or_checked_mtg_inventory_records()
        if not records:
            QMessageBox.warning(self, "無法刪除", "請先選擇或勾選 MTG 庫存。")
            return

        if len(records) == 1:
            record = records[0]
            message = f"確定要刪除這筆 MTG 庫存？\n\n{record.get('name', '')}\n數量：{record.get('quantity', 0)}"
        else:
            names = "\n".join(str(record.get("name", "")) for record in records[:8])
            more = f"\n...另有 {len(records) - 8} 筆" if len(records) > 8 else ""
            message = f"確定要刪除已勾選的 {len(records)} 筆 MTG 庫存？\n\n{names}{more}"
        if QMessageBox.question(self, "確認刪除", message) != QMessageBox.Yes:
            return

        record_ids = {str(record.get("id", "")) for record in records}
        self.db["mtg_inventory"] = [r for r in self.db.get("mtg_inventory", []) if str(r.get("id", "")) not in record_ids]
        self.mtg_inventory_checked_ids.difference_update(record_ids)
        self.ruten_checked_ids.difference_update(record_ids)
        save_db(self.db)
        self.refresh_mtg_inventory_filter_options()
        self.refresh_mtg_inventory_table()
        if hasattr(self, "refresh_ruten_table"):
            self.refresh_ruten_table()
        self.statusBar().showMessage(f"MTG 庫存已刪除 {len(record_ids)} 筆", 5000)

    def open_selected_mtg_inventory_card(self) -> None:
        record = self.selected_mtg_inventory_item()
        url = str(record.get("url", "")) if record else ""
        if url:
            QDesktopServices.openUrl(QUrl(url))

    def build_ruten_tab(self) -> None:
        root = QVBoxLayout(self.ruten_tab)

        settings_group = QGroupBox("露天同步控制")
        settings_grid = QGridLayout(settings_group)

        self.ruten_status_label = QLabel("尚未連線")
        self.ruten_status_label.setWordWrap(True)
        self.ruten_settings_btn = QPushButton("設定露天 API")
        self.ruten_settings_btn.clicked.connect(self.open_ruten_settings_dialog)
        self.ruten_test_btn = QPushButton("測試連線")
        self.ruten_test_btn.clicked.connect(self.test_ruten_api)
        self.ruten_logistic_btn = QPushButton("設定物流/付款")
        self.ruten_logistic_btn.clicked.connect(self.open_ruten_logistic_dialog)
        self.ruten_query_remote_btn = QPushButton("更新選取商品狀態")
        self.ruten_query_remote_btn.clicked.connect(self.refresh_selected_ruten_remote_item)
        self.ruten_sync_remote_list_btn = QPushButton("從露天匯入/更新")
        self.ruten_sync_remote_list_btn.clicked.connect(lambda _checked=False: self.sync_ruten_product_list(show_message=True))
        self.ruten_two_way_sync_btn = QPushButton("安全雙向同步")
        self.ruten_two_way_sync_btn.clicked.connect(self.safe_bidirectional_ruten_sync)
        self.ruten_auto_order_check = QCheckBox("自動查新訂單")
        self.ruten_auto_order_check.setChecked(bool(self.db.get("ruten_settings", {}).get("auto_order_check", False)))
        self.ruten_auto_order_check.stateChanged.connect(self.on_ruten_auto_settings_changed)
        self.ruten_auto_order_minutes_spin = QSpinBox()
        self.ruten_auto_order_minutes_spin.setRange(1, 1440)
        self.ruten_auto_order_minutes_spin.setValue(max(1, to_int(self.db.get("ruten_settings", {}).get("auto_order_minutes", 5)) or 5))
        self.ruten_auto_order_minutes_spin.valueChanged.connect(self.on_ruten_auto_settings_changed)
        self.ruten_auto_local_push_check = QCheckBox("本地變動自動調整上架數量")
        self.ruten_auto_local_push_check.setChecked(bool(self.db.get("ruten_settings", {}).get("auto_push_local_changes", False)))
        self.ruten_auto_local_push_check.stateChanged.connect(self.on_ruten_auto_settings_changed)
        self.ruten_auto_offline_zero_check = QCheckBox("露天上架數量0自動下架")
        self.ruten_auto_offline_zero_check.setChecked(bool(self.db.get("ruten_settings", {}).get("auto_offline_zero_stock", False)))
        self.ruten_auto_offline_zero_check.stateChanged.connect(self.on_ruten_auto_settings_changed)
        self.ruten_auto_online_positive_check = QCheckBox("露天上架數量>0自動上架")
        self.ruten_auto_online_positive_check.setChecked(bool(self.db.get("ruten_settings", {}).get("auto_online_positive_stock", False)))
        self.ruten_auto_online_positive_check.stateChanged.connect(self.on_ruten_auto_settings_changed)

        self.ruten_search_edit = QLineEdit()
        self.ruten_search_edit.setPlaceholderText("搜尋卡名 / 英文名 / Set / Collector / 露天商品ID / 自用料號")
        self.ruten_search_edit.textChanged.connect(self.on_ruten_filter_changed)
        self.ruten_filter_combo = QComboBox()
        self.ruten_filter_combo.addItems(["全部", "已配對", "未配對", "疑似配對", "配對衝突", "已填露天商品ID", "尚未填露天商品ID", "允許批次同步", "暫停批次同步", "本地有庫存", "本地已售完", "露天有庫存", "露天已售完", "露天匯入待確認"] )
        self.ruten_filter_combo.currentIndexChanged.connect(self.on_ruten_filter_changed)
        self.ruten_page_size_combo = QComboBox()
        self.ruten_page_size_combo.addItems(["20", "50", "100"])
        self.ruten_page_size_combo.setCurrentText(str(self.ruten_settings().get("page_size", 50) or 50))
        self.ruten_page_size_combo.currentIndexChanged.connect(self.on_ruten_page_size_changed)
        self.ruten_prev_page_btn = QPushButton("上一頁")
        self.ruten_prev_page_btn.clicked.connect(lambda: self.go_ruten_page(-1))
        self.ruten_next_page_btn = QPushButton("下一頁")
        self.ruten_next_page_btn.clicked.connect(lambda: self.go_ruten_page(1))
        self.ruten_page_label = QLabel("第 0 / 0 頁，共 0 筆")
        self.ruten_check_visible_btn = QPushButton("勾選目前頁")
        self.ruten_check_visible_btn.clicked.connect(lambda: self.set_visible_table_checks("ruten", True))
        self.ruten_check_filtered_btn = QPushButton("勾選目前搜尋結果")
        self.ruten_check_filtered_btn.clicked.connect(lambda: self.set_filtered_ruten_checks(True))
        self.ruten_clear_checks_btn = QPushButton("清除所有勾選")
        self.ruten_clear_checks_btn.clicked.connect(self.clear_all_ruten_checks)
        self.ruten_toggle_view_btn = QPushButton("卡圖檢視")
        self.ruten_toggle_view_btn.clicked.connect(self.toggle_ruten_view)

        settings_grid.addWidget(QLabel("連線狀態："), 0, 0)
        settings_grid.addWidget(self.ruten_status_label, 0, 1, 1, 5)
        settings_grid.addWidget(self.ruten_settings_btn, 1, 0)
        settings_grid.addWidget(self.ruten_test_btn, 1, 1)
        settings_grid.addWidget(self.ruten_logistic_btn, 1, 2)
        settings_grid.addWidget(self.ruten_query_remote_btn, 1, 3)
        settings_grid.addWidget(self.ruten_sync_remote_list_btn, 1, 4)
        settings_grid.addWidget(self.ruten_two_way_sync_btn, 1, 5)
        settings_grid.addWidget(self.ruten_auto_order_check, 2, 0)
        settings_grid.addWidget(QLabel("每幾分鐘："), 2, 1)
        settings_grid.addWidget(self.ruten_auto_order_minutes_spin, 2, 2)
        settings_grid.addWidget(self.ruten_auto_local_push_check, 2, 3)
        settings_grid.addWidget(self.ruten_auto_offline_zero_check, 2, 4)
        settings_grid.addWidget(self.ruten_auto_online_positive_check, 2, 5)
        settings_grid.addWidget(QLabel("搜尋："), 3, 0)
        settings_grid.addWidget(self.ruten_search_edit, 3, 1, 1, 3)
        settings_grid.addWidget(QLabel("篩選："), 3, 4)
        settings_grid.addWidget(self.ruten_filter_combo, 3, 5)
        settings_grid.addWidget(QLabel("每頁："), 4, 0)
        settings_grid.addWidget(self.ruten_page_size_combo, 4, 1)
        settings_grid.addWidget(self.ruten_prev_page_btn, 4, 2)
        settings_grid.addWidget(self.ruten_next_page_btn, 4, 3)
        settings_grid.addWidget(self.ruten_page_label, 4, 4, 1, 2)
        settings_grid.addWidget(self.ruten_check_visible_btn, 5, 0)
        settings_grid.addWidget(self.ruten_check_filtered_btn, 5, 1)
        settings_grid.addWidget(self.ruten_clear_checks_btn, 5, 2)
        settings_grid.addWidget(self.ruten_toggle_view_btn, 5, 3)
        self.ruten_table = QTableWidget(0, 15)
        self.ruten_table.setHorizontalHeaderLabels([
            "#",
            "卡圖",
            "批次同步",
            "MTG卡名",
            "Set",
            "Collector",
            "本地總庫存",
            "露天數量",
            "配對狀態",
            "露天商品ID",
            "規格ID",
            "露天售價",
            "露天狀態",
            "最後同步",
            "最後錯誤",
        ])
        self.ruten_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.ruten_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.ruten_table.verticalHeader().setVisible(False)
        setup_stable_table_columns(self.ruten_table, {
            0: 48,
            1: 82,
            2: 90,
            3: 260,
            4: 90,
            5: 100,
            6: 90,
            7: 90,
            8: 90,
            9: 130,
            10: 90,
            11: 80,
            12: 110,
            13: 160,
            14: 320,
        })
        self.ruten_table.itemSelectionChanged.connect(self.on_ruten_selected)
        self.ruten_table.itemChanged.connect(self.on_ruten_item_changed)

        self.ruten_grid_scroll = QScrollArea()
        self.ruten_grid_scroll.setWidgetResizable(True)
        self.ruten_grid_widget = QWidget()
        self.ruten_grid_layout = QGridLayout(self.ruten_grid_widget)
        self.ruten_grid_layout.setContentsMargins(8, 8, 8, 8)
        self.ruten_grid_layout.setSpacing(12)
        self.ruten_grid_scroll.setWidget(self.ruten_grid_widget)
        self.ruten_grid_scroll.hide()

        btn_row = QHBoxLayout()
        self.ruten_jump_mtg_btn = QPushButton("搜尋定位到MTG庫存")
        self.ruten_jump_mtg_btn.clicked.connect(self.jump_selected_ruten_to_mtg_inventory)
        self.ruten_jump_mtg_btn.setEnabled(False)
        self.ruten_open_page_btn = QPushButton("開啟商品網頁")
        self.ruten_open_page_btn.clicked.connect(self.open_selected_ruten_product_pages)
        self.ruten_open_page_btn.setEnabled(False)
        self.ruten_upsert_product_btn = QPushButton("上架/編輯露天商品")
        self.ruten_upsert_product_btn.clicked.connect(self.upsert_selected_ruten_products)
        self.ruten_upload_image_btn = QPushButton("上傳/更新露天卡圖")
        self.ruten_upload_image_btn.clicked.connect(self.upload_selected_ruten_image)
        self.ruten_offline_btn = QPushButton("下架露天商品")
        self.ruten_offline_btn.clicked.connect(lambda: self.set_selected_ruten_online_state(False))
        self.ruten_operation_log_btn = QPushButton("查看操作紀錄")
        self.ruten_operation_log_btn.clicked.connect(self.show_ruten_operation_log)
        for button in [
            self.ruten_jump_mtg_btn,
            self.ruten_open_page_btn,
            self.ruten_upsert_product_btn,
            self.ruten_upload_image_btn,
            self.ruten_offline_btn,
            self.ruten_operation_log_btn,
        ]:
            btn_row.addWidget(button)
        btn_row.addStretch(1)

        order_group = QGroupBox("訂單通知")
        order_layout = QVBoxLayout(order_group)
        order_controls = QHBoxLayout()
        self.ruten_order_status_combo = QComboBox()
        for label, value in [
            ("全部", "All"),
            ("尚未付款", "Unpaid"),
            ("待確認", "ToBeConfirmed"),
            ("待出貨", "ReadyToShip"),
            ("已出貨", "Shipped"),
            ("待取消", "InCancel"),
            ("已取消", "Cancelled"),
        ]:
            self.ruten_order_status_combo.addItem(label, value)
        self.ruten_order_start_edit = QLineEdit((datetime.now() - timedelta(days=30)).strftime("%Y%m%d000000"))
        self.ruten_order_end_edit = QLineEdit(datetime.now().strftime("%Y%m%d%H%M%S"))
        self.ruten_order_query_btn = QPushButton("更新訂單通知")
        self.ruten_order_query_btn.clicked.connect(lambda _checked=False: self.query_ruten_orders(show_message=True))
        self.ruten_order_manual_deduct_btn = QPushButton("手動扣庫存")
        self.ruten_order_manual_deduct_btn.clicked.connect(lambda: self.manual_adjust_selected_ruten_order("deduct"))
        self.ruten_order_manual_restore_btn = QPushButton("手動補回庫存")
        self.ruten_order_manual_restore_btn.clicked.connect(lambda: self.manual_adjust_selected_ruten_order("restore"))
        self.ruten_order_repair_match_btn = QPushButton("修正訂單配對")
        self.ruten_order_repair_match_btn.clicked.connect(self.repair_selected_ruten_order_match)
        self.ruten_order_auto_apply_check = QCheckBox("查到訂單後自動扣本地庫存")
        self.ruten_order_auto_apply_check.setChecked(bool(self.db.get("ruten_settings", {}).get("auto_apply_orders", False)))
        order_controls.addWidget(QLabel("狀態："))
        order_controls.addWidget(self.ruten_order_status_combo)
        order_controls.addWidget(QLabel("開始："))
        order_controls.addWidget(self.ruten_order_start_edit)
        order_controls.addWidget(QLabel("結束："))
        order_controls.addWidget(self.ruten_order_end_edit)
        order_controls.addWidget(self.ruten_order_auto_apply_check)
        order_controls.addWidget(self.ruten_order_query_btn)
        order_controls.addWidget(self.ruten_order_manual_deduct_btn)
        order_controls.addWidget(self.ruten_order_manual_restore_btn)
        order_controls.addWidget(self.ruten_order_repair_match_btn)
        order_controls.addStretch(1)

        self.ruten_notifications_table = QTableWidget(0, 11)
        self.ruten_notifications_table.setHorizontalHeaderLabels([
            "記錄時間",
            "訂單編號",
            "訂單狀態",
            "露天商品ID",
            "商品",
            "數量",
            "金額",
            "配對MTG",
            "已扣庫存",
            "已補庫存",
            "處理結果",
        ])
        self.ruten_notifications_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.ruten_notifications_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.ruten_notifications_table.verticalHeader().setVisible(False)
        setup_stable_table_columns(self.ruten_notifications_table, {
            0: 160,
            1: 140,
            2: 90,
            3: 130,
            4: 300,
            5: 70,
            6: 90,
            7: 180,
            8: 80,
            9: 80,
            10: 360,
        })

        order_layout.addLayout(order_controls)
        order_layout.addWidget(self.ruten_notifications_table, 1)

        root.addWidget(settings_group)
        root.addWidget(self.ruten_table, 2)
        root.addWidget(self.ruten_grid_scroll, 2)
        root.addLayout(btn_row)
        root.addWidget(order_group, 1)


    def selected_ruten_notification(self) -> dict[str, Any] | None:
        if not hasattr(self, "ruten_notifications_table"):
            return None
        row = self.ruten_notifications_table.currentRow()
        if row < 0:
            return None
        key_item = self.ruten_notifications_table.item(row, 0)
        key = clean_text(str(key_item.data(Qt.UserRole))) if key_item else ""
        if not key:
            return None
        for item in self.db.get("ruten_notifications", []):
            if clean_text(str(item.get("key", ""))) == key:
                return item
        return None

    def manual_adjust_selected_ruten_order(self, mode: str) -> None:
        notification = self.selected_ruten_notification()
        if not notification:
            QMessageBox.warning(self, "無法處理", "請先在訂單通知表選擇一筆訂單商品。")
            return
        matched_id = clean_text(str(notification.get("matched_mtg_id", "")))
        record = self.get_mtg_inventory_item(matched_id) if matched_id else None
        if not record:
            QMessageBox.warning(self, "無法處理", "這筆訂單尚未配對 MTG庫存，請先按「修正訂單配對」。")
            return
        qty = max(1, to_int(notification.get("quantity", 1)) or 1)
        action = "扣除" if mode == "deduct" else "補回"
        if QMessageBox.question(self, f"確認手動{action}庫存", f"商品：{record.get('name', '')}\n數量：{qty}\n\n確定要手動{action}本地庫存？") != QMessageBox.Yes:
            return
        processing = self.db.setdefault("ruten_order_processing", {})
        key = clean_text(str(notification.get("key", "")))
        proc = processing.get(key) if isinstance(processing.get(key), dict) else {}
        old_qty = max(0, to_int(record.get("quantity", 0)))
        ruten = ensure_ruten_item_fields(record)
        if mode == "deduct":
            new_qty = max(0, old_qty - qty)
            record["quantity"] = new_qty
            proc["applied_qty"] = max(to_int(proc.get("applied_qty", 0)), qty)
            proc["manual_deduct_at"] = now_text()
            proc["deduct_before_qty"] = old_qty
            proc["deduct_after_qty"] = new_qty
            notification["applied_to_inventory"] = True
            notification["result"] = f"已手動扣 MTG庫存：{old_qty} -> {new_qty}"
            ruten["remote_stock"] = max(0, to_int(ruten.get("remote_stock", 0)) - qty)
            if bool(ruten.get("auto_restock", False)):
                set_ruten_listing_qty(record, min(to_int(ruten.get("restock_target", 1)) or 1, max(0, to_int(record.get("quantity", 0)))))
            else:
                set_ruten_listing_qty(record, max(0, to_int(ruten.get("remote_stock", 0))))
        else:
            new_qty = old_qty + qty
            record["quantity"] = new_qty
            proc["restored_qty"] = max(to_int(proc.get("restored_qty", 0)), qty)
            proc["manual_restore_at"] = now_text()
            proc["restore_before_qty"] = old_qty
            proc["restore_after_qty"] = new_qty
            notification["restored_to_inventory"] = True
            notification["result"] = f"已手動補回 MTG庫存：{old_qty} -> {new_qty}"
            ruten["remote_stock"] = max(0, to_int(ruten.get("remote_stock", 0)) + qty)
            if bool(ruten.get("auto_restock", False)):
                set_ruten_listing_qty(record, min(to_int(ruten.get("restock_target", 1)) or 1, max(0, to_int(record.get("quantity", 0)))))
            else:
                set_ruten_listing_qty(record, max(0, to_int(ruten.get("remote_stock", 0))))
        record["updated_at"] = now_text()
        self.append_ruten_operation_log(
            f"手動{action}訂單庫存",
            "成功",
            record,
            {"order_id": notification.get("order_id", ""), "qty": qty, "before_qty": old_qty, "after_qty": record.get("quantity", 0), "notification_key": key},
        )
        proc["key"] = key
        proc["matched_mtg_id"] = record.get("id", "")
        proc["matched_name"] = record.get("name", "")
        proc["current_local_qty"] = record.get("quantity", 0)
        processing[key] = proc
        update_ruten_pairing_conflicts(self.db)
        save_db(self.db)
        self.refresh_mtg_inventory_table()
        self.refresh_ruten_table()
        self.refresh_ruten_notifications_table()
        QMessageBox.information(self, "完成", notification.get("result", "已處理"))

    def repair_selected_ruten_order_match(self) -> None:
        notification = self.selected_ruten_notification()
        if not notification:
            QMessageBox.warning(self, "無法修正", "請先在訂單通知表選擇一筆訂單商品。")
            return
        keyword_default = clean_text(str(notification.get("item_name", ""))) or clean_text(str(notification.get("custom_no", "")))
        keyword, ok = QInputDialog.getText(self, "搜尋 MTG庫存配對", "輸入卡名 / 英文名 / Set / Collector / 自用料號：", text=keyword_default)
        if not ok:
            return
        keyword = clean_text(keyword).lower()
        candidates: list[dict[str, Any]] = []
        for record in self.db.get("mtg_inventory", []):
            ruten = ensure_ruten_item_fields(record)
            haystack = " ".join([
                str(record.get("name", "")), str(record.get("english_name", "")), str(record.get("edition", "")),
                str(record.get("set_code", "")), str(record.get("collector", "")), str(ruten.get("custom_no", "")),
                str(ruten.get("item_id", "")), str(ruten.get("title", "")),
            ]).lower()
            if not keyword or keyword in haystack:
                candidates.append(record)
        if not candidates:
            QMessageBox.information(self, "沒有結果", "找不到符合關鍵字的 MTG庫存。")
            return
        labels = []
        for record in candidates[:80]:
            ruten = ensure_ruten_item_fields(record)
            labels.append(f"{record.get('name','')}｜{record.get('set_code','')} #{record.get('collector','')}｜本地 {record.get('quantity',0)}｜ID {ruten.get('item_id','') or '-'}")
        choice, ok = QInputDialog.getItem(self, "選擇配對商品", "選擇這筆訂單對應的 MTG庫存：", labels, 0, False)
        if not ok or not choice:
            return
        selected_index = labels.index(choice)
        record = candidates[selected_index]
        notification["matched_mtg_id"] = record.get("id", "")
        notification["result"] = f"已手動配對 MTG庫存：{record.get('name', '')}"
        key = clean_text(str(notification.get("key", "")))
        processing = self.db.setdefault("ruten_order_processing", {})
        proc = processing.get(key) if isinstance(processing.get(key), dict) else {}
        proc.update({
            "key": key,
            "matched_mtg_id": record.get("id", ""),
            "matched_name": record.get("name", ""),
            "manual_match_at": now_text(),
        })
        processing[key] = proc
        ruten = ensure_ruten_item_fields(record)
        if notification.get("item_id") and not clean_text(str(ruten.get("item_id", ""))):
            ruten["item_id"] = clean_text(str(notification.get("item_id", "")))
        if notification.get("spec_id") and not clean_text(str(ruten.get("spec_id", ""))):
            ruten["spec_id"] = clean_text(str(notification.get("spec_id", "")))
        if notification.get("custom_no") and not clean_text(str(ruten.get("custom_no", ""))):
            ruten["custom_no"] = clean_text(str(notification.get("custom_no", "")))
        ruten["match_status"] = "已配對"
        ruten["match_note"] = "由訂單通知手動配對。"
        self.append_ruten_operation_log(
            "修正訂單配對",
            "成功",
            record,
            {"order_id": notification.get("order_id", ""), "item_id": notification.get("item_id", ""), "spec_id": notification.get("spec_id", ""), "notification_key": key},
        )
        update_ruten_pairing_conflicts(self.db)
        save_db(self.db)
        self.refresh_mtg_inventory_table()
        self.refresh_ruten_table()
        self.refresh_ruten_notifications_table()
        QMessageBox.information(self, "完成", f"已配對：{record.get('name', '')}")

    def confirm_ruten_batch_action(self, title: str, records: list[dict[str, Any]], action_text: str) -> bool:
        if not records:
            return False
        status_counts: dict[str, int] = {}
        unbound = 0
        zero_local = 0
        listing_zero = 0
        for record in records:
            ruten = ensure_ruten_item_fields(record)
            status_label = self.ruten_status_text(str(ruten.get("status", "unknown")))
            status_counts[status_label] = status_counts.get(status_label, 0) + 1
            if not clean_text(str(ruten.get("item_id", ""))):
                unbound += 1
            if max(0, to_int(record.get("quantity", 0))) <= 0:
                zero_local += 1
            if ruten_listing_qty(record) <= 0:
                listing_zero += 1
        status_text = "\n".join(f"- {name}：{count} 筆" for name, count in sorted(status_counts.items())) or "- 無狀態資料"
        message = (
            f"即將{action_text} {len(records)} 筆商品。\n\n"
            f"狀態摘要：\n{status_text}\n\n"
            f"未綁定露天ID：{unbound} 筆\n"
            f"本地總庫存為 0：{zero_local} 筆\n"
            f"露天上架數量為 0：{listing_zero} 筆\n\n"
            "確定執行？"
        )
        return QMessageBox.question(self, title, message) == QMessageBox.Yes

    def ruten_settings(self) -> dict[str, Any]:
        return ensure_ruten_settings(self.db)

    def ruten_client(self) -> RutenApiClient:
        settings = dict(self.ruten_settings())
        license_status = evaluate_license(use_network=False)
        settings["__license_allowed"] = bool(license_status.get("ok", False))
        settings["__license_reason"] = clean_text(str(license_status.get("message", "程式尚未啟用。")))
        return RutenApiClient(settings)

    def open_ruten_settings_dialog(self) -> None:
        settings = self.ruten_settings()
        dialog = RutenSettingsDialog(settings, self)
        if dialog.exec() != QDialog.Accepted:
            return
        settings.update(dialog.values())
        save_db(self.db)
        self.apply_ruten_settings_to_controls()
        self.restart_ruten_timers()
        self.update_ruten_status_label()
        self.ruten_status_label.setText("露天 API 已儲存。")

    def query_current_ruten_logistic_default(self) -> None:
        settings = self.ruten_settings()
        client = self.ruten_client()
        if not client.is_ready():
            QMessageBox.warning(self, "尚未設定 API", "請先設定露天 API 金鑰後再查詢物流/付款。")
            return
        try:
            response = client.get_default_logistic()
            if not ruten_response_ok(response):
                raise RuntimeError(ruten_response_message(response))
            remote_values = ruten_extract_logistic_payload(response)
            if not remote_values:
                raise RuntimeError("露天沒有回傳可辨識的物流/付款預設檔。請先到露天後台或本程式的『設定物流/付款』建立預設檔。")
            settings.update(remote_values)
            settings["last_logistic_api_status"] = "正常"
            settings["last_logistic_check_at"] = now_text()
            settings["last_logistic_error"] = ""
            settings["last_product_api_status"] = "正常"
            settings["last_api_status"] = "正常"
            settings["last_success_at"] = now_text()
            settings["last_error"] = ""
            save_db(self.db)
            self.update_ruten_status_label()
            self.append_ruten_operation_log("查詢物流/付款預設檔", "成功", None, ruten_default_logistic_payload(settings))
            QMessageBox.information(self, "已套用目前物流/付款", ruten_logistic_settings_summary(settings))
        except Exception as exc:
            error_text = str(exc)
            settings["last_logistic_api_status"] = "異常"
            settings["last_logistic_check_at"] = now_text()
            settings["last_logistic_error"] = error_text
            settings["last_failure_at"] = now_text()
            settings["last_error"] = error_text
            save_db(self.db)
            self.update_ruten_status_label()
            self.append_ruten_operation_log("查詢物流/付款預設檔", "失敗", None, {}, error_text)
            QMessageBox.warning(self, "查詢失敗", error_text)

    def open_ruten_logistic_dialog(self) -> None:
        settings = self.ruten_settings()
        client = self.ruten_client()
        if client.is_ready():
            try:
                response = client.get_default_logistic()
                if ruten_response_ok(response):
                    remote_values = ruten_extract_logistic_payload(response)
                    if remote_values:
                        settings.update(remote_values)
                        settings["last_logistic_api_status"] = "正常"
                        settings["last_logistic_check_at"] = now_text()
                        settings["last_logistic_error"] = ""
                else:
                    settings["last_logistic_api_status"] = "異常"
                    settings["last_logistic_check_at"] = now_text()
                    settings["last_logistic_error"] = ruten_response_message(response)
            except Exception as exc:
                settings["last_logistic_api_status"] = "異常"
                settings["last_logistic_check_at"] = now_text()
                settings["last_logistic_error"] = str(exc)

        dialog = RutenLogisticDefaultDialog(settings, self)
        if dialog.exec() != QDialog.Accepted:
            save_db(self.db)
            self.update_ruten_status_label()
            return

        settings.update(dialog.values())
        save_db(self.db)

        if not client.is_ready():
            self.update_ruten_status_label()
            QMessageBox.information(self, "已儲存", "物流/付款設定已儲存在程式內。API 金鑰設定完成後即可套用到露天。")
            return

        try:
            response = client.set_default_logistic(ruten_default_logistic_payload(settings))
            if not ruten_response_ok(response):
                raise RuntimeError(ruten_response_message(response))
            settings["last_logistic_api_status"] = "正常"
            settings["last_logistic_check_at"] = now_text()
            settings["last_logistic_error"] = ""
            settings["last_product_api_status"] = "正常"
            settings["last_api_status"] = "正常"
            settings["last_success_at"] = now_text()
            settings["last_error"] = ""
            save_db(self.db)
            self.update_ruten_status_label()
            QMessageBox.information(self, "完成", "已套用露天物流/付款預設檔。")
        except Exception as exc:
            settings["last_logistic_api_status"] = "異常"
            settings["last_logistic_check_at"] = now_text()
            settings["last_logistic_error"] = str(exc)
            settings["last_failure_at"] = now_text()
            settings["last_error"] = str(exc)
            save_db(self.db)
            self.update_ruten_status_label()
            QMessageBox.warning(self, "設定失敗", str(exc))

    def ensure_ruten_logistic_default_for_create(self) -> None:
        settings = self.ruten_settings()
        client = self.ruten_client()
        response = client.get_default_logistic()
        if not ruten_response_ok(response):
            raise RuntimeError("查詢露天物流/付款預設檔失敗：" + ruten_response_message(response))
        remote_values = ruten_extract_logistic_payload(response)
        if not remote_values or not remote_values.get("default_logistic_info"):
            raise RuntimeError("露天新增商品預設物流/付款尚未設定。請先按『設定物流/付款』，在視窗內查詢目前設定或建立物流/付款預設檔。")
        settings.update(remote_values)
        settings["last_logistic_api_status"] = "正常"
        settings["last_logistic_check_at"] = now_text()
        settings["last_logistic_error"] = ""
        save_db(self.db)
        self.update_ruten_status_label()

    def apply_ruten_settings_to_controls(self) -> None:
        settings = self.ruten_settings()
        if hasattr(self, "ruten_order_auto_apply_check"):
            self.ruten_order_auto_apply_check.setChecked(bool(settings.get("auto_apply_orders", False)))
        if hasattr(self, "ruten_auto_order_check"):
            self.ruten_auto_order_check.blockSignals(True)
            self.ruten_auto_order_check.setChecked(bool(settings.get("auto_order_check", False)))
            self.ruten_auto_order_check.blockSignals(False)
        if hasattr(self, "ruten_auto_order_minutes_spin"):
            self.ruten_auto_order_minutes_spin.blockSignals(True)
            self.ruten_auto_order_minutes_spin.setValue(max(1, to_int(settings.get("auto_order_minutes", 5)) or 5))
            self.ruten_auto_order_minutes_spin.blockSignals(False)
        if hasattr(self, "ruten_auto_local_push_check"):
            self.ruten_auto_local_push_check.blockSignals(True)
            self.ruten_auto_local_push_check.setChecked(bool(settings.get("auto_push_local_changes", False)))
            self.ruten_auto_local_push_check.blockSignals(False)
        if hasattr(self, "ruten_auto_offline_zero_check"):
            self.ruten_auto_offline_zero_check.blockSignals(True)
            self.ruten_auto_offline_zero_check.setChecked(bool(settings.get("auto_offline_zero_stock", False)))
            self.ruten_auto_offline_zero_check.blockSignals(False)
        if hasattr(self, "ruten_auto_online_positive_check"):
            self.ruten_auto_online_positive_check.blockSignals(True)
            self.ruten_auto_online_positive_check.setChecked(bool(settings.get("auto_online_positive_stock", False)))
            self.ruten_auto_online_positive_check.blockSignals(False)

    def on_ruten_auto_settings_changed(self, *_args: Any) -> None:
        settings = self.ruten_settings()
        if hasattr(self, "ruten_auto_order_check"):
            settings["auto_order_check"] = bool(self.ruten_auto_order_check.isChecked())
        if hasattr(self, "ruten_auto_order_minutes_spin"):
            settings["auto_order_minutes"] = int(self.ruten_auto_order_minutes_spin.value())
        if hasattr(self, "ruten_auto_local_push_check"):
            settings["auto_push_local_changes"] = bool(self.ruten_auto_local_push_check.isChecked())
        if hasattr(self, "ruten_auto_offline_zero_check"):
            settings["auto_offline_zero_stock"] = bool(self.ruten_auto_offline_zero_check.isChecked())
        if hasattr(self, "ruten_auto_online_positive_check"):
            settings["auto_online_positive_stock"] = bool(self.ruten_auto_online_positive_check.isChecked())
        save_db(self.db)
        self.restart_ruten_timers()
        self.update_ruten_status_label()

    def restart_ruten_timers(self) -> None:
        if not hasattr(self, "ruten_order_timer"):
            return
        settings = self.ruten_settings()
        minutes = max(1, to_int(settings.get("auto_order_minutes", 5)) or 5)
        if bool(settings.get("auto_order_check", False)) and self.ruten_client().is_ready():
            self.ruten_order_timer.start(minutes * 60 * 1000)
        else:
            self.ruten_order_timer.stop()

    def update_ruten_status_label(self) -> None:
        if not hasattr(self, "ruten_status_label"):
            return
        settings = self.ruten_settings()
        api = str(settings.get("last_api_status", "未測試"))
        product = str(settings.get("last_product_api_status", "未測試"))
        order = str(settings.get("last_order_api_status", "未測試"))
        logistic = str(settings.get("last_logistic_api_status", "未測試"))
        success = str(settings.get("last_success_at", ""))
        failure = str(settings.get("last_failure_at", ""))
        error = str(settings.get("last_error", ""))
        auto_text = "自動查單開啟" if settings.get("auto_order_check", False) else "自動查單關閉"
        license_status = evaluate_license(use_network=False)
        license_text = "授權：已啟用" if license_status.get("ok") else f"授權：{license_status.get('label', '未啟用')}"
        detail = f"{license_text}｜露天 API：{api}｜商品：{product}｜訂單：{order}｜物流付款：{logistic}｜{auto_text}"
        if success:
            detail += f"｜最後成功：{success}"
        if failure:
            detail += f"｜最後失敗：{failure}"
        if error:
            detail += f"｜錯誤：{error}"
        self.ruten_status_label.setText(detail)

    def set_ruten_api_status(self, product_ok: bool | None = None, order_ok: bool | None = None, error: str = "") -> None:
        settings = self.ruten_settings()
        now = now_text()
        if product_ok is not None:
            settings["last_product_api_status"] = "正常" if product_ok else "異常"
        if order_ok is not None:
            settings["last_order_api_status"] = "正常" if order_ok else "異常"
        ok_values = [v for v in (product_ok, order_ok) if v is not None]
        if ok_values and all(ok_values):
            settings["last_api_status"] = "正常"
            settings["last_success_at"] = now
            settings["last_error"] = ""
        elif ok_values and any(ok_values):
            settings["last_api_status"] = "部分正常"
            settings["last_success_at"] = now
            settings["last_failure_at"] = now
            settings["last_error"] = error
        elif ok_values:
            settings["last_api_status"] = "異常"
            settings["last_failure_at"] = now
            settings["last_error"] = error
        save_db(self.db)
        self.update_ruten_status_label()

    def test_ruten_api(self) -> None:
        client = self.ruten_client()
        product_ok = False
        order_ok = False
        messages: list[str] = []
        try:
            product_payload = client.list_products(status="all", offset=1, limit=1)
            product_ok = ruten_response_ok(product_payload)
            if not product_ok:
                messages.append(f"商品 API：{ruten_response_message(product_payload)}")
        except Exception as exc:
            messages.append(f"商品 API：{exc}")
        try:
            end = datetime.now()
            start = end - timedelta(days=1)
            order_payload = client.list_orders("All", start.strftime("%Y%m%d000000"), end.strftime("%Y%m%d%H%M%S"), page=1, page_size=10)
            order_ok = ruten_response_ok(order_payload)
            if not order_ok:
                messages.append(f"訂單 API：{ruten_response_message(order_payload)}")
        except Exception as exc:
            messages.append(f"訂單 API：{exc}")

        error_text = "；".join(messages)
        self.set_ruten_api_status(product_ok=product_ok, order_ok=order_ok, error=error_text)
        if product_ok and order_ok:
            if QMessageBox.question(self, "露天連線成功", "商品 API 與訂單 API 都連線成功。要現在從露天匯入/更新賣場商品嗎？") == QMessageBox.Yes:
                self.sync_ruten_product_list(show_message=True)
            else:
                QMessageBox.information(self, "完成", "露天連線成功。")
        elif product_ok:
            if QMessageBox.question(self, "商品 API 可用", f"商品 API 可用，但訂單 API 失敗：\n{error_text}\n\n要先從露天匯入/更新賣場商品嗎？") == QMessageBox.Yes:
                self.sync_ruten_product_list(show_message=True)
        else:
            QMessageBox.warning(self, "露天連線失敗", error_text or "無法連線露天 API。")

    def ruten_status_text(self, status: str) -> str:
        mapping = {
            "not_bound": "未填商品ID",
            "online": "上架中",
            "offline": "已下架",
            "on": "上架中",
            "off": "已下架",
            "out": "缺貨",
            "unknown": "未取得",
            "undefined": "未取得",
            "none": "未取得",
            "null": "未取得",
        }
        return mapping.get(clean_text(str(status)), clean_text(str(status)) or "未知")

    def fetch_ruten_status_from_lists(self, item_id: str) -> str:
        item_id = clean_text(str(item_id))
        if not item_id:
            return "unknown"
        client = self.ruten_client()
        for status_code in ("on", "off", "out"):
            offset = 1
            limit = 100
            for _page in range(100):
                payload = client.list_products(status=status_code, offset=offset, limit=limit)
                if not ruten_response_ok(payload):
                    break
                page_items = ruten_product_list_items(payload)
                for item in page_items:
                    current_item_id = clean_text(str(ruten_pick(item, "item_id", "id", "product_id", "rt_item_id")))
                    if current_item_id == item_id:
                        return normalize_ruten_status(status_code)
                if not page_items or len(page_items) < limit:
                    break
                offset += limit
        return "unknown"

    def ruten_record_matches_filter(self, record: dict[str, Any]) -> bool:
        ruten = ensure_ruten_item_fields(record)
        search = self.ruten_search_edit.text().strip().lower() if hasattr(self, "ruten_search_edit") else ""
        mode = self.ruten_filter_combo.currentText() if hasattr(self, "ruten_filter_combo") else "全部"

        pair_status = ruten_pairing_status(record)
        if mode == "已配對" and pair_status != "已配對":
            return False
        if mode == "未配對" and pair_status not in {"未配對", "待查ID", "待確認"}:
            return False
        if mode == "疑似配對" and pair_status != "疑似配對":
            return False
        if mode == "配對衝突" and pair_status != "衝突":
            return False
        if mode == "已填露天商品ID" and not clean_text(str(ruten.get("item_id", ""))):
            return False
        if mode == "尚未填露天商品ID" and clean_text(str(ruten.get("item_id", ""))):
            return False
        if mode == "允許批次同步" and not bool(ruten.get("enabled", True)):
            return False
        if mode == "暫停批次同步" and bool(ruten.get("enabled", True)):
            return False
        if mode == "本地有庫存" and int(record.get("quantity", 0) or 0) <= 0:
            return False
        if mode == "本地已售完" and int(record.get("quantity", 0) or 0) > 0:
            return False
        if mode == "露天有庫存" and to_int(ruten.get("remote_stock", 0)) <= 0:
            return False
        if mode == "露天已售完" and to_int(ruten.get("remote_stock", 0)) > 0:
            return False
        if mode == "露天匯入待確認" and str(record.get("source", "")) != "ruten":
            return False

        if search:
            haystack = " ".join([
                str(record.get("name", "")),
                str(record.get("english_name", "")),
                str(record.get("edition", "")),
                str(record.get("set_code", "")),
                str(record.get("collector", "")),
                str(ruten.get("item_id", "")),
                str(ruten.get("spec_id", "")),
                str(ruten.get("custom_no", "")),
                str(ruten.get("title", "")),
                ruten_pairing_status(record),
                str(ruten.get("match_note", "")),
            ]).lower()
            if search not in haystack:
                return False
        return True

    def current_ruten_records(self) -> list[dict[str, Any]]:
        records = []
        for record in self.db.get("mtg_inventory", []):
            ensure_ruten_item_fields(record)
            if self.ruten_record_matches_filter(record):
                records.append(record)
        return sorted(records, key=lambda r: (natural_sort_key(r.get("set_code", "")), collector_number_sort_key(r.get("collector", "")), natural_sort_key(r.get("name", ""))))

    def ruten_page_size(self) -> int:
        combo = getattr(self, "ruten_page_size_combo", None)
        if isinstance(combo, QComboBox):
            size = to_int(combo.currentText())
        else:
            size = to_int(self.ruten_settings().get("page_size", 50))
        return max(1, size or 50)

    def on_ruten_filter_changed(self, *_args: Any) -> None:
        self.ruten_current_page = 0
        self.refresh_ruten_table()

    def on_ruten_page_size_changed(self, *_args: Any) -> None:
        self.ruten_current_page = 0
        settings = self.ruten_settings()
        settings["page_size"] = self.ruten_page_size()
        save_db(self.db)
        self.refresh_ruten_table()

    def go_ruten_page(self, delta: int) -> None:
        records = self.current_ruten_records()
        page_size = self.ruten_page_size()
        total_pages = max(1, (len(records) + page_size - 1) // page_size)
        self.ruten_current_page = max(0, min(total_pages - 1, int(getattr(self, "ruten_current_page", 0)) + delta))
        self.refresh_ruten_table()

    def set_ruten_page_for_record(self, record_id: str) -> bool:
        records = self.current_ruten_records()
        page_size = self.ruten_page_size()
        for index, record in enumerate(records):
            if clean_text(str(record.get("id", ""))) == str(record_id):
                self.ruten_current_page = index // max(1, page_size)
                return True
        return False

    def refresh_ruten_table(self) -> None:
        if not hasattr(self, "ruten_table"):
            return
        records = self.current_ruten_records()
        page_size = self.ruten_page_size()
        total = len(records)
        total_pages = max(1, (total + page_size - 1) // page_size)
        self.ruten_current_page = max(0, min(total_pages - 1, int(getattr(self, "ruten_current_page", 0))))
        start = self.ruten_current_page * page_size
        end = min(start + page_size, total)
        page_records = records[start:end]
        self._updating_ruten_table = True
        self.ruten_table.setRowCount(0)
        try:
            for offset, record in enumerate(page_records):
                row = offset
                global_index = start + offset
                ruten = ensure_ruten_item_fields(record)
                self.ruten_table.insertRow(row)
                self.ruten_table.setRowHeight(row, 96)
                record_id = clean_text(str(record.get("id", "")))
                number_item = checkable_row_item(str(global_index + 1), record_id, record_id in self.ruten_checked_ids)
                self.ruten_table.setItem(row, 0, number_item)
                self.ruten_table.setCellWidget(row, 1, make_card_thumbnail_label(record, 64, 88))
                self.ruten_table.setItem(row, 2, QTableWidgetItem("允許" if bool(ruten.get("enabled", True)) else "暫停"))
                self.ruten_table.setItem(row, 3, QTableWidgetItem(str(record.get("name", ""))))
                self.ruten_table.setItem(row, 4, QTableWidgetItem(str(record.get("set_code", record.get("edition", "")))))
                self.ruten_table.setItem(row, 5, QTableWidgetItem(str(record.get("collector", ""))))
                self.ruten_table.setItem(row, 6, QTableWidgetItem(str(record.get("quantity", 0))))
                remote_stock_text = clean_text(str(ruten.get("remote_stock", "")))
                display_ruten_qty = remote_stock_text if remote_stock_text else str(ruten_listing_qty(record))
                self.ruten_table.setItem(row, 7, QTableWidgetItem(display_ruten_qty))
                self.ruten_table.setItem(row, 8, QTableWidgetItem(ruten_pairing_status(record)))
                self.ruten_table.setItem(row, 9, QTableWidgetItem(str(ruten.get("item_id", ""))))
                self.ruten_table.setItem(row, 10, QTableWidgetItem(str(ruten.get("spec_id", ""))))
                self.ruten_table.setItem(row, 11, QTableWidgetItem(str(to_int(ruten.get("price", 0)))))
                self.ruten_table.setItem(row, 12, QTableWidgetItem(self.ruten_status_text(str(ruten.get("status", "not_bound")))))
                self.ruten_table.setItem(row, 13, QTableWidgetItem(str(ruten.get("last_sync_at", ""))))
                self.ruten_table.setItem(row, 14, QTableWidgetItem(str(ruten.get("last_error", ""))))
        finally:
            self._updating_ruten_table = False
        checked_count = len(self.ruten_checked_ids)
        if hasattr(self, "ruten_page_label"):
            if total:
                self.ruten_page_label.setText(f"第 {self.ruten_current_page + 1} / {total_pages} 頁，顯示 {start + 1}-{end} / 共 {total} 筆，已勾選 {checked_count} 筆")
            else:
                self.ruten_page_label.setText(f"第 0 / 0 頁，共 0 筆，已勾選 {checked_count} 筆")
        if hasattr(self, "ruten_prev_page_btn"):
            self.ruten_prev_page_btn.setEnabled(self.ruten_current_page > 0)
        if hasattr(self, "ruten_next_page_btn"):
            self.ruten_next_page_btn.setEnabled(self.ruten_current_page < total_pages - 1)
        if hasattr(self, "ruten_grid_scroll"):
            self.refresh_ruten_grid(page_records, start)

    def toggle_ruten_view(self) -> None:
        enabled = not bool(getattr(self, "ruten_grid_view_enabled", False))
        self.ruten_grid_view_enabled = enabled
        self.ruten_table.setVisible(not enabled)
        self.ruten_grid_scroll.setVisible(enabled)
        self.ruten_toggle_view_btn.setText("表格檢視" if enabled else "卡圖檢視")
        self.refresh_ruten_table()

    def refresh_ruten_grid(self, page_records: list[dict[str, Any]], start_index: int) -> None:
        if not hasattr(self, "ruten_grid_layout"):
            return
        clear_qt_layout(self.ruten_grid_layout)
        if not bool(getattr(self, "ruten_grid_view_enabled", False)):
            return
        columns = 5
        selected_record_id = self.selected_ruten_mtg_id() if hasattr(self, "ruten_table") else ""
        for offset, record in enumerate(page_records):
            record_id = clean_text(str(record.get("id", "")))
            ruten = ensure_ruten_item_fields(record)
            remote_stock_text = clean_text(str(ruten.get("remote_stock", "")))
            display_ruten_qty = remote_stock_text if remote_stock_text else str(ruten_listing_qty(record))
            title = str(record.get("name", ""))
            subtitle = "\n".join(part for part in [
                f"露天數量：{display_ruten_qty}",
                self.ruten_status_text(str(ruten.get("status", "not_bound"))),
                str(ruten.get("item_id", "")),
            ] if part)
            tile = CardGridTile(record, title, subtitle, lambda rid=record_id: self.select_ruten_grid_record(rid), checked=record_id in self.ruten_checked_ids, selected=(record_id == selected_record_id))
            self.ruten_grid_layout.addWidget(tile, offset // columns, offset % columns)
        self.ruten_grid_layout.setRowStretch((len(page_records) + columns - 1) // columns, 1)

    def select_ruten_grid_record(self, record_id: str) -> None:
        if not record_id:
            return
        if self.select_table_row_by_record_id(self.ruten_table, record_id):
            self.on_ruten_selected()
            record = self.get_mtg_inventory_item(record_id)
            self.statusBar().showMessage(f"已選取露天商品：{record.get('name', '') if record else record_id}", 4000)
            if bool(getattr(self, "ruten_grid_view_enabled", False)):
                records = self.current_ruten_records()
                page_size = self.ruten_page_size()
                start = self.ruten_current_page * page_size
                self.refresh_ruten_grid(records[start:start + page_size], start)

    def selected_ruten_mtg_id(self) -> str:
        row = self.ruten_table.currentRow() if hasattr(self, "ruten_table") else -1
        if row < 0:
            return ""
        item = self.ruten_table.item(row, 0)
        return str(item.data(Qt.UserRole)) if item else ""

    def selected_ruten_record(self) -> dict[str, Any] | None:
        record_id = self.selected_ruten_mtg_id()
        return self.get_mtg_inventory_item(record_id) if record_id else None

    def checked_ruten_ids(self) -> list[str]:
        if hasattr(self, "ruten_table"):
            for row in range(self.ruten_table.rowCount()):
                item = self.ruten_table.item(row, 0)
                if not item:
                    continue
                record_id = clean_text(str(item.data(Qt.UserRole)))
                if not record_id:
                    continue
                if item.checkState() == Qt.CheckState.Checked:
                    self.ruten_checked_ids.add(record_id)
                else:
                    self.ruten_checked_ids.discard(record_id)
        return list(self.ruten_checked_ids)

    def checked_ruten_records(self) -> list[dict[str, Any]]:
        records: list[dict[str, Any]] = []
        for record_id in self.checked_ruten_ids():
            record = self.get_mtg_inventory_item(record_id)
            if record:
                records.append(record)
        return records

    def selected_or_checked_ruten_records(self) -> list[dict[str, Any]]:
        checked = self.checked_ruten_records()
        if checked:
            return checked
        record = self.selected_ruten_record()
        return [record] if record else []

    def on_ruten_item_changed(self, item: QTableWidgetItem) -> None:
        if bool(getattr(self, "_updating_ruten_table", False)):
            return
        if item.column() != 0:
            return
        record_id = clean_text(str(item.data(Qt.UserRole)))
        if not record_id:
            return
        if item.checkState() == Qt.CheckState.Checked:
            self.ruten_checked_ids.add(record_id)
        else:
            self.ruten_checked_ids.discard(record_id)
        count = len(self.ruten_checked_ids)
        self.statusBar().showMessage(f"露天賣場已勾選 {count} 筆" if count else "露天賣場已清除勾選", 3000)

    def set_visible_table_checks(self, table_name: str, checked: bool) -> None:
        if table_name == "mtg":
            table = getattr(self, "mtg_inventory_table", None)
            id_set = self.mtg_inventory_checked_ids
            updating_attr = "_updating_mtg_inventory_table"
        else:
            table = getattr(self, "ruten_table", None)
            id_set = self.ruten_checked_ids
            updating_attr = "_updating_ruten_table"
        if table is None:
            return
        setattr(self, updating_attr, True)
        try:
            for row in range(table.rowCount()):
                item = table.item(row, 0)
                if not item:
                    continue
                record_id = clean_text(str(item.data(Qt.UserRole)))
                if not record_id:
                    continue
                item.setCheckState(Qt.CheckState.Checked if checked else Qt.CheckState.Unchecked)
                if checked:
                    id_set.add(record_id)
                else:
                    id_set.discard(record_id)
        finally:
            setattr(self, updating_attr, False)
        count = len(id_set)
        self.statusBar().showMessage(f"已勾選 {count} 筆" if checked else "已清除目前列表勾選", 3000)
        if table_name == "mtg" and hasattr(self, "mtg_inventory_detail_label"):
            self.refresh_mtg_inventory_table()
        elif table_name == "ruten" and hasattr(self, "ruten_status_label"):
            self.refresh_ruten_table()

    def set_filtered_ruten_checks(self, checked: bool) -> None:
        records = self.current_ruten_records()
        record_ids = {clean_text(str(record.get("id", ""))) for record in records}
        record_ids.discard("")
        if checked:
            self.ruten_checked_ids.update(record_ids)
            message = f"已勾選目前搜尋結果 {len(record_ids)} 筆"
        else:
            self.ruten_checked_ids.difference_update(record_ids)
            message = f"已取消目前搜尋結果 {len(record_ids)} 筆"
        self.refresh_ruten_table()
        self.statusBar().showMessage(message, 4000)

    def clear_all_ruten_checks(self) -> None:
        self.ruten_checked_ids.clear()
        self.refresh_ruten_table()
        self.statusBar().showMessage("露天賣場已清除所有勾選", 3000)

    def on_ruten_selected(self) -> None:
        record = self.selected_ruten_record()
        if not record:
            if hasattr(self, "ruten_jump_mtg_btn"):
                self.ruten_jump_mtg_btn.setEnabled(False)
            if hasattr(self, "ruten_open_page_btn"):
                self.ruten_open_page_btn.setEnabled(False)
            if hasattr(self, "ruten_detail_label"):
                self.ruten_detail_label.setText("尚未選擇露天商品")
            if hasattr(self, "ruten_image_preview"):
                load_card_record_preview(self.ruten_image_preview, None, "選擇一筆露天商品可預覽卡圖")
            return
        ruten = ensure_ruten_item_fields(record)
        if hasattr(self, "ruten_jump_mtg_btn"):
            self.ruten_jump_mtg_btn.setEnabled(True)
        if hasattr(self, "ruten_open_page_btn"):
            self.ruten_open_page_btn.setEnabled(bool(make_ruten_item_web_url(ruten.get("item_id", ""))))
        self.ruten_status_label.setText(
            f"選取：{record.get('name', '')}｜本地總庫存 {record.get('quantity', 0)}｜露天上架數量 {ruten_listing_qty(record)}｜露天目前庫存 {ruten.get('remote_stock', '') or '-'}｜露天商品ID：{ruten.get('item_id', '') or '未填'}"
        )
        if hasattr(self, "ruten_detail_label"):
            self.ruten_detail_label.setText(
                f"MTG卡名：{record.get('name', '')}\n"
                f"Set：{record.get('set_code', record.get('edition', ''))}｜Collector：{record.get('collector', '')}\n"
                f"本地總庫存：{record.get('quantity', 0)}｜露天上架數量：{ruten_listing_qty(record)}｜露天目前庫存：{ruten.get('remote_stock', '') or '-'}｜售價：{to_int(ruten.get('price', 0))}\n"
                f"露天商品ID：{ruten.get('item_id', '') or '未填'}｜狀態：{self.ruten_status_text(str(ruten.get('status', 'not_bound')))}｜配對：{ruten_pairing_status(record)}\n"
                f"最後同步：{ruten.get('last_sync_at', '') or '-'}\n"
                f"最後錯誤：{ruten.get('last_error', '') or '-'}"
            )
        if hasattr(self, "ruten_image_preview"):
            load_card_record_preview(self.ruten_image_preview, record, "無卡圖")
        if bool(getattr(self, "ruten_grid_view_enabled", False)):
            records = self.current_ruten_records()
            page_size = self.ruten_page_size()
            start = self.ruten_current_page * page_size
            self.refresh_ruten_grid(records[start:start + page_size], start)

    def ruten_product_url_for_record(self, record: dict[str, Any] | None) -> str:
        if not record:
            return ""
        ruten = ensure_ruten_item_fields(record)
        return make_ruten_item_web_url(ruten.get("item_id", ""))

    def open_ruten_product_pages_for_records(self, records: list[dict[str, Any]], source_name: str = "商品") -> None:
        urls: list[tuple[str, str]] = []
        missing: list[str] = []
        seen: set[str] = set()
        for record in records:
            url = self.ruten_product_url_for_record(record)
            name = clean_text(str(record.get("name", ""))) or "未命名商品"
            if url:
                if url not in seen:
                    urls.append((url, name))
                    seen.add(url)
            else:
                missing.append(name)
        if not urls:
            QMessageBox.warning(self, "無法開啟商品網頁", "選取的商品尚未有露天商品ID，請先上架或綁定露天商品ID。")
            return
        if len(urls) > 1:
            preview = "\n".join(name for _url, name in urls[:8])
            more = f"\n...另有 {len(urls) - 8} 筆" if len(urls) > 8 else ""
            if QMessageBox.question(self, "開啟多個商品網頁", f"將開啟 {len(urls)} 個露天商品網頁：\n\n{preview}{more}\n\n確定開啟？") != QMessageBox.Yes:
                return
        opened = 0
        for url, _name in urls:
            if QDesktopServices.openUrl(QUrl(url)):
                opened += 1
        if missing:
            self.statusBar().showMessage(f"已開啟 {opened} 個{source_name}網頁；{len(missing)} 筆尚未綁定露天商品ID。", 6000)
        else:
            self.statusBar().showMessage(f"已開啟 {opened} 個{source_name}網頁。", 4000)

    def open_selected_ruten_product_pages(self) -> None:
        records = self.selected_or_checked_ruten_records()
        if not records:
            QMessageBox.warning(self, "無法開啟商品網頁", "請先在露天賣場頁選擇或勾選商品。")
            return
        self.open_ruten_product_pages_for_records(records, "露天商品")

    def open_selected_mtg_inventory_ruten_pages(self) -> None:
        records = self.selected_or_checked_mtg_inventory_records()
        if not records:
            QMessageBox.warning(self, "無法開啟商品網頁", "請先在 MTG庫存 選擇或勾選商品。")
            return
        self.open_ruten_product_pages_for_records(records, "露天商品")

    def quick_jump_search_text(self, record: dict[str, Any] | None, target: str) -> str:
        if not record:
            return ""
        ruten = ensure_ruten_item_fields(record)
        for value in [
            ruten.get("item_id", ""),
            ruten.get("custom_no", ""),
            ruten.get("title", ""),
            record.get("name", ""),
            record.get("english_name", ""),
            record.get("printed_name", ""),
        ]:
            text = clean_text(str(value))
            if text:
                return text
        return clean_text(str(record.get("id", "")))

    def select_table_row_by_record_id(self, table: QTableWidget, record_id: str) -> bool:
        for row in range(table.rowCount()):
            item = table.item(row, 0)
            if item and str(item.data(Qt.UserRole)) == str(record_id):
                table.selectRow(row)
                table.setCurrentCell(row, 0)
                hint = getattr(QAbstractItemView, "PositionAtCenter", None)
                if hint is None:
                    hint = QAbstractItemView.ScrollHint.PositionAtCenter
                table.scrollToItem(item, hint)
                return True
        return False

    def select_ruten_record_by_mtg_id(self, record_id: str) -> bool:
        if not record_id or not hasattr(self, "ruten_table"):
            return False
        record = self.get_mtg_inventory_item(record_id)
        self.tabs.setCurrentWidget(self.ruten_tab)
        if hasattr(self, "ruten_filter_combo"):
            self.ruten_filter_combo.blockSignals(True)
            self.ruten_filter_combo.setCurrentIndex(0)
            self.ruten_filter_combo.blockSignals(False)
        if hasattr(self, "ruten_search_edit"):
            self.ruten_search_edit.blockSignals(True)
            self.ruten_search_edit.setText(self.quick_jump_search_text(record, "ruten"))
            self.ruten_search_edit.blockSignals(False)
        self.set_ruten_page_for_record(record_id)
        self.refresh_ruten_table()
        if self.select_table_row_by_record_id(self.ruten_table, record_id):
            return True
        if hasattr(self, "ruten_search_edit"):
            self.ruten_search_edit.blockSignals(True)
            self.ruten_search_edit.clear()
            self.ruten_search_edit.blockSignals(False)
        self.ruten_current_page = 0
        self.set_ruten_page_for_record(record_id)
        self.refresh_ruten_table()
        return self.select_table_row_by_record_id(self.ruten_table, record_id)

    def select_mtg_inventory_record_by_id(self, record_id: str) -> bool:
        if not record_id or not hasattr(self, "mtg_inventory_table"):
            return False
        record = self.get_mtg_inventory_item(record_id)
        self.tabs.setCurrentWidget(self.mtg_inventory_tab)
        if hasattr(self, "mtg_inventory_edition_filter"):
            self.mtg_inventory_edition_filter.blockSignals(True)
            self.mtg_inventory_edition_filter.setCurrentIndex(0)
            self.mtg_inventory_edition_filter.blockSignals(False)
        for attr in [
            "mtg_inventory_format_filter",
            "mtg_inventory_color_filter",
            "mtg_inventory_rarity_filter",
            "mtg_inventory_type_filter",
            "mtg_inventory_language_filter",
        ]:
            combo = getattr(self, attr, None)
            if isinstance(combo, QComboBox):
                combo.blockSignals(True)
                combo.setCurrentIndex(0)
                combo.blockSignals(False)
        if hasattr(self, "mtg_inventory_search_edit"):
            self.mtg_inventory_search_edit.blockSignals(True)
            self.mtg_inventory_search_edit.setText(self.quick_jump_search_text(record, "mtg"))
            self.mtg_inventory_search_edit.blockSignals(False)
        self.refresh_mtg_inventory_table()
        if self.select_table_row_by_record_id(self.mtg_inventory_table, record_id):
            return True
        if hasattr(self, "mtg_inventory_search_edit"):
            self.mtg_inventory_search_edit.blockSignals(True)
            self.mtg_inventory_search_edit.clear()
            self.mtg_inventory_search_edit.blockSignals(False)
        self.refresh_mtg_inventory_table()
        return self.select_table_row_by_record_id(self.mtg_inventory_table, record_id)

    def jump_selected_mtg_inventory_to_ruten(self) -> None:
        record_id = self.selected_mtg_inventory_id()
        if not record_id:
            QMessageBox.warning(self, "無法跳轉", "請先在 MTG庫存 選擇一筆資料。")
            return
        if not self.select_ruten_record_by_mtg_id(record_id):
            QMessageBox.warning(self, "找不到對應資料", "露天賣場頁找不到這筆庫存。")
        else:
            self.statusBar().showMessage("已搜尋並定位到露天賣場對應商品", 4000)

    def jump_selected_ruten_to_mtg_inventory(self) -> None:
        record_id = self.selected_ruten_mtg_id()
        if not record_id:
            QMessageBox.warning(self, "無法跳轉", "請先在露天賣場選擇一筆資料。")
            return
        if not self.select_mtg_inventory_record_by_id(record_id):
            QMessageBox.warning(self, "找不到對應資料", "MTG庫存頁找不到這筆資料。")
        else:
            self.statusBar().showMessage("已搜尋並定位到 MTG庫存 對應商品", 4000)

    def created_ruten_ids_from_response(self, client: RutenApiClient, response: Any, custom_no: str = "") -> tuple[str, str]:
        item_id = ""
        spec_id = ""
        candidates: list[Any] = []
        if isinstance(response, dict):
            candidates.append(response.get("data"))
            candidates.append(response)
        for data in candidates:
            if isinstance(data, dict):
                if not item_id:
                    item_id = clean_text(str(ruten_pick(data, "item_id", "id", "product_id", "rt_item_id", default="")))
                if not spec_id:
                    spec_id = clean_text(str(ruten_pick(data, "spec_id", "sku_id", "option_id", default="")))
                spec_info = data.get("spec_info") or data.get("spec") or data.get("specs")
                if isinstance(spec_info, list) and spec_info:
                    first = spec_info[0]
                    if isinstance(first, dict):
                        if not item_id:
                            item_id = clean_text(str(ruten_pick(first, "item_id", "id", "product_id", default="")))
                        if not spec_id:
                            spec_id = clean_text(str(ruten_pick(first, "spec_id", "id", "sku_id", "option_id", default="")))
            elif isinstance(data, list):
                for row in data:
                    if isinstance(row, dict):
                        if not item_id:
                            item_id = clean_text(str(ruten_pick(row, "item_id", "id", "product_id", default="")))
                        if not spec_id:
                            spec_id = clean_text(str(ruten_pick(row, "spec_id", "id", "sku_id", "option_id", default="")))
                        if item_id:
                            break
            if item_id:
                break

        custom_no = sanitize_ruten_custom_no(custom_no)
        if not item_id and custom_no:
            lookup = client.find_item_id_by_custom_no(custom_no)
            if ruten_response_ok(lookup):
                lookup_data = lookup.get("data") if isinstance(lookup, dict) else {}
                if isinstance(lookup_data, dict):
                    item_id = clean_text(str(ruten_pick(lookup_data, "item_id", "id", "product_id", default="")))
                    spec_id = spec_id or clean_text(str(ruten_pick(lookup_data, "spec_id", "id", "sku_id", "option_id", default="")))
                elif isinstance(lookup_data, list):
                    for row in lookup_data:
                        if isinstance(row, dict):
                            item_id = clean_text(str(ruten_pick(row, "item_id", "id", "product_id", default="")))
                            spec_id = spec_id or clean_text(str(ruten_pick(row, "spec_id", "id", "sku_id", "option_id", default="")))
                            if item_id:
                                break
        return item_id, spec_id

    def upload_ruten_images_for_record(self, record: dict[str, Any], item_id: str, show_message: bool = False) -> bool:
        ruten = ensure_ruten_item_fields(record)
        try:
            image_path = prepare_ruten_image_file(record)
            if image_path is None:
                ruten["image_upload_error"] = "沒有可上傳的卡圖"
                return False
            payload = self.ruten_client().set_product_images(item_id, [image_path])
            if not ruten_response_ok(payload):
                raise RuntimeError(ruten_response_message(payload))
            ruten["image_uploaded_at"] = now_text()
            ruten["image_upload_error"] = ""
            self.append_ruten_operation_log("上傳露天卡圖", "成功", record, {"item_id": item_id})
            settings = self.ruten_settings()
            settings["last_image_upload_at"] = now_text()
            settings["last_image_upload_error"] = ""
            if show_message:
                QMessageBox.information(self, "完成", f"已上傳卡圖到露天商品。\n露天商品ID：{item_id}")
            return True
        except Exception as exc:
            message = translate_ruten_error("", exc)
            ruten["image_upload_error"] = message
            self.append_ruten_operation_log("上傳露天卡圖", "失敗", record, {"item_id": item_id}, message)
            settings = self.ruten_settings()
            settings["last_image_upload_error"] = message
            if show_message:
                QMessageBox.warning(self, "上傳卡圖失敗", message)
            return False

    def upload_selected_ruten_image(self) -> None:
        bound_items = self.require_bound_ruten_records("上傳卡圖")
        if not bound_items:
            return
        if len(bound_items) > 1:
            if QMessageBox.question(self, "確認批次上傳卡圖", f"將上傳/更新 {len(bound_items)} 筆露天商品卡圖，露天會以目前程式卡圖覆蓋商品圖片，確定執行？") != QMessageBox.Yes:
                return
        ok_count = 0
        fail_count = 0
        fail_messages: list[str] = []
        for record, ruten in bound_items:
            item_id = clean_text(str(ruten.get("item_id", "")))
            ok = self.upload_ruten_images_for_record(record, item_id, show_message=False)
            record["updated_at"] = now_text()
            if ok:
                ok_count += 1
            else:
                fail_count += 1
                fail_messages.append(f"{record.get('name', '')}：{ruten.get('image_upload_error', '未知錯誤')}")
        save_db(self.db)
        self.refresh_ruten_views_now()
        if len(bound_items) == 1 and ok_count == 1:
            QMessageBox.information(self, "完成", "已上傳卡圖到露天商品。")
            self.statusBar().showMessage("露天卡圖上傳完成", 5000)
        else:
            detail = "\n".join(fail_messages[:8])
            QMessageBox.information(self, "批次上傳完成", f"成功：{ok_count} 筆\n失敗：{fail_count} 筆" + (f"\n\n{detail}" if detail else ""))

    def create_ruten_product_and_bind_record(
        self,
        record: dict[str, Any],
        payload: dict[str, Any],
        default_values: dict[str, Any] | None = None,
    ) -> str:
        client = self.ruten_client()
        if int(payload.get("shipping_setting", 1) or 1) == 1:
            self.ensure_ruten_logistic_default_for_create()
        api_payload = dict(payload)
        api_payload["description"] = ruten_description_for_api(api_payload.get("description", ""))
        response = client.create_product(api_payload)
        if not ruten_response_ok(response):
            message = ruten_response_message(response)
            if "211101" in message:
                raise RuntimeError(message + "\n請先按『設定物流/付款』，在視窗內查詢目前設定或建立物流/付款預設檔。")
            raise RuntimeError(message)

        title = str(payload.get("name", ""))
        qty = int(payload.get("qty", 0) or 0)
        price = int(payload.get("price", 0) or 0)
        custom_no = sanitize_ruten_custom_no(payload.get("custom_no", ""))
        item_id, spec_id = self.created_ruten_ids_from_response(client, response, custom_no)
        if not item_id:
            raise RuntimeError("露天已回傳成功，但沒有取得商品ID。請先到露天後台確認商品是否已建立，再用自用料號查回商品ID。")

        ruten = ensure_ruten_item_fields(record)
        ruten.update({
            "enabled": True,
            "item_id": item_id,
            "spec_id": spec_id,
            "custom_no": custom_no,
            "title": title,
            "price": price,
            "status": "online",
            "listing_qty": qty,
            "remote_stock": qty,
            "description": normalize_ruten_description_lines(payload.get("description", "")),
            "class_id": normalize_ruten_class_id(payload.get("class_id", "")),
            "store_class_id": clean_text(str(payload.get("store_class_id", ""))),
            "condition": to_int(payload.get("condition", 1)) or 1,
            "stock_status": clean_text(str(payload.get("stock_status", "3DAY"))) or "3DAY",
            "location_type": to_int(payload.get("location_type", 1)) or 1,
            "location": normalize_ruten_location_code(payload.get("location", DEFAULT_RUTEN_LOCATION_CODE)),
            "match_status": "已配對",
            "match_note": "此商品由程式建立並已綁定露天商品ID。",
            "last_sync_at": now_text(),
            "last_error": "",
        })
        record["quantity"] = max(0, int(record.get("quantity", qty) or qty))
        record["price"] = str(price)
        record["updated_at"] = now_text()
        if default_values:
            self.ruten_settings().update(default_values)
        self.set_ruten_api_status(product_ok=True)
        if bool(self.ruten_settings().get("auto_upload_scryfall_image_on_create", True)):
            image_ok = self.upload_ruten_images_for_record(record, item_id, show_message=False)
            if not image_ok:
                image_error = clean_text(str(ruten.get("image_upload_error", "")))
                if image_error:
                    ruten["last_error"] = f"商品已建立，但卡圖未上傳：{image_error}"
        return item_id

    def create_ruten_product_for_record(self, record: dict[str, Any]) -> None:
        ruten = ensure_ruten_item_fields(record)
        if clean_text(str(ruten.get("item_id", ""))):
            QMessageBox.information(
                self,
                "已經是露天商品",
                "這筆庫存已經有露天商品ID。\n若要重新出售，請使用「上架到露天」。",
            )
            return
        if max(0, to_int(record.get("quantity", 0))) <= 0:
            QMessageBox.warning(self, "無法上架", "本地總庫存為 0，請先把庫存數量改成 1 以上再上架到露天。")
            return
        if not self.ruten_client().is_ready():
            QMessageBox.warning(self, "API 尚未設定", "請先設定露天 API 金鑰。")
            return

        dialog = RutenCreateProductDialog(record, self.ruten_settings(), self)
        if dialog.exec() != QDialog.Accepted:
            return
        payload = dialog.values()
        title = str(payload.get("name", ""))
        qty = int(payload.get("qty", 0) or 0)
        price = int(payload.get("price", 0) or 0)
        if QMessageBox.question(
            self,
            "建立露天商品前確認",
            self.ruten_create_confirmation_text(record, payload),
        ) != QMessageBox.Yes:
            self.append_ruten_operation_log("建立露天商品", "取消", record, {"title": title, "qty": qty, "price": price})
            return

        try:
            self.backup_db_before_ruten_write()
            item_id = self.create_ruten_product_and_bind_record(record, payload, dialog.default_values())
            self.append_ruten_operation_log(
                "建立露天商品",
                "成功",
                record,
                {"title": title, "qty": qty, "price": price, "item_id": item_id, "class_id": payload.get("class_id", "")},
            )
            save_db(self.db)
            self.refresh_ruten_views_now()
            ruten = ensure_ruten_item_fields(record)
            image_status = "卡圖：已上傳" if clean_text(str(ruten.get("image_uploaded_at", ""))) else f"卡圖：未上傳（{ruten.get('image_upload_error', '沒有可上傳的卡圖')}）"
            QMessageBox.information(
                self,
                "上架完成",
                f"已建立露天商品，並已和程式庫存連動。\n\n露天商品ID：{item_id}\n商品：{title}\n{image_status}",
            )
        except Exception as exc:
            error_text = translate_ruten_error("", exc)
            self.update_ruten_result(record, False, error_text)
            self.append_ruten_operation_log("建立露天商品", "失敗", record, {"title": title, "qty": qty, "price": price}, error_text)
            self.set_ruten_api_status(product_ok=False, error=error_text)
            save_db(self.db)
            self.refresh_ruten_views_now()
            QMessageBox.warning(self, "上架露天失敗", str(exc))

    def edit_existing_ruten_product_for_record(self, record: dict[str, Any]) -> None:
        ruten = ensure_ruten_item_fields(record)
        item_id = clean_text(str(ruten.get("item_id", "")))
        if not item_id:
            self.create_ruten_product_for_record(record)
            return
        if not self.ruten_client().is_ready():
            QMessageBox.warning(self, "API 尚未設定", "請先設定露天 API 金鑰。")
            return

        dialog = RutenExistingProductEditDialog(record, self.ruten_settings(), self)
        if dialog.exec() != QDialog.Accepted:
            return
        values = dialog.values()
        qty = max(0, int(values.get("qty", 0)))
        set_online = bool(values.get("set_online", False))
        if QMessageBox.question(
            self,
            "更新露天商品前確認",
            self.ruten_existing_confirmation_text(record, values),
        ) != QMessageBox.Yes:
            self.append_ruten_operation_log("更新露天商品", "取消", record, {"item_id": item_id, "qty": qty, "set_online": set_online})
            return

        try:
            self.backup_db_before_ruten_write()
            spec_id = clean_text(str(ruten.get("spec_id", "")))
            client = self.ruten_client()
            info_payload: dict[str, Any] = {
                "item_id": item_id,
                "name": str(values.get("title", "")),
                "class_id": normalize_ruten_class_id(values.get("class_id", "")),
                "condition": int(values.get("condition", 1) or 1),
                "stock_status": str(values.get("stock_status", "3DAY") or "3DAY"),
                "description": ruten_description_for_api(values.get("description", "") or make_ruten_description(record)),
                "location_type": int(values.get("location_type", 1) or 1),
                "location": normalize_ruten_location_code(values.get("location", DEFAULT_RUTEN_LOCATION_CODE)) or DEFAULT_RUTEN_LOCATION_CODE,
                "custom_no": str(values.get("custom_no", "")),
            }
            store_class_id = clean_text(str(values.get("store_class_id", "")))
            if store_class_id:
                info_payload["store_class_id"] = store_class_id
            if not info_payload["class_id"]:
                raise RuntimeError("缺少露天分類ID，無法更新商品說明。請先在上架視窗或設定中選擇露天分類。")
            payload = client.update_item_info(info_payload)
            if not ruten_response_ok(payload):
                raise RuntimeError(f"商品資料：{ruten_response_message(payload)}")
            payload = client.update_stock(item_id, qty, spec_id=spec_id)
            if not ruten_response_ok(payload):
                raise RuntimeError(f"庫存：{ruten_response_message(payload)}")
            if set_online:
                payload = client.set_online(item_id)
                if not ruten_response_ok(payload):
                    raise RuntimeError(f"上架：{ruten_response_message(payload)}")
                self.set_ruten_local_listing_status(record, True)

            set_ruten_listing_qty(record, qty)
            ruten["remote_stock"] = qty
            ruten["title"] = str(values.get("title", ""))
            ruten["custom_no"] = str(values.get("custom_no", ""))
            ruten["description"] = normalize_ruten_description_lines(values.get("description", ""))
            ruten["class_id"] = normalize_ruten_class_id(values.get("class_id", ""))
            ruten["store_class_id"] = clean_text(str(values.get("store_class_id", "")))
            ruten["condition"] = int(values.get("condition", 1) or 1)
            ruten["stock_status"] = str(values.get("stock_status", "3DAY") or "3DAY")
            ruten["location_type"] = int(values.get("location_type", 1) or 1)
            ruten["location"] = normalize_ruten_location_code(values.get("location", DEFAULT_RUTEN_LOCATION_CODE))
            ruten["auto_restock"] = bool(values.get("auto_restock", False))
            ruten["restock_target"] = max(1, to_int(values.get("restock_target", 1)) or 1)
            self.update_ruten_result(record, True)
            self.append_ruten_operation_log(
                "更新露天商品",
                "成功",
                record,
                {"item_id": item_id, "qty": qty, "set_online": set_online, "auto_restock": ruten.get("auto_restock", False), "description_updated": True},
            )
            save_db(self.db)
            self.refresh_ruten_views_now()
            QMessageBox.information(self, "更新完成", f"已更新露天上架數量與商品說明。\n\n商品：{record.get('name', '')}")
        except Exception as exc:
            error_text = translate_ruten_error("", exc)
            self.update_ruten_result(record, False, error_text)
            self.append_ruten_operation_log("更新露天商品", "失敗", record, {"item_id": item_id, "qty": qty, "set_online": set_online}, error_text)
            self.set_ruten_api_status(product_ok=False, error=error_text)
            save_db(self.db)
            self.refresh_ruten_views_now()
            QMessageBox.warning(self, "更新露天商品失敗", error_text)

    def upsert_ruten_product_for_record(self, record: dict[str, Any]) -> None:
        ruten = ensure_ruten_item_fields(record)
        if clean_text(str(ruten.get("item_id", ""))):
            self.edit_existing_ruten_product_for_record(record)
        else:
            self.create_ruten_product_for_record(record)

    def upsert_selected_ruten_products(self) -> None:
        records = self.selected_or_checked_ruten_records()
        if not records:
            QMessageBox.warning(self, "無法上架/編輯", "請先在露天賣場頁選擇或勾選商品。")
            return
        if len(records) == 1:
            self.upsert_ruten_product_for_record(records[0])
            return

        existing = [record for record in records if clean_text(str(ensure_ruten_item_fields(record).get("item_id", "")))]
        missing = [record for record in records if not clean_text(str(ensure_ruten_item_fields(record).get("item_id", "")))]
        msg = [f"已綁定露天商品ID：{len(existing)} 筆，會把『露天上架數量』同步到露天庫存。"]
        msg.append(f"尚未上架露天：{len(missing)} 筆，會逐筆開啟上架表單建立新露天商品。")
        if QMessageBox.question(self, "確認批次上架/編輯", "\n".join(msg) + "\n\n確定開始？") != QMessageBox.Yes:
            return

        if existing:
            try:
                self.backup_db_before_ruten_write()
                ok_count = 0
                fail_count = 0
                fail_messages: list[str] = []
                for record in existing:
                    try:
                        self.push_single_ruten_record_to_remote(record, sync_price=False, apply_online_rules=False)
                        ok_count += 1
                    except Exception as exc:
                        fail_count += 1
                        self.update_ruten_result(record, False, str(exc))
                        fail_messages.append(f"{record.get('name', '')}：{exc}")
                save_db(self.db)
                self.refresh_mtg_inventory_table()
                self.refresh_ruten_table()
                if fail_count:
                    QMessageBox.warning(self, "部分更新失敗", f"已綁定商品更新成功：{ok_count} 筆\n失敗：{fail_count} 筆\n\n" + "\n".join(fail_messages[:8]))
            except Exception as exc:
                QMessageBox.warning(self, "批次更新失敗", str(exc))
        for record in missing:
            self.create_ruten_product_for_record(record)

    def upsert_selected_mtg_inventory_products(self) -> None:
        records = self.selected_or_checked_mtg_inventory_records()
        if not records:
            QMessageBox.warning(self, "無法上架/編輯", "請先在 MTG庫存 選擇或勾選庫存。")
            return
        if len(records) == 1:
            self.upsert_ruten_product_for_record(records[0])
            return

        existing = [record for record in records if clean_text(str(ensure_ruten_item_fields(record).get("item_id", "")))]
        missing = [record for record in records if not clean_text(str(ensure_ruten_item_fields(record).get("item_id", "")))]
        msg = [f"已綁定露天商品ID：{len(existing)} 筆，會把『露天上架數量』同步到露天庫存。"]
        msg.append(f"尚未上架露天：{len(missing)} 筆，會逐筆開啟上架表單建立新露天商品。")
        if QMessageBox.question(self, "確認批次上架/編輯", "\n".join(msg) + "\n\n確定開始？") != QMessageBox.Yes:
            return
        if existing:
            try:
                self.backup_db_before_ruten_write()
                ok_count = 0
                fail_count = 0
                fail_messages: list[str] = []
                for record in existing:
                    try:
                        self.push_single_ruten_record_to_remote(record, sync_price=False, apply_online_rules=False)
                        ok_count += 1
                    except Exception as exc:
                        fail_count += 1
                        self.update_ruten_result(record, False, str(exc))
                        fail_messages.append(f"{record.get('name', '')}：{exc}")
                save_db(self.db)
                self.refresh_mtg_inventory_table()
                self.refresh_ruten_table()
                if fail_count:
                    QMessageBox.warning(self, "部分更新失敗", f"已綁定商品更新成功：{ok_count} 筆\n失敗：{fail_count} 筆\n\n" + "\n".join(fail_messages[:8]))
            except Exception as exc:
                QMessageBox.warning(self, "批次更新失敗", str(exc))
        for record in missing:
            self.create_ruten_product_for_record(record)

    def create_selected_ruten_product(self) -> None:
        self.upsert_selected_ruten_products()

    def create_selected_mtg_inventory_ruten_product(self) -> None:
        self.upsert_selected_mtg_inventory_products()

    def require_ruten_bound_record(self) -> tuple[dict[str, Any], dict[str, Any]] | None:
        record = self.selected_ruten_record()
        if not record:
            QMessageBox.warning(self, "無法同步", "請先選擇一筆露天商品。")
            return None
        ruten = ensure_ruten_item_fields(record)
        if not clean_text(str(ruten.get("item_id", ""))):
            QMessageBox.warning(self, "無法同步", "這筆 MTG庫存尚未填露天商品ID。")
            return None
        return record, ruten

    def require_bound_ruten_records(self, action_text: str = "同步") -> list[tuple[dict[str, Any], dict[str, Any]]]:
        records = self.selected_or_checked_ruten_records()
        if not records:
            QMessageBox.warning(self, f"無法{action_text}", "請先在露天賣場選擇或勾選商品。")
            return []
        bound: list[tuple[dict[str, Any], dict[str, Any]]] = []
        missing: list[str] = []
        for record in records:
            ruten = ensure_ruten_item_fields(record)
            if clean_text(str(ruten.get("item_id", ""))):
                bound.append((record, ruten))
            else:
                missing.append(str(record.get("name", "")))
        if missing:
            sample = "\n".join(missing[:8])
            more = f"\n...另有 {len(missing) - 8} 筆" if len(missing) > 8 else ""
            QMessageBox.warning(self, f"部分商品無法{action_text}", f"以下商品尚未有露天商品ID，請先上架成露天商品或綁定ID：\n\n{sample}{more}")
        return bound

    def update_ruten_result(self, record: dict[str, Any], ok: bool, message: str = "") -> None:
        ruten = ensure_ruten_item_fields(record)
        ruten["last_sync_at"] = now_text()
        ruten["last_error"] = "" if ok else message
        record["updated_at"] = now_text()

    def set_ruten_local_listing_status(self, record: dict[str, Any], online: bool) -> None:
        ruten = ensure_ruten_item_fields(record)
        ruten["status"] = "online" if online else "offline"
        ruten["last_sync_at"] = now_text()
        ruten["last_error"] = ""
        record["updated_at"] = now_text()

    def refresh_ruten_views_now(self) -> None:
        if hasattr(self, "refresh_ruten_table"):
            self.refresh_ruten_table()
        if hasattr(self, "refresh_mtg_inventory_table"):
            self.refresh_mtg_inventory_table()
        QApplication.processEvents()

    def append_ruten_operation_log(
        self,
        action: str,
        status: str,
        record: dict[str, Any] | None = None,
        details: dict[str, Any] | None = None,
        error: str = "",
    ) -> None:
        CONFIG_DIR.mkdir(parents=True, exist_ok=True)
        entry = {
            "time": now_text(),
            "action": clean_text(str(action)),
            "status": clean_text(str(status)),
            "error": clean_text(str(error)),
            "record_id": "",
            "card_name": "",
            "set_code": "",
            "collector": "",
            "item_id": "",
            "spec_id": "",
            "local_qty": "",
            "listing_qty": "",
            "remote_stock": "",
            "ruten_status": "",
            "details": details or {},
        }
        if isinstance(record, dict):
            ruten = ensure_ruten_item_fields(record)
            entry.update({
                "record_id": clean_text(str(record.get("id", ""))),
                "card_name": clean_text(str(record.get("name", ""))),
                "set_code": clean_text(str(record.get("set_code", record.get("edition", "")))),
                "collector": clean_text(str(record.get("collector", ""))),
                "item_id": clean_text(str(ruten.get("item_id", ""))),
                "spec_id": clean_text(str(ruten.get("spec_id", ""))),
                "local_qty": max(0, to_int(record.get("quantity", 0))),
                "listing_qty": ruten_listing_qty(record),
                "remote_stock": max(0, to_int(ruten.get("remote_stock", 0))),
                "ruten_status": clean_text(str(ruten.get("status", ""))),
            })
        logs: list[dict[str, Any]] = []
        try:
            if RUTEN_OPERATION_LOG_PATH.exists():
                with RUTEN_OPERATION_LOG_PATH.open("r", encoding="utf-8") as f:
                    raw = json.load(f)
                if isinstance(raw, list):
                    logs = raw
                elif isinstance(raw, dict) and isinstance(raw.get("logs"), list):
                    logs = raw.get("logs", [])
        except Exception:
            logs = []
        logs.append(entry)
        logs = logs[-3000:]
        try:
            tmp_path = RUTEN_OPERATION_LOG_PATH.with_suffix(".tmp")
            with tmp_path.open("w", encoding="utf-8") as f:
                json.dump(logs, f, ensure_ascii=False, indent=2)
            tmp_path.replace(RUTEN_OPERATION_LOG_PATH)
        except Exception:
            pass

    def show_ruten_operation_log(self) -> None:
        logs: list[dict[str, Any]] = []
        try:
            if RUTEN_OPERATION_LOG_PATH.exists():
                with RUTEN_OPERATION_LOG_PATH.open("r", encoding="utf-8") as f:
                    raw = json.load(f)
                if isinstance(raw, list):
                    logs = raw
        except Exception as exc:
            QMessageBox.warning(self, "讀取操作紀錄失敗", str(exc))
            return
        dialog = QDialog(self)
        dialog.setWindowTitle("露天操作紀錄")
        dialog.resize(980, 640)
        layout = QVBoxLayout(dialog)
        label = QLabel(f"紀錄檔：config/ruten_operation_log.json｜目前顯示最近 {min(len(logs), 300)} 筆")
        table = QTableWidget(0, 10)
        table.setHorizontalHeaderLabels(["時間", "操作", "結果", "卡名", "Set", "Collector", "本地總庫存", "上架數量", "露天ID", "錯誤/備註"])
        table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        table.setSelectionBehavior(QAbstractItemView.SelectRows)
        table.verticalHeader().setVisible(False)
        setup_stable_table_columns(table, {0: 150, 1: 150, 2: 80, 3: 220, 4: 70, 5: 80, 6: 90, 7: 90, 8: 130, 9: 320})
        for row, entry in enumerate(reversed(logs[-300:])):
            table.insertRow(row)
            table.setItem(row, 0, QTableWidgetItem(str(entry.get("time", ""))))
            table.setItem(row, 1, QTableWidgetItem(str(entry.get("action", ""))))
            table.setItem(row, 2, QTableWidgetItem(str(entry.get("status", ""))))
            table.setItem(row, 3, QTableWidgetItem(str(entry.get("card_name", ""))))
            table.setItem(row, 4, QTableWidgetItem(str(entry.get("set_code", ""))))
            table.setItem(row, 5, QTableWidgetItem(str(entry.get("collector", ""))))
            table.setItem(row, 6, QTableWidgetItem(str(entry.get("local_qty", ""))))
            table.setItem(row, 7, QTableWidgetItem(str(entry.get("listing_qty", ""))))
            table.setItem(row, 8, QTableWidgetItem(str(entry.get("item_id", ""))))
            note = str(entry.get("error", ""))
            if not note and isinstance(entry.get("details"), dict):
                detail = entry.get("details", {})
                note = " / ".join(f"{k}={v}" for k, v in list(detail.items())[:6])
            table.setItem(row, 9, QTableWidgetItem(note))
        buttons = QDialogButtonBox(QDialogButtonBox.Close)
        buttons.rejected.connect(dialog.reject)
        buttons.accepted.connect(dialog.accept)
        layout.addWidget(label)
        layout.addWidget(table, 1)
        layout.addWidget(buttons)
        dialog.exec()

    def ruten_create_confirmation_text(self, record: dict[str, Any], payload: dict[str, Any]) -> str:
        ruten = ensure_ruten_item_fields(record)
        title = clean_text(str(payload.get("name", "")))
        qty = max(0, to_int(payload.get("qty", 0)))
        local_qty = max(0, to_int(record.get("quantity", 0)))
        price = max(0, to_int(payload.get("price", 0)))
        location_type = "台灣" if to_int(payload.get("location_type", 1)) == 1 else "海外"
        location = ruten_location_label(payload.get("location", "")) if to_int(payload.get("location_type", 1)) == 1 else clean_text(str(payload.get("location", "")))
        image_source = "會嘗試上傳 Scryfall/本機卡圖" if bool(self.ruten_settings().get("auto_upload_scryfall_image_on_create", True)) else "不自動上傳卡圖"
        custom_no = sanitize_ruten_custom_no(payload.get("custom_no", ""))
        description = clean_text(str(payload.get("description", "")))
        preview = description[:260] + ("..." if len(description) > 260 else "")
        return (
            "即將建立新的露天商品，請確認以下內容：\n\n"
            f"商品標題：{title}\n"
            f"本地總庫存：{local_qty}\n"
            f"露天上架數量：{qty}\n"
            f"首次上架售價：NT$ {price}\n"
            f"露天分類ID：{payload.get('class_id', '')}\n"
            f"賣場分類ID：{payload.get('store_class_id', '') or '未設定'}\n"
            f"自用料號：{custom_no or '未設定'}\n"
            f"物品所在地：{location_type}．{location}\n"
            f"物流/付款：使用露天新增商品預設檔\n"
            f"卡圖：{image_source}\n\n"
            f"商品說明預覽：\n{preview}\n\n"
            "確認後會送出到露天並產生露天商品ID。"
        )

    def ruten_existing_confirmation_text(self, record: dict[str, Any], values: dict[str, Any]) -> str:
        ruten = ensure_ruten_item_fields(record)
        qty = max(0, to_int(values.get("qty", 0)))
        local_qty = max(0, to_int(record.get("quantity", 0)))
        set_online = bool(values.get("set_online", False))
        auto_restock = bool(values.get("auto_restock", False))
        restock_target = max(1, to_int(values.get("restock_target", 1)) or 1)
        status_action = "同步後設為上架中" if set_online else "不變更上架狀態"
        restock_text = f"開啟，目標補到 {restock_target}" if auto_restock else "關閉"
        return (
            "即將更新已存在的露天商品，不會重新建立商品：\n\n"
            f"商品：{record.get('name', '')}\n"
            f"露天商品ID：{ruten.get('item_id', '')}\n"
            f"目前露天狀態：{self.ruten_status_text(str(ruten.get('status', 'unknown')))}\n"
            f"本地總庫存：{local_qty}\n"
            f"露天上架數量將改為：{qty}\n"
            f"露天目前庫存紀錄：{ruten.get('remote_stock', '')}\n"
            f"自動補貨：{restock_text}\n"
            f"上架狀態：{status_action}\n\n"
            "確認後會更新露天庫存數量。"
        )

    def backup_db_before_ruten_write(self) -> None:
        if not DB_PATH.exists():
            return
        backup_dir = CONFIG_DIR / "backups"
        backup_dir.mkdir(parents=True, exist_ok=True)
        backup_path = backup_dir / f"card_inventory_before_ruten_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        shutil.copy2(DB_PATH, backup_path)

    def show_batch_result(self, title: str, ok_count: int, failures: list[dict[str, Any]]) -> None:
        CONFIG_DIR.mkdir(parents=True, exist_ok=True)
        try:
            with RUTEN_BATCH_FAILURE_PATH.open("w", encoding="utf-8") as f:
                json.dump({"created_at": now_text(), "title": title, "failures": failures}, f, ensure_ascii=False, indent=2)
        except Exception:
            pass
        if failures:
            detail = "\n".join(f"{item.get('name', '')}：{item.get('error', '')}" for item in failures[:10])
            more = f"\n...另有 {len(failures) - 10} 筆，完整清單已存到 config/ruten_last_batch_failures.json" if len(failures) > 10 else "\n完整失敗清單已存到 config/ruten_last_batch_failures.json"
            QMessageBox.warning(self, title, f"成功：{ok_count} 筆\n失敗：{len(failures)} 筆\n\n{detail}{more}")
        else:
            QMessageBox.information(self, title, f"成功：{ok_count} 筆\n失敗：0 筆")

    def run_ruten_batch(self, title: str, records: list[dict[str, Any]], worker: Any) -> tuple[int, list[dict[str, Any]]]:
        progress = QProgressDialog(title, "取消", 0, len(records), self)
        progress.setWindowTitle(title)
        progress.setWindowModality(Qt.ApplicationModal)
        progress.setMinimumDuration(300)
        ok_count = 0
        failures: list[dict[str, Any]] = []
        for index, record in enumerate(records, start=1):
            progress.setValue(index - 1)
            progress.setLabelText(f"{title}\n{index}/{len(records)}：{record.get('name', '')}")
            QApplication.processEvents()
            if progress.wasCanceled():
                failures.append({"name": "使用者取消", "error": f"已在第 {index} 筆取消，後續未處理。"})
                break
            try:
                worker(record)
                ok_count += 1
            except Exception as exc:
                error_text = translate_ruten_error("", exc)
                self.update_ruten_result(record, False, error_text)
                self.append_ruten_operation_log(title, "失敗", record, {}, error_text)
                failures.append({
                    "id": record.get("id", ""),
                    "name": record.get("name", ""),
                    "item_id": ensure_ruten_item_fields(record).get("item_id", ""),
                    "error": error_text,
                })
            time.sleep(0.08)
        progress.setValue(len(records))
        return ok_count, failures

    def push_single_ruten_record_to_remote(
        self,
        record: dict[str, Any],
        sync_price: bool = False,
        apply_online_rules: bool = True,
    ) -> tuple[bool, str]:
        ruten = ensure_ruten_item_fields(record)
        item_id = clean_text(str(ruten.get("item_id", "")))
        if not item_id:
            return False, "尚未填露天商品ID"
        if not bool(ruten.get("enabled", True)):
            return False, "這筆商品已暫停批次同步"

        client = self.ruten_client()
        spec_id = clean_text(str(ruten.get("spec_id", "")))
        qty = ruten_listing_qty(record)
        ruten["listing_qty"] = qty
        payload = client.update_stock(item_id, qty, spec_id=spec_id)
        if not ruten_response_ok(payload):
            raise RuntimeError(f"庫存：{ruten_response_message(payload)}")
        ruten["remote_stock"] = qty

        settings = self.ruten_settings()
        state_text = ""
        if apply_online_rules and qty <= 0 and bool(settings.get("auto_offline_zero_stock", False)):
            payload = client.set_offline(item_id)
            if not ruten_response_ok(payload):
                raise RuntimeError(f"下架：{ruten_response_message(payload)}")
            self.set_ruten_local_listing_status(record, False)
            state_text = "，已自動下架"
        elif apply_online_rules and qty > 0 and bool(settings.get("auto_online_positive_stock", False)):
            payload = client.set_online(item_id)
            if not ruten_response_ok(payload):
                raise RuntimeError(f"上架：{ruten_response_message(payload)}")
            self.set_ruten_local_listing_status(record, True)
            state_text = "，已自動上架"

        self.update_ruten_result(record, True)
        self.append_ruten_operation_log(
            "同步露天上架數量",
            "成功",
            record,
            {"item_id": item_id, "qty": qty, "apply_online_rules": apply_online_rules, "result": state_text.strip("，")},
        )
        return True, f"已同步露天上架數量 {qty}{state_text}"

    def auto_push_local_ruten_change(self, record: dict[str, Any], reason: str = "") -> None:
        settings = self.ruten_settings()
        if not bool(settings.get("auto_push_local_changes", False)):
            return
        ruten = ensure_ruten_item_fields(record)
        if not clean_text(str(ruten.get("item_id", ""))):
            return
        try:
            ok, msg = self.push_single_ruten_record_to_remote(record, sync_price=False, apply_online_rules=True)
            save_db(self.db)
            if hasattr(self, "refresh_ruten_table"):
                self.refresh_ruten_table()
            if ok:
                self.statusBar().showMessage(f"露天自動同步完成：{record.get('name', '')}｜{msg}", 7000)
        except Exception as exc:
            self.update_ruten_result(record, False, str(exc))
            save_db(self.db)
            if hasattr(self, "refresh_ruten_table"):
                self.refresh_ruten_table()
            self.statusBar().showMessage(f"露天自動同步失敗：{record.get('name', '')}｜{exc}", 10000)

    def list_selected_ruten_item_to_remote(self) -> None:
        records = self.selected_or_checked_ruten_records()
        if not records:
            QMessageBox.warning(self, "無法上架", "請先在露天賣場頁選擇或勾選商品。")
            return
        existing = [record for record in records if clean_text(str(ensure_ruten_item_fields(record).get("item_id", "")))]
        missing = [record for record in records if not clean_text(str(ensure_ruten_item_fields(record).get("item_id", "")))]
        if existing:
            self.set_ruten_online_state_for_records(existing, True)
        if missing:
            if len(records) > 1:
                if QMessageBox.question(self, "建立新露天商品", f"另有 {len(missing)} 筆尚未有露天商品ID，將逐筆開啟上架表單，確定繼續？") != QMessageBox.Yes:
                    return
            for record in missing:
                self.create_ruten_product_for_record(record)

    def set_ruten_online_state_for_records(self, records: list[dict[str, Any]], online: bool) -> None:
        bound_items: list[tuple[dict[str, Any], dict[str, Any]]] = []
        missing: list[str] = []
        for record in records:
            ruten = ensure_ruten_item_fields(record)
            if clean_text(str(ruten.get("item_id", ""))):
                bound_items.append((record, ruten))
            else:
                missing.append(str(record.get("name", "")))
        if missing:
            sample = "\n".join(missing[:8])
            QMessageBox.warning(self, "部分商品缺少露天商品ID", f"以下商品尚未有露天商品ID，無法直接上下架：\n\n{sample}")
        if not bound_items:
            return
        action_text = "上架" if online else "下架"
        if not self.confirm_ruten_batch_action(f"確認{action_text}", [record for record, _ruten in bound_items], f"{action_text}露天商品"):
            return
        self.backup_db_before_ruten_write()
        client = self.ruten_client()

        def worker(record: dict[str, Any]) -> None:
            ruten = ensure_ruten_item_fields(record)
            item_id = clean_text(str(ruten.get("item_id", "")))
            payload = client.set_online(item_id) if online else client.set_offline(item_id)
            if not ruten_response_ok(payload):
                raise RuntimeError(ruten_response_message(payload))
            self.set_ruten_local_listing_status(record, online)
            self.update_ruten_result(record, True)
            self.append_ruten_operation_log(
                f"{action_text}露天商品",
                "成功",
                record,
                {"item_id": item_id, "target_status": "online" if online else "offline"},
            )

        ok_count, failures = self.run_ruten_batch(f"批次{action_text}露天商品", [record for record, _ruten in bound_items], worker)
        save_db(self.db)
        self.refresh_ruten_views_now()
        if len(bound_items) == 1 and ok_count == 1 and not failures:
            QMessageBox.information(self, "完成", f"已{action_text}：{bound_items[0][0].get('name', '')}")
        else:
            self.show_batch_result(f"批次{action_text}完成", ok_count, failures)

    def set_selected_ruten_online_state(self, online: bool) -> None:
        records = self.selected_or_checked_ruten_records()
        if not records:
            QMessageBox.warning(self, "無法上下架", "請先在露天賣場頁選擇或勾選商品。")
            return
        self.set_ruten_online_state_for_records(records, online)

    def refresh_selected_ruten_remote_item(self) -> None:
        bound_items = self.require_bound_ruten_records("查詢狀態")
        if not bound_items:
            return
        ok_count = 0
        fail_count = 0
        fail_messages: list[str] = []
        for record, ruten in bound_items:
            try:
                payload = self.ruten_client().get_item(str(ruten.get("item_id", "")))
                if not ruten_response_ok(payload):
                    raise RuntimeError(ruten_response_message(payload))
                data = ruten_flatten_product_data(payload.get("data") or {})
                status = first_valid_ruten_status(data, default=ruten.get("status", "unknown"))
                if status == "unknown":
                    status = self.fetch_ruten_status_from_lists(str(ruten.get("item_id", "")))
                ruten["status"] = status
                if "qty" in data:
                    ruten["remote_stock"] = data.get("qty")
                if "price" in data:
                    ruten["price"] = to_int(data.get("price", 0))
                if data.get("name"):
                    ruten["title"] = str(data.get("name", ""))
                self.update_ruten_result(record, True)
                ok_count += 1
            except Exception as exc:
                fail_count += 1
                self.update_ruten_result(record, False, str(exc))
                fail_messages.append(f"{record.get('name', '')}：{exc}")
        save_db(self.db)
        self.refresh_ruten_table()
        if len(bound_items) == 1 and ok_count == 1:
            QMessageBox.information(self, "完成", f"已查詢露天商品狀態：{self.ruten_status_text(str(bound_items[0][1].get('status', 'unknown')))}")
        else:
            detail = "\n".join(fail_messages[:8])
            QMessageBox.information(self, "批次查詢完成", f"成功：{ok_count} 筆\n失敗：{fail_count} 筆" + (f"\n\n{detail}" if detail else ""))

    def find_mtg_by_ruten_identity(self, item_id: str, spec_id: str = "", custom_no: str = "") -> dict[str, Any] | None:
        item_id = clean_text(str(item_id))
        spec_id = clean_text(str(spec_id))
        custom_no = clean_text(str(custom_no))
        for record in self.db.get("mtg_inventory", []):
            ruten = ensure_ruten_item_fields(record)
            local_item_id = clean_text(str(ruten.get("item_id", "")))
            local_spec_id = clean_text(str(ruten.get("spec_id", "")))
            local_custom_no = clean_text(str(ruten.get("custom_no", "")))
            if item_id and local_item_id == item_id:
                if spec_id:
                    if local_spec_id == spec_id:
                        return record
                elif not local_spec_id:
                    return record
            if custom_no and local_custom_no == custom_no:
                return record
        return None

    def apply_ruten_entry_to_existing_record(self, record: dict[str, Any], entry: dict[str, Any]) -> None:
        ruten = ensure_ruten_item_fields(record)
        item_id = clean_text(str(entry.get("item_id", "")))
        spec_id = clean_text(str(entry.get("spec_id", "")))
        custom_no = clean_text(str(entry.get("custom_no", "")))
        title = clean_text(str(entry.get("title", "")))
        price = to_int(entry.get("price", 0))
        qty = max(0, to_int(entry.get("qty", 0)))

        if item_id:
            ruten["item_id"] = item_id
        if spec_id:
            ruten["spec_id"] = spec_id
        if custom_no:
            ruten["custom_no"] = custom_no
        if title:
            ruten["title"] = title
        if price > 0:
            ruten["price"] = price
        description = normalize_ruten_description_lines(entry.get("description", ""))
        if description:
            ruten["description"] = description
        class_id = normalize_ruten_class_id(entry.get("class_id", ""))
        if class_id:
            ruten["class_id"] = class_id
        store_class_id = clean_text(str(entry.get("store_class_id", "")))
        if store_class_id:
            ruten["store_class_id"] = store_class_id
        condition = to_int(entry.get("condition", 0))
        if condition > 0:
            ruten["condition"] = condition
        stock_status = clean_text(str(entry.get("stock_status", "")))
        if stock_status:
            ruten["stock_status"] = stock_status
        location_type = to_int(entry.get("location_type", 0))
        if location_type > 0:
            ruten["location_type"] = location_type
        location = normalize_ruten_location_code(entry.get("location", ""))
        if location:
            ruten["location"] = location
        new_status = normalize_ruten_status(entry.get("status", "unknown"))
        if new_status != "unknown":
            ruten["status"] = new_status
        elif is_unknown_ruten_status(ruten.get("status", "unknown")):
            ruten["status"] = "unknown"
        ruten["remote_stock"] = qty
        if to_int(ruten.get("listing_qty", 0)) <= 0 or to_int(ruten.get("listing_qty", 0)) > max(0, to_int(record.get("quantity", 0))):
            ruten["listing_qty"] = min(qty, max(0, to_int(record.get("quantity", 0))))
        ruten["match_status"] = "已配對"
        ruten["match_note"] = "已透過露天商品ID / 規格ID / 自用料號配對。"
        ruten["last_sync_at"] = now_text()
        ruten["last_error"] = ""
        record["updated_at"] = now_text()

    def fetch_ruten_remote_entries(self) -> tuple[list[dict[str, Any]], int, int]:
        client = self.ruten_client()
        all_items: list[dict[str, Any]] = []
        total = 0
        offset = 1
        limit = 100
        seen_page_keys: set[tuple[str, str]] = set()
        for _page in range(100):
            payload = client.list_products(status="all", offset=offset, limit=limit)
            if not ruten_response_ok(payload):
                raise RuntimeError(ruten_response_message(payload))
            page_items = ruten_product_list_items(payload)
            total = max(total, ruten_product_total(payload, len(page_items)))
            new_in_page = 0
            for item in page_items:
                key = (
                    clean_text(str(ruten_pick(item, "item_id", "id", "product_id", "rt_item_id"))),
                    clean_text(str(ruten_pick(item, "spec_id", "sku_id", "option_id"))),
                )
                if key in seen_page_keys:
                    continue
                seen_page_keys.add(key)
                all_items.append(item)
                new_in_page += 1
            if not page_items or new_in_page <= 0 or len(page_items) < limit:
                break
            if total and len(all_items) >= total:
                break
            offset += limit

        items = all_items
        total = total or len(items)

        status_by_item_id: dict[str, str] = {}
        for status_code in ("on", "off", "out"):
            offset_status = 1
            limit_status = 100
            for _status_page in range(100):
                try:
                    status_payload = client.list_products(status=status_code, offset=offset_status, limit=limit_status)
                except Exception:
                    break
                if not ruten_response_ok(status_payload):
                    break
                status_items = ruten_product_list_items(status_payload)
                for status_item in status_items:
                    status_item_id = clean_text(str(ruten_pick(status_item, "item_id", "id", "product_id", "rt_item_id")))
                    if status_item_id:
                        status_by_item_id[status_item_id] = normalize_ruten_status(status_code)
                if not status_items or len(status_items) < limit_status:
                    break
                offset_status += limit_status

        entries: list[dict[str, Any]] = []
        detail_failures = 0
        seen_item_ids: set[str] = set()

        for index, item in enumerate(items, start=1):
            item_id = clean_text(str(ruten_pick(item, "item_id", "id", "product_id", "rt_item_id")))
            forced_status = status_by_item_id.get(item_id, "")
            if forced_status:
                item = dict(item)
                item["__query_status"] = forced_status
            detail_data: dict[str, Any] = {}
            if item_id and item_id not in seen_item_ids:
                seen_item_ids.add(item_id)
                try:
                    detail_payload = client.get_item(item_id)
                    if ruten_response_ok(detail_payload):
                        detail_data = ruten_flatten_product_data(detail_payload.get("data") or {})
                    else:
                        detail_failures += 1
                except Exception:
                    detail_failures += 1
                time.sleep(0.08)
            entries.extend(ruten_remote_entries(item, detail_data))
            if index % 20 == 0:
                self.ruten_status_label.setText(f"正在讀取露天商品：{index}/{len(items)}")
                QApplication.processEvents()

        unique_entries: list[dict[str, Any]] = []
        seen_keys: set[tuple[str, str, str]] = set()
        for entry in entries:
            key = (
                clean_text(str(entry.get("item_id", ""))),
                clean_text(str(entry.get("spec_id", ""))),
                clean_text(str(entry.get("custom_no", ""))),
            )
            if key in seen_keys:
                continue
            seen_keys.add(key)
            unique_entries.append(entry)
        return unique_entries, total, detail_failures

    def sync_ruten_product_list(self, show_message: bool = True) -> dict[str, int]:
        try:
            before_empty = len(self.db.get("mtg_inventory", [])) == 0
            entries, total, detail_failures = self.fetch_ruten_remote_entries()
            imported = 0
            updated = 0
            for entry in entries:
                record = self.find_mtg_by_ruten_identity(
                    str(entry.get("item_id", "")),
                    str(entry.get("spec_id", "")),
                    str(entry.get("custom_no", "")),
                )
                if record:
                    self.apply_ruten_entry_to_existing_record(record, entry)
                    if not clean_text(str(record.get("image_url", ""))) or str(record.get("source", "")) == "ruten":
                        enrich_ruten_import_record_with_scryfall(record, entry)
                    updated += 1
                else:
                    new_record = make_mtg_inventory_item_from_ruten(entry)
                    enrich_ruten_import_record_with_scryfall(new_record, entry)
                    self.db.setdefault("mtg_inventory", []).append(new_record)
                    imported += 1

            ensure_ruten_settings(self.db)["last_remote_import_at"] = now_text()
            update_ruten_pairing_conflicts(self.db)
            self.set_ruten_api_status(product_ok=True)
            save_db(self.db)
            self.refresh_mtg_inventory_filter_options()
            self.refresh_mtg_inventory_table()
            self.refresh_ruten_table()
            stats = {
                "remote_total": int(total),
                "remote_entries": len(entries),
                "imported": imported,
                "updated": updated,
                "detail_failures": detail_failures,
                "before_empty": 1 if before_empty else 0,
            }
            self.ruten_status_label.setText(f"露天匯入/更新完成：新增 {imported}，更新 {updated}")
            if show_message:
                extra = "\n本機原本沒有 MTG庫存，這次已優先從露天建立本機資料。" if before_empty and imported > 0 else ""
                detail_text = f"\n商品明細讀取失敗：{detail_failures} 筆" if detail_failures else ""
                QMessageBox.information(
                    self,
                    "完成",
                    f"露天匯入/更新完成。\n露天商品數：{total}\n同步項目數：{len(entries)}\n本機新增：{imported}\n本機更新：{updated}{detail_text}{extra}",
                )
            return stats
        except Exception as exc:
            self.set_ruten_api_status(product_ok=False, error=str(exc))
            if show_message:
                QMessageBox.warning(self, "從露天匯入/更新失敗", str(exc))
                return {"remote_total": 0, "remote_entries": 0, "imported": 0, "updated": 0, "detail_failures": 0, "before_empty": 0}
            raise

    def push_enabled_ruten_records_to_remote(self, records: list[dict[str, Any]]) -> tuple[int, int]:
        def worker(record: dict[str, Any]) -> None:
            ok, msg = self.push_single_ruten_record_to_remote(record, sync_price=False, apply_online_rules=True)
            if not ok:
                raise RuntimeError(msg)
        ok_count, failures = self.run_ruten_batch("批次同步露天上架數量", records, worker)
        self._last_ruten_batch_failures = failures
        return ok_count, len(failures)

    def safe_bidirectional_ruten_sync(self) -> None:
        if QMessageBox.question(
            self,
            "確認安全雙向同步",
            "會先從露天匯入/更新商品，缺少的露天商品會建立到本機；接著再把本機允許同步的庫存數量同步回露天。確定執行？",
        ) != QMessageBox.Yes:
            return
        try:
            self.backup_db_before_ruten_write()
            import_stats = self.sync_ruten_product_list(show_message=False)
            records = []
            for record in self.db.get("mtg_inventory", []):
                ruten = ensure_ruten_item_fields(record)
                if bool(ruten.get("enabled", True)) and clean_text(str(ruten.get("item_id", ""))):
                    records.append(record)
            ok_count, fail_count = self.push_enabled_ruten_records_to_remote(records)
            save_db(self.db)
            self.refresh_mtg_inventory_filter_options()
            self.refresh_mtg_inventory_table()
            self.refresh_ruten_table()
            QMessageBox.information(
                self,
                "安全雙向同步完成",
                f"露天讀取商品數：{import_stats.get('remote_total', 0)}\n"
                f"本機新增：{import_stats.get('imported', 0)}\n"
                f"本機更新：{import_stats.get('updated', 0)}\n"
                f"同步回露天成功：{ok_count}\n"
                f"同步回露天失敗：{fail_count}",
            )
        except Exception as exc:
            QMessageBox.warning(self, "安全雙向同步失敗", str(exc))

    def ruten_order_status_code(self, status: Any) -> str:
        text = clean_text(str(status))
        mapping = {
            "全部": "All",
            "尚未付款": "Unpaid",
            "待確認": "ToBeConfirmed",
            "待出貨": "ReadyToShip",
            "已出貨": "Shipped",
            "待取消": "InCancel",
            "已取消": "Cancelled",
        }
        return mapping.get(text, text)

    def ruten_order_should_deduct(self, status: Any) -> bool:
        settings = self.ruten_settings()
        status_code = self.ruten_order_status_code(status)
        allowed = settings.get("auto_apply_order_statuses")
        if not isinstance(allowed, list) or not allowed:
            allowed = ["ToBeConfirmed", "ReadyToShip", "Shipped"]
        return status_code in {str(item) for item in allowed}

    def ruten_order_is_cancelled(self, status: Any) -> bool:
        return self.ruten_order_status_code(status) in {"Cancelled"}

    def ruten_order_item_key(self, order_id: str, item_id: str, spec_id: str = "", custom_no: str = "") -> str:
        return f"{clean_text(order_id)}:{clean_text(item_id)}:{clean_text(spec_id)}:{clean_text(custom_no)}"

    def find_mtg_by_ruten_order_item(self, item: dict[str, Any]) -> dict[str, Any] | None:
        item_id = clean_text(str(item.get("item_id", "")))
        spec_id = clean_text(str(item.get("spec_id", "")))
        custom_no = clean_text(str(item.get("custom_no", "")))
        for record in self.db.get("mtg_inventory", []):
            ruten = ensure_ruten_item_fields(record)
            if item_id and clean_text(str(ruten.get("item_id", ""))) == item_id:
                local_spec = clean_text(str(ruten.get("spec_id", "")))
                if not spec_id or not local_spec or local_spec == spec_id:
                    return record
            if custom_no and clean_text(str(ruten.get("custom_no", ""))) == custom_no:
                return record
        return None

    def append_ruten_notification(self, notification: dict[str, Any]) -> bool:
        self.db.setdefault("ruten_notifications", [])
        key = str(notification.get("key", ""))
        for item in self.db.get("ruten_notifications", []):
            if key and str(item.get("key", "")) == key:
                created_at = item.get("created_at", notification.get("created_at", now_text()))
                item.update(notification)
                item["created_at"] = created_at
                item["updated_at"] = now_text()
                return False
        self.db["ruten_notifications"].append(notification)
        self.db["ruten_notifications"] = self.db["ruten_notifications"][-500:]
        return True

    def query_ruten_orders(self, show_message: bool = True, auto_mode: bool = False) -> None:
        settings = self.ruten_settings()
        if hasattr(self, "ruten_order_auto_apply_check"):
            settings["auto_apply_orders"] = bool(self.ruten_order_auto_apply_check.isChecked())
        now_dt = datetime.now()
        if auto_mode:
            order_status = "All"
            end_date = now_dt.strftime("%Y%m%d%H%M%S")
            start_date = (now_dt - timedelta(days=7)).strftime("%Y%m%d000000")
        else:
            order_status = str(self.ruten_order_status_combo.currentData() or "All")
            start_date = self.ruten_order_start_edit.text().strip()
            end_date = self.ruten_order_end_edit.text().strip()
        settings["last_order_check_at"] = now_text()
        save_db(self.db)

        try:
            client = self.ruten_client()
            payload = client.list_orders(order_status, start_date, end_date, page=1, page_size=100)
            if not ruten_response_ok(payload):
                raise RuntimeError(ruten_response_message(payload))
            data = payload.get("data") or {}
            order_list = data.get("order_list", []) if isinstance(data, dict) else []
            order_ids = [clean_text(str(item.get("order_id", ""))) for item in order_list if isinstance(item, dict) and item.get("order_id")]
            new_count = 0
            applied_count = 0
            restored_count = 0
            unmatched_count = 0
            order_status_by_id = {clean_text(str(item.get("order_id", ""))): clean_text(str(item.get("order_status", ""))) for item in order_list if isinstance(item, dict)}
            processing = self.db.setdefault("ruten_order_processing", {})
            if not isinstance(processing, dict):
                processing = {}
                self.db["ruten_order_processing"] = processing
            records_to_push: list[dict[str, Any]] = []

            for start in range(0, len(order_ids), 30):
                detail_payload = client.order_detail(order_ids[start:start + 30])
                if not ruten_response_ok(detail_payload):
                    raise RuntimeError(f"查詢訂單明細失敗：{ruten_response_message(detail_payload)}")
                details = detail_payload.get("data") or []
                if isinstance(details, dict):
                    details = [details]
                for detail_entry in details:
                    if not isinstance(detail_entry, dict):
                        continue
                    order_detail = detail_entry.get("order_detail") or {}
                    order_info = order_detail.get("order_info") or {}
                    checkout_info = order_detail.get("checkout_info") or {}
                    item_list = order_detail.get("item_list") or []
                    order_id = clean_text(str(detail_entry.get("order_id") or order_info.get("order_id") or ""))
                    status = clean_text(str(order_info.get("order_status") or order_status_by_id.get(order_id, "")))
                    buyer_id = clean_text(str(order_info.get("buyer_id", "")))
                    for item in item_list:
                        if not isinstance(item, dict):
                            continue
                        item_id = clean_text(str(item.get("item_id", "")))
                        spec_id = clean_text(str(item.get("spec_id", "")))
                        custom_no = clean_text(str(item.get("custom_no", "")))
                        qty = max(0, to_int(ruten_pick(item, "quantity_purchased", "qty", "quantity", "item_qty", default=0)))
                        matched = self.find_mtg_by_ruten_order_item(item)
                        key = self.ruten_order_item_key(order_id, item_id, spec_id, custom_no)
                        proc = processing.get(key)
                        if not isinstance(proc, dict):
                            proc = {}
                        applied_qty = max(0, to_int(proc.get("applied_qty", 0)))
                        restored_qty = max(0, to_int(proc.get("restored_qty", 0)))
                        result_text = "已通知"
                        applied_now = False
                        restored_now = False

                        if matched:
                            ruten = ensure_ruten_item_fields(matched)
                            ruten["last_order_at"] = now_text()
                            if self.ruten_order_is_cancelled(status) and bool(settings.get("auto_restore_cancelled_orders", True)):
                                restore_qty = max(0, applied_qty - restored_qty)
                                if restore_qty > 0:
                                    old_qty = int(matched.get("quantity", 0) or 0)
                                    matched["quantity"] = old_qty + restore_qty
                                    matched["updated_at"] = now_text()
                                    ruten["remote_stock"] = max(0, to_int(ruten.get("remote_stock", 0)) + restore_qty)
                                    if bool(ruten.get("auto_restock", False)):
                                        set_ruten_listing_qty(matched, min(to_int(ruten.get("restock_target", 1)) or 1, max(0, to_int(matched.get("quantity", 0)))))
                                    else:
                                        set_ruten_listing_qty(matched, max(0, to_int(ruten.get("remote_stock", 0))))
                                    proc["restored_qty"] = applied_qty
                                    proc["restore_before_qty"] = old_qty
                                    proc["restore_after_qty"] = matched["quantity"]
                                    restored_count += 1
                                    restored_now = True
                                    result_text = f"訂單已取消，已補回 MTG庫存：{old_qty} -> {matched['quantity']}"
                                    self.append_ruten_operation_log(
                                        "訂單取消補回庫存",
                                        "成功",
                                        matched,
                                        {"order_id": order_id, "item_id": item_id, "spec_id": spec_id, "restore_qty": restore_qty, "before_qty": old_qty, "after_qty": matched["quantity"], "order_status": status},
                                    )
                                    records_to_push.append(matched)
                                else:
                                    result_text = "訂單已取消；沒有需要補回的庫存"
                            elif settings.get("auto_apply_orders", False) and self.ruten_order_should_deduct(status) and qty > applied_qty:
                                deduct_qty = qty - applied_qty
                                old_qty = int(matched.get("quantity", 0) or 0)
                                matched["quantity"] = max(0, old_qty - deduct_qty)
                                matched["updated_at"] = now_text()
                                ruten["remote_stock"] = max(0, to_int(ruten.get("remote_stock", 0)) - deduct_qty)
                                if bool(ruten.get("auto_restock", False)):
                                    set_ruten_listing_qty(matched, min(to_int(ruten.get("restock_target", 1)) or 1, max(0, to_int(matched.get("quantity", 0)))))
                                else:
                                    set_ruten_listing_qty(matched, max(0, to_int(ruten.get("remote_stock", 0))))
                                proc["applied_qty"] = qty
                                proc["deduct_before_qty"] = old_qty
                                proc["deduct_after_qty"] = matched["quantity"]
                                proc["listing_qty_after"] = ruten_listing_qty(matched)
                                proc["remote_stock_after"] = ruten.get("remote_stock", "")
                                applied_count += 1
                                applied_now = True
                                result_text = f"已匹配並扣 MTG庫存：{old_qty} -> {matched['quantity']}；露天上架數量：{ruten_listing_qty(matched)}"
                                self.append_ruten_operation_log(
                                    "訂單扣本地庫存",
                                    "成功",
                                    matched,
                                    {"order_id": order_id, "item_id": item_id, "spec_id": spec_id, "deduct_qty": deduct_qty, "before_qty": old_qty, "after_qty": matched["quantity"], "order_status": status},
                                )
                                records_to_push.append(matched)
                            elif settings.get("auto_apply_orders", False) and not self.ruten_order_should_deduct(status):
                                result_text = f"已匹配；訂單狀態 {status or '-'} 尚未設定為扣庫存狀態"
                            elif applied_qty > 0:
                                result_text = f"已匹配；此訂單先前已扣庫存 {applied_qty}"
                            else:
                                result_text = "已匹配；未自動扣庫存"
                        else:
                            unmatched_count += 1
                            result_text = "未匹配 MTG庫存"

                        proc.update({
                            "key": key,
                            "order_id": order_id,
                            "item_id": item_id,
                            "spec_id": spec_id,
                            "custom_no": custom_no,
                            "quantity": qty,
                            "last_status": status,
                            "last_checked_at": now_text(),
                            "matched_mtg_id": matched.get("id", "") if matched else "",
                            "matched_name": matched.get("name", "") if matched else "",
                            "current_local_qty": matched.get("quantity", "") if matched else "",
                            "current_listing_qty": ruten_listing_qty(matched) if matched else "",
                        })
                        if applied_now:
                            proc["last_applied_at"] = now_text()
                        if restored_now:
                            proc["last_restored_at"] = now_text()
                        processing[key] = proc

                        notification = {
                            "key": key,
                            "created_at": now_text(),
                            "order_id": order_id,
                            "order_status": status,
                            "buyer_id": buyer_id,
                            "item_id": item_id,
                            "spec_id": spec_id,
                            "custom_no": custom_no,
                            "item_name": clean_text(str(item.get("item_name", ""))),
                            "quantity": qty,
                            "price": to_int(ruten_pick(item, "discount_price", "original_price", "price", "item_price", default=0)),
                            "total_amount": to_int(checkout_info.get("total_amount", 0)),
                            "matched_mtg_id": matched.get("id", "") if matched else "",
                            "applied_to_inventory": to_int(proc.get("applied_qty", 0)) > 0,
                            "restored_to_inventory": to_int(proc.get("restored_qty", 0)) > 0,
                            "result": result_text,
                        }
                        if self.append_ruten_notification(notification):
                            new_count += 1

            if bool(settings.get("auto_push_after_order_apply", False)) and records_to_push:
                unique_records: list[dict[str, Any]] = []
                seen_ids: set[str] = set()
                for record in records_to_push:
                    rid = str(record.get("id", ""))
                    if rid and rid not in seen_ids:
                        seen_ids.add(rid)
                        unique_records.append(record)
                self.push_enabled_ruten_records_to_remote(unique_records)

            settings["last_order_success_at"] = now_text()
            settings["last_order_error"] = ""
            self.append_ruten_operation_log(
                "查詢露天訂單",
                "成功",
                None,
                {"order_count": len(order_ids), "new_notifications": new_count, "deducted": applied_count, "restored": restored_count, "unmatched": unmatched_count, "auto_mode": auto_mode},
            )
            self.set_ruten_api_status(order_ok=True)
            save_db(self.db)
            self.refresh_ruten_table()
            self.refresh_mtg_inventory_table()
            self.refresh_ruten_notifications_table()
            if show_message:
                QMessageBox.information(
                    self,
                    "訂單通知完成",
                    f"訂單數：{len(order_ids)}\n新增通知：{new_count}\n自動扣庫存：{applied_count}\n取消補庫存：{restored_count}\n未匹配商品：{unmatched_count}",
                )
            else:
                self.statusBar().showMessage(
                    f"露天自動查單完成：訂單 {len(order_ids)}，新通知 {new_count}，扣庫存 {applied_count}，補庫存 {restored_count}，未匹配 {unmatched_count}",
                    8000,
                )
        except Exception as exc:
            settings["last_order_failure_at"] = now_text()
            error_text = translate_ruten_error("", exc)
            settings["last_order_error"] = error_text
            self.append_ruten_operation_log("查詢露天訂單", "失敗", None, {"auto_mode": auto_mode}, error_text)
            self.set_ruten_api_status(order_ok=False, error=error_text)
            save_db(self.db)
            if show_message:
                QMessageBox.warning(self, "查詢訂單通知失敗", error_text)
            else:
                self.statusBar().showMessage(f"露天自動查單失敗：{error_text}", 10000)

    def auto_query_ruten_orders_tick(self) -> None:
        settings = self.ruten_settings()
        if not bool(settings.get("auto_order_check", False)):
            return
        if not self.ruten_client().is_ready():
            self.statusBar().showMessage("露天自動查單略過：API 尚未設定完整", 8000)
            return
        self.query_ruten_orders(show_message=False, auto_mode=True)

    def refresh_ruten_notifications_table(self) -> None:
        if not hasattr(self, "ruten_notifications_table"):
            return
        notifications = list(self.db.get("ruten_notifications", []))
        notifications = sorted(notifications, key=lambda x: str(x.get("created_at", "")), reverse=True)[:200]
        self.ruten_notifications_table.setRowCount(0)
        for row, item in enumerate(notifications):
            self.ruten_notifications_table.insertRow(row)
            created_item = QTableWidgetItem(str(item.get("created_at", "")))
            created_item.setData(Qt.UserRole, str(item.get("key", "")))
            self.ruten_notifications_table.setItem(row, 0, created_item)
            self.ruten_notifications_table.setItem(row, 1, QTableWidgetItem(str(item.get("order_id", ""))))
            self.ruten_notifications_table.setItem(row, 2, QTableWidgetItem(str(item.get("order_status", ""))))
            self.ruten_notifications_table.setItem(row, 3, QTableWidgetItem(str(item.get("item_id", ""))))
            self.ruten_notifications_table.setItem(row, 4, QTableWidgetItem(str(item.get("item_name", ""))))
            self.ruten_notifications_table.setItem(row, 5, QTableWidgetItem(str(item.get("quantity", 0))))
            self.ruten_notifications_table.setItem(row, 6, QTableWidgetItem(str(item.get("price", ""))))
            matched_name = ""
            matched_id = str(item.get("matched_mtg_id", ""))
            if matched_id:
                matched_record = self.get_mtg_inventory_item(matched_id)
                matched_name = str(matched_record.get("name", "")) if matched_record else matched_id
            self.ruten_notifications_table.setItem(row, 7, QTableWidgetItem(matched_name))
            self.ruten_notifications_table.setItem(row, 8, QTableWidgetItem("是" if bool(item.get("applied_to_inventory", False)) else "否"))
            self.ruten_notifications_table.setItem(row, 9, QTableWidgetItem("是" if bool(item.get("restored_to_inventory", False)) else "否"))
            self.ruten_notifications_table.setItem(row, 10, QTableWidgetItem(str(item.get("result", ""))))

    def build_about_tab(self) -> None:
        root = QVBoxLayout(self.about_tab)

        activate_group = QGroupBox("啟用狀態")
        activate_layout = QVBoxLayout(activate_group)
        self.license_status_label = QLabel("授權狀態載入中...")
        self.license_status_label.setWordWrap(True)
        activate_layout.addWidget(self.license_status_label)

        server_row = QHBoxLayout()
        self.license_server_url_edit = QLineEdit()
        self.license_server_url_edit.setPlaceholderText("例如：https://script.google.com/macros/s/部署ID/exec")
        self.license_save_server_btn = QPushButton("儲存授權伺服器")
        self.license_save_server_btn.clicked.connect(self.save_license_server_from_input)
        server_row.addWidget(QLabel("授權伺服器："))
        server_row.addWidget(self.license_server_url_edit, 1)
        server_row.addWidget(self.license_save_server_btn)
        activate_layout.addLayout(server_row)

        key_row = QHBoxLayout()
        self.license_key_edit = QLineEdit()
        self.license_key_edit.setPlaceholderText("貼上 CARDTRADELIB-LIC.v1... 啟用金鑰")
        self.license_activate_btn = QPushButton("啟用金鑰")
        self.license_activate_btn.clicked.connect(self.activate_license_from_input)
        self.license_check_btn = QPushButton("立即驗證授權")
        self.license_check_btn.clicked.connect(lambda _checked=False: self.refresh_about_license_status(use_network=True, show_message=True))
        key_row.addWidget(QLabel("啟用金鑰："))
        key_row.addWidget(self.license_key_edit, 1)
        key_row.addWidget(self.license_activate_btn)
        key_row.addWidget(self.license_check_btn)
        activate_layout.addLayout(key_row)

        activate_note = QLabel(
            "試用版金鑰啟用後有效 7 天；正式版金鑰啟用後有效 30 天。\n"
            "啟用與驗證會連到你的 Google Apps Script / Google Sheet 授權伺服器；同一組金鑰只能綁定一台電腦。\n"
            f"離線超過 {LICENSE_OFFLINE_GRACE_HOURS} 小時未驗證時，露天同步、上架與訂單功能會暫停。"
        )
        activate_note.setWordWrap(True)
        activate_layout.addWidget(activate_note)

        about_group = QGroupBox("關於")
        about_layout = QVBoxLayout(about_group)
        about_label = QLabel(
            f"{APP_TITLE} v63 Google Sheet\n"
            "用途：本機卡片庫存、Scryfall 查詢、MTG庫存與露天賣場同步管理。\n\n"
            f"程式資料夾：{BASE_DIR}\n"
            f"設定資料夾：{CONFIG_DIR}\n"
            f"資料庫：{DB_PATH}\n"
            f"授權狀態：{LICENSE_STATE_PATH}\n"
            f"露天 API 金鑰：{RUTEN_SECRET_PATH}\n"
            f"圖片資料夾：{IMAGE_DIR}\n"
        )
        about_label.setWordWrap(True)
        about_layout.addWidget(about_label)

        button_row = QHBoxLayout()
        self.about_open_config_btn = QPushButton("開啟 config 資料夾")
        self.about_open_config_btn.clicked.connect(lambda _checked=False: self.open_local_path(CONFIG_DIR))
        self.about_open_images_btn = QPushButton("開啟 card_images 資料夾")
        self.about_open_images_btn.clicked.connect(lambda _checked=False: self.open_local_path(IMAGE_DIR))
        self.about_open_log_btn = QPushButton("開啟操作紀錄")
        self.about_open_log_btn.clicked.connect(lambda _checked=False: self.open_local_path(RUTEN_OPERATION_LOG_PATH))
        self.about_open_license_btn = QPushButton("開啟授權狀態檔")
        self.about_open_license_btn.clicked.connect(lambda _checked=False: self.open_local_path(LICENSE_STATE_PATH))
        button_row.addWidget(self.about_open_config_btn)
        button_row.addWidget(self.about_open_images_btn)
        button_row.addWidget(self.about_open_log_btn)
        button_row.addWidget(self.about_open_license_btn)
        button_row.addStretch(1)
        about_layout.addLayout(button_row)

        note_group = QGroupBox("注意")
        note_layout = QVBoxLayout(note_group)
        note_label = QLabel(
            "不要分享 config/ruten_api_secrets.json，裡面可能包含你的露天 API Key / Secret Key / Salt Key。\n"
            "不要把 license_keygen.py 給使用者；它是你自己產生金鑰用的工具。\n"
            "如果要打包或備份給別人，請先刪除或排除露天 API 金鑰檔。"
        )
        note_label.setWordWrap(True)
        note_layout.addWidget(note_label)

        root.addWidget(activate_group)
        root.addWidget(about_group)
        root.addWidget(note_group)
        root.addStretch(1)

    def save_license_server_from_input(self) -> None:
        url = self.license_server_url_edit.text().strip() if hasattr(self, "license_server_url_edit") else ""
        if url and not (url.startswith("https://") or url.startswith("http://")):
            QMessageBox.warning(self, "網址格式錯誤", "授權伺服器網址需要以 https:// 或 http:// 開頭。")
            return
        save_license_server_settings({"server_url": url})
        QMessageBox.information(self, "已儲存", "授權伺服器網址已儲存。")
        self.refresh_about_license_status(use_network=False)

    def activate_license_from_input(self) -> None:
        key = self.license_key_edit.text().strip() if hasattr(self, "license_key_edit") else ""
        if not key:
            QMessageBox.warning(self, "未輸入金鑰", "請先貼上啟用金鑰。")
            return
        ok, message, _state = activate_license_key(key)
        if ok:
            self.license_key_edit.clear()
            QMessageBox.information(self, "啟用成功", message)
        else:
            QMessageBox.warning(self, "啟用失敗", message)
        self.refresh_about_license_status(use_network=False)
        self.update_license_gated_controls()
        self.restart_ruten_timers()

    def refresh_about_license_status(self, use_network: bool = False, show_message: bool = False) -> None:
        status = evaluate_license(use_network=use_network)
        server_settings = load_license_server_settings()
        if hasattr(self, "license_server_url_edit"):
            current = self.license_server_url_edit.text().strip()
            target = clean_text(str(server_settings.get("server_url", "")))
            if current != target:
                self.license_server_url_edit.setText(target)
        state = status.get("state", {}) if isinstance(status.get("state"), dict) else {}
        payload = state.get("license_payload", {}) if isinstance(state.get("license_payload"), dict) else {}
        license_type = clean_text(str(state.get("license_type", ""))).lower()
        type_label = "試用版" if license_type == "trial" else ("正式版" if license_type == "pro" else "未啟用")
        lines = [
            f"目前狀態：{status.get('label', '未知')}",
            f"說明：{status.get('message', '')}",
            f"授權伺服器：{server_settings.get('server_url', '') or '尚未設定'}",
            f"本機機器碼：{machine_id_hash()[:16]}...",
        ]
        if state:
            lines.extend([
                f"授權版本：{type_label}",
                f"金鑰：{state.get('license_key_mask', '')}",
                f"License ID：{payload.get('license_id', '')}",
                f"Customer：{payload.get('customer', '')}",
                f"啟用時間：{state.get('activated_at', '')}",
                f"到期時間：{state.get('expires_at', '')}",
                f"上次網路驗證：{state.get('last_server_check_at', '')}",
                f"網路時間來源：{state.get('last_network_source', '')}",
                f"授權狀態檔：{LICENSE_STATE_PATH}",
            ])
        lines.append("露天 API 需在『露天賣場 → 設定露天 API』填入金鑰；程式授權有效時才能使用同步、上架、訂單功能。")
        if hasattr(self, "license_status_label"):
            self.license_status_label.setText("\n".join(lines))
        self.update_license_gated_controls()
        if show_message:
            if status.get("ok"):
                QMessageBox.information(self, "授權驗證成功", clean_text(str(status.get("message", ""))))
            else:
                QMessageBox.warning(self, "授權驗證失敗", clean_text(str(status.get("message", ""))))

    def license_allows_ruten_features(self) -> bool:
        return bool(evaluate_license(use_network=False).get("ok", False))

    def update_license_gated_controls(self) -> None:
        status = evaluate_license(use_network=False)
        allowed = bool(status.get("ok", False))
        reason = clean_text(str(status.get("message", "程式尚未啟用。")))
        gated_names = [
            "ruten_test_btn",
            "ruten_logistic_btn",
            "ruten_query_remote_btn",
            "ruten_sync_remote_list_btn",
            "ruten_two_way_sync_btn",
            "ruten_auto_order_check",
            "ruten_auto_order_minutes_spin",
            "ruten_auto_local_push_check",
            "ruten_auto_offline_zero_check",
            "ruten_auto_online_positive_check",
            "ruten_upsert_product_btn",
            "ruten_upload_image_btn",
            "ruten_offline_btn",
            "ruten_order_query_btn",
            "ruten_order_manual_deduct_btn",
            "ruten_order_manual_restore_btn",
            "ruten_order_repair_match_btn",
            "ruten_order_auto_apply_check",
            "mtg_inventory_list_ruten_btn",
        ]
        for name in gated_names:
            widget = getattr(self, name, None)
            if widget is not None:
                widget.setEnabled(allowed)
                widget.setToolTip("" if allowed else reason)
        if hasattr(self, "ruten_status_label"):
            self.update_ruten_status_label()

    def open_local_path(self, path: Path) -> None:
        target = Path(path)
        try:
            if target.suffix:
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.exists():
                    target.write_text("[]", encoding="utf-8")
            else:
                target.mkdir(parents=True, exist_ok=True)
            ok = QDesktopServices.openUrl(QUrl.fromLocalFile(str(target)))
            if not ok:
                QMessageBox.warning(self, "無法開啟", f"無法開啟：{target}")
        except Exception as exc:
            QMessageBox.warning(self, "無法開啟", str(exc))

    def build_add_tab(self) -> None:
        root = QHBoxLayout(self.add_tab)

        form_group = QGroupBox("新增一筆買入庫存")
        form = QFormLayout(form_group)

        self.add_name_edit = QLineEdit()
        self.add_name_edit.setPlaceholderText("例如：Michael Jordan 1996 Finest Refractor")

        self.add_category_combo = QComboBox()
        self.edit_category_btn = QPushButton("編輯分類")
        self.edit_category_btn.clicked.connect(self.open_category_dialog)
        category_row = QHBoxLayout()
        category_row.addWidget(self.add_category_combo, 1)
        category_row.addWidget(self.edit_category_btn)

        self.add_psa_check = QCheckBox("鑑定卡(PSA)")
        self.add_psa_score_edit = QLineEdit()
        self.add_psa_score_edit.setPlaceholderText("PSA 分數")
        self.add_bgs_check = QCheckBox("鑑定卡(BGS)")
        self.add_bgs_score_edit = QLineEdit()
        self.add_bgs_score_edit.setPlaceholderText("BGS 分數")
        grade_row = QGridLayout()
        grade_row.addWidget(self.add_psa_check, 0, 0)
        grade_row.addWidget(self.add_psa_score_edit, 0, 1)
        grade_row.addWidget(self.add_bgs_check, 1, 0)
        grade_row.addWidget(self.add_bgs_score_edit, 1, 1)

        self.add_quantity_spin = QSpinBox()
        self.add_quantity_spin.setRange(1, 999_999)
        self.add_quantity_spin.setValue(1)

        self.add_buy_total_spin = QDoubleSpinBox()
        self.add_buy_total_spin.setRange(0, 999_999_999)
        self.add_buy_total_spin.setDecimals(0)
        self.add_buy_total_spin.setSingleStep(100)
        self.add_buy_total_spin.setPrefix("NT$ ")

        self.add_buy_method_combo = QComboBox()

        self.add_note_edit = QTextEdit()
        self.add_note_edit.setPlaceholderText("可填來源、狀態、卡況、交易備註等")
        self.add_note_edit.setFixedHeight(110)

        self.add_image_btn = QPushButton("選擇圖片")
        self.add_image_btn.clicked.connect(self.choose_add_image)
        self.clear_add_image_btn = QPushButton("清除圖片")
        self.clear_add_image_btn.clicked.connect(self.clear_add_image)
        image_btn_row = QHBoxLayout()
        image_btn_row.addWidget(self.add_image_btn)
        image_btn_row.addWidget(self.clear_add_image_btn)
        image_btn_row.addStretch(1)

        self.add_submit_btn = QPushButton("加入庫存")
        self.add_submit_btn.setMinimumHeight(42)
        self.add_submit_btn.clicked.connect(self.add_inventory_item)

        form.addRow("卡片名稱：", self.add_name_edit)
        form.addRow("分類：", category_row)
        form.addRow("鑑定標籤：", grade_row)
        form.addRow("買入數量：", self.add_quantity_spin)
        form.addRow("買入總金額：", self.add_buy_total_spin)
        form.addRow("買入方式：", self.add_buy_method_combo)
        form.addRow("圖片：", image_btn_row)
        form.addRow("備註：", self.add_note_edit)
        form.addRow("", self.add_submit_btn)

        preview_group = QGroupBox("圖片預覽")
        preview_layout = QVBoxLayout(preview_group)
        self.add_image_preview = QLabel("無圖片")
        preview_layout.addWidget(self.add_image_preview, 1)

        root.addWidget(form_group, 2)
        root.addWidget(preview_group, 1)

    def build_inventory_tab(self) -> None:
        root = QVBoxLayout(self.inventory_tab)

        filter_row = QHBoxLayout()
        self.inventory_search_edit = QLineEdit()
        self.inventory_search_edit.setPlaceholderText("搜尋卡名 / 備註 / 分類 / 鑑定")
        self.inventory_search_edit.textChanged.connect(self.refresh_inventory_table)

        self.inventory_category_filter = QComboBox()
        self.inventory_category_filter.currentIndexChanged.connect(self.refresh_inventory_table)

        self.inventory_only_stock_combo = QComboBox()
        self.inventory_only_stock_combo.addItems(["只看有庫存", "全部批次", "只看已售完"])
        self.inventory_only_stock_combo.currentIndexChanged.connect(self.refresh_inventory_table)

        filter_row.addWidget(QLabel("搜尋："))
        filter_row.addWidget(self.inventory_search_edit, 1)
        filter_row.addWidget(QLabel("分類："))
        filter_row.addWidget(self.inventory_category_filter)
        filter_row.addWidget(QLabel("狀態："))
        filter_row.addWidget(self.inventory_only_stock_combo)

        self.inventory_table = QTableWidget(0, 11)
        self.inventory_table.setHorizontalHeaderLabels([
            "#",
            "卡片名稱",
            "分類",
            "鑑定標籤",
            "剩餘庫存",
            "原始數量",
            "買入單價",
            "買入總金額",
            "買入方式",
            "建立時間",
            "備註",
        ])
        self.inventory_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.inventory_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        setup_stable_table_columns(self.inventory_table, {
            0: 54,
            1: 240,
            2: 120,
            3: 120,
            4: 80,
            5: 80,
            6: 100,
            7: 120,
            8: 100,
            9: 160,
            10: 300,
        })
        self.inventory_table.verticalHeader().setVisible(False)
        self.inventory_table.itemSelectionChanged.connect(self.on_inventory_selected)
        self.inventory_table.itemDoubleClicked.connect(lambda _item: self.edit_selected_card())

        bottom = QHBoxLayout()
        self.inventory_image_preview = QLabel("選擇一筆庫存可預覽圖片")
        self.inventory_detail_label = QLabel("尚未選擇庫存")
        self.inventory_detail_label.setWordWrap(True)
        self.inventory_edit_btn = QPushButton("修改選取批次")
        self.inventory_edit_btn.clicked.connect(self.edit_selected_card)
        self.inventory_edit_btn.setToolTip("可修改卡名、分類、PSA/BGS、數量、買入金額、買入方式、圖片與備註。")

        self.inventory_export_btn = QPushButton("匯出庫存CSV")
        self.inventory_export_btn.clicked.connect(self.export_inventory_csv)

        self.inventory_delete_btn = QPushButton("刪除選取批次")
        self.inventory_delete_btn.clicked.connect(self.delete_selected_card)
        self.inventory_delete_btn.setToolTip("若已經有賣出紀錄，建議不要刪除；系統會要求確認。")

        action_col = QVBoxLayout()
        action_col.addWidget(self.inventory_edit_btn)
        action_col.addWidget(self.inventory_export_btn)
        action_col.addWidget(self.inventory_delete_btn)
        action_col.addStretch(1)

        bottom.addWidget(self.inventory_image_preview, 0)
        bottom.addWidget(self.inventory_detail_label, 1)
        bottom.addLayout(action_col, 0)

        root.addLayout(filter_row)
        root.addWidget(self.inventory_table, 1)
        root.addLayout(bottom)

    def build_sell_tab(self) -> None:
        root = QHBoxLayout(self.sell_tab)

        form_group = QGroupBox("賣出 / 扣庫存")
        form = QFormLayout(form_group)

        self.sell_category_filter = QComboBox()
        self.sell_category_filter.currentIndexChanged.connect(self.refresh_sell_combo)

        self.sell_search_edit = QLineEdit()
        self.sell_search_edit.setPlaceholderText("搜尋卡名 / 備註 / 分類 / 鑑定")
        self.sell_search_edit.textChanged.connect(self.refresh_sell_combo)

        self.sell_card_combo = QComboBox()
        self.sell_card_combo.currentIndexChanged.connect(self.on_sell_card_changed)

        self.sell_info_label = QLabel("請先選擇庫存")
        self.sell_info_label.setWordWrap(True)

        self.sell_quantity_spin = QSpinBox()
        self.sell_quantity_spin.setRange(1, 1)
        self.sell_quantity_spin.valueChanged.connect(self.update_sell_estimate)

        self.sell_total_spin = QDoubleSpinBox()
        self.sell_total_spin.setRange(0, 999_999_999)
        self.sell_total_spin.setDecimals(0)
        self.sell_total_spin.setSingleStep(100)
        self.sell_total_spin.setPrefix("NT$ ")
        self.sell_total_spin.valueChanged.connect(self.update_sell_estimate)

        self.sell_fee_spin = QDoubleSpinBox()
        self.sell_fee_spin.setRange(0, 999_999_999)
        self.sell_fee_spin.setDecimals(0)
        self.sell_fee_spin.setSingleStep(10)
        self.sell_fee_spin.setPrefix("NT$ ")
        self.sell_fee_spin.valueChanged.connect(self.update_sell_estimate)

        self.sell_note_edit = QTextEdit()
        self.sell_note_edit.setPlaceholderText("可填平台、買家、寄送、交易備註等")
        self.sell_note_edit.setFixedHeight(110)

        self.sell_estimate_label = QLabel("收益預估：-")
        self.sell_estimate_label.setStyleSheet("font-weight: bold; font-size: 16px;")

        self.sell_submit_btn = QPushButton("確認賣出並扣庫存")
        self.sell_submit_btn.setMinimumHeight(42)
        self.sell_submit_btn.clicked.connect(self.sell_selected_inventory)

        form.addRow("分類篩選：", self.sell_category_filter)
        form.addRow("搜尋：", self.sell_search_edit)
        form.addRow("選擇庫存：", self.sell_card_combo)
        form.addRow("庫存資訊：", self.sell_info_label)
        form.addRow("賣出數量：", self.sell_quantity_spin)
        form.addRow("賣出總金額：", self.sell_total_spin)
        form.addRow("手續費/平台費/運費：", self.sell_fee_spin)
        form.addRow("備註：", self.sell_note_edit)
        form.addRow("", self.sell_estimate_label)
        form.addRow("", self.sell_submit_btn)

        preview_group = QGroupBox("選取庫存圖片")
        preview_layout = QVBoxLayout(preview_group)
        self.sell_image_preview = QLabel("無圖片")
        preview_layout.addWidget(self.sell_image_preview, 1)

        root.addWidget(form_group, 2)
        root.addWidget(preview_group, 1)

    def build_report_tab(self) -> None:
        root = QVBoxLayout(self.report_tab)

        self.summary_group = QGroupBox("總覽")
        summary_layout = QGridLayout(self.summary_group)
        self.summary_inventory_qty = QLabel("0")
        self.summary_inventory_cost = QLabel("NT$ 0")
        self.summary_sales_revenue = QLabel("NT$ 0")
        self.summary_sales_cost = QLabel("NT$ 0")
        self.summary_sales_fee = QLabel("NT$ 0")
        self.summary_profit = QLabel("NT$ 0")
        self.summary_roi = QLabel("0.00%")

        summary_layout.addWidget(QLabel("目前剩餘庫存數量："), 0, 0)
        summary_layout.addWidget(self.summary_inventory_qty, 0, 1)
        summary_layout.addWidget(QLabel("目前庫存成本："), 0, 2)
        summary_layout.addWidget(self.summary_inventory_cost, 0, 3)
        summary_layout.addWidget(QLabel("累計賣出金額："), 1, 0)
        summary_layout.addWidget(self.summary_sales_revenue, 1, 1)
        summary_layout.addWidget(QLabel("已售出成本："), 1, 2)
        summary_layout.addWidget(self.summary_sales_cost, 1, 3)
        summary_layout.addWidget(QLabel("累計費用："), 2, 0)
        summary_layout.addWidget(self.summary_sales_fee, 2, 1)
        summary_layout.addWidget(QLabel("已實現收益："), 2, 2)
        summary_layout.addWidget(self.summary_profit, 2, 3)
        summary_layout.addWidget(QLabel("已實現 ROI："), 3, 0)
        summary_layout.addWidget(self.summary_roi, 3, 1)

        self.sales_table = QTableWidget(0, 11)
        self.sales_table.setHorizontalHeaderLabels([
            "#",
            "賣出時間",
            "卡片名稱",
            "分類",
            "鑑定標籤",
            "數量",
            "賣出總額",
            "買入成本",
            "費用",
            "收益",
            "ROI",
        ])
        self.sales_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.sales_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        setup_stable_table_columns(self.sales_table, {
            0: 54,
            1: 160,
            2: 240,
            3: 100,
            4: 120,
            5: 70,
            6: 110,
            7: 110,
            8: 100,
            9: 110,
            10: 90,
        })
        self.sales_table.verticalHeader().setVisible(False)

        btn_row = QHBoxLayout()
        self.export_sales_btn = QPushButton("匯出賣出紀錄CSV")
        self.export_sales_btn.clicked.connect(self.export_sales_csv)
        self.export_all_btn = QPushButton("匯出完整資料CSV")
        self.export_all_btn.clicked.connect(self.export_all_csv)
        self.delete_sale_btn = QPushButton("刪除選取賣出紀錄並回補庫存")
        self.delete_sale_btn.clicked.connect(self.delete_selected_sale)
        btn_row.addWidget(self.export_sales_btn)
        btn_row.addWidget(self.export_all_btn)
        btn_row.addWidget(self.delete_sale_btn)
        btn_row.addStretch(1)

        root.addWidget(self.summary_group)
        root.addWidget(QLabel("賣出紀錄："))
        root.addWidget(self.sales_table, 1)
        root.addLayout(btn_row)

    def refresh_all(self) -> None:
        self.refresh_category_combos()
        self.refresh_buy_method_combo()
        self.refresh_inventory_table()
        self.refresh_sell_combo()
        self.refresh_reports()
        self.refresh_mtg_inventory_filter_options()
        self.refresh_mtg_inventory_table()
        if hasattr(self, "refresh_ruten_table"):
            self.refresh_ruten_table()
        if hasattr(self, "refresh_ruten_notifications_table"):
            self.refresh_ruten_notifications_table()

    def refresh_category_combos(self) -> None:
        current_add = self.add_category_combo.currentText() if hasattr(self, "add_category_combo") else ""
        current_filter = self.inventory_category_filter.currentText() if hasattr(self, "inventory_category_filter") else ""
        current_sell_filter = self.sell_category_filter.currentText() if hasattr(self, "sell_category_filter") else ""

        self.add_category_combo.blockSignals(True)
        self.add_category_combo.clear()
        self.add_category_combo.addItems(self.categories())
        if current_add in self.categories():
            self.add_category_combo.setCurrentText(current_add)
        self.add_category_combo.blockSignals(False)

        self.inventory_category_filter.blockSignals(True)
        self.inventory_category_filter.clear()
        self.inventory_category_filter.addItem("全部分類")
        self.inventory_category_filter.addItems(self.categories())
        if current_filter:
            idx = self.inventory_category_filter.findText(current_filter)
            if idx >= 0:
                self.inventory_category_filter.setCurrentIndex(idx)
        self.inventory_category_filter.blockSignals(False)

        if hasattr(self, "sell_category_filter"):
            self.sell_category_filter.blockSignals(True)
            self.sell_category_filter.clear()
            self.sell_category_filter.addItem("全部分類")
            self.sell_category_filter.addItems(self.categories())
            if current_sell_filter:
                idx = self.sell_category_filter.findText(current_sell_filter)
                if idx >= 0:
                    self.sell_category_filter.setCurrentIndex(idx)
            self.sell_category_filter.blockSignals(False)

    def refresh_buy_method_combo(self) -> None:
        current = self.add_buy_method_combo.currentText() if hasattr(self, "add_buy_method_combo") else ""
        self.add_buy_method_combo.clear()
        self.add_buy_method_combo.addItems(self.buy_methods())
        if current in self.buy_methods():
            self.add_buy_method_combo.setCurrentText(current)

    def get_card(self, card_id: str) -> dict[str, Any] | None:
        for card in self.db["cards"]:
            if card.get("id") == card_id:
                return card
        return None

    def choose_add_image(self) -> None:
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            "選擇卡片圖片",
            str(BASE_DIR),
            "圖片檔案 (*.png *.jpg *.jpeg *.bmp *.webp);;所有檔案 (*.*)",
        )
        if not file_path:
            return
        self.selected_add_image_path = file_path
        load_image_preview(self.add_image_preview, file_path)

    def clear_add_image(self) -> None:
        self.selected_add_image_path = ""
        load_image_preview(self.add_image_preview, "")

    def add_inventory_item(self) -> None:
        name = self.add_name_edit.text().strip()
        if not name:
            QMessageBox.warning(self, "無法加入", "請輸入卡片名稱。")
            return

        quantity = int(self.add_quantity_spin.value())
        buy_total = float(self.add_buy_total_spin.value())
        psa_score = self.add_psa_score_edit.text().strip()
        bgs_score = self.add_bgs_score_edit.text().strip()
        psa_enabled = self.add_psa_check.isChecked() or bool(psa_score)
        bgs_enabled = self.add_bgs_check.isChecked() or bool(bgs_score)
        if not psa_enabled:
            psa_score = ""
        if not bgs_enabled:
            bgs_score = ""

        image_path = ""
        if self.selected_add_image_path:
            try:
                image_path = copy_image_to_library(self.selected_add_image_path)
            except Exception as exc:
                QMessageBox.warning(self, "圖片複製失敗", f"圖片無法複製到資料夾：\n{exc}")
                return

        card = {
            "id": uuid.uuid4().hex,
            "name": name,
            "category": self.add_category_combo.currentText(),
            "psa_enabled": psa_enabled,
            "psa_score": psa_score,
            "bgs_enabled": bgs_enabled,
            "bgs_score": bgs_score,
            "buy_method": self.add_buy_method_combo.currentText(),
            "buy_quantity": quantity,
            "remaining_quantity": quantity,
            "buy_total": buy_total,
            "image_path": image_path,
            "note": self.add_note_edit.toPlainText().strip(),
            "created_at": now_text(),
            "updated_at": now_text(),
        }
        self.db["cards"].append(card)
        save_db(self.db)

        self.add_name_edit.clear()
        self.add_psa_check.setChecked(False)
        self.add_psa_score_edit.clear()
        self.add_bgs_check.setChecked(False)
        self.add_bgs_score_edit.clear()
        self.add_quantity_spin.setValue(1)
        self.add_buy_total_spin.setValue(0)
        self.add_note_edit.clear()
        self.clear_add_image()

        self.refresh_all()
        self.statusBar().showMessage(f"已加入庫存：{name} x {quantity}", 5000)
        QMessageBox.information(self, "完成", f"已加入庫存：{name}\n數量：{quantity}\n買入單價：NT$ {money(card_unit_cost(card))}")

    def open_category_dialog(self) -> None:
        used = {str(card.get("category", "")) for card in self.db["cards"] if card.get("category")}
        dialog = CategoryDialog(self.categories(), used, self)
        if dialog.exec() != QDialog.Accepted:
            return

        old_to_new = dialog.rename_map
        for card in self.db["cards"]:
            old_category = card.get("category", "")
            if old_category in old_to_new:
                card["category"] = old_to_new[old_category]
                card["updated_at"] = now_text()

        self.db["categories"] = dialog.categories
        save_db(self.db)
        self.refresh_all()
        self.statusBar().showMessage("分類已更新", 5000)

    def refresh_inventory_table(self) -> None:
        search = self.inventory_search_edit.text().strip().lower() if hasattr(self, "inventory_search_edit") else ""
        category_filter = self.inventory_category_filter.currentText() if hasattr(self, "inventory_category_filter") else "全部分類"
        stock_mode = self.inventory_only_stock_combo.currentText() if hasattr(self, "inventory_only_stock_combo") else "只看有庫存"

        cards = []
        for card in self.db["cards"]:
            remaining = int(card.get("remaining_quantity", 0) or 0)
            if stock_mode == "只看有庫存" and remaining <= 0:
                continue
            if stock_mode == "只看已售完" and remaining > 0:
                continue
            if category_filter != "全部分類" and card.get("category") != category_filter:
                continue

            haystack = " ".join([
                str(card.get("name", "")),
                str(card.get("category", "")),
                card_grade_text(card),
                str(card.get("buy_method", "")),
                str(card.get("note", "")),
            ]).lower()
            if search and search not in haystack:
                continue

            cards.append(card)

        self.inventory_table.setRowCount(0)
        for row, card in enumerate(cards):
            self.inventory_table.insertRow(row)
            item_no = QTableWidgetItem(str(row + 1))
            item_no.setData(Qt.UserRole, card.get("id"))
            self.inventory_table.setItem(row, 0, item_no)
            self.inventory_table.setItem(row, 1, QTableWidgetItem(str(card.get("name", ""))))
            self.inventory_table.setItem(row, 2, QTableWidgetItem(str(card.get("category", ""))))
            self.inventory_table.setItem(row, 3, QTableWidgetItem(card_grade_text(card)))
            self.inventory_table.setItem(row, 4, QTableWidgetItem(str(card.get("remaining_quantity", 0))))
            self.inventory_table.setItem(row, 5, QTableWidgetItem(str(card.get("buy_quantity", 0))))
            self.inventory_table.setItem(row, 6, QTableWidgetItem(f"NT$ {money(card_unit_cost(card))}"))
            self.inventory_table.setItem(row, 7, QTableWidgetItem(f"NT$ {money(card.get('buy_total', 0))}"))
            self.inventory_table.setItem(row, 8, QTableWidgetItem(str(card.get("buy_method", ""))))
            self.inventory_table.setItem(row, 9, QTableWidgetItem(str(card.get("created_at", ""))))
            self.inventory_table.setItem(row, 10, QTableWidgetItem(str(card.get("note", ""))))


    def selected_inventory_card_id(self) -> str:
        row = self.inventory_table.currentRow()
        if row < 0:
            return ""
        item = self.inventory_table.item(row, 0)
        return str(item.data(Qt.UserRole)) if item else ""

    def on_inventory_selected(self) -> None:
        card_id = self.selected_inventory_card_id()
        card = self.get_card(card_id) if card_id else None
        if not card:
            self.inventory_detail_label.setText("尚未選擇庫存")
            load_image_preview(self.inventory_image_preview, "", "選擇一筆庫存可預覽圖片")
            return

        remaining = int(card.get("remaining_quantity", 0) or 0)
        buy_qty = int(card.get("buy_quantity", 0) or 0)
        unit = card_unit_cost(card)
        self.inventory_detail_label.setText(
            f"卡片：{card.get('name', '')}\n"
            f"分類：{card.get('category', '')}｜鑑定標籤：{card_grade_text(card)}｜買入方式：{card.get('buy_method', '')}\n"
            f"庫存：{remaining}/{buy_qty}｜買入單價：NT$ {money(unit)}｜剩餘成本：NT$ {money(unit * remaining)}\n"
            f"備註：{card.get('note', '')}"
        )
        load_image_preview(self.inventory_image_preview, str(card.get("image_path", "")))

    def edit_selected_card(self) -> None:
        card_id = self.selected_inventory_card_id()
        card = self.get_card(card_id) if card_id else None
        if not card:
            QMessageBox.warning(self, "無法修改", "請先在庫存列表選擇一筆庫存。")
            return

        dialog = InventoryEditDialog(card, self.categories(), self.buy_methods(), self)
        if dialog.exec() != QDialog.Accepted:
            return

        values = dialog.values()
        old_name = str(card.get("name", ""))

        if dialog.clear_image_requested:
            values["image_path"] = ""
        elif dialog.selected_new_image_path:
            try:
                values["image_path"] = copy_image_to_library(dialog.selected_new_image_path)
            except Exception as exc:
                QMessageBox.warning(self, "圖片複製失敗", f"圖片無法複製到資料夾：\n{exc}")
                return

        card.update(values)
        card["updated_at"] = now_text()

        self.recalculate_sales_for_card(card)
        save_db(self.db)
        self.refresh_all()
        self.statusBar().showMessage(f"已修改庫存：{old_name}", 5000)
        QMessageBox.information(self, "完成", "庫存內容已修改。")

    def recalculate_sales_for_card(self, card: dict[str, Any]) -> None:
        card_id = str(card.get("id", ""))
        if not card_id:
            return

        for sale in self.db.get("sales", []):
            if str(sale.get("card_id", "")) != card_id:
                continue

            qty = int(sale.get("quantity", 0) or 0)
            sell_total = float(sale.get("sell_total", 0) or 0)
            fee_total = float(sale.get("fee_total", 0) or 0)
            buy_cost, profit, roi = sale_profit(card, qty, sell_total, fee_total)

            sale["name"] = card.get("name", "")
            sale["category"] = card.get("category", "")
            sale["psa_enabled"] = bool(card.get("psa_enabled", False))
            sale["psa_score"] = str(card.get("psa_score", "")).strip()
            sale["bgs_enabled"] = bool(card.get("bgs_enabled", False))
            sale["bgs_score"] = str(card.get("bgs_score", "")).strip()
            sale["buy_cost_total"] = buy_cost
            sale["profit"] = profit
            sale["roi"] = roi
            sale["updated_at"] = now_text()

    def delete_selected_card(self) -> None:
        card_id = self.selected_inventory_card_id()
        card = self.get_card(card_id) if card_id else None
        if not card:
            QMessageBox.warning(self, "無法刪除", "請先選擇一筆庫存。")
            return

        related_sales = [sale for sale in self.db["sales"] if sale.get("card_id") == card_id]
        warning = ""
        if related_sales:
            warning = f"\n\n注意：這筆庫存已有 {len(related_sales)} 筆賣出紀錄。刪除庫存不會刪除既有賣出紀錄，但報表仍會保留賣出歷史。"

        if QMessageBox.question(
            self,
            "確認刪除",
            f"確定要刪除庫存批次？\n\n{card.get('name', '')}{warning}",
        ) != QMessageBox.Yes:
            return

        self.db["cards"] = [c for c in self.db["cards"] if c.get("id") != card_id]
        save_db(self.db)
        self.refresh_all()
        self.statusBar().showMessage("庫存批次已刪除", 5000)

    def refresh_sell_combo(self) -> None:
        current_card_id = self.sell_card_combo.currentData() if hasattr(self, "sell_card_combo") else None
        category_filter = self.sell_category_filter.currentText() if hasattr(self, "sell_category_filter") else "全部分類"
        search = self.sell_search_edit.text().strip().lower() if hasattr(self, "sell_search_edit") else ""

        self.sell_card_combo.blockSignals(True)
        self.sell_card_combo.clear()

        stock_cards = []
        for card in self.db["cards"]:
            if int(card.get("remaining_quantity", 0) or 0) <= 0:
                continue
            if category_filter != "全部分類" and card.get("category") != category_filter:
                continue

            haystack = " ".join([
                str(card.get("name", "")),
                str(card.get("category", "")),
                card_grade_text(card),
                str(card.get("buy_method", "")),
                str(card.get("note", "")),
            ]).lower()
            if search and search not in haystack:
                continue

            stock_cards.append(card)

        for card in stock_cards:
            label = (
                f"{card.get('name', '')}｜{card.get('category', '')}｜{card_grade_text(card)}｜"
                f"庫存 {card.get('remaining_quantity', 0)}｜單價 NT$ {money(card_unit_cost(card))}"
            )
            self.sell_card_combo.addItem(label, card.get("id"))

        if current_card_id:
            idx = self.sell_card_combo.findData(current_card_id)
            if idx >= 0:
                self.sell_card_combo.setCurrentIndex(idx)

        self.sell_card_combo.blockSignals(False)
        self.on_sell_card_changed()

    def current_sell_card(self) -> dict[str, Any] | None:
        card_id = self.sell_card_combo.currentData()
        return self.get_card(str(card_id)) if card_id else None

    def on_sell_card_changed(self) -> None:
        card = self.current_sell_card()
        if not card:
            self.sell_info_label.setText("目前沒有符合分類/搜尋條件的可賣出庫存。")
            self.sell_quantity_spin.setRange(1, 1)
            self.sell_quantity_spin.setEnabled(False)
            self.sell_total_spin.setEnabled(False)
            self.sell_fee_spin.setEnabled(False)
            self.sell_submit_btn.setEnabled(False)
            load_image_preview(self.sell_image_preview, "")
            self.update_sell_estimate()
            return

        remaining = int(card.get("remaining_quantity", 0) or 0)
        self.sell_quantity_spin.setEnabled(True)
        self.sell_total_spin.setEnabled(True)
        self.sell_fee_spin.setEnabled(True)
        self.sell_submit_btn.setEnabled(True)
        self.sell_quantity_spin.setRange(1, max(1, remaining))
        self.sell_quantity_spin.setValue(1)
        self.sell_info_label.setText(
            f"分類：{card.get('category', '')}\n"
            f"鑑定標籤：{card_grade_text(card)}\n"
            f"剩餘庫存：{remaining}\n"
            f"買入單價：NT$ {money(card_unit_cost(card))}\n"
            f"買入方式：{card.get('buy_method', '')}"
        )
        load_image_preview(self.sell_image_preview, str(card.get("image_path", "")))
        self.update_sell_estimate()

    def update_sell_estimate(self) -> None:
        card = self.current_sell_card()
        if not card:
            self.sell_estimate_label.setText("收益預估：-")
            return
        qty = int(self.sell_quantity_spin.value())
        sell_total = float(self.sell_total_spin.value())
        fee_total = float(self.sell_fee_spin.value())
        buy_cost, profit, roi = sale_profit(card, qty, sell_total, fee_total)
        self.sell_estimate_label.setText(
            f"收益預估：賣出 NT$ {money(sell_total)} - 成本 NT$ {money(buy_cost)} - 費用 NT$ {money(fee_total)} "
            f"= NT$ {money(profit)}｜ROI {percent(roi)}"
        )
        if profit >= 0:
            self.sell_estimate_label.setStyleSheet("font-weight: bold; font-size: 16px; color: #0a7a24;")
        else:
            self.sell_estimate_label.setStyleSheet("font-weight: bold; font-size: 16px; color: #b00020;")

    def sell_selected_inventory(self) -> None:
        card = self.current_sell_card()
        if not card:
            QMessageBox.warning(self, "無法賣出", "目前沒有可賣出的庫存。")
            return

        qty = int(self.sell_quantity_spin.value())
        remaining = int(card.get("remaining_quantity", 0) or 0)
        if qty <= 0 or qty > remaining:
            QMessageBox.warning(self, "無法賣出", "賣出數量不可大於剩餘庫存。")
            return

        sell_total = float(self.sell_total_spin.value())
        fee_total = float(self.sell_fee_spin.value())
        buy_cost, profit, roi = sale_profit(card, qty, sell_total, fee_total)

        if QMessageBox.question(
            self,
            "確認賣出",
            f"卡片：{card.get('name', '')}\n"
            f"數量：{qty}\n"
            f"賣出總金額：NT$ {money(sell_total)}\n"
            f"成本：NT$ {money(buy_cost)}\n"
            f"費用：NT$ {money(fee_total)}\n"
            f"收益：NT$ {money(profit)}\n"
            f"ROI：{percent(roi)}\n\n確定要扣庫存？",
        ) != QMessageBox.Yes:
            return

        card["remaining_quantity"] = remaining - qty
        card["updated_at"] = now_text()
        sale = {
            "id": uuid.uuid4().hex,
            "card_id": card.get("id"),
            "name": card.get("name", ""),
            "category": card.get("category", ""),
            "psa_enabled": bool(card.get("psa_enabled", False)) or str(card.get("grade_company", "無")) == "PSA",
            "psa_score": str(card.get("psa_score", card.get("grade_score", "") if str(card.get("grade_company", "無")) == "PSA" else "")).strip(),
            "bgs_enabled": bool(card.get("bgs_enabled", False)) or str(card.get("grade_company", "無")) == "BGS",
            "bgs_score": str(card.get("bgs_score", card.get("grade_score", "") if str(card.get("grade_company", "無")) == "BGS" else "")).strip(),
            "quantity": qty,
            "sell_total": sell_total,
            "fee_total": fee_total,
            "buy_cost_total": buy_cost,
            "profit": profit,
            "roi": roi,
            "note": self.sell_note_edit.toPlainText().strip(),
            "sold_at": now_text(),
        }
        self.db["sales"].append(sale)
        save_db(self.db)

        self.sell_total_spin.setValue(0)
        self.sell_fee_spin.setValue(0)
        self.sell_note_edit.clear()

        self.refresh_all()
        self.statusBar().showMessage(f"已賣出：{sale['name']} x {qty}，收益 NT$ {money(profit)}", 5000)
        QMessageBox.information(self, "完成", f"已扣庫存。\n本次收益：NT$ {money(profit)}\nROI：{percent(roi)}")

    def ask_csv_path(self, default_name: str) -> str:
        file_path, _ = QFileDialog.getSaveFileName(
            self,
            "匯出 CSV",
            str(BASE_DIR / default_name),
            "CSV 檔案 (*.csv);;所有檔案 (*.*)",
        )
        if not file_path:
            return ""
        if not file_path.lower().endswith(".csv"):
            file_path += ".csv"
        return file_path

    def write_csv(self, file_path: str, headers: list[str], rows: list[list[Any]]) -> None:
        with open(file_path, "w", encoding="utf-8-sig", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(headers)
            writer.writerows(rows)

    def inventory_csv_rows(self) -> tuple[list[str], list[list[Any]]]:
        headers = [
            "id",
            "卡片名稱",
            "分類",
            "鑑定標籤",
            "PSA",
            "PSA分數",
            "BGS",
            "BGS分數",
            "剩餘庫存",
            "原始數量",
            "買入單價",
            "買入總金額",
            "買入方式",
            "圖片路徑",
            "建立時間",
            "更新時間",
            "備註",
        ]
        rows = []
        for card in self.db.get("cards", []):
            rows.append([
                card.get("id", ""),
                card.get("name", ""),
                card.get("category", ""),
                card_grade_text(card),
                "Y" if bool(card.get("psa_enabled", False)) else "",
                card.get("psa_score", ""),
                "Y" if bool(card.get("bgs_enabled", False)) else "",
                card.get("bgs_score", ""),
                int(card.get("remaining_quantity", 0) or 0),
                int(card.get("buy_quantity", 0) or 0),
                card_unit_cost(card),
                float(card.get("buy_total", 0) or 0),
                card.get("buy_method", ""),
                card.get("image_path", ""),
                card.get("created_at", ""),
                card.get("updated_at", ""),
                card.get("note", ""),
            ])
        return headers, rows

    def sales_csv_rows(self) -> tuple[list[str], list[list[Any]]]:
        headers = [
            "id",
            "card_id",
            "賣出時間",
            "卡片名稱",
            "分類",
            "鑑定標籤",
            "PSA",
            "PSA分數",
            "BGS",
            "BGS分數",
            "賣出數量",
            "賣出總額",
            "買入成本",
            "費用",
            "收益",
            "ROI",
            "更新時間",
            "備註",
        ]
        rows = []
        for sale in self.db.get("sales", []):
            rows.append([
                sale.get("id", ""),
                sale.get("card_id", ""),
                sale.get("sold_at", ""),
                sale.get("name", ""),
                sale.get("category", ""),
                card_grade_text(sale),
                "Y" if bool(sale.get("psa_enabled", False)) else "",
                sale.get("psa_score", ""),
                "Y" if bool(sale.get("bgs_enabled", False)) else "",
                sale.get("bgs_score", ""),
                int(sale.get("quantity", 0) or 0),
                float(sale.get("sell_total", 0) or 0),
                float(sale.get("buy_cost_total", 0) or 0),
                float(sale.get("fee_total", 0) or 0),
                float(sale.get("profit", 0) or 0),
                float(sale.get("roi", 0) or 0),
                sale.get("updated_at", ""),
                sale.get("note", ""),
            ])
        return headers, rows

    def mtg_inventory_csv_rows(self, records: list[dict[str, Any]] | None = None) -> tuple[list[str], list[list[Any]]]:
        headers = [
            "id",
            "source",
            "數量",
            "Card name",
            "English name",
            "Printed name",
            "Edition",
            "Set Code",
            "Rarity",
            "Collector #",
            "Type",
            "Oracle Type",
            "Color",
            "Language",
            "Language Code",
            "Prices",
            "Card Text",
            "Legalities",
            "Released At",
            "Layout",
            "Scryfall ID",
            "Scryfall URL",
            "Image URL",
            "Source URL",
            "露天同步",
            "露天商品ID",
            "露天規格ID",
            "露天自用料號",
            "露天標題",
            "露天售價",
            "露天狀態",
            "露天遠端庫存",
            "露天最後同步",
            "露天最後訂單",
            "露天最後錯誤",
            "建立時間",
            "更新時間",
            "備註",
        ]
        if records is None:
            records = list(self.db.get("mtg_inventory", []))

        rows = []
        for record in records:
            rows.append([
                record.get("id", ""),
                record.get("source", ""),
                int(record.get("quantity", 0) or 0),
                record.get("name", ""),
                record.get("english_name", ""),
                record.get("printed_name", ""),
                record.get("edition", ""),
                record.get("set_code", ""),
                record.get("rarity", ""),
                record.get("collector", ""),
                record.get("type", ""),
                record.get("oracle_type", ""),
                record.get("colors", ""),
                record.get("lang_label", record.get("lang", "")),
                record.get("lang", ""),
                record.get("price", ""),
                record.get("text", ""),
                record.get("legalities", ""),
                record.get("released_at", ""),
                record.get("layout", ""),
                record.get("scryfall_id", ""),
                record.get("url", ""),
                record.get("image_url", ""),
                record.get("source_url", ""),
                "Y" if bool(ensure_ruten_item_fields(record).get("enabled", True)) else "N",
                ensure_ruten_item_fields(record).get("item_id", ""),
                ensure_ruten_item_fields(record).get("spec_id", ""),
                ensure_ruten_item_fields(record).get("custom_no", ""),
                ensure_ruten_item_fields(record).get("title", ""),
                ensure_ruten_item_fields(record).get("price", ""),
                ensure_ruten_item_fields(record).get("status", ""),
                ensure_ruten_item_fields(record).get("remote_stock", ""),
                ensure_ruten_item_fields(record).get("last_sync_at", ""),
                ensure_ruten_item_fields(record).get("last_order_at", ""),
                ensure_ruten_item_fields(record).get("last_error", ""),
                record.get("created_at", ""),
                record.get("updated_at", ""),
                record.get("note", ""),
            ])
        return headers, rows

    def export_inventory_csv(self) -> None:
        default_name = f"card_inventory_stock_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
        file_path = self.ask_csv_path(default_name)
        if not file_path:
            return

        try:
            headers, rows = self.inventory_csv_rows()
            self.write_csv(file_path, headers, rows)
        except Exception as exc:
            QMessageBox.warning(self, "匯出失敗", f"庫存 CSV 無法匯出：\n{exc}")
            return

        self.statusBar().showMessage(f"已匯出庫存 CSV：{file_path}", 5000)
        QMessageBox.information(self, "完成", f"已匯出庫存 CSV：\n{file_path}")

    def export_mtg_inventory_csv(self) -> None:
        default_name = f"mtg_inventory_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
        file_path = self.ask_csv_path(default_name)
        if not file_path:
            return

        try:
            records = self.current_mtg_inventory_records() if hasattr(self, "mtg_inventory_table") else list(self.db.get("mtg_inventory", []))
            headers, rows = self.mtg_inventory_csv_rows(records)
            self.write_csv(file_path, headers, rows)
        except Exception as exc:
            QMessageBox.warning(self, "匯出失敗", f"MTG 庫存 CSV 無法匯出：\n{exc}")
            return

        self.statusBar().showMessage(f"已匯出 MTG 庫存 CSV：{file_path}", 5000)
        QMessageBox.information(self, "完成", f"已匯出 MTG 庫存 CSV：\n{file_path}\n\n匯出筆數：{len(rows)}")

    def export_sales_csv(self) -> None:
        default_name = f"card_inventory_sales_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
        file_path = self.ask_csv_path(default_name)
        if not file_path:
            return

        try:
            headers, rows = self.sales_csv_rows()
            self.write_csv(file_path, headers, rows)
        except Exception as exc:
            QMessageBox.warning(self, "匯出失敗", f"賣出紀錄 CSV 無法匯出：\n{exc}")
            return

        self.statusBar().showMessage(f"已匯出賣出紀錄 CSV：{file_path}", 5000)
        QMessageBox.information(self, "完成", f"已匯出賣出紀錄 CSV：\n{file_path}")

    def export_all_csv(self) -> None:
        default_name = f"card_inventory_all_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
        file_path = self.ask_csv_path(default_name)
        if not file_path:
            return

        try:
            inventory_headers, inventory_rows = self.inventory_csv_rows()
            mtg_headers, mtg_rows = self.mtg_inventory_csv_rows()
            sales_headers, sales_rows = self.sales_csv_rows()
            with open(file_path, "w", encoding="utf-8-sig", newline="") as f:
                writer = csv.writer(f)
                writer.writerow(["庫存列表"])
                writer.writerow(inventory_headers)
                writer.writerows(inventory_rows)
                writer.writerow([])
                writer.writerow(["MTG庫存"])
                writer.writerow(mtg_headers)
                writer.writerows(mtg_rows)
                writer.writerow([])
                writer.writerow(["賣出紀錄"])
                writer.writerow(sales_headers)
                writer.writerows(sales_rows)
        except Exception as exc:
            QMessageBox.warning(self, "匯出失敗", f"完整資料 CSV 無法匯出：\n{exc}")
            return

        self.statusBar().showMessage(f"已匯出完整資料 CSV：{file_path}", 5000)
        QMessageBox.information(self, "完成", f"已匯出完整資料 CSV：\n{file_path}")

    def refresh_reports(self) -> None:
        cards = self.db["cards"]
        sales = self.db["sales"]

        inventory_qty = sum(int(card.get("remaining_quantity", 0) or 0) for card in cards)
        inventory_cost = sum(card_unit_cost(card) * int(card.get("remaining_quantity", 0) or 0) for card in cards)
        sales_revenue = sum(float(sale.get("sell_total", 0) or 0) for sale in sales)
        sales_cost = sum(float(sale.get("buy_cost_total", 0) or 0) for sale in sales)
        sales_fee = sum(float(sale.get("fee_total", 0) or 0) for sale in sales)
        sales_profit = sum(float(sale.get("profit", 0) or 0) for sale in sales)
        sales_roi = (sales_profit / sales_cost * 100.0) if sales_cost > 0 else 0.0

        self.summary_inventory_qty.setText(str(inventory_qty))
        self.summary_inventory_cost.setText(f"NT$ {money(inventory_cost)}")
        self.summary_sales_revenue.setText(f"NT$ {money(sales_revenue)}")
        self.summary_sales_cost.setText(f"NT$ {money(sales_cost)}")
        self.summary_sales_fee.setText(f"NT$ {money(sales_fee)}")
        self.summary_profit.setText(f"NT$ {money(sales_profit)}")
        self.summary_roi.setText(percent(sales_roi))

        if sales_profit >= 0:
            self.summary_profit.setStyleSheet("color: #0a7a24; font-weight: bold;")
        else:
            self.summary_profit.setStyleSheet("color: #b00020; font-weight: bold;")

        self.sales_table.setRowCount(0)
        for row, sale in enumerate(reversed(sales)):
            self.sales_table.insertRow(row)
            item_no = QTableWidgetItem(str(row + 1))
            item_no.setData(Qt.UserRole, sale.get("id"))
            self.sales_table.setItem(row, 0, item_no)
            self.sales_table.setItem(row, 1, QTableWidgetItem(str(sale.get("sold_at", ""))))
            self.sales_table.setItem(row, 2, QTableWidgetItem(str(sale.get("name", ""))))
            self.sales_table.setItem(row, 3, QTableWidgetItem(str(sale.get("category", ""))))
            self.sales_table.setItem(row, 4, QTableWidgetItem(card_grade_text(sale)))
            self.sales_table.setItem(row, 5, QTableWidgetItem(str(sale.get("quantity", 0))))
            self.sales_table.setItem(row, 6, QTableWidgetItem(f"NT$ {money(sale.get('sell_total', 0))}"))
            self.sales_table.setItem(row, 7, QTableWidgetItem(f"NT$ {money(sale.get('buy_cost_total', 0))}"))
            self.sales_table.setItem(row, 8, QTableWidgetItem(f"NT$ {money(sale.get('fee_total', 0))}"))
            self.sales_table.setItem(row, 9, QTableWidgetItem(f"NT$ {money(sale.get('profit', 0))}"))
            self.sales_table.setItem(row, 10, QTableWidgetItem(percent(float(sale.get("roi", 0) or 0))))


    def selected_sale_id(self) -> str:
        row = self.sales_table.currentRow()
        if row < 0:
            return ""
        item = self.sales_table.item(row, 0)
        return str(item.data(Qt.UserRole)) if item else ""

    def delete_selected_sale(self) -> None:
        sale_id = self.selected_sale_id()
        if not sale_id:
            QMessageBox.warning(self, "無法刪除", "請先選擇一筆賣出紀錄。")
            return

        sale = next((s for s in self.db["sales"] if s.get("id") == sale_id), None)
        if not sale:
            QMessageBox.warning(self, "無法刪除", "找不到這筆賣出紀錄。")
            return

        if QMessageBox.question(
            self,
            "確認刪除",
            f"刪除賣出紀錄後會回補庫存。\n\n卡片：{sale.get('name', '')}\n數量：{sale.get('quantity', 0)}\n確定刪除？",
        ) != QMessageBox.Yes:
            return

        card = self.get_card(str(sale.get("card_id", "")))
        if card:
            card["remaining_quantity"] = int(card.get("remaining_quantity", 0) or 0) + int(sale.get("quantity", 0) or 0)
            card["updated_at"] = now_text()

        self.db["sales"] = [s for s in self.db["sales"] if s.get("id") != sale_id]
        save_db(self.db)
        self.refresh_all()
        self.statusBar().showMessage("賣出紀錄已刪除並回補庫存", 5000)


def main() -> None:
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    window = MainWindow()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
