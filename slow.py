# slow.py
import os
import re
import sys
import json
import time
import uuid
import asyncio
import tempfile
import sqlite3
import unicodedata
from dataclasses import dataclass
from typing import Optional, Tuple, Dict, Tuple as Tup, List

from datetime import timezone

from dotenv import dotenv_values

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, CallbackQueryHandler, MessageHandler,
    ContextTypes, filters
)

from telethon import TelegramClient
from telethon.errors import (
    UserAlreadyParticipantError,
    InviteHashExpiredError,
    InviteHashInvalidError,
)
from telethon.tl.functions.messages import CheckChatInviteRequest, ImportChatInviteRequest

from telethon.sessions import StringSession


# ---------- Ajuste Windows (buena práctica para asyncio)
if sys.platform.startswith("win"):
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# ---------- Cargar .env y validar
ENV = {**os.environ, **dotenv_values(".env")}
BOT_TOKEN = ENV.get("BOT_TOKEN")
ADMIN_ID = int(ENV.get("ADMIN_ID", "0"))

API_ID = int(ENV.get("API_ID", "0"))
API_HASH = ENV.get("API_HASH")
PHONE_NUMBER = ENV.get("PHONE_NUMBER")

# Canal 1 (obligatorio alguno)
SOURCE_CHAT_1 = (ENV.get("SOURCE_CHAT_1") or "").strip()
SOURCE_INVITE_LINK_1 = (ENV.get("SOURCE_INVITE_LINK_1") or "").strip()
# Canal 2 (opcional)
SOURCE_CHAT_2 = (ENV.get("SOURCE_CHAT_2") or "").strip()
SOURCE_INVITE_LINK_2 = (ENV.get("SOURCE_INVITE_LINK_2") or "").strip()

CONCURRENCY_LIMIT = int(ENV.get("CONCURRENCY_LIMIT", "5"))

if not BOT_TOKEN or not ADMIN_ID or not API_ID or not API_HASH or not PHONE_NUMBER:
    raise RuntimeError("Revisa .env: faltan BOT_TOKEN, ADMIN_ID, API_ID, API_HASH o PHONE_NUMBER.")

# ---------- Persistencia simple para auth/keys
STORE_PATH = "auth_store.json"
store_lock = asyncio.Lock()

def now_ts() -> int:
    return int(time.time())

def load_store() -> dict:
    if not os.path.exists(STORE_PATH):
        return {"users": {}, "keys": {}}
    try:
        with open(STORE_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {"users": {}, "keys": {}}

def save_store(data: dict):
    tmp = STORE_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.replace(tmp, STORE_PATH)

store = load_store()

def is_admin(user_id: int) -> bool:
    return user_id == ADMIN_ID

def user_status(user_id: int) -> Tuple[bool, str]:
    u = store["users"].get(str(user_id))
    if not u:
        return False, "No autorizado. Usa /redeem <KEY> o el botón para canjear."
    if u["expires_at"] and now_ts() > u["expires_at"]:
        return False, "Tu acceso expiró."
    if u["remaining"] <= 0:
        return False, "Sin usos disponibles."
    exp = time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime(u["expires_at"])) if u["expires_at"] else "sin fecha"
    return True, f"OK (usos restantes: {u['remaining']}, expira: {exp})"

async def grant_user(user_id: int, days: int, runs: int):
    uid = str(user_id)
    cur = store["users"].get(uid)
    extra_seconds = days * 86400 if days > 0 else 0
    if cur:
        base = max(cur.get("expires_at", 0) or 0, now_ts())
        new_exp = base + extra_seconds if days > 0 else cur.get("expires_at", 0)
        cur["expires_at"] = new_exp
        cur["remaining"] = cur.get("remaining", 0) + runs
        store["users"][uid] = cur
    else:
        exp = now_ts() + extra_seconds if days > 0 else 0
        store["users"][uid] = {"expires_at": exp, "remaining": runs}
    save_store(store)

def cleanup_expired():
    now = now_ts()
    to_del_u = []
    for uid, u in store["users"].items():
        if u["expires_at"] and now > u["expires_at"]:
            to_del_u.append(uid)
    for uid in to_del_u:
        del store["users"][uid]

    to_del_k = []
    for k, v in store["keys"].items():
        if (v.get("key_expires_at") and now > v["key_expires_at"]) or v.get("uses_left", 0) <= 0:
            to_del_k.append(k)
    for k in to_del_k:
        del store["keys"][k]
    save_store(store)

def gen_key(days: int, runs: int, uses: int, keydays: int) -> str:
    key = uuid.uuid4().hex[:8] + "-" + uuid.uuid4().hex[:8]
    key_exp = now_ts() + keydays * 86400 if keydays > 0 else 0
    store["keys"][key] = {
        "grant_days": days,
        "grant_runs": runs,
        "uses_left": uses,
        "key_expires_at": key_exp
    }
    save_store(store)
    return key

async def redeem_key_async(key: str, user_id: int) -> Tuple[bool, str]:
    async with store_lock:
        cleanup_expired()
        v = store["keys"].get(key)
        if not v:
            return False, "Key inválida o agotada."
        if v.get("key_expires_at") and now_ts() > v["key_expires_at"]:
            return False, "Key expirada."
        if v.get("uses_left", 0) <= 0:
            return False, "Key sin usos."
        days = int(v.get("grant_days", 0))
        runs = int(v.get("grant_runs", 0))
        await grant_user(user_id, days, runs)
        v["uses_left"] -= 1
        save_store(store)
        return True, f"Acceso activado: +{runs} usos; +{days} días."

def consume_usage_on_success(user_id: int):
    uid = str(user_id)
    u = store["users"].get(uid)
    if not u:
        return
    if u["remaining"] > 0:
        u["remaining"] -= 1
        save_store(store)

# ---------- Telethon (MTProto) y canales
telethon_client: Optional[TelegramClient] = None
SOURCE_IDS: Dict[int, Optional[int]] = {1: None, 2: None}
SOURCE_NAMES: Dict[int, str] = {1: "", 2: ""}

INVITE_HASH_RE = re.compile(r"(?:t\.me/|https?://t\.me/)(?:\+|joinchat/)?([A-Za-z0-9_-]{16,})")

def extract_invite_hash(link: str) -> str:
    m = INVITE_HASH_RE.search(link)
    if not m:
        return link.split("+")[-1].split("/")[-1]
    return m.group(1)

async def ensure_join_and_get_source_id(client: TelegramClient, invite_link: str) -> int:
    invite_hash = extract_invite_hash(invite_link)
    info = await client(CheckChatInviteRequest(invite_hash))
    if hasattr(info, "chat"):
        return info.chat.id
    try:
        upd = await client(ImportChatInviteRequest(invite_hash))
        if getattr(upd, "chats", None):
            return upd.chats[0].id
        entity = await client.get_entity(invite_link)
        return entity.id
    except UserAlreadyParticipantError:
        entity = await client.get_entity(invite_link)
        return entity.id
    except (InviteHashExpiredError, InviteHashInvalidError):
        raise RuntimeError("El enlace de invitación está expirado o es inválido.")

async def resolve_env_source_id(client: TelegramClient, uname: str, invite: str) -> Optional[int]:
    uname = (uname or "").strip()
    invite = (invite or "").strip()
    if invite:
        return await ensure_join_and_get_source_id(client, invite)
    if uname:
        entity = await client.get_entity(uname)
        return entity.id
    return None

async def resolve_sources(client: TelegramClient):
    sid1 = await resolve_env_source_id(client, SOURCE_CHAT_1, SOURCE_INVITE_LINK_1)
    if not sid1:
        raise RuntimeError("Configura SOURCE_CHAT_1 o SOURCE_INVITE_LINK_1 en .env para el Canal 1.")
    SOURCE_IDS[1] = sid1
    ent1 = await client.get_entity(sid1)
    SOURCE_NAMES[1] = getattr(ent1, "title", None) or getattr(ent1, "username", None) or str(sid1)

    try:
        sid2 = await resolve_env_source_id(client, SOURCE_CHAT_2, SOURCE_INVITE_LINK_2)
    except Exception:
        sid2 = None
    if sid2:
        SOURCE_IDS[2] = sid2
        ent2 = await client.get_entity(sid2)
        SOURCE_NAMES[2] = getattr(ent2, "title", None) or getattr(ent2, "username", None) or str(sid2)
    else:
        SOURCE_IDS[2] = None
        SOURCE_NAMES[2] = "(no configurado)"

def selected_source_id(cfg) -> int:
    sid = SOURCE_IDS.get(cfg.source_idx)
    if sid:
        return sid
    other = 2 if cfg.source_idx == 1 else 1
    sid2 = SOURCE_IDS.get(other)
    if sid2:
        return sid2
    raise RuntimeError("No hay canales configurados correctamente.")

# ---------- SQLite (Base de Datos)
DB_PATH = "messages.db"

def db_init():
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS messages (
            channel INTEGER,
            msg_id  INTEGER,
            date    INTEGER,
            text    TEXT,
            norm    TEXT,
            PRIMARY KEY (channel, msg_id)
        )
    """)
    cur.execute("CREATE INDEX IF NOT EXISTS idx_messages_channel_date ON messages(channel, date)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_messages_channel_norm ON messages(channel, norm)")
    con.commit()
    con.close()

def _normalize_no_accents(s: str) -> str:
    if not s:
        return ""
    s = unicodedata.normalize("NFD", s)
    s = "".join(ch for ch in s if unicodedata.category(ch) != "Mn")
    return s

def _normalize_for_index(s: str) -> str:
    return _normalize_no_accents(s or "").lower()

async def reindex_channel(channel_idx: int, progress_chat_id: int, context) -> Tuple[int, int]:
    """
    Extrae mensajes del canal (channel_idx=1/2) y los guarda/actualiza en DB.
    Retorna (insertados_o_actualizados, último_id_base).
    """
    global telethon_client
    src_id = selected_source_id(ExtractConfig(source_idx=channel_idx))

    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    cur.execute("SELECT COALESCE(MAX(msg_id), 0) FROM messages WHERE channel=?", (channel_idx,))
    last_id = cur.fetchone()[0] or 0

    batch = 0
    total = 0
    t0 = time.time()

    kwargs = {}
    if last_id > 0:
        kwargs["min_id"] = last_id  # solo nuevos

    await context.bot.send_message(progress_chat_id, f"🧩 Reindexando canal {channel_idx}… (desde id>{last_id})")

    async for msg in telethon_client.iter_messages(src_id, reverse=True, **kwargs):
        text = (msg.message or "").strip()
        if not text:
            continue
        norm = _normalize_for_index(text)
        # msg.date ya es aware para Telethon; normalizamos a UTC epoch
        date_ts = int(msg.date.replace(tzinfo=timezone.utc).timestamp())
        cur.execute(
            "INSERT OR REPLACE INTO messages(channel, msg_id, date, text, norm) VALUES(?,?,?,?,?)",
            (channel_idx, msg.id, date_ts, text, norm)
        )
        batch += 1
        total += 1
        if batch >= 1000:
            con.commit()
            batch = 0
            if total % 5000 == 0:
                await context.bot.send_message(progress_chat_id, f"… {total} guardados (canal {channel_idx}).")

    if batch:
        con.commit()
    con.close()
    dt = time.time() - t0
    await context.bot.send_message(progress_chat_id, f"✅ Reindexación canal {channel_idx} lista: {total} mensajes en {dt:.1f}s.")
    return total, last_id

async def reindex_both(progress_chat_id: int, context):
    done = []
    for idx in (1, 2):
        if SOURCE_IDS.get(idx):
            try:
                t, _ = await reindex_channel(idx, progress_chat_id, context)
                done.append((idx, t))
            except Exception as e:
                await context.bot.send_message(progress_chat_id, f"⚠️ Error reindexando canal {idx}: {e}")
    if not done:
        await context.bot.send_message(progress_chat_id, "ℹ️ No hay canales configurados para reindexar.")

def _db_select_texts(cfg, max_fetch: int = 100000) -> List[str]:
    """
    Selecciona candidatos desde SQLite, respetando canal y orden.
    Si es literal: usa LIKE sobre 'norm'. Si es regex: full-scan ordenado (luego filtra Python).
    """
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    order_sql = "ASC" if cfg.order == "antiguos" else "DESC"

    texts: List[str] = []
    try:
        if not cfg.is_regex:
            needle = _normalize_for_index(cfg.pattern_text)
            over_limit = min(cfg.limit * 50, max_fetch)
            cur.execute(
                f"SELECT text FROM messages WHERE channel=? AND norm LIKE ? ORDER BY date {order_sql} LIMIT ?",
                (cfg.source_idx, f"%{needle}%", over_limit)
            )
            rows = cur.fetchall()
            texts = [r[0] for r in rows]
        else:
            cur.execute(
                f"SELECT text FROM messages WHERE channel=? ORDER BY date {order_sql} LIMIT ?",
                (cfg.source_idx, max_fetch)
            )
            rows = cur.fetchall()
            texts = [r[0] for r in rows]
    finally:
        con.close()
    return texts

# ---------- Extracción (métodos)
@dataclass
class ExtractConfig:
    pattern_text: str = "CC:"
    is_regex: bool = False
    case_ins: bool = True
    dot_all: bool = False
    scope: str = "nums_line"       # "mensaje"|"match"|"group1"|"query_line"|"nums_line"
    order: str = "recientes"       # "recientes"|"antiguos"
    limit: int = 100
    anonymize_digits: bool = False
    max_scan: int = 2000
    max_seconds: int = 30
    source_idx: int = 1
    idcc_only: bool = True
    numbers_only: bool = False     # NUEVO: devolver solo números y signos (se usa con IDCC)
    use_db: bool = False           # NUEVO: modo BD

SCOPES = ["mensaje", "match", "group1", "query_line", "nums_line"]

def build_regex_from_text(text: str, literal: bool, case_ins: bool, dot_all: bool) -> re.Pattern:
    """
    Si literal=True -> re.escape(text).
    Si literal=False (regex) pero el patrón es inválido, fallback a literal automáticamente.
    """
    pattern = (text or "").strip()
    flags = 0
    if case_ins:
        flags |= re.IGNORECASE
    if dot_all:
        flags |= re.DOTALL

    if literal or pattern == "":
        return re.compile(re.escape(pattern), flags)

    try:
        return re.compile(pattern, flags)
    except re.error:
        return re.compile(re.escape(pattern), flags)

def build_regex(cfg: ExtractConfig) -> re.Pattern:
    return build_regex_from_text(cfg.pattern_text, literal=not cfg.is_regex, case_ins=cfg.case_ins, dot_all=cfg.dot_all)

def first_line_with_match(text: str, m: re.Match) -> str:
    s = text.replace("\r\n", "\n").replace("\r", "\n")
    start = m.start()
    prev = s.rfind("\n", 0, start)
    nxt = s.find("\n", start)
    a = 0 if prev == -1 else prev + 1
    b = len(s) if nxt == -1 else nxt
    return s[a:b].strip()

def third_line(text: str) -> Optional[str]:
    s = text.replace("\r\n", "\n").replace("\r", "\n")
    lines = s.split("\n")
    if len(lines) >= 3:
        t = lines[2].strip()
        return t if t else None
    return None

def only_numbers_and_signs(s: str) -> str:
    # Quita letras (incluidos acentos) y espacios; deja dígitos y signos/puntuación
    return re.sub(r"[➤⚜️:A-Za-zÁÉÍÓÚÜÑáéíóúüñ\s]", "", s)

def maybe_anonymize(s: str, on: bool) -> str:
    if not on or not s:
        return s
    return re.sub(r"\d", "x", s)

def extract_idcc_line(text: str, numbers_only: bool = False) -> Optional[str]:
    """
    Devuelve SOLO el valor después de '(ID )?CC[:|-|—]' en esa línea.
    No usa grupos para evitar 'no such group'.
    """
    s = text.replace("\r\n", "\n").replace("\r", "\n")
    detect = re.compile(r'(?:ID\s*)?CC\s*[:\-—]', re.IGNORECASE)
    strip_prefix = re.compile(r'^.*?(?:ID\s*)?CC\s*[:\-—]\s*', re.IGNORECASE)

    for ln in s.split("\n"):
        if detect.search(ln):
            val = strip_prefix.sub('', ln).strip()
            if not val:
                return None
            if numbers_only:
                val = only_numbers_and_signs(val)
            return val
    return None

def extract_content_normal(text: str, rx: re.Pattern, cfg: ExtractConfig) -> Optional[str]:
    m = rx.search(text)
    if not m:
        return None
    if cfg.idcc_only:
        return extract_idcc_line(text, numbers_only=cfg.numbers_only)

    sc = cfg.scope
    if sc == "mensaje":
        extracted = text
    elif sc == "match":
        extracted = m.group(0)
    elif sc == "group1":
        try:
            extracted = m.group(1)
        except IndexError:
            extracted = m.group(0)
    elif sc == "query_line":
        line = first_line_with_match(text, m)
        extracted = f"{cfg.pattern_text} {line}".strip()
    elif sc == "nums_line":
        line = first_line_with_match(text, m)
        extracted = only_numbers_and_signs(line) or ""
    else:
        extracted = text
    return extracted

async def run_extraction(cfg: ExtractConfig, cancel_key: Tup[int,int]) -> Tuple[str, int, int, float, dict]:
    """
    Lectura en vivo (Telethon) del canal origen.
    """
    global telethon_client
    assert telethon_client is not None

    src_id = selected_source_id(cfg)
    rx = build_regex(cfg)
    reverse = True if cfg.order == "antiguos" else False

    count = 0
    lines = []
    scanned = 0
    t0 = time.time()
    cancel_event = cancel_flags.get(cancel_key)

    async for msg in telethon_client.iter_messages(src_id, reverse=reverse):
        if cancel_event and cancel_event.is_set():
            break

        scanned += 1

        text = (msg.message or "").strip()
        if not text:
            continue

        out = extract_content_normal(text, rx, cfg)
        if out is None or out == "":
            # límites de abandono temprano si no hay hallazgos
            if count == 0:
                if cfg.max_scan and scanned >= cfg.max_scan:
                    break
                if cfg.max_seconds and (time.time() - t0) >= cfg.max_seconds:
                    break
            continue

        out = maybe_anonymize(out, cfg.anonymize_digits)
        lines.append(out)
        count += 1

        if count >= cfg.limit:
            break

    fd, path = tempfile.mkstemp(prefix="extract_", suffix=".txt")
    os.close(fd)
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    elapsed = time.time() - t0
    return path, count, scanned, elapsed, {}

async def run_extraction_db(cfg: ExtractConfig, cancel_key: Tup[int,int]) -> Tuple[str, int, int, float, dict]:
    """
    Búsqueda usando la BD local (SQLite).
    """
    t0 = time.time()
    texts = await asyncio.to_thread(_db_select_texts, cfg)
    scanned = 0
    count = 0
    lines: List[str] = []
    rx = build_regex(cfg)
    cancel_event = cancel_flags.get(cancel_key)

    for text in texts:
        if cancel_event and cancel_event.is_set():
            break
        scanned += 1
        if not text:
            continue

        out = extract_content_normal(text, rx, cfg)
        if out is None or out == "":
            if count == 0:
                if cfg.max_scan and scanned >= cfg.max_scan:
                    break
                if cfg.max_seconds and (time.time() - t0) >= cfg.max_seconds:
                    break
            continue

        out = maybe_anonymize(out, cfg.anonymize_digits)
        lines.append(out)
        count += 1
        if count >= cfg.limit:
            break

    fd, path = tempfile.mkstemp(prefix="extract_", suffix=".txt")
    os.close(fd)
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    elapsed = time.time() - t0
    return path, count, scanned, elapsed, {}

# ---------- UI (panel)
def cfg_to_lines(cfg: ExtractConfig) -> str:
    name1 = SOURCE_NAMES.get(1, "") or "(canal 1)"
    name2 = SOURCE_NAMES.get(2, "") or "(canal 2)"
    has2 = bool(SOURCE_IDS.get(2))

    source_line = f""
    if has2:
        source_line += f"\n*Canales:* 1=“Slow” · 2=“KEN”"
    else:
        source_line += f"\n*Canales:* 1=“SlowKen” · 2=(no configurado)"

    base = (
        f"{source_line}\n\n"
        f"*Patrón:* `{cfg.pattern_text}` ({'regex' if cfg.is_regex else 'literal'})\n"
        f"*Scope:* `{cfg.scope}`\n"
        f"*Orden:* `{cfg.order}`\n"
        f"*Límite:* `{cfg.limit}`\n"
        f"*Modo búsqueda:* {'BD' if cfg.use_db else 'Live'}\n"
        f"*Flags:* ignorecase={cfg.case_ins}, dotall={cfg.dot_all}, anon={cfg.anonymize_digits}\n"
        f"*Exploración:* {cfg.max_scan} msgs · {cfg.max_seconds}s\n"
        f"*IDCC:* {'ON' if cfg.idcc_only else 'OFF'} (si ON, salida = línea que contenga 'CC:')\n"
        f"*Num+Signos:* {'ON' if cfg.numbers_only else 'OFF'}\n"
    )
    return base

def build_menu(cfg: ExtractConfig, is_admin_user: bool = False) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton(f"Canal: {cfg.source_idx}", callback_data="toggle:source"),
         InlineKeyboardButton("🔄 Refrescar canales", callback_data="action:refresh_sources")],

        [InlineKeyboardButton(f"Patrón: {'regex' if cfg.is_regex else 'literal'}", callback_data="toggle:mode"),
         InlineKeyboardButton("✏️ Cambiar patrón", callback_data="set:pattern")],

        [InlineKeyboardButton(f"Scope: {cfg.scope}", callback_data="cycle:scope"),
         InlineKeyboardButton(f"IDCC: {'ON' if cfg.idcc_only else 'OFF'}", callback_data="toggle:idcc"),
         InlineKeyboardButton(f"Num+Signos: {'ON' if cfg.numbers_only else 'OFF'}", callback_data="toggle:numsigns")],

        [InlineKeyboardButton(f"Orden: {cfg.order}", callback_data="toggle:order"),
         InlineKeyboardButton(f"Límite: {cfg.limit}", callback_data="set:limit")],

        [InlineKeyboardButton(f"IC: {int(cfg.case_ins)}", callback_data="toggle:ic"),
         InlineKeyboardButton(f"DOTALL: {int(cfg.dot_all)}", callback_data="toggle:da"),
         InlineKeyboardButton(f"ANON: {int(cfg.anonymize_digits)}", callback_data="toggle:anon")],

        [InlineKeyboardButton(f"Exploración: {cfg.max_scan} msgs", callback_data="set:maxscan"),
         InlineKeyboardButton(f"Tiempo: {cfg.max_seconds}s", callback_data="set:maxtime")],

        [InlineKeyboardButton(f"Modo: {'BD' if cfg.use_db else 'Live'}", callback_data="toggle:dbmode")],

        [InlineKeyboardButton("✅ Iniciar", callback_data="action:start"),
         InlineKeyboardButton("✖️ Cancelar", callback_data="action:cancel")],
    ]

    if is_admin_user:
        rows.insert(-1, [
            InlineKeyboardButton("🧩 Actualizar BD (canal)", callback_data="action:reindex:current"),
            InlineKeyboardButton("🧩 Actualizar BD (ambos)", callback_data="action:reindex:both"),
        ])

    return InlineKeyboardMarkup(rows)

def build_locked_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("🔑 Canjear key", callback_data="set:redeem")]])

# ---------- Descarga TXT (token)
download_tokens: Dict[str, dict] = {}

async def expire_token_later(token: str, seconds: int = 3600):
    await asyncio.sleep(seconds)
    info = download_tokens.pop(token, None)
    if info:
        try:
            if os.path.exists(info["path"]):
                os.remove(info["path"])
        except Exception:
            pass

def register_download_token(path: str, user_id: int, count: int, ttl_seconds: int = 3600) -> str:
    token = uuid.uuid4().hex[:10]
    download_tokens[token] = {
        "path": path,
        "user_id": user_id,
        "count": count,
        "expires_at": now_ts() + ttl_seconds
    }
    asyncio.create_task(expire_token_later(token, ttl_seconds))
    return token

# ---------- Concurrencia extracción
task_semaphore = asyncio.Semaphore(CONCURRENCY_LIMIT)
running_tasks: Dict[Tup[int,int], asyncio.Task] = {}
cancel_flags: Dict[Tup[int,int], asyncio.Event] = {}

# ---------- Ayudas UI
def read_first_lines(path: str, n: int = 20, max_chars: int = 3500) -> List[str]:
    out = []
    used = 0
    try:
        with open(path, "r", encoding="utf-8") as f:
            for i, line in enumerate(f):
                if i >= n:
                    break
                s = line.rstrip("\n")
                if not s:
                    continue
                add = len(s) + 1
                if used + add > max_chars:
                    break
                out.append(s)
                used += add
    except Exception as e:
        return [f"(No se pudo leer preview: {e})"]
    return out

# ---------- Decoradores auth
def require_auth(func):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE, *args, **kwargs):
        user = update.effective_user
        if not user:
            return
        if is_admin(user.id):
            return await func(update, context, *args, **kwargs)
        ok, msg = user_status(user.id)
        if not ok:
            await update.effective_chat.send_message(
                f"🔒 {msg}\nPulsa el botón para canjear una key.",
                reply_markup=build_locked_menu()
            )
            return
        return await func(update, context, *args, **kwargs)
    return wrapper

def require_admin(func):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE, *args, **kwargs):
        if not update.effective_user or not is_admin(update.effective_user.id):
            await update.effective_chat.send_message("⛔ Solo el admin puede usar este comando.")
            return
        return await func(update, context, *args, **kwargs)
    return wrapper

# ---------- Textos de ayuda
def help_text_user() -> str:
    return (
        "🤖 *Bot privado*\n"
        "Comandos de usuario:\n"
        "• /start — abrir panel / canjear key\n"
        "• /status — estado de acceso\n"
        "• /redeem <KEY> — canjear key\n"
    )

def help_text_admin() -> str:
    return (
        "👑 *Comandos de admin*\n"
        "• /genkey days=<d> runs=<r> uses=<u> keydays=<kd>\n"
        "• /adduser id=<uid> days=<d> runs=<r>\n"
        "• /deluser id=<uid>\n"
        "• /users\n"
        "• /keys\n"
    )

# ---------- Handlers básicos
async def start_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user

    if is_admin(user.id):
        await update.effective_chat.send_message(
            help_text_user() + "\n" + help_text_admin(),
            parse_mode="Markdown"
        )
    else:
        ok, msg = user_status(user.id)
        if not ok:
            await update.effective_chat.send_message(
                f"🔒 {msg}\nPulsa el botón para canjear una key o usa /redeem <KEY>.",
                reply_markup=build_locked_menu()
            )
            return
        else:
            await update.effective_chat.send_message(
                help_text_user(),
                parse_mode="Markdown"
            )

    cfg = context.user_data.get("cfg") or ExtractConfig()
    if cfg.source_idx not in (1, 2):
        cfg.source_idx = 1
    if cfg.source_idx == 2 and not SOURCE_IDS.get(2):
        cfg.source_idx = 1

    context.user_data["cfg"] = cfg
    for k in ["awaiting_pattern","awaiting_limit","awaiting_redeem","awaiting_maxscan","awaiting_maxtime"]:
        context.user_data[k] = False

    await update.effective_chat.send_message(
        "🤖 *Extractor interactivo*\nConfigura y pulsa *Iniciar*.\n\n" + cfg_to_lines(cfg),
        parse_mode="Markdown",
        reply_markup=build_menu(cfg, is_admin_user=is_admin(user.id))
    )

@require_auth
async def status_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ok, msg = user_status(update.effective_user.id)
    cfg: ExtractConfig = context.user_data.get("cfg", ExtractConfig())
    await update.effective_chat.send_message(
        f"⚙️ *Estado*\n{msg}\n\n" + cfg_to_lines(cfg), parse_mode="Markdown",
        reply_markup=build_menu(cfg, is_admin_user=is_admin(update.effective_user.id))
    )

async def redeem_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_chat.send_message("Uso: /redeem <KEY>")
        return
    key = context.args[0].strip()
    ok, msg = await redeem_key_async(key, update.effective_user.id)
    await update.effective_chat.send_message(("✅ " if ok else "❌ ") + msg)
    if ok:
        await start_cmd(update, context)

@require_admin
async def genkey_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    params = {k: v for k, v in (p.split("=", 1) for p in context.args if "=" in p)}
    days = int(params.get("days", "30"))
    runs = int(params.get("runs", "100"))
    uses = int(params.get("uses", "1"))
    keydays = int(params.get("keydays", "7"))
    k = gen_key(days, runs, uses, keydays)
    await update.effective_chat.send_message(
        f"🔑 Key: `{k}`\nConcede: {runs} usos, {days} días · Usos disponibles: {uses} · Caduca en {keydays} días.",
        parse_mode="Markdown"
    )

@require_admin
async def adduser_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    params = {k: v for k, v in (p.split("=", 1) for p in context.args if "=" in p)}
    uid = int(params.get("id", "0"))
    days = int(params.get("days", "30"))
    runs = int(params.get("runs", "100"))
    if not uid:
        await update.effective_chat.send_message("Uso: /adduser id=<uid> days=<d> runs=<r>")
        return
    async with store_lock:
        await grant_user(uid, days, runs)
    await update.effective_chat.send_message(f"✅ Usuario {uid} habilitado (+{runs} usos, +{days} días).")

@require_admin
async def deluser_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    params = {k: v for k, v in (p.split("=", 1) for p in context.args if "=" in p)}
    uid = params.get("id")
    if not uid:
        await update.effective_chat.send_message("Uso: /deluser id=<uid>")
        return
    async with store_lock:
        if store["users"].pop(uid, None):
            save_store(store)
            await update.effective_chat.send_message(f"🗑️ Usuario {uid} eliminado.")
        else:
            await update.effective_chat.send_message("ℹ️ Usuario no encontrado.")

@require_admin
async def users_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cleanup_expired()
    lines = []
    for uid, u in store["users"].items():
        exp = u["expires_at"]
        exp_str = time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime(exp)) if exp else "sin fecha"
        lines.append(f"{uid}: usos={u['remaining']}, expira={exp_str}")
    if not lines:
        lines = ["(sin usuarios)"]
    await update.effective_chat.send_message("👥 *Usuarios*\n" + "\n".join(lines), parse_mode="Markdown")

@require_admin
async def keys_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cleanup_expired()
    lines = []
    for k, v in store["keys"].items():
        kd = v.get("key_expires_at")
        kd_str = time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime(kd)) if kd else "sin fecha"
        lines.append(f"{k}: concede {v['grant_runs']} usos/{v['grant_days']} días · usos_left={v['uses_left']} · caduca={kd_str}")
    if not lines:
        lines = ["(sin keys)"]
    await update.effective_chat.send_message("🔑 *Keys*\n" + "\n".join(lines), parse_mode="Markdown")

# ---------- Botones / callbacks
async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    user = update.effective_user
    data = query.data

    # Descargar todo
    if data.startswith("getall:"):
        token = data.split(":", 1)[1]
        info = download_tokens.get(token)
        if not info:
            await query.edit_message_text("⚠️ Enlace de descarga inválido o expirado.")
            return
        if info["user_id"] != user.id and not is_admin(user.id):
            await query.edit_message_text("⛔ No puedes descargar resultados de otra sesión.")
            return
        path = info["path"]
        try:
            await context.bot.send_document(chat_id=update.effective_chat.id, document=path,
                                            caption=f"📄 Resultados completos ({info['count']})")
            try:
                os.remove(path)
            except Exception:
                pass
            download_tokens.pop(token, None)
            try:
                await query.edit_message_text("✅ Archivo enviado.")
            except Exception:
                pass
        except Exception as e:
            await query.edit_message_text(f"⚠️ No pude enviar el archivo: {e}")
        return

    # Botón canjear
    if data == "set:redeem":
        context.user_data["awaiting_redeem"] = True
        for k in ["awaiting_pattern","awaiting_limit","awaiting_maxscan","awaiting_maxtime"]:
            context.user_data[k] = False
        await query.edit_message_text("🔑 Envía tu *KEY* en un mensaje.", parse_mode="Markdown")
        return

    # Autorización (antes de operar)
    if not is_admin(user.id):
        ok, msg = user_status(user.id)
        if not ok:
            await query.edit_message_text(
                f"🔒 {msg}\nPulsa el botón para canjear una key.",
                reply_markup=build_locked_menu()
            )
            return

    cfg: ExtractConfig = context.user_data.get("cfg", ExtractConfig())

    # Alternar canal
    if data == "toggle:source":
        new_idx = 2 if cfg.source_idx == 1 else 1
        if SOURCE_IDS.get(new_idx):
            cfg.source_idx = new_idx
            msg = f"✅ Canal cambiado a {new_idx} — {SOURCE_NAMES.get(new_idx,'')}"
        else:
            msg = "ℹ️ El Canal 2 no está configurado. Permanece en Canal 1."
        context.user_data["cfg"] = cfg
        try:
            await query.edit_message_text(
                f"{msg}\n\n" + cfg_to_lines(cfg),
                parse_mode="Markdown",
                reply_markup=build_menu(cfg, is_admin_user=is_admin(user.id))
            )
        except Exception:
            pass
        return

    # Refrescar canales
    if data == "action:refresh_sources":
        try:
            await resolve_sources(telethon_client)
            if cfg.source_idx == 2 and not SOURCE_IDS.get(2):
                cfg.source_idx = 1
            context.user_data["cfg"] = cfg
            await query.edit_message_text(
                "🔄 Canales actualizados.\n\n" + cfg_to_lines(cfg),
                parse_mode="Markdown",
                reply_markup=build_menu(cfg, is_admin_user=is_admin(user.id))
            )
        except Exception as e:
            await query.edit_message_text(f"⚠️ No se pudieron refrescar canales: {e}")
        return

    # Toggles y set…
    if data == "toggle:idcc":
        cfg.idcc_only = not cfg.idcc_only
    elif data == "toggle:numsigns":
        cfg.numbers_only = not cfg.numbers_only
    elif data == "toggle:mode":
        cfg.is_regex = not cfg.is_regex
    elif data == "set:pattern":
        context.user_data["awaiting_pattern"] = True
        for k in ["awaiting_limit","awaiting_redeem","awaiting_maxscan","awaiting_maxtime"]:
            context.user_data[k] = False
        await query.edit_message_text("✏️ Envía ahora el *patrón* (texto o regex) como mensaje.", parse_mode="Markdown")
        return
    elif data == "cycle:scope":
        i = SCOPES.index(cfg.scope)
        cfg.scope = SCOPES[(i + 1) % len(SCOPES)]
    elif data == "toggle:order":
        cfg.order = "antiguos" if cfg.order == "recientes" else "recientes"
    elif data == "set:limit":
        context.user_data["awaiting_limit"] = True
        for k in ["awaiting_pattern","awaiting_redeem","awaiting_maxscan","awaiting_maxtime"]:
            context.user_data[k] = False
        await query.edit_message_text("🔢 Envía el *límite* (entero, máx 10000) como mensaje.", parse_mode="Markdown")
        return
    elif data == "toggle:ic":
        cfg.case_ins = not cfg.case_ins
    elif data == "toggle:da":
        cfg.dot_all = not cfg.dot_all
    elif data == "toggle:anon":
        cfg.anonymize_digits = not cfg.anonymize_digits
    elif data == "set:maxscan":
        context.user_data["awaiting_maxscan"] = True
        for k in ["awaiting_maxtime","awaiting_limit","awaiting_pattern","awaiting_redeem"]:
            context.user_data[k] = False
        await query.edit_message_text("🔍 Envía *máx mensajes a explorar sin hallazgos* (entero, p. ej. 2000).",
                                      parse_mode="Markdown")
        return
    elif data == "set:maxtime":
        context.user_data["awaiting_maxtime"] = True
        for k in ["awaiting_maxscan","awaiting_limit","awaiting_pattern","awaiting_redeem"]:
            context.user_data[k] = False
        await query.edit_message_text("⏱️ Envía *tiempo máximo sin hallazgos* en segundos (entero, p. ej. 20).",
                                      parse_mode="Markdown")
        return
    elif data == "toggle:dbmode":
        cfg.use_db = not cfg.use_db
    elif data == "action:cancel":
        try:
            await query.edit_message_text("❌ Operación cancelada.")
        except Exception:
            pass
        return
    elif data == "action:start":
        context.user_data["cfg"] = cfg
        await start_extraction_flow(update, context, cfg)
        return
    elif data == "action:reindex:current":
        if not is_admin(user.id):
            await query.edit_message_text("⛔ Solo el admin puede reindexar la base de datos.")
            return
        await query.edit_message_text("⏳ Iniciando reindex del canal actual…")
        try:
            await reindex_channel(cfg.source_idx, update.effective_chat.id, context)
        except Exception as e:
            await context.bot.send_message(update.effective_chat.id, f"⚠️ Error: {e}")
        return
    elif data == "action:reindex:both":
        if not is_admin(user.id):
            await query.edit_message_text("⛔ Solo el admin puede reindexar la base de datos.")
            return
        await query.edit_message_text("⏳ Iniciando reindex de ambos canales…")
        try:
            await reindex_both(update.effective_chat.id, context)
        except Exception as e:
            await context.bot.send_message(update.effective_chat.id, f"⚠️ Error: {e}")
        return

    context.user_data["cfg"] = cfg
    try:
        await query.edit_message_text("🤖 *Extractor interactivo*\n" + cfg_to_lines(cfg),
                                      parse_mode="Markdown",
                                      reply_markup=build_menu(cfg, is_admin_user=is_admin(user.id)))
    except Exception:
        pass

async def stop_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    data = q.data  # stop:<chat_id>:<user_id>
    try:
        _, cid_str, uid_str = data.split(":", 2)
        cid = int(cid_str); uid = int(uid_str)
    except Exception:
        try:
            await q.edit_message_text("⚠️ Botón inválido.")
        except Exception:
            pass
        return
    key = (cid, uid)
    ev = cancel_flags.get(key)
    if ev:
        ev.set()
        try:
            await q.edit_message_text("🛑 Solicitando detener…")
        except Exception:
            pass
    else:
        try:
            await q.edit_message_text("ℹ️ No hay búsqueda en curso para tu sesión.")
        except Exception:
            pass

# ---------- Router de texto (key/patrón/límite/maxscan/maxtime)
async def text_input_router(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (update.message.text or "").strip()
    if not text:
        return

    # 1) KEY
    if context.user_data.get("awaiting_redeem"):
        ok, msg = await redeem_key_async(text, update.effective_user.id)
        context.user_data["awaiting_redeem"] = False
        await update.effective_chat.send_message(("✅ " if ok else "❌ ") + msg)
        if ok:
            await start_cmd(update, context)
        else:
            await update.effective_chat.send_message(
                "Pulsa para intentar otra key.",
                reply_markup=build_locked_menu()
            )
        return

    # Autorización
    ok, _ = user_status(update.effective_user.id)
    if not ok and not is_admin(update.effective_user.id):
        await update.effective_chat.send_message("🔒 No autorizado. Canjea una key primero.",
                                                 reply_markup=build_locked_menu())
        return

    # 2) Límite
    if context.user_data.get("awaiting_limit"):
        if not text.isdigit() or int(text) <= 0:
            await update.effective_chat.send_message("❗ Límite inválido. Escribe un entero positivo (máx 10000).")
            return
        limit = min(int(text), 10000)
        cfg: ExtractConfig = context.user_data.get("cfg", ExtractConfig())
        cfg.limit = limit
        context.user_data["cfg"] = cfg
        context.user_data["awaiting_limit"] = False
        await update.effective_chat.send_message("✅ Límite actualizado.\n\n" + cfg_to_lines(cfg),
                                                 parse_mode="Markdown",
                                                 reply_markup=build_menu(cfg, is_admin_user=is_admin(update.effective_user.id)))
        return

    # 3) Patrón
    if context.user_data.get("awaiting_pattern"):
        cfg: ExtractConfig = context.user_data.get("cfg", ExtractConfig())
        cfg.pattern_text = text
        context.user_data["cfg"] = cfg
        context.user_data["awaiting_pattern"] = False
        await update.effective_chat.send_message("✅ Patrón actualizado.\n\n" + cfg_to_lines(cfg),
                                                 parse_mode="Markdown",
                                                 reply_markup=build_menu(cfg, is_admin_user=is_admin(update.effective_user.id)))
        return

    # 4) Máx mensajes sin hallazgos
    if context.user_data.get("awaiting_maxscan"):
        if not text.isdigit() or int(text) <= 0:
            await update.effective_chat.send_message("❗ Valor inválido. Escribe un entero positivo (p. ej. 2000).")
            return
        val = min(int(text), 200000)
        cfg: ExtractConfig = context.user_data.get("cfg", ExtractConfig())
        cfg.max_scan = val
        context.user_data["cfg"] = cfg
        context.user_data["awaiting_maxscan"] = False
        await update.effective_chat.send_message("✅ Exploración (máx mensajes) actualizada.\n\n" + cfg_to_lines(cfg),
                                                 parse_mode="Markdown",
                                                 reply_markup=build_menu(cfg, is_admin_user=is_admin(update.effective_user.id)))
        return

    # 5) Tiempo máx sin hallazgos
    if context.user_data.get("awaiting_maxtime"):
        if not text.isdigit() or int(text) <= 0:
            await update.effective_chat.send_message("❗ Valor inválido. Escribe segundos como entero positivo (p. ej. 20).")
            return
        val = min(int(text), 3600)
        cfg: ExtractConfig = context.user_data.get("cfg", ExtractConfig())
        cfg.max_seconds = val
        context.user_data["cfg"] = cfg
        context.user_data["awaiting_maxtime"] = False
        await update.effective_chat.send_message("✅ Tiempo máximo actualizado.\n\n" + cfg_to_lines(cfg),
                                                 parse_mode="Markdown",
                                                 reply_markup=build_menu(cfg, is_admin_user=is_admin(update.effective_user.id)))
        return

# ---------- Flujo de extracción
@require_auth
async def start_extraction_flow(update: Update, context: ContextTypes.DEFAULT_TYPE, cfg: ExtractConfig):
    user_id = update.effective_user.id
    chat_id = update.effective_chat.id
    key: Tup[int,int] = (chat_id, user_id)

    task = running_tasks.get(key)
    if task and not task.done():
        await update.effective_chat.send_message("⏳ Ya tienes una extracción en curso aquí. Usa el botón 🔴 Detener o espera a que termine.")
        return

    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔴 Detener búsqueda", callback_data=f"stop:{chat_id}:{user_id}")]])
    msgm = await update.effective_chat.send_message("⏳ Buscando coincidencias…", reply_markup=kb)

    ev = cancel_flags.get(key)
    if ev is None:
        ev = asyncio.Event()
        cancel_flags[key] = ev
    else:
        ev.clear()

    running_tasks[key] = asyncio.create_task(extraction_worker(key, cfg, msgm, update, context, user_id))

async def extraction_worker(key: Tup[int,int], cfg: ExtractConfig, msgm, update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int):
    chat_id, _ = key
    try:
        async with task_semaphore:
            try:
                if cfg.use_db:
                    path, count, scanned, elapsed, stats = await run_extraction_db(cfg, key)
                else:
                    path, count, scanned, elapsed, stats = await run_extraction(cfg, key)
            except Exception as e:
                try:
                    await msgm.edit_text(f"❌ Error en extracción: {e}")
                except Exception:
                    await context.bot.send_message(chat_id=chat_id, text=f"❌ Error en extracción: {e}")
                return

            # Cancelado
            if cancel_flags.get(key) and cancel_flags[key].is_set():
                try:
                    await msgm.edit_text("🛑 Búsqueda detenida por el usuario.")
                except Exception:
                    await context.bot.send_message(chat_id=chat_id, text="🛑 Búsqueda detenida por el usuario.")
                try:
                    if os.path.exists(path) and os.path.getsize(path) == 0:
                        os.remove(path)
                except Exception:
                    pass
                return

            # Sin resultados
            if count == 0:
                msg_txt = f"🔎 No se encontraron coincidencias tras explorar {scanned} {'registros de BD' if cfg.use_db else 'mensajes'} en {elapsed:.1f}s."
                try:
                    await msgm.edit_text(msg_txt, parse_mode="Markdown")
                except Exception:
                    await context.bot.send_message(chat_id=chat_id, text=msg_txt, parse_mode="Markdown")
                try:
                    if os.path.exists(path):
                        os.remove(path)
                except Exception:
                    pass
                return

            # Preview (primeros 20) SIN numeración
            preview_lines = read_first_lines(path, n=20, max_chars=3500)
            first_n = min(20, count)
            body = "\n".join(preview_lines)
            await context.bot.send_message(
                chat_id=chat_id,
                text=f"🧾 Primeros {first_n} resultados (de {count}):\n{body}"
            )

            if count > 20:
                dl_token = register_download_token(path, user_id, count, ttl_seconds=3600)
                kb = InlineKeyboardMarkup([[InlineKeyboardButton(f"📄 Descargar TXT ({count})", callback_data=f"getall:{dl_token}")]])
                await context.bot.send_message(chat_id=chat_id, text="Hay más resultados. Descarga el archivo completo:", reply_markup=kb)
                try:
                    await msgm.edit_text("✅ Búsqueda finalizada (preview enviada).")
                except Exception:
                    pass
            else:
                try:
                    await msgm.edit_text("✅ Búsqueda finalizada.")
                except Exception:
                    pass
                try:
                    os.remove(path)
                except Exception:
                    pass

            if not is_admin(user_id):
                consume_usage_on_success(user_id)

    finally:
        running_tasks.pop(key, None)

# ---------- Ciclo de vida: iniciar Telethon + DB
async def post_init(app: Application):
    """
    Conecta sin reloguear. Solo si marcas FIRST_LOGIN=1 o no hay sesión,
    hace el flujo de login una sola vez y guarda 'bridge_session.session'.
    Si defines STRING_SESSION en .env, usará esa en lugar del archivo.
    """
    global telethon_client

    FIRST_LOGIN = (ENV.get("FIRST_LOGIN", "0").strip() == "1")
    STRING = (ENV.get("STRING_SESSION") or "").strip()

    # Construir cliente con archivo de sesión o StringSession
    if STRING:
        telethon_client = TelegramClient(
            StringSession(STRING),
            API_ID,
            API_HASH,
            device_model="PC",
            system_version="Windows 11",
            app_version="10.0",
            lang_code="es",
        )
    else:
        telethon_client = TelegramClient(
            "bridge_session",      # ¡mantén SIEMPRE el mismo nombre!
            API_ID,
            API_HASH,
            device_model="PC",
            system_version="Windows 11",
            app_version="10.0",
            lang_code="es",
        )

    # Estrategia:
    # - Si FIRST_LOGIN=1 -> start(phone=...), solo la primera vez.
    # - Si FIRST_LOGIN=0 -> connect() y exige que ya exista sesión válida.
    if FIRST_LOGIN:
        # Primera vez: hará el flujo de código/2FA y guardará la sesión.
        await telethon_client.start(phone=PHONE_NUMBER)
    else:
        # Reutiliza sesión sin reloguear
        await telethon_client.connect()
        if not await telethon_client.is_user_authorized():
            raise RuntimeError(
                "No hay sesión de usuario aún. Ejecuta una sola vez con FIRST_LOGIN=1 "
                "para iniciar sesión y generar 'bridge_session.session', o bien define STRING_SESSION en .env."
            )

    # Ya conectados: resolver canales + BD
    await resolve_sources(telethon_client)
    db_init()
    names = " | ".join([f"{i}:{SOURCE_NAMES.get(i,'')}" for i in (1,2)])
    print(f"[MTProto] Conectado. SOURCES => {names}")


# ---------- Main
def main():
    app = Application.builder().token(BOT_TOKEN).post_init(post_init).build()
    # usuario
    app.add_handler(CommandHandler("start", start_cmd))
    app.add_handler(CommandHandler("status", status_cmd))
    app.add_handler(CommandHandler("redeem", redeem_cmd))
    # admin
    app.add_handler(CommandHandler("genkey", genkey_cmd))
    app.add_handler(CommandHandler("adduser", adduser_cmd))
    app.add_handler(CommandHandler("deluser", deluser_cmd))
    app.add_handler(CommandHandler("users", users_cmd))
    app.add_handler(CommandHandler("keys", keys_cmd))
    # botones
    app.add_handler(CallbackQueryHandler(stop_button, pattern=r"^stop:-?\d+:-?\d+$"))
    app.add_handler(CallbackQueryHandler(on_button))
    # router de texto
    app.add_handler(MessageHandler(filters.TEXT & (~filters.COMMAND), text_input_router))

    print(f"Bot listo. Concurrencia máxima: {CONCURRENCY_LIMIT}. Usa /start para abrir el panel.")
    app.run_polling(close_loop=False)

if __name__ == "__main__":
    main()
