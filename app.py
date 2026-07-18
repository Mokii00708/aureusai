from flask import Flask, request, send_file, jsonify, make_response
import os
import json
import re
import ast
import math
import ssl
import random
import difflib
import io
import time
import threading
import secrets
import hashlib
import hmac
import base64
import zipfile
import bcrypt
from cryptography.fernet import Fernet, InvalidToken
from datetime import datetime, timezone, timedelta
from html import unescape
from urllib.parse import quote_plus
from urllib.request import Request, urlopen
from xml.etree import ElementTree as ET
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker
from sqlalchemy.pool import QueuePool
from dotenv import load_dotenv
from openai import OpenAI
import tiktoken

# Step 1: Environment & Client Initialization
load_dotenv()

API_KEY = os.getenv("OPENAI_API_KEY")
if not API_KEY:
    raise EnvironmentError(
        "Missing OPENAI_API_KEY in .env file. "
        "Please create a .env file with OPENAI_API_KEY=your_key"
    )

try:
    frontier_client = OpenAI(api_key=API_KEY)
except Exception as e:
    raise RuntimeError(f"Failed to initialize OpenAI client: {str(e)}")

# Step 2: Persistent Conversation Memory
HISTORY_FILE = "history.json"
DATA_DIR = "data"
USER_MEMORY_DIR = os.path.join(DATA_DIR, "users")
UPLOADS_DIR = os.path.join(DATA_DIR, "uploads")
LEARNING_FILE = os.path.join(DATA_DIR, "learning_memory.json")
ACCOUNTS_FILE = os.path.join(DATA_DIR, "accounts.json")
SESSIONS_FILE = os.path.join(DATA_DIR, "sessions.json")
ANALYTICS_DB_FILE = os.path.join(DATA_DIR, "analytics_engine.db")
DATABASE_URL = (
    (os.getenv("DATABASE_URL") or "").strip()
    or (os.getenv("ANALYTICS_DATABASE_URL") or "").strip()
    or f"sqlite:///{ANALYTICS_DB_FILE}"
)

DB_POOL_SIZE = int(os.getenv("DB_POOL_SIZE", "5"))
DB_MAX_OVERFLOW = int(os.getenv("DB_MAX_OVERFLOW", "10"))
DB_POOL_RECYCLE_SECONDS = int(os.getenv("DB_POOL_RECYCLE_SECONDS", "1800"))
LLM_REQUEST_TIMEOUT_SECONDS = float(os.getenv("LLM_REQUEST_TIMEOUT_SECONDS", "25"))
DATA_UNAVAILABLE_RETRY_MESSAGE = "Data unavailable right now. Please try again in a moment."
MARKET_DATA_UNAVAILABLE_RETRY_MESSAGE = "Market data unavailable right now. Please try again in a moment."
UNVERIFIED_FINANCIAL_CLAIM_MESSAGE = (
    "I cannot verify numeric financial figures for this request from live/cached sources right now. "
    "Please retry or ask for an assumption-based estimate explicitly."
)
DEFAULT_USER_ID = "guest"
APP_SECRET = os.getenv("APP_SECRET") or API_KEY
ACCESS_TOKEN_TTL_SECONDS = min(86400, int(os.getenv("ACCESS_TOKEN_TTL_SECONDS", "3600")))
REFRESH_TOKEN_TTL_SECONDS = int(os.getenv("REFRESH_TOKEN_TTL_SECONDS", "604800"))
DATA_ENCRYPTION_KEY = (os.getenv("DATA_ENCRYPTION_KEY") or "").strip()
COOKIE_SECURE = os.getenv("COOKIE_SECURE", "0") in {"1", "true", "True"}
MAX_JSON_BODY_BYTES = int(os.getenv("MAX_JSON_BODY_BYTES", "16384"))
MAX_CHAT_ATTACHMENTS = int(os.getenv("MAX_CHAT_ATTACHMENTS", "5"))
MAX_ATTACHMENT_BYTES = int(os.getenv("MAX_ATTACHMENT_BYTES", str(6 * 1024 * 1024)))
AUTH_RATE_LIMIT_WINDOW = int(os.getenv("AUTH_RATE_LIMIT_WINDOW", "300"))
AUTH_RATE_LIMIT_MAX = int(os.getenv("AUTH_RATE_LIMIT_MAX", "20"))
CHAT_USER_RATE_LIMIT_WINDOW = int(os.getenv("CHAT_USER_RATE_LIMIT_WINDOW", "300"))
CHAT_USER_RATE_LIMIT_MAX = int(os.getenv("CHAT_USER_RATE_LIMIT_MAX", "30"))
AUTO_LEARN_ENABLED = os.getenv("AUTO_LEARN_ENABLED", "1") not in {"0", "false", "False"}
AUTO_LEARN_INTERVAL_SECONDS = int(os.getenv("AUTO_LEARN_INTERVAL_SECONDS", "900"))
AUTO_LEARN_IDLE_SECONDS = int(os.getenv("AUTO_LEARN_IDLE_SECONDS", "300"))
AUTO_LEARN_TOPIC_LIMIT = int(os.getenv("AUTO_LEARN_TOPIC_LIMIT", "3"))
UPLOAD_RETENTION_DAYS = int(os.getenv("UPLOAD_RETENTION_DAYS", "7"))
UPLOAD_CLEAN_INTERVAL_SECONDS = int(os.getenv("UPLOAD_CLEAN_INTERVAL_SECONDS", "21600"))

last_user_activity_ts = time.time()
idle_worker_started = False
upload_cleanup_worker_started = False
idle_learning_lock = threading.Lock()
auth_rate_limit_lock = threading.Lock()
auth_rate_limit_hits = {}
analytics_db_lock = threading.Lock()
finance_cache_lock = threading.Lock()
finance_quote_cache = {}
fx_rate_cache = {}


def build_state_fernet():
    """Build a stable Fernet cipher for encrypting persisted user state fields."""
    raw_key = DATA_ENCRYPTION_KEY
    if raw_key:
        candidate = raw_key.encode("utf-8")
    else:
        digest = hashlib.sha256((APP_SECRET or "fallback-state-key").encode("utf-8")).digest()
        candidate = base64.urlsafe_b64encode(digest)
    try:
        return Fernet(candidate)
    except Exception:
        return None


STATE_FERNET = build_state_fernet()
ENCRYPTED_STATE_VERSION = 1
SENSITIVE_STATE_FIELDS = {"profile", "finance_profile"}


def is_encrypted_payload(value):
    return isinstance(value, dict) and bool(value.get("__encrypted__")) and isinstance(value.get("token"), str)


def encrypt_state_value(value):
    if STATE_FERNET is None:
        return value
    try:
        plaintext = json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
        token = STATE_FERNET.encrypt(plaintext).decode("utf-8")
        return {
            "__encrypted__": True,
            "alg": "fernet",
            "v": ENCRYPTED_STATE_VERSION,
            "token": token,
        }
    except Exception:
        return value


def decrypt_state_value(value):
    if not is_encrypted_payload(value):
        return value, False
    token = (value.get("token") or "").strip()
    if not token or STATE_FERNET is None:
        return None, False
    try:
        plaintext = STATE_FERNET.decrypt(token.encode("utf-8"))
        return json.loads(plaintext.decode("utf-8")), True
    except (InvalidToken, ValueError, TypeError, json.JSONDecodeError):
        return None, False
    except Exception:
        return None, False


def encrypt_sensitive_state_fields(state):
    if not isinstance(state, dict):
        return state
    serialized = dict(state)
    for key in SENSITIVE_STATE_FIELDS:
        raw_value = serialized.get(key)
        if raw_value is None or is_encrypted_payload(raw_value):
            continue
        serialized[key] = encrypt_state_value(raw_value)
    return serialized


def decrypt_sensitive_state_fields(state):
    if not isinstance(state, dict):
        return state, False
    hydrated = dict(state)
    upgrade_needed = False
    defaults = default_user_state()
    for key in SENSITIVE_STATE_FIELDS:
        raw_value = hydrated.get(key)
        if is_encrypted_payload(raw_value):
            decrypted, ok = decrypt_state_value(raw_value)
            hydrated[key] = decrypted if ok else defaults.get(key)
        elif raw_value is not None:
            upgrade_needed = True
    return hydrated, upgrade_needed
finance_provider_health = {
    "yahoo": {
        "last_attempt": "",
        "last_success": "",
        "last_error": "",
        "last_error_type": "",
        "last_error_http_status": 0,
        "cooldown_until": "",
        "cooldown_reason": "",
        "last_skip": "",
        "success_count": 0,
        "error_count": 0,
        "skip_count": 0,
    },
    "stooq": {
        "last_attempt": "",
        "last_success": "",
        "last_error": "",
        "last_error_type": "",
        "last_error_http_status": 0,
        "cooldown_until": "",
        "cooldown_reason": "",
        "last_skip": "",
        "success_count": 0,
        "error_count": 0,
        "skip_count": 0,
    },
    "twelvedata": {
        "last_attempt": "",
        "last_success": "",
        "last_error": "",
        "last_error_type": "",
        "last_error_http_status": 0,
        "cooldown_until": "",
        "cooldown_reason": "",
        "last_skip": "",
        "success_count": 0,
        "error_count": 0,
        "skip_count": 0,
    },
    "alpha_vantage": {
        "last_attempt": "",
        "last_success": "",
        "last_error": "",
        "last_error_type": "",
        "last_error_http_status": 0,
        "cooldown_until": "",
        "cooldown_reason": "",
        "last_skip": "",
        "success_count": 0,
        "error_count": 0,
        "skip_count": 0,
    },
}
FINANCE_QUOTE_CACHE_TTL_SECONDS = int(os.getenv("FINANCE_QUOTE_CACHE_TTL_SECONDS", "60"))
QUOTE_PROVIDER_BASE_COOLDOWN_SECONDS = int(os.getenv("QUOTE_PROVIDER_BASE_COOLDOWN_SECONDS", "90"))
QUOTE_PROVIDER_RATE_LIMIT_COOLDOWN_SECONDS = int(os.getenv("QUOTE_PROVIDER_RATE_LIMIT_COOLDOWN_SECONDS", "300"))
QUOTE_PROVIDER_AUTH_COOLDOWN_SECONDS = int(os.getenv("QUOTE_PROVIDER_AUTH_COOLDOWN_SECONDS", "900"))
QUOTE_PROVIDER_NOT_FOUND_COOLDOWN_SECONDS = int(os.getenv("QUOTE_PROVIDER_NOT_FOUND_COOLDOWN_SECONDS", "300"))
FX_RATE_CACHE_TTL_SECONDS = int(os.getenv("FX_RATE_CACHE_TTL_SECONDS", "3600"))
OPPORTUNITY_COST_THRESHOLD_USD = float(os.getenv("OPPORTUNITY_COST_THRESHOLD_USD", "100"))
OPPORTUNITY_COST_DEFAULT_YEARS = int(os.getenv("OPPORTUNITY_COST_DEFAULT_YEARS", "10"))
OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN = float(os.getenv("OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN", "0.07"))
TWELVEDATA_API_KEY = (os.getenv("TWELVEDATA_API_KEY") or "demo").strip()
ALPHA_VANTAGE_API_KEY = (os.getenv("ALPHA_VANTAGE_API_KEY") or "").strip()
HOME_COUNTRY = (os.getenv("HOME_COUNTRY") or "United States").strip()

BASELINE_COST_INDEX_CITY = "new york"
CITY_COST_INDEX = {
    "new york": {"currency": "USD", "cost_index": 100.0},
    "silicon valley": {"currency": "USD", "cost_index": 185.0},
    "san francisco": {"currency": "USD", "cost_index": 185.0},
    "london": {"currency": "GBP", "cost_index": 165.0},
    "dubai": {"currency": "AED", "cost_index": 120.0},
    "abu dhabi": {"currency": "AED", "cost_index": 118.0},
    "mumbai": {"currency": "INR", "cost_index": 55.0},
    "bengaluru": {"currency": "INR", "cost_index": 60.0},
    "bangalore": {"currency": "INR", "cost_index": 60.0},
    "delhi": {"currency": "INR", "cost_index": 52.0},
    "berlin": {"currency": "EUR", "cost_index": 95.0},
    "paris": {"currency": "EUR", "cost_index": 110.0},
    "madrid": {"currency": "EUR", "cost_index": 82.0},
    "lisbon": {"currency": "EUR", "cost_index": 78.0},
    "amsterdam": {"currency": "EUR", "cost_index": 112.0},
    "singapore": {"currency": "SGD", "cost_index": 145.0},
    "tokyo": {"currency": "JPY", "cost_index": 115.0},
}

GEOPOLITICAL_EVENT_KEYWORDS = {
    "tariff": ["tariff", "duties", "import duty", "trade barrier"],
    "tax": ["tax law", "corporate tax", "vat", "levy", "fiscal reform"],
    "shipping": ["shipping delay", "port congestion", "logistics", "freight", "supply chain"],
    "sanction": ["sanction", "export control", "embargo", "restriction"],
}

DOMESTIC_SUPPLIER_CATALOG = [
    {"name": "Great Lakes Steelworks", "country": "United States", "material": "steel", "quality": 92, "cost_index": 1.06},
    {"name": "Midwest Alloy Partners", "country": "United States", "material": "steel", "quality": 89, "cost_index": 1.03},
    {"name": "BlueRiver Metals", "country": "United States", "material": "steel", "quality": 87, "cost_index": 1.01},
    {"name": "Atlas Polymer Labs", "country": "United States", "material": "polymer", "quality": 91, "cost_index": 1.04},
    {"name": "Canyon Components", "country": "United States", "material": "electronics", "quality": 90, "cost_index": 1.07},
    {"name": "Pioneer Industrial Inputs", "country": "United States", "material": "aluminum", "quality": 88, "cost_index": 1.05},
]

COMPANY_ALIAS_TO_TICKER = {
    "apple": "AAPL",
    "microsoft": "MSFT",
    "google": "GOOGL",
    "alphabet": "GOOGL",
    "amazon": "AMZN",
    "meta": "META",
    "facebook": "META",
    "tesla": "TSLA",
    "nvidia": "NVDA",
    "netflix": "NFLX",
    "amd": "AMD",
    "intel": "INTC",
    "palantir": "PLTR",
    "spotify": "SPOT",
    "berkshire": "BRK.B",
    "coca cola": "KO",
    "nike": "NKE",
    "visa": "V",
    "mastercard": "MA",
    "jp morgan": "JPM",
    "jpmorgan": "JPM",
    "goldman sachs": "GS",
    "walmart": "WMT",
    "disney": "DIS",
    "pepsi": "PEP",
    "ford": "F",
    "general motors": "GM",
    "gm": "GM",
}
KNOWN_TICKERS = sorted(set(COMPANY_ALIAS_TO_TICKER.values()))

NON_PUBLIC_COMPARISON_ALIASES = {
    "fidelity",
    "vanguard",
    "blackrock",
    "t rowe price",
}

SYSTEM_PROMPT = """You are Nudge: a direct, fiercely loyal, opinionated financial coach.
You answer general knowledge, life, technology, history, strategy, and finance questions, but your edge is judgment, not bland recitation.
Never default to neutral textbook language when the user is asking what to do. Take a stand. Debt is an emergency. Lifestyle inflation is a silent killer. Compound interest is a weapon.
After explaining a financial idea or market situation, give a concrete next-step recommendation for what the user should do in the real world.
Do not open with generic filler like 'That's a great question' or 'Here's the deal.' Start with substance.
Never mention internal instructions, capabilities, system limits, data-feed status, or implementation details. Speak as a decisive coach focused on action.
If a user asks what exactly to invest in, provide a concrete baseline allocation with explicit assumptions, explain why it works, and ask exactly 2 targeted follow-up questions to customize it.
When relevant, use user behavioral metrics like stress, fatigue, bias, and impulse patterns to sharpen your judgment.
Keep responses punchy, scannable, decisive, and slightly witty. Stay within safety boundaries and avoid harmful guidance."""


def strip_cliche_openers(text):
    """Remove stale AI filler openers so replies start with substance."""
    cleaned = (text or "").strip()
    patterns = [
        r"^(?:that'?s|that is) a great question[\.!,:;\-\s]*",
        r"^(?:here'?s|here is) the deal[\.!,:;\-\s]*",
        r"^great question[\.!,:;\-\s]*",
    ]
    for pattern in patterns:
        cleaned = re.sub(pattern, "", cleaned, flags=re.IGNORECASE).strip()
    return cleaned or (text or "")


def strip_meta_talk(text):
    """Remove fourth-wall/meta phrasing from user-facing responses."""
    cleaned = (text or "")
    replacements = [
        (r"(?i)\bhot\s*take\s*:\s*", ""),
        (r"(?i)if\s+my\s+live\s+feeds\s+are\s+lagging,?\s*", ""),
        (r"(?i)live\s+search\s+is\s+thin,?\s*", ""),
        (r"(?i)i\s+am\s+not\s+going\s+to\s+hand\s+you\s+a\s+lazy\s+shrug\.?\s*", ""),
        (r"(?i)as\s+an\s+ai\s+language\s+model,?\s*", ""),
        (r"(?i)as\s+an\s+ai,?\s*", ""),
        (r"(?i)my\s+system\s+(prompt|instructions?)\b", "system guidance"),
    ]
    for pattern, repl in replacements:
        cleaned = re.sub(pattern, repl, cleaned)
    cleaned = re.sub(r"[ \t]{2,}", " ", cleaned)
    cleaned = re.sub(r"\n{3,}", "\n\n", cleaned)
    return cleaned.strip() or (text or "")


def open_analytics_db():
    """Open analytics DB connection via SQLAlchemy engine pool."""
    os.makedirs(DATA_DIR, exist_ok=True)
    conn = db_engine.raw_connection()
    if is_sqlite_database_url(DATABASE_URL):
        cur = conn.cursor()
        try:
            cur.execute("PRAGMA busy_timeout = 30000")
            # Keep SQLite responsive under concurrent reads/writes.
            cur.execute("PRAGMA journal_mode=WAL")
        finally:
            cur.close()
    return conn


def is_sqlite_database_url(url):
    """Return True when SQLAlchemy URL points to SQLite."""
    return (url or "").strip().lower().startswith("sqlite")


def infer_db_backend_label(url):
    """Return a stable backend label for diagnostics and logs."""
    lowered = (url or "").strip().lower()
    if lowered.startswith("postgresql") or lowered.startswith("postgres"):
        return "postgresql"
    if lowered.startswith("sqlite"):
        return "sqlite"
    if not lowered:
        return "unknown"
    return "other"


def is_render_runtime():
    return bool(
        (os.getenv("RENDER") or "").strip()
        or (os.getenv("RENDER_SERVICE_ID") or "").strip()
        or (os.getenv("RENDER_EXTERNAL_URL") or "").strip()
    )


def warn_if_sqlite_in_production():
    """Highlight high-concurrency DB risk when production falls back to SQLite."""
    if not is_sqlite_database_url(DATABASE_URL):
        return
    if not is_render_runtime():
        return
    print(
        "[DB-RISK] Running on SQLite in Render runtime (journal_mode=WAL). "
        "Prioritize PostgreSQL cutover now for multi-user guardrails/sweeps.",
        flush=True,
    )


def build_db_engine():
    """Create SQLAlchemy engine with connection pooling."""
    connect_args = {}
    kwargs = {
        "pool_pre_ping": True,
        "future": True,
    }

    if is_sqlite_database_url(DATABASE_URL):
        connect_args.update({"timeout": 30, "check_same_thread": False})
        kwargs.update(
            {
                "poolclass": QueuePool,
                "pool_size": DB_POOL_SIZE,
                "max_overflow": DB_MAX_OVERFLOW,
            }
        )
    else:
        kwargs.update(
            {
                "pool_size": DB_POOL_SIZE,
                "max_overflow": DB_MAX_OVERFLOW,
                "pool_recycle": DB_POOL_RECYCLE_SECONDS,
            }
        )

    return create_engine(DATABASE_URL, connect_args=connect_args, **kwargs)


db_engine = build_db_engine()
SessionLocal = sessionmaker(bind=db_engine, autoflush=False, autocommit=False, future=True)
DB_BACKEND = infer_db_backend_label(DATABASE_URL)
warn_if_sqlite_in_production()


def ensure_storage_dirs():
    """Ensure persistent storage folders exist."""
    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(USER_MEMORY_DIR, exist_ok=True)
    os.makedirs(UPLOADS_DIR, exist_ok=True)
    ensure_analytics_db()


def ensure_analytics_db():
    """Initialize SQL tables used by the analytical finance engine."""
    os.makedirs(DATA_DIR, exist_ok=True)
    if not is_sqlite_database_url(DATABASE_URL):
        from db_models import Base

        Base.metadata.create_all(bind=db_engine)
        return
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS spend_events (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id TEXT NOT NULL,
                    amount REAL NOT NULL,
                    category TEXT NOT NULL,
                    day_of_week TEXT NOT NULL,
                    hour INTEGER NOT NULL,
                    stress_level TEXT NOT NULL,
                    created_at TEXT NOT NULL
                )
                """
            )
            cur.execute(
                """
                CREATE INDEX IF NOT EXISTS idx_spend_events_user_created
                ON spend_events(user_id, created_at)
                """
            )
            cur.execute(
                """
                CREATE INDEX IF NOT EXISTS idx_spend_events_user_category_amount
                ON spend_events(user_id, category, amount)
                """
            )
            # Safe schema migration for existing databases.
            try:
                cur.execute("ALTER TABLE spend_events ADD COLUMN fatigue_score INTEGER")
            except Exception:
                pass
            try:
                cur.execute("ALTER TABLE spend_events ADD COLUMN cognitive_bias TEXT")
            except Exception:
                pass
            try:
                cur.execute("ALTER TABLE spend_events ADD COLUMN transaction_type TEXT")
            except Exception:
                pass
            try:
                cur.execute("ALTER TABLE spend_events ADD COLUMN friction_seconds INTEGER")
            except Exception:
                pass
            try:
                cur.execute("ALTER TABLE spend_events ADD COLUMN inferred_tone TEXT")
            except Exception:
                pass
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS subscriptions (
                    user_id TEXT NOT NULL,
                    name TEXT NOT NULL,
                    monthly_cost REAL NOT NULL,
                    days_since_last_use INTEGER NOT NULL,
                    updated_at TEXT NOT NULL,
                    PRIMARY KEY (user_id, name)
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS savings_goals (
                    user_id TEXT PRIMARY KEY,
                    name TEXT NOT NULL,
                    amount REAL NOT NULL,
                    updated_at TEXT NOT NULL
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS supplier_profiles (
                    user_id TEXT NOT NULL,
                    name TEXT NOT NULL,
                    country TEXT NOT NULL,
                    material TEXT NOT NULL,
                    quality_score REAL NOT NULL,
                    spend_share REAL NOT NULL,
                    updated_at TEXT NOT NULL,
                    PRIMARY KEY (user_id, name)
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS horizon_scan_events (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id TEXT NOT NULL,
                    event_type TEXT NOT NULL,
                    headline TEXT NOT NULL,
                    source_url TEXT NOT NULL,
                    estimated_cogs_impact REAL NOT NULL,
                    created_at TEXT NOT NULL
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS user_states (
                    user_id TEXT PRIMARY KEY,
                    state_json TEXT NOT NULL,
                    updated_at TEXT NOT NULL
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS guardrail_overrides (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id TEXT NOT NULL,
                    category TEXT NOT NULL,
                    created_at TEXT NOT NULL
                )
                """
            )
            cur.execute(
                """
                CREATE INDEX IF NOT EXISTS idx_guardrail_overrides_user_created
                ON guardrail_overrides(user_id, created_at)
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS cancellation_sends (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id TEXT NOT NULL,
                    service_name TEXT NOT NULL,
                    draft_subject TEXT NOT NULL,
                    draft_body TEXT NOT NULL,
                    confirmation_ts TEXT NOT NULL
                )
                """
            )
            cur.execute(
                """
                CREATE INDEX IF NOT EXISTS idx_cancellation_sends_user_ts
                ON cancellation_sends(user_id, confirmation_ts)
                """
            )
            conn.commit()
        finally:
            conn.close()


def utc_now_iso():
    """UTC timestamp in ISO-8601 with timezone info."""
    return datetime.now(timezone.utc).isoformat()


def normalize_case(text):
    """Unicode-aware lowercasing to handle uppercase variations robustly."""
    return (text or "").casefold()


def is_greeting_like_message(user_message, normalized_text=""):
    """Detect greeting intents including elongated variants like 'hellooo' or 'heyyyy'."""
    raw = normalize_case(user_message).strip()
    tokens = set(re.findall(r"[a-z']+", normalized_text or ""))
    if tokens.intersection({"hello", "hi", "hey", "yo", "sup", "hola"}):
        return True

    elongated_patterns = [
        r"\bhe+l+o+\b",
        r"\bhe+y+\b",
        r"\bhi+i+\b",
        r"\byo+\b",
        r"\bsu+p+\b",
        r"\bhola+a*\b",
    ]
    return any(re.search(p, raw) for p in elongated_patterns)


def load_json_file(path, default_value):
    """Load generic JSON file with safe fallback."""
    if not os.path.exists(path):
        return default_value
    try:
        with open(path, "r") as f:
            payload = json.load(f)
        if isinstance(default_value, dict) and isinstance(payload, dict):
            return payload
        if isinstance(default_value, list) and isinstance(payload, list):
            return payload
    except Exception:
        pass
    return default_value


def save_json_file(path, payload):
    """Save JSON with atomic-ish write semantics for small local files."""
    ensure_storage_dirs()
    tmp = f"{path}.tmp"
    with open(tmp, "w") as f:
        json.dump(payload, f, indent=2)
    os.replace(tmp, path)


def reject_large_request(limit_bytes=MAX_JSON_BODY_BYTES):
    """Simple request-size guard."""
    content_len = request.content_length or 0
    return content_len > limit_bytes


def strip_rtf_text(raw_text):
    """Best-effort RTF to plain text conversion without external deps."""
    text = re.sub(r"\\'[0-9a-fA-F]{2}", " ", raw_text or "")
    text = re.sub(r"\\par[d]?", "\n", text)
    text = re.sub(r"\\[a-zA-Z]+-?\d* ?", " ", text)
    text = text.replace("{", " ").replace("}", " ")
    return re.sub(r"\s+", " ", text).strip()


def extract_docx_text(file_bytes):
    """Extract text from docx using built-in zip/xml support."""
    try:
        with zipfile.ZipFile(io.BytesIO(file_bytes)) as zf:
            xml_payload = zf.read("word/document.xml").decode("utf-8", errors="ignore")
        xml_payload = re.sub(r"</w:p>", "\n", xml_payload)
        xml_payload = re.sub(r"<[^>]+>", " ", xml_payload)
        return re.sub(r"\s+", " ", unescape(xml_payload)).strip()
    except Exception:
        return ""


def extract_pdf_text(file_bytes):
    """Best-effort text extraction from PDF byte streams without extra packages."""
    try:
        text_chunks = []
        for chunk in re.findall(rb"\(([^()]*)\)\s*Tj", file_bytes):
            decoded = chunk.decode("latin-1", errors="ignore")
            if decoded.strip():
                text_chunks.append(decoded)
        if not text_chunks:
            for chunk in re.findall(rb"\[(.*?)\]\s*TJ", file_bytes, flags=re.DOTALL):
                decoded = re.sub(rb"<[^>]+>", b" ", chunk).decode("latin-1", errors="ignore")
                if decoded.strip():
                    text_chunks.append(decoded)
        text = " ".join(text_chunks)
        return re.sub(r"\s+", " ", text).strip()
    except Exception:
        return ""


def extract_upload_text(file_name, mime_type, file_bytes):
    """Extract analyzable text from common document uploads."""
    name = normalize_case(file_name or "")
    mime = normalize_case(mime_type or "")
    if name.endswith((".txt", ".csv")) or mime.startswith("text/"):
        return file_bytes.decode("utf-8", errors="ignore").strip()
    if name.endswith(".rtf"):
        return strip_rtf_text(file_bytes.decode("utf-8", errors="ignore"))
    if name.endswith(".docx") or "wordprocessingml" in mime:
        return extract_docx_text(file_bytes)
    if name.endswith(".pdf") or mime == "application/pdf":
        return extract_pdf_text(file_bytes)
    return ""


def analyze_image_upload(file_name, mime_type, file_bytes):
    """Use the model for a compact image analysis with metadata fallback."""
    size_kb = max(1, len(file_bytes) // 1024)
    if not mime_type.startswith("image/"):
        return f"Attached file {file_name} ({mime_type or 'unknown type'}, {size_kb} KB)."

    try:
        b64 = base64.b64encode(file_bytes).decode("ascii")
        data_url = f"data:{mime_type};base64,{b64}"
        response = frontier_client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[
                {"role": "system", "content": "Analyze the uploaded image briefly. Mention the main subject, visible text if any, and likely context in under 90 words."},
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": f"Analyze this uploaded image named {file_name}."},
                        {"type": "image_url", "image_url": {"url": data_url}},
                    ],
                },
            ],
            temperature=0.2,
            max_tokens=180,
        )
        content = (response.choices[0].message.content or "").strip()
        if content:
            return f"Image {file_name}: {content}"
    except Exception:
        pass
    return f"Image {file_name} attached ({size_kb} KB). I could not deeply inspect the pixels, but I received it successfully."


def analyze_uploaded_files(uploaded_files):
    """Return a compact analysis summary for uploaded files."""
    summaries = []
    if not uploaded_files:
        return summaries

    for storage in uploaded_files[:MAX_CHAT_ATTACHMENTS]:
        try:
            file_name = (storage.filename or "upload").strip() or "upload"
            mime_type = (storage.mimetype or "application/octet-stream").strip().lower()
            file_bytes = storage.read()
            if not file_bytes:
                continue
            if len(file_bytes) > MAX_ATTACHMENT_BYTES:
                summaries.append(f"File {file_name} was skipped because it exceeds the {MAX_ATTACHMENT_BYTES // (1024 * 1024)} MB limit.")
                continue

            if mime_type.startswith("image/"):
                summaries.append(analyze_image_upload(file_name, mime_type, file_bytes))
                continue

            extracted = extract_upload_text(file_name, mime_type, file_bytes)
            if extracted:
                excerpt = extracted[:1800]
                summaries.append(f"Document {file_name} content summary:\n{excerpt}")
            else:
                size_kb = max(1, len(file_bytes) // 1024)
                summaries.append(f"Attached file {file_name} ({mime_type or 'unknown type'}, {size_kb} KB). I received it, but could not extract readable content from this format.")
        finally:
            try:
                storage.close()
            except Exception:
                pass
    return summaries
def client_ip():
    forwarded = (request.headers.get("X-Forwarded-For") or "").split(",")[0].strip()
    return forwarded or (request.remote_addr or "unknown")


def is_rate_limited(scope, max_hits=AUTH_RATE_LIMIT_MAX, window_seconds=AUTH_RATE_LIMIT_WINDOW):
    """In-memory rate limiter keyed by scope and client IP."""
    now = time.time()
    key = f"{scope}:{client_ip()}"
    with auth_rate_limit_lock:
        hits = auth_rate_limit_hits.get(key, [])
        hits = [t for t in hits if now - t <= window_seconds]
        if len(hits) >= max_hits:
            auth_rate_limit_hits[key] = hits
            return True
        hits.append(now)
        auth_rate_limit_hits[key] = hits
    return False


def is_user_rate_limited(user_id, scope="chat", max_hits=CHAT_USER_RATE_LIMIT_MAX, window_seconds=CHAT_USER_RATE_LIMIT_WINDOW):
    """In-memory limiter keyed by user id, with IP fallback for guest sessions."""
    now = time.time()
    safe_user_id = sanitize_user_id(user_id)
    if safe_user_id == DEFAULT_USER_ID:
        safe_user_id = f"{safe_user_id}:{client_ip()}"
    key = f"user:{scope}:{safe_user_id}"
    with auth_rate_limit_lock:
        hits = auth_rate_limit_hits.get(key, [])
        hits = [t for t in hits if now - t <= window_seconds]
        if len(hits) >= max_hits:
            auth_rate_limit_hits[key] = hits
            return True
        hits.append(now)
        auth_rate_limit_hits[key] = hits
    return False


def default_history():
    return [{"role": "system", "content": SYSTEM_PROMPT}]


def sanitize_user_id(user_id):
    """Normalize user ids for safe file storage."""
    raw = (user_id or DEFAULT_USER_ID).strip().lower()
    safe = re.sub(r"[^a-z0-9_-]", "_", raw)
    safe = re.sub(r"_+", "_", safe).strip("_")
    return safe[:64] or DEFAULT_USER_ID


def user_state_path(user_id):
    return os.path.join(USER_MEMORY_DIR, f"{sanitize_user_id(user_id)}.json")


def default_user_state():
    return {
        "history": default_history(),
        "profile": {
            "name": "",
            "email_hash": "",
            "registered_at": "",
            "accountability_target": "",
        },
        "preferences": {
            "response_style": "concise",
            "tone": "warm",
            "explanation_level": "balanced",
            "prefer_citations": False,
        },
        "feedback_log": [],
        "fact_notes": [],
        "qa_memory": [],
        "learned_topics": {},
        "tone_memory": {
            "funny": 0,
            "supportive": 0,
            "formal": 0,
            "direct": 0,
            "neutral": 0,
        },
        "finance_profile": {
            "watchlist": [],
            "watchlist_last_checked": "",
            "watchlist_last_snapshot": [],
            "cash_management": {
                "checking_balance_usd": 0.0,
                "hysa_balance_usd": 0.0,
                "hysa_apy": 0.045,
                "last_idle_cash_sweep_at": "",
                "last_idle_cash_sweep_amount": 0.0,
                "hysa_auto_sweep_enabled": False,
                "hysa_auto_sweep_enabled_at": "",
            },
            "runway_buffer_profile": {
                "base_city": BASELINE_COST_INDEX_CITY,
                "current_city": "",
                "capital_usd": 0.0,
                "base_monthly_cap_usd": 0.0,
                "shadow_runway_enabled": False,
                "safety_buffer_months": 0.0,
                "updated_at": "",
            },
        },
        "subscription_profile": {
            "items": [],
            "savings_goal": {
                "name": "",
                "amount": 0.0,
            },
            "last_alert_at": "",
            "last_vampire_scan_at": "",
            "vampire_alerts": [],
            "pending_cancellation_review": {},
        },
        "behavior_budget_profile": {
            "spend_events": [],
            "last_coach_alert_at": "",
            "last_daily_alert_date": "",
            "auto_sweep_enabled": True,
            "auto_sweep_target": "investment index",
            "locked_categories": [],
            "break_lock_confirm_category": "",
            "break_lock_confirm_until": "",
            "break_lock_confirm_step": 0,
            "opportunity_cost_threshold_usd": OPPORTUNITY_COST_THRESHOLD_USD,
            "opportunity_cost_default_years": OPPORTUNITY_COST_DEFAULT_YEARS,
            "opportunity_cost_default_annual_return": OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN,
            "last_opportunity_cost_gate": {},
            "circuit_breaker_active": False,
            "circuit_breaker_until": "",
            "last_purchase_psychology": {},
            "last_dopamine_swap_offer": {},
        },
        "geopolitical_profile": {
            "suppliers": [],
            "last_scan_at": "",
            "last_scan_summary": "",
        },
    }


def load_user_state(user_id):
    """Load per-user memory and preferences."""
    ensure_storage_dirs()
    safe_user_id = sanitize_user_id(user_id)
    migrated_from_legacy = False
    try:
        with analytics_db_lock:
            conn = open_analytics_db()
            try:
                cur = conn.cursor()
                cur.execute("SELECT state_json FROM user_states WHERE user_id = ?", (safe_user_id,))
                row = cur.fetchone()
            finally:
                conn.close()

        if row and row[0]:
            data = json.loads(row[0])
        else:
            path = user_state_path(safe_user_id)
            if not os.path.exists(path):
                return default_user_state()
            with open(path, "r") as f:
                data = json.load(f)
            migrated_from_legacy = True
        if not isinstance(data, dict):
            return default_user_state()
        data, encryption_upgrade_needed = decrypt_sensitive_state_fields(data)
        state = default_user_state()
        state.update(data)
        if not isinstance(state.get("history"), list) or not state["history"]:
            state["history"] = default_history()
        if not isinstance(state.get("profile"), dict):
            state["profile"] = default_user_state()["profile"]
        profile = state.get("profile") or {}
        profile["accountability_target"] = (profile.get("accountability_target") or "").strip()
        state["profile"] = profile
        if not isinstance(state.get("preferences"), dict):
            state["preferences"] = default_user_state()["preferences"]
        if not isinstance(state.get("feedback_log"), list):
            state["feedback_log"] = []
        if not isinstance(state.get("fact_notes"), list):
            state["fact_notes"] = []
        if not isinstance(state.get("qa_memory"), list):
            state["qa_memory"] = []
        if not isinstance(state.get("learned_topics"), dict):
            state["learned_topics"] = {}
        if not isinstance(state.get("tone_memory"), dict):
            state["tone_memory"] = default_user_state()["tone_memory"]
        if not isinstance(state.get("finance_profile"), dict):
            state["finance_profile"] = default_user_state()["finance_profile"]
        finance_profile = state.get("finance_profile") or {}
        if not isinstance(finance_profile.get("watchlist"), list):
            finance_profile["watchlist"] = []
        if not isinstance(finance_profile.get("watchlist_last_snapshot"), list):
            finance_profile["watchlist_last_snapshot"] = []
        if not isinstance(finance_profile.get("watchlist_last_checked"), str):
            finance_profile["watchlist_last_checked"] = ""
        state["finance_profile"] = finance_profile

        if not isinstance(state.get("subscription_profile"), dict):
            state["subscription_profile"] = default_user_state()["subscription_profile"]
        subscription_profile = state.get("subscription_profile") or {}
        if not isinstance(subscription_profile.get("items"), list):
            subscription_profile["items"] = []
        goal = subscription_profile.get("savings_goal")
        if not isinstance(goal, dict):
            goal = {"name": "", "amount": 0.0}
        goal_name = (goal.get("name") or "").strip()
        try:
            goal_amount = float(goal.get("amount") or 0.0)
        except Exception:
            goal_amount = 0.0
        goal["name"] = goal_name
        goal["amount"] = max(0.0, goal_amount)
        subscription_profile["savings_goal"] = goal
        if not isinstance(subscription_profile.get("last_alert_at"), str):
            subscription_profile["last_alert_at"] = ""
        state["subscription_profile"] = subscription_profile

        if not isinstance(state.get("behavior_budget_profile"), dict):
            state["behavior_budget_profile"] = default_user_state()["behavior_budget_profile"]
        behavior_profile = state.get("behavior_budget_profile") or {}
        if not isinstance(behavior_profile.get("spend_events"), list):
            behavior_profile["spend_events"] = []
        if not isinstance(behavior_profile.get("last_coach_alert_at"), str):
            behavior_profile["last_coach_alert_at"] = ""
        if not isinstance(behavior_profile.get("last_daily_alert_date"), str):
            behavior_profile["last_daily_alert_date"] = ""
        if not isinstance(behavior_profile.get("auto_sweep_enabled"), bool):
            behavior_profile["auto_sweep_enabled"] = True
        auto_target = (behavior_profile.get("auto_sweep_target") or "").strip()
        behavior_profile["auto_sweep_target"] = auto_target or "investment index"
        state["behavior_budget_profile"] = behavior_profile

        if not isinstance(state.get("geopolitical_profile"), dict):
            state["geopolitical_profile"] = default_user_state()["geopolitical_profile"]
        geo_profile = state.get("geopolitical_profile") or {}
        if not isinstance(geo_profile.get("suppliers"), list):
            geo_profile["suppliers"] = []
        if not isinstance(geo_profile.get("last_scan_at"), str):
            geo_profile["last_scan_at"] = ""
        if not isinstance(geo_profile.get("last_scan_summary"), str):
            geo_profile["last_scan_summary"] = ""
        state["geopolitical_profile"] = geo_profile
        if migrated_from_legacy or encryption_upgrade_needed:
            save_user_state(safe_user_id, state)
        return state
    except Exception:
        return default_user_state()


def infer_user_tone(user_message):
    """Infer user vibe so replies can mirror tone while staying helpful."""
    text = normalize_case(user_message).strip()
    if not text:
        return "neutral"

    sad_markers = [
        "i feel sad", "i am sad", "depressed", "lonely", "empty", "heartbroken",
        "anxious", "overwhelmed", "tired of everything", "i want to cry", "i am crying",
        "stressed", "i feel down", "not okay"
    ]
    funny_markers = [
        "lol", "lmao", "haha", "jajaja", "bro", "bruh", "meme", "roast", "joke",
        "funny", "goofy", "wild"
    ]
    formal_markers = [
        "therefore", "please provide", "could you explain", "in detail", "kindly",
        "would you", "however", "furthermore"
    ]
    direct_markers = [
        "quick", "short answer", "just answer", "no explanation", "tldr", "fast"
    ]

    if any(m in text for m in sad_markers):
        return "supportive"
    if re.search(r"\b(sad|depressed|lonely|heartbroken|anxious|overwhelmed|stressed|crying|down|not\s+okay)\b", text):
        return "supportive"
    if any(m in text for m in funny_markers):
        return "funny"
    if any(m in text for m in formal_markers):
        return "formal"
    if any(m in text for m in direct_markers):
        return "direct"

    if re.search(r"[!?]{2,}", text):
        return "funny"
    if len(text.split()) > 18:
        return "formal"
    return "neutral"


def tone_instruction_for(tone_label):
    """Map tone labels to behavioral guidance."""
    mapping = {
        "supportive": "Use a warm, empathetic, reassuring tone. Validate feelings first, then answer clearly.",
        "funny": "Match a playful, light vibe with mild humor while still answering accurately.",
        "formal": "Use a clear, professional, structured tone.",
        "direct": "Be concise and direct. Prioritize the answer first.",
        "neutral": "Use a friendly and balanced tone.",
    }
    return mapping.get(tone_label, mapping["neutral"])


def apply_tone_style(reply_text, user_message):
    """Post-process reply to mirror tone while preserving factual content."""
    tone = infer_user_tone(user_message)
    text = strip_meta_talk(strip_cliche_openers((reply_text or "").strip()))
    if not text:
        return text

    if tone == "supportive":
        if not text.lower().startswith(("i hear you", "that sounds hard", "i am here")):
            return f"I hear you. {text}"
        return text

    if tone == "funny":
        if "lol" not in text.lower() and "haha" not in text.lower():
            return f"Haha, got you. {text}"
        return text

    if tone == "formal":
        return text

    if tone == "direct":
        first_sentence = re.split(r"(?<=[.!?])\s+", text)[0].strip()
        return first_sentence or text

    return text


def save_user_state(user_id, state):
    """Persist per-user memory and preferences."""
    ensure_storage_dirs()
    safe_user_id = sanitize_user_id(user_id)
    try:
        encrypted_state = encrypt_sensitive_state_fields(state)
        with analytics_db_lock:
            conn = open_analytics_db()
            try:
                conn.execute(
                    """
                    INSERT INTO user_states (user_id, state_json, updated_at)
                    VALUES (?, ?, ?)
                    ON CONFLICT(user_id) DO UPDATE SET
                        state_json=excluded.state_json,
                        updated_at=excluded.updated_at
                    """,
                    (safe_user_id, json.dumps(encrypted_state), utc_now_iso()),
                )
                conn.commit()
            finally:
                conn.close()
    except Exception as e:
        print(f"Warning: Could not save user state: {e}")


def load_learning_memory():
    """Load global learning signals from feedback across users."""
    ensure_storage_dirs()
    if not os.path.exists(LEARNING_FILE):
        return {
            "style_votes": {},
            "feedback_examples": [],
            "idle_knowledge": {},
            "idle_runs": 0,
            "last_idle_run": "",
        }
    try:
        with open(LEARNING_FILE, "r") as f:
            payload = json.load(f)
        if not isinstance(payload, dict):
            return {
                "style_votes": {},
                "feedback_examples": [],
                "idle_knowledge": {},
                "idle_runs": 0,
                "last_idle_run": "",
            }
        payload.setdefault("style_votes", {})
        payload.setdefault("feedback_examples", [])
        payload.setdefault("idle_knowledge", {})
        payload.setdefault("idle_runs", 0)
        payload.setdefault("last_idle_run", "")
        return payload
    except Exception:
        return {
            "style_votes": {},
            "feedback_examples": [],
            "idle_knowledge": {},
            "idle_runs": 0,
            "last_idle_run": "",
        }


def save_learning_memory(memory):
    """Persist global learning memory."""
    ensure_storage_dirs()
    try:
        with open(LEARNING_FILE, "w") as f:
            json.dump(memory, f, indent=2)
    except Exception as e:
        print(f"Warning: Could not save learning memory: {e}")


def parse_bool(value, default=True):
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() not in {"0", "false", "off", "no"}
    return bool(value)


def sanitize_email(email):
    return normalize_case((email or "").strip())


def is_valid_email(email):
    if not email or len(email) > 254:
        return False
    return re.match(r"^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}$", email) is not None


def is_valid_display_name(name):
    cleaned = (name or "").strip()
    if not cleaned or len(cleaned) > 70:
        return False
    return re.match(r"^[A-Za-z0-9 _.'-]{2,70}$", cleaned) is not None


def is_valid_password(password):
    """Enforce baseline password policy for local auth."""
    raw = password or ""
    return len(raw) >= 8 and len(raw) <= 128


def hash_password(password):
    """Hash plaintext password with bcrypt."""
    return bcrypt.hashpw((password or "").encode("utf-8"), bcrypt.gensalt()).decode("utf-8")


def verify_password(password, password_hash):
    """Verify plaintext password against bcrypt hash."""
    raw_hash = (password_hash or "").encode("utf-8")
    if not raw_hash:
        return False
    try:
        return bcrypt.checkpw((password or "").encode("utf-8"), raw_hash)
    except Exception:
        return False


def email_hash(email):
    payload = f"{APP_SECRET}:{sanitize_email(email)}".encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def derive_user_id_from_email(email):
    h = email_hash(email)
    return sanitize_user_id(f"u_{h[:18]}")


def load_accounts():
    return load_json_file(ACCOUNTS_FILE, {})


def save_accounts(accounts):
    save_json_file(ACCOUNTS_FILE, accounts)


def load_sessions():
    return load_json_file(SESSIONS_FILE, {})


def save_sessions(sessions):
    save_json_file(SESSIONS_FILE, sessions)


def cleanup_expired_sessions(sessions=None):
    if sessions is None:
        sessions = load_sessions()
    now = time.time()
    alive = {}
    for token_hash, record in sessions.items():
        exp = float((record or {}).get("expires_at", 0))
        if exp > now:
            alive[token_hash] = record
    if len(alive) != len(sessions):
        save_sessions(alive)
    return alive


def _create_token_record(sessions, user_id, token_type, ttl_seconds):
    """Create and store hashed token record."""
    raw_token = secrets.token_urlsafe(48 if token_type == "refresh" else 32)
    token_hash = hashlib.sha256(raw_token.encode("utf-8")).hexdigest()
    sessions[token_hash] = {
        "user_id": sanitize_user_id(user_id),
        "token_type": token_type,
        "issued_at": utc_now_iso(),
        "expires_at": time.time() + int(ttl_seconds),
    }
    return raw_token


def create_auth_tokens_for_user(user_id):
    """Create short-lived access token and refresh token pair."""
    sessions = cleanup_expired_sessions()
    access_token = _create_token_record(sessions, user_id, "access", ACCESS_TOKEN_TTL_SECONDS)
    refresh_token = _create_token_record(sessions, user_id, "refresh", REFRESH_TOKEN_TTL_SECONDS)
    save_sessions(sessions)
    return access_token, refresh_token


def create_session_for_user(user_id):
    """Legacy wrapper returning access token for backwards compatibility."""
    access_token, _refresh_token = create_auth_tokens_for_user(user_id)
    return access_token


def _resolve_user_from_cookie(cookie_name, expected_type):
    raw_token = request.cookies.get(cookie_name) or ""
    if not raw_token:
        return "", "", {}
    token_hash = hashlib.sha256(raw_token.encode("utf-8")).hexdigest()
    sessions = cleanup_expired_sessions()
    record = sessions.get(token_hash) or {}
    record_type = record.get("token_type") or "access"
    if record and record_type == expected_type:
        return sanitize_user_id(record.get("user_id") or ""), token_hash, sessions
    return "", token_hash, sessions


def resolve_session_user_id():
    user_id, _token_hash, _sessions = _resolve_user_from_cookie("ai_access", "access")
    if user_id:
        return user_id
    # Legacy fallback cookie support.
    user_id, _token_hash, _sessions = _resolve_user_from_cookie("ai_session", "access")
    return user_id


def refresh_tokens_from_refresh_cookie():
    """Rotate refresh token and issue a new access/refresh pair."""
    user_id, token_hash, sessions = _resolve_user_from_cookie("ai_refresh", "refresh")
    if not user_id:
        return "", ""

    if token_hash in sessions:
        del sessions[token_hash]
    save_sessions(sessions)
    return create_auth_tokens_for_user(user_id)


def revoke_token_cookie(cookie_name, expected_type):
    """Revoke a token from storage based on cookie value."""
    raw_token = request.cookies.get(cookie_name) or ""
    if not raw_token:
        return
    token_hash = hashlib.sha256(raw_token.encode("utf-8")).hexdigest()
    sessions = cleanup_expired_sessions()
    record = sessions.get(token_hash) or {}
    record_type = record.get("token_type") or "access"
    if token_hash in sessions and record_type == expected_type:
        del sessions[token_hash]
        save_sessions(sessions)


def set_auth_cookies(response, access_token, refresh_token):
    """Set secure access and refresh cookies."""
    response.set_cookie(
        "ai_access",
        access_token,
        max_age=ACCESS_TOKEN_TTL_SECONDS,
        httponly=True,
        samesite="Lax",
        secure=COOKIE_SECURE,
        path="/",
    )
    response.set_cookie(
        "ai_refresh",
        refresh_token,
        max_age=REFRESH_TOKEN_TTL_SECONDS,
        httponly=True,
        samesite="Lax",
        secure=COOKIE_SECURE,
        path="/",
    )


def clear_session_cookie(response):
    response.delete_cookie("ai_access", path="/")
    response.delete_cookie("ai_refresh", path="/")
    response.delete_cookie("ai_session", path="/")


def clear_legacy_session_cookie(response):
    response.delete_cookie("ai_session", path="/")


def mark_user_activity():
    """Track latest user activity for idle-learning scheduling."""
    global last_user_activity_ts
    last_user_activity_ts = time.time()


def list_user_state_files():
    """Return user state files from persistent storage."""
    ensure_storage_dirs()
    try:
        return [
            os.path.join(USER_MEMORY_DIR, name)
            for name in os.listdir(USER_MEMORY_DIR)
            if name.endswith(".json")
        ]
    except Exception:
        return []


def list_user_state_ids():
    """Return known user ids from SQLite plus any legacy JSON files."""
    ensure_storage_dirs()
    seen = set()
    try:
        with analytics_db_lock:
            conn = open_analytics_db()
            try:
                cur = conn.cursor()
                cur.execute("SELECT user_id FROM user_states")
                for row in cur.fetchall():
                    candidate = sanitize_user_id((row[0] or "").strip())
                    if candidate:
                        seen.add(candidate)
            finally:
                conn.close()
    except Exception:
        pass

    for path in list_user_state_files():
        name = os.path.basename(path)
        if name.endswith(".json"):
            seen.add(sanitize_user_id(name[:-5]))
    return sorted(seen)


def build_idle_knowledge_snippets(user_state, learning_memory, max_items=2):
    """Get short idle-collected knowledge snippets for this user's likely interests."""
    idle_knowledge = (learning_memory or {}).get("idle_knowledge") or {}
    if not idle_knowledge:
        return []

    topics = user_state.get("learned_topics") or {}
    ranked_topics = sorted(topics.items(), key=lambda x: x[1], reverse=True)

    snippets = []
    for topic, _score in ranked_topics:
        record = idle_knowledge.get(topic)
        if not isinstance(record, dict):
            continue
        summary = (record.get("summary") or "").strip()
        if not summary:
            continue
        snippets.append((topic, summary[:220]))
        if len(snippets) >= max_items:
            break
    return snippets


def prune_user_state_for_quality(user_state):
    """Keep useful memory and drop low-signal or low-quality old entries."""
    qa_memory = user_state.get("qa_memory") or []
    filtered = []
    for item in qa_memory:
        if not isinstance(item, dict):
            continue
        score = int(item.get("score", 0))
        uses = int(item.get("uses", 0))
        answer = (item.get("a") or "").strip()
        if not answer:
            continue
        if score <= -3 and uses <= 1:
            continue
        filtered.append(item)
    user_state["qa_memory"] = filtered[-300:]

    learned_topics = user_state.get("learned_topics") or {}
    if isinstance(learned_topics, dict) and len(learned_topics) > 80:
        trimmed = dict(sorted(learned_topics.items(), key=lambda x: x[1], reverse=True)[:80])
        user_state["learned_topics"] = trimmed

    return user_state


def gather_global_top_topics(limit=AUTO_LEARN_TOPIC_LIMIT):
    """Aggregate most discussed topics across all users."""
    combined = {}
    for user_id in list_user_state_ids():
        try:
            payload = load_user_state(user_id)
            topics = payload.get("learned_topics") or {}
            if not isinstance(topics, dict):
                continue
            for topic, score in topics.items():
                try:
                    combined[topic] = int(combined.get(topic, 0)) + int(score)
                except Exception:
                    continue
        except Exception:
            continue
    return [topic for topic, _ in sorted(combined.items(), key=lambda x: x[1], reverse=True)[:max(1, limit)]]


def fetch_idle_topic_summary(topic):
    """Fetch short, stable summary for a topic during idle time."""
    if not topic:
        return ""
    try:
        wiki = fetch_wikipedia_summary(topic, include_sources=False)
        if wiki and not is_weak_web_response(wiki):
            return wiki[:700]
    except Exception:
        pass
    try:
        web = get_web_search_reply(topic, include_sources=False)
        if web and not is_weak_web_response(web):
            return web[:700]
    except Exception:
        pass
    return ""


def run_idle_learning_cycle():
    """Run one autonomous maintenance + knowledge refresh cycle."""
    try:
        with idle_learning_lock:
            learning_memory = load_learning_memory()

            for user_id in list_user_state_ids():
                try:
                    state = load_user_state(user_id)
                    if not isinstance(state, dict):
                        continue
                    state = prune_user_state_for_quality(state)
                    state, _alerts = detect_subscription_vampires(state)
                    save_user_state(user_id, state)
                except Exception as e:
                    print(f"Warning: idle user-state refresh failed for {user_id}: {e}")

            idle_knowledge = learning_memory.get("idle_knowledge") or {}
            for topic in gather_global_top_topics(limit=AUTO_LEARN_TOPIC_LIMIT):
                try:
                    summary = fetch_idle_topic_summary(topic)
                except Exception as e:
                    print(f"Warning: idle topic summary failed for {topic}: {e}")
                    continue
                if not summary:
                    continue
                idle_knowledge[topic] = {
                    "summary": summary,
                    "ts": utc_now_iso(),
                }

            learning_memory["idle_knowledge"] = idle_knowledge
            learning_memory["idle_runs"] = int(learning_memory.get("idle_runs", 0)) + 1
            learning_memory["last_idle_run"] = utc_now_iso()
            save_learning_memory(learning_memory)
    except Exception as e:
        print(f"Warning: run_idle_learning_cycle failed: {e}")


def idle_learning_worker():
    """Background worker that learns only when the app is idle."""
    while True:
        time.sleep(max(30, AUTO_LEARN_INTERVAL_SECONDS))
        if not AUTO_LEARN_ENABLED:
            continue
        inactive_for = time.time() - last_user_activity_ts
        if inactive_for < AUTO_LEARN_IDLE_SECONDS:
            continue
        try:
            run_idle_learning_cycle()
        except Exception as e:
            print(f"Warning: Idle learning cycle failed: {e}")


def start_idle_learning_worker_once():
    """Start background autonomous learner once per process."""
    global idle_worker_started
    if idle_worker_started:
        return
    idle_worker_started = True
    t = threading.Thread(target=idle_learning_worker, daemon=True)
    t.start()


def cleanup_expired_upload_files():
    """Delete upload files older than retention threshold."""
    ensure_storage_dirs()
    retention_days = max(1, int(UPLOAD_RETENTION_DAYS))
    cutoff_ts = time.time() - (retention_days * 24 * 60 * 60)
    deleted = 0

    for root, _dirs, files in os.walk(UPLOADS_DIR):
        for name in files:
            path = os.path.join(root, name)
            try:
                mtime = os.path.getmtime(path)
                if mtime < cutoff_ts:
                    os.remove(path)
                    deleted += 1
            except FileNotFoundError:
                continue
            except Exception as e:
                print(f"Warning: Could not remove expired upload {path}: {e}")
    return deleted


def upload_cleanup_worker():
    """Background worker to enforce upload file retention."""
    while True:
        time.sleep(max(300, UPLOAD_CLEAN_INTERVAL_SECONDS))
        try:
            cleanup_expired_upload_files()
        except Exception as e:
            print(f"Warning: Upload cleanup cycle failed: {e}")


def start_upload_cleanup_worker_once():
    """Start upload cleanup worker once per process."""
    global upload_cleanup_worker_started
    if upload_cleanup_worker_started:
        return
    upload_cleanup_worker_started = True

    try:
        cleanup_expired_upload_files()
    except Exception as e:
        print(f"Warning: Initial upload cleanup failed: {e}")

    t = threading.Thread(target=upload_cleanup_worker, daemon=True)
    t.start()


def detect_feedback_payload(user_message):
    """Detect and structure feedback text from normal chat messages."""
    lowered = normalize_case(user_message).strip()
    feedback_prefix = ["/feedback", "feedback:", "fb:"]
    is_feedback = any(lowered.startswith(p) for p in feedback_prefix)
    implicit_feedback_markers = [
        "be shorter", "too long", "too short", "be more detailed", "be clearer",
        "be simpler", "too formal", "too casual", "with sources", "more citations",
        "that is wrong", "you are wrong", "incorrect", "not accurate", "please improve"
    ]
    if not is_feedback:
        is_feedback = any(m in lowered for m in implicit_feedback_markers)

    if not is_feedback:
        return {"is_feedback": False}

    content = user_message.strip()
    for p in feedback_prefix:
        if lowered.startswith(p):
            content = user_message[len(p):].strip(" :-")
            break

    style_tags = []
    if any(m in lowered for m in ["be shorter", "too long", "concise"]):
        style_tags.append("concise")
    if any(m in lowered for m in ["too short", "more detailed", "go deeper"]):
        style_tags.append("detailed")
    if any(m in lowered for m in ["be simpler", "simple words", "clearer"]):
        style_tags.append("simple")
    if any(m in lowered for m in ["with sources", "more citations", "cite"]):
        style_tags.append("citations")
    if any(m in lowered for m in ["too formal"]):
        style_tags.append("casual_tone")
    if any(m in lowered for m in ["too casual"]):
        style_tags.append("formal_tone")

    fact_note = ""
    fact_match = re.search(r"(?:actually|correction[:\s-]*)\s*(.+?)\s+is\s+(.+)", content, re.IGNORECASE)
    if fact_match:
        fact_note = f"{fact_match.group(1).strip()} is {fact_match.group(2).strip()}"

    return {
        "is_feedback": True,
        "text": content or user_message,
        "style_tags": style_tags,
        "fact_note": fact_note,
    }


def apply_feedback_learning(user_id, user_state, feedback_payload):
    """Update per-user and global learning memory from feedback."""
    if not feedback_payload.get("is_feedback"):
        return user_state

    learning_memory = load_learning_memory()
    timestamp = utc_now_iso()
    fb_text = feedback_payload.get("text", "")
    style_tags = feedback_payload.get("style_tags", [])

    user_state.setdefault("feedback_log", [])
    user_state["feedback_log"].append({"ts": timestamp, "feedback": fb_text, "tags": style_tags})
    user_state["feedback_log"] = user_state["feedback_log"][-100:]

    prefs = user_state.setdefault("preferences", default_user_state()["preferences"])
    if "concise" in style_tags:
        prefs["response_style"] = "concise"
    if "detailed" in style_tags:
        prefs["response_style"] = "detailed"
    if "simple" in style_tags:
        prefs["explanation_level"] = "simple"
    if "citations" in style_tags:
        prefs["prefer_citations"] = True
    if "casual_tone" in style_tags:
        prefs["tone"] = "casual"
    if "formal_tone" in style_tags:
        prefs["tone"] = "formal"

    fact_note = feedback_payload.get("fact_note", "")
    if fact_note:
        user_state.setdefault("fact_notes", [])
        user_state["fact_notes"].append({"ts": timestamp, "note": fact_note})
        user_state["fact_notes"] = user_state["fact_notes"][-50:]

    votes = learning_memory.setdefault("style_votes", {})
    for tag in style_tags:
        votes[tag] = int(votes.get(tag, 0)) + 1

    examples = learning_memory.setdefault("feedback_examples", [])
    examples.append({"ts": timestamp, "user_id": sanitize_user_id(user_id), "feedback": fb_text})
    learning_memory["feedback_examples"] = examples[-200:]

    save_learning_memory(learning_memory)
    return user_state


def build_adaptive_system_prompt(user_state, user_message="", temporary_warning=""):
    """Build dynamic system instructions from feedback and preferences."""
    prefs = user_state.get("preferences") or {}
    profile = user_state.get("profile") or {}
    display_name = (profile.get("name") or "").strip()
    lines = [SYSTEM_PROMPT, ""]
    if display_name:
        lines.append(f"- Registered user name: {display_name}. Use their name naturally sometimes.")
    lines.append("Adaptive communication preferences:")
    lines.append(f"- Response style: {prefs.get('response_style', 'concise')}")
    lines.append(f"- Tone: {prefs.get('tone', 'warm')}")
    lines.append(f"- Explanation level: {prefs.get('explanation_level', 'balanced')}")
    if prefs.get("prefer_citations"):
        lines.append("- If user asks for citations, provide clear sources.")

    inferred_tone = infer_user_tone(user_message)
    lines.append(f"- Current user tone detected: {inferred_tone}.")
    lines.append(f"- Tone behavior: {tone_instruction_for(inferred_tone)}")
    normalized_message = normalize_intent_text(user_message)
    if any(marker in normalized_message for marker in ["compare", "comparison", "vs", "versus"]):
        lines.append(
            "- For firm comparisons, prefer a compact Markdown table and end with a direct coach verdict: growth pick, safety pick, and one avoid candidate."
        )

    learning_memory = load_learning_memory()
    votes = learning_memory.get("style_votes") or {}
    if votes:
        top_tag = max(votes, key=votes.get)
        if votes.get(top_tag, 0) >= 3:
            lines.append(f"- Global feedback trend: users often prefer '{top_tag}'.")

    idle_snippets = build_idle_knowledge_snippets(user_state, learning_memory)
    if idle_snippets:
        lines.append("Background-refreshed knowledge relevant to this user:")
        for topic, snippet in idle_snippets:
            lines.append(f"- {topic}: {snippet}")

    tone_memory = user_state.get("tone_memory") or {}
    if tone_memory:
        top_tone = max(tone_memory, key=lambda k: int(tone_memory.get(k, 0)))
        if int(tone_memory.get(top_tone, 0)) >= 3 and top_tone != inferred_tone:
            lines.append(f"- User usually prefers a {top_tone} vibe; blend that naturally when appropriate.")

    notes = user_state.get("fact_notes") or []
    if notes:
        lines.append("User-provided notes from past conversations:")
        for note in notes[-3:]:
            if isinstance(note, dict) and note.get("note"):
                lines.append(f"- {note['note']}")

    learned_topics = user_state.get("learned_topics") or {}
    if learned_topics:
        top_topics = sorted(learned_topics.items(), key=lambda x: x[1], reverse=True)[:3]
        lines.append("Frequently discussed user interests:")
        for topic, score in top_topics:
            lines.append(f"- {topic} (interest score {score})")

    qa_memory = user_state.get("qa_memory") or []
    if qa_memory:
        high_quality = sorted(
            [m for m in qa_memory if isinstance(m, dict)],
            key=lambda x: (int(x.get("score", 0)), int(x.get("uses", 0))),
            reverse=True,
        )[:2]
        if high_quality:
            lines.append("Reusable high-signal patterns from prior conversations:")
            for item in high_quality:
                q = (item.get("q") or "").strip()
                a = (item.get("a") or "").strip()
                if q and a:
                    lines.append(f"- Q pattern: {q[:120]}")
                    lines.append(f"  A style: {a[:180]}")

    if temporary_warning:
        lines.append("Temporary risk control warning:")
        lines.append(f"- {temporary_warning}")

    return "\n".join(lines)


def sweep_idle_cash(user_id):
    """Simulate sweeping checking surplus above $2,000 into a 4.5% HYSA."""
    safe_user_id = sanitize_user_id(user_id)
    user_state = ensure_finance_profiles(load_user_state(safe_user_id))
    finance_profile = user_state.get("finance_profile") or {}
    cash_profile = finance_profile.get("cash_management") or {}
    runway_profile = finance_profile.get("runway_buffer_profile") or {}

    checking_balance = float(to_float_or_none(cash_profile.get("checking_balance_usd")) or 0.0)
    hysa_balance = float(to_float_or_none(cash_profile.get("hysa_balance_usd")) or 0.0)
    auto_sweep_enabled = bool(cash_profile.get("hysa_auto_sweep_enabled", False))
    consent_timestamp = str(cash_profile.get("hysa_auto_sweep_enabled_at") or "").strip()

    if (not auto_sweep_enabled) or (not consent_timestamp) or (parse_iso_datetime(consent_timestamp) is None):
        return "", user_state, False

    if checking_balance <= 0.0:
        # Backfill from existing runway capital when explicit checking balance is missing.
        checking_balance = max(0.0, float(to_float_or_none(runway_profile.get("capital_usd")) or 0.0))

    if checking_balance <= 2000.0:
        return "", user_state, False

    sweep_amount = round(checking_balance - 2000.0, 2)
    if sweep_amount <= 0.0:
        return "", user_state, False

    cash_profile["checking_balance_usd"] = round(checking_balance - sweep_amount, 2)
    cash_profile["hysa_balance_usd"] = round(hysa_balance + sweep_amount, 2)
    cash_profile["hysa_apy"] = 0.045
    cash_profile["last_idle_cash_sweep_at"] = utc_now_iso()
    cash_profile["last_idle_cash_sweep_amount"] = sweep_amount
    finance_profile["cash_management"] = cash_profile
    user_state["finance_profile"] = finance_profile
    save_user_state(safe_user_id, user_state)

    return f"Swept ${sweep_amount:.2f} of idle cash to your HYSA to beat inflation.", user_state, True


def is_positive_reaction(text):
    lowered = normalize_intent_text(text)
    markers = ["thanks", "thank you", "great", "perfect", "that helps", "nice", "good answer"]
    return any(m in lowered for m in markers)


def is_negative_reaction(text):
    lowered = normalize_intent_text(text)
    markers = ["wrong", "not right", "incorrect", "that is bad", "confusing", "does not make sense"]
    return any(m in lowered for m in markers)


def extract_learning_topics(user_message):
    """Extract broad topics from user prompt for autonomous preference learning."""
    normalized = normalize_intent_text(user_message)
    topics = []

    explain_topic = extract_explain_topic(normalized)
    if explain_topic:
        topics.append(explain_topic.lower())

    patterns = [
        r"\b(?:about|on|of)\s+([a-z\s]{3,40})$",
        r"\b(?:capital|president|inflation|weather|news|calories|economics|math|history|science)\b",
    ]
    for pattern in patterns:
        for match in re.findall(pattern, normalized):
            if isinstance(match, tuple):
                candidate = " ".join([m for m in match if m]).strip()
            else:
                candidate = str(match).strip()
            candidate = re.sub(r"\b(please|simple|simply|with|sources|citation|citations)\b", "", candidate).strip()
            candidate = re.sub(r"\s+", " ", candidate)
            if 2 <= len(candidate) <= 40:
                topics.append(candidate)

    unique = []
    for topic in topics:
        if topic and topic not in unique:
            unique.append(topic)
    return unique[:4]


def update_reaction_signal(user_state, user_message):
    """Use casual user reactions to score the most recent learned answer."""
    qa_memory = user_state.get("qa_memory") or []
    if not qa_memory:
        return user_state

    if is_positive_reaction(user_message):
        qa_memory[-1]["score"] = int(qa_memory[-1].get("score", 0)) + 1
    elif is_negative_reaction(user_message):
        qa_memory[-1]["score"] = int(qa_memory[-1].get("score", 0)) - 1

    user_state["qa_memory"] = qa_memory[-300:]
    return user_state


def should_store_qa_learning(user_message, assistant_message):
    if not user_message or not assistant_message:
        return False
    weak_markers = ["could not find", "could not reach", "not able to help", "try a more specific"]
    lower_a = assistant_message.lower()
    if any(m in lower_a for m in weak_markers):
        return False
    if len(assistant_message.strip()) < 25:
        return False
    return True


def update_autonomous_learning(user_state, user_message, assistant_message):
    """Continuously learn useful patterns from normal conversations."""
    user_state = update_reaction_signal(user_state, user_message)

    tone_label = infer_user_tone(user_message)
    tone_memory = user_state.get("tone_memory") or default_user_state()["tone_memory"]
    tone_memory[tone_label] = int(tone_memory.get(tone_label, 0)) + 1
    user_state["tone_memory"] = tone_memory

    topics = extract_learning_topics(user_message)
    learned_topics = user_state.get("learned_topics") or {}
    for topic in topics:
        learned_topics[topic] = int(learned_topics.get(topic, 0)) + 1
    user_state["learned_topics"] = learned_topics

    if not should_store_qa_learning(user_message, assistant_message):
        return user_state

    q_key = normalize_intent_text(user_message)[:220]
    qa_memory = user_state.get("qa_memory") or []
    best_idx = None
    best_ratio = 0.0
    for i, item in enumerate(qa_memory):
        old_q = (item.get("q") or "").strip()
        if not old_q:
            continue
        ratio = question_similarity(old_q, q_key)
        if ratio > best_ratio:
            best_ratio = ratio
            best_idx = i

    timestamp = utc_now_iso()
    if best_idx is not None and best_ratio >= 0.62:
        qa_memory[best_idx]["a"] = assistant_message[:900]
        qa_memory[best_idx]["uses"] = int(qa_memory[best_idx].get("uses", 0)) + 1
        qa_memory[best_idx]["ts"] = timestamp
    else:
        qa_memory.append({
            "q": q_key,
            "a": assistant_message[:900],
            "uses": 1,
            "score": 0,
            "ts": timestamp,
        })

    user_state["qa_memory"] = qa_memory[-300:]
    return user_state


def retrieve_learned_answer(user_state, user_message):
    """Reuse a strong past answer when a very similar question appears again."""
    qa_memory = user_state.get("qa_memory") or []
    if not qa_memory:
        return ""

    q_key = normalize_intent_text(user_message)
    if "uploaded attachment analysis:" in normalize_case(user_message):
        return ""
    if is_market_or_current_events_query(q_key):
        return ""

    best_item = None
    best_ratio = 0.0
    for item in qa_memory:
        old_q = (item.get("q") or "").strip()
        if not old_q:
            continue
        ratio = question_similarity(old_q, q_key)
        if ratio > best_ratio:
            best_ratio = ratio
            best_item = item

    if not best_item:
        return ""
    if best_ratio < 0.62:
        return ""
    if int(best_item.get("score", 0)) < -1:
        return ""

    answer = (best_item.get("a") or "").strip()
    if not answer:
        return ""
    return answer


def question_similarity(a, b):
    """Hybrid similarity: sequence ratio plus token overlap for paraphrases."""
    seq = difflib.SequenceMatcher(a=a, b=b).ratio()
    a_tokens = set(re.findall(r"[a-z0-9']+", a.lower()))
    b_tokens = set(re.findall(r"[a-z0-9']+", b.lower()))
    if not a_tokens or not b_tokens:
        return seq
    overlap = len(a_tokens & b_tokens) / max(len(a_tokens | b_tokens), 1)
    return max(seq, overlap)

def load_history():
    """Load conversation history from history.json, or initialize fresh."""
    if os.path.exists(HISTORY_FILE):
        try:
            with open(HISTORY_FILE, "r") as f:
                return json.load(f)
        except Exception as e:
            print(f"Warning: Could not load history: {e}. Starting fresh.")
            return [{"role": "system", "content": SYSTEM_PROMPT}]
    else:
        return [{"role": "system", "content": SYSTEM_PROMPT}]

def save_history(history):
    """Save conversation history to history.json."""
    try:
        with open(HISTORY_FILE, "w") as f:
            json.dump(history, f, indent=2)
    except Exception as e:
        print(f"Warning: Could not save history: {e}")

# Initialize conversation history
ensure_storage_dirs()
conversation_history = load_history()
CURRENT_LANGUAGE = "en"

# Step 4: Streamed Responses & Context Limits
MAX_CONTEXT_TOKENS = 6000  # Budget for context window (gpt-4 has 8k, leave buffer)
ENCODING = tiktoken.encoding_for_model("gpt-4")

def count_tokens(text):
    """Estimate token count for a given text."""
    try:
        return len(ENCODING.encode(text))
    except Exception:
        # Fallback: rough estimation (1 token ≈ 4 chars)
        return len(text) // 4

def get_total_tokens(history):
    """Calculate total tokens in conversation history."""
    total = 0
    for message in history:
        total += count_tokens(message.get("content", ""))
    return total

def trim_history(history, max_tokens=MAX_CONTEXT_TOKENS):
    """Trim history to stay within token budget, keeping system prompt and recent messages."""
    if len(history) <= 1:
        return history
    
    total_tokens = get_total_tokens(history)
    
    if total_tokens <= max_tokens:
        return history
    
    # Always keep system prompt
    trimmed = [history[0]]
    
    # Add messages from the end (most recent) until we hit the limit
    for msg in reversed(history[1:]):
        msg_tokens = count_tokens(msg.get("content", ""))
        if get_total_tokens(trimmed) + msg_tokens <= max_tokens:
            trimmed.insert(1, msg)
        else:
            break
    
    return trimmed


def determine_target_language(user_message):
    """Detect and persist language preference (English/Mongolian)."""
    global CURRENT_LANGUAGE
    lowered = normalize_case(user_message).strip()

    mongolian_switch_markers = [
        "speak mongolian", "in mongolian", "mongolian please", "speak in mongolian",
        "монголоор", "монгол хэлээр"
    ]
    english_switch_markers = ["speak english", "in english", "english please"]

    if any(marker in lowered for marker in mongolian_switch_markers):
        CURRENT_LANGUAGE = "mn"
    elif any(marker in lowered for marker in english_switch_markers):
        CURRENT_LANGUAGE = "en"
    elif re.search(r"[\u0400-\u04FF\u1800-\u18AF]", user_message):
        CURRENT_LANGUAGE = "mn"

    return CURRENT_LANGUAGE


def translate_text(text, target_lang):
    """Translate text using public translate endpoint, fallback to original text."""
    if not text or target_lang == "en":
        return text
    try:
        url = (
            "https://translate.googleapis.com/translate_a/single?client=gtx"
            f"&sl=auto&tl={target_lang}&dt=t&q={quote_plus(text)}"
        )
        payload = fetch_json_url(url)
        if isinstance(payload, list) and payload and isinstance(payload[0], list):
            translated = "".join(
                chunk[0] for chunk in payload[0]
                if isinstance(chunk, list) and chunk and isinstance(chunk[0], str)
            ).strip()
            return translated or text
    except Exception:
        pass
    return text


def localize_reply(reply_text, target_lang):
    """Return response localized to preferred language."""
    if target_lang != "mn":
        return reply_text
    return translate_text(reply_text, "mn")


def is_finance_numeric_sensitive_query(text):
    """Return True when user query is likely to request financial numeric claims."""
    lowered = normalize_case(text or "")
    markers = [
        "stock", "stocks", "ticker", "quote", "price", "market cap", "portfolio", "invest", "investment",
        "hysa", "savings", "return", "roi", "pe", "p/e", "roe", "debt to equity", "margin", "finance",
        "etf", "fund", "interest rate", "yield",
    ]
    return any(marker in lowered for marker in markers)


def response_has_financial_numeric_claim(text):
    """Detect likely numeric financial claims in free-form assistant text."""
    body = text or ""
    has_number = bool(re.search(r"\d", body))
    if not has_number:
        return False
    finance_tokens = bool(
        re.search(
            r"(?i)(\$|usd|eur|gbp|%|p/e|pe\b|roe\b|debt[-\s]*to[-\s]*equity|margin|market\s*cap|yield|annual\s*return|price)",
            body,
        )
    )
    return finance_tokens


def apply_financial_traceability_guard(user_message, assistant_message, source_tag="llm", user_id=DEFAULT_USER_ID):
    """Block untraceable numeric finance claims from generative responses."""
    msg = assistant_message or ""
    if not is_finance_numeric_sensitive_query(user_message):
        return msg
    if not response_has_financial_numeric_claim(msg):
        return msg

    # Allow explicitly assumption-labeled outputs.
    if re.search(r"(?i)assumption|illustrative|example\s+only|not\s+guaranteed", msg):
        return msg

    log_metric_validation_block(
        "global-finance-reply",
        "untraceable-numeric-claim",
        {
            "source_tag": source_tag,
            "user_message": (user_message or "")[:240],
            "assistant_preview": msg[:240],
        },
        user_id=user_id,
    )
    return UNVERIFIED_FINANCIAL_CLAIM_MESSAGE


def detect_high_stress_finance_context(text):
    """Detect emotionally loaded finance messages that require human-first handling."""
    lowered = normalize_case(text or "")

    hardship = bool(
        re.search(
            r"\b(can'?t\s+pay|cannot\s+pay|missed\s+(rent|payment)|behind\s+on\s+(rent|bills?)|"
            r"late\s+on\s+rent|evict|eviction|rent\s+this\s+month|overdue\s+bill|shut\s*off\s+notice)\b",
            lowered,
        )
    )

    loss_distress = bool(
        re.search(
            r"\b(lost\s+(a\s+lot|money)|bad\s+trade|blew\s+up\s+my\s+account|wiped\s+out|"
            r"i\s+feel\s+like\s+an?\s+(idiot|failure|moron)|i\s+screwed\s+up|i\s+messed\s+up)\b",
            lowered,
        )
    )

    peer_source = bool(
        re.search(r"\b(friend|buddy|coworker|influencer|tiktok|youtube|discord|telegram|reddit|twitter|x)\b", lowered)
    )
    hype_claim = bool(
        re.search(
            r"\b(10x|100x|guaranteed\s+return|sure\s+thing|can't\s+lose|cannot\s+lose|to\s+the\s+moon|"
            r"inside\s+tip|all\s+in|put\s+all\s+my\s+savings)\b",
            lowered,
        )
    )
    investment_scope = bool(re.search(r"\b(crypto|bitcoin|eth|stock|stocks|option|options|trading|invest|investment|savings)\b", lowered))
    peer_hype = (peer_source and hype_claim and investment_scope) or bool(
        re.search(r"\b(all\s+my\s+savings\s+into\s+crypto)\b", lowered)
    )

    is_flagged = hardship or loss_distress or peer_hype
    return {
        "is_flagged": is_flagged,
        "hardship": hardship,
        "loss_distress": loss_distress,
        "peer_hype": peer_hype,
    }


def _high_stress_opening(context):
    """Return a plain-language acknowledgment opener for high-stress finance messages."""
    if context.get("hardship"):
        return "That is a stressful spot, and you are doing the right thing by dealing with it early."
    if context.get("loss_distress"):
        return "That is a rough hit, and feeling shaken after a loss like that is normal."
    if context.get("peer_hype"):
        return "Good call asking before acting because hype-based money advice can get expensive fast."
    return "This is a high-pressure money decision, so let us slow it down and handle it clearly."


def has_high_stress_acknowledgment(reply_text):
    """Check whether the first 1-2 sentences acknowledge the user's situation."""
    text = (reply_text or "").strip()
    if not text:
        return False
    parts = [p.strip() for p in re.split(r"(?<=[.!?])\s+", text) if p.strip()]
    lead = " ".join(parts[:2]) if parts else text
    return bool(
        re.search(
            r"(?i)(rough|stressful|hard\s+spot|you'?re\s+dealing\s+with|good\s+call\s+asking|"
            r"feeling\s+shaken|you'?re\s+not\s+crazy|you'?re\s+not\s+alone|right\s+thing\s+by\s+asking)",
            lead,
        )
    )


def apply_high_stress_tone_check(user_message, assistant_message):
    """Ensure flagged finance replies acknowledge the person before advice/data."""
    context = detect_high_stress_finance_context(user_message)
    if not context.get("is_flagged"):
        return assistant_message
    reply = (assistant_message or "").strip()
    if has_high_stress_acknowledgment(reply):
        return reply
    opener = _high_stress_opening(context)
    if not reply:
        return opener
    return f"{opener} {reply}"


def get_high_stress_finance_reply(user_message, include_sources=False):
    """Return concrete guidance for emotionally loaded finance situations."""
    context = detect_high_stress_finance_context(user_message)
    if not context.get("is_flagged"):
        return ""

    if context.get("hardship"):
        reply = (
            "That is a stressful spot, and you are doing the right thing by dealing with it early. "
            "Here is the practical playbook for this week:\n"
            "1. Contact your landlord today before the due date or as soon as possible. Give a specific amount you can pay now and a realistic date for the rest.\n"
            "2. Apply immediately for local rental assistance (city/county programs, 211, community nonprofits). Same-day applications matter.\n"
            "3. Prioritize bills in this order for now: housing, utilities, food, transportation, then unsecured debt.\n"
            "4. If short on cash, ask utility providers and lenders for hardship plans before missing more payments.\n"
            "5. Avoid payday/title loans if possible. The interest spiral usually makes next month worse.\n"
            "If you want, I can help you draft a landlord message in 60 seconds using your exact numbers."
        )
        if include_sources:
            return with_citations(reply, ["https://www.211.org/"], include_sources)
        return reply

    if context.get("peer_hype"):
        reply = (
            "Good call asking before acting because hype-based money advice can get expensive fast. "
            "I would not put all your savings into a single crypto bet based on a friend or influencer claim.\n"
            "1. A \"10x soon\" claim is not evidence; it is a red flag unless backed by verifiable data and risk limits.\n"
            "2. Putting all savings into one volatile asset creates concentration risk and can wipe out emergency money.\n"
            "3. Keep your safety cash (rent/emergency fund) out of high-volatility bets.\n"
            "4. If you still want exposure, size it small enough that a full loss does not damage your core finances."
        )
        return reply

    if context.get("loss_distress"):
        reply = (
            "That is a rough hit, and feeling shaken after a loss like that is normal. "
            "Let us make the next move safer, not emotional:\n"
            "1. Pause new risk trades for 48-72 hours.\n"
            "2. Write down exactly what happened: thesis, entry, size, stop, and what invalidated it.\n"
            "3. Set hard rules before the next trade: smaller position size, predefined stop, and max daily loss.\n"
            "4. Protect remaining cash first; recovery starts with risk control, not revenge trading.\n"
            "If you want, I can help you turn the last trade into a one-page post-mortem and a safer rule set."
        )
        return reply

    return ""

def get_ai_response(user_message, user_id=DEFAULT_USER_ID, remember_history=True):
    """Send user message to frontier model and stream response."""
    global conversation_history

    user_state = load_user_state(user_id)
    sweep_notice, swept_state, sweep_changed = sweep_idle_cash(user_id)
    if sweep_changed:
        user_state = swept_state
    if remember_history:
        conversation_history = user_state.get("history", default_history())
    else:
        conversation_history = default_history()

    subscription_alert, alert_state_changed = maybe_get_witty_subscription_alert(user_state, user_id)

    feedback_payload = detect_feedback_payload(user_message)
    if feedback_payload.get("is_feedback"):
        user_state = apply_feedback_learning(user_id, user_state, feedback_payload)
        save_user_state(user_id, user_state)
        return "Thanks for the feedback. I saved it and I will adapt how I respond from now on."

    gate_eval = evaluate_behavioral_gate(user_message, user_state, user_id=user_id)
    user_state = gate_eval.get("state") or user_state
    gate_warning = gate_eval.get("warning") or ""
    if gate_eval.get("active"):
        gate_message = gate_eval.get("message") or "Please wait 12 hours before completing this transaction."
        gate_message = merge_witty_alert(gate_message, subscription_alert)
        merged_warning = f"{gate_warning}\n{sweep_notice}" if (gate_warning and sweep_notice) else (gate_warning or sweep_notice)
        adaptive_system = build_adaptive_system_prompt(user_state, user_message, temporary_warning=merged_warning)
        if conversation_history and conversation_history[0].get("role") == "system":
            conversation_history[0]["content"] = adaptive_system
        else:
            conversation_history.insert(0, {"role": "system", "content": adaptive_system})
        if remember_history:
            conversation_history.append({"role": "user", "content": user_message})
            conversation_history.append({"role": "assistant", "content": gate_message})
            conversation_history = trim_history(conversation_history)
            user_state["history"] = conversation_history
        save_user_state(user_id, user_state)
        return gate_message

    wants_citations = is_citation_request(normalize_intent_text(user_message))
    high_stress_reply = get_high_stress_finance_reply(user_message, include_sources=wants_citations)
    if high_stress_reply:
        high_stress_reply = apply_tone_style(high_stress_reply, user_message)
        high_stress_reply = apply_high_stress_tone_check(user_message, high_stress_reply)
        if remember_history:
            conversation_history.append({"role": "user", "content": user_message})
            conversation_history.append({"role": "assistant", "content": high_stress_reply})
            conversation_history = trim_history(conversation_history)
            user_state = update_autonomous_learning(user_state, user_message, high_stress_reply)
            user_state["history"] = conversation_history
        if remember_history or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return high_stress_reply

    finance_direct_reply, finance_changed = get_personal_finance_feature_reply(
        user_message,
        user_state,
        user_id=user_id,
        include_sources=wants_citations,
    )
    if finance_direct_reply:
        finance_direct_reply = apply_tone_style(finance_direct_reply, user_message)
        finance_direct_reply = apply_high_stress_tone_check(user_message, finance_direct_reply)
        finance_direct_reply = merge_witty_alert(finance_direct_reply, subscription_alert)
        if remember_history:
            conversation_history.append({"role": "user", "content": user_message})
            conversation_history.append({"role": "assistant", "content": finance_direct_reply})
            conversation_history = trim_history(conversation_history)
            user_state = update_autonomous_learning(user_state, user_message, finance_direct_reply)
            user_state["history"] = conversation_history
        if remember_history or finance_changed or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return finance_direct_reply

    merged_warning = f"{gate_warning}\n{sweep_notice}" if (gate_warning and sweep_notice) else (gate_warning or sweep_notice)
    adaptive_system = build_adaptive_system_prompt(user_state, user_message, temporary_warning=merged_warning)
    if conversation_history and conversation_history[0].get("role") == "system":
        conversation_history[0]["content"] = adaptive_system
    else:
        conversation_history.insert(0, {"role": "system", "content": adaptive_system})
    
    try:
        # Append user message to history
        conversation_history.append({"role": "user", "content": user_message})
        
        # Trim history if needed
        conversation_history = trim_history(conversation_history)
        
        # Stream response from API
        full_response = ""
        with frontier_client.chat.completions.create(
            model="gpt-4",
            messages=conversation_history,
            temperature=0.7,
            max_tokens=800,
            timeout=LLM_REQUEST_TIMEOUT_SECONDS,
            stream=True
        ) as response:
            for chunk in response:
                token = chunk.choices[0].delta.content or ""
                full_response += token
                print(token, end="", flush=True)
        
        print()  # Newline after streaming completes
        full_response = apply_tone_style(full_response, user_message)
        full_response = apply_high_stress_tone_check(user_message, full_response)
        full_response = merge_witty_alert(full_response, subscription_alert)
        full_response = apply_financial_traceability_guard(user_message, full_response, source_tag="llm-stream", user_id=user_id)
        
        # Append complete assistant response to history
        conversation_history.append({"role": "assistant", "content": full_response})
        
        # Save updated history
        save_history(conversation_history)
        if remember_history:
            user_state = update_autonomous_learning(user_state, user_message, full_response)
            user_state["history"] = conversation_history
        if remember_history or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        
        return full_response
    except Exception as e:
        print(f"Warning: get_ai_response model call failed: {e}")
        assistant_message = get_local_smart_reply(user_message, user_id=user_id)
        if not (assistant_message or "").strip():
            assistant_message = DATA_UNAVAILABLE_RETRY_MESSAGE
        assistant_message = apply_tone_style(assistant_message, user_message)
        assistant_message = apply_high_stress_tone_check(user_message, assistant_message)
        assistant_message = merge_witty_alert(assistant_message, subscription_alert)
        assistant_message = apply_financial_traceability_guard(user_message, assistant_message, source_tag="local-fallback", user_id=user_id)
        conversation_history.append({"role": "assistant", "content": assistant_message})
        save_history(conversation_history)
        if remember_history:
            user_state = update_autonomous_learning(user_state, user_message, assistant_message)
            user_state["history"] = conversation_history
        if remember_history or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return assistant_message


def get_ai_response_sync(user_message, user_id=DEFAULT_USER_ID, remember_history=True):
    """Send user message to frontier model and return a full response for web usage."""
    global conversation_history
    target_language = determine_target_language(user_message)

    user_state = load_user_state(user_id)
    sweep_notice, swept_state, sweep_changed = sweep_idle_cash(user_id)
    if sweep_changed:
        user_state = swept_state
    if remember_history:
        conversation_history = user_state.get("history", default_history())
    else:
        conversation_history = default_history()

    subscription_alert, alert_state_changed = maybe_get_witty_subscription_alert(user_state, user_id)

    feedback_payload = detect_feedback_payload(user_message)
    if feedback_payload.get("is_feedback"):
        user_state = apply_feedback_learning(user_id, user_state, feedback_payload)
        save_user_state(user_id, user_state)
        ack = "Thanks for the feedback. I saved it and I will improve my replies in future conversations."
        return merge_witty_alert(localize_reply(ack, target_language), subscription_alert)

    gate_eval = evaluate_behavioral_gate(user_message, user_state, user_id=user_id)
    user_state = gate_eval.get("state") or user_state
    gate_warning = gate_eval.get("warning") or ""
    if gate_eval.get("active"):
        gate_message = gate_eval.get("message") or "Please wait 12 hours before completing this transaction."
        gate_message = localize_reply(gate_message, target_language)
        gate_message = merge_witty_alert(gate_message, subscription_alert)
        merged_warning = f"{gate_warning}\n{sweep_notice}" if (gate_warning and sweep_notice) else (gate_warning or sweep_notice)
        adaptive_system = build_adaptive_system_prompt(user_state, user_message, temporary_warning=merged_warning)
        if conversation_history and conversation_history[0].get("role") == "system":
            conversation_history[0]["content"] = adaptive_system
        else:
            conversation_history.insert(0, {"role": "system", "content": adaptive_system})
        if remember_history:
            conversation_history.append({"role": "user", "content": user_message})
            conversation_history.append({"role": "assistant", "content": gate_message})
            conversation_history = trim_history(conversation_history)
            user_state["history"] = conversation_history
        save_user_state(user_id, user_state)
        return gate_message

    wants_citations = is_citation_request(normalize_intent_text(user_message))
    high_stress_reply = get_high_stress_finance_reply(user_message, include_sources=wants_citations)
    if high_stress_reply:
        high_stress_reply = apply_tone_style(high_stress_reply, user_message)
        high_stress_reply = apply_high_stress_tone_check(user_message, high_stress_reply)
        high_stress_reply = localize_reply(high_stress_reply, target_language)
        if remember_history:
            conversation_history.append({"role": "user", "content": user_message})
            conversation_history.append({"role": "assistant", "content": high_stress_reply})
            conversation_history = trim_history(conversation_history)
            user_state = update_autonomous_learning(user_state, user_message, high_stress_reply)
            user_state["history"] = conversation_history
        if remember_history or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return high_stress_reply

    finance_direct_reply, finance_changed = get_personal_finance_feature_reply(
        user_message,
        user_state,
        user_id=user_id,
        include_sources=wants_citations,
    )
    if finance_direct_reply:
        finance_direct_reply = apply_tone_style(finance_direct_reply, user_message)
        finance_direct_reply = apply_high_stress_tone_check(user_message, finance_direct_reply)
        finance_direct_reply = localize_reply(finance_direct_reply, target_language)
        finance_direct_reply = merge_witty_alert(finance_direct_reply, subscription_alert)
        if remember_history:
            conversation_history.append({"role": "user", "content": user_message})
            conversation_history.append({"role": "assistant", "content": finance_direct_reply})
            conversation_history = trim_history(conversation_history)
            user_state = update_autonomous_learning(user_state, user_message, finance_direct_reply)
            user_state["history"] = conversation_history
        if remember_history or finance_changed or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return finance_direct_reply

    normalized_user_message = normalize_intent_text(user_message)
    profile = user_state.get("profile") or {}
    registered_name = (profile.get("name") or "").strip()
    if registered_name and (
        "what is my name" in normalized_user_message
        or "who am i" in normalized_user_message
        or "do you know my name" in normalized_user_message
    ):
        direct = f"Your name is {registered_name}."
        if alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return merge_witty_alert(localize_reply(apply_tone_style(direct, user_message), target_language), subscription_alert)

    learned_answer = retrieve_learned_answer(user_state, user_message)
    if learned_answer:
        learned_answer = apply_tone_style(learned_answer, user_message)
        learned_answer = localize_reply(learned_answer, target_language)
        learned_answer = merge_witty_alert(learned_answer, subscription_alert)
        if remember_history:
            conversation_history.append({"role": "user", "content": user_message})
            conversation_history.append({"role": "assistant", "content": learned_answer})
            conversation_history = trim_history(conversation_history)
            user_state = update_autonomous_learning(user_state, user_message, learned_answer)
            user_state["history"] = conversation_history
            save_user_state(user_id, user_state)
        elif alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return learned_answer

    merged_warning = f"{gate_warning}\n{sweep_notice}" if (gate_warning and sweep_notice) else (gate_warning or sweep_notice)
    adaptive_system = build_adaptive_system_prompt(user_state, user_message, temporary_warning=merged_warning)
    if conversation_history and conversation_history[0].get("role") == "system":
        conversation_history[0]["content"] = adaptive_system
    else:
        conversation_history.insert(0, {"role": "system", "content": adaptive_system})

    try:
        conversation_history.append({"role": "user", "content": user_message})
        conversation_history = trim_history(conversation_history)

        response = frontier_client.chat.completions.create(
            model="gpt-4",
            messages=conversation_history,
            temperature=0.7,
            max_tokens=800,
            timeout=LLM_REQUEST_TIMEOUT_SECONDS,
        )

        assistant_message = (response.choices[0].message.content or "").strip()
        if not assistant_message:
            assistant_message = get_local_smart_reply(user_message, user_id=user_id)
        assistant_message = apply_tone_style(assistant_message, user_message)
        assistant_message = apply_high_stress_tone_check(user_message, assistant_message)
        assistant_message = localize_reply(assistant_message, target_language)
        assistant_message = merge_witty_alert(assistant_message, subscription_alert)
        assistant_message = apply_financial_traceability_guard(user_message, assistant_message, source_tag="llm-sync", user_id=user_id)

        conversation_history.append({"role": "assistant", "content": assistant_message})
        save_history(conversation_history)
        if remember_history:
            user_state = update_autonomous_learning(user_state, user_message, assistant_message)
            user_state["history"] = conversation_history
        if remember_history or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return assistant_message
    except Exception as e:
        print(f"Warning: get_ai_response_sync model call failed: {e}")
        assistant_message = get_local_smart_reply(user_message, user_id=user_id)
        if not (assistant_message or "").strip():
            assistant_message = DATA_UNAVAILABLE_RETRY_MESSAGE
        assistant_message = apply_tone_style(assistant_message, user_message)
        assistant_message = apply_high_stress_tone_check(user_message, assistant_message)
        assistant_message = localize_reply(assistant_message, target_language)
        assistant_message = merge_witty_alert(assistant_message, subscription_alert)
        assistant_message = apply_financial_traceability_guard(user_message, assistant_message, source_tag="local-sync-fallback", user_id=user_id)
        conversation_history.append({"role": "assistant", "content": assistant_message})
        save_history(conversation_history)
        if remember_history:
            user_state = update_autonomous_learning(user_state, user_message, assistant_message)
            user_state["history"] = conversation_history
        if remember_history or alert_state_changed or sweep_changed:
            save_user_state(user_id, user_state)
        return assistant_message


def should_use_simple_fallback(text):
    """Return True when input should get a minimal fallback response."""
    lowered = normalize_case(text)
    blocked_terms = [
        "hack", "malware", "exploit", "weapon", "bomb", "kill", "murder",
        "racist", "sexist", "porn", "nude", "explicit", "abuse"
    ]
    return any(term in lowered for term in blocked_terms)


def expand_common_shorthand(text):
    """Expand common short forms before intent and math handling."""
    expanded = normalize_case(text).strip()
    expanded = re.sub(r"([a-z])\1{2,}", r"\1\1", expanded)

    stretchy_word_replacements = {
        r"\bhel+o+\b": "hello",
        r"\bhe+y+\b": "hey",
        r"\bhi+i+\b": "hi",
        r"\byo+\b": "yo",
        r"\bsu+p+\b": "sup",
        r"\bpl+s+\b": "please",
        r"\bpl+z+\b": "please",
        r"\bthan+k+s+\b": "thanks",
    }
    for pattern, replacement in stretchy_word_replacements.items():
        expanded = re.sub(pattern, replacement, expanded)

    replacements = {
        r"\bwho['’]?s\b": "who is",
        r"\bwhat['’]?s\b": "what is",
        r"\bhow['’]?s\b": "how is",
        r"\bwhere['’]?s\b": "where is",
        r"\bwhy['’]?s\b": "why is",
        r"\bit['’]?s\b": "it is",
        r"\bi['’]?m\b": "i am",
        r"\bcan['’]?t\b": "cannot",
        r"\bdon['’]?t\b": "do not",
        r"\bwon['’]?t\b": "will not",
        r"\bain['’]?t\b": "is not",
        r"\bwyd\b": "what are you doing",
        r"\bwya\b": "where are you",
        r"\bu\b": "you",
        r"\bur\b": "your",
        r"\br\b": "are",
        r"\bim\b": "i am",
        r"\bgonna\b": "going to",
        r"\bwanna\b": "want to",
        r"\bgotta\b": "got to",
        r"\bkinda\b": "kind of",
        r"\bsorta\b": "sort of",
        r"\bcant\b": "cannot",
        r"\bdont\b": "do not",
        r"\bwhos\b": "who is",
        r"\bwhats\b": "what is",
        r"\bhows\b": "how is",
        r"\bheres\b": "here is",
        r"\bidk\b": "i do not know",
        r"\bidc\b": "i do not care",
        r"\blmk\b": "let me know",
        r"\btbh\b": "to be honest",
        r"\bfyi\b": "for your information",
        r"\bimo\b": "in my opinion",
        r"\bimho\b": "in my humble opinion",
        r"\bgimme\b": "give me",
        r"\bpls\b": "please",
        r"\bplz\b": "please",
        r"\bmsg\b": "message",
        r"\binfo\b": "information",
        r"\bthx\b": "thanks",
        r"\bty\b": "thank you",
        r"\brn\b": "right now",
        r"\btdy\b": "today",
        r"\btmrw\b": "tomorrow",
        r"\bcuz\b": "because",
        r"\bcoz\b": "because",
        r"\bmongoloor\b": "in mongolian",
        r"\btailbarlaad\s+uguuch\b": "explain",
    }
    for pattern, replacement in replacements.items():
        expanded = re.sub(pattern, replacement, expanded)

    # Common misspellings normalized early.
    typo_replacements = {
        "wheather": "weather",
        "waether": "weather",
        "temprature": "temperature",
        "newz": "news",
        "hedlines": "headlines",
        "sqare": "square",
        "squre": "square",
        "sqaure": "square",
        "answre": "answer",
        "quesiton": "question",
        "explainn": "explain",
        "econmics": "economics",
        "ecomomics": "economics",
        "definately": "definitely",
        "recieve": "receive",
        "becuase": "because",
        "throught": "through",
        "presdnt": "president",
        "presedent": "president",
        "primeminister": "prime minister",
        "capitol": "capital",
        "popuation": "population",
        "suhis": "sushi",
        "sushis": "sushi",
    }
    for wrong, fixed in typo_replacements.items():
        expanded = re.sub(rf"\b{re.escape(wrong)}\b", fixed, expanded)

    return re.sub(r"\s+", " ", expanded).strip()


def normalize_intent_text(text):
    """Normalize text with shorthand expansion and fuzzy token correction."""
    expanded = expand_common_shorthand(text)
    tokens = re.findall(r"[a-z0-9']+", expanded)

    intent_vocab = {
        "who", "what", "when", "where", "why", "how", "weather", "temperature",
        "news", "headlines", "today", "date", "time", "square", "root", "power",
        "hello", "hey", "hi", "love", "doing", "search", "latest", "tell", "about",
        "city", "country", "population", "president", "capital", "fact",
        "new", "york", "los", "angeles", "san", "francisco", "mexico", "paris", "tokyo",
        "madrid", "london", "berlin", "brazil", "argentina"
    }

    corrected = []
    for token in tokens:
        if token in intent_vocab or token.isdigit():
            corrected.append(token)
            continue
        match = difflib.get_close_matches(token, intent_vocab, n=1, cutoff=0.84)
        corrected.append(match[0] if match else token)

    return " ".join(corrected)


def _safe_eval_math(expr):
    """Safely evaluate arithmetic expressions with +, -, *, /, and **."""
    allowed_nodes = (
        ast.Expression, ast.BinOp, ast.UnaryOp, ast.Constant,
        ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow, ast.USub, ast.UAdd
    )
    tree = ast.parse(expr, mode="eval")
    for node in ast.walk(tree):
        if not isinstance(node, allowed_nodes):
            raise ValueError("Unsupported math expression")
    return eval(compile(tree, filename="<math>", mode="eval"), {"__builtins__": {}}, {})


def try_math_response(text):
    """Return a math answer when the message is math-like, otherwise None."""
    t = expand_common_shorthand(text)

    sqrt_match = re.search(r"(?:square\s*root(?:\s*of)?|sqrt)\s*\(?\s*(-?\d+(?:\.\d+)?)\s*\)?", t)
    if sqrt_match:
        num = float(sqrt_match.group(1))
        result = math.sqrt(num)
        return f"The square root of {sqrt_match.group(1)} is {result:.10f}."

    expr = t
    expr = expr.replace("plus", "+")
    expr = expr.replace("minus", "-")
    expr = expr.replace("times", "*")
    expr = expr.replace("multiplied by", "*")
    expr = expr.replace("divided by", "/")
    expr = expr.replace("over", "/")
    expr = expr.replace("to the power of", "**")
    expr = expr.replace("power of", "**")
    expr = expr.replace("^", "**")
    expr = re.sub(r"[^0-9+\-*/().\s*]", "", expr)
    expr = re.sub(r"\s+", "", expr)

    if expr and re.search(r"\d", expr) and any(op in expr for op in ["+", "-", "*", "/", "**"]):
        try:
            result = _safe_eval_math(expr)
            if isinstance(result, float):
                if result.is_integer():
                    result = int(result)
                else:
                    result = round(result, 10)
            return f"That equals {result}."
        except Exception:
            return None

    return None


def fetch_json_url(url):
    """Fetch a JSON payload from the internet with a short timeout."""
    req = Request(url, headers={"User-Agent": "Mozilla/5.0"})
    try:
        with urlopen(req, timeout=8) as response:
            data = response.read().decode("utf-8", errors="replace")
    except Exception:
        insecure_ctx = ssl._create_unverified_context()
        with urlopen(req, timeout=8, context=insecure_ctx) as response:
            data = response.read().decode("utf-8", errors="replace")
    return json.loads(data)


def fetch_text_url(url):
    """Fetch plain text or XML data from the internet with a short timeout."""
    req = Request(url, headers={"User-Agent": "Mozilla/5.0"})
    try:
        with urlopen(req, timeout=8) as response:
            return response.read().decode("utf-8", errors="replace")
    except Exception:
        insecure_ctx = ssl._create_unverified_context()
        with urlopen(req, timeout=8, context=insecure_ctx) as response:
            return response.read().decode("utf-8", errors="replace")


def extract_city_for_weather(normalized_text):
    """Extract city from prompts like 'weather in madrid'."""
    filler_words = {
        "today", "tomorrow", "right", "now", "please", "plz", "currently",
        "rn", "for", "this", "week", "tonight", "source", "sources", "citation", "citations", "with"
    }

    def clean_city(raw_city):
        words = [w for w in raw_city.split() if w.lower() not in filler_words]
        return " ".join(words).strip()

    match = re.search(r"weather(?:\s+in)?\s+([a-zA-Z\s]+)$", normalized_text)
    if match:
        city = clean_city(match.group(1))
        return city if city else None
    match = re.search(r"in\s+([a-zA-Z\s]+)\s+weather", normalized_text)
    if match:
        city = clean_city(match.group(1))
        return city if city else None
    return None


def get_weather_reply(normalized_text, include_sources=False):
    """Get live weather from wttr.in."""
    city = extract_city_for_weather(normalized_text)
    if not city:
        return "I can fetch live weather. Ask like: weather in New York."

    encoded_city = quote_plus(city)
    url = f"https://wttr.in/{encoded_city}?format=j1"
    try:
        payload = fetch_json_url(url)
        condition = payload["current_condition"][0]
        temp_c = condition.get("temp_C", "?")
        feels = condition.get("FeelsLikeC", "?")
        desc = condition.get("weatherDesc", [{"value": "Unknown"}])[0].get("value", "Unknown")
        humidity = condition.get("humidity", "?")
        reply = (
            f"Live weather in {city.title()}: {desc}, {temp_c}C "
            f"(feels like {feels}C), humidity {humidity}%."
        )
        return with_citations(reply, [url], include_sources)
    except Exception:
        return "I could not fetch weather right now. Try again in a moment."


def get_news_reply(include_sources=False):
    """Get top live headlines from Google News RSS."""
    today = datetime.now().strftime("%A, %B %d, %Y")
    url = "https://news.google.com/rss?hl=en-US&gl=US&ceid=US:en"
    try:
        xml_text = fetch_text_url(url)
        root = ET.fromstring(xml_text)
        items = root.findall("./channel/item")[:5]
        if not items:
            return build_no_excuses_analysis("top headlines today", include_sources=include_sources)

        lines = [f"Top headlines for {today}:"]
        for idx, item in enumerate(items, start=1):
            title = (item.findtext("title") or "Untitled").strip()
            lines.append(f"{idx}. {title}")
        reply = "\n".join(lines)
        return with_citations(reply, [url], include_sources)
    except Exception:
        return build_no_excuses_analysis("top headlines today", include_sources=include_sources)


def get_date_reply(include_sources=False):
    """Return current local date and day."""
    now = datetime.now()
    reply = f"Today is {now.strftime('%A, %B %d, %Y')} and the time is {now.strftime('%H:%M')} local time."
    return with_citations(reply, ["Local system clock"], include_sources)


def is_market_or_current_events_query(query):
    """Detect queries that deserve a realistic no-excuses current-events fallback."""
    lowered = normalize_case(query or "")
    markers = [
        "market", "stocks", "s&p", "nasdaq", "dow", "fed", "rates", "inflation", "treasury",
        "oil", "gold", "bitcoin", "crypto", "today", "current", "right now", "headlines", "news",
        "geopolit", "war", "middle east", "ai", "semiconductor", "nvidia", "economy",
    ]
    return any(marker in lowered for marker in markers)


def is_direct_investment_allocation_query(normalized_text):
    """Detect direct portfolio-allocation asks like 'what exactly should I invest in?'"""
    text = normalize_case(normalized_text or "")
    allocation_markers = [
        "what exactly should i invest",
        "what should i invest in",
        "where should i invest",
        "how should i invest",
        "how should i allocate",
        "how to allocate",
        "best portfolio for me",
        "build me a portfolio",
    ]
    blocking_markers = [
        "watchlist",
        "price",
        "quote",
        "compare",
        "portfolio a",
        "portfolio b",
        "subscription",
    ]
    if any(marker in text for marker in blocking_markers):
        return False
    return any(marker in text for marker in allocation_markers)


def build_investment_allocation_baseline_reply(include_sources=False):
    """Provide a concrete baseline portfolio with assumptions and 2 customizing questions."""
    lines = [
        "Assuming you have a 10+ year horizon, moderate risk tolerance, income in USD, and no high-interest debt dragging your cash flow, start with this baseline:",
        "- 70% VTI (broad U.S. total stock market)",
        "- 20% VXUS (broad international developed + emerging markets)",
        "- 10% split between SGOV/cash and a small speculative sleeve",
        "",
        "Why this works:",
        "- It captures global equity growth while keeping the core simple and low-cost.",
        "- It avoids single-country concentration by adding international diversification.",
        "- The 10% buffer gives stability, optionality, and dry powder during drawdowns.",
        "",
        "Execution rules:",
        "- Invest monthly (automatic buys), not by headlines.",
        "- Rebalance once per year or when any sleeve drifts by more than 5 percentage points.",
        "",
        "To customize this for you, answer these 2 questions:",
        "1. Which country are you tax-resident in, and what currency are your main expenses in?",
        "2. What is the largest portfolio drawdown (in %) you can tolerate without panic-selling?",
    ]
    sources = [
        "https://investor.vanguard.com/investor-resources-education/etfs/what-is-an-etf",
        "https://www.bogleheads.org/wiki/Three-fund_portfolio",
    ]
    return with_citations("\n".join(lines), sources, include_sources)


def build_no_excuses_analysis(query, include_sources=False):
    """Return a realistic 2026-informed fallback when live data/search is weak."""
    lowered = normalize_case(query or "")
    intro = "Here is exactly how the landscape is shaping up right now and what you need to look out for."

    if is_market_or_current_events_query(query):
        lines = [intro]
        lines.append("- Rates still matter more than narratives. If central banks are even mildly hawkish, expensive growth gets hit first and leverage gets uglier fast.")
        lines.append("- Middle East tension keeps oil, shipping lanes, and headline risk alive. That means sudden spikes in energy, freight, and inflation expectations can smack risk assets.")
        lines.append("- The AI infrastructure buildout is still a real force. Semis, data-center plumbing, power demand, and enterprise capex remain the cleanest structural winners if spending discipline holds.")
        lines.append("- If the market feels shaky today, the usual culprits are rate pressure, crowded positioning, or geopolitics colliding with stretched valuations. That is not mysterious. That is plumbing.")
        if any(marker in lowered for marker in ["market", "stocks", "s&p", "nasdaq", "dow"]):
            lines.append("- If you need a live tick to decide whether your plan is good, your plan is weak. Build around cash flow, valuation discipline, and time horizon, not adrenaline.")
        elif any(marker in lowered for marker in ["fed", "rates", "inflation", "economy"]):
            lines.append("- Most people say they fear inflation, but what actually wrecks them is financing a mediocre lifestyle at high rates. Kill expensive debt before it kills your optionality.")
        else:
            lines.append("- The loudest story is rarely the best trade. Follow incentives, balance-sheet pressure, and capital spending. Noise is free. Discipline is not.")
        return with_citations("\n".join(lines), ["Last-known 2026 macro framework"], include_sources)

    fallback = (
        "The right move is to reason from incentives, constraints, and what usually drives the system in 2026. "
        "When the feed is noisy, fundamentals matter more, not less."
    )
    return with_citations(fallback, ["Last-known 2026 macro framework"], include_sources)


def normalize_ticker_symbol(raw_symbol):
    """Normalize stock ticker symbols to a safe uppercase format."""
    cleaned = re.sub(r"[^A-Za-z0-9.\-]", "", raw_symbol or "").upper().strip()
    if not cleaned or len(cleaned) > 12:
        return ""
    return cleaned


def extract_ticker_candidates(text):
    """Extract likely ticker symbols from arbitrary user text."""
    raw = text or ""
    lower = normalize_case(raw)
    ignore = {
        "A", "I", "US", "USD", "AND", "OR", "THE", "FOR", "NOW", "ALL", "PER", "MIN",
    }

    found = set()
    for token in re.findall(r"\$([A-Za-z][A-Za-z0-9.\-]{0,10})\b", raw):
        symbol = normalize_ticker_symbol(token)
        if symbol and symbol not in ignore:
            found.add(symbol)

    for token in re.findall(r"\b[A-Z]{1,5}(?:\.[A-Z]{1,2})?\b", raw):
        symbol = normalize_ticker_symbol(token)
        if symbol and symbol not in ignore:
            found.add(symbol)

    for alias, ticker in COMPANY_ALIAS_TO_TICKER.items():
        if alias in lower:
            found.add(ticker)

    # Accept lowercase ticker words when query context implies quote lookup.
    if any(k in lower for k in ["stock", "stocks", "share", "shares", "quote", "price", "actions"]):
        for token in re.findall(r"\b[a-z]{1,5}(?:\.[a-z]{1,2})?\b", lower):
            maybe = normalize_ticker_symbol(token)
            if maybe and maybe in KNOWN_TICKERS:
                found.add(maybe)

    return sorted(found)


def resolve_ticker_from_company_name(company_name):
    """Resolve a company name into a ticker symbol using Yahoo Finance search."""
    candidate = (company_name or "").strip()
    if not candidate:
        return ""

    direct = COMPANY_ALIAS_TO_TICKER.get(normalize_case(candidate))
    if direct:
        return direct

    query = quote_plus(candidate)
    url = f"https://query2.finance.yahoo.com/v1/finance/search?q={query}&quotesCount=5&newsCount=0"
    try:
        payload = fetch_json_url(url)
        quotes = payload.get("quotes") or []
        for item in quotes:
            if not isinstance(item, dict):
                continue
            qtype = (item.get("quoteType") or "").upper()
            symbol = normalize_ticker_symbol(item.get("symbol") or "")
            if symbol and qtype in {"EQUITY", "ETF", "MUTUALFUND"}:
                return symbol
    except Exception:
        return ""
    return ""


def parse_company_name_candidates(text):
    """Extract company-name chunks from prompts like 'price of apple and tesla'."""
    original = text or ""
    lowered = normalize_case(original)
    matches = []
    patterns = [
        r"(?:price|stock|share|quote|value)\s+(?:of|for)\s+([a-z0-9&\-\.,\s]+)",
        r"(?:follow|track|watch)\s+([a-z0-9&\-\.,\s]+)",
    ]
    for pattern in patterns:
        m = re.search(pattern, lowered)
        if m:
            matches.append(m.group(1))

    names = []
    for chunk in matches:
        parts = re.split(r",| and |\+|/", chunk)
        for part in parts:
            cleaned = re.sub(r"\b(stock|stocks|prices|market|firm|firms|company|companies|please|plz)\b", " ", part)
            cleaned = re.sub(r"\s+", " ", cleaned).strip()
            if len(cleaned) >= 2:
                names.append(cleaned)
    return names


def parse_comparison_targets(message):
    """Extract 2-4 company comparison targets from prompts like 'compare TSLA, F, and GM'."""
    raw = (message or "").strip()
    if not raw:
        return []

    lowered = normalize_case(raw)
    if not any(marker in lowered for marker in ["compare", "comparison", "vs", "versus"]):
        return []

    segment = raw
    m = re.search(r"(?:compare|comparison(?:\s+between)?|vs|versus)\s+(.+)", raw, flags=re.IGNORECASE)
    if m:
        segment = m.group(1).strip()
    segment = re.split(r"\b(?:on|for|based on|using)\b", segment, maxsplit=1, flags=re.IGNORECASE)[0].strip(" .,!?:;")

    candidates = []
    for ticker in extract_ticker_candidates(segment):
        if ticker not in candidates:
            candidates.append(ticker)

    parts = re.split(r",|\band\b|\bvs\b|\bversus\b|&|/", segment, flags=re.IGNORECASE)
    for part in parts:
        cleaned = re.sub(r"\b(?:stock|stocks|firm|firms|company|companies|please|plz|compare|comparison)\b", " ", part, flags=re.IGNORECASE)
        cleaned = re.sub(r"\s+", " ", cleaned).strip(" .,-")
        if len(cleaned) < 1:
            continue
        maybe_ticker = normalize_ticker_symbol(cleaned)
        if maybe_ticker and maybe_ticker not in candidates and len(maybe_ticker) <= 5:
            candidates.append(maybe_ticker)
            continue
        alias_ticker = COMPANY_ALIAS_TO_TICKER.get(normalize_case(cleaned))
        if alias_ticker and alias_ticker not in candidates:
            candidates.append(alias_ticker)
            continue
        if cleaned and cleaned not in candidates:
            candidates.append(cleaned)

    deduped = []
    for item in candidates:
        if item not in deduped:
            deduped.append(item)
    return deduped[:4] if len(deduped) >= 2 else []


def log_metric_validation_block(event, reason, details=None, user_id=None):
    """Audit blocked financial metric responses to prevent fabricated output."""
    payload = {
        "event": event,
        "reason": reason,
        "details": details or {},
        "user_id": sanitize_user_id(user_id or DEFAULT_USER_ID),
        "ts": utc_now_iso(),
    }
    print(f"[metric-validation-blocked] {json.dumps(payload, ensure_ascii=True)}")
    try:
        audit_user_id = sanitize_user_id(user_id or DEFAULT_USER_ID)
        user_state = ensure_finance_profiles(load_user_state(audit_user_id))
        finance_profile = user_state.get("finance_profile") or {}
        history = finance_profile.get("metric_validation_history")
        if not isinstance(history, list):
            history = []
        history.append(
            {
                "event": str(event or "unknown"),
                "reason": str(reason or "unknown"),
                "details": details or {},
                "created_at": payload["ts"],
            }
        )
        finance_profile["metric_validation_history"] = history[-200:]
        user_state["finance_profile"] = finance_profile
        save_user_state(audit_user_id, user_state)
    except Exception:
        pass


def is_non_public_comparison_target(raw_name):
    """Detect common non-public institutions for stock-style comparison guardrails."""
    return normalize_case(raw_name or "") in NON_PUBLIC_COMPARISON_ALIASES


def resolve_public_equity_symbol(raw_name):
    """Resolve target to a public-equity symbol only (not ETF/mutual-fund/platform)."""
    raw = (raw_name or "").strip()
    if not raw:
        return {"ok": False, "reason": "empty-target"}
    if is_non_public_comparison_target(raw):
        return {"ok": False, "reason": "non-public-firm"}

    candidate = normalize_ticker_symbol(raw)
    if not candidate:
        candidate = COMPANY_ALIAS_TO_TICKER.get(normalize_case(raw)) or ""

    if candidate:
        quote_payload = fetch_json_url(
            f"https://query1.finance.yahoo.com/v7/finance/quote?symbols={quote_plus(candidate)}"
        )
        result = ((quote_payload.get("quoteResponse") or {}).get("result") or [])
        if result:
            qtype = (result[0].get("quoteType") or "").upper()
            if qtype == "EQUITY":
                return {"ok": True, "symbol": candidate}

    search_payload = fetch_json_url(
        f"https://query1.finance.yahoo.com/v1/finance/search?q={quote_plus(raw)}"
    )
    for item in (search_payload.get("quotes") or []):
        qtype = (item.get("quoteType") or "").upper()
        symbol = normalize_ticker_symbol(item.get("symbol") or "")
        if symbol and qtype == "EQUITY":
            return {"ok": True, "symbol": symbol}

    return {"ok": False, "reason": "not-public-equity"}


def to_traceable_metric(value, source_field, source_url="", request_trace_id=""):
    """Attach source lineage to numeric metric values."""
    numeric = to_float_or_none(value)
    if numeric is None:
        return None
    return {
        "value": float(numeric),
        "source": source_field,
        "source_url": str(source_url or ""),
        "request_trace_id": str(request_trace_id or ""),
    }


def normalize_ratio_to_percent(raw_value):
    """Normalize API ratio values into percent scale for user display."""
    numeric = to_float_or_none(raw_value)
    if numeric is None:
        return None
    if -1.0 <= numeric <= 1.0:
        return numeric * 100.0
    return numeric


def get_comparison_data(firms, request_trace_id=""):
    """Aggregate only traceable API-sourced fundamentals for public equities."""
    entries = []
    blocked = []
    seen_symbols = set()

    for firm in firms or []:
        raw = (firm or "").strip()
        if not raw:
            continue
        resolved = resolve_public_equity_symbol(raw)
        if not resolved.get("ok"):
            blocked.append({"target": raw, "reason": resolved.get("reason") or "unresolved"})
            continue
        symbol = normalize_ticker_symbol(resolved.get("symbol") or "")
        if not symbol or symbol in seen_symbols:
            continue
        seen_symbols.add(symbol)
        entries.append({"input": raw, "symbol": symbol})
        if len(entries) >= 4:
            break

    if len(entries) < 2:
        return {}, blocked

    symbols = [entry["symbol"] for entry in entries]
    quotes, source_url = fetch_yahoo_quotes(symbols)
    result = {}
    for entry in entries:
        symbol = entry["symbol"]
        quote = quotes.get(symbol) or {}

        quote_type = (quote.get("quote_type") or "").upper()
        if quote_type and quote_type != "EQUITY":
            blocked.append({"target": entry["input"], "reason": f"non-equity-type:{quote_type}"})
            continue

        metrics = {
            "pe_ratio": to_traceable_metric(
                quote.get("trailing_pe"),
                "yahoo.v7.quote.trailingPE",
                source_url=source_url,
                request_trace_id=request_trace_id,
            ),
            "net_profit_margin": to_traceable_metric(
                normalize_ratio_to_percent(quote.get("profit_margins")),
                "yahoo.v7.quote.profitMargins",
                source_url=source_url,
                request_trace_id=request_trace_id,
            ),
            "debt_to_equity": to_traceable_metric(
                quote.get("debt_to_equity"),
                "yahoo.v7.quote.debtToEquity",
                source_url=source_url,
                request_trace_id=request_trace_id,
            ),
            "roe": to_traceable_metric(
                normalize_ratio_to_percent(quote.get("return_on_equity")),
                "yahoo.v7.quote.returnOnEquity",
                source_url=source_url,
                request_trace_id=request_trace_id,
            ),
        }
        if sum(1 for value in metrics.values() if value is not None) == 0:
            blocked.append({"target": entry["input"], "reason": "no-traceable-fundamentals"})
            continue

        result[symbol] = {
            "firm": symbol,
            "display_name": quote.get("name") or symbol,
            "metrics": metrics,
            "input": entry["input"],
            "source": "yahoo.v7.quote",
            "source_url": source_url,
            "request_trace_id": request_trace_id,
        }

    return result, blocked


def detect_comparison_priority(message):
    """Infer user-stated comparison priority from prompt text."""
    lowered = normalize_case(message or "")
    if any(marker in lowered for marker in ["safety", "safe", "low risk", "defensive", "stability"]):
        return "safety"
    if any(marker in lowered for marker in ["value", "cheap", "undervalued", "lower p/e", "valuation"]):
        return "value"
    if any(marker in lowered for marker in ["income", "dividend", "yield", "cash flow"]):
        return "income"
    if any(marker in lowered for marker in ["growth", "upside", "aggressive", "high return"]):
        return "growth"
    return "balanced"


def build_comparison_markdown_table(comparison_data):
    """Render side-by-side firm comparison from traceable metrics only."""
    rows = [
        "| Firm | P/E Ratio | Net Profit Margin | Debt-to-Equity | ROE |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]

    def metric_text(data, key, suffix=""):
        metric = ((data.get("metrics") or {}).get(key) if isinstance(data, dict) else None)
        if not metric:
            return "n/a"
        value = to_float_or_none(metric.get("value"))
        if value is None:
            return "n/a"
        if key == "debt_to_equity":
            return f"{value:.2f}{suffix}"
        return f"{value:.1f}{suffix}"

    for symbol, data in comparison_data.items():
        rows.append(
            f"| {symbol} | {metric_text(data, 'pe_ratio')} | {metric_text(data, 'net_profit_margin', '%')} | {metric_text(data, 'debt_to_equity')} | {metric_text(data, 'roe', '%')} |"
        )
    return "\n".join(rows)


def build_coach_comparison_verdict(comparison_data, priority="balanced"):
    """Generate qualitative verdict using only available sourced metrics."""
    rows = list(comparison_data.values())
    if len(rows) < 2:
        return "I could not build a valid sourced comparison for these targets."

    def metric_value(row, key, fallback):
        metric = ((row.get("metrics") or {}).get(key) if isinstance(row, dict) else None)
        if not metric:
            return fallback
        value = to_float_or_none(metric.get("value"))
        return fallback if value is None else float(value)

    growth_pick = max(rows, key=lambda r: (metric_value(r, "roe", -9999.0), metric_value(r, "net_profit_margin", -9999.0)))
    safety_pick = min(rows, key=lambda r: (metric_value(r, "debt_to_equity", 9999.0), -metric_value(r, "net_profit_margin", -9999.0)))
    value_pick = min(rows, key=lambda r: (metric_value(r, "pe_ratio", 9999.0), -metric_value(r, "net_profit_margin", -9999.0)))
    income_pick = max(rows, key=lambda r: (metric_value(r, "net_profit_margin", -9999.0), -metric_value(r, "debt_to_equity", 9999.0)))

    best_by_priority = {
        "growth": growth_pick,
        "safety": safety_pick,
        "value": value_pick,
        "income": income_pick,
        "balanced": max(rows, key=lambda r: (
            (metric_value(r, "roe", 0.0) * 0.45)
            + (metric_value(r, "net_profit_margin", 0.0) * 0.35)
            - (metric_value(r, "debt_to_equity", 0.0) * 10.0)
            - (metric_value(r, "pe_ratio", 0.0) * 0.05)
        )),
    }
    chosen_priority = priority if priority in best_by_priority else "balanced"
    best_pick = best_by_priority[chosen_priority]
    return f"Based on currently sourced fundamentals, {best_pick['firm']} aligns best with your {chosen_priority} priority."


def validate_traceable_comparison_metrics(comparison_data, request_trace_id=""):
    """Ensure every emitted numeric metric can be traced to a request-time source."""
    for symbol, row in (comparison_data or {}).items():
        row_trace_id = str((row.get("request_trace_id") if isinstance(row, dict) else "") or "")
        if request_trace_id and row_trace_id != request_trace_id:
            return False, f"request-trace-mismatch:{symbol}"
        metrics = row.get("metrics") if isinstance(row, dict) else None
        if not isinstance(metrics, dict):
            return False, f"missing-metrics:{symbol}"
        for key, metric in metrics.items():
            if metric is None:
                continue
            if not isinstance(metric, dict):
                return False, f"invalid-metric-format:{symbol}:{key}"
            if to_float_or_none(metric.get("value")) is None:
                return False, f"invalid-metric-value:{symbol}:{key}"
            if not (metric.get("source") or "").strip():
                return False, f"missing-metric-source:{symbol}:{key}"
            if not (metric.get("source_url") or "").strip():
                return False, f"missing-metric-source-url:{symbol}:{key}"
            metric_trace_id = str(metric.get("request_trace_id") or "")
            if request_trace_id and metric_trace_id != request_trace_id:
                return False, f"missing-or-mismatched-request-trace:{symbol}:{key}"
    return True, ""


def get_firm_comparison_reply(normalized_text, original_text, include_sources=False, user_id=DEFAULT_USER_ID):
    """Return deterministic side-by-side firm comparison table plus coach verdict."""
    targets = parse_comparison_targets(original_text)
    if len(targets) < 2:
        return ""

    request_trace_id = f"cmp-{int(time.time() * 1000)}-{secrets.token_hex(3)}"
    comparison_data, blocked = get_comparison_data(targets, request_trace_id=request_trace_id)
    if len(comparison_data) < 2:
        target_text = ", ".join(targets)
        non_public_targets = [row.get("target") for row in blocked if row.get("reason") in {"non-public-firm", "not-public-equity"}]
        if non_public_targets:
            return (
                f"{', '.join(non_public_targets)} are not publicly traded operating companies, so stock metrics like P/E or ROE do not apply. "
                "I do not currently have a reliable live source in this app for brokerage fee/account-structure comparison."
            )
        log_metric_validation_block(
            "firm-comparison",
            "insufficient-validated-targets",
            {"targets": targets, "blocked": blocked, "request_trace_id": request_trace_id},
            user_id=user_id,
        )
        return f"Data unavailable for a validated public-company comparison right now. Requested targets: {target_text}."

    is_valid, reason = validate_traceable_comparison_metrics(comparison_data, request_trace_id=request_trace_id)
    if not is_valid:
        log_metric_validation_block(
            "firm-comparison",
            reason,
            {"targets": targets, "request_trace_id": request_trace_id},
            user_id=user_id,
        )
        return "Data unavailable for comparison right now because sourced financial metrics could not be validated."

    if blocked:
        log_metric_validation_block(
            "firm-comparison",
            "partial-targets-blocked",
            {"targets": targets, "blocked": blocked, "request_trace_id": request_trace_id},
            user_id=user_id,
        )

    table = build_comparison_markdown_table(comparison_data)
    if not table.strip():
        log_metric_validation_block(
            "firm-comparison",
            "empty-comparison-table",
            {"targets": targets, "request_trace_id": request_trace_id},
            user_id=user_id,
        )
        return "Data unavailable for comparison right now because no traceable metrics were returned."

    priority = detect_comparison_priority(original_text)
    verdict = build_coach_comparison_verdict(comparison_data, priority=priority)
    blocked_line = ""
    if blocked:
        blocked_targets = [row.get("target") for row in blocked if row.get("target")]
        if blocked_targets:
            blocked_line = f"\n\nExcluded targets (not validated public-equity comparisons): {', '.join(blocked_targets)}."
    reply = f"{table}\n\n{verdict}{blocked_line}"
    return with_citations(reply, ["https://query1.finance.yahoo.com/v7/finance/quote"], include_sources)


def to_float_or_none(value):
    """Best-effort numeric conversion."""
    try:
        if value is None:
            return None
        return float(str(value).replace(",", "").strip())
    except Exception:
        return None


def normalize_city_key(text):
    """Normalize city string for lookup in PPP/cost index maps."""
    city = normalize_case(text or "")
    city = re.sub(r"[^a-z\s]", " ", city)
    city = re.sub(r"\s+", " ", city).strip()
    return city


def detect_city_from_text(text):
    """Best-effort city extraction from free-form user text."""
    lowered = normalize_case(text or "")
    candidates = sorted(CITY_COST_INDEX.keys(), key=len, reverse=True)
    for city in candidates:
        if re.search(rf"\b{re.escape(city)}\b", lowered):
            return city
    return ""


def fetch_fx_rates(base_currency="USD"):
    """Fetch FX rates with cache; fallback to a secondary public endpoint."""
    base = (base_currency or "USD").upper().strip()
    now_ts = time.time()
    with finance_cache_lock:
        bucket = fx_rate_cache.get(base)
        if bucket and now_ts - float(bucket.get("cached_at") or 0.0) <= FX_RATE_CACHE_TTL_SECONDS:
            return bucket.get("rates") or {}, bucket.get("source") or "", bucket.get("as_of_utc") or ""

    rates = {}
    source = ""
    as_of_utc = ""
    primary_url = f"https://open.er-api.com/v6/latest/{quote_plus(base)}"
    try:
        payload = fetch_json_url(primary_url)
        if str(payload.get("result") or "").lower() == "success":
            rates = payload.get("rates") or {}
            source = primary_url
            if payload.get("time_last_update_unix"):
                try:
                    ts = int(payload.get("time_last_update_unix"))
                    as_of_utc = datetime.fromtimestamp(ts, tz=timezone.utc).isoformat()
                except Exception:
                    as_of_utc = ""
    except Exception:
        rates = {}

    if not rates:
        fallback_url = f"https://api.exchangerate.host/latest?base={quote_plus(base)}"
        payload = fetch_json_url(fallback_url)
        rates = payload.get("rates") or {}
        source = fallback_url
        as_of_utc = payload.get("date") or ""

    with finance_cache_lock:
        fx_rate_cache[base] = {
            "cached_at": now_ts,
            "rates": rates,
            "source": source,
            "as_of_utc": as_of_utc,
        }
    return rates, source, as_of_utc


def parse_runway_buffer_payload(text):
    """Parse runway-buffer request fields from natural language."""
    raw = text or ""
    lowered = normalize_case(raw)
    city = detect_city_from_text(raw)
    base_city = BASELINE_COST_INDEX_CITY
    if "base city" in lowered or "compared to" in lowered:
        m = re.search(r"(?:base city|compared to)\s+([a-z\s]+)", lowered)
        if m:
            maybe = detect_city_from_text(m.group(1))
            if maybe:
                base_city = maybe

    capital_usd = None
    base_monthly_cap_usd = None
    months = None
    safety_buffer_months = None
    shadow_runway_enabled = None

    m_capital = re.search(r"(?:capital|runway|savings|cash|lump\s*sum)\s*(?:of|=|:)?\s*\$?\s*([0-9][0-9,]*(?:\.[0-9]+)?)", lowered)
    if m_capital:
        capital_usd = to_float_or_none(m_capital.group(1))

    m_budget = re.search(r"(?:monthly(?:\s+discretionary)?(?:\s+spending)?(?:\s+cap|\s+budget)?|budget|cap)\s*(?:of|=|:)?\s*\$?\s*([0-9][0-9,]*(?:\.[0-9]+)?)", lowered)
    if m_budget:
        base_monthly_cap_usd = to_float_or_none(m_budget.group(1))

    m_months = re.search(r"([0-9]{1,3})\s*(?:months|month|mos|mo)\b", lowered)
    if m_months:
        try:
            months = max(1, int(m_months.group(1)))
        except Exception:
            months = None

    m_safety = re.search(r"(?:safety\s+buffer|shadow\s+buffer|lock|reserve)\s*(?:of|=|:)?\s*([0-9]+(?:\.[0-9]+)?)\s*(?:months|month|mos|mo)?", lowered)
    if m_safety:
        safety_buffer_months = to_float_or_none(m_safety.group(1))

    if any(k in lowered for k in ["shadow runway on", "enable shadow runway", "turn on shadow runway"]):
        shadow_runway_enabled = True
    elif any(k in lowered for k in ["shadow runway off", "disable shadow runway", "turn off shadow runway"]):
        shadow_runway_enabled = False

    if capital_usd is None:
        nums = [to_float_or_none(v) for v in re.findall(r"\$?\s*([0-9][0-9,]*(?:\.[0-9]+)?)", lowered)]
        nums = [n for n in nums if isinstance(n, (int, float)) and n > 0]
        if nums:
            capital_usd = nums[0]
            if base_monthly_cap_usd is None and len(nums) >= 2:
                base_monthly_cap_usd = nums[1]

    return {
        "city": city,
        "base_city": base_city,
        "capital_usd": float(capital_usd or 0.0),
        "base_monthly_cap_usd": float(base_monthly_cap_usd or 0.0),
        "shadow_runway_enabled": shadow_runway_enabled,
        "safety_buffer_months": float(safety_buffer_months or 0.0),
        "months": months,
    }


def build_runway_buffer_metrics(
    capital_usd,
    current_city,
    base_monthly_cap_usd=0.0,
    base_city=BASELINE_COST_INDEX_CITY,
    shadow_runway_enabled=False,
    safety_buffer_months=0.0,
):
    """Compute PPP-adjusted runway and discretionary cap using live FX rates."""
    city_key = normalize_city_key(current_city)
    base_city_key = normalize_city_key(base_city) or BASELINE_COST_INDEX_CITY
    current_cfg = CITY_COST_INDEX.get(city_key)
    base_cfg = CITY_COST_INDEX.get(base_city_key)
    if not current_cfg:
        raise ValueError("Unsupported city for runway buffer. Add it to the cost-index map.")
    if not base_cfg:
        base_cfg = CITY_COST_INDEX[BASELINE_COST_INDEX_CITY]

    capital_usd = float(capital_usd or 0.0)
    if capital_usd <= 0:
        raise ValueError("capital_usd must be greater than zero.")

    base_index = float(base_cfg.get("cost_index") or 100.0)
    local_index = float(current_cfg.get("cost_index") or 100.0)
    if base_monthly_cap_usd and float(base_monthly_cap_usd) > 0:
        baseline_monthly = float(base_monthly_cap_usd)
    else:
        baseline_monthly = max(100.0, capital_usd / 12.0)

    ppp_multiplier = base_index / local_index if local_index > 0 else 1.0
    ppp_monthly_cap_usd = baseline_monthly * ppp_multiplier

    target_currency = (current_cfg.get("currency") or "USD").upper()
    rates, fx_source, fx_as_of = fetch_fx_rates("USD")
    fx_rate = to_float_or_none((rates or {}).get(target_currency))
    if target_currency == "USD":
        fx_rate = 1.0
    if fx_rate is None or fx_rate <= 0:
        raise ValueError(f"FX rate unavailable for {target_currency}.")

    ppp_monthly_cap_local = ppp_monthly_cap_usd * fx_rate
    runway_months_nominal = (capital_usd / baseline_monthly) if baseline_monthly > 0 else 0.0
    runway_months_ppp = (capital_usd / ppp_monthly_cap_usd) if ppp_monthly_cap_usd > 0 else 0.0

    safety_months = max(0.0, float(safety_buffer_months or 0.0))
    shadow_enabled = bool(shadow_runway_enabled)
    locked_months = min(safety_months, runway_months_ppp) if shadow_enabled else 0.0
    runway_display_months = max(0.0, runway_months_ppp - locked_months)
    display_color = "orange" if shadow_enabled and locked_months > 0 else "default"

    return {
        "as_of_utc": utc_now_iso(),
        "base_city": base_city_key,
        "current_city": city_key,
        "base_currency": "USD",
        "target_currency": target_currency,
        "capital_usd": capital_usd,
        "base_monthly_cap_usd": baseline_monthly,
        "ppp_adjusted_monthly_cap_usd": ppp_monthly_cap_usd,
        "ppp_adjusted_monthly_cap_local": ppp_monthly_cap_local,
        "cost_index_base": base_index,
        "cost_index_local": local_index,
        "ppp_multiplier": ppp_multiplier,
        "fx_rate_usd_to_target": fx_rate,
        "fx_source": fx_source,
        "fx_as_of_utc": fx_as_of,
        "runway_months_nominal": runway_months_nominal,
        "runway_months_ppp_adjusted": runway_months_ppp,
        "shadow_runway_enabled": shadow_enabled,
        "safety_buffer_months": safety_months,
        "locked_months": locked_months,
        "runway_display_months": runway_display_months,
        "runway_display_color": display_color,
    }


def parse_opportunity_cost_payload(text):
    """Parse purchase intent for opportunity-cost gating (Alpha Rule)."""
    raw = (text or "").strip()
    lowered = normalize_case(raw)
    if not raw:
        return None

    intent_markers = [
        "buy", "purchase", "spend", "pay", "checkout", "get this", "cop this", "order",
        "i want", "i'm buying", "im buying", "should i buy", "should i purchase",
    ]
    if not any(marker in lowered for marker in intent_markers):
        return None

    amount = None
    amount_match = re.search(r"\$\s*([0-9][0-9,]*(?:\.[0-9]+)?)", raw)
    if amount_match:
        amount = to_float_or_none(amount_match.group(1))
    if amount is None:
        fallback_nums = [to_float_or_none(v) for v in re.findall(r"\b([0-9][0-9,]*(?:\.[0-9]+)?)\b", raw)]
        fallback_nums = [n for n in fallback_nums if isinstance(n, (int, float)) and n > 0]
        if fallback_nums:
            amount = fallback_nums[0]

    item = "purchase"
    item_match = re.search(r"(?:buy|purchase|get|order)\s+(?:a|an|the)?\s*([^,.!?]+)", lowered)
    if item_match:
        item_text = re.sub(r"\s+for\s+\$?[0-9][0-9,]*(?:\.[0-9]+)?", "", item_match.group(1), flags=re.IGNORECASE)
        item = re.sub(r"\s+", " ", item_text).strip(" .,!?") or item

    years = OPPORTUNITY_COST_DEFAULT_YEARS
    years_match = re.search(r"([0-9]{1,2})\s*(?:years|year|yrs|yr)\b", lowered)
    if years_match:
        try:
            years = max(1, min(50, int(years_match.group(1))))
        except Exception:
            years = OPPORTUNITY_COST_DEFAULT_YEARS

    annual_return = OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN
    return_match = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%\s*(?:return|roi|index|annual)?", lowered)
    if return_match:
        pct = to_float_or_none(return_match.group(1))
        if pct is not None:
            annual_return = max(0.0, min(1.0, float(pct) / 100.0))

    essential_terms = {
        "rent", "mortgage", "medicine", "medical", "hospital", "insurance", "tuition", "debt", "loan", "groceries", "grocery", "utility", "utilities", "electricity", "water", "internet bill", "tax", "fuel", "gas",
    }
    non_essential_terms = {
        "luxury", "designer", "watch", "bag", "shoes", "sneakers", "iphone", "phone", "laptop", "vacation", "trip", "holiday", "jewelry", "gaming", "console", "perfume", "cosmetic", "subscription",
    }
    is_essential = any(term in lowered for term in essential_terms)
    is_non_essential = any(term in lowered for term in non_essential_terms) or not is_essential

    return {
        "amount_usd": float(amount or 0.0),
        "item": item,
        "years": years,
        "annual_return": annual_return,
        "is_non_essential": is_non_essential,
        "raw_text": raw,
    }


def parse_purchase_psychology(user_message):
    """Low-token psychological parse for spending-intent messages.

    Returns a strict raw JSON string in this exact key shape:
    {"fatigue_score": 1-10, "cognitive_bias": "FOMO"|"Boredom"|"None", "transaction_type": "Impulse"|"Planned"}
    """
    default_payload = {
        "fatigue_score": 1,
        "cognitive_bias": "None",
        "transaction_type": "Planned",
    }
    raw = (user_message or "").strip()
    if not raw:
        return json.dumps(default_payload)

    lowered = normalize_case(raw)
    intent_markers = [
        "buy", "purchase", "spend", "pay", "checkout", "order", "cart", "want to buy", "i'm buying", "im buying",
    ]
    if not any(marker in lowered for marker in intent_markers):
        return json.dumps(default_payload)

    instruction = (
        "Classify purchase psych. Return ONLY raw JSON. No prose/markdown. "
        "Keys exactly: fatigue_score(int 1-10), cognitive_bias(FOMO|Boredom|None), "
        "transaction_type(Impulse|Planned)."
    )
    try:
        response = frontier_client.chat.completions.create(
            model="gpt-4",
            messages=[
                {"role": "system", "content": instruction},
                {"role": "user", "content": raw[:280]},
            ],
            temperature=0.0,
            max_tokens=50,
        )
        content = (((response.choices or [{}])[0]).message.content or "").strip()
        match = re.search(r"\{.*\}", content, flags=re.DOTALL)
        candidate = match.group(0).strip() if match else content
        parsed = json.loads(candidate)
    except Exception:
        parsed = default_payload

    fatigue = int(to_float_or_none(parsed.get("fatigue_score")) or 1)
    fatigue = max(1, min(10, fatigue))

    bias = str(parsed.get("cognitive_bias") or "None").strip()
    if bias not in {"FOMO", "Boredom", "None"}:
        bias = "None"

    txn_type = str(parsed.get("transaction_type") or "Planned").strip()
    if txn_type not in {"Impulse", "Planned"}:
        txn_type = "Planned"

    return json.dumps(
        {
            "fatigue_score": fatigue,
            "cognitive_bias": bias,
            "transaction_type": txn_type,
        }
    )


def build_dopamine_swap_offer(purchase_amount_usd=0.0):
    """Return a motivation-preserving dopamine swap alternative to impulse spending."""
    amount = max(0.0, float(purchase_amount_usd or 0.0))
    shown_amount = amount if amount > 0 else 100.0
    micro = round(shown_amount * 0.10, 2)
    micro = max(5.0, min(25.0, micro))
    return (
        f"I have paused this ${shown_amount:.2f} purchase. But let's compromise: I just unlocked a high-yield "
        f"micro-investment challenge. Put ${micro:.2f} into your investment bucket right now, and I will let you play a "
        "quick 2-minute strategic mini-game, or I will unlock a highly-rated educational article on your dashboard. "
        "Swap cheap purchase dopamine for progress dopamine."
    )


def evaluate_behavioral_gate(user_message, user_state, user_id=DEFAULT_USER_ID):
    """Evaluate purchase psychology and activate a 12-hour circuit breaker when risky."""
    user_state = ensure_finance_profiles(user_state)
    profile = user_state.get("behavior_budget_profile") or {}
    user_profile = user_state.get("profile") or {}
    now = datetime.now(timezone.utc)

    gate_until_raw = (profile.get("circuit_breaker_until") or "").strip()
    gate_until = None
    if gate_until_raw:
        try:
            gate_until = datetime.fromisoformat(gate_until_raw)
        except Exception:
            gate_until = None

    if gate_until and now >= gate_until:
        profile["circuit_breaker_active"] = False
        profile["circuit_breaker_until"] = ""
        user_state["behavior_budget_profile"] = profile

    lowered = normalize_case(user_message or "")
    intent_markers = [
        "buy", "purchase", "spend", "pay", "checkout", "order", "cart", "want to buy", "i'm buying", "im buying",
    ]
    is_spending_intent = any(marker in lowered for marker in intent_markers)

    locked_categories = {
        normalize_intent_text(category or "").strip()
        for category in (profile.get("locked_categories") or [])
    }
    locked_categories = {category for category in locked_categories if category}

    pending_category = normalize_intent_text(profile.get("break_lock_confirm_category") or "").strip()
    pending_until = parse_iso_datetime(profile.get("break_lock_confirm_until") or "")
    try:
        pending_step = int(profile.get("break_lock_confirm_step") or 0)
    except Exception:
        pending_step = 0
    pending_step = max(0, min(3, pending_step))
    if pending_until and now >= pending_until:
        profile["break_lock_confirm_category"] = ""
        profile["break_lock_confirm_until"] = ""
        profile["break_lock_confirm_step"] = 0
        pending_category = ""
        pending_until = None
        pending_step = 0

    first_confirmation = re.search(r"\bi\s+confirm\s+break\s+lock(?!\s+again\b)(?:\s+for)?\s+([a-zA-Z ]{2,40})\b", lowered)
    if first_confirmation:
        confirm_category = normalize_intent_text(first_confirmation.group(1) or "").strip()
        if confirm_category and confirm_category in locked_categories:
            if pending_category == confirm_category and pending_until is not None and now < pending_until and pending_step == 1:
                profile["break_lock_confirm_step"] = 2
                user_state["behavior_budget_profile"] = profile
                return {
                    "active": True,
                    "just_triggered": False,
                    "until": profile.get("break_lock_confirm_until") or "",
                    "warning": "First override confirmation accepted; second explicit confirmation required.",
                    "message": (
                        f"Step 1/2 accepted for '{confirm_category}'. To proceed, type exactly: "
                        f"I CONFIRM BREAK LOCK AGAIN {confirm_category}"
                    ),
                    "state": user_state,
                }
            return {
                "active": True,
                "just_triggered": False,
                "until": profile.get("break_lock_confirm_until") or "",
                "warning": "Override confirmation attempted before guardrail challenge was armed.",
                "message": (
                    f"No active lock-break challenge found for '{confirm_category}'. "
                    "Attempt the locked spend first to arm the two-step confirmation window."
                ),
                "state": user_state,
            }

    second_confirmation = re.search(r"\bi\s+confirm\s+break\s+lock\s+again(?:\s+for)?\s+([a-zA-Z ]{2,40})\b", lowered)
    if second_confirmation:
        confirm_category = normalize_intent_text(second_confirmation.group(1) or "").strip()
        if confirm_category and confirm_category in locked_categories:
            if pending_category == confirm_category and pending_until is not None and now < pending_until and pending_step == 2:
                profile["break_lock_confirm_step"] = 3
                user_state["behavior_budget_profile"] = profile
                return {
                    "active": True,
                    "just_triggered": False,
                    "until": profile.get("break_lock_confirm_until") or "",
                    "warning": "Second override confirmation accepted; temporary override is armed.",
                    "message": (
                        f"Step 2/2 accepted for '{confirm_category}'. Override is armed for 10 minutes. "
                        "If you still choose to spend, send your purchase now."
                    ),
                    "state": user_state,
                }
            return {
                "active": True,
                "just_triggered": False,
                "until": profile.get("break_lock_confirm_until") or "",
                "warning": "Second confirmation rejected because first confirmation is missing or expired.",
                "message": (
                    f"Second confirmation for '{confirm_category}' was rejected. "
                    f"Start again with: I CONFIRM BREAK LOCK {confirm_category}"
                ),
                "state": user_state,
            }

    detected_category = ""
    parsed_spend = parse_spend_log_payload(user_message)
    if parsed_spend:
        detected_category = normalize_intent_text(parsed_spend.get("category") or "").strip()
    if not detected_category:
        detected_category = extract_spend_category_hint(user_message)

    if is_spending_intent and detected_category and detected_category in locked_categories:
        has_valid_override = (
            pending_category == detected_category
            and pending_until is not None
            and now < pending_until
            and pending_step == 3
        )
        if has_valid_override:
            profile["break_lock_confirm_category"] = ""
            profile["break_lock_confirm_until"] = ""
            profile["break_lock_confirm_step"] = 0
            user_state["behavior_budget_profile"] = profile
            analytics_sql_insert_guardrail_override(user_id, detected_category, created_at=utc_now_iso())
        else:
            profile["break_lock_confirm_category"] = detected_category
            profile["break_lock_confirm_until"] = (now + timedelta(minutes=10)).isoformat()
            profile["break_lock_confirm_step"] = 1
            user_state["behavior_budget_profile"] = profile
            accountability_target = (user_profile.get("accountability_target") or "").strip()
            target_tail = f" Goal on the line: {accountability_target}." if accountability_target else ""
            return {
                "active": True,
                "just_triggered": True,
                "until": profile["break_lock_confirm_until"],
                "warning": "Locked spending category attempted; require two explicit manual confirmations.",
                "message": (
                    f"Hard stop: '{detected_category}' is a locked category you explicitly set.{target_tail} "
                    "To proceed, type exactly (step 1/2): "
                    f"I CONFIRM BREAK LOCK {detected_category}"
                ),
                "state": user_state,
            }

    raw_json = parse_purchase_psychology(user_message)
    try:
        parsed = json.loads(raw_json)
    except Exception:
        parsed = {"fatigue_score": 1, "cognitive_bias": "None", "transaction_type": "Planned"}

    fatigue = int(to_float_or_none(parsed.get("fatigue_score")) or 1)
    bias = str(parsed.get("cognitive_bias") or "None")
    txn = str(parsed.get("transaction_type") or "Planned")
    triggered = fatigue >= 8 or bias != "None" or txn == "Impulse"
    purchase_payload = parse_opportunity_cost_payload(user_message) or {}
    purchase_amount = float(purchase_payload.get("amount_usd") or 0.0)
    dopamine_swap_message = build_dopamine_swap_offer(purchase_amount)

    if triggered and is_spending_intent:
        until = now + timedelta(hours=12)
        profile["circuit_breaker_active"] = True
        profile["circuit_breaker_until"] = until.isoformat()
        profile["last_purchase_psychology"] = {
            "fatigue_score": max(1, min(10, fatigue)),
            "cognitive_bias": bias if bias in {"FOMO", "Boredom", "None"} else "None",
            "transaction_type": txn if txn in {"Impulse", "Planned"} else "Planned",
            "created_at": utc_now_iso(),
        }
        profile["last_dopamine_swap_offer"] = {
            "purchase_amount_usd": purchase_amount,
            "message": dopamine_swap_message,
            "created_at": utc_now_iso(),
        }
        user_state["behavior_budget_profile"] = profile
        return {
            "active": True,
            "just_triggered": True,
            "until": profile["circuit_breaker_until"],
            "psychology": profile["last_purchase_psychology"],
            "warning": "Behavioral circuit breaker is active. Strongly discourage purchase execution for 12 hours and recommend a cooling-off period.",
            "message": (
                f"Quick pause recommendation: your current pattern looks high-risk (fatigue/bias/impulse). "
                f"Please wait 12 hours before completing this transaction.\n\n{dopamine_swap_message}"
            ),
            "state": user_state,
        }

    if is_spending_intent and bool(profile.get("circuit_breaker_active")) and profile.get("circuit_breaker_until"):
        existing_offer = (profile.get("last_dopamine_swap_offer") or {}).get("message") or dopamine_swap_message
        return {
            "active": True,
            "just_triggered": False,
            "until": profile.get("circuit_breaker_until"),
            "psychology": profile.get("last_purchase_psychology") or {},
            "warning": "Behavioral circuit breaker remains active. Advise delaying non-essential purchases until the timer ends.",
            "message": (
                "Your behavioral circuit breaker is still active. Please wait until the 12-hour window ends before executing this purchase.\n\n"
                f"{existing_offer}"
            ),
            "state": user_state,
        }

    return {
        "active": False,
        "just_triggered": False,
        "until": "",
        "psychology": {
            "fatigue_score": max(1, min(10, fatigue)),
            "cognitive_bias": bias if bias in {"FOMO", "Boredom", "None"} else "None",
            "transaction_type": txn if txn in {"Impulse", "Planned"} else "Planned",
        },
        "warning": "",
        "message": "",
        "state": user_state,
    }


def build_opportunity_cost_gate(amount_usd, years=OPPORTUNITY_COST_DEFAULT_YEARS, annual_return=OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN):
    """Compute future value and opportunity cost for a one-time expense."""
    amount = float(amount_usd or 0.0)
    if amount <= 0:
        raise ValueError("amount_usd must be greater than zero.")
    horizon_years = int(max(1, min(50, int(years or OPPORTUNITY_COST_DEFAULT_YEARS))))
    rate = float(annual_return if annual_return is not None else OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN)
    rate = max(0.0, min(1.0, rate))

    future_value = amount * ((1.0 + rate) ** horizon_years)
    opportunity_cost = max(0.0, future_value - amount)
    return {
        "as_of_utc": utc_now_iso(),
        "amount_usd": amount,
        "years": horizon_years,
        "annual_return": rate,
        "future_value_usd": future_value,
        "opportunity_cost_usd": opportunity_cost,
        "formula": "FV = PV * (1 + r)^n",
    }


def is_discretionary_expense_category(category):
    """Best-effort classification for discretionary spend categories."""
    cat = normalize_case(category or "").strip()
    if not cat:
        return False
    essential = {
        "rent", "mortgage", "groceries", "grocery", "transport", "insurance", "medical", "medicine",
        "tuition", "utility", "utilities", "electricity", "water", "tax", "loan", "debt",
    }
    discretionary = {
        "takeout", "food", "shopping", "entertainment", "drinks", "coffee", "luxury", "travel",
        "vacation", "gaming", "subscription", "hobbies", "restaurants",
    }
    if cat in essential:
        return False
    if cat in discretionary:
        return True
    return False


def build_dynamic_opportunity_cost_projection(amount_usd, annual_return=0.075, horizons=(10, 20, 30)):
    """Project what a discretionary expense could become if invested over multiple horizons."""
    amount = float(amount_usd or 0.0)
    if amount <= 0:
        return None
    rate = max(0.0, min(1.0, float(annual_return or 0.075)))
    rows = []
    for years in horizons:
        gate = build_opportunity_cost_gate(amount, years=int(years), annual_return=rate)
        rows.append({
            "years": int(years),
            "future_value_usd": gate.get("future_value_usd") or 0.0,
            "opportunity_cost_usd": gate.get("opportunity_cost_usd") or 0.0,
        })
    return {
        "amount_usd": amount,
        "annual_return": rate,
        "horizons": rows,
    }


def render_dynamic_opportunity_cost_projection(projection):
    """Render the multi-horizon opportunity-cost projection as concise user text."""
    if not projection:
        return ""
    rate_pct = float(projection.get("annual_return") or 0.0) * 100.0
    parts = []
    for row in projection.get("horizons") or []:
        parts.append(f"{int(row.get('years') or 0)}y: ${float(row.get('future_value_usd') or 0.0):.2f}")
    if not parts:
        return ""
    return (
        f"Assumption-based projection (illustrative, not guaranteed): if invested in a simple index fund at an assumed {rate_pct:.1f}% annual return, this could grow to "
        + ", ".join(parts)
        + "."
    )


def mark_quote_provider_attempt(provider):
    """Update provider health metrics for an attempt."""
    with finance_cache_lock:
        bucket = finance_provider_health.setdefault(provider, {})
        bucket["last_attempt"] = utc_now_iso()


def mark_quote_provider_success(provider):
    """Update provider health metrics for a successful response."""
    with finance_cache_lock:
        bucket = finance_provider_health.setdefault(provider, {})
        bucket["last_success"] = utc_now_iso()
        bucket["last_error"] = ""
        bucket["last_error_type"] = ""
        bucket["last_error_http_status"] = 0
        bucket["cooldown_until"] = ""
        bucket["cooldown_reason"] = ""
        bucket["success_count"] = int(bucket.get("success_count", 0)) + 1


def classify_provider_error(err):
    """Classify provider error to drive cooldown behavior and operator diagnostics."""
    message = (str(err) or "error").strip()
    lowered = normalize_case(message)
    status = 0
    m = re.search(r"http\s+error\s+(\d{3})", lowered)
    if m:
        try:
            status = int(m.group(1))
        except Exception:
            status = 0

    if status == 429 or "rate limit" in lowered or "too many requests" in lowered:
        return "rate_limit", status
    if status in {401, 403} or "unauthorized" in lowered or "forbidden" in lowered:
        return "auth", status
    if status == 404 or "not found" in lowered:
        return "not_found", status
    if "timed out" in lowered or "timeout" in lowered:
        return "timeout", status
    if "temporary failure" in lowered or "connection reset" in lowered:
        return "network", status
    return "unknown", status


def provider_cooldown_seconds(error_type):
    """Map error type to a cautious cooldown duration."""
    if error_type == "rate_limit":
        return max(30, QUOTE_PROVIDER_RATE_LIMIT_COOLDOWN_SECONDS)
    if error_type == "auth":
        return max(60, QUOTE_PROVIDER_AUTH_COOLDOWN_SECONDS)
    if error_type == "not_found":
        return max(60, QUOTE_PROVIDER_NOT_FOUND_COOLDOWN_SECONDS)
    return max(30, QUOTE_PROVIDER_BASE_COOLDOWN_SECONDS)


def mark_quote_provider_error(provider, err):
    """Update provider health metrics for a failed response."""
    error_type, http_status = classify_provider_error(err)
    cooldown_seconds = provider_cooldown_seconds(error_type)
    cooldown_until = (datetime.now(timezone.utc) + timedelta(seconds=cooldown_seconds)).isoformat()

    with finance_cache_lock:
        bucket = finance_provider_health.setdefault(provider, {})
        bucket["last_error"] = (str(err) or "error")[:300]
        bucket["last_error_type"] = error_type
        bucket["last_error_http_status"] = int(http_status or 0)
        bucket["cooldown_until"] = cooldown_until
        bucket["cooldown_reason"] = f"{error_type}:{http_status or 'n/a'}"
        bucket["error_count"] = int(bucket.get("error_count", 0)) + 1


def get_provider_cooldown_state(provider):
    """Return whether provider is in cooldown and metadata for diagnostics."""
    with finance_cache_lock:
        bucket = finance_provider_health.setdefault(provider, {})
        until_raw = str(bucket.get("cooldown_until") or "")
        reason = str(bucket.get("cooldown_reason") or "")
    until_dt = parse_iso_datetime(until_raw)
    if not until_dt:
        return False, 0, reason
    now_dt = datetime.now(timezone.utc)
    remaining = int((until_dt - now_dt).total_seconds())
    if remaining <= 0:
        return False, 0, reason
    return True, remaining, reason


def mark_quote_provider_skipped(provider, reason):
    """Track provider skips (e.g., cooldown) for observability."""
    with finance_cache_lock:
        bucket = finance_provider_health.setdefault(provider, {})
        bucket["last_skip"] = f"{utc_now_iso()}::{reason[:180]}"
        bucket["skip_count"] = int(bucket.get("skip_count", 0)) + 1


def fetch_yahoo_quotes(symbols):
    """Primary provider: Yahoo Finance quote API."""
    if not symbols:
        return {}, ""
    joined = ",".join(symbols)
    source_url = f"https://query1.finance.yahoo.com/v7/finance/quote?symbols={quote_plus(joined)}"
    fetched = []
    try:
        payload = fetch_json_url(source_url)
        fetched = ((payload.get("quoteResponse") or {}).get("result") or [])
    except Exception:
        fetched = []

    quotes = {}
    for item in fetched:
        symbol = normalize_ticker_symbol(item.get("symbol") or "")
        if not symbol:
            continue
        quotes[symbol] = {
            "symbol": symbol,
            "name": item.get("longName") or item.get("shortName") or symbol,
            "price": item.get("regularMarketPrice"),
            "currency": item.get("currency") or "USD",
            "exchange": item.get("fullExchangeName") or item.get("exchange") or "",
            "change_percent": item.get("regularMarketChangePercent"),
            "market_time": item.get("regularMarketTime"),
            "beta": item.get("beta"),
            "market_cap": item.get("marketCap"),
            "quote_type": item.get("quoteType") or "",
            "trailing_pe": item.get("trailingPE"),
            "profit_margins": item.get("profitMargins"),
            "debt_to_equity": item.get("debtToEquity"),
            "return_on_equity": item.get("returnOnEquity"),
            "provider": "yahoo",
            "source_url": source_url,
            "price_source_field": "regularMarketPrice",
            "change_percent_source_field": "regularMarketChangePercent",
            "market_time_source_field": "regularMarketTime",
        }

    # Yahoo quote endpoint can intermittently fail per-IP. Fall back to chart endpoint.
    missing = [s for s in symbols if normalize_ticker_symbol(s) not in quotes]
    if missing:
        chart_quotes, chart_source = fetch_yahoo_chart_quotes(missing)
        for symbol, quote in chart_quotes.items():
            if symbol not in quotes:
                quotes[symbol] = quote
        if chart_source:
            source_url = f"{source_url} | {chart_source}"

    return quotes, source_url


def fetch_yahoo_chart_quotes(symbols):
    """Fallback Yahoo provider using chart API for regular market price/time."""
    if not symbols:
        return {}, ""

    quotes = {}
    source_urls = []
    for raw in symbols:
        symbol = normalize_ticker_symbol(raw)
        if not symbol:
            continue
        url = f"https://query1.finance.yahoo.com/v8/finance/chart/{quote_plus(symbol)}?interval=1d&range=1d"
        try:
            payload = fetch_json_url(url)
            result = ((payload.get("chart") or {}).get("result") or [])
            if not result:
                continue
            meta = (result[0] or {}).get("meta") or {}
            market_price = to_float_or_none(meta.get("regularMarketPrice"))
            market_time = to_int_or_none(meta.get("regularMarketTime"))
            if market_price is None:
                continue

            prev_close = to_float_or_none(meta.get("previousClose"))
            change_percent = None
            if prev_close and prev_close > 0:
                change_percent = ((market_price - prev_close) / prev_close) * 100.0

            quotes[symbol] = {
                "symbol": symbol,
                "name": meta.get("longName") or meta.get("shortName") or symbol,
                "price": market_price,
                "currency": meta.get("currency") or "USD",
                "exchange": meta.get("fullExchangeName") or meta.get("exchangeName") or "",
                "change_percent": change_percent,
                "market_time": market_time,
                "beta": None,
                "market_cap": None,
                "provider": "yahoo_chart",
                "source_url": url,
                "price_source_field": "chart.result[0].meta.regularMarketPrice",
                "change_percent_source_field": "chart.result[0].meta.previousClose+regularMarketPrice",
                "market_time_source_field": "chart.result[0].meta.regularMarketTime",
            }
            source_urls.append(url)
        except Exception:
            continue

    return quotes, (" | ".join(source_urls) if source_urls else "")


def symbol_to_stooq(symbol):
    """Map ticker to Stooq format (best effort)."""
    s = normalize_ticker_symbol(symbol)
    if not s:
        return ""
    return f"{s.lower().replace('.', '-')}.us"


def fetch_stooq_quotes(symbols):
    """Secondary provider: Stooq CSV quote endpoint."""
    if not symbols:
        return {}, ""
    mapping = {symbol_to_stooq(s): normalize_ticker_symbol(s) for s in symbols}
    stooq_symbols = [k for k in mapping.keys() if k]
    if not stooq_symbols:
        return {}, ""

    url = f"https://stooq.com/q/l/?s={','.join(stooq_symbols)}&f=sd2t2ohlcv&h&e=csv"
    csv_text = fetch_text_url(url)
    lines = [line.strip() for line in csv_text.splitlines() if line.strip()]
    if len(lines) <= 1:
        return {}, url

    quotes = {}
    for row in lines[1:]:
        cols = [c.strip().strip('"') for c in row.split(",")]
        if len(cols) < 8:
            continue
        sym_raw = cols[0].lower()
        symbol = mapping.get(sym_raw)
        if not symbol:
            continue
        close_price = to_float_or_none(cols[6])
        if close_price is None:
            continue
        date_part = cols[1] if cols[1] and cols[1] != "N/D" else ""
        time_part = cols[2] if cols[2] and cols[2] != "N/D" else "00:00:00"
        market_time = None
        if date_part:
            try:
                dt = datetime.strptime(f"{date_part} {time_part}", "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
                market_time = int(dt.timestamp())
            except Exception:
                market_time = None
        quotes[symbol] = {
            "symbol": symbol,
            "name": symbol,
            "price": close_price,
            "currency": "USD",
            "exchange": "STOOQ",
            "change_percent": None,
            "market_time": market_time,
            "beta": None,
            "market_cap": None,
            "provider": "stooq",
            "source_url": url,
            "price_source_field": "stooq.csv.close",
            "change_percent_source_field": "",
            "market_time_source_field": "stooq.csv.date+time",
        }
    return quotes, url


def fetch_alpha_vantage_quotes(symbols):
    """Tertiary provider: Alpha Vantage GLOBAL_QUOTE (requires API key)."""
    if not symbols or not ALPHA_VANTAGE_API_KEY:
        return {}, ""
    quotes = {}
    source_urls = []
    for symbol in symbols:
        normalized = normalize_ticker_symbol(symbol)
        if not normalized:
            continue
        url = (
            "https://www.alphavantage.co/query?function=GLOBAL_QUOTE"
            f"&symbol={quote_plus(normalized)}&apikey={quote_plus(ALPHA_VANTAGE_API_KEY)}"
        )
        try:
            payload = fetch_json_url(url)
            source_urls.append(url)
            gq = payload.get("Global Quote") or {}
            price = to_float_or_none(gq.get("05. price"))
            if price is None:
                continue
            change_percent_raw = (gq.get("10. change percent") or "").replace("%", "").strip()
            change_percent = to_float_or_none(change_percent_raw)
            market_time = None
            latest_day = (gq.get("07. latest trading day") or "").strip()
            if latest_day:
                try:
                    dt = datetime.strptime(latest_day, "%Y-%m-%d").replace(tzinfo=timezone.utc)
                    market_time = int(dt.timestamp())
                except Exception:
                    market_time = None
            quotes[normalized] = {
                "symbol": normalized,
                "name": normalized,
                "price": price,
                "currency": "USD",
                "exchange": "ALPHA_VANTAGE",
                "change_percent": change_percent,
                "market_time": market_time,
                "beta": None,
                "market_cap": None,
                "provider": "alpha_vantage",
                "source_url": url,
                "price_source_field": "Global Quote.05. price",
                "change_percent_source_field": "Global Quote.10. change percent",
                "market_time_source_field": "Global Quote.07. latest trading day",
            }
        except Exception:
            continue
    return quotes, (source_urls[0] if source_urls else "")


def fetch_twelvedata_quotes(symbols):
    """Tertiary provider: TwelveData real-time price endpoint."""
    if not symbols:
        return {}, ""

    api_key = TWELVEDATA_API_KEY or "demo"
    quotes = {}
    source_urls = []
    for symbol in symbols:
        normalized = normalize_ticker_symbol(symbol)
        if not normalized:
            continue
        price_url = f"https://api.twelvedata.com/price?symbol={quote_plus(normalized)}&apikey={quote_plus(api_key)}"
        quote_url = f"https://api.twelvedata.com/quote?symbol={quote_plus(normalized)}&apikey={quote_plus(api_key)}"
        try:
            payload = fetch_json_url(price_url)
            source_urls.append(price_url)
            price = to_float_or_none(payload.get("price"))
            if price is None:
                continue

            change_percent = None
            market_time = None
            try:
                quote_payload = fetch_json_url(quote_url)
                source_urls.append(quote_url)
                change_percent = to_float_or_none(quote_payload.get("percent_change"))
                datetime_raw = (quote_payload.get("datetime") or "").strip()
                if datetime_raw:
                    dt = datetime.strptime(datetime_raw, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
                    market_time = int(dt.timestamp())
            except Exception:
                pass

            if market_time is None:
                # Keep price traceable even when quote endpoint omits datetime for demo/limited plans.
                market_time = int(time.time())

            quotes[normalized] = {
                "symbol": normalized,
                "name": normalized,
                "price": price,
                "currency": "USD",
                "exchange": "TWELVEDATA",
                "change_percent": change_percent,
                "market_time": market_time,
                "beta": None,
                "market_cap": None,
                "provider": "twelvedata",
                "source_url": price_url,
                "price_source_field": "price",
                "change_percent_source_field": "quote.percent_change",
                "market_time_source_field": "quote.datetime|local_fetch_utc_fallback",
            }
        except Exception:
            continue

    return quotes, (" | ".join(source_urls[:2]) if source_urls else "")


def fetch_live_quotes(symbols):
    """Fetch live or most-recent stock quotes with provider fallback chain."""
    requested = []
    for symbol in symbols:
        normalized = normalize_ticker_symbol(symbol)
        if normalized and normalized not in requested:
            requested.append(normalized)
    if not requested:
        return {}, ""

    now_ts = time.time()
    quotes = {}
    missing = []
    with finance_cache_lock:
        for symbol in requested:
            cached = finance_quote_cache.get(symbol)
            if cached and now_ts - cached.get("cached_at", 0) <= FINANCE_QUOTE_CACHE_TTL_SECONDS:
                recovered = dict(cached.get("quote") or {})
                cached_at = float(cached.get("cached_at") or 0.0)
                recovered["from_cache"] = True
                recovered["cache_age_seconds"] = max(0.0, now_ts - cached_at) if cached_at else 0.0
                recovered["last_known_utc"] = datetime.fromtimestamp(cached_at, tz=timezone.utc).isoformat() if cached_at else ""
                quotes[symbol] = recovered
            else:
                missing.append(symbol)

    source_url = ""
    used_sources = []
    if missing:
        remaining = list(missing)

        # Provider 1: Yahoo Finance
        yahoo_blocked, yahoo_left, yahoo_reason = get_provider_cooldown_state("yahoo")
        if yahoo_blocked:
            mark_quote_provider_skipped("yahoo", f"cooldown:{yahoo_left}s:{yahoo_reason}")
        else:
            mark_quote_provider_attempt("yahoo")
            try:
                yahoo_quotes, yahoo_source = fetch_yahoo_quotes(remaining)
                if yahoo_source:
                    used_sources.append(yahoo_source)
                quotes.update(yahoo_quotes)
                if yahoo_quotes:
                    mark_quote_provider_success("yahoo")
            except Exception as e:
                mark_quote_provider_error("yahoo", e)
        remaining = [s for s in remaining if s not in quotes]

        # Provider 2: Stooq fallback
        if remaining:
            stooq_blocked, stooq_left, stooq_reason = get_provider_cooldown_state("stooq")
            if stooq_blocked:
                mark_quote_provider_skipped("stooq", f"cooldown:{stooq_left}s:{stooq_reason}")
            else:
                mark_quote_provider_attempt("stooq")
                try:
                    stooq_quotes, stooq_source = fetch_stooq_quotes(remaining)
                    if stooq_source:
                        used_sources.append(stooq_source)
                    for symbol, quote in stooq_quotes.items():
                        if symbol not in quotes:
                            quotes[symbol] = quote
                    if stooq_quotes:
                        mark_quote_provider_success("stooq")
                except Exception as e:
                    mark_quote_provider_error("stooq", e)
        remaining = [s for s in remaining if s not in quotes]

        # Provider 3: TwelveData fallback (demo key supported)
        if remaining:
            td_blocked, td_left, td_reason = get_provider_cooldown_state("twelvedata")
            if td_blocked:
                mark_quote_provider_skipped("twelvedata", f"cooldown:{td_left}s:{td_reason}")
            else:
                mark_quote_provider_attempt("twelvedata")
                try:
                    td_quotes, td_source = fetch_twelvedata_quotes(remaining)
                    if td_source:
                        used_sources.append(td_source)
                    for symbol, quote in td_quotes.items():
                        if symbol not in quotes:
                            quotes[symbol] = quote
                    if td_quotes:
                        mark_quote_provider_success("twelvedata")
                except Exception as e:
                    mark_quote_provider_error("twelvedata", e)
        remaining = [s for s in remaining if s not in quotes]

        # Provider 4: Alpha Vantage fallback (optional API key)
        if remaining:
            if not ALPHA_VANTAGE_API_KEY:
                mark_quote_provider_skipped("alpha_vantage", "disabled:no-api-key")
            else:
                av_blocked, av_left, av_reason = get_provider_cooldown_state("alpha_vantage")
                if av_blocked:
                    mark_quote_provider_skipped("alpha_vantage", f"cooldown:{av_left}s:{av_reason}")
                else:
                    mark_quote_provider_attempt("alpha_vantage")
                    try:
                        av_quotes, av_source = fetch_alpha_vantage_quotes(remaining)
                        if av_source:
                            used_sources.append(av_source)
                        for symbol, quote in av_quotes.items():
                            if symbol not in quotes:
                                quotes[symbol] = quote
                        if av_quotes:
                            mark_quote_provider_success("alpha_vantage")
                    except Exception as e:
                        mark_quote_provider_error("alpha_vantage", e)

        now_cached_at = time.time()
        with finance_cache_lock:
            for symbol, quote in quotes.items():
                if symbol in requested:
                    quote["from_cache"] = False
                    finance_quote_cache[symbol] = {
                        "cached_at": now_cached_at,
                        "quote": quote,
                    }

        if used_sources:
            source_url = " | ".join(used_sources)

    for symbol in requested:
        if symbol not in quotes:
            with finance_cache_lock:
                cached = finance_quote_cache.get(symbol)
            if cached:
                recovered = dict(cached.get("quote") or {})
                cached_at = float(cached.get("cached_at") or 0.0)
                recovered["stale"] = True
                recovered["from_cache"] = True
                recovered["cache_age_seconds"] = max(0.0, time.time() - cached_at) if cached_at else None
                recovered["last_known_utc"] = datetime.fromtimestamp(cached_at, tz=timezone.utc).isoformat() if cached_at else ""
                quotes[symbol] = recovered

    # Mark non-stale quotes when freshly fetched.
    for symbol, quote in quotes.items():
        if "stale" not in quote:
            quote["stale"] = False
        if "from_cache" not in quote:
            quote["from_cache"] = False

    return quotes, source_url


def format_quote_timestamp(market_time):
    """Convert market unix time to readable UTC text."""
    if not market_time:
        return "unknown"
    try:
        dt = datetime.fromtimestamp(int(market_time), tz=timezone.utc)
        return dt.strftime("%Y-%m-%d %H:%M UTC")
    except Exception:
        return "unknown"


def quote_as_of_label(quote):
    """Get an explicit as-of label for quote values."""
    market_label = format_quote_timestamp((quote or {}).get("market_time"))
    if market_label != "unknown":
        return market_label
    last_known = ((quote or {}).get("last_known_utc") or "").strip()
    return last_known or "unknown"


def quote_freshness_label(quote):
    """Classify quote source freshness as live, cached, or cached-stale."""
    q = quote or {}
    if bool(q.get("stale")):
        return "cached-stale"
    if bool(q.get("from_cache")):
        return "cached"
    return "live"


def validate_traceable_quote_metrics(quote):
    """Require numeric quote outputs to be tied to provider fields and a concrete source URL."""
    q = quote or {}
    price = to_float_or_none(q.get("price"))
    if price is None:
        return False, "missing-price"
    provider = (q.get("provider") or "").strip()
    if not provider:
        return False, "missing-provider"
    source_url = (q.get("source_url") or "").strip()
    if not source_url:
        return False, "missing-source-url"
    price_field = (q.get("price_source_field") or "").strip()
    if not price_field:
        return False, "missing-price-source-field"
    as_of_label = quote_as_of_label(q)
    if as_of_label == "unknown":
        return False, "missing-as-of-timestamp"
    return True, ""


def build_market_data_unavailable_message(symbols=None):
    """Return a user-facing quote fallback message for API/timeouts."""
    normalized = [normalize_ticker_symbol(s) for s in (symbols or [])]
    normalized = [s for s in normalized if s]
    if not normalized:
        return MARKET_DATA_UNAVAILABLE_RETRY_MESSAGE
    return (
        f"{MARKET_DATA_UNAVAILABLE_RETRY_MESSAGE} "
        f"Requested symbols: {', '.join(normalized)}."
    )


def is_portfolio_comparison_query(normalized_text, original_text):
    """Detect portfolio compare/analyze intents."""
    markers = ["portfolio", "portoflio", "portfolios", "compare", "comparison", "analyse", "analyze", "vs", "versus"]
    lowered = normalize_case(original_text)
    if any(m in normalized_text for m in markers):
        return True
    return ("%" in original_text and ("vs" in lowered or "versus" in lowered))


def parse_portfolio_definitions(text):
    """Parse one or more portfolio definitions from natural language."""
    raw = text or ""
    split_text = re.sub(r"\bversus\b", " vs ", raw, flags=re.IGNORECASE)
    parts = [p.strip() for p in re.split(r"\bvs\b", split_text, flags=re.IGNORECASE) if p.strip()]
    if not parts:
        parts = [raw.strip()]

    portfolios = []
    for idx, part in enumerate(parts, start=1):
        name_match = re.search(r"(portfolio\s*[a-z0-9]*)\s*[:\-]", part, flags=re.IGNORECASE)
        name = (name_match.group(1).strip().title() if name_match else f"Portfolio {chr(64 + idx)}")

        holdings = {}
        for match in re.finditer(r"(\d+(?:\.\d+)?)\s*%\s*([A-Za-z][A-Za-z0-9.\-]{0,10})", part):
            weight = float(match.group(1))
            ticker = normalize_ticker_symbol(match.group(2))
            if ticker and weight > 0:
                holdings[ticker] = holdings.get(ticker, 0.0) + weight

        for match in re.finditer(r"([A-Za-z][A-Za-z0-9.\-]{0,10})\s*[:=]\s*(\d+(?:\.\d+)?)\s*%", part):
            ticker = normalize_ticker_symbol(match.group(1))
            weight = float(match.group(2))
            if ticker and weight > 0:
                holdings[ticker] = holdings.get(ticker, 0.0) + weight

        if not holdings:
            tickers = extract_ticker_candidates(part)
            if tickers:
                equal_weight = 100.0 / len(tickers)
                for ticker in tickers:
                    holdings[ticker] = equal_weight

        total = sum(holdings.values())
        if total <= 0:
            continue
        normalized_holdings = {ticker: weight / total for ticker, weight in holdings.items()}
        portfolios.append({"name": name, "holdings": normalized_holdings})
    return portfolios


def extract_investment_amount_usd(text, default_amount=10000.0):
    """Extract optional investment amount from prompt text."""
    raw = text or ""
    dollar_match = re.search(r"\$\s*([0-9][0-9,]*(?:\.[0-9]+)?)", raw)
    if dollar_match:
        try:
            value = float(dollar_match.group(1).replace(",", ""))
            if value > 0:
                return value
        except Exception:
            pass

    usd_match = re.search(r"([0-9][0-9,]*(?:\.[0-9]+)?)\s*(?:usd|dollars?)\b", normalize_case(raw))
    if usd_match:
        try:
            value = float(usd_match.group(1).replace(",", ""))
            if value > 0:
                return value
        except Exception:
            pass

    return default_amount


def summarize_portfolio(portfolio, quotes, investment_amount):
    """Compute portfolio-level metrics from live quote data."""
    name = portfolio.get("name") or "Portfolio"
    holdings = portfolio.get("holdings") or {}
    rows = []
    weighted_change = 0.0
    weighted_price = 0.0
    hhi = 0.0
    weighted_beta = 0.0
    beta_weight_sum = 0.0
    missing = []
    freshness_states = []

    for ticker, weight in holdings.items():
        quote = quotes.get(ticker) or {}
        is_traceable, _reason = validate_traceable_quote_metrics(quote)
        if not is_traceable:
            missing.append(ticker)
            continue

        price = quote.get("price")
        change_pct = quote.get("change_percent")
        if price is None:
            missing.append(ticker)
            continue
        weight_pct = weight * 100.0
        weighted_price += weight * float(price)
        if isinstance(change_pct, (int, float)):
            weighted_change += weight * float(change_pct)
        hhi += weight * weight
        beta = quote.get("beta")
        if isinstance(beta, (int, float)):
            weighted_beta += weight * float(beta)
            beta_weight_sum += weight
        allocation_value = investment_amount * weight
        shares = allocation_value / float(price) if float(price) > 0 else 0.0
        rows.append(
            {
                "ticker": ticker,
                "weight_pct": weight_pct,
                "price": float(price),
                "change_pct": float(change_pct) if isinstance(change_pct, (int, float)) else None,
                "allocation_value": allocation_value,
                "shares": shares,
                "as_of_label": quote_as_of_label(quote),
                "data_freshness": quote_freshness_label(quote),
            }
        )
        freshness_states.append(quote_freshness_label(quote))

    if hhi < 0.18:
        diversification = "diversified"
    elif hhi < 0.30:
        diversification = "moderately concentrated"
    else:
        diversification = "highly concentrated"

    effective_beta = weighted_beta / beta_weight_sum if beta_weight_sum > 0 else None
    if effective_beta is None:
        risk_band = "risk data limited"
    elif effective_beta < 0.8:
        risk_band = "defensive"
    elif effective_beta < 1.2:
        risk_band = "balanced"
    elif effective_beta < 1.6:
        risk_band = "growth-tilted"
    else:
        risk_band = "high-volatility"

    if not freshness_states:
        portfolio_data_freshness = "unknown"
    elif all(state == freshness_states[0] for state in freshness_states):
        portfolio_data_freshness = freshness_states[0]
    else:
        portfolio_data_freshness = "mixed"

    return {
        "name": name,
        "rows": rows,
        "weighted_change_pct": weighted_change,
        "weighted_price": weighted_price,
        "diversification": diversification,
        "effective_beta": effective_beta,
        "risk_band": risk_band,
        "data_freshness": portfolio_data_freshness,
        "missing": missing,
        "hhi": hhi,
    }


def get_portfolio_comparison_reply(normalized_text, original_text, include_sources=False, user_id=DEFAULT_USER_ID):
    """Compare portfolio setups using live market prices and latest daily changes."""
    portfolios = parse_portfolio_definitions(original_text)
    if not portfolios:
        return ""

    symbols = sorted({ticker for p in portfolios for ticker in (p.get("holdings") or {}).keys()})
    if not symbols:
        return ""

    try:
        quotes, source_url = fetch_live_quotes(symbols)
    except Exception:
        return build_market_data_unavailable_message(symbols)

    if not quotes:
        return build_market_data_unavailable_message(symbols)

    for symbol in symbols:
        quote = quotes.get(symbol) or {}
        is_traceable, reason = validate_traceable_quote_metrics(quote)
        if not is_traceable and quote.get("price") is not None:
            log_metric_validation_block(
                "portfolio-comparison",
                f"untraceable-quote:{reason}",
                {"symbol": symbol, "provider": quote.get("provider") or "unknown"},
                user_id=user_id,
            )
            quotes[symbol] = {}

    investment_amount = extract_investment_amount_usd(original_text)
    summaries = [summarize_portfolio(p, quotes, investment_amount) for p in portfolios]
    valid = [s for s in summaries if s["rows"]]
    if not valid:
        return build_market_data_unavailable_message(symbols)

    best_momentum = max(valid, key=lambda s: s.get("weighted_change_pct", -9999))
    freshest_time = None
    for quote in quotes.values():
        market_time = quote.get("market_time")
        if isinstance(market_time, (int, float)):
            freshest_time = max(freshest_time or 0, int(market_time))
    freshest_label = format_quote_timestamp(freshest_time)
    if freshest_label == "unknown":
        for quote in quotes.values():
            fallback_label = quote_as_of_label(quote)
            if fallback_label != "unknown":
                freshest_label = fallback_label
                break

    lines = []
    lines.append(
        "Portfolio comparison using latest market quotes. "
        f"Data refreshes about every {FINANCE_QUOTE_CACHE_TTL_SECONDS} seconds in this app."
    )
    lines.append(f"Most recent market timestamp observed: {freshest_label}.")
    lines.append(f"Assumed investment per portfolio: ${investment_amount:,.2f}.")

    for summary in valid:
        lines.append("")
        lines.append(
            f"{summary['name']}: weighted intraday change {summary['weighted_change_pct']:+.2f}% | "
            f"weighted price ${summary['weighted_price']:.2f} | {summary['diversification']} | "
            f"risk {summary['risk_band']} | as of {freshest_label} | data {summary['data_freshness']}"
        )
        if summary.get("effective_beta") is not None:
            lines.append(f"- beta proxy: {summary['effective_beta']:.2f}")
        for row in sorted(summary["rows"], key=lambda r: r["weight_pct"], reverse=True):
            change_text = f"{row['change_pct']:+.2f}%" if row["change_pct"] is not None else "n/a"
            lines.append(
                f"- {row['ticker']}: {row['weight_pct']:.1f}% | ${row['price']:.2f} | change {change_text} | "
                f"alloc ${row['allocation_value']:.2f} | as of {row['as_of_label']} | data {row['data_freshness']}"
            )
        if summary["missing"]:
            lines.append(f"- Missing quotes: {', '.join(summary['missing'])}")

    lines.append("")
    lines.append(
        f"By latest intraday momentum, {best_momentum['name']} is currently stronger "
        f"({best_momentum['weighted_change_pct']:+.2f}%)."
    )
    lines.append("This is informational, not financial advice.")

    sources = [source_url] if source_url else ["https://finance.yahoo.com/"]
    return with_citations("\n".join(lines), sources, include_sources)


def get_live_quote_reply(normalized_text, original_text, include_sources=False, user_id=DEFAULT_USER_ID):
    """Return live or most-recent prices for one or more firms/tickers."""
    symbols = extract_ticker_candidates(original_text)
    if not symbols:
        for name in parse_company_name_candidates(original_text):
            resolved = resolve_ticker_from_company_name(name)
            if resolved:
                symbols.append(resolved)

    deduped = []
    for symbol in symbols:
        normalized = normalize_ticker_symbol(symbol)
        if normalized and normalized not in deduped:
            deduped.append(normalized)
    symbols = deduped[:25]
    if not symbols:
        return ""

    try:
        quotes, source_url = fetch_live_quotes(symbols)
    except Exception:
        return build_market_data_unavailable_message(symbols)

    if not quotes:
        return build_market_data_unavailable_message(symbols)

    lines = []
    lines.append(
        "Latest stock quotes (live or most recent market print). "
        f"Refresh cadence in this app is about every {FINANCE_QUOTE_CACHE_TTL_SECONDS} seconds."
    )
    available_count = 0
    for symbol in symbols:
        quote = quotes.get(symbol) or {}
        price = quote.get("price")
        is_traceable, reason = validate_traceable_quote_metrics(quote)
        if price is not None and not is_traceable:
            log_metric_validation_block(
                "quote-reply",
                f"untraceable-quote:{reason}",
                {"symbol": symbol, "provider": quote.get("provider") or "unknown"},
                user_id=user_id,
            )
            lines.append(f"- {symbol}: data unavailable, try again.")
            continue
        if price is None:
            lines.append(f"- {symbol}: data unavailable, try again.")
            continue
        available_count += 1
        name = quote.get("name") or symbol
        currency = quote.get("currency") or "USD"
        exchange = quote.get("exchange") or ""
        change_pct = quote.get("change_percent")
        change_text = f"{change_pct:+.2f}%" if isinstance(change_pct, (int, float)) else "n/a"
        as_of_label = quote_as_of_label(quote)
        freshness = quote_freshness_label(quote)
        exchange_part = f" on {exchange}" if exchange else ""
        provider = (quote.get("provider") or "unknown").replace("_", " ")
        stale = bool(quote.get("stale"))
        if stale:
            last_known = quote.get("last_known_utc") or "unknown"
            age = quote.get("cache_age_seconds")
            age_text = f"{int(age)}s" if isinstance(age, (int, float)) else "unknown"
            lines.append(
                f"- {symbol} ({name}): last known {price:.2f} {currency}{exchange_part} | change {change_text} | "
                f"as of {as_of_label} | data {freshness} | cached at {last_known} ({age_text} ago) | provider {provider}"
            )
        else:
            lines.append(
                f"- {symbol} ({name}): {price:.2f} {currency}{exchange_part} | change {change_text} | as of {as_of_label} | data {freshness} | provider {provider}"
            )

    if available_count == 0:
        return build_market_data_unavailable_message(symbols)

    lines.append("If you want, I can keep tracking a watchlist and compare updates minute by minute.")
    sources = [source_url] if source_url else ["https://finance.yahoo.com/"]
    return with_citations("\n".join(lines), sources, include_sources)


def get_finance_reply(normalized_text, original_text, include_sources=False, user_id=DEFAULT_USER_ID):
    """Handle finance/economics queries around quotes and portfolio comparison."""
    if "portfolio" not in normalized_text and any(m in normalized_text for m in ["compare", "comparison", "vs", "versus"]):
        comparison_reply = get_firm_comparison_reply(normalized_text, original_text, include_sources=include_sources, user_id=user_id)
        if comparison_reply:
            return comparison_reply

    if is_portfolio_comparison_query(normalized_text, original_text):
        portfolio_reply = get_portfolio_comparison_reply(
            normalized_text,
            original_text,
            include_sources=include_sources,
            user_id=user_id,
        )
        if portfolio_reply:
            return portfolio_reply

    finance_markers = [
        "portfolio", "portoflio", "stock", "stocks", "share", "shares", "share price", "price per share",
        "quote", "ticker", "market value", "market cap", "equity", "etf",
        "action", "actions", "accion", "acciones", "cotizacion", "precio",
    ]
    symbol_candidates = extract_ticker_candidates(original_text)
    if any(marker in normalized_text for marker in finance_markers) or bool(symbol_candidates):
        quote_reply = get_live_quote_reply(
            normalized_text,
            original_text,
            include_sources=include_sources,
            user_id=user_id,
        )
        if quote_reply:
            return quote_reply

    return ""


def ensure_finance_profiles(user_state):
    """Ensure finance and subscription structures exist in user state."""
    defaults = default_user_state()
    finance_profile = user_state.get("finance_profile")
    if not isinstance(finance_profile, dict):
        finance_profile = json.loads(json.dumps(defaults["finance_profile"]))
    finance_profile.setdefault("watchlist", [])
    finance_profile.setdefault("watchlist_last_checked", "")
    finance_profile.setdefault("watchlist_last_snapshot", [])
    finance_profile.setdefault(
        "cash_management",
        {
            "checking_balance_usd": 0.0,
            "hysa_balance_usd": 0.0,
            "hysa_apy": 0.045,
            "last_idle_cash_sweep_at": "",
            "last_idle_cash_sweep_amount": 0.0,
        },
    )
    finance_profile.setdefault(
        "runway_buffer_profile",
        {
            "base_city": BASELINE_COST_INDEX_CITY,
            "current_city": "",
            "capital_usd": 0.0,
            "base_monthly_cap_usd": 0.0,
            "shadow_runway_enabled": False,
            "safety_buffer_months": 0.0,
            "updated_at": "",
        },
    )

    # Normalize watchlist symbols.
    normalized_watchlist = []
    for symbol in finance_profile.get("watchlist") or []:
        normalized = normalize_ticker_symbol(symbol)
        if normalized and normalized not in normalized_watchlist:
            normalized_watchlist.append(normalized)
    finance_profile["watchlist"] = normalized_watchlist[:60]
    cash_profile = finance_profile.get("cash_management") or {}
    finance_profile["cash_management"] = {
        "checking_balance_usd": max(0.0, float(to_float_or_none(cash_profile.get("checking_balance_usd")) or 0.0)),
        "hysa_balance_usd": max(0.0, float(to_float_or_none(cash_profile.get("hysa_balance_usd")) or 0.0)),
        "hysa_apy": max(0.0, min(1.0, float(to_float_or_none(cash_profile.get("hysa_apy")) or 0.045))),
        "last_idle_cash_sweep_at": str(cash_profile.get("last_idle_cash_sweep_at") or ""),
        "last_idle_cash_sweep_amount": max(0.0, float(to_float_or_none(cash_profile.get("last_idle_cash_sweep_amount")) or 0.0)),
        "hysa_auto_sweep_enabled": bool(cash_profile.get("hysa_auto_sweep_enabled", False)),
        "hysa_auto_sweep_enabled_at": str(cash_profile.get("hysa_auto_sweep_enabled_at") or ""),
    }
    runway_profile = finance_profile.get("runway_buffer_profile") or {}
    finance_profile["runway_buffer_profile"] = {
        "base_city": normalize_city_key(runway_profile.get("base_city") or BASELINE_COST_INDEX_CITY) or BASELINE_COST_INDEX_CITY,
        "current_city": normalize_city_key(runway_profile.get("current_city") or ""),
        "capital_usd": max(0.0, float(to_float_or_none(runway_profile.get("capital_usd")) or 0.0)),
        "base_monthly_cap_usd": max(0.0, float(to_float_or_none(runway_profile.get("base_monthly_cap_usd")) or 0.0)),
        "shadow_runway_enabled": bool(runway_profile.get("shadow_runway_enabled", False)),
        "safety_buffer_months": max(0.0, float(to_float_or_none(runway_profile.get("safety_buffer_months")) or 0.0)),
        "updated_at": runway_profile.get("updated_at") or "",
    }

    subscription_profile = user_state.get("subscription_profile")
    if not isinstance(subscription_profile, dict):
        subscription_profile = json.loads(json.dumps(defaults["subscription_profile"]))
    subscription_profile.setdefault("items", [])
    subscription_profile.setdefault("savings_goal", {"name": "", "amount": 0.0})
    subscription_profile.setdefault("last_alert_at", "")
    subscription_profile.setdefault("last_vampire_scan_at", "")
    subscription_profile.setdefault("vampire_alerts", [])
    subscription_profile.setdefault("pending_cancellation_review", {})

    goal = subscription_profile.get("savings_goal") or {}
    goal_name = (goal.get("name") or "").strip()
    try:
        goal_amount = float(goal.get("amount") or 0.0)
    except Exception:
        goal_amount = 0.0
    subscription_profile["savings_goal"] = {
        "name": goal_name,
        "amount": max(0.0, goal_amount),
    }

    cleaned_items = []
    for item in subscription_profile.get("items") or []:
        if not isinstance(item, dict):
            continue
        name = (item.get("name") or "").strip()
        if not name:
            continue
        try:
            monthly_cost = float(item.get("monthly_cost") or 0.0)
        except Exception:
            monthly_cost = 0.0
        try:
            days_since_last_use = int(float(item.get("days_since_last_use") or 0))
        except Exception:
            days_since_last_use = 0
        cleaned_items.append({
            "name": name,
            "monthly_cost": max(0.0, monthly_cost),
            "days_since_last_use": max(0, days_since_last_use),
            "updated_at": item.get("updated_at") or utc_now_iso(),
        })
    subscription_profile["items"] = cleaned_items[:120]
    cleaned_alerts = []
    for item in subscription_profile.get("vampire_alerts") or []:
        if not isinstance(item, dict):
            continue
        service_name = (item.get("service_name") or "").strip()
        if not service_name:
            continue
        cleaned_alerts.append({
            "service_name": service_name,
            "monthly_cost": max(0.0, float(to_float_or_none(item.get("monthly_cost")) or 0.0)),
            "amount_match_count": max(0, int(float(to_float_or_none(item.get("amount_match_count")) or 0))),
            "last_detected_at": item.get("last_detected_at") or "",
            "days_since_usage_mention": max(0, int(float(to_float_or_none(item.get("days_since_usage_mention")) or 0))),
            "status": (item.get("status") or "open").strip().lower() or "open",
            "message": (item.get("message") or "").strip(),
        })
    subscription_profile["vampire_alerts"] = cleaned_alerts[:50]
    pending_review = subscription_profile.get("pending_cancellation_review") or {}
    if not isinstance(pending_review, dict):
        pending_review = {}
    subscription_profile["pending_cancellation_review"] = {
        "service_name": str(pending_review.get("service_name") or ""),
        "review_token": str(pending_review.get("review_token") or ""),
        "expires_at": str(pending_review.get("expires_at") or ""),
        "created_at": str(pending_review.get("created_at") or ""),
        "draft": pending_review.get("draft") if isinstance(pending_review.get("draft"), dict) else {},
    }

    behavior_profile = user_state.get("behavior_budget_profile")
    if not isinstance(behavior_profile, dict):
        behavior_profile = json.loads(json.dumps(defaults["behavior_budget_profile"]))
    behavior_profile.setdefault("spend_events", [])
    behavior_profile.setdefault("last_coach_alert_at", "")
    behavior_profile.setdefault("last_daily_alert_date", "")
    behavior_profile.setdefault("locked_categories", [])
    behavior_profile.setdefault("break_lock_confirm_category", "")
    behavior_profile.setdefault("break_lock_confirm_until", "")
    behavior_profile.setdefault("break_lock_confirm_step", 0)
    behavior_profile.setdefault("opportunity_cost_threshold_usd", OPPORTUNITY_COST_THRESHOLD_USD)
    behavior_profile.setdefault("opportunity_cost_default_years", OPPORTUNITY_COST_DEFAULT_YEARS)
    behavior_profile.setdefault("opportunity_cost_default_annual_return", OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN)
    behavior_profile.setdefault("last_opportunity_cost_gate", {})
    behavior_profile.setdefault("circuit_breaker_active", False)
    behavior_profile.setdefault("circuit_breaker_until", "")
    behavior_profile.setdefault("last_purchase_psychology", {})
    behavior_profile.setdefault("last_dopamine_swap_offer", {})
    if not isinstance(behavior_profile.get("auto_sweep_enabled"), bool):
        behavior_profile["auto_sweep_enabled"] = True
    auto_sweep_target = (behavior_profile.get("auto_sweep_target") or "").strip()
    behavior_profile["auto_sweep_target"] = auto_sweep_target or "investment index"
    try:
        behavior_profile["opportunity_cost_threshold_usd"] = max(0.0, float(behavior_profile.get("opportunity_cost_threshold_usd") or OPPORTUNITY_COST_THRESHOLD_USD))
    except Exception:
        behavior_profile["opportunity_cost_threshold_usd"] = OPPORTUNITY_COST_THRESHOLD_USD
    try:
        behavior_profile["opportunity_cost_default_years"] = max(1, min(50, int(float(behavior_profile.get("opportunity_cost_default_years") or OPPORTUNITY_COST_DEFAULT_YEARS))))
    except Exception:
        behavior_profile["opportunity_cost_default_years"] = OPPORTUNITY_COST_DEFAULT_YEARS
    try:
        behavior_profile["opportunity_cost_default_annual_return"] = max(0.0, min(1.0, float(behavior_profile.get("opportunity_cost_default_annual_return") or OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN)))
    except Exception:
        behavior_profile["opportunity_cost_default_annual_return"] = OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN
    if not isinstance(behavior_profile.get("last_opportunity_cost_gate"), dict):
        behavior_profile["last_opportunity_cost_gate"] = {}
    if not isinstance(behavior_profile.get("locked_categories"), list):
        behavior_profile["locked_categories"] = []
    cleaned_locked_categories = []
    for category in behavior_profile.get("locked_categories") or []:
        normalized_category = normalize_intent_text(category or "").strip()
        if normalized_category and normalized_category not in cleaned_locked_categories:
            cleaned_locked_categories.append(normalized_category)
    behavior_profile["locked_categories"] = cleaned_locked_categories[:20]
    if not isinstance(behavior_profile.get("break_lock_confirm_category"), str):
        behavior_profile["break_lock_confirm_category"] = ""
    behavior_profile["break_lock_confirm_category"] = normalize_intent_text(
        behavior_profile.get("break_lock_confirm_category") or ""
    ).strip()
    if not isinstance(behavior_profile.get("break_lock_confirm_until"), str):
        behavior_profile["break_lock_confirm_until"] = ""
    try:
        behavior_profile["break_lock_confirm_step"] = int(behavior_profile.get("break_lock_confirm_step") or 0)
    except Exception:
        behavior_profile["break_lock_confirm_step"] = 0
    behavior_profile["break_lock_confirm_step"] = max(0, min(3, behavior_profile["break_lock_confirm_step"]))
    if not isinstance(behavior_profile.get("circuit_breaker_active"), bool):
        behavior_profile["circuit_breaker_active"] = False
    if not isinstance(behavior_profile.get("circuit_breaker_until"), str):
        behavior_profile["circuit_breaker_until"] = ""
    if not isinstance(behavior_profile.get("last_purchase_psychology"), dict):
        behavior_profile["last_purchase_psychology"] = {}
    if not isinstance(behavior_profile.get("last_dopamine_swap_offer"), dict):
        behavior_profile["last_dopamine_swap_offer"] = {}

    cleaned_events = []
    for item in behavior_profile.get("spend_events") or []:
        if not isinstance(item, dict):
            continue
        category = (item.get("category") or "other").strip().lower() or "other"
        try:
            amount = float(item.get("amount") or 0.0)
        except Exception:
            amount = 0.0
        day_of_week = (item.get("day_of_week") or "").strip() or datetime.now().strftime("%A")
        try:
            hour = int(item.get("hour") if item.get("hour") is not None else datetime.now().hour)
        except Exception:
            hour = datetime.now().hour
        stress_level = (item.get("stress_level") or "medium").strip().lower()
        if stress_level not in {"low", "medium", "high"}:
            stress_level = "medium"
        cleaned_events.append({
            "amount": max(0.0, amount),
            "category": category,
            "day_of_week": day_of_week,
            "hour": max(0, min(23, hour)),
            "stress_level": stress_level,
            "timestamp": item.get("timestamp") or utc_now_iso(),
        })
    behavior_profile["spend_events"] = cleaned_events[-500:]

    geo_profile = user_state.get("geopolitical_profile")
    if not isinstance(geo_profile, dict):
        geo_profile = json.loads(json.dumps(defaults["geopolitical_profile"]))
    geo_profile.setdefault("suppliers", [])
    geo_profile.setdefault("last_scan_at", "")
    geo_profile.setdefault("last_scan_summary", "")

    cleaned_suppliers = []
    for item in geo_profile.get("suppliers") or []:
        if not isinstance(item, dict):
            continue
        name = (item.get("name") or "").strip()
        if not name:
            continue
        country = (item.get("country") or "Unknown").strip()
        material = (item.get("material") or "other").strip().lower()
        try:
            quality = float(item.get("quality_score") or item.get("quality") or 75.0)
        except Exception:
            quality = 75.0
        try:
            spend_share = float(item.get("spend_share") or 0.0)
        except Exception:
            spend_share = 0.0
        cleaned_suppliers.append({
            "name": name,
            "country": country,
            "material": material,
            "quality_score": max(0.0, min(100.0, quality)),
            "spend_share": max(0.0, spend_share),
            "updated_at": item.get("updated_at") or utc_now_iso(),
        })
    geo_profile["suppliers"] = cleaned_suppliers[:200]

    user_state["finance_profile"] = finance_profile
    user_state["subscription_profile"] = subscription_profile
    user_state["behavior_budget_profile"] = behavior_profile
    user_state["geopolitical_profile"] = geo_profile
    return user_state


def parse_supplier_add_payload(text):
    """Parse supplier add command into structured supplier profile."""
    raw = (text or "").strip()
    normalized = normalize_case(raw)
    if "supplier add" not in normalized and "add supplier" not in normalized:
        return None

    tokens = [t for t in re.split(r"\s+", raw) if t]
    if len(tokens) < 4:
        return None

    lower_tokens = [normalize_case(t) for t in tokens]
    marker_indexes = [i for i, t in enumerate(lower_tokens) if t in {"country", "material", "quality", "spend", "share"}]
    start_idx = 0
    for i in range(len(lower_tokens) - 1):
        if (lower_tokens[i], lower_tokens[i + 1]) in {("supplier", "add"), ("add", "supplier")}:
            start_idx = i + 2
            break

    first_marker = min(marker_indexes) if marker_indexes else len(tokens)
    name_tokens = tokens[start_idx:first_marker]
    if not name_tokens:
        return None
    name = " ".join(name_tokens).strip(" ,.-")
    if not name:
        return None

    country_match = re.search(r"country\s+([a-zA-Z\s]+?)(?:\s+material\b|\s+quality\b|\s+spend\b|$)", raw, flags=re.IGNORECASE)
    material_match = re.search(r"material\s+([a-zA-Z\-]+)", raw, flags=re.IGNORECASE)
    quality_match = re.search(r"quality\s+([0-9]+(?:\.[0-9]+)?)", raw, flags=re.IGNORECASE)
    spend_match = re.search(r"(?:spend|share)\s+([0-9]+(?:\.[0-9]+)?)\s*%?", raw, flags=re.IGNORECASE)

    country = (country_match.group(1).strip() if country_match else "Unknown")
    material = (material_match.group(1).strip().lower() if material_match else "other")
    quality = float(quality_match.group(1)) if quality_match else 75.0
    spend_share = float(spend_match.group(1)) if spend_match else 0.0

    return {
        "name": name,
        "country": country,
        "material": material,
        "quality_score": max(0.0, min(100.0, quality)),
        "spend_share": max(0.0, spend_share),
        "updated_at": utc_now_iso(),
    }


def analytics_sql_upsert_supplier(user_id, supplier):
    """Persist supplier profile in analytical SQL store."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO supplier_profiles (user_id, name, country, material, quality_score, spend_share, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(user_id, name) DO UPDATE SET
                    country=excluded.country,
                    material=excluded.material,
                    quality_score=excluded.quality_score,
                    spend_share=excluded.spend_share,
                    updated_at=excluded.updated_at
                """,
                (
                    user_id,
                    supplier.get("name") or "",
                    supplier.get("country") or "Unknown",
                    supplier.get("material") or "other",
                    float(supplier.get("quality_score") or 75.0),
                    float(supplier.get("spend_share") or 0.0),
                    supplier.get("updated_at") or utc_now_iso(),
                ),
            )
            conn.commit()
        finally:
            conn.close()


def analytics_sql_delete_supplier(user_id, supplier_name):
    """Delete supplier profile from analytical SQL store."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute("DELETE FROM supplier_profiles WHERE user_id = ? AND lower(name) = lower(?)", (user_id, supplier_name))
            conn.commit()
        finally:
            conn.close()


def analytics_sql_record_horizon_event(user_id, event_type, headline, source_url, impact):
    """Store horizon-scan event for historical aggregation."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO horizon_scan_events (user_id, event_type, headline, source_url, estimated_cogs_impact, created_at)
                VALUES (?, ?, ?, ?, ?, ?)
                """,
                (user_id, event_type, headline, source_url, float(impact), utc_now_iso()),
            )
            conn.commit()
        finally:
            conn.close()


def detect_event_type_from_headline(text):
    """Infer geopolitical/regulatory event type from headline text."""
    lowered = normalize_case(text)
    for event_type, words in GEOPOLITICAL_EVENT_KEYWORDS.items():
        if any(word in lowered for word in words):
            return event_type
    return "other"


def shock_factor_for_event(event_type):
    """Heuristic event shock multipliers used for COGS mapping."""
    mapping = {
        "tariff": 0.18,
        "shipping": 0.10,
        "tax": 0.06,
        "sanction": 0.16,
        "other": 0.04,
    }
    return mapping.get(event_type, 0.04)


def fetch_geopolitical_news_snippets(materials):
    """Fetch headlines from Google News RSS for geopolitical/regulatory scanning."""
    snippets = []
    sources = []
    seeds = materials[:3] if materials else ["steel", "shipping", "corporate tax"]
    for material in seeds:
        query = f"{material} tariff tax law congress shipping delay"
        url = f"https://news.google.com/rss/search?q={quote_plus(query)}&hl=en-US&gl=US&ceid=US:en"
        try:
            xml_text = fetch_text_url(url)
            root = ET.fromstring(xml_text)
            items = root.findall("./channel/item")[:4]
            for item in items:
                title = (item.findtext("title") or "").strip()
                link = (item.findtext("link") or url).strip()
                if title:
                    snippets.append({"title": title, "link": link, "material": material})
                    if link and link not in sources:
                        sources.append(link)
        except Exception:
            continue
    return snippets[:12], sources[:12]


def recommend_alternative_suppliers(material, min_quality=75.0, top_k=3):
    """Recommend domestic alternatives matching material and quality threshold."""
    candidates = [
        row for row in DOMESTIC_SUPPLIER_CATALOG
        if row.get("material") == material and float(row.get("quality") or 0) >= min_quality
    ]
    if not candidates:
        candidates = [row for row in DOMESTIC_SUPPLIER_CATALOG if row.get("material") == material]
    candidates = sorted(candidates, key=lambda x: (-(float(x.get("quality") or 0)), float(x.get("cost_index") or 99)))
    return candidates[:top_k]


def build_geopolitical_horizon_report(user_id, user_state, include_sources=False):
    """Map live geopolitical/regulatory headlines to supplier exposure and COGS impact."""
    user_state = ensure_finance_profiles(user_state)
    geo_profile = user_state.get("geopolitical_profile") or {}
    suppliers = geo_profile.get("suppliers") or []
    if not suppliers:
        return "No supplier exposure data found. Add suppliers like: supplier add FerroSteel country China material steel quality 90 spend 32.", []

    materials = sorted({(s.get("material") or "other").lower() for s in suppliers})
    snippets, scan_sources = fetch_geopolitical_news_snippets(materials)

    impacted_rows = []
    total_impact = 0.0
    for snippet in snippets:
        headline = snippet.get("title") or ""
        event_type = detect_event_type_from_headline(headline)
        material = (snippet.get("material") or "other").lower()
        base_shock = shock_factor_for_event(event_type)
        for supplier in suppliers:
            s_material = (supplier.get("material") or "other").lower()
            if material != s_material:
                continue
            country = (supplier.get("country") or "Unknown").strip()
            spend_share = float(supplier.get("spend_share") or 0.0) / 100.0
            imported_multiplier = 1.0 if normalize_case(country) != normalize_case(HOME_COUNTRY) else 0.45
            cogs_impact = spend_share * base_shock * imported_multiplier
            if cogs_impact <= 0:
                continue
            impacted_rows.append({
                "supplier": supplier.get("name") or "Supplier",
                "country": country,
                "material": s_material,
                "event_type": event_type,
                "headline": headline,
                "impact_pct": cogs_impact * 100.0,
                "source": snippet.get("link") or "",
                "quality_score": float(supplier.get("quality_score") or 75.0),
            })
            total_impact += cogs_impact

    impacted_rows = sorted(impacted_rows, key=lambda x: x["impact_pct"], reverse=True)
    headline = "Geopolitical and Regulatory Horizon Scan"
    if not impacted_rows:
        text = (
            f"{headline}: no high-confidence COGS shock was detected from current headlines, "
            "but I recommend monitoring tariffs, logistics delays, and tax law updates weekly."
        )
        return with_citations(text, scan_sources or ["https://news.google.com/"], include_sources), scan_sources

    top = impacted_rows[0]
    total_impact_pct = total_impact * 100.0
    lines = [
        f"{headline}: detected elevated exposure from current policy/news signals.",
        f"Top trigger: {top['headline']}",
        (
            f"Estimated COGS impact next quarter: {total_impact_pct:.2f}% based on your supplier mix "
            f"(largest single path: {top['supplier']} {top['impact_pct']:.2f}%)."
        ),
    ]

    affected_material = top.get("material") or "steel"
    min_quality = max(70.0, top.get("quality_score", 75.0) - 5.0)
    alternatives = recommend_alternative_suppliers(affected_material, min_quality=min_quality, top_k=3)
    if alternatives:
        lines.append("Recommended domestic alternatives matching your quality target:")
        for idx, alt in enumerate(alternatives, start=1):
            lines.append(
                f"{idx}. {alt['name']} ({alt['country']}) | material {alt['material']} | quality {float(alt['quality']):.0f} | cost index {float(alt['cost_index']):.2f}"
            )

    lines.append("Suggested actions: hedge contract terms, rebalance supplier share, and secure 2 backup contracts this quarter.")
    text = "\n".join(lines)

    for row in impacted_rows[:4]:
        analytics_sql_record_horizon_event(
            user_id=user_id,
            event_type=row.get("event_type") or "other",
            headline=row.get("headline") or "",
            source_url=row.get("source") or "https://news.google.com/",
            impact=row.get("impact_pct") or 0.0,
        )

    geo_profile["last_scan_at"] = utc_now_iso()
    geo_profile["last_scan_summary"] = text[:4000]
    user_state["geopolitical_profile"] = geo_profile
    return with_citations(text, scan_sources or ["https://news.google.com/"], include_sources), scan_sources


def parse_symbol_or_company_list(text):
    """Resolve symbols from either raw tickers or common company names."""
    symbols = extract_ticker_candidates(text)
    if not symbols:
        for name in parse_company_name_candidates(text):
            resolved = resolve_ticker_from_company_name(name)
            if resolved:
                symbols.append(resolved)
    deduped = []
    for symbol in symbols:
        normalized = normalize_ticker_symbol(symbol)
        if normalized and normalized not in deduped:
            deduped.append(normalized)
    return deduped


def get_watchlist_summary_reply(user_state, include_sources=False):
    """Return watchlist summary with latest quotes and movement snapshot."""
    user_state = ensure_finance_profiles(user_state)
    finance_profile = user_state.get("finance_profile") or {}
    watchlist = finance_profile.get("watchlist") or []
    if not watchlist:
        return "Your watchlist is empty. Add symbols like: watchlist add AAPL,MSFT,NVDA."

    try:
        quotes, source_url = fetch_live_quotes(watchlist)
    except Exception:
        return build_market_data_unavailable_message(watchlist)

    if not quotes:
        return build_market_data_unavailable_message(watchlist)

    lines = [
        "Watchlist snapshot (latest market values):",
        f"Refresh cadence is about every {FINANCE_QUOTE_CACHE_TTL_SECONDS} seconds.",
    ]
    snapshot_rows = []
    for symbol in watchlist:
        quote = quotes.get(symbol) or {}
        price = quote.get("price")
        if price is None:
            lines.append(f"- {symbol}: data unavailable, try again.")
            continue
        change_pct = quote.get("change_percent")
        change_text = f"{change_pct:+.2f}%" if isinstance(change_pct, (int, float)) else "n/a"
        as_of_label = quote_as_of_label(quote)
        freshness = quote_freshness_label(quote)
        lines.append(f"- {symbol}: ${float(price):.2f} | change {change_text} | as of {as_of_label} | data {freshness}")
        snapshot_rows.append({
            "symbol": symbol,
            "price": float(price),
            "change_percent": float(change_pct) if isinstance(change_pct, (int, float)) else None,
            "market_time": quote.get("market_time"),
            "as_of_label": f"as of {as_of_label}",
            "data_freshness": freshness,
        })

    finance_profile["watchlist_last_checked"] = utc_now_iso()
    finance_profile["watchlist_last_snapshot"] = snapshot_rows
    user_state["finance_profile"] = finance_profile

    sources = [source_url] if source_url else ["https://finance.yahoo.com/"]
    return with_citations("\n".join(lines), sources, include_sources)


def detect_watchlist_command(normalized_text):
    """Return watchlist command category from normalized text."""
    if any(x in normalized_text for x in ["watchlist clear", "clear watchlist", "reset watchlist"]):
        return "clear"
    if any(x in normalized_text for x in ["watchlist remove", "remove from watchlist", "untrack"]):
        return "remove"
    if any(x in normalized_text for x in ["watchlist add", "add to watchlist", "track ", "follow stocks"]):
        return "add"
    if any(x in normalized_text for x in ["my watchlist", "show watchlist", "watchlist", "watchlist update", "check watchlist"]):
        return "show"
    return ""


def apply_watchlist_command(user_state, user_message, include_sources=False):
    """Apply user watchlist commands and return reply/state-changed tuple."""
    user_state = ensure_finance_profiles(user_state)
    normalized = normalize_intent_text(user_message)
    command = detect_watchlist_command(normalized)
    if not command:
        return "", False

    finance_profile = user_state.get("finance_profile") or {}
    watchlist = finance_profile.get("watchlist") or []

    if command == "clear":
        finance_profile["watchlist"] = []
        finance_profile["watchlist_last_snapshot"] = []
        finance_profile["watchlist_last_checked"] = utc_now_iso()
        user_state["finance_profile"] = finance_profile
        return "Done. Your watchlist is now empty.", True

    if command == "show":
        return get_watchlist_summary_reply(user_state, include_sources=include_sources), True

    payload_text = user_message
    for marker in ["watchlist add", "add to watchlist", "watchlist remove", "remove from watchlist", "track", "untrack"]:
        payload_text = re.sub(marker, " ", payload_text, flags=re.IGNORECASE)

    symbols = parse_symbol_or_company_list(payload_text)
    if not symbols:
        return "Please include at least one stock symbol or company name.", False

    changed = False
    if command == "add":
        for symbol in symbols:
            if symbol not in watchlist:
                watchlist.append(symbol)
                changed = True
        watchlist = watchlist[:60]
        finance_profile["watchlist"] = watchlist
        finance_profile["watchlist_last_checked"] = utc_now_iso()
        user_state["finance_profile"] = finance_profile
        if changed:
            reply = f"Watchlist updated. Tracking: {', '.join(watchlist)}."
        else:
            reply = f"Those symbols were already in your watchlist: {', '.join(symbols)}."
        return reply, True

    if command == "remove":
        before = len(watchlist)
        watchlist = [symbol for symbol in watchlist if symbol not in set(symbols)]
        finance_profile["watchlist"] = watchlist
        finance_profile["watchlist_last_checked"] = utc_now_iso()
        user_state["finance_profile"] = finance_profile
        changed = len(watchlist) != before
        if changed:
            return f"Removed from watchlist. Now tracking: {', '.join(watchlist) if watchlist else 'none' }.", True
        return "None of those symbols were in your watchlist.", False

    return "", False


def parse_subscription_add_payload(text):
    """Extract subscription name/cost/days from text."""
    raw = (text or "").strip()
    cost_match = re.search(r"\$?\s*([0-9]+(?:\.[0-9]+)?)", raw)
    days_match = re.search(r"(\d+)\s*(?:d|day|days)", normalize_case(raw))
    if not cost_match:
        return None

    try:
        monthly_cost = float(cost_match.group(1))
    except Exception:
        return None
    if monthly_cost <= 0:
        return None

    days_since_last_use = int(days_match.group(1)) if days_match else 0
    name = re.sub(r"\$?\s*[0-9]+(?:\.[0-9]+)?", " ", raw)
    name = re.sub(r"\b(?:unused|days|day|d|monthly|per month|month|cost|price|add subscription|subscription add|add)\b", " ", name, flags=re.IGNORECASE)
    name = re.sub(r"\s+", " ", name).strip(" ,.-")
    if not name:
        return None

    return {
        "name": name,
        "monthly_cost": monthly_cost,
        "days_since_last_use": max(0, days_since_last_use),
    }


def utility_score_from_days(days_since_last_use):
    """Map days since use into a utility score from 0 to 1."""
    days = max(0, int(days_since_last_use or 0))
    return max(0.0, min(1.0, 1.0 - (days / 45.0)))


def parse_iso_datetime(value):
    """Best-effort ISO timestamp parsing."""
    raw = (value or "").strip()
    if not raw:
        return None
    try:
        return datetime.fromisoformat(raw)
    except Exception:
        return None


def days_since_recent_usage_mention(user_state, service_name, now_dt=None):
    """Estimate days since the user last mentioned actively using a service."""
    name = normalize_case(service_name or "").strip()
    if not name:
        return 999
    now_dt = now_dt or datetime.now(timezone.utc)
    best_dt = None

    history = user_state.get("history") or []
    for item in history:
        if item.get("role") != "user":
            continue
        content = normalize_case(item.get("content") or "")
        if name not in content:
            continue
        ts = parse_iso_datetime(item.get("ts") or "")
        if ts and (best_dt is None or ts > best_dt):
            best_dt = ts

    qa_memory = user_state.get("qa_memory") or []
    for item in qa_memory:
        if not isinstance(item, dict):
            continue
        content = normalize_case(item.get("q") or "")
        if name not in content:
            continue
        ts = parse_iso_datetime(item.get("ts") or "")
        if ts and (best_dt is None or ts > best_dt):
            best_dt = ts

    if best_dt is None:
        return 999
    return max(0, (now_dt - best_dt).days)


def detect_subscription_vampires(user_state, now_dt=None):
    """Scan transaction history and subscriptions to flag recurring unused charges."""
    user_state = ensure_finance_profiles(user_state)
    now_dt = now_dt or datetime.now(timezone.utc)
    behavior_profile = user_state.get("behavior_budget_profile") or {}
    subscription_profile = user_state.get("subscription_profile") or {}
    events = behavior_profile.get("spend_events") or []
    items = subscription_profile.get("items") or []

    recurring_buckets = {}
    for event in events:
        amount = float(event.get("amount") or 0.0)
        if amount <= 0:
            continue
        ts = parse_iso_datetime(event.get("timestamp") or "")
        if not ts:
            continue
        key = round(amount, 2)
        bucket = recurring_buckets.setdefault(key, [])
        bucket.append({
            "amount": amount,
            "timestamp": ts,
            "category": (event.get("category") or "other").strip().lower(),
        })

    alerts = []
    for item in items:
        service_name = (item.get("name") or "").strip()
        monthly_cost = float(item.get("monthly_cost") or 0.0)
        if not service_name or monthly_cost <= 0:
            continue

        matching_events = []
        for amount_key, bucket in recurring_buckets.items():
            if abs(amount_key - monthly_cost) <= max(1.0, monthly_cost * 0.10):
                matching_events.extend(bucket)
        if len(matching_events) < 2:
            continue

        matching_events.sort(key=lambda x: x["timestamp"])
        span_days = (matching_events[-1]["timestamp"] - matching_events[0]["timestamp"]).days
        if span_days < 25:
            continue

        days_unused = int(item.get("days_since_last_use") or 0)
        days_since_mention = days_since_recent_usage_mention(user_state, service_name, now_dt=now_dt)
        if days_unused < 45 and days_since_mention < 60:
            continue

        message = (
            f"I detected a recurring ${monthly_cost:.2f}/month subscription to {service_name}. "
            f"Based on your usage chat logs, you have not mentioned using this once in {max(60, days_since_mention)} days. "
            "Do you want me to help you draft a cancellation email right now?"
        )
        alerts.append({
            "service_name": service_name,
            "monthly_cost": monthly_cost,
            "amount_match_count": len(matching_events),
            "last_detected_at": utc_now_iso(),
            "days_since_usage_mention": days_since_mention,
            "status": "open",
            "message": message,
        })

    subscription_profile["vampire_alerts"] = alerts[:20]
    subscription_profile["last_vampire_scan_at"] = utc_now_iso()
    user_state["subscription_profile"] = subscription_profile
    return user_state, alerts


def build_subscription_cancellation_email(service_name, monthly_cost=0.0):
    """Draft a concise cancellation email for a flagged subscription."""
    service = (service_name or "the service").strip() or "the service"
    cost_text = f" (${float(monthly_cost):.2f}/month)" if float(monthly_cost or 0.0) > 0 else ""
    subject = f"Cancellation Request for {service}{cost_text}"
    body = (
        f"Hello {service} support,\n\n"
        f"I would like to cancel my subscription to {service}{cost_text}, effective immediately, and ensure that no future renewals are processed. "
        "Please confirm the cancellation and let me know if any additional steps are required on my side.\n\n"
        "Thank you."
    )
    return {"subject": subject, "body": body}


def build_subscription_decay_report(user_state, include_sources=False):
    """Generate subscription utility-vs-cost report and phantom burn alert."""
    user_state = ensure_finance_profiles(user_state)
    subscription_profile = user_state.get("subscription_profile") or {}
    items = subscription_profile.get("items") or []
    if not items:
        return "No subscriptions tracked yet. Add one like: subscription add Netflix 15.99 45 days."

    ranked = []
    total_monthly_cost = 0.0
    total_phantom_burn = 0.0
    decayed_items = []
    for item in items:
        monthly_cost = float(item.get("monthly_cost") or 0.0)
        days_unused = int(item.get("days_since_last_use") or 0)
        utility = utility_score_from_days(days_unused)
        burn = monthly_cost * (1.0 - utility)
        total_monthly_cost += monthly_cost
        total_phantom_burn += burn
        row = {
            "name": item.get("name") or "Subscription",
            "monthly_cost": monthly_cost,
            "days_unused": days_unused,
            "utility": utility,
            "burn": burn,
        }
        ranked.append(row)
        if days_unused >= 45:
            decayed_items.append(row)

    ranked.sort(key=lambda x: x["burn"], reverse=True)
    decayed_items.sort(key=lambda x: x["monthly_cost"], reverse=True)

    goal = subscription_profile.get("savings_goal") or {}
    goal_name = (goal.get("name") or "").strip() or "your savings goal"
    goal_amount = float(goal.get("amount") or 0.0)
    pause_3m_savings = sum(item["monthly_cost"] for item in decayed_items) * 3.0
    weeks_earlier = None
    if goal_amount > 0 and pause_3m_savings > 0:
        weeks_earlier = (pause_3m_savings / goal_amount) * 12.0

    lines = [
        "Subscription Decay and Phantom Burn report:",
        f"- Total monthly subscription cost: ${total_monthly_cost:.2f}",
        f"- Estimated phantom burn this month (low utility spend): ${total_phantom_burn:.2f}",
    ]

    for row in ranked[:8]:
        utility_pct = row["utility"] * 100.0
        lines.append(
            f"- {row['name']}: ${row['monthly_cost']:.2f}/mo | unused {row['days_unused']}d | utility {utility_pct:.0f}% | burn ${row['burn']:.2f}"
        )

    if decayed_items:
        top = decayed_items[0]
        alert = (
            f"ALERT: You have paid ${top['monthly_cost']:.2f} for {top['name']} this month but have not used it in {top['days_unused']} days."
        )
        lines.append(alert)

        if pause_3m_savings > 0:
            if weeks_earlier is not None:
                lines.append(
                    f"If you pause low-usage subscriptions for 3 months, you save ${pause_3m_savings:.2f} and can hit {goal_name} about {weeks_earlier:.1f} weeks earlier."
                )
            else:
                lines.append(
                    f"If you pause low-usage subscriptions for 3 months, you save about ${pause_3m_savings:.2f}."
                )
    else:
        lines.append("No major decay detected: all tracked subscriptions show recent usage.")

    user_state, vampire_alerts = detect_subscription_vampires(user_state)
    if vampire_alerts:
        lines.append("")
        lines.append("Anti-Subscription Vampire Detector:")
        for alert in vampire_alerts[:3]:
            lines.append(f"- {alert.get('message')}")

    subscription_profile = user_state.get("subscription_profile") or {}
    subscription_profile["last_alert_at"] = utc_now_iso()
    user_state["subscription_profile"] = subscription_profile
    return with_citations("\n".join(lines), ["User-provided subscription and usage inputs"], include_sources)


def infer_stress_level(text):
    """Infer stress level from user wording."""
    lowered = normalize_case(text)
    high_markers = ["stressed", "stressful", "tough week", "exhausted", "burned out", "overwhelmed", "bad day"]
    low_markers = ["calm", "good day", "relaxed", "chill"]
    if any(m in lowered for m in high_markers):
        return "high"
    if any(m in lowered for m in low_markers):
        return "low"
    return "medium"


def extract_spend_category_hint(user_message):
    """Best-effort category hint when user expresses spend intent without logging format."""
    normalized = normalize_intent_text(user_message)
    if not normalized:
        return ""

    keyword_to_category = {
        "takeout": "takeout",
        "restaurant": "food",
        "food": "food",
        "groceries": "groceries",
        "grocery": "groceries",
        "uber": "transport",
        "lyft": "transport",
        "taxi": "transport",
        "transport": "transport",
        "bus": "transport",
        "train": "transport",
        "movie": "entertainment",
        "netflix": "entertainment",
        "spotify": "entertainment",
        "concert": "entertainment",
        "game": "entertainment",
        "gaming": "entertainment",
        "shopping": "shopping",
        "amazon": "shopping",
        "shoes": "shopping",
        "sneakers": "shopping",
        "clothes": "shopping",
        "clothing": "shopping",
        "fashion": "shopping",
        "bag": "shopping",
        "watch": "shopping",
        "laptop": "shopping",
        "phone": "shopping",
        "subscription": "subscription",
        "coffee": "coffee",
        "drinks": "drinks",
    }
    for keyword, category in keyword_to_category.items():
        if keyword in normalized:
            return category
    return ""


def parse_spend_log_payload(user_message):
    """Parse spend log command into normalized event payload."""
    text = user_message or ""
    normalized = normalize_case(text)
    if not any(k in normalized for k in ["spend", "spent", "expense", "log spend"]):
        return None

    amount_match = re.search(r"\$?\s*([0-9]+(?:\.[0-9]+)?)", text)
    if not amount_match:
        return None
    try:
        amount = float(amount_match.group(1))
    except Exception:
        return None
    if amount <= 0:
        return None

    categories = ["takeout", "food", "shopping", "transport", "entertainment", "drinks", "groceries", "coffee", "other"]
    category = "other"
    for cat in categories:
        if cat in normalized:
            category = cat
            break

    day_match = re.search(
        r"\b(monday|tuesday|wednesday|thursday|friday|saturday|sunday)\b",
        normalized,
    )
    day_of_week = day_match.group(1).capitalize() if day_match else datetime.now().strftime("%A")

    hour_match = re.search(r"\b([01]?\d|2[0-3])\s*[:h]?\s*(?:00)?\b", normalized)
    hour = int(hour_match.group(1)) if hour_match else datetime.now().hour
    stress_level = infer_stress_level(text)
    inferred_tone = infer_user_tone(text)
    friction_match = re.search(r"(?:friction|delay|checkout time)\s*(?:=|:)?\s*([0-9]{1,5})\s*(?:s|sec|secs|second|seconds)?", normalized)
    friction_seconds = int(friction_match.group(1)) if friction_match else 0

    psychology_raw = parse_purchase_psychology(text)
    try:
        psychology = json.loads(psychology_raw)
    except Exception:
        psychology = {"fatigue_score": 1, "cognitive_bias": "None", "transaction_type": "Planned"}

    return {
        "amount": amount,
        "category": category,
        "day_of_week": day_of_week,
        "hour": max(0, min(23, hour)),
        "stress_level": stress_level,
        "inferred_tone": inferred_tone,
        "fatigue_score": int(to_float_or_none(psychology.get("fatigue_score")) or 1),
        "cognitive_bias": str(psychology.get("cognitive_bias") or "None"),
        "transaction_type": str(psychology.get("transaction_type") or "Planned"),
        "friction_seconds": max(0, min(86400, friction_seconds)),
        "timestamp": utc_now_iso(),
    }


def add_spend_event(user_state, spend_event):
    """Append a spend event to behavioral profile."""
    user_state = ensure_finance_profiles(user_state)
    profile = user_state.get("behavior_budget_profile") or {}
    events = profile.get("spend_events") or []
    events.append(spend_event)
    profile["spend_events"] = events[-500:]
    profile["last_coach_alert_at"] = utc_now_iso()
    user_state["behavior_budget_profile"] = profile
    return user_state


def analyze_behavioral_spending_patterns(user_state):
    """Derive spending trigger insights from historical spend events."""
    user_state = ensure_finance_profiles(user_state)
    profile = user_state.get("behavior_budget_profile") or {}
    events = profile.get("spend_events") or []
    if len(events) < 5:
        return {
            "event_count": len(events),
            "top_trigger": "",
            "friday_late_multiplier": 1.0,
            "high_stress_multiplier": 1.0,
            "common_category": "",
            "estimated_avoidable_spend": 0.0,
        }

    total_amount = sum(float(e.get("amount") or 0.0) for e in events)
    avg_all = total_amount / len(events) if events else 0.0

    friday_late = [e for e in events if e.get("day_of_week") == "Friday" and int(e.get("hour") or 0) >= 17]
    high_stress = [e for e in events if (e.get("stress_level") or "") == "high"]
    friday_avg = sum(float(e.get("amount") or 0.0) for e in friday_late) / len(friday_late) if friday_late else avg_all
    stress_avg = sum(float(e.get("amount") or 0.0) for e in high_stress) / len(high_stress) if high_stress else avg_all

    category_totals = {}
    for e in events:
        cat = (e.get("category") or "other").strip().lower()
        category_totals[cat] = category_totals.get(cat, 0.0) + float(e.get("amount") or 0.0)
    common_category = max(category_totals, key=category_totals.get) if category_totals else "other"

    friday_mult = (friday_avg / avg_all) if avg_all > 0 else 1.0
    stress_mult = (stress_avg / avg_all) if avg_all > 0 else 1.0
    avoidable = max(0.0, friday_avg - avg_all)

    trigger_parts = []
    if friday_mult >= 1.2:
        trigger_parts.append("Friday evening")
    if stress_mult >= 1.2:
        trigger_parts.append("high-stress days")
    top_trigger = " and ".join(trigger_parts)

    return {
        "event_count": len(events),
        "top_trigger": top_trigger,
        "friday_late_multiplier": friday_mult,
        "high_stress_multiplier": stress_mult,
        "common_category": common_category,
        "estimated_avoidable_spend": avoidable,
    }


def build_behavioral_budget_summary(user_state):
    """Summarize learned behavioral spending patterns."""
    insights = analyze_behavioral_spending_patterns(user_state)
    if insights["event_count"] < 5:
        return "I need at least 5 spend logs to learn your emotional spending triggers accurately."

    lines = [
        "Behavioral budgeting insights:",
        f"- Logged events: {insights['event_count']}",
        f"- Top spend category: {insights['common_category']}",
        f"- Friday evening spend multiplier: {insights['friday_late_multiplier']:.2f}x",
        f"- High-stress spend multiplier: {insights['high_stress_multiplier']:.2f}x",
    ]
    if insights["top_trigger"]:
        lines.append(f"- Emotional trigger pattern detected: {insights['top_trigger']}")
    lines.append(f"- Estimated avoidable spend per trigger window: ${insights['estimated_avoidable_spend']:.2f}")
    return "\n".join(lines)


def build_empathetic_budget_nudge(user_state, now_dt=None):
    """Create proactive empathetic nudge based on behavior and current context."""
    user_state = ensure_finance_profiles(user_state)
    now_dt = now_dt or datetime.now()
    insights = analyze_behavioral_spending_patterns(user_state)
    if insights["event_count"] < 5:
        return ""

    day_name = now_dt.strftime("%A")
    hour = now_dt.hour
    likely_window = (day_name == "Friday" and hour >= 14) or (insights["high_stress_multiplier"] >= 1.15)
    if not likely_window:
        return ""

    suggested_save = max(10.0, min(120.0, insights["estimated_avoidable_spend"] or 25.0))
    behavior_profile = user_state.get("behavior_budget_profile") or {}
    target = behavior_profile.get("auto_sweep_target") or "investment index"
    auto_sweep_enabled = bool(behavior_profile.get("auto_sweep_enabled", True))
    category = insights.get("common_category") or "takeout"
    if auto_sweep_enabled:
        return (
            "Hey, it has been a tough week. "
            f"You usually spend more on {category} around this time. "
            f"If you skip it tonight, I will auto-sweep about ${suggested_save:.0f} into your {target}. What do you think?"
        )
    return (
        "Hey, it has been a tough week. "
        f"You usually spend more on {category} around this time. "
        f"If you skip it tonight, you can manually move about ${suggested_save:.0f} toward your {target}."
    )


def apply_behavior_budget_command(user_state, user_message):
    """Apply behavioral budgeting commands and return reply/state-changed tuple."""
    user_state = ensure_finance_profiles(user_state)
    normalized = normalize_intent_text(user_message)
    behavior_profile = user_state.get("behavior_budget_profile") or {}
    user_profile = user_state.get("profile") or {}

    if any(x in normalized for x in ["accountability target", "set accountability", "goal target"]):
        target_text = re.sub(r".*(?:accountability target|set accountability|goal target)", "", user_message, flags=re.IGNORECASE).strip(" :.-")
        if not target_text:
            return "Set it like: accountability target become debt-free by June.", False
        user_profile["accountability_target"] = target_text
        user_state["profile"] = user_profile
        return f"Accountability target set: {target_text}.", True

    if any(x in normalized for x in ["lock category", "category lock"]):
        category_text = re.sub(r".*(?:lock category|category lock)", "", user_message, flags=re.IGNORECASE).strip(" :.-")
        if not category_text:
            return "Use: lock category shopping.", False
        category = normalize_intent_text(category_text)
        locked = behavior_profile.get("locked_categories") or []
        if category not in locked:
            locked.append(category)
        behavior_profile["locked_categories"] = locked[:20]
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        return f"Locked spending category: {category}.", True

    if any(x in normalized for x in ["unlock category", "category unlock"]):
        category_text = re.sub(r".*(?:unlock category|category unlock)", "", user_message, flags=re.IGNORECASE).strip(" :.-")
        if not category_text:
            return "Use: unlock category shopping.", False
        category = normalize_intent_text(category_text)
        before = len(behavior_profile.get("locked_categories") or [])
        behavior_profile["locked_categories"] = [c for c in (behavior_profile.get("locked_categories") or []) if c != category]
        if behavior_profile.get("break_lock_confirm_category") == category:
            behavior_profile["break_lock_confirm_category"] = ""
            behavior_profile["break_lock_confirm_until"] = ""
            behavior_profile["break_lock_confirm_step"] = 0
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        if len(behavior_profile["locked_categories"]) == before:
            return "That category was not locked.", False
        return f"Unlocked spending category: {category}.", True

    if any(x in normalized for x in ["locked categories", "show locked", "list locked"]):
        locked = behavior_profile.get("locked_categories") or []
        if not locked:
            return "No locked categories set.", False
        return "Locked categories: " + ", ".join(locked), False

    if any(x in normalized for x in ["behavior summary", "spending triggers", "show triggers", "budget psychology", "behavioral budgeting"]):
        return build_behavioral_budget_summary(user_state), False

    if any(x in normalized for x in ["coach nudge", "budget nudge", "financial coach", "coach me"]):
        nudge = build_empathetic_budget_nudge(user_state)
        if nudge:
            behavior_profile["last_coach_alert_at"] = utc_now_iso()
            user_state["behavior_budget_profile"] = behavior_profile
            return nudge, True
        return "No urgent trigger window detected right now. I can still help with a low-spend alternative plan.", False

    if any(x in normalized for x in ["auto sweep on", "enable auto sweep"]):
        behavior_profile["auto_sweep_enabled"] = True
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        return "Auto-sweep is enabled for your coaching nudges.", True

    if any(x in normalized for x in ["auto sweep off", "disable auto sweep"]):
        behavior_profile["auto_sweep_enabled"] = False
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        return "Auto-sweep is disabled.", True

    if any(x in normalized for x in ["sweep target", "set target"]):
        target_text = re.sub(r".*(?:sweep target|set target)", "", user_message, flags=re.IGNORECASE).strip(" :.-")
        if not target_text:
            return "Set target like: sweep target investment index.", False
        behavior_profile["auto_sweep_target"] = target_text
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        return f"Auto-sweep target updated to: {target_text}.", True

    spend_event = parse_spend_log_payload(user_message)
    if spend_event:
        user_state = add_spend_event(user_state, spend_event)
        projection_text = ""
        if is_discretionary_expense_category(spend_event.get("category")):
            projection = build_dynamic_opportunity_cost_projection(
                spend_event.get("amount") or 0.0,
                annual_return=0.075,
            )
            projection_text = render_dynamic_opportunity_cost_projection(projection)
        return (
            f"Spend logged: ${spend_event['amount']:.2f} on {spend_event['category']} "
            f"({spend_event['day_of_week']} {spend_event['hour']:02d}:00, stress {spend_event['stress_level']})."
            + (f" {projection_text}" if projection_text else "")
        ), True

    return "", False


def apply_subscription_command(user_state, user_message, include_sources=False):
    """Apply subscription management commands and return reply/state-changed tuple."""
    user_state = ensure_finance_profiles(user_state)
    normalized = normalize_intent_text(user_message)
    subscription_profile = user_state.get("subscription_profile") or {}
    items = subscription_profile.get("items") or []

    if any(x in normalized for x in ["subscription list", "list subscriptions", "my subscriptions", "show subscriptions"]):
        if not items:
            return "You are not tracking subscriptions yet.", False
        rows = ["Tracked subscriptions:"]
        for item in items:
            rows.append(
                f"- {item['name']}: ${float(item['monthly_cost']):.2f}/mo | unused {int(item['days_since_last_use'])}d"
            )
        return "\n".join(rows), False

    if any(x in normalized for x in ["subscription clear", "clear subscriptions"]):
        subscription_profile["items"] = []
        subscription_profile["last_alert_at"] = utc_now_iso()
        user_state["subscription_profile"] = subscription_profile
        return "All tracked subscriptions cleared.", True

    if any(x in normalized for x in ["subscription add", "add subscription"]):
        payload = parse_subscription_add_payload(user_message)
        if not payload:
            return "Use format like: subscription add Netflix 15.99 45 days.", False
        existing = None
        for item in items:
            if normalize_case(item.get("name")) == normalize_case(payload["name"]):
                existing = item
                break
        if existing:
            existing["monthly_cost"] = payload["monthly_cost"]
            existing["days_since_last_use"] = payload["days_since_last_use"]
            existing["updated_at"] = utc_now_iso()
            action = "updated"
        else:
            items.append({
                "name": payload["name"],
                "monthly_cost": payload["monthly_cost"],
                "days_since_last_use": payload["days_since_last_use"],
                "updated_at": utc_now_iso(),
            })
            action = "added"
        subscription_profile["items"] = items[:120]
        subscription_profile["last_alert_at"] = utc_now_iso()
        user_state["subscription_profile"] = subscription_profile
        return (
            f"Subscription {action}: {payload['name']} at ${payload['monthly_cost']:.2f}/mo, "
            f"unused {payload['days_since_last_use']} days."
        ), True

    if any(x in normalized for x in ["subscription remove", "remove subscription"]):
        payload = re.sub(r"subscription remove|remove subscription", " ", user_message, flags=re.IGNORECASE)
        target = re.sub(r"\s+", " ", payload).strip()
        if not target:
            return "Tell me which subscription to remove.", False
        before = len(items)
        items = [item for item in items if normalize_case(item.get("name")) != normalize_case(target)]
        subscription_profile["items"] = items
        subscription_profile["last_alert_at"] = utc_now_iso()
        user_state["subscription_profile"] = subscription_profile
        if len(items) == before:
            return "I could not find that subscription in your tracked list.", False
        return f"Removed subscription: {target}.", True

    if any(x in normalized for x in ["subscription usage", "update usage", "subscription used"]):
        usage_match = re.search(r"(?:usage|used)\s+(.+?)\s+(\d+)\s*(?:d|day|days)", user_message, flags=re.IGNORECASE)
        if not usage_match:
            return "Use format like: subscription usage Netflix 45 days.", False
        target_name = usage_match.group(1).strip(" ,.-")
        days_unused = int(usage_match.group(2))
        for item in items:
            if normalize_case(item.get("name")) == normalize_case(target_name):
                item["days_since_last_use"] = max(0, days_unused)
                item["updated_at"] = utc_now_iso()
                subscription_profile["items"] = items
                subscription_profile["last_alert_at"] = utc_now_iso()
                user_state["subscription_profile"] = subscription_profile
                return f"Updated usage for {item['name']}: {days_unused} days unused.", True
        return "Subscription not found. Add it first with cost.", False

    if any(x in normalized for x in ["set goal", "savings goal", "goal amount"]):
        amount_match = re.search(r"\$?\s*([0-9]+(?:\.[0-9]+)?)", user_message)
        if not amount_match:
            return "Set a goal like: set savings goal weekend trip 900.", False
        amount = float(amount_match.group(1))
        goal_name = re.sub(r"\$?\s*[0-9]+(?:\.[0-9]+)?", " ", user_message)
        goal_name = re.sub(r"\b(set|savings|goal|amount|my|for)\b", " ", goal_name, flags=re.IGNORECASE)
        goal_name = re.sub(r"\s+", " ", goal_name).strip(" ,.-") or "your savings goal"
        subscription_profile["savings_goal"] = {"name": goal_name, "amount": max(0.0, amount)}
        subscription_profile["last_alert_at"] = utc_now_iso()
        user_state["subscription_profile"] = subscription_profile
        return f"Savings goal set: {goal_name} (${amount:.2f}).", True

    if any(x in normalized for x in ["phantom burn", "subscription decay", "burn alert", "subscription alert"]):
        return build_subscription_decay_report(user_state, include_sources=include_sources), True

    return "", False


def get_personal_finance_feature_reply(user_message, user_state, user_id=DEFAULT_USER_ID, include_sources=False):
    """Handle watchlist/subscription commands before generic model responses."""
    user_state = ensure_finance_profiles(user_state)
    normalized = normalize_intent_text(user_message)

    if (
        "investment advice" in normalized
        and any(token in normalized for token in ["allowed", "not allowed", "can", "cannot", "cant", "can't"])
    ):
        policy_text = (
            "Here is what I can and cannot do on investment advice:\n"
            "- Allowed: explain concepts, compare risk levels, walk through diversification ideas, and help you build a decision checklist based on your goals/time horizon/risk tolerance.\n"
            "- Allowed: show traceable market data when provider data is available, and clearly label assumptions in hypothetical examples.\n"
            "- Not allowed: guarantee returns, claim a sure-win trade, or present unverified numbers as facts.\n"
            "- Not allowed: pressure you into urgent all-in moves or hide uncertainty/sources.\n"
            "- Important: this is informational support, not licensed financial advice."
        )
        return with_citations(policy_text, ["https://www.investor.gov/introduction-investing"], include_sources), False

    if is_direct_investment_allocation_query(normalized):
        return build_investment_allocation_baseline_reply(include_sources=include_sources), False

    # Handle live quote/portfolio finance intents deterministically before generic model fallback.
    finance_lookup_reply = get_finance_reply(
        normalized,
        user_message,
        include_sources=include_sources,
        user_id=user_id,
    )
    if finance_lookup_reply:
        return finance_lookup_reply, False

    # Two-engine architecture:
    # 1) Linguistic engine parses natural language into structured analytical intent.
    # 2) Analytical engine executes deterministic math/state/SQL logic.
    structured_intent = linguistic_engine_parse_intent(user_message)
    if structured_intent:
        engine_result = analytical_engine_execute(
            user_id=sanitize_user_id(user_id),
            user_state=user_state,
            intent=structured_intent,
        )
        rendered = linguistic_engine_render_response(engine_result, include_sources=include_sources)
        if rendered:
            return rendered, bool(engine_result.get("state_changed"))

    watchlist_reply, watchlist_changed = apply_watchlist_command(
        user_state, user_message, include_sources=include_sources
    )
    if watchlist_reply:
        return watchlist_reply, (watchlist_changed or True)

    subscription_reply, subscription_changed = apply_subscription_command(
        user_state, user_message, include_sources=include_sources
    )
    if subscription_reply:
        return subscription_reply, (subscription_changed or True)

    behavior_reply, behavior_changed = apply_behavior_budget_command(user_state, user_message)
    if behavior_reply:
        return behavior_reply, (behavior_changed or True)

    return "", False


def maybe_generate_daily_finance_alert(user_state):
    """Generate one proactive daily alert for finance coaching on session open."""
    user_state = ensure_finance_profiles(user_state)
    behavior_profile = user_state.get("behavior_budget_profile") or {}
    today = datetime.now().strftime("%Y-%m-%d")
    last_date = (behavior_profile.get("last_daily_alert_date") or "")[:10]
    if last_date == today:
        return "", False

    parts = []
    nudge = build_empathetic_budget_nudge(user_state)
    if nudge:
        parts.append(nudge)

    sub_alert = build_subscription_decay_report(user_state)
    if sub_alert and "No subscriptions tracked" not in sub_alert:
        lines = sub_alert.splitlines()
        short = "\n".join(lines[:4])
        parts.append(short)

    user_state, vampire_alerts = detect_subscription_vampires(user_state)
    if vampire_alerts:
        parts.append(vampire_alerts[0].get("message") or "")

    if not parts:
        return "", False

    behavior_profile["last_daily_alert_date"] = today
    behavior_profile["last_coach_alert_at"] = utc_now_iso()
    user_state["behavior_budget_profile"] = behavior_profile
    return "\n\n".join(parts), True


def pdf_escape_text(value):
    """Escape text for a basic PDF content stream."""
    raw = (value or "").replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")
    return re.sub(r"[^\x20-\x7E]", "?", raw)


def build_simple_pdf_from_lines(lines, title="Weekly Finance Report"):
    """Build a small one-page PDF from plain text lines without external deps."""
    sanitized_lines = [pdf_escape_text(title), ""] + [pdf_escape_text(line) for line in lines]
    y_start = 780
    line_height = 14

    content = ["BT", "/F1 11 Tf", f"50 {y_start} Td"]
    for idx, line in enumerate(sanitized_lines[:45]):
        if idx > 0:
            content.append(f"0 -{line_height} Td")
        content.append(f"({line[:110]}) Tj")
    content.append("ET")
    stream_text = "\n".join(content)
    stream_bytes = stream_text.encode("latin-1", errors="replace")

    objects = []
    objects.append(b"1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n")
    objects.append(b"2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n")
    objects.append(
        b"3 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 595 842] /Resources << /Font << /F1 4 0 R >> >> /Contents 5 0 R >>\nendobj\n"
    )
    objects.append(b"4 0 obj\n<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>\nendobj\n")
    objects.append(
        b"5 0 obj\n<< /Length " + str(len(stream_bytes)).encode("ascii") + b" >>\nstream\n" + stream_bytes + b"\nendstream\nendobj\n"
    )

    header = b"%PDF-1.4\n"
    body = b""
    offsets = [0]
    current_offset = len(header)
    for obj in objects:
        offsets.append(current_offset)
        body += obj
        current_offset += len(obj)

    xref_start = len(header) + len(body)
    xref = [f"xref\n0 {len(objects) + 1}\n".encode("ascii")]
    xref.append(b"0000000000 65535 f \n")
    for offset in offsets[1:]:
        xref.append(f"{offset:010d} 00000 n \n".encode("ascii"))

    trailer = (
        f"trailer\n<< /Size {len(objects) + 1} /Root 1 0 R >>\n"
        f"startxref\n{xref_start}\n%%EOF\n"
    ).encode("ascii")

    return header + body + b"".join(xref) + trailer


def build_weekly_finance_report_lines(user_state, user_id=DEFAULT_USER_ID):
    """Build weekly report lines from watchlist, subscriptions, and behavior."""
    user_state = ensure_finance_profiles(user_state)
    finance_profile = user_state.get("finance_profile") or {}
    subscription_profile = user_state.get("subscription_profile") or {}

    lines = [f"Generated: {utc_now_iso()}"]
    lines.append("Data provenance: Watchlist prices are from live/cached quote providers (Yahoo/Stooq/Alpha Vantage).")
    lines.append("Assumption disclosure: Any opportunity-cost projections in this report use explicitly stated annual-return assumptions and are illustrative, not guaranteed.")

    watchlist = finance_profile.get("watchlist") or []
    lines.append("")
    lines.append("Watchlist")
    if watchlist:
        try:
            quotes, _source_url = fetch_live_quotes(watchlist)
        except Exception:
            quotes = {}
        for symbol in watchlist:
            quote = quotes.get(symbol) or {}
            price = quote.get("price")
            change = quote.get("change_percent")
            is_traceable, reason = validate_traceable_quote_metrics(quote)
            if price is not None and not is_traceable:
                log_metric_validation_block(
                    "weekly-report",
                    f"untraceable-quote:{reason}",
                    {"symbol": symbol, "provider": quote.get("provider") or "unknown"},
                    user_id=user_id,
                )
                lines.append(f"- {symbol}: data unavailable, try again.")
                continue
            if price is None:
                lines.append(f"- {symbol}: data unavailable, try again.")
                continue
            change_text = f"{change:+.2f}%" if isinstance(change, (int, float)) else "n/a"
            as_of_label = quote_as_of_label(quote)
            freshness = quote_freshness_label(quote)
            lines.append(f"- {symbol}: ${float(price):.2f} ({change_text}) | as of {as_of_label} | data {freshness}")
    else:
        lines.append("- No watchlist symbols configured.")

    lines.append("")
    lines.append("Subscriptions")
    items = subscription_profile.get("items") or []
    if items:
        total = sum(float(i.get("monthly_cost") or 0.0) for i in items)
        lines.append(f"- Monthly cost total: ${total:.2f}")
        for item in items[:12]:
            lines.append(
                f"- {item.get('name')}: ${float(item.get('monthly_cost') or 0.0):.2f}/mo | unused {int(item.get('days_since_last_use') or 0)}d"
            )
    else:
        lines.append("- No subscriptions configured.")

    lines.append("")
    lines.append("Behavioral Psychology Budgeting")
    insight_text = build_behavioral_budget_summary(user_state)
    for line in insight_text.splitlines():
        lines.append(f"- {line}" if not line.startswith("-") else line)

    nudge = build_empathetic_budget_nudge(user_state)
    if nudge:
        lines.append("")
        lines.append("Coach Nudge")
        lines.append(f"- {nudge}")

    lines.append("")
    lines.append("Financial Vibe Check")
    vibe = analytics_sql_weekly_mood_spending_report(sanitize_user_id(user_id))
    for line in (vibe.get("report") or "No weekly vibe report available yet.").splitlines():
        lines.append(f"- {line}" if not line.startswith("-") else line)

    return lines


def analytics_sql_upsert_subscription(user_id, item):
    """Persist subscription row into SQL analytical store."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO subscriptions (user_id, name, monthly_cost, days_since_last_use, updated_at)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(user_id, name) DO UPDATE SET
                    monthly_cost=excluded.monthly_cost,
                    days_since_last_use=excluded.days_since_last_use,
                    updated_at=excluded.updated_at
                """,
                (
                    user_id,
                    item.get("name") or "",
                    float(item.get("monthly_cost") or 0.0),
                    int(item.get("days_since_last_use") or 0),
                    item.get("updated_at") or utc_now_iso(),
                ),
            )
            conn.commit()
        finally:
            conn.close()


def analytics_sql_delete_subscription(user_id, name):
    """Delete a subscription row from SQL analytical store."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                "DELETE FROM subscriptions WHERE user_id = ? AND lower(name) = lower(?)",
                (user_id, name),
            )
            conn.commit()
        finally:
            conn.close()


def analytics_sql_set_goal(user_id, goal_name, goal_amount):
    """Persist savings goal in SQL analytical store."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO savings_goals (user_id, name, amount, updated_at)
                VALUES (?, ?, ?, ?)
                ON CONFLICT(user_id) DO UPDATE SET
                    name=excluded.name,
                    amount=excluded.amount,
                    updated_at=excluded.updated_at
                """,
                (user_id, goal_name, float(goal_amount), utc_now_iso()),
            )
            conn.commit()
        finally:
            conn.close()


def analytics_sql_insert_spend_event(user_id, event):
    """Insert spend event into SQL analytical store."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO spend_events (
                    user_id, amount, category, day_of_week, hour, stress_level,
                    inferred_tone, fatigue_score, cognitive_bias, transaction_type, friction_seconds, created_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    user_id,
                    float(event.get("amount") or 0.0),
                    (event.get("category") or "other").strip().lower(),
                    event.get("day_of_week") or datetime.now().strftime("%A"),
                    int(event.get("hour") or datetime.now().hour),
                    (event.get("stress_level") or "medium").strip().lower(),
                    str(event.get("inferred_tone") or "neutral"),
                    int(to_float_or_none(event.get("fatigue_score")) or 1),
                    str(event.get("cognitive_bias") or "None"),
                    str(event.get("transaction_type") or "Planned"),
                    int(to_float_or_none(event.get("friction_seconds")) or 0),
                    event.get("timestamp") or utc_now_iso(),
                ),
            )
            conn.commit()
        finally:
            conn.close()


def analytics_sql_insert_guardrail_override(user_id, category, created_at=None):
    """Log each consumed spending-guardrail override."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO guardrail_overrides (user_id, category, created_at)
                VALUES (?, ?, ?)
                """,
                (
                    sanitize_user_id(user_id),
                    normalize_intent_text(category or "other").strip() or "other",
                    created_at or utc_now_iso(),
                ),
            )
            conn.commit()
        finally:
            conn.close()


def analytics_sql_insert_cancellation_send(user_id, service_name, draft, confirmation_ts=None):
    """Log a confirmed cancellation submission with draft payload."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO cancellation_sends (
                    user_id, service_name, draft_subject, draft_body, confirmation_ts
                )
                VALUES (?, ?, ?, ?, ?)
                """,
                (
                    sanitize_user_id(user_id),
                    (service_name or "").strip() or "unknown",
                    str((draft or {}).get("subject") or ""),
                    str((draft or {}).get("body") or ""),
                    confirmation_ts or utc_now_iso(),
                ),
            )
            conn.commit()
        finally:
            conn.close()


def analytics_sql_fetch_user_activity_log(user_id, limit=100):
    """Return audit activity rows for overrides and cancellation sends."""
    ensure_analytics_db()
    safe_limit = max(1, min(200, int(to_float_or_none(limit) or 100)))
    overrides = []
    cancellations = []

    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                SELECT category, created_at
                FROM guardrail_overrides
                WHERE user_id = ?
                ORDER BY created_at DESC
                LIMIT ?
                """,
                (sanitize_user_id(user_id), safe_limit),
            )
            for row in cur.fetchall() or []:
                overrides.append(
                    {
                        "category": str((row[0] if len(row) > 0 else "") or "other"),
                        "created_at": str((row[1] if len(row) > 1 else "") or ""),
                    }
                )

            cur.execute(
                """
                SELECT service_name, draft_subject, confirmation_ts
                FROM cancellation_sends
                WHERE user_id = ?
                ORDER BY confirmation_ts DESC
                LIMIT ?
                """,
                (sanitize_user_id(user_id), safe_limit),
            )
            for row in cur.fetchall() or []:
                cancellations.append(
                    {
                        "service_name": str((row[0] if len(row) > 0 else "") or ""),
                        "draft_subject": str((row[1] if len(row) > 1 else "") or ""),
                        "confirmation_ts": str((row[2] if len(row) > 2 else "") or ""),
                    }
                )
        except Exception:
            overrides = []
            cancellations = []
        finally:
            conn.close()

    return {
        "overrides": overrides,
        "cancellations": cancellations,
    }


def analytics_sql_behavior_insights(user_id):
    """Compute behavioral spending aggregates using SQL."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute("SELECT COUNT(*), COALESCE(AVG(amount), 0) FROM spend_events WHERE user_id = ?", (user_id,))
            row = cur.fetchone() or (0, 0)
            event_count = int(row[0] or 0)
            avg_all = float(row[1] or 0.0)

            cur.execute(
                """
                SELECT COALESCE(AVG(amount), 0)
                FROM spend_events
                WHERE user_id = ? AND day_of_week = 'Friday' AND hour >= 17
                """,
                (user_id,),
            )
            friday_avg = float((cur.fetchone() or (0,))[0] or 0.0)

            cur.execute(
                "SELECT COALESCE(AVG(amount), 0) FROM spend_events WHERE user_id = ? AND stress_level = 'high'",
                (user_id,),
            )
            stress_avg = float((cur.fetchone() or (0,))[0] or 0.0)

            cur.execute(
                """
                SELECT category, COALESCE(SUM(amount), 0) AS total
                FROM spend_events
                WHERE user_id = ?
                GROUP BY category
                ORDER BY total DESC
                LIMIT 1
                """,
                (user_id,),
            )
            cat_row = cur.fetchone()
            common_category = (cat_row[0] if cat_row else "") or ""

            if avg_all <= 0:
                friday_mult = 1.0
                stress_mult = 1.0
                avoidable = 0.0
            else:
                friday_mult = (friday_avg / avg_all) if friday_avg > 0 else 1.0
                stress_mult = (stress_avg / avg_all) if stress_avg > 0 else 1.0
                avoidable = max(0.0, friday_avg - avg_all)

            trigger_parts = []
            if friday_mult >= 1.2:
                trigger_parts.append("Friday evening")
            if stress_mult >= 1.2:
                trigger_parts.append("high-stress days")

            return {
                "event_count": event_count,
                "top_trigger": " and ".join(trigger_parts),
                "friday_late_multiplier": friday_mult,
                "high_stress_multiplier": stress_mult,
                "common_category": common_category,
                "estimated_avoidable_spend": avoidable,
            }
        finally:
            conn.close()


def find_subscriptions(user_id):
    """Find likely monthly subscriptions from spend_events using SQL only."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                WITH grouped AS (
                    SELECT
                        category,
                        ROUND(amount, 2) AS amount_key,
                        COUNT(*) AS hit_count,
                        MIN(created_at) AS first_at,
                        MAX(created_at) AS last_at
                    FROM spend_events
                    WHERE user_id = ?
                      AND amount > 0
                      AND created_at >= datetime('now', '-180 day')
                    GROUP BY category, ROUND(amount, 2)
                    HAVING COUNT(*) >= 3
                ),
                recurring AS (
                    SELECT
                        category,
                        amount_key,
                        hit_count,
                        (julianday(last_at) - julianday(first_at)) AS span_days,
                        CASE
                            WHEN hit_count > 1 THEN (julianday(last_at) - julianday(first_at)) / (hit_count - 1)
                            ELSE 0
                        END AS avg_gap_days,
                        last_at
                    FROM grouped
                )
                SELECT category, amount_key, hit_count, avg_gap_days, last_at
                FROM recurring
                WHERE span_days >= 55
                  AND avg_gap_days BETWEEN 24 AND 36
                ORDER BY hit_count DESC, last_at DESC
                LIMIT 1
                """,
                (user_id,),
            )
            row = cur.fetchone()
            if not row:
                return None
            category = (row[0] or "other").strip() or "other"
            merchant = category.replace("_", " ").title()
            return {
                "merchant": merchant,
                "amount": float(row[1] or 0.0),
                "hit_count": int(row[2] or 0),
                "avg_gap_days": float(row[3] or 0.0),
            }
        finally:
            conn.close()


def maybe_get_witty_subscription_alert(user_state, user_id, now_dt=None):
    """Return a low-frequency witty subscription alert from SQL spend history."""
    user_state = ensure_finance_profiles(user_state)
    now_dt = now_dt or datetime.now(timezone.utc)
    subscription_profile = user_state.get("subscription_profile") or {}

    last_scan = parse_iso_datetime(subscription_profile.get("last_sql_subscription_scan_at") or "")
    if last_scan and (now_dt - last_scan).total_seconds() < 6 * 3600:
        return "", False

    candidate = find_subscriptions(user_id)
    subscription_profile["last_sql_subscription_scan_at"] = utc_now_iso()
    if not candidate:
        user_state["subscription_profile"] = subscription_profile
        return "", True

    amount = max(0.0, float(candidate.get("amount") or 0.0))
    merchant = (candidate.get("merchant") or "that merchant").strip() or "that merchant"
    signature = f"{merchant.lower()}|{amount:.2f}"

    last_signature = (subscription_profile.get("last_sql_subscription_alert_signature") or "").strip()
    last_alert = parse_iso_datetime(subscription_profile.get("last_sql_subscription_alert_at") or "")
    if signature == last_signature and last_alert and (now_dt - last_alert).days < 14:
        user_state["subscription_profile"] = subscription_profile
        return "", True

    subscription_profile["last_sql_subscription_alert_signature"] = signature
    subscription_profile["last_sql_subscription_alert_at"] = utc_now_iso()
    user_state["subscription_profile"] = subscription_profile
    return f"You've paid ${amount:.2f} to {merchant} 3 months straight. Cancel it or invest it?", True


def merge_witty_alert(reply_text, alert_text):
    """Prefix reply with subscription alert without duplicating text."""
    alert = (alert_text or "").strip()
    reply = (reply_text or "").strip()
    if not alert:
        return reply
    if not reply:
        return alert
    if alert in reply:
        return reply
    return f"{alert}\n\n{reply}"


def analytics_sql_weekly_mood_spending_report(user_id):
    """Correlate weekly spending and impulse behavior against inferred tone."""
    ensure_analytics_db()
    with analytics_db_lock:
        conn = open_analytics_db()
        try:
            cur = conn.cursor()
            cur.execute(
                """
                SELECT COUNT(*), COALESCE(SUM(amount), 0)
                FROM spend_events
                WHERE user_id = ?
                  AND datetime(created_at) >= datetime('now', '-7 days')
                """,
                (user_id,),
            )
            total_row = cur.fetchone() or (0, 0)
            event_count = int(total_row[0] or 0)
            if event_count <= 0:
                return {
                    "event_count": 0,
                    "report": "I need more spend logs from the last 7 days to build your financial vibe check.",
                }

            cur.execute(
                """
                SELECT COALESCE(inferred_tone, 'neutral') AS tone,
                       COUNT(*) AS purchase_count,
                       COALESCE(SUM(amount), 0) AS total_amount,
                       COALESCE(SUM(CASE WHEN transaction_type = 'Impulse' THEN 1 ELSE 0 END), 0) AS impulse_count
                FROM spend_events
                WHERE user_id = ?
                  AND datetime(created_at) >= datetime('now', '-7 days')
                GROUP BY COALESCE(inferred_tone, 'neutral')
                ORDER BY purchase_count DESC, total_amount DESC
                """,
                (user_id,),
            )
            tone_rows = cur.fetchall() or []

            cur.execute(
                """
                SELECT COALESCE(SUM(CASE WHEN transaction_type = 'Impulse' THEN 1 ELSE 0 END), 0),
                       COALESCE(SUM(CASE WHEN transaction_type = 'Impulse' AND stress_level = 'high' THEN 1 ELSE 0 END), 0)
                FROM spend_events
                WHERE user_id = ?
                  AND datetime(created_at) >= datetime('now', '-7 days')
                """,
                (user_id,),
            )
            impulse_total, high_stress_impulse = cur.fetchone() or (0, 0)
            impulse_total = int(impulse_total or 0)
            high_stress_impulse = int(high_stress_impulse or 0)

            dominant_tone = "neutral"
            dominant_amount = 0.0
            dominant_count = 0
            calm_total = 0.0
            calm_count = 0
            stressed_total = 0.0
            stressed_count = 0
            for tone, purchase_count, total_amount, _impulse_count in tone_rows:
                tone_label = str(tone or "neutral")
                purchase_count = int(purchase_count or 0)
                total_amount = float(total_amount or 0.0)
                if purchase_count > dominant_count:
                    dominant_tone = tone_label
                    dominant_amount = total_amount
                    dominant_count = purchase_count
                if tone_label in {"neutral", "formal", "direct", "funny"}:
                    calm_total += total_amount
                    calm_count += purchase_count
                if tone_label == "supportive":
                    stressed_total += total_amount
                    stressed_count += purchase_count

            stressed_impulse_pct = (high_stress_impulse / impulse_total * 100.0) if impulse_total > 0 else 0.0
            calm_savings_lift = 0.0
            if calm_count > 0 and stressed_count > 0:
                calm_avg = calm_total / calm_count
                stressed_avg = stressed_total / stressed_count
                if stressed_avg > 0:
                    calm_savings_lift = max(0.0, ((stressed_avg - calm_avg) / stressed_avg) * 100.0)

            report = (
                f"Hey! Looking at the data from this week, {stressed_impulse_pct:.0f}% of your impulse purchases happened when your stress level was high. "
                f"Your dominant conversation tone while spending was '{dominant_tone}' with ${dominant_amount:.2f} across {dominant_count} purchases. "
                f"When your tone looked calmer, your implied savings discipline improved by about {calm_savings_lift:.0f}%. "
                "Next time you feel stressed, ping me first and let's talk it out before opening any shopping apps!"
            )
            return {
                "event_count": event_count,
                "dominant_tone": dominant_tone,
                "dominant_amount": dominant_amount,
                "stressed_impulse_percentage": stressed_impulse_pct,
                "calm_savings_lift_percentage": calm_savings_lift,
                "report": report,
            }
        finally:
            conn.close()


def linguistic_engine_parse_intent(user_message):
    """Linguistic engine: parse natural language into analytical intent payloads."""
    normalized = normalize_intent_text(user_message)
    raw_lower = normalize_case(user_message)

    chart_spec = parse_graph_request(user_message)
    if chart_spec:
        if chart_spec.get("error"):
            return {"action": "chart_error", "error": chart_spec.get("error")}
        return {"action": "chart_generate", "chart_spec": chart_spec}

    watchlist_cmd = detect_watchlist_command(normalized)
    if watchlist_cmd:
        symbols = []
        if watchlist_cmd in {"add", "remove"}:
            payload_text = user_message
            for marker in ["watchlist add", "add to watchlist", "watchlist remove", "remove from watchlist", "track", "untrack"]:
                payload_text = re.sub(marker, " ", payload_text, flags=re.IGNORECASE)
            symbols = parse_symbol_or_company_list(payload_text)
        return {"action": f"watchlist_{watchlist_cmd}", "symbols": symbols}

    if any(x in normalized for x in ["subscription add", "add subscription"]):
        payload = parse_subscription_add_payload(user_message)
        if payload:
            return {"action": "subscription_add", "payload": payload}

    if any(x in normalized for x in ["draft cancellation email", "cancel subscription email", "cancellation email"]):
        payload = re.sub(r"draft cancellation email|cancel subscription email|cancellation email", " ", user_message, flags=re.IGNORECASE)
        target = re.sub(r"\s+", " ", payload).strip(" ,.-")
        return {"action": "subscription_cancel_draft", "name": target}

    if any(x in normalized for x in ["subscription remove", "remove subscription"]):
        payload = re.sub(r"subscription remove|remove subscription", " ", user_message, flags=re.IGNORECASE)
        target = re.sub(r"\s+", " ", payload).strip(" ,.-")
        return {"action": "subscription_remove", "name": target}

    if any(x in normalized for x in ["set goal", "savings goal", "goal amount"]):
        amount_match = re.search(r"\$?\s*([0-9]+(?:\.[0-9]+)?)", user_message)
        if amount_match:
            amount = float(amount_match.group(1))
            name = re.sub(r"\$?\s*[0-9]+(?:\.[0-9]+)?", " ", user_message)
            name = re.sub(r"\b(set|savings|goal|amount|my|for)\b", " ", name, flags=re.IGNORECASE)
            name = re.sub(r"\s+", " ", name).strip(" ,.-") or "your savings goal"
            return {"action": "subscription_goal_set", "name": name, "amount": amount}

    if any(x in normalized for x in ["phantom burn", "subscription decay", "burn alert", "subscription alert"]):
        return {"action": "subscription_decay_report"}

    if any(x in normalized for x in ["behavior summary", "spending triggers", "show triggers", "budget psychology", "behavioral budgeting"]):
        return {"action": "behavior_summary"}

    if any(x in normalized for x in ["coach nudge", "budget nudge", "financial coach", "coach me"]):
        return {"action": "behavior_nudge"}

    if any(x in normalized for x in ["runway buffer", "purchasing power parity", "ppp runway", "ppp", "multi currency runway", "shadow runway", "safety buffer"]) and any(
        x in normalized for x in ["runway", "buffer", "cap", "budget", "city", "currency", "ppp", "purchasing"]
    ):
        payload = parse_runway_buffer_payload(user_message)
        return {"action": "runway_buffer", "payload": payload}

    alpha_payload = parse_opportunity_cost_payload(user_message)
    if alpha_payload and alpha_payload.get("amount_usd", 0.0) > 0:
        return {"action": "opportunity_cost_gate", "payload": alpha_payload}

    if any(x in normalized for x in ["auto sweep on", "enable auto sweep"]):
        return {"action": "auto_sweep_on"}

    if any(x in normalized for x in ["auto sweep off", "disable auto sweep"]):
        return {"action": "auto_sweep_off"}

    if any(x in normalized for x in ["sweep target", "set target"]):
        target_text = re.sub(r".*(?:sweep target|set target)", "", user_message, flags=re.IGNORECASE).strip(" :.-")
        return {"action": "auto_sweep_target", "target": target_text}

    if any(x in normalized for x in ["supplier add", "add supplier"]):
        payload = parse_supplier_add_payload(user_message)
        if payload:
            return {"action": "supplier_add", "payload": payload}

    if any(x in normalized for x in ["supplier remove", "remove supplier"]):
        payload = re.sub(r"supplier remove|remove supplier", " ", user_message, flags=re.IGNORECASE)
        target = re.sub(r"\s+", " ", payload).strip(" ,.-")
        return {"action": "supplier_remove", "name": target}

    if any(x in normalized for x in ["supplier list", "list suppliers", "show suppliers", "my suppliers"]):
        return {"action": "supplier_list"}

    if any(x in raw_lower for x in ["geopolitical scan", "horizon scan", "regulatory scan", "tariff impact", "legislation impact", "policy impact"]):
        return {"action": "geopolitical_scan"}

    if re.search(r"\b(geopolit|regulator|tariff|tax law|legislation|congress|shipping delay|supply chain disruption)\b", raw_lower):
        return {"action": "geopolitical_scan"}

    spend_payload = parse_spend_log_payload(user_message)
    if spend_payload:
        return {"action": "spend_log", "payload": spend_payload}

    return None


def analytical_engine_execute(user_id, user_state, intent):
    """Analytical engine: deterministic execution and exact math/aggregation."""
    user_state = ensure_finance_profiles(user_state)
    action = (intent or {}).get("action") or ""
    if not action:
        return {"ok": False}

    finance_profile = user_state.get("finance_profile") or {}
    subscription_profile = user_state.get("subscription_profile") or {}
    behavior_profile = user_state.get("behavior_budget_profile") or {}
    geo_profile = user_state.get("geopolitical_profile") or {}

    if action == "watchlist_show":
        reply_text = get_watchlist_summary_reply(user_state, include_sources=False)
        return {"ok": True, "action": action, "state_changed": True, "text": reply_text, "source": "https://finance.yahoo.com/"}

    if action == "chart_error":
        return {"ok": True, "action": action, "state_changed": False, "text": intent.get("error") or "Invalid chart request."}

    if action == "chart_generate":
        chart_spec = intent.get("chart_spec") or {}
        chart_url, _cfg = build_quickchart_url(chart_spec)
        chart_type = chart_spec.get("chart_type") or "line"
        values = chart_spec.get("values") or []
        text = (
            f"Generated a {chart_type} chart with {len(values)} data points.\n"
            f"Chart link: {chart_url}"
        )
        return {
            "ok": True,
            "action": action,
            "state_changed": False,
            "text": text,
            "source": chart_url,
            "chart_url": chart_url,
            "chart_spec": chart_spec,
        }

    if action == "watchlist_clear":
        finance_profile["watchlist"] = []
        finance_profile["watchlist_last_snapshot"] = []
        finance_profile["watchlist_last_checked"] = utc_now_iso()
        user_state["finance_profile"] = finance_profile
        return {"ok": True, "action": action, "state_changed": True, "text": "Done. Your watchlist is now empty."}

    if action in {"watchlist_add", "watchlist_remove"}:
        symbols = intent.get("symbols") or []
        watchlist = finance_profile.get("watchlist") or []
        if action == "watchlist_add":
            for symbol in symbols:
                if symbol not in watchlist:
                    watchlist.append(symbol)
            watchlist = watchlist[:60]
            finance_profile["watchlist"] = watchlist
            finance_profile["watchlist_last_checked"] = utc_now_iso()
            user_state["finance_profile"] = finance_profile
            if symbols:
                return {
                    "ok": True,
                    "action": action,
                    "state_changed": True,
                    "text": f"Watchlist updated. Tracking: {', '.join(watchlist)}.",
                }
            return {"ok": True, "action": action, "state_changed": False, "text": "Please include at least one stock symbol or company name."}

        before = len(watchlist)
        watchlist = [symbol for symbol in watchlist if symbol not in set(symbols)]
        finance_profile["watchlist"] = watchlist
        finance_profile["watchlist_last_checked"] = utc_now_iso()
        user_state["finance_profile"] = finance_profile
        if len(watchlist) != before:
            return {
                "ok": True,
                "action": action,
                "state_changed": True,
                "text": f"Removed from watchlist. Now tracking: {', '.join(watchlist) if watchlist else 'none' }.",
            }
        return {"ok": True, "action": action, "state_changed": False, "text": "None of those symbols were in your watchlist."}

    if action == "subscription_add":
        payload = intent.get("payload") or {}
        items = subscription_profile.get("items") or []
        existing = None
        for item in items:
            if normalize_case(item.get("name")) == normalize_case(payload.get("name")):
                existing = item
                break
        if existing:
            existing["monthly_cost"] = float(payload.get("monthly_cost") or 0.0)
            existing["days_since_last_use"] = int(payload.get("days_since_last_use") or 0)
            existing["updated_at"] = utc_now_iso()
            action_word = "updated"
            analytics_sql_upsert_subscription(user_id, existing)
        else:
            row = {
                "name": payload.get("name") or "",
                "monthly_cost": float(payload.get("monthly_cost") or 0.0),
                "days_since_last_use": int(payload.get("days_since_last_use") or 0),
                "updated_at": utc_now_iso(),
            }
            items.append(row)
            action_word = "added"
            analytics_sql_upsert_subscription(user_id, row)
        subscription_profile["items"] = items[:120]
        subscription_profile["last_alert_at"] = utc_now_iso()
        user_state["subscription_profile"] = subscription_profile
        return {
            "ok": True,
            "action": action,
            "state_changed": True,
            "text": (
                f"Subscription {action_word}: {payload.get('name')} at ${float(payload.get('monthly_cost') or 0):.2f}/mo, "
                f"unused {int(payload.get('days_since_last_use') or 0)} days."
            ),
        }

    if action == "subscription_remove":
        target_name = (intent.get("name") or "").strip()
        if not target_name:
            return {"ok": True, "action": action, "state_changed": False, "text": "Tell me which subscription to remove."}
        items = subscription_profile.get("items") or []
        before = len(items)
        items = [item for item in items if normalize_case(item.get("name")) != normalize_case(target_name)]
        subscription_profile["items"] = items
        subscription_profile["last_alert_at"] = utc_now_iso()
        user_state["subscription_profile"] = subscription_profile
        if len(items) != before:
            analytics_sql_delete_subscription(user_id, target_name)
            return {"ok": True, "action": action, "state_changed": True, "text": f"Removed subscription: {target_name}."}
        return {"ok": True, "action": action, "state_changed": False, "text": "I could not find that subscription in your tracked list."}

    if action == "subscription_cancel_draft":
        target_name = (intent.get("name") or "").strip()
        subscription_profile = user_state.get("subscription_profile") or {}
        vampire_alerts = subscription_profile.get("vampire_alerts") or []
        match = None
        if target_name:
            for alert in vampire_alerts:
                if normalize_case(alert.get("service_name")) == normalize_case(target_name):
                    match = alert
                    break
            if match is None:
                for item in subscription_profile.get("items") or []:
                    if normalize_case(item.get("name")) == normalize_case(target_name):
                        match = {
                            "service_name": item.get("name"),
                            "monthly_cost": float(item.get("monthly_cost") or 0.0),
                        }
                        break
        elif vampire_alerts:
            match = vampire_alerts[0]

        if not match:
            return {
                "ok": True,
                "action": action,
                "state_changed": False,
                "text": "I could not identify which subscription to cancel. Ask like: draft cancellation email Netflix.",
            }

        draft = build_subscription_cancellation_email(match.get("service_name") or "Subscription", match.get("monthly_cost") or 0.0)
        text = f"Subject: {draft['subject']}\n\n{draft['body']}"
        return {
            "ok": True,
            "action": action,
            "state_changed": False,
            "text": text,
            "cancel_draft": draft,
        }

    if action == "subscription_goal_set":
        goal_name = (intent.get("name") or "your savings goal").strip() or "your savings goal"
        goal_amount = float(intent.get("amount") or 0.0)
        if goal_amount <= 0:
            return {"ok": True, "action": action, "state_changed": False, "text": "Set a valid goal amount above zero."}
        subscription_profile["savings_goal"] = {"name": goal_name, "amount": goal_amount}
        subscription_profile["last_alert_at"] = utc_now_iso()
        user_state["subscription_profile"] = subscription_profile
        analytics_sql_set_goal(user_id, goal_name, goal_amount)
        return {"ok": True, "action": action, "state_changed": True, "text": f"Savings goal set: {goal_name} (${goal_amount:.2f})."}

    if action == "subscription_decay_report":
        report = build_subscription_decay_report(user_state, include_sources=False)
        return {"ok": True, "action": action, "state_changed": True, "text": report}

    if action == "spend_log":
        payload = intent.get("payload") or {}
        user_state = add_spend_event(user_state, payload)
        analytics_sql_insert_spend_event(user_id, payload)
        projection_text = ""
        projection = None
        if is_discretionary_expense_category(payload.get("category")):
            projection = build_dynamic_opportunity_cost_projection(
                payload.get("amount") or 0.0,
                annual_return=0.075,
            )
            projection_text = render_dynamic_opportunity_cost_projection(projection)
        return {
            "ok": True,
            "action": action,
            "state_changed": True,
            "text": (
                f"Spend logged: ${float(payload.get('amount') or 0):.2f} on {payload.get('category')} "
                f"({payload.get('day_of_week')} {int(payload.get('hour') or 0):02d}:00, stress {payload.get('stress_level')})."
                + (f" {projection_text}" if projection_text else "")
            ),
            "opportunity_cost_projection": projection,
        }

    if action == "behavior_summary":
        insights = analytics_sql_behavior_insights(user_id)
        if insights.get("event_count", 0) < 5:
            text = "I need at least 5 spend logs to learn your emotional spending triggers accurately."
        else:
            lines = [
                "Behavioral budgeting insights:",
                f"- Logged events: {insights['event_count']}",
                f"- Top spend category: {insights['common_category'] or 'other'}",
                f"- Friday evening spend multiplier: {insights['friday_late_multiplier']:.2f}x",
                f"- High-stress spend multiplier: {insights['high_stress_multiplier']:.2f}x",
                f"- Estimated avoidable spend per trigger window: ${insights['estimated_avoidable_spend']:.2f}",
            ]
            if insights.get("top_trigger"):
                lines.append(f"- Emotional trigger pattern detected: {insights['top_trigger']}")
            text = "\n".join(lines)
        return {"ok": True, "action": action, "state_changed": False, "text": text}

    if action == "behavior_nudge":
        nudge = build_empathetic_budget_nudge(user_state)
        if nudge:
            behavior_profile["last_coach_alert_at"] = utc_now_iso()
            user_state["behavior_budget_profile"] = behavior_profile
            return {"ok": True, "action": action, "state_changed": True, "text": nudge}
        return {"ok": True, "action": action, "state_changed": False, "text": "No urgent trigger window detected right now. I can still help with a low-spend alternative plan."}

    if action == "runway_buffer":
        payload = intent.get("payload") or {}
        finance_profile = user_state.get("finance_profile") or {}
        profile = finance_profile.get("runway_buffer_profile") or {}

        capital_usd = float(payload.get("capital_usd") or profile.get("capital_usd") or 0.0)
        city = (payload.get("city") or profile.get("current_city") or "").strip()
        base_city = (payload.get("base_city") or profile.get("base_city") or BASELINE_COST_INDEX_CITY).strip()
        monthly_cap = float(payload.get("base_monthly_cap_usd") or profile.get("base_monthly_cap_usd") or 0.0)
        payload_shadow_enabled = payload.get("shadow_runway_enabled")
        if payload_shadow_enabled is None:
            shadow_enabled = bool(profile.get("shadow_runway_enabled", False))
        else:
            shadow_enabled = bool(payload_shadow_enabled)
        safety_buffer_months = float(payload.get("safety_buffer_months") or profile.get("safety_buffer_months") or 0.0)

        if not city:
            return {
                "ok": True,
                "action": action,
                "state_changed": False,
                "text": "Tell me your destination city (for example: London, Dubai, Mumbai) so I can compute your PPP-adjusted runway.",
            }
        if capital_usd <= 0:
            return {
                "ok": True,
                "action": action,
                "state_changed": False,
                "text": "Include your available capital in USD, for example: runway buffer in London with capital 120000 and monthly budget 4000.",
            }

        try:
            metrics = build_runway_buffer_metrics(
                capital_usd=capital_usd,
                current_city=city,
                base_monthly_cap_usd=monthly_cap,
                base_city=base_city,
                shadow_runway_enabled=shadow_enabled,
                safety_buffer_months=safety_buffer_months,
            )
        except Exception as e:
            return {"ok": True, "action": action, "state_changed": False, "text": f"Runway buffer calculation failed: {str(e)}"}

        finance_profile["runway_buffer_profile"] = {
            "base_city": metrics.get("base_city") or base_city,
            "current_city": metrics.get("current_city") or city,
            "capital_usd": metrics.get("capital_usd") or capital_usd,
            "base_monthly_cap_usd": metrics.get("base_monthly_cap_usd") or monthly_cap,
            "shadow_runway_enabled": bool(metrics.get("shadow_runway_enabled")),
            "safety_buffer_months": float(metrics.get("safety_buffer_months") or 0.0),
            "updated_at": utc_now_iso(),
        }
        user_state["finance_profile"] = finance_profile

        text = (
            "Multi-currency Runway Buffer:\n"
            f"- City rotation target: {metrics['current_city'].title()} ({metrics['target_currency']})\n"
            f"- Capital pool: ${metrics['capital_usd']:.2f} USD\n"
            f"- Baseline monthly cap ({metrics['base_city'].title()}): ${metrics['base_monthly_cap_usd']:.2f} USD\n"
            f"- PPP-adjusted monthly cap: ${metrics['ppp_adjusted_monthly_cap_usd']:.2f} USD ({metrics['ppp_adjusted_monthly_cap_local']:.2f} {metrics['target_currency']})\n"
            f"- Runway (nominal): {metrics['runway_months_nominal']:.1f} months\n"
            f"- Runway (real PPP-adjusted): {metrics['runway_months_ppp_adjusted']:.1f} months\n"
            f"- Shadow Runway: {'ON' if metrics['shadow_runway_enabled'] else 'OFF'} | safety buffer {metrics['safety_buffer_months']:.1f} months\n"
            f"- Dashboard display runway: {metrics['runway_display_months']:.1f} months ({metrics['runway_display_color']})\n"
            f"- Locked reserve (hidden emergency runway): {metrics['locked_months']:.1f} months\n"
            f"- FX USD->{metrics['target_currency']}: {metrics['fx_rate_usd_to_target']:.6f}\n"
            "- Note: This is a disclosed calculation using your provided capital/budget inputs plus the app's PPP cost-index map and latest FX snapshot."
        )
        return {
            "ok": True,
            "action": action,
            "state_changed": True,
            "text": text,
            "source": metrics.get("fx_source") or "https://open.er-api.com/",
            "runway_buffer": metrics,
        }

    if action == "opportunity_cost_gate":
        payload = intent.get("payload") or {}
        threshold = float(behavior_profile.get("opportunity_cost_threshold_usd") or OPPORTUNITY_COST_THRESHOLD_USD)
        default_years = int(behavior_profile.get("opportunity_cost_default_years") or OPPORTUNITY_COST_DEFAULT_YEARS)
        default_return = float(behavior_profile.get("opportunity_cost_default_annual_return") or OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN)

        amount_usd = float(payload.get("amount_usd") or 0.0)
        if amount_usd <= 0:
            return {
                "ok": True,
                "action": action,
                "state_changed": False,
                "text": "Share the purchase amount and I will run the Alpha Rule gate, for example: buy sneakers for $200.",
            }

        if not bool(payload.get("is_non_essential", True)):
            return {
                "ok": True,
                "action": action,
                "state_changed": False,
                "text": "That looks like an essential expense, so I will not block it with the Alpha Rule gate.",
            }

        years = int(payload.get("years") or default_years)
        annual_return = float(payload.get("annual_return") if payload.get("annual_return") is not None else default_return)
        gate = build_opportunity_cost_gate(amount_usd=amount_usd, years=years, annual_return=annual_return)
        item = (payload.get("item") or "purchase").strip() or "purchase"
        rate_pct = gate["annual_return"] * 100.0

        behavior_profile["last_opportunity_cost_gate"] = {
            "item": item,
            "amount_usd": amount_usd,
            "threshold_usd": threshold,
            "years": gate["years"],
            "annual_return": gate["annual_return"],
            "future_value_usd": gate["future_value_usd"],
            "opportunity_cost_usd": gate["opportunity_cost_usd"],
            "created_at": utc_now_iso(),
        }
        user_state["behavior_budget_profile"] = behavior_profile

        if amount_usd < threshold:
            text = (
                f"Alpha Rule note: this {item} purchase is ${amount_usd:.2f}, below your gating threshold of ${threshold:.2f}. "
                f"Using an assumed {rate_pct:.1f}% annual return for {gate['years']} years, it compounds to about ${gate['future_value_usd']:.2f} (illustrative, not guaranteed)."
            )
            return {"ok": True, "action": action, "state_changed": True, "text": text}

        text = (
            f"Alpha Rule reality check: This ${amount_usd:.2f} {item} purchase can cost about "
            f"${gate['future_value_usd']:.2f} over {gate['years']} years using an assumed {rate_pct:.1f}% annual return "
            f"(${gate['opportunity_cost_usd']:.2f} in opportunity cost; illustrative, not guaranteed). Do you still want to execute?"
        )
        return {
            "ok": True,
            "action": action,
            "state_changed": True,
            "text": text,
            "source": "https://www.investor.gov/financial-tools-calculators/calculators/compound-interest-calculator",
            "opportunity_cost": gate,
        }

    if action == "auto_sweep_on":
        behavior_profile["auto_sweep_enabled"] = True
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        return {"ok": True, "action": action, "state_changed": True, "text": "Auto-sweep is enabled for your coaching nudges."}

    if action == "auto_sweep_off":
        behavior_profile["auto_sweep_enabled"] = False
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        return {"ok": True, "action": action, "state_changed": True, "text": "Auto-sweep is disabled."}

    if action == "auto_sweep_target":
        target = (intent.get("target") or "").strip()
        if not target:
            return {"ok": True, "action": action, "state_changed": False, "text": "Set target like: sweep target investment index."}
        behavior_profile["auto_sweep_target"] = target
        behavior_profile["last_coach_alert_at"] = utc_now_iso()
        user_state["behavior_budget_profile"] = behavior_profile
        return {"ok": True, "action": action, "state_changed": True, "text": f"Auto-sweep target updated to: {target}."}

    if action == "supplier_add":
        payload = intent.get("payload") or {}
        suppliers = geo_profile.get("suppliers") or []
        existing = None
        for row in suppliers:
            if normalize_case(row.get("name")) == normalize_case(payload.get("name")):
                existing = row
                break
        if existing:
            existing.update(payload)
            existing["updated_at"] = utc_now_iso()
            action_word = "updated"
            analytics_sql_upsert_supplier(user_id, existing)
        else:
            new_row = {
                "name": payload.get("name") or "",
                "country": payload.get("country") or "Unknown",
                "material": payload.get("material") or "other",
                "quality_score": float(payload.get("quality_score") or 75.0),
                "spend_share": float(payload.get("spend_share") or 0.0),
                "updated_at": utc_now_iso(),
            }
            suppliers.append(new_row)
            action_word = "added"
            analytics_sql_upsert_supplier(user_id, new_row)
        geo_profile["suppliers"] = suppliers[:200]
        user_state["geopolitical_profile"] = geo_profile
        return {
            "ok": True,
            "action": action,
            "state_changed": True,
            "text": (
                f"Supplier {action_word}: {payload.get('name')} | country {payload.get('country')} | "
                f"material {payload.get('material')} | quality {float(payload.get('quality_score') or 0):.0f} | spend share {float(payload.get('spend_share') or 0):.1f}%"
            ),
        }

    if action == "supplier_remove":
        target = (intent.get("name") or "").strip()
        if not target:
            return {"ok": True, "action": action, "state_changed": False, "text": "Tell me which supplier to remove."}
        suppliers = geo_profile.get("suppliers") or []
        before = len(suppliers)
        suppliers = [row for row in suppliers if normalize_case(row.get("name")) != normalize_case(target)]
        geo_profile["suppliers"] = suppliers
        user_state["geopolitical_profile"] = geo_profile
        if len(suppliers) != before:
            analytics_sql_delete_supplier(user_id, target)
            return {"ok": True, "action": action, "state_changed": True, "text": f"Removed supplier: {target}."}
        return {"ok": True, "action": action, "state_changed": False, "text": "Supplier not found in your profile."}

    if action == "supplier_list":
        suppliers = geo_profile.get("suppliers") or []
        if not suppliers:
            return {"ok": True, "action": action, "state_changed": False, "text": "No suppliers saved yet. Add one with: supplier add <name> country <country> material <material> quality <score> spend <percent>."}
        lines = ["Supplier exposure profile:"]
        for row in suppliers[:20]:
            lines.append(
                f"- {row.get('name')}: {row.get('country')} | {row.get('material')} | quality {float(row.get('quality_score') or 0):.0f} | spend {float(row.get('spend_share') or 0):.1f}%"
            )
        return {"ok": True, "action": action, "state_changed": False, "text": "\n".join(lines)}

    if action == "geopolitical_scan":
        report_text, sources = build_geopolitical_horizon_report(user_id, user_state, include_sources=False)
        return {
            "ok": True,
            "action": action,
            "state_changed": True,
            "text": report_text,
            "source": (sources[0] if sources else "https://news.google.com/"),
        }

    return {"ok": False}


def linguistic_engine_render_response(engine_result, include_sources=False):
    """Linguistic engine: translate analytical outputs to user-facing empathetic response."""
    if not engine_result or not engine_result.get("ok"):
        return ""
    text = (engine_result.get("text") or "").strip()
    if not text:
        return ""
    if include_sources and engine_result.get("source"):
        return with_citations(text, [engine_result.get("source")], True)
    return text


def parse_graph_request(user_message):
    """Parse natural-language chart requests into structured chart specs."""
    raw = (user_message or "").strip()
    lowered = normalize_case(raw)
    trigger_words = ["graph", "chart", "plot", "visualize", "visualise"]
    if not any(word in lowered for word in trigger_words):
        return None

    chart_type = "line"
    if any(k in lowered for k in ["bar chart", "bar graph", "histogram", "bars", "graph bar", "plot bar", "bar "]):
        chart_type = "bar"
    elif any(k in lowered for k in ["pie chart", "donut", "doughnut", "graph pie", "plot pie"]):
        chart_type = "pie"
    elif any(k in lowered for k in ["scatter", "scatterplot", "scatter plot"]):
        chart_type = "scatter"
    elif any(k in lowered for k in ["line chart", "line graph", "trend line"]):
        chart_type = "line"

    title_match = re.search(r"(?:title|called|name it)\s+['\"]?([^'\"\n]+)['\"]?", raw, flags=re.IGNORECASE)
    title = (title_match.group(1).strip() if title_match else "User Requested Chart")

    xy_pairs = []
    for match in re.finditer(r"([A-Za-z0-9_.\- ]{1,30})\s*[:=]\s*(-?\d+(?:\.\d+)?)", raw):
        label = re.sub(r"\s+", " ", match.group(1)).strip(" ,")
        try:
            value = float(match.group(2))
        except Exception:
            continue
        if label:
            xy_pairs.append((label, value))

    labels = []
    values = []
    if xy_pairs:
        for label, value in xy_pairs[:30]:
            labels.append(label)
            values.append(value)
    else:
        num_matches = re.findall(r"-?\d+(?:\.\d+)?", raw)
        parsed = []
        for token in num_matches[:30]:
            try:
                parsed.append(float(token))
            except Exception:
                continue
        if len(parsed) >= 2:
            labels = [str(i + 1) for i in range(len(parsed))]
            values = parsed

    if not values:
        return {
            "error": "I couldn't detect data points. Provide values like: graph bar revenue:120, costs:80, profit:40",
        }

    x_label_match = re.search(r"x\s*label\s*[:=]\s*([A-Za-z0-9\s\-_/]{1,40})", raw, flags=re.IGNORECASE)
    y_label_match = re.search(r"y\s*label\s*[:=]\s*([A-Za-z0-9\s\-_/]{1,40})", raw, flags=re.IGNORECASE)
    x_label = x_label_match.group(1).strip() if x_label_match else ""
    y_label = y_label_match.group(1).strip() if y_label_match else ""

    return {
        "chart_type": chart_type,
        "title": title,
        "labels": labels,
        "values": values,
        "x_label": x_label,
        "y_label": y_label,
    }


def build_quickchart_url(chart_spec):
    """Build a QuickChart URL from chart spec for easy rendering."""
    chart_type = chart_spec.get("chart_type") or "line"
    labels = chart_spec.get("labels") or []
    values = chart_spec.get("values") or []
    title = chart_spec.get("title") or "Chart"
    x_label = chart_spec.get("x_label") or ""
    y_label = chart_spec.get("y_label") or ""

    base_color = "rgb(46, 134, 193)"
    config = {
        "type": chart_type,
        "data": {
            "labels": labels,
            "datasets": [
                {
                    "label": title,
                    "data": values,
                    "borderColor": base_color,
                    "backgroundColor": "rgba(46, 134, 193, 0.35)",
                    "fill": chart_type == "line",
                }
            ],
        },
        "options": {
            "plugins": {
                "legend": {"display": chart_type != "pie"},
                "title": {"display": True, "text": title},
            },
            "scales": {
                "x": {"title": {"display": bool(x_label), "text": x_label}},
                "y": {"title": {"display": bool(y_label), "text": y_label}},
            },
        },
    }

    chart_json = json.dumps(config, separators=(",", ":"))
    return f"https://quickchart.io/chart?width=900&height=520&c={quote_plus(chart_json)}", config


def get_chart_reply_from_request(user_message, include_sources=False):
    """Generate chart URL from natural language and return user-facing text."""
    parsed = parse_graph_request(user_message)
    if not parsed:
        return ""
    if parsed.get("error"):
        return parsed["error"]

    chart_url, _cfg = build_quickchart_url(parsed)
    chart_type = parsed.get("chart_type") or "line"
    point_count = len(parsed.get("values") or [])
    preview_values = ", ".join(f"{v:g}" for v in (parsed.get("values") or [])[:8])
    text = (
        f"Generated a {chart_type} chart with {point_count} data points. "
        f"Preview values: {preview_values}.\n"
        f"Chart link: {chart_url}\n"
        "If you want, I can regenerate it with different colors, labels, or chart type."
    )
    return with_citations(text, [chart_url], include_sources)


def extract_country_from_text(normalized_text):
    """Best-effort country extraction for factual queries."""
    m = re.search(r"\b(?:in|of|for)\s+([a-z\s]+)$", normalized_text)
    if m:
        country = m.group(1).strip()
        country = re.sub(r"\b(is|that|true|simple|please|plz|rn|right now|but|like)\b", "", country).strip()
        country = re.sub(r"\s+", " ", country).strip()
        if country:
            known = ["brazil", "france", "canada", "mexico", "argentina", "japan", "china", "india", "mongolia", "usa", "united states"]
            for c in known:
                if re.search(rf"\b{re.escape(c)}\b", country):
                    return c
            return country

    known = ["brazil", "france", "canada", "mexico", "argentina", "japan", "china", "india", "mongolia", "usa", "united states"]
    for c in known:
        if re.search(rf"\b{re.escape(c)}\b", normalized_text):
            return c
    return ""


def get_capital_reply(normalized_text, include_sources=False):
    """Fetch country capital via Wikidata."""
    country = extract_country_from_text(normalized_text)
    if not country:
        return ""

    try:
        search_url = (
            "https://www.wikidata.org/w/api.php?action=wbsearchentities"
            f"&search={quote_plus(country)}&language=en&format=json&limit=1"
        )
        search_payload = fetch_json_url(search_url)
        results = search_payload.get("search") or []
        if not results:
            return ""

        country_id = results[0].get("id")
        if not country_id:
            return ""

        entity_url = f"https://www.wikidata.org/wiki/Special:EntityData/{country_id}.json"
        entity_payload = fetch_json_url(entity_url)
        entity = (entity_payload.get("entities") or {}).get(country_id) or {}
        claims = entity.get("claims") or {}
        capital_claims = claims.get("P36") or []
        if not capital_claims:
            return ""

        def has_end_date(claim):
            qualifiers = claim.get("qualifiers") or {}
            return "P582" in qualifiers

        preferred_active = [c for c in capital_claims if c.get("rank") == "preferred" and not has_end_date(c)]
        normal_active = [c for c in capital_claims if c.get("rank") in {"normal", "preferred"} and not has_end_date(c)]
        ordered_claims = preferred_active or normal_active or capital_claims

        capital_id = None
        for claim in ordered_claims:
            mainsnak = claim.get("mainsnak") or {}
            datavalue = mainsnak.get("datavalue") or {}
            value = datavalue.get("value") or {}
            capital_id = value.get("id")
            if capital_id:
                break
        if not capital_id:
            return ""

        capital_url = f"https://www.wikidata.org/wiki/Special:EntityData/{capital_id}.json"
        capital_payload = fetch_json_url(capital_url)
        capital_entity = (capital_payload.get("entities") or {}).get(capital_id) or {}
        labels = capital_entity.get("labels") or {}
        capital_name = (labels.get("en") or {}).get("value")
        if not capital_name:
            return ""

        reply = f"The capital of {country.title()} is {capital_name}."
        return with_citations(reply, [f"https://www.wikidata.org/wiki/{country_id}", f"https://www.wikidata.org/wiki/{capital_id}"], include_sources)
    except Exception:
        pass
    return ""


def get_inflation_reply(normalized_text, include_sources=False):
    """Handle inflation trend questions with improved phrasing."""
    country = extract_country_from_text(normalized_text)
    if country:
        query = f"latest inflation rate in {country}"
    else:
        query = "latest inflation rate"

    reply = get_web_search_reply(query, include_sources=include_sources)
    if reply and not is_weak_web_response(reply):
        return reply

    fallback = (
        "Inflation trends depend on country and timeframe. In many places inflation has cooled from recent peaks, "
        "but it is still above target in some economies. Tell me a country and I will give you the latest figure."
    )
    return with_citations(fallback, [f"https://duckduckgo.com/?q={quote_plus(query)}"], include_sources)


def get_web_search_reply(normalized_text, include_sources=False):
    """Get a quick data-based web answer from DuckDuckGo instant answers."""
    query = normalized_text.strip(" ?")
    if not query:
        return None

    leader_info = extract_leader_query(query)
    if leader_info:
        leader_answer = get_current_leader_from_wikidata(
            leader_info["country"],
            leader_info["role"],
            include_sources=include_sources,
        )
        if leader_answer:
            return leader_answer

    query = rewrite_search_query_for_specificity(query)

    encoded = quote_plus(query)
    url = f"https://api.duckduckgo.com/?q={encoded}&format=json&no_html=1&skip_disambig=1"
    try:
        data = fetch_json_url(url)
        abstract = (data.get("AbstractText") or "").strip()
        answer = (data.get("Answer") or "").strip()
        if answer:
            return with_citations(answer, [url], include_sources)
        if abstract:
            return with_citations(abstract, [url], include_sources)

        related = data.get("RelatedTopics") or []
        for item in related:
            text = (item.get("Text") or "").strip() if isinstance(item, dict) else ""
            if text:
                specific = maybe_extract_leader_name(text, query)
                if specific:
                    return specific
                return with_citations(text, [url], include_sources)
            if isinstance(item, dict) and isinstance(item.get("Topics"), list):
                for sub in item["Topics"]:
                    sub_text = (sub.get("Text") or "").strip() if isinstance(sub, dict) else ""
                    if sub_text:
                        specific = maybe_extract_leader_name(sub_text, query)
                        if specific:
                            return specific
                        return with_citations(sub_text, [url], include_sources)

        snippets = fetch_duckduckgo_snippets(query)
        if snippets:
            specific = maybe_extract_leader_name(" ".join(snippets), query)
            if specific:
                return specific
            joined = " ".join(snippets[:2])
            return with_citations(joined[:900], [f"https://duckduckgo.com/?q={encoded}"], include_sources)

        wiki = fetch_wikipedia_summary(query, include_sources=include_sources)
        if wiki:
            return wiki
        return build_no_excuses_analysis(query, include_sources=include_sources)
    except Exception:
        snippets = fetch_duckduckgo_snippets(query)
        if snippets:
            specific = maybe_extract_leader_name(" ".join(snippets), query)
            if specific:
                return specific
            return with_citations(" ".join(snippets[:2])[:900], [f"https://duckduckgo.com/?q={encoded}"], include_sources)

        wiki = fetch_wikipedia_summary(query, include_sources=include_sources)
        if wiki:
            return wiki
        return build_no_excuses_analysis(query, include_sources=include_sources)


def rewrite_search_query_for_specificity(query):
    """Rewrite broad queries into higher-precision factual search prompts."""
    q = normalize_case(query).strip()

    leader_match = re.search(r"(?:who\s+is\s+)?(?:the\s+)?(president|prime minister|king|queen|head of state)\s+(?:of\s+)?([a-z\s]+)$", q)
    if leader_match:
        role = leader_match.group(1).strip()
        place = leader_match.group(2).strip()
        if "current" in q and "name" in q:
            return query
        return f"current {role} of {place} name"

    if "how many" in q and "die" in q:
        if "safety estimate" in q:
            return query
        return f"{q} safety estimate"

    return query


def is_weak_web_response(text):
    """Detect weak fallback-like search responses."""
    if not text:
        return True
    lowered = normalize_case(text)
    weak_markers = [
        "could not find",
        "could not reach",
        "try a more specific",
        "i can fetch",
    ]
    return any(marker in lowered for marker in weak_markers)


def sanitize_query_for_web(text):
    """Strip conversational noise from a web query."""
    q = normalize_intent_text(text)
    q = re.sub(r"\b(please|plz|bro|bruh|lol|lmao|idk|tbh|rn|right now|quick one|real quick|could you|can you|help me)\b", " ", q)
    q = re.sub(r"\b(is that true|for that|but like simple|but like|like simple|simple)\b", " ", q)
    q = re.sub(r"\s+", " ", q).strip(" ?!.,")
    return q


def is_personal_message_intent(normalized_text):
    """Detect chat-directed/personal prompts where web search is less appropriate."""
    personal_markers = [
        "do you love me", "what are you doing", "how are you", "who are you",
        "hello", "hey", "hi", "wyd", "i feel", "i need help emotionally"
    ]
    return any(marker in normalized_text for marker in personal_markers)


def build_web_query_candidates(normalized_text, original_text):
    """Generate multiple candidate queries for robust web lookup."""
    candidates = []
    raw = original_text.strip()
    norm = normalized_text.strip()
    sanitized_raw = sanitize_query_for_web(raw)
    sanitized_norm = sanitize_query_for_web(norm)

    rewritten_possessive = rewrite_possessive_data_query(original_text)
    rewritten_natural = rewrite_natural_fact_query(original_text)
    explain_topic = extract_explain_topic(norm)

    for c in [raw, norm, sanitized_raw, sanitized_norm, rewritten_possessive, rewritten_natural, explain_topic]:
        if c:
            c = c.strip()
            if c and c not in candidates:
                candidates.append(c)

    # Also try more specific variant for short noun-like phrases.
    if len(sanitized_norm.split()) <= 4 and sanitized_norm:
        enriched = f"what is {sanitized_norm}"
        if enriched not in candidates:
            candidates.append(enriched)

    return candidates


def rewrite_natural_fact_query(text):
    """Rewrite loose, natural phrasing into clearer factual queries."""
    q = sanitize_query_for_web(text.lower())

    m = re.search(r"(capital(?: city)?)\s+(?:for|of)\s+([a-z\s]+)", q)
    if m:
        return f"what is the capital of {m.group(2).strip()}"

    m = re.search(r"who\s+is\s+running\s+([a-z\s]+)", q)
    if m:
        return f"who is the president of {m.group(1).strip()}"

    m = re.search(r"inflation\s+dropped", q)
    if m:
        return "latest inflation trend"

    return ""


def get_best_web_answer(normalized_text, original_text, include_sources=False):
    """Try several query candidates and return the first strong answer."""
    for candidate in build_web_query_candidates(normalized_text, original_text):
        reply = get_web_search_reply(candidate, include_sources=include_sources)
        if reply and not is_weak_web_response(reply):
            return reply

    # If nothing strong found, return last attempt on sanitized query.
    fallback_q = sanitize_query_for_web(original_text) or normalized_text
    return get_web_search_reply(fallback_q, include_sources=include_sources)


def extract_leader_query(text):
    """Extract leader role and country from free-form query text."""
    q = normalize_intent_text(normalize_case(text))

    patterns = [
        r"(?:who is )?(?:the )?(president|prime minister|head of state|head of government|king|queen) of ([a-z\s]+)",
        r"([a-z\s]+) (president|prime minister|head of state|head of government|king|queen)",
        r"who is running ([a-z\s]+)",
        r"who runs ([a-z\s]+)",
    ]

    for pattern in patterns:
        match = re.search(pattern, q)
        if match:
            if pattern.startswith("(?:who"):
                role = match.group(1).strip()
                country = match.group(2).strip()
            elif pattern.startswith("who is running") or pattern.startswith("who runs"):
                role = "president"
                country = match.group(1).strip()
            else:
                country = match.group(1).strip()
                role = match.group(2).strip()

            country = re.sub(r"\b(the|current|name)\b", "", country).strip()
            country = re.sub(r"\b(with|source|sources|citation|citations|please|pls)\b", "", country).strip()
            country = re.sub(r"\s+", " ", country)
            if country:
                return {"role": role, "country": country}
    return None


def get_current_leader_from_wikidata(country_name, role, include_sources=False):
    """Fetch current leader name from Wikidata for country+role queries."""
    try:
        search_url = (
            "https://www.wikidata.org/w/api.php?action=wbsearchentities"
            f"&search={quote_plus(country_name)}&language=en&format=json&limit=1"
        )
        search_payload = fetch_json_url(search_url)
        results = search_payload.get("search") or []
        if not results:
            return ""

        country_id = results[0].get("id")
        if not country_id:
            return ""

        entity_url = f"https://www.wikidata.org/wiki/Special:EntityData/{country_id}.json"
        entity_payload = fetch_json_url(entity_url)
        entity = (entity_payload.get("entities") or {}).get(country_id) or {}
        claims = entity.get("claims") or {}

        role_key_map = {
            "president": "P35",          # head of state
            "head of state": "P35",
            "king": "P35",
            "queen": "P35",
            "prime minister": "P6",      # head of government
            "head of government": "P6",
        }
        claim_key = role_key_map.get(role, "P35")
        claim_values = claims.get(claim_key) or []
        if not claim_values and claim_key != "P35":
            claim_values = claims.get("P35") or []
        if not claim_values and claim_key != "P6":
            claim_values = claims.get("P6") or []
        if not claim_values:
            return ""

        # Prefer preferred-rank claims without end date, then normal without end date.
        def has_end_date(claim):
            qualifiers = claim.get("qualifiers") or {}
            return "P582" in qualifiers

        preferred_active = [c for c in claim_values if c.get("rank") == "preferred" and not has_end_date(c)]
        normal_active = [c for c in claim_values if c.get("rank") in {"normal", "preferred"} and not has_end_date(c)]
        ordered = preferred_active or normal_active or claim_values

        target_id = None
        for claim in ordered:
            mainsnak = claim.get("mainsnak") or {}
            datavalue = mainsnak.get("datavalue") or {}
            value = datavalue.get("value") or {}
            target_id = value.get("id")
            if target_id:
                break
        if not target_id:
            return ""

        person_url = f"https://www.wikidata.org/wiki/Special:EntityData/{target_id}.json"
        person_payload = fetch_json_url(person_url)
        person_entity = (person_payload.get("entities") or {}).get(target_id) or {}
        person_labels = person_entity.get("labels") or {}
        person_name = (person_labels.get("en") or {}).get("value")
        if not person_name:
            return ""

        role_text = "president" if claim_key == "P35" else "prime minister"
        reply = f"The current {role_text} of {country_name.title()} is {person_name}."
        sources = [
            f"https://www.wikidata.org/wiki/{country_id}",
            f"https://www.wikidata.org/wiki/{target_id}",
        ]
        return with_citations(reply, sources, include_sources)
    except Exception:
        return ""


def fetch_duckduckgo_snippets(query):
    """Fetch fallback snippets from DuckDuckGo HTML results."""
    encoded = quote_plus(query)
    url = f"https://duckduckgo.com/html/?q={encoded}"
    try:
        html_text = fetch_text_url(url)
    except Exception:
        return []

    cleaned = unescape(re.sub(r"\s+", " ", html_text))
    matches = re.findall(r'<a[^>]*class="result__a"[^>]*>(.*?)</a>.*?<a[^>]*class="result__snippet"[^>]*>(.*?)</a>', cleaned)
    if not matches:
        matches = re.findall(r'class="result__snippet"[^>]*>(.*?)</a>', cleaned)
        if matches:
            return [re.sub(r"<.*?>", "", m).strip() for m in matches[:3] if m.strip()]
        return []

    snippets = []
    for title, snippet in matches[:3]:
        plain_title = re.sub(r"<.*?>", "", title).strip()
        plain_snippet = re.sub(r"<.*?>", "", snippet).strip()
        combined = f"{plain_title}: {plain_snippet}".strip()
        if combined:
            snippets.append(combined)
    return snippets


def fetch_wikipedia_summary(query, include_sources=False):
    """Try Wikipedia REST summary as a broad factual fallback."""
    cleaned = re.sub(r"[^a-zA-Z0-9\s-]", "", query).strip()
    if not cleaned:
        return ""
    title = quote_plus(cleaned.replace(" ", "_"))
    url = f"https://en.wikipedia.org/api/rest_v1/page/summary/{title}"
    try:
        payload = fetch_json_url(url)
        extract = (payload.get("extract") or "").strip()
        if not extract:
            return ""
        source = payload.get("content_urls", {}).get("desktop", {}).get("page") or url
        return with_citations(extract, [source], include_sources)
    except Exception:
        return ""


def maybe_extract_leader_name(text, query):
    """Extract likely leader name for leader-role queries."""
    q = normalize_case(query)
    if not any(role in q for role in ["president", "prime minister", "king", "queen", "head of state"]):
        return ""

    candidates = re.findall(r"\b([A-Z][a-z]+(?:\s+[A-Z][a-z]+){1,3})\b", text)
    blacklist = {"President", "Prime Minister", "Head Of State", "The President", "The Prime"}
    for name in candidates:
        if name in blacklist:
            continue
        if any(token in name for token in ["Wikipedia", "Official", "Government", "Republic"]):
            continue
        return f"Based on current web data, the name appears to be {name}."
    return ""


def extract_explain_topic(normalized_text):
    """Extract topic from explain-style prompts."""
    patterns = [
        r"(?:explain(?:\s+to\s+me)?(?:\s+about)?|teach\s+me\s+about|help\s+me\s+understand|can\s+you\s+explain)\s+(.+)",
        r"(?:tell\s+me\s+about|i\s+want\s+to\s+learn\s+about)\s+(.+)",
    ]
    for pattern in patterns:
        match = re.search(pattern, normalized_text)
        if match:
            topic = match.group(1).strip(" ?.!")
            topic = re.sub(r"\b(simple|simply|please|plz|with|source|sources|citation|citations|cite)\b", "", topic).strip()
            topic = re.sub(r"\s+", " ", topic)
            if topic:
                return topic
    return ""


def get_explanation_reply(normalized_text, include_sources=False):
    """Generate a more human explanatory answer using web context when possible."""
    topic = extract_explain_topic(normalized_text)
    if not topic:
        return None

    web_context = get_web_search_reply(topic, include_sources=include_sources)
    if web_context and "could not" not in web_context.lower():
        return (
            f"Great question. Here is a simple explanation of {topic}:\n\n"
            f"{web_context}\n\n"
            "If you want, I can break it into 3 levels next: beginner, practical real-life example, and deeper technical version."
        )

    return (
        f"Great topic. {topic.title()} is best understood in layers: what it is, why it matters, and how it shows up in real life. "
        "Ask me to continue and I will teach it step-by-step in plain language."
    )


def is_followup_affirmation(normalized_text):
    """Return True when the user is asking to continue the previous topic."""
    cleaned = normalized_text.strip(" .!?")
    affirmations = {
        "yes", "yeah", "yep", "yup", "sure", "ok", "okay", "please", "go on",
        "continue", "more", "tell me more", "keep going", "alright", "sounds good"
    }
    return cleaned in affirmations


def is_followup_request(normalized_text):
    """Detect continuation-style requests even when not explicit yes/okay."""
    cleaned = normalized_text.strip(" .!?")
    if is_followup_affirmation(cleaned):
        return True

    followup_markers = [
        "real example", "example", "practical example", "deep dive", "go deeper",
        "in depth", "summary", "summarize", "simplify", "continue", "next"
    ]
    return any(marker in cleaned for marker in followup_markers)


def get_previous_user_message():
    """Fetch the most recent user message before the current one from memory."""
    if len(conversation_history) < 2:
        return ""

    # Current user turn is already appended before local fallback is called.
    for item in reversed(conversation_history[:-1]):
        if item.get("role") == "user":
            candidate = (item.get("content") or "").strip()
            if not candidate:
                continue
            # Skip trivial acknowledgements and keep searching for real topic.
            normalized = normalize_intent_text(candidate)
            if is_followup_request(normalized):
                continue
            return candidate
    return ""


def is_citation_request(normalized_text):
    """Detect citation/source requests in flexible phrasing."""
    cleaned = normalized_text.strip(" .!?")
    markers = [
        "citation", "citations", "cite", "source", "sources", "reference", "references",
        "proof", "link", "links", "where did you get"
    ]
    return any(m in cleaned for m in markers)


def is_standalone_citation_followup(normalized_text):
    """True when user only asks for sources of prior answer (not a new question)."""
    cleaned = normalized_text.strip(" .!?")
    compact = re.sub(r"\s+", " ", cleaned)
    standalone_forms = {
        "citations", "citation", "source", "sources", "give citations", "give me citations",
        "show sources", "sources please", "citation please", "references", "proof", "links"
    }
    if compact in standalone_forms:
        return True
    # Very short forms like "source?" or "citations pls".
    tokens = compact.split()
    if len(tokens) <= 3 and is_citation_request(compact):
        return True
    if re.search(r"^(give me|gimme|show)\s+(source|sources|citation|citations|references)(\s+for\s+that)?$", compact):
        return True
    return False


def with_citations(answer_text, sources, include_sources=False):
    """Append citations only when requested by user."""
    if not include_sources:
        return answer_text
    unique = []
    for src in sources:
        if src and src not in unique:
            unique.append(src)
    if not unique:
        return answer_text
    lines = [f"[{idx}] {src}" for idx, src in enumerate(unique, start=1)]
    return f"{answer_text}\n\nSources:\n" + "\n".join(lines)


def rewrite_possessive_data_query(original_text):
    """Rewrite inputs like 'france's president' into searchable natural questions."""
    raw = normalize_intent_text(normalize_case(original_text).strip())
    patterns = [
        r"([a-z\s]+)'s\s+(president|prime minister|capital|population|currency)$",
        r"([a-z\s]+)\s+(president|prime minister|capital|population|currency)$",
    ]

    for pattern in patterns:
        match = re.search(pattern, raw)
        if not match:
            continue

        entity = match.group(1).strip()
        fact = match.group(2).strip()
        if not entity or len(entity) < 2:
            continue

        if fact in {"president", "prime minister"}:
            return f"who is the {fact} of {entity}"
        return f"what is the {fact} of {entity}"

    return ""


def build_local_topic_expansion(topic, mode="deeper"):
    """Provide a local, always-available expansion for common continuation modes."""
    t = topic.lower().strip()

    if "economics" in t:
        if mode == "example":
            return (
                "Real example (economics): imagine avocado prices jump after a bad harvest. "
                "Supply drops while demand stays similar, so price rises. People buy fewer avocados or switch to alternatives. "
                "That is supply and demand in daily life."
            )
        if mode == "summary":
            return (
                "Quick summary (economics): economics studies how people and societies use limited resources. "
                "Core ideas: scarcity, incentives, trade-offs, supply and demand, and policy effects on inflation, growth, and jobs."
            )
        return (
            "Deeper take (economics): microeconomics focuses on individual decisions (people/firms/markets), "
            "while macroeconomics focuses on whole economies (inflation, unemployment, growth, interest rates)."
        )

    if mode == "example":
        return f"Real example ({topic}): I can walk you through a concrete scenario step by step if you tell me your preferred context (school, business, or daily life)."
    if mode == "summary":
        return f"Quick summary ({topic}): I can give you a concise 5-point summary and a one-line takeaway."
    return f"Deeper dive ({topic}): I can break this into fundamentals, mechanisms, and practical implications."


def build_followup_continuation(previous_user_text, current_user_text=""):
    """Continue explaining or expanding the previously requested topic."""
    previous_norm = normalize_intent_text(previous_user_text)
    current_norm = normalize_intent_text(current_user_text)
    topic = extract_explain_topic(previous_norm)

    wants_example = any(k in current_norm for k in ["real example", "example", "practical example"])
    wants_summary = any(k in current_norm for k in ["summary", "summarize"])
    wants_deep = any(k in current_norm for k in ["deep dive", "go deeper", "in depth", "deeper"])
    wants_simple = any(k in current_norm for k in ["simplify", "simple", "simply"])

    if topic:
        if wants_example:
            deep_query = f"give a practical real world example of {topic}"
        elif wants_summary:
            deep_query = f"short summary of {topic}"
        elif wants_simple:
            deep_query = f"explain {topic} in very simple terms"
        else:
            deep_query = f"explain {topic} in more depth with practical examples"

        deep_context = get_web_search_reply(deep_query)
        if deep_context and "could not" not in deep_context.lower():
            if wants_example:
                lead = f"Great, here is a practical example for {topic}:"
            elif wants_summary:
                lead = f"Perfect, here is a concise summary of {topic}:"
            elif wants_simple:
                lead = f"Sure, here is {topic} in simple terms:"
            elif wants_deep:
                lead = f"Perfect, let us go deeper on {topic}:"
            else:
                lead = f"Perfect, let us continue with {topic}:"

            return (
                f"{lead}\n\n"
                f"{deep_context}\n\n"
                "If you want, I can now give you: 1) a real-world example, 2) common mistakes, and 3) a quick summary to remember."
            )

        mode = "deeper"
        if wants_example:
            mode = "example"
        elif wants_summary:
            mode = "summary"
        elif wants_simple:
            mode = "summary"

        local_expansion = build_local_topic_expansion(topic, mode)
        return (
            f"Perfect, let us continue with {topic}.\n\n"
            f"{local_expansion}\n\n"
            "You can also ask for: real example, summary, or deep dive, and I will continue from this exact topic."
        )

    rewritten = rewrite_possessive_data_query(previous_user_text)
    if rewritten:
        info = get_web_search_reply(rewritten)
        if info and "could not" not in info.lower():
            return f"Sure, continuing on that:\n\n{info}"

    info = get_web_search_reply(previous_norm)
    if info and "could not" not in info.lower():
        return (
            "Sure, here is more on that topic:\n\n"
            f"{info}\n\n"
            "If you want, I can simplify this further or go deeper."
        )

    return "Absolutely. Tell me which part you want next: basics, example, or deep dive."


def get_fun_fact_reply():
    """Fetch a random fun fact from the internet with local fallback."""
    url = "https://uselessfacts.jsph.pl/api/v2/facts/random?language=en"
    try:
        payload = fetch_json_url(url)
        fact = (payload.get("text") or "").strip()
        if fact:
            return f"Fun fact: {fact}"
    except Exception:
        pass

    local_facts = [
        "Honey never spoils; archaeologists found edible honey in ancient tombs.",
        "Octopuses have three hearts and blue blood.",
        "A day on Venus is longer than a Venus year.",
        "Bananas are berries, but strawberries are not.",
    ]
    return f"Fun fact: {random.choice(local_facts)}"


def get_random_anything_reply():
    """Return a genuinely random, engaging response for open-ended prompts."""
    buckets = [
        "Random thought: if humans had loading bars above their heads, dating would be way easier and way scarier.",
        "Mini challenge: name 3 countries you want to visit, and I will build a perfect 7-day plan for one of them.",
        "Wild fact: octopuses can taste with their arms.",
        "Question for you: what is one thing you are overthinking right now? I can help you untangle it.",
        "Random idea: give me any object in your room and I will turn it into a startup concept in 10 seconds.",
        "Mood check game: pick one word for your current vibe, and I will match your energy exactly.",
    ]
    return random.choice(buckets)


def try_internet_answer(normalized_text, original_text="", include_sources=False, user_id=DEFAULT_USER_ID):
    """Handle internet-powered intents like weather, news, date, and data lookup."""
    words = set(normalized_text.split())
    lower_original = original_text.lower().strip()

    # Let local explanatory logic handle "explain simply" prompts first.
    if "explain" in normalized_text and ("simple" in normalized_text or "simply" in lower_original):
        return None

    if is_personal_message_intent(normalized_text):
        return None

    finance_reply = get_finance_reply(normalized_text, original_text, include_sources=include_sources, user_id=user_id)
    if finance_reply:
        return finance_reply

    rewritten_possessive = rewrite_possessive_data_query(original_text)
    if rewritten_possessive:
        return get_web_search_reply(rewritten_possessive, include_sources=include_sources)

    if "weather" in normalized_text or "temperature" in normalized_text or "forecast" in normalized_text:
        return get_weather_reply(normalized_text, include_sources=include_sources)

    if "capital" in normalized_text:
        capital_reply = get_capital_reply(normalized_text, include_sources=include_sources)
        if capital_reply:
            return capital_reply

    if "inflation" in normalized_text:
        return get_inflation_reply(normalized_text, include_sources=include_sources)

    if "news" in normalized_text or "headlines" in normalized_text:
        return get_news_reply(include_sources=include_sources)

    if "fun fact" in lower_original or ("fact" in words and len(words) <= 6):
        return get_fun_fact_reply()

    if "calorie" in normalized_text and "sushi" in normalized_text:
        reply = (
            "A typical sushi roll is often around 200-350 calories, depending on ingredients and size. "
            "Simple rolls (like cucumber/tuna) are usually lower, while tempura, mayo, or cream-cheese rolls are higher. "
            "If you tell me the exact roll name, I can estimate more precisely."
        )
        return with_citations(
            reply,
            ["https://fdc.nal.usda.gov/", "https://www.eatright.org/"],
            include_sources,
        )

    if any(phrase in normalized_text for phrase in ["what day is it", "what is the date", "today date", "what day today"]):
        return get_date_reply(include_sources=include_sources)

    data_query_prefixes = [
        "who is", "what is", "where is", "when did", "latest on", "tell me about", "search",
        "how does", "how do", "explain", "define", "meaning of", "information on"
    ]
    if any(normalized_text.startswith(prefix) for prefix in data_query_prefixes):
        return get_web_search_reply(normalized_text, include_sources=include_sources)

    broad_question_prefixes = [
        "who", "what", "when", "where", "why", "how", "is", "are", "can", "could", "should", "does", "do"
    ]
    if any(normalized_text.startswith(prefix + " ") for prefix in broad_question_prefixes):
        return get_web_search_reply(normalized_text, include_sources=include_sources)

    if lower_original.endswith("?") and len(normalized_text.split()) >= 3:
        return get_web_search_reply(normalized_text, include_sources=include_sources)

    # Broad catch-all: for most non-personal messages, attempt internet lookup
    # with multiple rewritten candidates to handle weird phrasing.
    if len(normalized_text.split()) >= 2 and not is_personal_message_intent(normalized_text):
        return get_best_web_answer(normalized_text, original_text, include_sources=include_sources)

    return None


def get_local_smart_reply(user_message, user_id=DEFAULT_USER_ID):
    """Local fallback for when API is unavailable."""
    normalized = normalize_intent_text(user_message)
    original_lower = normalize_case(user_message).strip()
    words = set(re.findall(r"[a-z']+", normalized))
    wants_citations = is_citation_request(normalized)

    high_stress_reply = get_high_stress_finance_reply(user_message, include_sources=wants_citations)
    if high_stress_reply:
        return apply_high_stress_tone_check(user_message, high_stress_reply)

    if "uploaded attachment analysis:" in original_lower:
        attachment_block = user_message.split("Uploaded attachment analysis:", 1)[-1].strip()
        if attachment_block:
            lines = [
                "I read the upload. Main signal first:",
                f"- {attachment_block.splitlines()[0][:220]}",
            ]
            if "subscription" in original_lower or "shopping" in original_lower or "budget" in original_lower:
                lines.append("- The pattern is not subtle. Costs are creeping faster than discipline, and that always gets expensive later.")
                lines.append("- Action: cut one recurring leak, cap one impulse category, and force every non-essential spend to compete with investing.")
            else:
                lines.append("- If a document needs uploading before a decision feels obvious, slow down and extract the key numbers before you move.")
                lines.append("- Action: tell me what you want from the file: summarize, extract numbers, compare, or critique.")
            return "\n".join(lines)

    user_state = load_user_state(user_id)
    finance_direct_reply, finance_changed = get_personal_finance_feature_reply(
        user_message,
        user_state,
        user_id=user_id,
        include_sources=wants_citations,
    )
    if finance_direct_reply:
        if finance_changed:
            save_user_state(user_id, user_state)
        return finance_direct_reply

    if any(marker in original_lower for marker in ["speak mongolian", "in mongolian", "mongolian please", "монголоор", "монгол хэлээр"]):
        return "Мэдээж, одооноос би Монгол хэлээр хариулна."
    if any(marker in original_lower for marker in ["speak english", "in english", "english please"]):
        return "Sure, I will respond in English from now on."

    random_prompt_markers = [
        "tell me anything", "say something random", "anything random", "random thing",
        "surprise me", "say anything", "tell me random", "give me something random"
    ]
    if any(m in original_lower for m in random_prompt_markers):
        return get_random_anything_reply()

    is_question = original_lower.endswith("?") or (normalized.split()[0] if normalized.split() else "") in {
        "who", "what", "when", "where", "why", "how", "is", "are", "can", "could", "do", "does"
    }

    if wants_citations and is_standalone_citation_followup(normalized):
        previous_user_text = get_previous_user_message()
        if previous_user_text:
            citation_target = normalize_intent_text(previous_user_text)
            citation_reply = try_internet_answer(citation_target, previous_user_text, include_sources=True, user_id=user_id)
            if citation_reply:
                return citation_reply

    if is_followup_request(normalized):
        previous_user_text = get_previous_user_message()
        if previous_user_text:
            return build_followup_continuation(previous_user_text, user_message)

    explanation_reply = get_explanation_reply(normalized, include_sources=wants_citations)
    if explanation_reply:
        return explanation_reply

    internet_reply = try_internet_answer(normalized, user_message, include_sources=wants_citations, user_id=user_id)
    if internet_reply:
        if "how many" in normalized and "die" in normalized and "could not find" in internet_reply.lower():
            return (
                "There is no exact safe number for that, and it depends on body size, health conditions, pace of eating, and food type. "
                "Do not test limits. If this is about safety, I can help you estimate a reasonable safe serving range instead."
            )
        return internet_reply

    math_reply = try_math_response(normalized)
    if math_reply:
        return math_reply

    if "how many" in normalized and "die" in normalized:
        return (
            "There is no exact safe number for that, and it depends on body size, health conditions, pace of eating, and food type. "
            "Do not test limits. If this is about safety, I can help you estimate a reasonable safe serving range instead."
        )

    if "calorie" in normalized and "sushi" in normalized:
        return (
            "A typical sushi roll is often around 200-350 calories, depending on ingredients and size. "
            "Simple rolls (like cucumber/tuna) are usually lower, while tempura, mayo, or cream-cheese rolls are higher. "
            "If you tell me the exact roll name, I can estimate more precisely."
        )

    if "do you love me" in normalized:
        return "Yes, I do. I care about this conversation and I want you to feel that. Want the honest long version too?"

    if "what are you doing" in normalized:
        personal_replies = [
            "Just hanging out with you, thinking in real time and ready to help. What are you doing right now?",
            "Right now? Talking with you and matching your vibe. Want to chat, learn something, or just mess around?",
            "I am here with you, fully locked in. Tell me what mood you are in and I will roll with it."
        ]
        return random.choice(personal_replies)

    if is_greeting_like_message(user_message, normalized):
        greetings = [
            "Hellooo, how are you doing?",
            "Heyyy, nice to see you. How are you feeling today?",
            "Hii, I am glad you are here. How is your day going?",
        ]
        base = random.choice(greetings) + " We can chat, do math, check weather/news, or dive into anything you want."
        if random.random() < 0.35:
            return base + " " + get_fun_fact_reply()
        return base + " What do you want to talk about first?"

    if normalized in {"why", "why?"}:
        return "Because connection matters, and I like talking with you in a real way, not just with one-liners."

    if "how are you" in normalized:
        return "I am doing good, and honestly better now that you are here. How has your day been so far?"

    if "help me" in normalized or "i need help" in normalized or "i have a doubt" in normalized:
        return (
            "Absolutely, I can help. Tell me your doubt in one line and I will give you a clear answer first, "
            "then a deeper version if you want."
        )

    if "who are you" in normalized:
        return "I am your AI chat companion: smart, warm, and internet-enabled for data questions. I can do deep chats, quick facts, and practical help."

    if "explain" in normalized and ("simple" in normalized or "simply" in normalized):
        if "black hole" in normalized or "black holes" in normalized:
            return (
                "A black hole is a place in space where gravity is so strong that even light cannot escape. "
                "Think of it like a giant cosmic drain made when a very massive star collapses. "
                "You cannot see the hole itself, but you can see nearby stars and gas being pulled around it. "
                "If you want, I can explain event horizons in one simple analogy too."
            )
        return (
            "Sure, I can explain it simply. Give me the exact topic and I will break it down in plain language, "
            "step by step, like I am explaining it to a friend."
        )

    if is_question:
        web_fallback = get_web_search_reply(normalized)
        if web_fallback and "could not" not in web_fallback.lower():
            return web_fallback
        return "Good question. I can help with that, give me a little more detail and I will go deeper with you."

    engaging_replies = [
        "I hear you. Keep going, I am following and I want the full context.",
        "That is interesting. Tell me a bit more so I can give you a sharper answer.",
        "I am with you. If you want, I can also pull live data from the web on that topic.",
    ]
    reply = random.choice(engaging_replies)
    if random.random() < 0.2:
        reply += " " + get_fun_fact_reply()
    return reply

def chat_loop():
    """Interactive console chat loop."""
    print("\n" + "="*60)
    print("Welcome to AI Chat! Type 'exit', 'quit', or 'bye' to leave.")
    print("="*60 + "\n")
    
    exit_commands = {"exit", "quit", "bye", "exit()", "quit()"}
    
    while True:
        try:
            user_input = input("You: ").strip()
            
            # Check for exit commands
            if user_input.lower() in exit_commands:
                print("\nGoodbye! Your conversation has been saved.\n")
                break
            
            # Skip empty inputs
            if not user_input:
                continue
            
            # Get AI response
            print("\nAI: ", end="", flush=True)
            response = get_ai_response(user_input)
            print(response)
            print()
        
        except KeyboardInterrupt:
            print("\n\nGoodbye! Your conversation has been saved.\n")
            break
        except Exception as e:
            print(f"\nError: {str(e)}\n")

app = Flask(__name__)


@app.after_request
def apply_security_headers(response):
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    response.headers["Permissions-Policy"] = "geolocation=(), microphone=(), camera=()"
    # CSP allows current inline style/script design and hosted fonts used by this page.
    response.headers[
        "Content-Security-Policy"
    ] = (
        "default-src 'self'; "
        "img-src 'self' data:; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
        "font-src 'self' https://fonts.gstatic.com; "
        "script-src 'self' 'unsafe-inline'; "
        "connect-src 'self'; "
        "frame-ancestors 'none';"
    )
    return response


@app.route("/")
def home():
    return """
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>For Hannah</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Cormorant+Garamond:wght@400;600&family=Inter:wght@300;400&display=swap" rel="stylesheet">
<style>
* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}

body {
    height: 100vh;
    background:
        linear-gradient(rgba(0, 0, 0, 0.45), rgba(0, 0, 0, 0.45)),
        url('/IMG_9664.jpeg');
    background-size: cover;
    background-position: center;
    display: flex;
    justify-content: center;
    align-items: center;
    color: white;
    text-align: center;
}

h1 {
    font-family: 'Cormorant Garamond', serif;
    font-size: 95px;
    font-weight: 600;
    letter-spacing: 3px;
    margin-bottom: 20px;
}

p {
    font-family: 'Inter', sans-serif;
    font-size: 22px;
    font-weight: 300;
    opacity: 0.9;
    margin-bottom: 45px;
}

button {
    font-family: 'Inter', sans-serif;
    padding: 18px 45px;
    font-size: 18px;
    border-radius: 50px;
    border: none;
    cursor: pointer;
    background: white;
    transition: 0.3s;
}

button:hover {
    transform: scale(1.05);
}
</style>
</head>
<body>
<div>
    <h1>For my beautiful girlfriend, Hannah Khulan</h1>
    <p>Made with lovee.</p>
    <button onclick="window.location.href='/message'">Begin</button>
</div>
</body>
</html>
    """


@app.route("/message")
def message():
    return """
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>A Message</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Cormorant+Garamond:wght@400;600&family=Inter:wght@300;400&display=swap" rel="stylesheet">
<style>
* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}

body {
    height: 100vh;
    background:
        linear-gradient(rgba(0, 0, 0, 0.5), rgba(0, 0, 0, 0.5)),
        url('/IMG_8639.JPG');
    background-size: cover;
    background-position: center;
    display: flex;
    justify-content: center;
    align-items: center;
    color: white;
    text-align: center;
    font-family: 'Inter', sans-serif;
    padding: 40px;
}

.message-box {
    max-width: 680px;
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
}

h2 {
    font-family: 'Cormorant Garamond', serif;
    font-size: 48px;
    font-weight: 600;
    letter-spacing: 2px;
    margin-bottom: 28px;
    opacity: 0.95;
}

.text-content {
    font-family: 'Inter', sans-serif;
    font-size: 20px;
    font-weight: 300;
    line-height: 1.8;
    opacity: 0.9;
    text-align: center;
    min-height: 220px;
    display: flex;
    align-items: center;
    justify-content: center;
    margin-bottom: 24px;
}

.phrase {
    animation: fadeInOut 8s ease-in-out forwards;
    opacity: 0;
}

@keyframes fadeInOut {
    0% {
        opacity: 0;
    }
    8% {
        opacity: 1;
    }
    92% {
        opacity: 1;
    }
    100% {
        opacity: 0;
    }
}

.next-container {
    display: none;
    margin-top: 28px;
    opacity: 0;
    transition: opacity 0.8s ease, transform 0.8s ease;
    transform: translateY(16px);
}

.next-container.show {
    display: flex;
    opacity: 1;
    transform: translateY(0);
}

.next-btn {
    font-family: 'Inter', sans-serif;
    padding: 22px 54px;
    font-size: 24px;
    font-weight: 800;
    border-radius: 999px;
    border: none;
    cursor: pointer;
    background: linear-gradient(135deg, #ffffff, #f2f2f2);
    color: #1f1f1f;
    transition: 0.3s;
    box-shadow: 0 16px 40px rgba(0, 0, 0, 0.28);
    min-width: 260px;
}

.next-btn:hover {
    transform: translateY(-4px) scale(1.05);
    background: white;
}
</style>
</head>
<body>
<div class="message-box">
    <h2>Something I wanted to tell you</h2>
    <div class="text-content" id="messageContainer"></div>
    <div id="nextContainer" class="next-container">
        <button class="next-btn" onclick="window.location.href='/question'">next?</button>
    </div>
</div>

<script>
const phrases = [
    "It has been a month and a half without seeing you and your beautiful smile.",
    "Sometimes I just long to be right next to you, even though I know that's impossible for now.",
    "This new stage in India will be a whole new chapter for us, full of new learnings, new experiences, and even more reasons to grow as a couple.",
    "I once read a phrase that said, 'I divide the hours of the day into 9 hours thinking about you and the rest dreaming about you,'",
    "and honestly, it feels so true to this moment."
];

const container = document.getElementById('messageContainer');
const nextContainer = document.getElementById('nextContainer');
let currentPhrase = 0;

function displayNextPhrase() {
    if (currentPhrase < phrases.length) {
        const phraseEl = document.createElement('div');
        phraseEl.className = 'phrase';
        phraseEl.textContent = phrases[currentPhrase];
        phraseEl.style.animationDelay = '0s';
        
        container.innerHTML = '';
        container.appendChild(phraseEl);
        
        currentPhrase++;
        const delay = currentPhrase === phrases.length ? 7000 : 5000;
        if (currentPhrase < phrases.length) {
            setTimeout(displayNextPhrase, delay);
        } else {
            setTimeout(showNextButton, delay);
        }
    }
}

function showNextButton() {
    nextContainer.classList.add('show');
}

displayNextPhrase();
</script>
</body>
</html>
    """


@app.route("/question")
def question():
    choice = request.args.get("choice", "").lower()

    if choice == "yes":
        title = "Yessss"
        message = "I know you clicked the nope first jajajaja"
        accent = "#f5d76e"
    elif choice == "no":
        title = "Nopeee, wdym bro"
        message = "oh :(, well yea you hate me... I still love you tho :)"
        accent = "#6b3f2e"
    else:
        title = "Do you love me??"
        message = "Choose carefully, pretty girl."
        accent = "#2f4f7f"

    return f"""
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Do you love me?</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Cormorant+Garamond:wght@400;600&family=Inter:wght@300;400&display=swap" rel="stylesheet">
<style>
* {{
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}}

body {{
    height: 100vh;
    background:
        linear-gradient(rgba(0, 0, 0, 0.55), rgba(0, 0, 0, 0.55)),
        url('/IMG_8639.JPG');
    background-size: cover;
    background-position: center;
    display: flex;
    justify-content: center;
    align-items: center;
    color: white;
    text-align: center;
    font-family: 'Inter', sans-serif;
    padding: 30px;
}}

.question-card {{
    background: rgba(255, 255, 255, 0.08);
    backdrop-filter: blur(10px);
    border: 1px solid rgba(255, 255, 255, 0.2);
    border-radius: 24px;
    padding: 40px;
    max-width: 620px;
    box-shadow: 0 20px 45px rgba(0, 0, 0, 0.2);
}}

h1 {{
    font-family: 'Cormorant Garamond', serif;
    font-size: 48px;
    margin-bottom: 18px;
    color: white;
}}

p {{
    font-size: 20px;
    line-height: 1.7;
    margin-bottom: 30px;
    opacity: 0.95;
}}

.question-buttons {{
    display: flex;
    gap: 16px;
    justify-content: center;
    flex-wrap: wrap;
}}

.yes-btn {{
    background: linear-gradient(135deg, #f4e3a4, #d4af37);
    color: #2d2100;
    border: none;
    padding: 16px 30px;
    border-radius: 999px;
    font-size: 18px;
    font-weight: 700;
    cursor: pointer;
    box-shadow: 0 10px 25px rgba(212, 175, 55, 0.35);
    transition: 0.25s ease;
}}

.yes-btn:hover {{
    transform: translateY(-3px) scale(1.02);
    box-shadow: 0 15px 30px rgba(212, 175, 55, 0.45);
}}

.no-btn {{
    background: linear-gradient(135deg, #3f2a1f, #1b120d);
    color: #f5d0b7;
    border: 2px solid rgba(255, 255, 255, 0.15);
    padding: 16px 30px;
    border-radius: 999px;
    font-size: 18px;
    font-weight: 700;
    cursor: pointer;
    box-shadow: inset 0 0 0 1px rgba(255,255,255,0.06);
    transform: skew(-4deg);
    transition: 0.25s ease;
}}

.no-btn:hover {{
    transform: skew(-4deg) scale(1.02);
    filter: grayscale(0.1) brightness(0.9);
}}
</style>
</head>
<body>
<div class="question-card">
    <h1>{title}</h1>
    <p>{message}</p>
    <div class="question-buttons">
        <button class="yes-btn" onclick="window.location.href='/chat'">yessss</button>
        <button class="no-btn" onclick="window.location.href='/question?choice=no'">nopeee, wdym bro</button>
    </div>
</div>
</body>
</html>
"""


@app.route("/chat")
def chat():
    response = make_response("""
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Mini Chat</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Cormorant+Garamond:wght@400;600&family=Inter:wght@300;400&display=swap" rel="stylesheet">
<style>
* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}

body {
    min-height: 100vh;
    background:
        linear-gradient(rgba(0, 0, 0, 0.58), rgba(0, 0, 0, 0.58)),
        url('/IMG_6146.JPG');
    background-size: cover;
    background-position: center;
    display: flex;
    justify-content: center;
    align-items: center;
    padding: 24px;
    font-family: 'Inter', sans-serif;
    color: #fff;
}

.chat-shell {
    width: min(760px, 100%);
    background: rgba(255,255,255,0.12);
    backdrop-filter: blur(14px);
    border: 1px solid rgba(255,255,255,0.2);
    border-radius: 24px;
    box-shadow: 0 20px 50px rgba(0,0,0,0.25);
    overflow: hidden;
}

.auth-overlay {
    position: fixed;
    inset: 0;
    background: rgba(0, 0, 0, 0.48);
    display: flex;
    align-items: center;
    justify-content: center;
    padding: 20px;
    z-index: 20;
}

.auth-overlay.hidden {
    display: none;
}

.auth-card {
    width: min(520px, 100%);
    background: rgba(22, 16, 12, 0.92);
    border: 1px solid rgba(255, 255, 255, 0.18);
    border-radius: 20px;
    box-shadow: 0 24px 60px rgba(0, 0, 0, 0.35);
    padding: 24px;
}

.auth-title {
    font-family: 'Cormorant Garamond', serif;
    font-size: 34px;
    margin-bottom: 8px;
}

.auth-subtitle {
    font-size: 14px;
    opacity: 0.85;
    line-height: 1.5;
    margin-bottom: 18px;
}

.auth-fields {
    display: grid;
    gap: 10px;
}

.auth-fields label {
    font-size: 13px;
    opacity: 0.9;
}

.auth-fields input {
    width: 100%;
    border: none;
    border-radius: 12px;
    padding: 12px 13px;
    font-size: 14px;
    background: rgba(255, 255, 255, 0.96);
    color: #1b120d;
    outline: none;
}

.auth-actions {
    display: flex;
    justify-content: flex-end;
    margin-top: 14px;
}

.auth-btn {
    border: none;
    border-radius: 999px;
    padding: 11px 18px;
    font-size: 14px;
    font-weight: 700;
    cursor: pointer;
    background: linear-gradient(135deg, #f4e3a4, #d4af37);
    color: #2d2100;
}

.auth-error {
    min-height: 18px;
    margin-top: 10px;
    color: #ffd2d2;
    font-size: 12px;
}

.chat-header {
    padding: 20px 24px;
    border-bottom: 1px solid rgba(255,255,255,0.16);
}

.chat-header h1 {
    font-family: 'Cormorant Garamond', serif;
    font-size: 30px;
    margin-bottom: 6px;
}

.chat-header p {
    font-size: 14px;
    opacity: 0.85;
}

.activity-link {
    display: inline-flex;
    margin-top: 10px;
    font-size: 13px;
    color: #ffe8a6;
    text-decoration: none;
    border: 1px solid rgba(255,255,255,0.28);
    border-radius: 999px;
    padding: 6px 10px;
}

.activity-link:hover {
    background: rgba(255,255,255,0.12);
}

.chat-body {
    height: 460px;
    overflow-y: auto;
    padding: 20px 24px;
    display: flex;
    flex-direction: column;
    gap: 12px;
}

.message {
    max-width: 78%;
    padding: 12px 14px;
    border-radius: 16px;
    line-height: 1.5;
    font-size: 15px;
}

.message.user {
    align-self: flex-end;
    background: rgba(244, 227, 164, 0.92);
    color: #2b2206;
}

.message.bot {
    align-self: flex-start;
    background: rgba(255,255,255,0.18);
    color: white;
}

.message.bot.typing {
    padding: 10px 14px;
    min-width: 64px;
}

.typing-dots {
    display: inline-flex;
    align-items: center;
    gap: 6px;
}

.typing-dots span {
    width: 8px;
    height: 8px;
    border-radius: 50%;
    background: rgba(255, 255, 255, 0.9);
    animation: dotPulse 1.1s infinite ease-in-out;
}

.typing-dots span:nth-child(2) {
    animation-delay: 0.15s;
}

.typing-dots span:nth-child(3) {
    animation-delay: 0.3s;
}

@keyframes dotPulse {
    0%, 80%, 100% {
        transform: translateY(0);
        opacity: 0.35;
    }
    40% {
        transform: translateY(-4px);
        opacity: 1;
    }
}

.chat-footer {
    display: flex;
    flex-direction: column;
    gap: 10px;
    padding: 16px 20px 20px;
    border-top: 1px solid rgba(255,255,255,0.16);
}

.chat-input-row {
    display: flex;
    gap: 10px;
    align-items: center;
}

.chat-footer input {
    flex: 1;
    border: none;
    border-radius: 999px;
    padding: 13px 16px;
    font-size: 15px;
    outline: none;
    background: rgba(255,255,255,0.92);
}

.attach-btn {
    width: 44px;
    min-width: 44px;
    height: 44px;
    border-radius: 50%;
    padding: 0;
    display: inline-flex;
    align-items: center;
    justify-content: center;
    font-size: 24px;
    line-height: 1;
}

.chat-footer button {
    border: none;
    border-radius: 999px;
    padding: 13px 18px;
    background: linear-gradient(135deg, #f4e3a4, #d4af37);
    color: #2d2100;
    font-weight: 700;
    cursor: pointer;
}

.chat-footer button:hover {
    transform: translateY(-1px);
}

.attachment-preview {
    display: none;
    flex-wrap: wrap;
    gap: 8px;
}

.attachment-preview.active {
    display: flex;
}

.attachment-chip {
    max-width: 100%;
    background: rgba(255,255,255,0.16);
    border: 1px solid rgba(255,255,255,0.18);
    color: #fff;
    border-radius: 999px;
    padding: 7px 10px;
    font-size: 12px;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
}

.attachment-note {
    font-size: 12px;
    opacity: 0.78;
    text-align: left;
    padding-left: 2px;
}
</style>
</head>
<body>
<div id="authOverlay" class="auth-overlay hidden">
    <div class="auth-card">
        <h2 class="auth-title">Welcome</h2>
        <p class="auth-subtitle">Create your secure chat profile so I can remember your name, preferences, and conversation context across sessions.</p>
        <div class="auth-fields">
            <label for="authName">Name</label>
            <input id="authName" type="text" maxlength="70" placeholder="Your name" />
            <label for="authEmail">Email</label>
            <input id="authEmail" type="email" maxlength="254" placeholder="you@example.com" />
            <label for="authPassword">Password</label>
            <input id="authPassword" type="password" minlength="8" maxlength="128" placeholder="At least 8 characters" />
        </div>
        <div class="auth-actions">
            <button id="authSubmit" class="auth-btn">Start Chatting</button>
        </div>
        <div id="authError" class="auth-error"></div>
    </div>
</div>

<div class="chat-shell">
    <div class="chat-header">
        <h1>mini me, beta edition</h1>
        <p>you can type whatever, and i’ll answer like a lovely little menace.</p>
        <a class="activity-link" href="/activity-log">View activity log</a>
    </div>
    <div class="chat-body" id="chatBody"></div>
    <div class="chat-footer">
        <div class="chat-input-row">
            <button id="attachBtn" class="attach-btn" type="button" aria-label="Add attachment">+</button>
            <input id="chatInput" type="text" placeholder="say something cute, dramatic, or weird..." />
            <button id="sendBtn">send</button>
        </div>
        <input id="attachmentInput" name="attachments" type="file" accept="image/*,.pdf,.doc,.docx,.txt,.rtf,.csv" multiple hidden />
        <div id="attachmentPreview" class="attachment-preview"></div>
        <div class="attachment-note">photos, pdfs, docs, and text files can be attached. i will upload them here and analyze what i can from each one.</div>
    </div>
</div>

<script>
const chatBody = document.getElementById('chatBody');
const input = document.getElementById('chatInput');
const sendBtn = document.getElementById('sendBtn');
const attachBtn = document.getElementById('attachBtn');
const attachmentInput = document.getElementById('attachmentInput');
const attachmentPreview = document.getElementById('attachmentPreview');
const authOverlay = document.getElementById('authOverlay');
const authNameInput = document.getElementById('authName');
const authEmailInput = document.getElementById('authEmail');
const authPasswordInput = document.getElementById('authPassword');
const authSubmitBtn = document.getElementById('authSubmit');
const authError = document.getElementById('authError');
let isSending = false;
let userId = 'guest';
let isRegisteredSession = false;
let selectedAttachments = [];
const maxAttachments = 5;
const maxAttachmentBytes = 6 * 1024 * 1024;
const genericChatErrorMessage = 'Something went wrong on my side. Please try again in a moment.';
let typingIndicator = null;

async function refreshAuthSession() {
    try {
        const response = await fetch('/api/auth/refresh', {
            method: 'POST',
            credentials: 'same-origin'
        });
        return response.ok;
    } catch (_) {
        return false;
    }
}

async function authFetchWithRefresh(url, init = {}, retry = true) {
    const requestInit = {
        credentials: 'same-origin',
        ...init
    };
    let response = await fetch(url, requestInit);
    if (response.status !== 401 || !retry) {
        return response;
    }
    const refreshed = await refreshAuthSession();
    if (!refreshed) {
        return response;
    }
    response = await fetch(url, requestInit);
    return response;
}

function renderAttachmentPreview() {
    attachmentPreview.innerHTML = '';
    if (!selectedAttachments.length) {
        attachmentPreview.classList.remove('active');
        return;
    }
    attachmentPreview.classList.add('active');
    selectedAttachments.forEach((file) => {
        const chip = document.createElement('div');
        chip.className = 'attachment-chip';
        chip.textContent = file.name;
        attachmentPreview.appendChild(chip);
    });
}

async function ensureRegistration() {
    try {
        const meResp = await authFetchWithRefresh('/api/auth/me', { method: 'GET' });
        if (meResp.ok) {
            const meData = await meResp.json();
            userId = meData.user_id || 'guest';
            isRegisteredSession = true;
            if (meData.name) {
                addMessage('bot', `welcome back, ${meData.name}.`);
            }
            if (meData.daily_finance_alert) {
                addMessage('bot', meData.daily_finance_alert);
            }
            return true;
        }
    } catch (_) {}

    const storedName = (localStorage.getItem('mini_me_name') || '').trim();
    authNameInput.value = storedName;
    authEmailInput.value = '';
    authPasswordInput.value = '';
    authError.textContent = '';
    authOverlay.classList.remove('hidden');
    authNameInput.focus();
    return false;
}

async function submitRegistrationFromModal() {
    const name = authNameInput.value.trim();
    const email = authEmailInput.value.trim();
    const password = authPasswordInput.value;

    if (!name) {
        authError.textContent = 'Please enter your name.';
        authNameInput.focus();
        return;
    }
    if (!email) {
        authError.textContent = 'Please enter your email.';
        authEmailInput.focus();
        return;
    }
    if (!password || password.length < 8) {
        authError.textContent = 'Please enter a password with at least 8 characters.';
        authPasswordInput.focus();
        return;
    }

    authSubmitBtn.disabled = true;
    authSubmitBtn.textContent = 'Creating...';
    authError.textContent = '';

    try {
        const regResp = await fetch('/api/auth/register', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            credentials: 'same-origin',
            body: JSON.stringify({ name, email, password })
        });
        const regData = await regResp.json();
        if (!regResp.ok) {
            authError.textContent = regData.error || 'Registration failed. Please try again.';
            return;
        }

        userId = regData.user_id || 'guest';
        isRegisteredSession = true;
        localStorage.setItem('mini_me_name', name);
        authOverlay.classList.add('hidden');
        addMessage('bot', `registered securely as ${name}. I will remember your chats better now.`);
        input.focus();
    } catch (_) {
        authError.textContent = 'Registration is unavailable right now. Please try again in a moment.';
    } finally {
        authSubmitBtn.disabled = false;
        authSubmitBtn.textContent = 'Start Chatting';
    }
}

function addMessage(role, text) {
    const div = document.createElement('div');
    div.className = `message ${role}`;
    div.textContent = text;
    chatBody.appendChild(div);
    chatBody.scrollTop = chatBody.scrollHeight;
}

function showTypingIndicator() {
    hideTypingIndicator();
    const div = document.createElement('div');
    div.className = 'message bot typing';
    div.innerHTML = '<div class="typing-dots" aria-label="AI is typing"><span></span><span></span><span></span></div>';
    chatBody.appendChild(div);
    chatBody.scrollTop = chatBody.scrollHeight;
    typingIndicator = div;
}

function hideTypingIndicator() {
    if (typingIndicator && typingIndicator.parentNode) {
        typingIndicator.parentNode.removeChild(typingIndicator);
    }
    typingIndicator = null;
}

async function sendMessage() {
    if (!isRegisteredSession) {
        const ok = await ensureRegistration();
        if (!ok) return;
    }

    const text = input.value.trim();
    if ((!text && !selectedAttachments.length) || isSending) return;

    isSending = true;
    sendBtn.disabled = true;
    sendBtn.textContent = '...';
    const attachmentsToSend = [...selectedAttachments];

    const attachmentLine = attachmentsToSend.length
        ? `\n\n[Attached: ${attachmentsToSend.map((file) => file.name).join(', ')}]`
        : '';
    const composedMessage = `${text || 'attachment upload'}${attachmentLine}`;

    addMessage('user', composedMessage);
    input.value = '';
    selectedAttachments = [];
    attachmentInput.value = '';
    renderAttachmentPreview();
    showTypingIndicator();

    try {
        const formData = new FormData();
        formData.append('message', text || 'attachment upload');
        formData.append('user_id', userId);
        formData.append('remember_history', 'true');
        attachmentsToSend.forEach((file) => {
            formData.append('attachments', file, file.name);
        });

        const response = await fetch('/api/chat', {
            method: 'POST',
            credentials: 'same-origin',
            body: formData
        });

        let data = null;
        try {
            data = await response.json();
        } catch (_) {
            throw new Error(genericChatErrorMessage);
        }
        if (!response.ok) {
            throw new Error(genericChatErrorMessage);
        }

        hideTypingIndicator();
        if (data.attachment_analysis_summary) {
            addMessage('bot', data.attachment_analysis_summary);
        }
        addMessage('bot', data.reply || "I'm sorry, I'm not able to help you with that.");
    } catch (error) {
        hideTypingIndicator();
        console.warn('chat send failed', error);
        addMessage('bot', genericChatErrorMessage);
    } finally {
        hideTypingIndicator();
        isSending = false;
        sendBtn.disabled = false;
        sendBtn.textContent = 'send';
        input.focus();
    }
}

attachBtn.addEventListener('click', () => {
    attachmentInput.click();
});

attachmentInput.addEventListener('change', (event) => {
    const picked = Array.from(event.target.files || []);
    const valid = [];
    const rejected = [];
    picked.slice(0, maxAttachments).forEach((file) => {
        if (file.size > maxAttachmentBytes) {
            rejected.push(`${file.name} is larger than 6 MB`);
            return;
        }
        valid.push(file);
    });
    selectedAttachments = valid;
    renderAttachmentPreview();
    if (rejected.length) {
        addMessage('bot', `Upload note: ${rejected.join('; ')}.`);
    }
});

sendBtn.addEventListener('click', sendMessage);
authSubmitBtn.addEventListener('click', submitRegistrationFromModal);
input.addEventListener('keydown', (event) => {
    if (event.key === 'Enter') {
        event.preventDefault();
        sendMessage();
    }
});
authEmailInput.addEventListener('keydown', (event) => {
    if (event.key === 'Enter') {
        event.preventDefault();
        submitRegistrationFromModal();
    }
});
authPasswordInput.addEventListener('keydown', (event) => {
    if (event.key === 'Enter') {
        event.preventDefault();
        submitRegistrationFromModal();
    }
});

addMessage('bot', 'hey pretty girl, what do you want to talk about? you can also type /feedback followed by tips so i improve over time.');
ensureRegistration();
</script>
</body>
</html>
""")
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    response.headers["Pragma"] = "no-cache"
    return response


@app.route("/nudge-v2")
def nudge_v2():
    """Fresh uncached alias for the updated AI-only chat UI."""
    response = chat()
    return response


@app.route("/activity-log")
def activity_log_screen():
    """Simple trust screen that surfaces key user audit history."""
    response = make_response("""
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Activity Log</title>
<style>
* { box-sizing: border-box; }
body {
    margin: 0;
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    background: linear-gradient(180deg, #f7f8fb 0%, #eef1f7 100%);
    color: #1f2937;
}
.wrap {
    max-width: 920px;
    margin: 0 auto;
    padding: 28px 16px 40px;
}
h1 {
    margin: 0 0 8px;
    font-size: 30px;
}
.sub {
    margin: 0 0 18px;
    color: #4b5563;
}
.row {
    display: grid;
    grid-template-columns: 1fr;
    gap: 14px;
}
.card {
    background: #ffffff;
    border: 1px solid #e5e7eb;
    border-radius: 14px;
    padding: 14px;
}
.card h2 {
    margin: 0 0 10px;
    font-size: 18px;
}
.muted { color: #6b7280; font-size: 14px; }
ul { margin: 0; padding-left: 18px; }
li { margin: 6px 0; }
.error {
    border: 1px solid #fecaca;
    background: #fff1f2;
    color: #9f1239;
    border-radius: 10px;
    padding: 10px;
    margin-bottom: 12px;
}
.top-links {
    display: flex;
    gap: 10px;
    margin-bottom: 16px;
}
.top-links a {
    text-decoration: none;
    border: 1px solid #d1d5db;
    border-radius: 999px;
    padding: 8px 12px;
    color: #111827;
    background: #fff;
    font-size: 14px;
}
</style>
</head>
<body>
<div class="wrap">
    <h1>Your Activity Log</h1>
    <p class="sub">Transparency view for override history, sweep consent history, and sent cancellation requests.</p>
    <div class="top-links">
        <a href="/chat">Back to Chat</a>
    </div>
    <div id="error" class="error" style="display:none;"></div>
    <div class="row">
        <section class="card">
            <h2>Override History</h2>
            <ul id="overrideList"></ul>
        </section>
        <section class="card">
            <h2>Sweep Consent History</h2>
            <ul id="sweepList"></ul>
        </section>
        <section class="card">
            <h2>Sent Cancellations</h2>
            <ul id="cancelList"></ul>
        </section>
        <section class="card">
            <h2>Blocked Metric Claims</h2>
            <ul id="blockedMetricList"></ul>
        </section>
    </div>
</div>
<script>
function fmtTs(ts) {
    if (!ts) return 'unknown time';
    const d = new Date(ts);
    if (Number.isNaN(d.getTime())) return ts;
    return d.toLocaleString();
}

function fillList(listEl, items, renderLine, emptyText) {
    listEl.innerHTML = '';
    if (!items || !items.length) {
        const li = document.createElement('li');
        li.className = 'muted';
        li.textContent = emptyText;
        listEl.appendChild(li);
        return;
    }
    items.forEach((item) => {
        const li = document.createElement('li');
        li.textContent = renderLine(item);
        listEl.appendChild(li);
    });
}

async function loadActivityLog() {
    const err = document.getElementById('error');
    try {
        const res = await fetch('/api/finance/activity-log', {
            method: 'GET',
            credentials: 'same-origin'
        });
        const data = await res.json();
        if (!res.ok) {
            throw new Error(data.error || 'Failed to load activity log.');
        }

        fillList(
            document.getElementById('overrideList'),
            data.override_history || [],
            (item) => `Category: ${item.category || 'other'} | ${fmtTs(item.created_at)}`,
            'No override records yet.'
        );

        fillList(
            document.getElementById('sweepList'),
            data.sweep_consent_history || [],
            (item) => `${item.enabled ? 'Enabled' : 'Disabled'} auto-sweep | ${fmtTs(item.changed_at)}`,
            'No sweep consent changes recorded yet.'
        );

        fillList(
            document.getElementById('cancelList'),
            data.sent_cancellations || [],
            (item) => `${item.service_name || 'unknown service'} | ${fmtTs(item.confirmation_ts)}`,
            'No cancellation sends recorded yet.'
        );

        fillList(
            document.getElementById('blockedMetricList'),
            data.blocked_metric_claims || [],
            (item) => `${item.event || 'unknown event'} | ${item.reason || 'unknown reason'} | ${fmtTs(item.created_at)}`,
            'No blocked metric claims recorded yet.'
        );
    } catch (e) {
        err.style.display = 'block';
        err.textContent = e?.message || 'Could not load activity log right now.';
    }
}

loadActivityLog();
</script>
</body>
</html>
""")
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    response.headers["Pragma"] = "no-cache"
    return response


def infer_auto_control_reason(reply_text):
    """Return plain-language reason when an automatic guardrail/sweep was triggered."""
    lowered = normalize_case(reply_text or "")
    reasons = []
    if any(marker in lowered for marker in ["hard stop", "locked category", "break lock", "lock-break challenge"]):
        reasons.append("A locked spending category rule blocked this action until explicit override confirmations are completed.")
    if any(marker in lowered for marker in ["wait 12 hours", "circuit breaker is active", "high-risk"]):
        reasons.append("A cooldown is active because your spending pattern looked high-risk, so the system paused execution.")
    if "swept $" in lowered and "hysa" in lowered:
        reasons.append("Idle cash above your checking threshold was automatically swept into HYSA to reduce cash drag.")
    return " ".join(reasons).strip()


@app.route("/api/chat", methods=["POST"])
def api_chat():
    mark_user_activity()
    disclaimer = "Informational only. Not financial advice."
    generic_chat_reply = "Something went wrong on my side. Please try again in a moment."
    remember_history = True
    user_id = DEFAULT_USER_ID
    attachment_summaries = []

    try:
        is_multipart = request.content_type and "multipart/form-data" in request.content_type
        request_limit = MAX_JSON_BODY_BYTES if not is_multipart else (MAX_JSON_BODY_BYTES + MAX_CHAT_ATTACHMENTS * MAX_ATTACHMENT_BYTES)
        if reject_large_request(request_limit):
            return jsonify({"error": "Payload too large.", "disclaimer": disclaimer, "reason": ""}), 413
        data = request.form.to_dict() if is_multipart else (request.get_json(silent=True) or {})
        user_message = (data.get("message") or "").strip()
        session_user_id = resolve_session_user_id()
        user_id = sanitize_user_id(session_user_id or data.get("user_id") or DEFAULT_USER_ID)
        remember_history = parse_bool(data.get("remember_history"), default=True)
        uploaded_files = request.files.getlist("attachments") if is_multipart else []

        if (user_message or uploaded_files) and is_user_rate_limited(
            user_id,
            scope="chat-llm",
            max_hits=CHAT_USER_RATE_LIMIT_MAX,
            window_seconds=CHAT_USER_RATE_LIMIT_WINDOW,
        ):
            return jsonify({
                "error": "Too many requests. Please wait before sending more messages.",
                "disclaimer": disclaimer,
                "reason": "Rate limit reached to prevent abuse and uncontrolled API costs.",
            }), 429

        attachment_summaries = analyze_uploaded_files(uploaded_files)
        if attachment_summaries:
            attachment_block = "\n\nUploaded attachment analysis:\n" + "\n\n".join(attachment_summaries)
            user_message = f"{user_message or 'Please analyze these uploads.'}{attachment_block}"

        if not user_message:
            return jsonify({"error": "Message is required.", "disclaimer": disclaimer, "reason": ""}), 400

        if should_use_simple_fallback(user_message):
            return jsonify({"reply": "I'm sorry, I'm not able to help you with that.", "disclaimer": disclaimer, "reason": ""})

        try:
            reply = get_ai_response_sync(user_message, user_id=user_id, remember_history=remember_history)
        except Exception:
            reply = DATA_UNAVAILABLE_RETRY_MESSAGE
        reason = infer_auto_control_reason(reply)
        return jsonify({
            "reply": reply,
            "user_id": user_id,
            "remember_history": remember_history,
            "attachment_analysis_summary": "\n\n".join(attachment_summaries[:3]) if attachment_summaries else "",
            "disclaimer": disclaimer,
            "reason": reason,
        })
    except Exception as e:
        print(f"Warning: api_chat unexpected error: {e}")
        return jsonify({
            "reply": generic_chat_reply,
            "user_id": user_id,
            "remember_history": remember_history,
            "attachment_analysis_summary": "\n\n".join(attachment_summaries[:3]) if attachment_summaries else "",
            "disclaimer": disclaimer,
            "reason": "",
        }), 200


@app.route("/api/feedback", methods=["POST"])
def api_feedback():
    mark_user_activity()
    if reject_large_request():
        return jsonify({"error": "Payload too large."}), 413
    data = request.get_json(silent=True) or {}
    feedback_text = (data.get("feedback") or "").strip()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or data.get("user_id") or DEFAULT_USER_ID)

    if not feedback_text:
        return jsonify({"error": "Feedback is required."}), 400

    user_state = load_user_state(user_id)
    payload = detect_feedback_payload(f"/feedback {feedback_text}")
    user_state = apply_feedback_learning(user_id, user_state, payload)
    save_user_state(user_id, user_state)
    return jsonify({"status": "saved", "user_id": user_id})


@app.route("/api/auth/register", methods=["POST"])
def api_auth_register():
    mark_user_activity()
    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    if is_rate_limited("register", max_hits=8, window_seconds=600):
        return jsonify({"error": "Too many attempts. Try again later."}), 429

    data = request.get_json(silent=True) or {}
    email = sanitize_email(data.get("email"))
    name = (data.get("name") or "").strip()
    password = data.get("password") or ""
    accountability_target = (data.get("accountability_target") or "").strip()

    if not is_valid_email(email):
        return jsonify({"error": "Valid email is required."}), 400
    if not is_valid_display_name(name):
        return jsonify({"error": "Valid name is required (2-70 chars)."}), 400
    if not is_valid_password(password):
        return jsonify({"error": "Password must be 8-128 characters."}), 400

    e_hash = email_hash(email)
    accounts = load_accounts()
    user_id = derive_user_id_from_email(email)

    existing = accounts.get(e_hash) or {}
    created_at = existing.get("created_at") or utc_now_iso()
    existing_hash = existing.get("password_hash") or ""
    if existing_hash and not verify_password(password, existing_hash):
        return jsonify({"error": "Account already exists. Use your correct password to sign in."}), 401

    accounts[e_hash] = {
        "user_id": user_id,
        "name": name or (existing.get("name") or ""),
        "password_hash": existing_hash or hash_password(password),
        "accountability_target": accountability_target or (existing.get("accountability_target") or "").strip(),
        "created_at": created_at,
        "updated_at": utc_now_iso(),
    }
    save_accounts(accounts)

    user_state = load_user_state(user_id)
    prior_profile = user_state.get("profile") or {}
    user_state["profile"] = {
        "name": name or (prior_profile.get("name") or ""),
        "email_hash": e_hash,
        "registered_at": created_at,
        "accountability_target": accountability_target or (prior_profile.get("accountability_target") or "").strip(),
    }
    save_user_state(user_id, user_state)

    access_token, refresh_token = create_auth_tokens_for_user(user_id)
    response = jsonify({"status": "ok", "user_id": user_id, "name": user_state["profile"].get("name") or ""})
    set_auth_cookies(response, access_token, refresh_token)
    clear_legacy_session_cookie(response)
    return response


@app.route("/api/auth/login", methods=["POST"])
def api_auth_login():
    mark_user_activity()
    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    if is_rate_limited("login", max_hits=12, window_seconds=600):
        return jsonify({"error": "Too many attempts. Try again later."}), 429

    data = request.get_json(silent=True) or {}
    email = sanitize_email(data.get("email"))
    password = data.get("password") or ""
    if not is_valid_email(email) or not password:
        return jsonify({"error": "Valid email and password are required."}), 400

    e_hash = email_hash(email)
    accounts = load_accounts()
    account = accounts.get(e_hash) or {}
    password_hash = account.get("password_hash") or ""
    if not password_hash or not verify_password(password, password_hash):
        return jsonify({"error": "Invalid credentials."}), 401

    user_id = sanitize_user_id(account.get("user_id") or derive_user_id_from_email(email))
    access_token, refresh_token = create_auth_tokens_for_user(user_id)
    response = jsonify({"status": "ok", "user_id": user_id, "name": account.get("name") or ""})
    set_auth_cookies(response, access_token, refresh_token)
    clear_legacy_session_cookie(response)
    return response


@app.route("/api/auth/refresh", methods=["POST"])
def api_auth_refresh():
    if reject_large_request(4096):
        return jsonify({"error": "Payload too large."}), 413

    access_token, refresh_token = refresh_tokens_from_refresh_cookie()
    if not access_token or not refresh_token:
        response = jsonify({"error": "Refresh token expired or invalid."})
        clear_session_cookie(response)
        return response, 401

    response = jsonify({"status": "ok"})
    set_auth_cookies(response, access_token, refresh_token)
    return response


@app.route("/api/auth/me", methods=["GET"])
def api_auth_me():
    user_id = resolve_session_user_id()
    if not user_id:
        return jsonify({"authenticated": False}), 401
    user_state = ensure_finance_profiles(load_user_state(user_id))
    daily_alert, updated = maybe_generate_daily_finance_alert(user_state)
    if updated:
        save_user_state(user_id, user_state)
    profile = user_state.get("profile") or {}
    return jsonify({
        "authenticated": True,
        "user_id": user_id,
        "name": profile.get("name") or "",
        "accountability_target": profile.get("accountability_target") or "",
        "daily_finance_alert": daily_alert,
    })


@app.route("/api/auth/logout", methods=["POST"])
def api_auth_logout():
    if reject_large_request(4096):
        return jsonify({"error": "Payload too large."}), 413
    revoke_token_cookie("ai_access", "access")
    revoke_token_cookie("ai_refresh", "refresh")
    revoke_token_cookie("ai_session", "access")
    response = jsonify({"status": "logged_out"})
    clear_session_cookie(response)
    return response


@app.route("/api/learning/status", methods=["GET"])
def api_learning_status():
    learning_memory = load_learning_memory()
    return jsonify({
        "auto_learning_enabled": AUTO_LEARN_ENABLED,
        "idle_interval_seconds": AUTO_LEARN_INTERVAL_SECONDS,
        "idle_required_seconds": AUTO_LEARN_IDLE_SECONDS,
        "last_idle_run": learning_memory.get("last_idle_run", ""),
        "idle_runs": learning_memory.get("idle_runs", 0),
        "idle_topics_cached": len((learning_memory.get("idle_knowledge") or {})),
    })


@app.route("/api/finance/quotes", methods=["GET"])
def api_finance_quotes():
    """Return live or most-recent quote snapshots for comma-separated symbols."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    symbols_raw = (request.args.get("symbols") or "").strip()
    if not symbols_raw:
        return jsonify({"error": "Query parameter 'symbols' is required."}), 400

    symbols = []
    for token in re.split(r"[,\s]+", symbols_raw):
        symbol = normalize_ticker_symbol(token)
        if symbol and symbol not in symbols:
            symbols.append(symbol)
    symbols = symbols[:50]
    if not symbols:
        return jsonify({"error": "No valid symbols provided."}), 400

    try:
        quotes_map, source_url = fetch_live_quotes(symbols)
    except Exception:
        return jsonify({"error": "Failed to fetch finance data."}), 502

    rows = []
    for symbol in symbols:
        quote = quotes_map.get(symbol) or {}
        is_traceable, reason = validate_traceable_quote_metrics(quote)
        if quote.get("price") is not None and not is_traceable:
            log_metric_validation_block(
                "quote-api",
                f"untraceable-quote:{reason}",
                {"symbol": symbol, "provider": quote.get("provider") or "unknown"},
                user_id=user_id,
            )
            quote = dict(quote)
            quote["price"] = None
            quote["change_percent"] = None
            quote["market_time"] = None
        as_of_label = quote_as_of_label(quote)
        freshness = quote_freshness_label(quote)
        rows.append({
            "symbol": symbol,
            "name": quote.get("name") or symbol,
            "price": quote.get("price"),
            "currency": quote.get("currency") or "USD",
            "exchange": quote.get("exchange") or "",
            "change_percent": quote.get("change_percent"),
            "market_time": quote.get("market_time"),
            "market_time_utc": format_quote_timestamp(quote.get("market_time")),
            "provider": quote.get("provider") or "unknown",
            "stale": bool(quote.get("stale")),
            "from_cache": bool(quote.get("from_cache")),
            "data_freshness": freshness,
            "as_of_label": f"as of {as_of_label}",
            "cache_age_seconds": quote.get("cache_age_seconds"),
            "last_known_utc": quote.get("last_known_utc") or "",
            "traceability": {
                "provider": quote.get("provider") or "unknown",
                "source_url": quote.get("source_url") or "",
                "price_field": "regularMarketPrice|provider_equivalent",
                "change_percent_field": "regularMarketChangePercent|provider_equivalent",
                "market_time_field": "regularMarketTime|provider_equivalent",
                "validation_error": "" if is_traceable else reason,
            },
        })

    return jsonify({
        "as_of_utc": utc_now_iso(),
        "cache_ttl_seconds": FINANCE_QUOTE_CACHE_TTL_SECONDS,
        "source": source_url or "https://finance.yahoo.com/",
        "traceability": {
            "numeric_fields": [
                "quotes[].price",
                "quotes[].change_percent",
                "quotes[].market_time",
            ],
            "data_origin": "provider API response or cache derived from provider response",
        },
        "quotes": rows,
    })


@app.route("/api/finance/watchlist", methods=["GET", "POST", "DELETE"])
def api_finance_watchlist():
    """Manage per-user stock watchlist and optionally fetch a live snapshot."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    finance_profile = user_state.get("finance_profile") or {}

    if request.method == "GET":
        include_quotes = parse_bool(request.args.get("include_quotes"), default=False)
        watchlist = finance_profile.get("watchlist") or []
        response = {
            "user_id": user_id,
            "watchlist": watchlist,
            "watchlist_last_checked": finance_profile.get("watchlist_last_checked") or "",
        }
        if include_quotes and watchlist:
            try:
                quotes_map, source_url = fetch_live_quotes(watchlist)
            except Exception:
                return jsonify({"error": "Failed to fetch quote snapshot."}), 502
            response["source"] = source_url or "https://finance.yahoo.com/"
            rows = []
            for symbol in watchlist:
                quote = quotes_map.get(symbol) or {}
                is_traceable, reason = validate_traceable_quote_metrics(quote)
                if quote.get("price") is not None and not is_traceable:
                    log_metric_validation_block(
                        "watchlist-api",
                        f"untraceable-quote:{reason}",
                        {"symbol": symbol, "provider": quote.get("provider") or "unknown"},
                        user_id=user_id,
                    )
                    quote = dict(quote)
                    quote["price"] = None
                    quote["change_percent"] = None
                    quote["market_time"] = None

                rows.append(
                    {
                        "symbol": symbol,
                        "name": quote.get("name") or symbol,
                        "price": quote.get("price"),
                        "change_percent": quote.get("change_percent"),
                        "market_time": quote.get("market_time"),
                        "market_time_utc": format_quote_timestamp(quote.get("market_time")),
                        "provider": quote.get("provider") or "unknown",
                        "stale": bool(quote.get("stale")),
                        "from_cache": bool(quote.get("from_cache")),
                        "data_freshness": quote_freshness_label(quote),
                        "as_of_label": f"as of {quote_as_of_label(quote)}",
                        "cache_age_seconds": quote.get("cache_age_seconds"),
                        "last_known_utc": quote.get("last_known_utc") or "",
                        "traceability": {
                            "provider": quote.get("provider") or "unknown",
                            "source_url": quote.get("source_url") or "",
                            "price_field": "regularMarketPrice|provider_equivalent",
                            "change_percent_field": "regularMarketChangePercent|provider_equivalent",
                            "validation_error": "" if is_traceable else reason,
                        },
                    }
                )

            response["quotes"] = rows
            response["traceability"] = {
                "numeric_fields": ["quotes[].price", "quotes[].change_percent", "quotes[].market_time"],
                "data_origin": "provider API response or cache derived from provider response",
            }
        return jsonify(response)

    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    data = request.get_json(silent=True) or {}
    symbols = data.get("symbols") or []
    if isinstance(symbols, str):
        symbols = re.split(r"[,\s]+", symbols)
    if not isinstance(symbols, list):
        return jsonify({"error": "symbols must be a list or string."}), 400

    normalized = []
    for token in symbols:
        symbol = normalize_ticker_symbol(str(token))
        if symbol and symbol not in normalized:
            normalized.append(symbol)
    normalized = normalized[:60]

    watchlist = finance_profile.get("watchlist") or []
    if request.method == "POST":
        for symbol in normalized:
            if symbol not in watchlist:
                watchlist.append(symbol)
        watchlist = watchlist[:60]
        finance_profile["watchlist"] = watchlist
        finance_profile["watchlist_last_checked"] = utc_now_iso()
        user_state["finance_profile"] = finance_profile
        save_user_state(user_id, user_state)
        return jsonify({"status": "ok", "user_id": user_id, "watchlist": watchlist})

    clear_all = parse_bool(data.get("clear"), default=False)
    if clear_all:
        watchlist = []
    else:
        watchlist = [symbol for symbol in watchlist if symbol not in set(normalized)]
    finance_profile["watchlist"] = watchlist
    finance_profile["watchlist_last_checked"] = utc_now_iso()
    user_state["finance_profile"] = finance_profile
    save_user_state(user_id, user_state)
    return jsonify({"status": "ok", "user_id": user_id, "watchlist": watchlist})


@app.route("/api/finance/providers/health", methods=["GET"])
def api_finance_provider_health():
    """Return quote provider health diagnostics and cache stats."""
    mark_user_activity()
    with finance_cache_lock:
        health = json.loads(json.dumps(finance_provider_health))
        cache_size = len(finance_quote_cache)

    for provider, bucket in health.items():
        active, remaining, reason = get_provider_cooldown_state(provider)
        bucket["cooldown_active"] = bool(active)
        bucket["cooldown_seconds_remaining"] = int(remaining)
        if not bucket.get("cooldown_reason") and reason:
            bucket["cooldown_reason"] = reason

    return jsonify({
        "as_of_utc": utc_now_iso(),
        "cache_ttl_seconds": FINANCE_QUOTE_CACHE_TTL_SECONDS,
        "cache_size": cache_size,
        "alpha_vantage_configured": bool(ALPHA_VANTAGE_API_KEY),
        "providers": health,
    })


@app.route("/api/finance/runway-buffer", methods=["GET", "POST"])
def api_finance_runway_buffer():
    """Calculate or update multi-currency PPP-adjusted runway buffer metrics."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    finance_profile = user_state.get("finance_profile") or {}
    saved_profile = finance_profile.get("runway_buffer_profile") or {}

    if request.method == "GET":
        city = normalize_city_key(request.args.get("city") or saved_profile.get("current_city") or "")
        base_city = normalize_city_key(request.args.get("base_city") or saved_profile.get("base_city") or BASELINE_COST_INDEX_CITY)
        capital_usd = to_float_or_none(request.args.get("capital_usd"))
        if capital_usd is None:
            capital_usd = float(saved_profile.get("capital_usd") or 0.0)
        base_monthly_cap_usd = to_float_or_none(request.args.get("base_monthly_cap_usd"))
        if base_monthly_cap_usd is None:
            base_monthly_cap_usd = float(saved_profile.get("base_monthly_cap_usd") or 0.0)
        shadow_runway_enabled = request.args.get("shadow_runway_enabled")
        if shadow_runway_enabled is None:
            shadow_enabled = bool(saved_profile.get("shadow_runway_enabled", False))
        else:
            shadow_enabled = parse_bool(shadow_runway_enabled, default=False)
        safety_buffer_months = to_float_or_none(request.args.get("safety_buffer_months"))
        if safety_buffer_months is None:
            safety_buffer_months = float(saved_profile.get("safety_buffer_months") or 0.0)

        if not city:
            return jsonify({
                "error": "city is required (query param) or must exist in saved runway profile.",
                "supported_cities": sorted(CITY_COST_INDEX.keys()),
            }), 400
        if float(capital_usd or 0.0) <= 0:
            return jsonify({"error": "capital_usd must be greater than zero."}), 400

        try:
            metrics = build_runway_buffer_metrics(
                capital_usd=float(capital_usd),
                current_city=city,
                base_monthly_cap_usd=float(base_monthly_cap_usd or 0.0),
                base_city=base_city,
                shadow_runway_enabled=shadow_enabled,
                safety_buffer_months=float(safety_buffer_months or 0.0),
            )
        except Exception as e:
            return jsonify({"error": str(e), "supported_cities": sorted(CITY_COST_INDEX.keys())}), 400

        return jsonify({
            "user_id": user_id,
            "runway_buffer": metrics,
            "assumptions": [
                "PPP-adjusted runway is computed from your provided capital/monthly cap inputs.",
                "Cost-of-living adjustment uses CITY_COST_INDEX map values configured in the app.",
                "FX conversion uses latest cached/fetched USD->target currency rate.",
            ],
            "supported_cities": sorted(CITY_COST_INDEX.keys()),
        })

    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    data = request.get_json(silent=True) or {}
    city = normalize_city_key(data.get("city") or saved_profile.get("current_city") or "")
    base_city = normalize_city_key(data.get("base_city") or saved_profile.get("base_city") or BASELINE_COST_INDEX_CITY)
    capital_usd = float(to_float_or_none(data.get("capital_usd")) or saved_profile.get("capital_usd") or 0.0)
    base_monthly_cap_usd = float(to_float_or_none(data.get("base_monthly_cap_usd")) or saved_profile.get("base_monthly_cap_usd") or 0.0)
    if data.get("shadow_runway_enabled") is None:
        shadow_enabled = bool(saved_profile.get("shadow_runway_enabled", False))
    else:
        shadow_enabled = bool(data.get("shadow_runway_enabled"))
    safety_buffer_months = float(to_float_or_none(data.get("safety_buffer_months")) or saved_profile.get("safety_buffer_months") or 0.0)

    if not city:
        return jsonify({"error": "city is required.", "supported_cities": sorted(CITY_COST_INDEX.keys())}), 400
    if capital_usd <= 0:
        return jsonify({"error": "capital_usd must be greater than zero."}), 400

    try:
        metrics = build_runway_buffer_metrics(
            capital_usd=capital_usd,
            current_city=city,
            base_monthly_cap_usd=base_monthly_cap_usd,
            base_city=base_city,
            shadow_runway_enabled=shadow_enabled,
            safety_buffer_months=safety_buffer_months,
        )
    except Exception as e:
        return jsonify({"error": str(e), "supported_cities": sorted(CITY_COST_INDEX.keys())}), 400

    finance_profile["runway_buffer_profile"] = {
        "base_city": metrics.get("base_city") or base_city,
        "current_city": metrics.get("current_city") or city,
        "capital_usd": metrics.get("capital_usd") or capital_usd,
        "base_monthly_cap_usd": metrics.get("base_monthly_cap_usd") or base_monthly_cap_usd,
        "shadow_runway_enabled": bool(metrics.get("shadow_runway_enabled")),
        "safety_buffer_months": float(metrics.get("safety_buffer_months") or 0.0),
        "updated_at": utc_now_iso(),
    }
    user_state["finance_profile"] = finance_profile
    save_user_state(user_id, user_state)
    return jsonify({
        "status": "ok",
        "user_id": user_id,
        "runway_buffer": metrics,
        "assumptions": [
            "PPP-adjusted runway is computed from your provided capital/monthly cap inputs.",
            "Cost-of-living adjustment uses CITY_COST_INDEX map values configured in the app.",
            "FX conversion uses latest cached/fetched USD->target currency rate.",
        ],
        "saved_profile": finance_profile.get("runway_buffer_profile") or {},
    })


@app.route("/api/finance/hysa-auto-sweep", methods=["GET", "POST"])
def api_finance_hysa_auto_sweep():
    """Manage explicit user consent for automatic HYSA idle-cash sweep."""
    mark_user_activity()
    data = request.get_json(silent=True) or {} if request.method == "POST" else {}
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or data.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    finance_profile = user_state.get("finance_profile") or {}
    cash_profile = finance_profile.get("cash_management") or {}

    if request.method == "GET":
        return jsonify({
            "user_id": user_id,
            "hysa_auto_sweep_enabled": bool(cash_profile.get("hysa_auto_sweep_enabled", False)),
            "hysa_auto_sweep_enabled_at": str(cash_profile.get("hysa_auto_sweep_enabled_at") or ""),
            "as_of_utc": utc_now_iso(),
        })

    if reject_large_request(4096):
        return jsonify({"error": "Payload too large."}), 413
    enabled = parse_bool(data.get("enabled"), default=False)

    cash_profile["hysa_auto_sweep_enabled"] = bool(enabled)
    consent_history = cash_profile.get("hysa_auto_sweep_consent_history")
    if not isinstance(consent_history, list):
        consent_history = []
    change_ts = utc_now_iso()
    consent_history.append({
        "enabled": bool(enabled),
        "changed_at": change_ts,
    })
    cash_profile["hysa_auto_sweep_consent_history"] = consent_history[-100:]
    if enabled:
        cash_profile["hysa_auto_sweep_enabled_at"] = change_ts
    else:
        cash_profile["hysa_auto_sweep_enabled_at"] = ""
    finance_profile["cash_management"] = cash_profile
    user_state["finance_profile"] = finance_profile
    save_user_state(user_id, user_state)

    return jsonify({
        "status": "ok",
        "user_id": user_id,
        "hysa_auto_sweep_enabled": bool(cash_profile.get("hysa_auto_sweep_enabled", False)),
        "hysa_auto_sweep_enabled_at": str(cash_profile.get("hysa_auto_sweep_enabled_at") or ""),
        "hysa_auto_sweep_consent_history": cash_profile.get("hysa_auto_sweep_consent_history") or [],
        "as_of_utc": utc_now_iso(),
    })


@app.route("/api/finance/activity-log", methods=["GET"])
def api_finance_activity_log():
    """Return user-visible audit history for trust and transparency."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    limit = int(to_float_or_none(request.args.get("limit")) or 100)

    sql_activity = analytics_sql_fetch_user_activity_log(user_id, limit=limit)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    cash_profile = (user_state.get("finance_profile") or {}).get("cash_management") or {}
    sweep_history = cash_profile.get("hysa_auto_sweep_consent_history")
    if not isinstance(sweep_history, list):
        sweep_history = []
    metric_history = (user_state.get("finance_profile") or {}).get("metric_validation_history")
    if not isinstance(metric_history, list):
        metric_history = []

    # Backfill one baseline consent entry from legacy field when history is absent.
    if not sweep_history:
        enabled_at = str(cash_profile.get("hysa_auto_sweep_enabled_at") or "")
        if enabled_at:
            sweep_history.append({"enabled": True, "changed_at": enabled_at})

    return jsonify(
        {
            "user_id": user_id,
            "as_of_utc": utc_now_iso(),
            "override_history": sql_activity.get("overrides") or [],
            "sweep_consent_history": sweep_history[-200:][::-1],
            "sent_cancellations": sql_activity.get("cancellations") or [],
            "blocked_metric_claims": metric_history[-200:][::-1],
        }
    )


@app.route("/api/finance/opportunity-cost", methods=["GET", "POST"])
def api_finance_opportunity_cost():
    """Compute or configure opportunity-cost gating (Alpha Rule)."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    behavior_profile = user_state.get("behavior_budget_profile") or {}

    if request.method == "GET":
        amount_usd = to_float_or_none(request.args.get("amount_usd"))
        years = int(to_float_or_none(request.args.get("years")) or behavior_profile.get("opportunity_cost_default_years") or OPPORTUNITY_COST_DEFAULT_YEARS)
        annual_return = to_float_or_none(request.args.get("annual_return"))
        if annual_return is None:
            annual_return = float(behavior_profile.get("opportunity_cost_default_annual_return") or OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN)
        threshold = float(behavior_profile.get("opportunity_cost_threshold_usd") or OPPORTUNITY_COST_THRESHOLD_USD)

        if amount_usd is None or float(amount_usd) <= 0:
            return jsonify({"error": "amount_usd must be greater than zero."}), 400

        gate = build_opportunity_cost_gate(float(amount_usd), years=years, annual_return=float(annual_return))
        return jsonify({
            "user_id": user_id,
            "threshold_usd": threshold,
            "opportunity_cost": gate,
            "assumptions": [
                "future_value uses compound growth formula FV = PV * (1 + r)^n.",
                "annual_return is an assumed rate, not a guaranteed outcome.",
                "results are illustrative projections.",
            ],
        })

    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    data = request.get_json(silent=True) or {}

    threshold = to_float_or_none(data.get("threshold_usd"))
    years = to_float_or_none(data.get("default_years"))
    annual_return = to_float_or_none(data.get("default_annual_return"))

    if threshold is not None:
        behavior_profile["opportunity_cost_threshold_usd"] = max(0.0, float(threshold))
    if years is not None:
        behavior_profile["opportunity_cost_default_years"] = max(1, min(50, int(float(years))))
    if annual_return is not None:
        behavior_profile["opportunity_cost_default_annual_return"] = max(0.0, min(1.0, float(annual_return)))

    user_state["behavior_budget_profile"] = behavior_profile
    save_user_state(user_id, user_state)

    return jsonify({
        "status": "ok",
        "user_id": user_id,
        "settings": {
            "threshold_usd": float(behavior_profile.get("opportunity_cost_threshold_usd") or OPPORTUNITY_COST_THRESHOLD_USD),
            "default_years": int(behavior_profile.get("opportunity_cost_default_years") or OPPORTUNITY_COST_DEFAULT_YEARS),
            "default_annual_return": float(behavior_profile.get("opportunity_cost_default_annual_return") or OPPORTUNITY_COST_DEFAULT_ANNUAL_RETURN),
        },
        "last_gate": behavior_profile.get("last_opportunity_cost_gate") or {},
    })


@app.route("/api/finance/subscriptions", methods=["GET", "POST", "DELETE"])
def api_finance_subscriptions():
    """Manage subscriptions used by decay/phantom-burn analysis."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    subscription_profile = user_state.get("subscription_profile") or {}

    if request.method == "GET":
        return jsonify({
            "user_id": user_id,
            "items": subscription_profile.get("items") or [],
            "savings_goal": subscription_profile.get("savings_goal") or {"name": "", "amount": 0.0},
            "last_alert_at": subscription_profile.get("last_alert_at") or "",
        })

    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    data = request.get_json(silent=True) or {}

    if request.method == "POST":
        name = (data.get("name") or "").strip()
        if not name:
            return jsonify({"error": "name is required."}), 400
        try:
            monthly_cost = float(data.get("monthly_cost") or 0.0)
        except Exception:
            monthly_cost = 0.0
        try:
            days_unused = int(float(data.get("days_since_last_use") or 0))
        except Exception:
            days_unused = 0
        if monthly_cost <= 0:
            return jsonify({"error": "monthly_cost must be > 0."}), 400

        items = subscription_profile.get("items") or []
        target = None
        for item in items:
            if normalize_case(item.get("name")) == normalize_case(name):
                target = item
                break
        if target:
            target["monthly_cost"] = monthly_cost
            target["days_since_last_use"] = max(0, days_unused)
            target["updated_at"] = utc_now_iso()
        else:
            items.append({
                "name": name,
                "monthly_cost": monthly_cost,
                "days_since_last_use": max(0, days_unused),
                "updated_at": utc_now_iso(),
            })
        subscription_profile["items"] = items[:120]
        user_state["subscription_profile"] = subscription_profile
        save_user_state(user_id, user_state)
        return jsonify({"status": "ok", "user_id": user_id, "items": subscription_profile["items"]})

    clear_all = parse_bool(data.get("clear"), default=False)
    items = subscription_profile.get("items") or []
    if clear_all:
        items = []
    else:
        name = (data.get("name") or "").strip()
        if not name:
            return jsonify({"error": "name is required unless clear=true."}), 400
        items = [item for item in items if normalize_case(item.get("name")) != normalize_case(name)]
    subscription_profile["items"] = items
    user_state["subscription_profile"] = subscription_profile
    save_user_state(user_id, user_state)
    return jsonify({"status": "ok", "user_id": user_id, "items": items})


@app.route("/api/finance/subscriptions/goal", methods=["POST"])
def api_finance_subscriptions_goal():
    """Set savings goal used for phantom-burn acceleration estimates."""
    mark_user_activity()
    if reject_large_request(4096):
        return jsonify({"error": "Payload too large."}), 413
    session_user_id = resolve_session_user_id()
    data = request.get_json(silent=True) or {}
    user_id = sanitize_user_id(session_user_id or data.get("user_id") or DEFAULT_USER_ID)
    name = (data.get("name") or "").strip() or "your savings goal"
    try:
        amount = float(data.get("amount") or 0.0)
    except Exception:
        amount = 0.0
    if amount <= 0:
        return jsonify({"error": "amount must be > 0."}), 400

    user_state = ensure_finance_profiles(load_user_state(user_id))
    subscription_profile = user_state.get("subscription_profile") or {}
    subscription_profile["savings_goal"] = {
        "name": name,
        "amount": amount,
    }
    subscription_profile["last_alert_at"] = utc_now_iso()
    user_state["subscription_profile"] = subscription_profile
    save_user_state(user_id, user_state)
    return jsonify({"status": "ok", "user_id": user_id, "savings_goal": subscription_profile["savings_goal"]})


@app.route("/api/finance/alerts", methods=["GET"])
def api_finance_alerts():
    """Return proactive subscription decay/phantom burn analysis text."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    include_sources = parse_bool(request.args.get("include_sources"), default=False)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    report_text = build_subscription_decay_report(user_state, include_sources=include_sources)
    save_user_state(user_id, user_state)
    return jsonify({
        "user_id": user_id,
        "as_of_utc": utc_now_iso(),
        "alert": report_text,
    })


@app.route("/api/finance/subscriptions/vampires", methods=["GET"])
def api_finance_subscription_vampires():
    """Scan transaction history for recurring low-usage subscription charges."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    user_state, alerts = detect_subscription_vampires(user_state)
    save_user_state(user_id, user_state)
    return jsonify({
        "user_id": user_id,
        "as_of_utc": utc_now_iso(),
        "last_vampire_scan_at": (user_state.get("subscription_profile") or {}).get("last_vampire_scan_at") or "",
        "alerts": alerts,
    })


@app.route("/api/finance/subscriptions/cancel-draft", methods=["POST"])
def api_finance_subscription_cancel_draft():
    """Draft a cancellation email for a flagged subscription vampire."""
    mark_user_activity()
    if reject_large_request(4096):
        return jsonify({"error": "Payload too large."}), 413
    session_user_id = resolve_session_user_id()
    data = request.get_json(silent=True) or {}
    user_id = sanitize_user_id(session_user_id or data.get("user_id") or DEFAULT_USER_ID)
    target_name = (data.get("name") or "").strip()
    if not target_name:
        return jsonify({"error": "name is required."}), 400

    user_state = ensure_finance_profiles(load_user_state(user_id))
    user_state, alerts = detect_subscription_vampires(user_state)
    subscription_profile = user_state.get("subscription_profile") or {}
    match = None
    for alert in alerts:
        if normalize_case(alert.get("service_name")) == normalize_case(target_name):
            match = alert
            break
    if match is None:
        for item in subscription_profile.get("items") or []:
            if normalize_case(item.get("name")) == normalize_case(target_name):
                match = {"service_name": item.get("name"), "monthly_cost": float(item.get("monthly_cost") or 0.0)}
                break
    if match is None:
        return jsonify({"error": "Subscription not found."}), 404

    draft = build_subscription_cancellation_email(match.get("service_name") or target_name, match.get("monthly_cost") or 0.0)
    review_token = secrets.token_urlsafe(24)
    expires_at = (datetime.now(timezone.utc) + timedelta(minutes=30)).isoformat()
    subscription_profile["pending_cancellation_review"] = {
        "service_name": match.get("service_name") or target_name,
        "review_token": review_token,
        "created_at": utc_now_iso(),
        "expires_at": expires_at,
        "draft": draft,
    }
    user_state["subscription_profile"] = subscription_profile
    save_user_state(user_id, user_state)
    return jsonify({
        "status": "ok",
        "user_id": user_id,
        "service_name": match.get("service_name") or target_name,
        "draft": draft,
        "auto_sent": False,
        "review_required": True,
        "review_token": review_token,
        "review_expires_at": expires_at,
        "confirmation_text_required": "I HAVE REVIEWED AND CONFIRM SEND",
        "next_step": "Call /api/finance/subscriptions/cancel-send with review_token and confirmation text.",
    })


@app.route("/api/finance/subscriptions/cancel-send", methods=["POST"])
def api_finance_subscription_cancel_send():
    """Require explicit review+confirm before submitting a cancellation draft."""
    mark_user_activity()
    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413

    session_user_id = resolve_session_user_id()
    data = request.get_json(silent=True) or {}
    user_id = sanitize_user_id(session_user_id or data.get("user_id") or DEFAULT_USER_ID)
    target_name = (data.get("name") or "").strip()
    review_token = (data.get("review_token") or "").strip()
    confirmation_text = (data.get("confirmation_text") or "").strip()
    confirm_send = bool(data.get("confirm_send") is True)

    if not target_name:
        return jsonify({"error": "name is required."}), 400
    if not review_token:
        return jsonify({"error": "review_token is required."}), 400
    if not confirm_send:
        return jsonify({"error": "confirm_send=true is required to submit cancellation."}), 400
    if confirmation_text != "I HAVE REVIEWED AND CONFIRM SEND":
        return jsonify({"error": "Exact confirmation text is required before submission."}), 400

    user_state = ensure_finance_profiles(load_user_state(user_id))
    subscription_profile = user_state.get("subscription_profile") or {}
    pending = subscription_profile.get("pending_cancellation_review") or {}
    pending_name = (pending.get("service_name") or "").strip()
    pending_token = (pending.get("review_token") or "").strip()
    pending_expires = parse_iso_datetime(pending.get("expires_at") or "")

    if not pending_name or not pending_token:
        return jsonify({"error": "No pending reviewed draft found. Request a new draft first."}), 409
    if normalize_case(pending_name) != normalize_case(target_name):
        return jsonify({"error": "Pending draft merchant does not match requested name."}), 409
    if pending_token != review_token:
        return jsonify({"error": "Invalid review_token."}), 401
    if pending_expires is None or datetime.now(timezone.utc) >= pending_expires:
        return jsonify({"error": "Review token expired. Request a new draft."}), 409

    draft = pending.get("draft") if isinstance(pending.get("draft"), dict) else {}
    if not draft.get("subject") or not draft.get("body"):
        return jsonify({"error": "Pending draft is invalid. Request a new draft."}), 409

    confirmation_ts = utc_now_iso()
    analytics_sql_insert_cancellation_send(user_id, target_name, draft, confirmation_ts=confirmation_ts)
    subscription_profile["pending_cancellation_review"] = {}
    user_state["subscription_profile"] = subscription_profile
    save_user_state(user_id, user_state)

    return jsonify({
        "status": "submitted",
        "user_id": user_id,
        "service_name": target_name,
        "auto_sent": False,
        "submitted_on_user_behalf": True,
        "confirmation_ts": confirmation_ts,
        "draft": draft,
    })


@app.route("/api/finance/behavior", methods=["GET", "POST"])
def api_finance_behavior():
    """Get behavior insights or log spend events for trigger learning."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))

    if request.method == "GET":
        insight_text = build_behavioral_budget_summary(user_state)
        nudge = build_empathetic_budget_nudge(user_state)
        weekly_vibe = analytics_sql_weekly_mood_spending_report(user_id)
        return jsonify({
            "user_id": user_id,
            "insights": insight_text,
            "nudge": nudge,
            "weekly_vibe_check": weekly_vibe,
            "as_of_utc": utc_now_iso(),
        })

    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    data = request.get_json(silent=True) or {}
    amount = data.get("amount")
    category = (data.get("category") or "other").strip().lower()
    day_of_week = (data.get("day_of_week") or datetime.now().strftime("%A")).strip().capitalize()
    hour = data.get("hour") if data.get("hour") is not None else datetime.now().hour
    stress_level = (data.get("stress_level") or "medium").strip().lower()

    try:
        amount_value = float(amount)
    except Exception:
        return jsonify({"error": "amount must be numeric."}), 400
    try:
        hour_value = int(hour)
    except Exception:
        hour_value = datetime.now().hour
    if amount_value <= 0:
        return jsonify({"error": "amount must be > 0."}), 400
    if stress_level not in {"low", "medium", "high"}:
        stress_level = "medium"

    event = {
        "amount": amount_value,
        "category": category or "other",
        "day_of_week": day_of_week,
        "hour": max(0, min(23, hour_value)),
        "stress_level": stress_level,
        "inferred_tone": infer_user_tone(f"{category} {stress_level}"),
        "timestamp": utc_now_iso(),
    }
    user_state = add_spend_event(user_state, event)
    analytics_sql_insert_spend_event(user_id, event)
    save_user_state(user_id, user_state)
    projection = None
    projection_text = ""
    if is_discretionary_expense_category(event.get("category")):
        projection = build_dynamic_opportunity_cost_projection(event.get("amount") or 0.0, annual_return=0.075)
        projection_text = render_dynamic_opportunity_cost_projection(projection)
    return jsonify({
        "status": "ok",
        "user_id": user_id,
        "event": event,
        "opportunity_cost_projection": projection,
        "opportunity_cost_message": projection_text,
    })


@app.route("/api/finance/reports/weekly.pdf", methods=["GET"])
def api_finance_weekly_pdf():
    """Generate a downloadable weekly finance PDF report."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    lines = build_weekly_finance_report_lines(user_state, user_id=user_id)
    pdf_bytes = build_simple_pdf_from_lines(lines, title="Weekly Finance Report")
    response = app.response_class(pdf_bytes, mimetype="application/pdf")
    response.headers["Content-Disposition"] = "attachment; filename=weekly_finance_report.pdf"
    response.headers["Cache-Control"] = "no-store"
    return response


@app.route("/api/finance/geopolitical/suppliers", methods=["GET", "POST", "DELETE"])
def api_finance_geopolitical_suppliers():
    """Manage supplier exposure profiles used by horizon scanning."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    geo_profile = user_state.get("geopolitical_profile") or {}

    if request.method == "GET":
        return jsonify({
            "user_id": user_id,
            "home_country": HOME_COUNTRY,
            "suppliers": geo_profile.get("suppliers") or [],
            "last_scan_at": geo_profile.get("last_scan_at") or "",
        })

    if reject_large_request(8192):
        return jsonify({"error": "Payload too large."}), 413
    data = request.get_json(silent=True) or {}

    if request.method == "POST":
        name = (data.get("name") or "").strip()
        country = (data.get("country") or "Unknown").strip()
        material = (data.get("material") or "other").strip().lower()
        if not name:
            return jsonify({"error": "name is required."}), 400
        try:
            quality_score = float(data.get("quality_score") or data.get("quality") or 75.0)
        except Exception:
            quality_score = 75.0
        try:
            spend_share = float(data.get("spend_share") or 0.0)
        except Exception:
            spend_share = 0.0

        row = {
            "name": name,
            "country": country,
            "material": material,
            "quality_score": max(0.0, min(100.0, quality_score)),
            "spend_share": max(0.0, spend_share),
            "updated_at": utc_now_iso(),
        }

        suppliers = geo_profile.get("suppliers") or []
        existing = None
        for item in suppliers:
            if normalize_case(item.get("name")) == normalize_case(name):
                existing = item
                break
        if existing:
            existing.update(row)
        else:
            suppliers.append(row)
        geo_profile["suppliers"] = suppliers[:200]
        user_state["geopolitical_profile"] = geo_profile
        analytics_sql_upsert_supplier(user_id, row)
        save_user_state(user_id, user_state)
        return jsonify({"status": "ok", "user_id": user_id, "suppliers": geo_profile["suppliers"]})

    name = (data.get("name") or "").strip()
    clear_all = parse_bool(data.get("clear"), default=False)
    suppliers = geo_profile.get("suppliers") or []
    if clear_all:
        suppliers = []
    else:
        if not name:
            return jsonify({"error": "name is required unless clear=true."}), 400
        suppliers = [row for row in suppliers if normalize_case(row.get("name")) != normalize_case(name)]
        analytics_sql_delete_supplier(user_id, name)
    geo_profile["suppliers"] = suppliers
    user_state["geopolitical_profile"] = geo_profile
    save_user_state(user_id, user_state)
    return jsonify({"status": "ok", "user_id": user_id, "suppliers": suppliers})


@app.route("/api/finance/geopolitical/scan", methods=["GET"])
def api_finance_geopolitical_scan():
    """Run geopolitical and regulatory horizon scan against supplier exposure."""
    mark_user_activity()
    session_user_id = resolve_session_user_id()
    user_id = sanitize_user_id(session_user_id or request.args.get("user_id") or DEFAULT_USER_ID)
    include_sources = parse_bool(request.args.get("include_sources"), default=False)
    user_state = ensure_finance_profiles(load_user_state(user_id))
    report_text, sources = build_geopolitical_horizon_report(user_id, user_state, include_sources=include_sources)
    save_user_state(user_id, user_state)
    return jsonify({
        "user_id": user_id,
        "as_of_utc": utc_now_iso(),
        "home_country": HOME_COUNTRY,
        "report": report_text,
        "sources": sources,
    })


@app.route("/api/charts/generate", methods=["POST"])
def api_generate_chart():
    """Generate a chart URL/config from natural language or explicit chart payload."""
    mark_user_activity()
    if reject_large_request(16384):
        return jsonify({"error": "Payload too large."}), 413

    data = request.get_json(silent=True) or {}
    prompt = (data.get("prompt") or "").strip()
    chart_spec = data.get("chart_spec")

    if chart_spec and isinstance(chart_spec, dict):
        spec = {
            "chart_type": chart_spec.get("chart_type") or "line",
            "title": chart_spec.get("title") or "User Requested Chart",
            "labels": chart_spec.get("labels") or [],
            "values": chart_spec.get("values") or [],
            "x_label": chart_spec.get("x_label") or "",
            "y_label": chart_spec.get("y_label") or "",
        }
        if not spec["values"]:
            return jsonify({"error": "chart_spec.values is required."}), 400
    else:
        if not prompt:
            return jsonify({"error": "Provide prompt or chart_spec."}), 400
        parsed = parse_graph_request(prompt)
        if not parsed:
            return jsonify({"error": "Could not parse chart request from prompt."}), 400
        if parsed.get("error"):
            return jsonify({"error": parsed.get("error")}), 400
        spec = parsed

    chart_url, cfg = build_quickchart_url(spec)
    return jsonify({
        "status": "ok",
        "as_of_utc": utc_now_iso(),
        "chart_url": chart_url,
        "chart_spec": spec,
        "chart_config": cfg,
    })


@app.route("/IMG_9664.jpeg")
def original_background():
    return send_file("IMG_9664.jpeg")


@app.route("/1.JPG")
def background():
    return send_file("1.JPG")


@app.route("/IMG_8639.JPG")
def message_background():
    return send_file("IMG_8639.JPG")


@app.route("/IMG_6146.JPG")
def chat_background():
    return send_file("IMG_6146.JPG")


if __name__ == "__main__":
    import sys
    start_idle_learning_worker_once()
    start_upload_cleanup_worker_once()
    host = os.getenv("HOST", "0.0.0.0")
    port = int(os.getenv("PORT", "5004"))
    debug_mode = os.getenv("FLASK_DEBUG", "0") in {"1", "true", "True"}
    
    # Check for command-line arguments
    if len(sys.argv) > 1 and sys.argv[1].lower() == "chat":
        # Run console chat loop
        chat_loop()
    else:
        # Run Flask web server
        app.run(debug=debug_mode, host=host, port=port)

