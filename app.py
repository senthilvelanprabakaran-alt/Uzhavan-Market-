"""
Mandi Vilai - Crop Price Alert - Flask backend
Run with: python app.py
"""

import os
import re
import ssl
import smtplib
import secrets
import logging
import traceback
from email.message import EmailMessage
from datetime import datetime, timedelta
from functools import wraps

import jwt
import requests
from flask import Flask, request, jsonify, session, g, send_from_directory
from flask_cors import CORS
from werkzeug.security import generate_password_hash, check_password_hash
import mysql.connector
from mysql.connector import pooling
from dotenv import load_dotenv

load_dotenv()

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
logger = logging.getLogger("mandi_vilai")

# ==========================================================
# APP CONFIG
# ==========================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", secrets.token_hex(32))

app.config.update(
    SESSION_COOKIE_HTTPONLY=True,          # JS on the page can never read the session cookie
    SESSION_COOKIE_SAMESITE="Lax",         # blocks most CSRF vectors on state-changing requests
    SESSION_COOKIE_SECURE=os.environ.get("FLASK_ENV") == "production",  # HTTPS-only in prod
    PERMANENT_SESSION_LIFETIME=timedelta(days=30),
)

# Allow the frontend origin to send credentials (cookies, used only by the
# admin panel) cross-origin during dev. In production, lock this down to
# your real domain. Farmer auth no longer uses cookies at all (see JWT
# CONFIG below) — it sends the token in an Authorization header instead,
# so it isn't affected by this setting.
CORS(app, supports_credentials=True, origins=os.environ.get("FRONTEND_ORIGIN", "*"))

# ==========================================================
# JWT CONFIG — farmer auth
# Farmers sign in with email + password and get back a signed JWT, which
# the frontend stores in localStorage and sends as
# "Authorization: Bearer <token>" on every request. No server-side session
# or DB table is needed for this — the token itself is proof of identity
# until it expires, which is what makes it "stateless" auth. Admin auth is
# unchanged and still uses Flask's cookie session (see ADMIN AUTH below) —
# the two are independent.
# ==========================================================
JWT_SECRET = os.environ.get("JWT_SECRET", app.secret_key)
JWT_ALGORITHM = "HS256"
JWT_EXPIRY_DAYS = int(os.environ.get("JWT_EXPIRY_DAYS", 30))


def generate_jwt(farmer_id: int, email: str, name: str) -> str:
    payload = {
        "farmer_id": farmer_id,
        "email": email,
        "name": name or "",
        "iat": datetime.utcnow(),
        "exp": datetime.utcnow() + timedelta(days=JWT_EXPIRY_DAYS),
    }
    return jwt.encode(payload, JWT_SECRET, algorithm=JWT_ALGORITHM)


def decode_jwt(token: str):
    try:
        return jwt.decode(token, JWT_SECRET, algorithms=[JWT_ALGORITHM])
    except jwt.ExpiredSignatureError:
        return None
    except jwt.InvalidTokenError:
        return None


# ==========================================================
# DB MIGRATION NOTE (run once):
#
#   ALTER TABLE farmers CHANGE phone email VARCHAR(254) NOT NULL UNIQUE;
#   ALTER TABLE subscriptions ADD COLUMN created_at TIMESTAMP
#       DEFAULT CURRENT_TIMESTAMP;
#   ALTER TABLE subscriptions ADD COLUMN last_notified_price DECIMAL(10,2) NULL;
#   ALTER TABLE subscriptions ADD COLUMN last_notified_at TIMESTAMP NULL;
#
#   -- Farmer ratings of mandis (fair prices / reliability), used to
#   -- show avgRating/ratingCount alongside each mandi's price:
#   CREATE TABLE mandi_ratings (
#       rating_id INT AUTO_INCREMENT PRIMARY KEY,
#       farmer_id INT NOT NULL,
#       mandi_id  INT NOT NULL,
#       rating    TINYINT NOT NULL CHECK (rating BETWEEN 1 AND 5),
#       rated_at  TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
#       FOREIGN KEY (farmer_id) REFERENCES farmers(farmer_id) ON DELETE CASCADE,
#       FOREIGN KEY (mandi_id) REFERENCES mandis(mandi_id) ON DELETE CASCADE,
#       UNIQUE KEY uq_farmer_mandi (farmer_id, mandi_id)
#   );
#
#   ALTER TABLE prices ADD COLUMN is_estimated TINYINT(1) NOT NULL DEFAULT 0;
#   ALTER TABLE commodities ADD UNIQUE KEY uq_commodity_name (commodity_name);
#   ALTER TABLE mandis ADD UNIQUE KEY uq_mandi_name_district (mandi_name, district);
#
#   -- Needed for admin "add/update price" to upsert cleanly, and so the
#   -- admin CRUD routes below can rely on FK errors (409) instead of
#   -- silently orphaning rows when a crop/mandi/farmer is deleted:
#   ALTER TABLE prices ADD UNIQUE KEY uq_price_commodity_mandi_date (commodity_id, mandi_id, price_date);
#
#   -- Switched from OTP-based sign-in to email+password+JWT — OTP and the
#   -- "trusted device" cookie/table are gone, replaced by a stored password
#   -- hash. If you have an existing trusted_devices table from an older
#   -- version of this app, it's no longer used and can be dropped:
#   ALTER TABLE farmers ADD COLUMN password_hash VARCHAR(255) NOT NULL DEFAULT '';
#   DROP TABLE IF EXISTS trusted_devices;
# ==========================================================

# ==========================================================
# DATABASE — connection pool, all queries parameterized
# ==========================================================
db_pool = pooling.MySQLConnectionPool(
    pool_name="crop_price_pool",
    pool_size=5,
    host=os.environ.get("DB_HOST", "localhost"),
    user=os.environ.get("DB_USER", "root"),
    password=os.environ.get("DB_PASSWORD", ""),
    database=os.environ.get("DB_NAME", "crop_price_alert"),
)


def get_db():
    return db_pool.get_connection()


# ==========================================================
# FRONTEND — serve index.html at the root URL
# index.html lives in the same folder as this file and calls the
# API at a relative "/api" path, so it must be served by this same
# Flask app (not opened directly / via Live Server) for fetch() calls
# and the session cookie to work.
# ==========================================================
@app.route("/")
def serve_index():
    return send_from_directory(BASE_DIR, "index.html")


@app.route("/admin")
@app.route("/admin.html")
def serve_admin():
    return send_from_directory(BASE_DIR, "admin.html")


# ==========================================================
# LOGIN ATTEMPT LIMITER
# In-memory for the MVP (swap for Redis before real multi-worker
# deployment). Slows down password-guessing against a single email —
# unrelated to the JWT itself, which has no attempt limit of its own
# since it's just a signature check.
# ==========================================================
login_attempt_log = {}   # email -> [timestamps of recent failed attempts]

LOGIN_MAX_ATTEMPTS_PER_WINDOW = 5
LOGIN_ATTEMPT_WINDOW_MINUTES = 10

EMAIL_RE = re.compile(r"^[^\s@]+@[^\s@]+\.[^\s@]+$")
MIN_PASSWORD_LENGTH = 6


def is_login_rate_limited(email: str) -> bool:
    now = datetime.utcnow()
    window_start = now - timedelta(minutes=LOGIN_ATTEMPT_WINDOW_MINUTES)
    recent = [t for t in login_attempt_log.get(email, []) if t > window_start]
    login_attempt_log[email] = recent
    return len(recent) >= LOGIN_MAX_ATTEMPTS_PER_WINDOW


def record_failed_login(email: str):
    login_attempt_log.setdefault(email, []).append(datetime.utcnow())


def clear_failed_logins(email: str):
    login_attempt_log.pop(email, None)

# ==========================================================
# TAMIL NADU DISTRICTS
# Canonical list so free-text district input from the frontend can be
# validated/normalized instead of silently accepting typos. Matches the
# dropdown shipped in index.html.
# ==========================================================
TN_DISTRICTS = [
    "Chennai", "Coimbatore", "Madurai", "Tiruchirappalli", "Salem", "Tirunelveli",
    "Vellore", "Erode", "Thanjavur", "Dindigul", "Cuddalore", "Kanchipuram",
    "Karur", "Namakkal", "Virudhunagar", "Thoothukudi", "Kanyakumari", "Krishnagiri",
    "Dharmapuri", "Villupuram", "Pudukkottai", "Ramanathapuram", "Theni", "Ariyalur",
    "Perambalur", "The Nilgiris (Ooty)", "Sivagangai", "Tiruvannamalai", "Nagapattinam",
    "Tiruvarur", "Tenkasi", "Tirupathur", "Ranipet", "Chengalpattu", "Kallakurichi",
    "Mayiladuthurai", "Hosur",
]
TN_DISTRICTS_LOWER = {d.lower(): d for d in TN_DISTRICTS}


def normalize_district(raw: str):
    """Case-insensitive match against TN_DISTRICTS. Returns the canonical
    name, or None if it isn't recognized."""
    return TN_DISTRICTS_LOWER.get(str(raw).strip().lower())


# ==========================================================
# ANY-CROP PRICE ESTIMATION
# The real pipeline populates `prices` from official mandi data, but a
# farmer can type ANY crop name — including ones the ingestion job hasn't
# covered yet, or that aren't in `commodities` at all. Rather than a hard
# 404, we:
#   1. auto-create the commodity if it doesn't exist yet (so the real
#      ingestion job can start filling it in later), and
#   2. if there's no real price row for it, derive a stable, clearly
#      labeled "estimated" price instead of failing — same crop+mandi
#      always yields the same estimate, it just isn't official data.
# Estimated rows are marked prices.is_estimated = 1 (see migration note)
# so /api/prices/nearest and the frontend can flag them honestly.
# ==========================================================
CROP_BASE_PRICES = {
    "tomato": 1400, "onion": 1600, "paddy": 2100, "rice": 3200, "banana": 1200,
    "chilli": 12000, "cotton": 6800, "maize": 2000, "groundnut": 5800, "potato": 1300,
    "brinjal": 1500, "okra": 1900, "garlic": 8500, "ginger": 6000, "turmeric": 9500,
    "sugarcane": 320, "coconut": 2800, "mango": 4500, "grapes": 4200, "cashew": 15000,
    "coffee": 22000, "tea": 18000, "pepper": 55000, "cardamom": 120000, "sesame": 9800,
    "sunflower": 6200, "soybean": 4600, "mustard": 5400, "jowar": 3000, "bajra": 2500,
    "ragi": 3400, "moong": 7500, "gram": 5200, "wheat": 2600, "cabbage": 1100,
    "cauliflower": 1600, "carrot": 2200, "beans": 3400, "peas": 4200, "jute": 4800,
    "apple": 8000, "papaya": 1600, "watermelon": 900, "lemon": 3800,
}


def stable_hash(text: str) -> int:
    """Deterministic (process-independent) hash, unlike Python's salted
    built-in hash() — needed so estimates stay the same across restarts."""
    return int(hashlib.sha256(text.encode()).hexdigest(), 16)


def get_base_price(crop_key: str) -> float:
    if crop_key in CROP_BASE_PRICES:
        return CROP_BASE_PRICES[crop_key]
    h = stable_hash(crop_key)
    return 700 + (h % 7500)


def estimate_price(crop_key: str, mandi_name: str) -> float:
    base = get_base_price(crop_key)
    h = stable_hash(f"{crop_key}:{mandi_name}")
    variance = ((h % 240) - 120) / 1000.0  # -12% .. +12%
    return max(200.0, round(base * (1 + variance), 2))


def estimate_trend(crop_key: str, mandi_name: str):
    h = stable_hash(f"{crop_key}:{mandi_name}:trend")
    if h % 3 == 0:
        return "flat", 0
    pct = h % 12
    return ("up" if h % 2 == 0 else "down"), pct


def get_or_create_commodity(cursor, crop_name: str):
    normalized = crop_name.strip().title()
    cursor.execute(
        "SELECT commodity_id, commodity_name FROM commodities WHERE commodity_name = %s",
        (normalized,),
    )
    row = cursor.fetchone()
    if row:
        return row["commodity_id"], row["commodity_name"]

    cursor.execute(
        "INSERT INTO commodities (commodity_name) VALUES (%s)", (normalized,)
    )
    return cursor.lastrowid, normalized


def get_or_create_mandi(cursor, mandi_name: str, district: str):
    cursor.execute(
        "SELECT mandi_id FROM mandis WHERE mandi_name = %s AND district = %s",
        (mandi_name, district),
    )
    row = cursor.fetchone()
    if row:
        return row["mandi_id"]

    cursor.execute(
        "INSERT INTO mandis (mandi_name, district) VALUES (%s, %s)",
        (mandi_name, district),
    )
    return cursor.lastrowid


def ensure_estimated_price_row(cursor, commodity_id, mandi_id, price):
    """Best-effort: persist today's estimate so re-queries and the
    ratings/alerts features have a real prices row to attach to. Safe to
    call repeatedly — INSERT IGNORE keeps the first value for the day."""
    try:
        cursor.execute(
            """INSERT IGNORE INTO prices (commodity_id, mandi_id, modal_price, price_date, is_estimated)
               VALUES (%s, %s, %s, CURDATE(), 1)""",
            (commodity_id, mandi_id, price),
        )
    except mysql.connector.Error as exc:
        # If the is_estimated column hasn't been migrated in yet, degrade
        # gracefully rather than breaking the whole request.
        logger.warning("[PRICE ESTIMATE] could not persist estimate (migration pending?): %s", exc)


def generate_estimated_mandis(cursor, crop_name: str, district: str, limit: int, persist=True):
    crop_key = crop_name.strip().lower()
    district = district or "Chennai"
    others = [d for d in TN_DISTRICTS if d != district]
    ranked = sorted(others, key=lambda p: stable_hash(f"{crop_key}:{p}"))
    markets = ([district] + ranked)[:limit]

    commodity_id = None
    if persist:
        commodity_id, _ = get_or_create_commodity(cursor, crop_name)

    results = []
    for place in markets:
        mandi_name = f"{place} Market"
        price = estimate_price(crop_key, mandi_name)
        trend, trend_pct = estimate_trend(crop_key, mandi_name)
        mandi_id = None
        if persist and commodity_id:
            mandi_id = get_or_create_mandi(cursor, mandi_name, place)
            ensure_estimated_price_row(cursor, commodity_id, mandi_id, price)
        results.append({
            "mandiId": mandi_id,
            "name": mandi_name,
            "district": place,
            "distanceKm": None,
            "price": price,
            "trend": trend,
            "trendPct": trend_pct,
            "stale": False,
            "updatedAt": datetime.utcnow().date().isoformat(),
            "avgRating": None,
            "ratingCount": 0,
            "estimated": True,
        })
    return sorted(results, key=lambda r: r["price"], reverse=True)


# ==========================================================
# TRUSTED DEVICES — lets a farmer skip OTP entirely on a device that
# already verified their email before, without trusting the email text
# itself (which anyone could type). Trust lives in a long random,
# httponly, secure cookie whose HASH is checked against this device's
# row in the DB and matched to the specific email being signed in with.
# Logging out clears the session but intentionally leaves the device
# trusted, so "already verified" really means "already verified here".
# ==========================================================
TRUSTED_DEVICE_COOKIE = "mv_device"
TRUSTED_DEVICE_DAYS = 90


def hash_device_token(token: str) -> str:
    return hashlib.sha256(f"{token}:{app.secret_key}".encode()).hexdigest()


def issue_trusted_device(response, farmer_id: int):
    token = secrets.token_urlsafe(32)
    token_hash = hash_device_token(token)
    expires_at = datetime.utcnow() + timedelta(days=TRUSTED_DEVICE_DAYS)

    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute(
            """INSERT INTO trusted_devices (farmer_id, token_hash, expires_at)
               VALUES (%s, %s, %s)""",
            (farmer_id, token_hash, expires_at),
        )
        conn.commit()
    finally:
        cursor.close()
        conn.close()

    response.set_cookie(
        TRUSTED_DEVICE_COOKIE,
        token,
        max_age=TRUSTED_DEVICE_DAYS * 24 * 3600,
        httponly=True,
        samesite="Lax",
        secure=os.environ.get("FLASK_ENV") == "production",
    )


def get_trusted_farmer_for_email(email: str):
    """Returns the farmer row if this device holds a still-valid trust
    token AND that token belongs to a farmer with this exact email."""
    token = request.cookies.get(TRUSTED_DEVICE_COOKIE)
    if not token:
        return None

    token_hash = hash_device_token(token)
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute(
            """SELECT f.farmer_id, f.name, f.district, f.email
               FROM trusted_devices td
               JOIN farmers f ON f.farmer_id = td.farmer_id
               WHERE td.token_hash = %s AND td.expires_at > NOW() AND f.email = %s""",
            (token_hash, email),
        )
        return cursor.fetchone()
    finally:
        cursor.close()
        conn.close()


def hash_otp(email: str, code: str) -> str:
    # Salting with the email is enough here since OTPs are short-lived and single-use.
    return hashlib.sha256(f"{email}:{code}:{app.secret_key}".encode()).hexdigest()


def is_rate_limited(email: str) -> bool:
    now = datetime.utcnow()
    window_start = now - timedelta(minutes=OTP_REQUEST_WINDOW_MINUTES)
    recent = [t for t in otp_request_log.get(email, []) if t > window_start]
    otp_request_log[email] = recent
    return len(recent) >= OTP_MAX_REQUESTS_PER_WINDOW


def record_otp_request(email: str):
    otp_request_log.setdefault(email, []).append(datetime.utcnow())


# ==========================================================
# EMAIL — isolated in one function so swapping providers later
# only touches this one place.
#
# Two ways to send, tried in this order:
#   1. RESEND_API_KEY set -> HTTPS API call (port 443). Recommended:
#      many college/office networks block outbound SMTP ports
#      (25 / 465 / 587) the same way yours blocked Groq for Zivo —
#      an HTTPS API call looks like normal web traffic and isn't
#      affected by that.
#   2. SMTP_HOST set -> plain SMTP (Gmail, SendGrid/Mailgun/Postmark
#      relay, or any other standard SMTP provider).
#   3. Neither set -> dev mode, prints to the console instead of
#      sending so you can test without any credentials.
#
# If mail "isn't coming", check the terminal running `python app.py` —
# every failure below is now logged with the real exception instead
# of failing silently. Common causes:
#   - Gmail: you must use a 16-character App Password (Google Account
#     -> Security -> 2-Step Verification -> App passwords), NOT your
#     normal login password. A normal password fails with
#     "Username and Password not accepted".
#   - College/office wifi blocking outbound SMTP ports -> switch to
#     RESEND_API_KEY (or any HTTP-based provider) instead of SMTP_HOST.
#   - .env not being picked up -> hit GET /api/debug/email-config
#     (only enabled outside FLASK_ENV=production) to see which vars
#     Flask actually loaded, without exposing the secret values.
# ==========================================================
RESEND_API_KEY = os.environ.get("RESEND_API_KEY")
SMTP_HOST = os.environ.get("SMTP_HOST")
SMTP_PORT = int(os.environ.get("SMTP_PORT", 587))
SMTP_USER = os.environ.get("SMTP_USER")
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD")
EMAIL_FROM = os.environ.get("EMAIL_FROM", SMTP_USER or "no-reply@mandivilai.app")
EMAIL_FROM_NAME = os.environ.get("EMAIL_FROM_NAME", "Mandi Vilai")


def _send_via_resend(to_email: str, subject: str, text_body: str, html_body: str) -> bool:
    try:
        resp = requests.post(
            "https://api.resend.com/emails",
            headers={
                "Authorization": f"Bearer {RESEND_API_KEY}",
                "Content-Type": "application/json",
            },
            json={
                "from": f"{EMAIL_FROM_NAME} <{EMAIL_FROM}>",
                "to": [to_email],
                "subject": subject,
                "text": text_body,
                "html": html_body,
            },
            timeout=10,
        )
        if resp.status_code >= 400:
            logger.error("[EMAIL ERROR] Resend API rejected the request (%s): %s",
                         resp.status_code, resp.text)
            return False
        return True
    except requests.RequestException:
        logger.error("[EMAIL ERROR] Resend API call failed:\n%s", traceback.format_exc())
        return False


def _send_via_smtp(to_email: str, subject: str, text_body: str, html_body: str) -> bool:
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = f"{EMAIL_FROM_NAME} <{EMAIL_FROM}>"
    msg["To"] = to_email
    msg.set_content(text_body)
    msg.add_alternative(html_body, subtype="html")

    try:
        context = ssl.create_default_context()
        with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=10) as server:
            server.starttls(context=context)
            if SMTP_USER and SMTP_PASSWORD:
                server.login(SMTP_USER, SMTP_PASSWORD)
            server.send_message(msg)
        return True
    except smtplib.SMTPAuthenticationError:
        logger.error(
            "[EMAIL ERROR] SMTP login rejected for %s. If this is Gmail, you need a "
            "16-character App Password, not your normal password.", SMTP_USER
        )
        return False
    except (TimeoutError, OSError) as exc:
        logger.error(
            "[EMAIL ERROR] could not reach %s:%s (%s). This looks like the network is "
            "blocking outbound SMTP — try RESEND_API_KEY instead, which sends over HTTPS.",
            SMTP_HOST, SMTP_PORT, exc,
        )
        return False
    except Exception:
        logger.error("[EMAIL ERROR] could not send to %s:\n%s", to_email, traceback.format_exc())
        return False


def email_delivery_mode() -> str:
    if RESEND_API_KEY:
        return "resend"
    if SMTP_HOST:
        return "smtp"
    return "dev"


def send_email(to_email: str, subject: str, text_body: str, html_body: str) -> bool:
    if RESEND_API_KEY:
        return _send_via_resend(to_email, subject, text_body, html_body)

    if SMTP_HOST:
        return _send_via_smtp(to_email, subject, text_body, html_body)

    # Dev mode: print instead of sending, so you can test without email credentials
    logger.info("[DEV EMAIL] to %s: %s\n%s", to_email, subject, text_body)
    return True


def send_otp_email(to_email: str, code: str) -> bool:
    subject = f"Your Mandi Vilai code is {code}"
    text_body = (
        f"Your Mandi Vilai verification code is {code}.\n"
        f"It expires in {OTP_TTL_MINUTES} minutes.\n\n"
        f"If you didn't request this, you can ignore this email."
    )
    html_body = f"""\
<div style="font-family:Arial,sans-serif;max-width:420px;margin:0 auto;padding:32px 24px;
            background:#F4FAF7;border-radius:16px;">
  <p style="font-size:14px;color:#4E5B53;margin:0 0 4px;">Mandi Vilai</p>
  <h2 style="font-size:20px;color:#0E2A1E;margin:0 0 20px;">Your verification code</h2>
  <div style="font-size:36px;font-weight:700;letter-spacing:6px;color:#1B4332;
              background:#fff;border:2px solid #DDE4DE;border-radius:12px;
              padding:16px;text-align:center;margin-bottom:16px;">{code}</div>
  <p style="font-size:13px;color:#4E5B53;margin:0;">
    This code expires in {OTP_TTL_MINUTES} minutes. If you didn't request it, you can safely ignore this email.
  </p>
</div>"""
    sent = send_email(to_email, subject, text_body, html_body)
    if not sent:
        logger.error("[EMAIL ERROR] OTP email to %s did not send — see the error above.", to_email)
    return sent


def send_price_alert_email(to_email: str, crop_label: str, mandi_name: str,
                            old_price: float, new_price: float) -> bool:
    direction = "up" if new_price > old_price else "down"
    diff = abs(new_price - old_price)
    pct = round(diff / old_price * 100, 1) if old_price else 0
    arrow = "▲" if direction == "up" else "▼"
    color = "#1B4332" if direction == "up" else "#C1401F"

    subject = f"{crop_label} price {direction} {pct}% at {mandi_name}"
    text_body = (
        f"{crop_label} at {mandi_name} moved from ₹{old_price:,.0f} to ₹{new_price:,.0f} "
        f"({direction} {pct}%).\n\nOpen Mandi Vilai to see all mandis for this crop."
    )
    html_body = f"""\
<div style="font-family:Arial,sans-serif;max-width:420px;margin:0 auto;padding:32px 24px;
            background:#F4FAF7;border-radius:16px;">
  <p style="font-size:14px;color:#4E5B53;margin:0 0 4px;">Mandi Vilai price alert</p>
  <h2 style="font-size:20px;color:#0E2A1E;margin:0 0 20px;">{crop_label} · {mandi_name}</h2>
  <div style="background:#fff;border:2px solid #DDE4DE;border-radius:12px;padding:20px;text-align:center;">
    <span style="font-size:15px;color:#4E5B53;text-decoration:line-through;">₹{old_price:,.0f}</span>
    <div style="font-size:32px;font-weight:700;color:{color};margin-top:6px;">
      {arrow} ₹{new_price:,.0f}
    </div>
    <div style="font-size:14px;color:{color};font-weight:600;margin-top:4px;">
      {pct}% {direction}
    </div>
  </div>
  <p style="font-size:13px;color:#4E5B53;margin-top:16px;">
    You're getting this because you're tracking {crop_label} on Mandi Vilai.
  </p>
</div>"""
    return send_email(to_email, subject, text_body, html_body)


# ==========================================================
# AUTH HELPERS
# ==========================================================
def login_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if "farmer_id" not in session:
            return jsonify({"error": "Not signed in"}), 401
        return f(*args, **kwargs)
    return wrapper


def valid_email(email: str) -> bool:
    return bool(email) and len(email) <= 254 and bool(EMAIL_RE.fullmatch(email))


# ==========================================================
# ADMIN AUTH
# Single admin account via env vars (no extra table/migration needed).
# Set ADMIN_USERNAME / ADMIN_PASSWORD in your .env before deploying —
# if ADMIN_PASSWORD is unset, admin login is disabled entirely rather
# than falling back to a guessable default.
# ==========================================================
ADMIN_USERNAME = os.environ.get("ADMIN_USERNAME", "admin")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD")


def admin_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if not session.get("is_admin"):
            return jsonify({"error": "Admin sign-in required"}), 401
        return f(*args, **kwargs)
    return wrapper


# ==========================================================
# ROUTE: GET/POST /api/profile
# Farmer's name + district. Asked once right after first sign-in
# (see isNewUser in verify-otp) so /api/prices/nearest has a real
# district to bias results toward, and the dashboard can greet the
# farmer by name.
# ==========================================================
@app.route("/api/profile", methods=["GET"])
@login_required
def get_profile():
    farmer_id = session["farmer_id"]
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute(
            "SELECT name, email, district FROM farmers WHERE farmer_id = %s", (farmer_id,)
        )
        farmer = cursor.fetchone()
        return jsonify(farmer or {}), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/profile", methods=["POST"])
@login_required
def update_profile():
    data = request.get_json(silent=True) or {}
    name = str(data.get("name", "")).strip()[:100]
    district_raw = str(data.get("district", "")).strip()[:100]

    if not name:
        return jsonify({"error": "Name is required"}), 400
    if not district_raw:
        return jsonify({"error": "District is required"}), 400

    district = normalize_district(district_raw)
    if not district:
        return jsonify({
            "error": "Unrecognized Tamil Nadu district",
            "validDistricts": TN_DISTRICTS,
        }), 400

    farmer_id = session["farmer_id"]
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute(
            "UPDATE farmers SET name = %s, district = %s WHERE farmer_id = %s",
            (name, district, farmer_id),
        )
        conn.commit()
        session["name"] = name
        return jsonify({"message": "Profile updated", "name": name, "district": district}), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# EMAIL CHANGE — a signed-in farmer can update their email, but it
# must be re-verified via OTP (same as sign-in) before it takes effect,
# and both the old and new address get notified once it does. Kept in
# its own in-memory store (like otp_store) rather than a table, since
# it's short-lived, single-farmer-at-a-time state.
# ==========================================================
email_change_store = {}   # farmer_id -> {new_email, hash, expires_at, attempts, old_email}


@app.route("/api/profile/email/request-change", methods=["POST"])
@login_required
def request_email_change():
    data = request.get_json(silent=True) or {}
    new_email = str(data.get("newEmail", "")).strip().lower()
    farmer_id = session["farmer_id"]
    old_email = session.get("email", "")

    if not valid_email(new_email):
        return jsonify({"error": "Enter a valid email address"}), 400
    if new_email == old_email:
        return jsonify({"error": "That's already your current email"}), 400

    if is_rate_limited(f"emailchange:{farmer_id}"):
        return jsonify({"error": "Too many attempts. Try again in a few minutes."}), 429

    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute("SELECT farmer_id FROM farmers WHERE email = %s", (new_email,))
        if cursor.fetchone():
            return jsonify({"error": "That email is already in use by another account"}), 409
    finally:
        cursor.close()
        conn.close()

    code = "".join(str(random.randint(0, 9)) for _ in range(OTP_LENGTH))
    email_change_store[farmer_id] = {
        "new_email": new_email,
        "old_email": old_email,
        "hash": hash_otp(new_email, code),
        "expires_at": datetime.utcnow() + timedelta(minutes=OTP_TTL_MINUTES),
        "attempts": 0,
    }
    record_otp_request(f"emailchange:{farmer_id}")

    if not send_otp_email(new_email, code):
        return jsonify({"error": "Could not send the code. Try again shortly."}), 502

    # Let the farmer know at their OLD address too, in case the change wasn't
    # them — this is purely informational, doesn't block anything.
    if old_email:
        send_email(
            old_email,
            "Email change requested on your Mandi Vilai account",
            f"Someone requested changing your Mandi Vilai account email to {new_email}. "
            f"If this wasn't you, you can ignore this — no change happens until the new "
            f"address is verified.",
            f"<p style='font-family:Arial,sans-serif'>Someone requested changing your Mandi "
            f"Vilai account email to <strong>{new_email}</strong>. If this wasn't you, ignore "
            f"this — nothing changes until that address is verified.</p>",
        )

    response = {"message": "Verification code sent to new email"}
    is_dev_mode = email_delivery_mode() == "dev" and os.environ.get("FLASK_ENV") != "production"
    if is_dev_mode:
        response["devModeCode"] = code
        response["devModeNote"] = "No email provider configured — this code was not actually emailed."
    return jsonify(response), 200


@app.route("/api/profile/email/confirm-change", methods=["POST"])
@login_required
def confirm_email_change():
    data = request.get_json(silent=True) or {}
    code = str(data.get("code", "")).strip()
    farmer_id = session["farmer_id"]

    record = email_change_store.get(farmer_id)
    if not record:
        return jsonify({"error": "No email change was requested"}), 400
    if datetime.utcnow() > record["expires_at"]:
        del email_change_store[farmer_id]
        return jsonify({"error": "Code expired. Request the change again."}), 400
    if record["attempts"] >= OTP_MAX_VERIFY_ATTEMPTS:
        del email_change_store[farmer_id]
        return jsonify({"error": "Too many incorrect attempts. Request the change again."}), 429
    if hash_otp(record["new_email"], code) != record["hash"]:
        record["attempts"] += 1
        return jsonify({"error": "Incorrect code"}), 400

    new_email, old_email = record["new_email"], record["old_email"]
    del email_change_store[farmer_id]

    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute(
            "UPDATE farmers SET email = %s WHERE farmer_id = %s", (new_email, farmer_id)
        )
        conn.commit()
    except mysql.connector.Error:
        return jsonify({"error": "That email is already in use by another account"}), 409
    finally:
        cursor.close()
        conn.close()

    session["email"] = new_email
    for addr, note in ((new_email, "This is now the email for your Mandi Vilai account."),
                       (old_email, "Your Mandi Vilai account email was changed away from this address.")):
        if addr:
            send_email(addr, "Your Mandi Vilai account email was changed",
                       f"{note}\n\nNew email: {new_email}",
                       f"<p style='font-family:Arial,sans-serif'>{note}</p><p>New email: <strong>{new_email}</strong></p>")

    return jsonify({"message": "Email updated", "email": new_email}), 200


# ==========================================================
# ROUTE: POST /api/auth/send-otp
# ==========================================================
@app.route("/api/auth/send-otp", methods=["POST"])
def send_otp():
    data = request.get_json(silent=True) or {}
    email = str(data.get("email", "")).strip().lower()

    if not valid_email(email):
        return jsonify({"error": "Enter a valid email address"}), 400

    # This device already verified this exact email before — no need to
    # send another OTP, sign the farmer straight in.
    trusted = get_trusted_farmer_for_email(email)
    if trusted:
        needs_profile = not trusted["name"] or not trusted["district"]
        session.clear()
        session.permanent = True
        session["farmer_id"] = trusted["farmer_id"]
        session["email"] = trusted["email"]
        session["name"] = trusted["name"] or ""

        response = jsonify({
            "message": "Signed in",
            "skipVerification": True,
            "isNewUser": False,
            "needsProfile": needs_profile,
            "email": trusted["email"],
            "name": trusted["name"] or "",
            "district": trusted["district"] or "",
        })
        issue_trusted_device(response, trusted["farmer_id"])  # rolling expiry
        return response, 200

    if is_rate_limited(email):
        return jsonify({"error": "Too many attempts. Try again in a few minutes."}), 429

    code = "".join(str(random.randint(0, 9)) for _ in range(OTP_LENGTH))

    otp_store[email] = {
        "hash": hash_otp(email, code),
        "expires_at": datetime.utcnow() + timedelta(minutes=OTP_TTL_MINUTES),
        "attempts": 0,
    }
    record_otp_request(email)

    if not send_otp_email(email, code):
        return jsonify({"error": "Could not send the code. Try again shortly."}), 502

    response = {"message": "OTP sent"}
    is_dev_mode = email_delivery_mode() == "dev" and os.environ.get("FLASK_ENV") != "production"
    if is_dev_mode:
        # No RESEND_API_KEY / SMTP_HOST configured, so nothing was actually emailed —
        # the code only went to the server terminal. Hand it back here too so you're
        # not stuck reading logs while testing locally. This never happens once a
        # real provider is configured, and never in FLASK_ENV=production.
        response["devModeCode"] = code
        response["devModeNote"] = "No email provider configured — this code was not actually emailed."

    return jsonify(response), 200


# ==========================================================
# ROUTE: POST /api/auth/verify-otp
# ==========================================================
@app.route("/api/auth/verify-otp", methods=["POST"])
def verify_otp():
    data = request.get_json(silent=True) or {}
    email = str(data.get("email", "")).strip().lower()
    code = str(data.get("code", "")).strip()

    if not valid_email(email) or not re.fullmatch(r"\d{6}", code):
        return jsonify({"error": "Invalid email or code"}), 400

    record = otp_store.get(email)
    if not record:
        return jsonify({"error": "No OTP was requested for this address"}), 400

    if datetime.utcnow() > record["expires_at"]:
        del otp_store[email]
        return jsonify({"error": "Code expired. Request a new one."}), 400

    if record["attempts"] >= OTP_MAX_VERIFY_ATTEMPTS:
        del otp_store[email]
        return jsonify({"error": "Too many incorrect attempts. Request a new code."}), 429

    if hash_otp(email, code) != record["hash"]:
        record["attempts"] += 1
        return jsonify({"error": "Incorrect code"}), 400

    # Correct code — consume it so it can't be replayed
    del otp_store[email]

    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute("SELECT farmer_id, name, district FROM farmers WHERE email = %s", (email,))
        farmer = cursor.fetchone()
        is_new_user = farmer is None

        if is_new_user:
            cursor.execute(
                "INSERT INTO farmers (name, email, district, state_id) VALUES (%s, %s, %s, %s)",
                ("", email, "", 1),
            )
            conn.commit()
            farmer_id = cursor.lastrowid
            farmer_name, farmer_district = "", ""
        else:
            farmer_id = farmer["farmer_id"]
            farmer_name, farmer_district = farmer["name"] or "", farmer["district"] or ""

        # Profile (name + district) is asked once, right after the very first
        # OTP verification. If somehow missing later too (e.g. old row), the
        # frontend re-asks — it never re-asks for the OTP itself, only this.
        needs_profile = is_new_user or not farmer_name or not farmer_district

        session.clear()
        session.permanent = True
        session["farmer_id"] = farmer_id
        session["email"] = email
        session["name"] = farmer_name

        response = jsonify({
            "message": "Signed in",
            "isNewUser": is_new_user,
            "needsProfile": needs_profile,
            "email": email,
            "name": farmer_name,
            "district": farmer_district,
        })
        issue_trusted_device(response, farmer_id)
        return response, 200
    except mysql.connector.Error as db_err:
        logger.error(
            "[DB ERROR] verify-otp query failed: %s\n"
            "If this mentions an unknown column 'email' (or 'phone'), you haven't run "
            "the migration note at the top of this file yet — run:\n"
            "  ALTER TABLE farmers CHANGE phone email VARCHAR(254) NOT NULL UNIQUE;",
            db_err,
        )
        return jsonify({"error": "Server database error. Check the terminal running app.py for details."}), 500
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ROUTE: GET /api/auth/session
# Lets the frontend check "am I already signed in?" on page load,
# so a browser refresh doesn't force the user back to the login screen.
# ==========================================================
@app.route("/api/auth/session", methods=["GET"])
def check_session():
    if "farmer_id" not in session:
        return jsonify({"signedIn": False}), 200
    return jsonify({
        "signedIn": True,
        "email": session.get("email"),
        "name": session.get("name", ""),
    }), 200


# ==========================================================
# ROUTE: POST /api/auth/logout
# ==========================================================
@app.route("/api/auth/logout", methods=["POST"])
def logout():
    session.clear()
    return jsonify({"message": "Signed out"}), 200


# ==========================================================
# ROUTE: GET /api/subscriptions
# Lists the crops the signed-in farmer already tracks, so the
# dashboard can rebuild the crop switcher after a page refresh.
# ==========================================================
@app.route("/api/subscriptions", methods=["GET"])
@login_required
def list_subscriptions():
    farmer_id = session["farmer_id"]
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute(
            """SELECT c.commodity_name FROM subscriptions s
               JOIN commodities c ON c.commodity_id = s.commodity_id
               WHERE s.farmer_id = %s
               ORDER BY s.created_at ASC""",
            (farmer_id,),
        )
        crops = [row["commodity_name"] for row in cursor.fetchall()]
        return jsonify({"crops": crops}), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ROUTE: POST /api/subscriptions
# ==========================================================
@app.route("/api/subscriptions", methods=["POST"])
@login_required
def add_subscriptions():
    data = request.get_json(silent=True) or {}
    crop_names = data.get("crops", [])

    if not isinstance(crop_names, list) or not crop_names:
        return jsonify({"error": "Provide at least one crop"}), 400

    farmer_id = session["farmer_id"]

    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        added = []
        for crop_name in crop_names:
            crop_name = str(crop_name).strip()
            if not crop_name:
                continue
            # Any crop name is accepted now — auto-creates the commodity
            # row so a farmer can track a crop before official ingestion
            # has ever seen it (see get_or_create_commodity).
            commodity_id, canonical_name = get_or_create_commodity(cursor, crop_name)

            cursor.execute(
                """INSERT IGNORE INTO subscriptions (farmer_id, commodity_id)
                   VALUES (%s, %s)""",
                (farmer_id, commodity_id),
            )
            added.append(canonical_name)

        conn.commit()
        return jsonify({"message": "Subscriptions saved", "crops": added}), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ROUTE: DELETE /api/subscriptions/<crop_name>
# ==========================================================
@app.route("/api/subscriptions/<crop_name>", methods=["DELETE"])
@login_required
def remove_subscription(crop_name):
    farmer_id = session["farmer_id"]
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute(
            "SELECT commodity_id FROM commodities WHERE commodity_name = %s",
            (crop_name.strip().title(),),
        )
        commodity = cursor.fetchone()
        if not commodity:
            return jsonify({"error": "Unknown crop"}), 404

        cursor.execute(
            "DELETE FROM subscriptions WHERE farmer_id = %s AND commodity_id = %s",
            (farmer_id, commodity["commodity_id"]),
        )
        conn.commit()
        return jsonify({"message": "Removed"}), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ROUTE: GET /api/prices/nearest?crop=tomato&limit=3
# ==========================================================
@app.route("/api/prices/nearest", methods=["GET"])
@login_required
def nearest_prices():
    crop_name = request.args.get("crop", "").strip()
    limit = min(int(request.args.get("limit", 3)), 10)  # cap to prevent abuse
    farmer_id = session["farmer_id"]

    if not crop_name:
        return jsonify({"error": "crop is required"}), 400

    # A farmer can override their saved district per-request (e.g. checking
    # prices for a place they're travelling to) — any of the 37 TN places.
    district_override = normalize_district(request.args.get("district", ""))

    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute("SELECT district FROM farmers WHERE farmer_id = %s", (farmer_id,))
        farmer = cursor.fetchone()
        district = district_override or (farmer["district"] if farmer else None) or "Chennai"

        # Any crop name is accepted — auto-creates the commodity if it's new
        # so the real ingestion pipeline can fill it in with official data
        # later. We never 404 here anymore; see generate_estimated_mandis
        # below for what happens when there's no real price data yet.
        commodity_id, canonical_crop_name = get_or_create_commodity(cursor, crop_name)
        conn.commit()

        # Latest price per mandi for this commodity, LOCAL TO THE REQUESTED
        # DISTRICT ONLY. Previously this had no district filter at all, so it
        # just returned whichever mandis happened to have price rows for the
        # crop — which in practice meant every farmer saw the same couple of
        # markets (e.g. Trichy/Thanjavur) no matter what location they'd
        # entered. Restricting to the requested district here, and letting
        # the estimate generator below produce genuinely nearby markets when
        # there's no real local data, makes results follow the location the
        # farmer actually asked about.
        # Also pulls in the average farmer rating for each mandi (see the
        # mandi_ratings table — farmers rate a mandi via POST /api/mandis/<id>/rating).
        cursor.execute(
            """
            SELECT m.mandi_id, m.mandi_name AS name, m.district,
                   p.modal_price AS price, p.price_date,
                   DATEDIFF(CURDATE(), p.price_date) AS days_old,
                   r.avg_rating, r.rating_count
            FROM prices p
            JOIN mandis m ON m.mandi_id = p.mandi_id
            LEFT JOIN (
                SELECT mandi_id, AVG(rating) AS avg_rating, COUNT(*) AS rating_count
                FROM mandi_ratings GROUP BY mandi_id
            ) r ON r.mandi_id = m.mandi_id
            WHERE p.commodity_id = %s
              AND m.district = %s
              AND p.price_date = (
                    SELECT MAX(p2.price_date) FROM prices p2
                    WHERE p2.mandi_id = p.mandi_id AND p2.commodity_id = p.commodity_id
              )
            ORDER BY p.price_date DESC
            LIMIT %s
            """,
            (commodity_id, district, limit),
        )
        rows = cursor.fetchall()

        # No official price data for this commodity in the requested district
        # yet (brand-new crop, or ingestion hasn't reached that district) —
        # fall back to a clearly-flagged estimate for markets near that same
        # requested location instead of showing unrelated far-away mandis.
        if not rows:
            estimated = generate_estimated_mandis(cursor, canonical_crop_name, district, limit)
            conn.commit()
            return jsonify(estimated), 200

        results = []
        for row in rows:
            # 7-day trend: compare latest price to price ~7 days earlier at same mandi
            cursor.execute(
                """
                SELECT modal_price FROM prices
                WHERE commodity_id = %s AND mandi_id = (
                    SELECT mandi_id FROM mandis WHERE mandi_name = %s AND district = %s LIMIT 1
                )
                AND price_date <= DATE_SUB(%s, INTERVAL 7 DAY)
                ORDER BY price_date DESC LIMIT 1
                """,
                (commodity_id, row["name"], row["district"], row["price_date"]),
            )
            past = cursor.fetchone()

            trend, trend_pct = "flat", 0
            if past and past["modal_price"]:
                diff = float(row["price"]) - float(past["modal_price"])
                pct = round(abs(diff) / float(past["modal_price"]) * 100)
                if diff > 0:
                    trend, trend_pct = "up", pct
                elif diff < 0:
                    trend, trend_pct = "down", pct

            results.append({
                "mandiId": row["mandi_id"],
                "name": row["name"],
                "distanceKm": None,  # populate once mandi lat/lng + farmer pincode geocoding is added
                "price": float(row["price"]),
                "trend": trend,
                "trendPct": trend_pct,
                "stale": row["days_old"] > 2,
                "updatedAt": row["price_date"].isoformat() if row["price_date"] else None,
                "avgRating": round(float(row["avg_rating"]), 1) if row["avg_rating"] is not None else None,
                "ratingCount": row["rating_count"] or 0,
                "estimated": False,
            })

        # Row 0 is the farmer's own district when available (query orders local
        # district first) — use it as the "what I'd get locally" baseline so we
        # can tell the farmer how much more/less another mandi pays.
        if results:
            local_price = results[0]["price"]
            best_idx = max(range(len(results)), key=lambda i: results[i]["price"])
            worst_idx = min(range(len(results)), key=lambda i: results[i]["price"])
            for i, r in enumerate(results):
                r["profitPct"] = (
                    round((r["price"] - local_price) / local_price * 100, 1) if local_price else 0
                )
                # Only meaningful once there's more than one mandi to compare
                r["isBest"] = len(results) > 1 and i == best_idx
                r["isLowest"] = len(results) > 1 and i == worst_idx and worst_idx != best_idx

        return jsonify(results), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ROUTE: POST /api/mandis/<mandi_id>/rating
# Lets a signed-in farmer rate a mandi 1-5 (e.g. on how fair/reliable
# it was to sell there). One rating per farmer per mandi — rating again
# just updates their existing score rather than adding a duplicate.
# ==========================================================
@app.route("/api/mandis/<int:mandi_id>/rating", methods=["POST"])
@login_required
def rate_mandi(mandi_id):
    data = request.get_json(silent=True) or {}
    try:
        rating = int(data.get("rating"))
    except (TypeError, ValueError):
        return jsonify({"error": "Rating must be a whole number from 1 to 5"}), 400

    if rating < 1 or rating > 5:
        return jsonify({"error": "Rating must be between 1 and 5"}), 400

    farmer_id = session["farmer_id"]
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute("SELECT mandi_id FROM mandis WHERE mandi_id = %s", (mandi_id,))
        if not cursor.fetchone():
            return jsonify({"error": "Unknown mandi"}), 404

        cursor.execute(
            """INSERT INTO mandi_ratings (farmer_id, mandi_id, rating)
               VALUES (%s, %s, %s)
               ON DUPLICATE KEY UPDATE rating = VALUES(rating), rated_at = NOW()""",
            (farmer_id, mandi_id, rating),
        )
        conn.commit()

        cursor.execute(
            "SELECT AVG(rating) AS avg_rating, COUNT(*) AS rating_count FROM mandi_ratings WHERE mandi_id = %s",
            (mandi_id,),
        )
        summary = cursor.fetchone()
        return jsonify({
            "message": "Rating saved",
            "avgRating": round(float(summary["avg_rating"]), 1) if summary["avg_rating"] is not None else rating,
            "ratingCount": summary["rating_count"],
        }), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# PRICE-CHANGE ALERT EMAILS
#
# This does NOT poll on its own — Flask request/response code isn't
# the right place to run a background loop. Instead call
# POST /api/notifications/run (protected by CRON_SECRET below) right
# after your price-ingestion script inserts new rows into `prices`.
# That's the same script mentioned in the Mandi Vilai ingestion step —
# just add one HTTP call at the end of it, e.g.:
#
#   requests.post(
#       "http://localhost:5000/api/notifications/run",
#       headers={"X-Cron-Secret": os.environ["CRON_SECRET"]},
#   )
#
# Or call it from a daily cron job / GitHub Action if ingestion and
# the Flask app run separately.
# ==========================================================
CRON_SECRET = os.environ.get("CRON_SECRET")


def get_latest_price(cursor, commodity_id, district):
    """Same 'nearest mandi' logic as /api/prices/nearest, but for one commodity."""
    cursor.execute(
        """
        SELECT m.mandi_name AS name, p.modal_price AS price, p.price_date
        FROM prices p
        JOIN mandis m ON m.mandi_id = p.mandi_id
        WHERE p.commodity_id = %s
          AND p.price_date = (
                SELECT MAX(p2.price_date) FROM prices p2
                WHERE p2.mandi_id = p.mandi_id AND p2.commodity_id = p.commodity_id
          )
        ORDER BY (m.district = %s) DESC, p.price_date DESC
        LIMIT 1
        """,
        (commodity_id, district),
    )
    return cursor.fetchone()


def check_price_alerts():
    """
    Walks every subscription, compares the latest price to the price we
    last emailed the farmer about, and sends an email for any change.
    First-time subscriptions just record a baseline silently — nobody
    gets an email the moment they subscribe.
    Returns a summary dict for the caller/endpoint to report back.
    """
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    sent, skipped, errors = 0, 0, 0
    try:
        cursor.execute(
            """
            SELECT s.farmer_id, s.commodity_id, s.last_notified_price,
                   f.email, f.district, c.commodity_name
            FROM subscriptions s
            JOIN farmers f ON f.farmer_id = s.farmer_id
            JOIN commodities c ON c.commodity_id = s.commodity_id
            """
        )
        subs = cursor.fetchall()

        for sub in subs:
            latest = get_latest_price(cursor, sub["commodity_id"], sub["district"])
            if not latest or latest["price"] is None:
                skipped += 1
                continue

            new_price = float(latest["price"])
            old_price = float(sub["last_notified_price"]) if sub["last_notified_price"] is not None else None

            if old_price is not None and new_price != old_price:
                ok = send_price_alert_email(
                    sub["email"], sub["commodity_name"], latest["name"], old_price, new_price
                )
                if ok:
                    sent += 1
                else:
                    errors += 1
                    continue  # leave last_notified_price as-is, retry next run

            cursor.execute(
                """UPDATE subscriptions SET last_notified_price = %s, last_notified_at = NOW()
                   WHERE farmer_id = %s AND commodity_id = %s""",
                (new_price, sub["farmer_id"], sub["commodity_id"]),
            )

        conn.commit()
        return {"checked": len(subs), "emails_sent": sent, "unchanged_or_skipped": skipped, "errors": errors}
    finally:
        cursor.close()
        conn.close()


@app.route("/api/notifications/run", methods=["POST"])
def run_notifications():
    if not CRON_SECRET or request.headers.get("X-Cron-Secret") != CRON_SECRET:
        return jsonify({"error": "Not authorized"}), 401
    summary = check_price_alerts()
    logger.info("[NOTIFICATIONS] %s", summary)
    return jsonify(summary), 200


# ==========================================================
# EMAIL CONFIG DEBUG — outside production only. Shows which
# email-related env vars Flask actually loaded, without ever
# exposing the secret values, so you can tell ".env not loaded"
# apart from "credentials are wrong".
# ==========================================================
@app.route("/api/debug/email-config", methods=["GET"])
def debug_email_config():
    if os.environ.get("FLASK_ENV") == "production":
        return jsonify({"error": "Not available in production"}), 404
    return jsonify({
        "active_method": "resend" if RESEND_API_KEY else ("smtp" if SMTP_HOST else "dev-console-only"),
        "RESEND_API_KEY_set": bool(RESEND_API_KEY),
        "SMTP_HOST_set": bool(SMTP_HOST),
        "SMTP_PORT": SMTP_PORT,
        "SMTP_USER_set": bool(SMTP_USER),
        "SMTP_PASSWORD_set": bool(SMTP_PASSWORD),
        "EMAIL_FROM": EMAIL_FROM,
        "CRON_SECRET_set": bool(CRON_SECRET),
    }), 200


# ==========================================================
# ADMIN — auth
# ==========================================================
@app.route("/api/admin/login", methods=["POST"])
def admin_login():
    if not ADMIN_PASSWORD:
        return jsonify({"error": "Admin login is not configured on this server"}), 503

    data = request.get_json(silent=True) or {}
    username = str(data.get("username", "")).strip()
    password = str(data.get("password", ""))

    # Constant-time-ish comparison isn't critical here (single low-value
    # local account), but hmac.compare_digest costs nothing to use.
    import hmac
    ok_user = hmac.compare_digest(username, ADMIN_USERNAME)
    ok_pass = hmac.compare_digest(password, ADMIN_PASSWORD)
    if not (ok_user and ok_pass):
        return jsonify({"error": "Invalid admin credentials"}), 401

    session["is_admin"] = True
    session["admin_username"] = username
    return jsonify({"message": "Signed in", "username": username}), 200


@app.route("/api/admin/session", methods=["GET"])
def admin_session():
    return jsonify({
        "signedIn": bool(session.get("is_admin")),
        "username": session.get("admin_username", ""),
    }), 200


@app.route("/api/admin/logout", methods=["POST"])
def admin_logout():
    session.pop("is_admin", None)
    session.pop("admin_username", None)
    return jsonify({"message": "Signed out"}), 200


# ==========================================================
# ADMIN — crops (commodities) CRUD
# ==========================================================
@app.route("/api/admin/crops", methods=["GET"])
@admin_required
def admin_list_crops():
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute("SELECT commodity_id, commodity_name FROM commodities ORDER BY commodity_name")
        return jsonify(cursor.fetchall()), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/crops", methods=["POST"])
@admin_required
def admin_create_crop():
    data = request.get_json(silent=True) or {}
    name = str(data.get("name", "")).strip().title()
    if not name:
        return jsonify({"error": "Crop name is required"}), 400
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute("INSERT INTO commodities (commodity_name) VALUES (%s)", (name,))
        conn.commit()
        return jsonify({"commodity_id": cursor.lastrowid, "commodity_name": name}), 201
    except mysql.connector.Error:
        return jsonify({"error": "That crop already exists"}), 409
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/crops/<int:commodity_id>", methods=["PUT"])
@admin_required
def admin_update_crop(commodity_id):
    data = request.get_json(silent=True) or {}
    name = str(data.get("name", "")).strip().title()
    if not name:
        return jsonify({"error": "Crop name is required"}), 400
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute(
            "UPDATE commodities SET commodity_name = %s WHERE commodity_id = %s", (name, commodity_id)
        )
        conn.commit()
        if cursor.rowcount == 0:
            return jsonify({"error": "Crop not found"}), 404
        return jsonify({"commodity_id": commodity_id, "commodity_name": name}), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/crops/<int:commodity_id>", methods=["DELETE"])
@admin_required
def admin_delete_crop(commodity_id):
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute("DELETE FROM commodities WHERE commodity_id = %s", (commodity_id,))
        conn.commit()
        if cursor.rowcount == 0:
            return jsonify({"error": "Crop not found"}), 404
        return jsonify({"message": "Deleted"}), 200
    except mysql.connector.Error:
        return jsonify({"error": "Can't delete — this crop still has prices or subscriptions attached"}), 409
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ADMIN — mandis CRUD
# ==========================================================
@app.route("/api/admin/mandis", methods=["GET"])
@admin_required
def admin_list_mandis():
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute("SELECT mandi_id, mandi_name, district FROM mandis ORDER BY district, mandi_name")
        return jsonify(cursor.fetchall()), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/mandis", methods=["POST"])
@admin_required
def admin_create_mandi():
    data = request.get_json(silent=True) or {}
    name = str(data.get("name", "")).strip()
    district = normalize_district(str(data.get("district", "")).strip())
    if not name:
        return jsonify({"error": "Mandi name is required"}), 400
    if not district:
        return jsonify({"error": "Unrecognized Tamil Nadu district", "validDistricts": TN_DISTRICTS}), 400
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute("INSERT INTO mandis (mandi_name, district) VALUES (%s, %s)", (name, district))
        conn.commit()
        return jsonify({"mandi_id": cursor.lastrowid, "mandi_name": name, "district": district}), 201
    except mysql.connector.Error:
        return jsonify({"error": "That mandi already exists in that district"}), 409
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/mandis/<int:mandi_id>", methods=["PUT"])
@admin_required
def admin_update_mandi(mandi_id):
    data = request.get_json(silent=True) or {}
    name = str(data.get("name", "")).strip()
    district = normalize_district(str(data.get("district", "")).strip())
    if not name or not district:
        return jsonify({"error": "Name and a valid Tamil Nadu district are required"}), 400
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute(
            "UPDATE mandis SET mandi_name = %s, district = %s WHERE mandi_id = %s",
            (name, district, mandi_id),
        )
        conn.commit()
        if cursor.rowcount == 0:
            return jsonify({"error": "Mandi not found"}), 404
        return jsonify({"mandi_id": mandi_id, "mandi_name": name, "district": district}), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/mandis/<int:mandi_id>", methods=["DELETE"])
@admin_required
def admin_delete_mandi(mandi_id):
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute("DELETE FROM mandis WHERE mandi_id = %s", (mandi_id,))
        conn.commit()
        if cursor.rowcount == 0:
            return jsonify({"error": "Mandi not found"}), 404
        return jsonify({"message": "Deleted"}), 200
    except mysql.connector.Error:
        return jsonify({"error": "Can't delete — this mandi still has prices attached"}), 409
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ADMIN — prices CRUD
# ==========================================================
@app.route("/api/admin/prices", methods=["GET"])
@admin_required
def admin_list_prices():
    limit = min(int(request.args.get("limit", 100)), 500)
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute(
            """SELECT p.price_id, p.commodity_id, c.commodity_name, p.mandi_id, m.mandi_name,
                      m.district, p.modal_price, p.price_date
               FROM prices p
               JOIN commodities c ON c.commodity_id = p.commodity_id
               JOIN mandis m ON m.mandi_id = p.mandi_id
               ORDER BY p.price_date DESC LIMIT %s""",
            (limit,),
        )
        rows = cursor.fetchall()
        for r in rows:
            if r.get("price_date"):
                r["price_date"] = r["price_date"].isoformat()
        return jsonify(rows), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/prices", methods=["POST"])
@admin_required
def admin_create_price():
    data = request.get_json(silent=True) or {}
    try:
        commodity_id = int(data.get("commodity_id"))
        mandi_id = int(data.get("mandi_id"))
        price = float(data.get("price"))
    except (TypeError, ValueError):
        return jsonify({"error": "commodity_id, mandi_id and price are required"}), 400
    if price <= 0:
        return jsonify({"error": "Price must be positive"}), 400
    price_date = str(data.get("date") or datetime.utcnow().date().isoformat())

    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute(
            """INSERT INTO prices (commodity_id, mandi_id, modal_price, price_date, is_estimated)
               VALUES (%s, %s, %s, %s, 0)
               ON DUPLICATE KEY UPDATE modal_price = VALUES(modal_price), is_estimated = 0""",
            (commodity_id, mandi_id, price, price_date),
        )
        conn.commit()
        return jsonify({"message": "Price saved"}), 201
    except mysql.connector.Error as exc:
        return jsonify({"error": f"Could not save price: {exc}"}), 400
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/prices/<int:price_id>", methods=["PUT"])
@admin_required
def admin_update_price(price_id):
    data = request.get_json(silent=True) or {}
    try:
        price = float(data.get("price"))
    except (TypeError, ValueError):
        return jsonify({"error": "A numeric price is required"}), 400
    if price <= 0:
        return jsonify({"error": "Price must be positive"}), 400
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute(
            "UPDATE prices SET modal_price = %s, is_estimated = 0 WHERE price_id = %s", (price, price_id)
        )
        conn.commit()
        if cursor.rowcount == 0:
            return jsonify({"error": "Price row not found"}), 404
        return jsonify({"message": "Updated"}), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/prices/<int:price_id>", methods=["DELETE"])
@admin_required
def admin_delete_price(price_id):
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute("DELETE FROM prices WHERE price_id = %s", (price_id,))
        conn.commit()
        if cursor.rowcount == 0:
            return jsonify({"error": "Price row not found"}), 404
        return jsonify({"message": "Deleted"}), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# ADMIN — farmers (view + delete only; no editing someone else's profile)
# ==========================================================
@app.route("/api/admin/farmers", methods=["GET"])
@admin_required
def admin_list_farmers():
    conn = get_db()
    cursor = conn.cursor(dictionary=True)
    try:
        cursor.execute(
            """SELECT farmer_id, name, email, district,
                      (SELECT COUNT(*) FROM subscriptions s WHERE s.farmer_id = f.farmer_id) AS crop_count
               FROM farmers f ORDER BY farmer_id DESC"""
        )
        return jsonify(cursor.fetchall()), 200
    finally:
        cursor.close()
        conn.close()


@app.route("/api/admin/farmers/<int:farmer_id>", methods=["DELETE"])
@admin_required
def admin_delete_farmer(farmer_id):
    conn = get_db()
    cursor = conn.cursor()
    try:
        cursor.execute("DELETE FROM farmers WHERE farmer_id = %s", (farmer_id,))
        conn.commit()
        if cursor.rowcount == 0:
            return jsonify({"error": "Farmer not found"}), 404
        return jsonify({"message": "Deleted"}), 200
    finally:
        cursor.close()
        conn.close()


# ==========================================================
# HEALTH CHECK
# ==========================================================
@app.route("/api/health", methods=["GET"])
def health():
    return jsonify({"status": "ok"}), 200


if __name__ == "__main__":
    debug_mode = os.environ.get("FLASK_ENV") != "production"
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=debug_mode)