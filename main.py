"""
Gasbulk Track API v2
Sources:
  PTGL Sheet         → ตำแหน่งรถ live  (col A=LicenseNO, E=Lat, F=Lng, M=Location)
  แผนงาน Gasbulk     → ทริปประจำวัน   (col C=วันที่, G=เวลากำหนด, M=ปลายทาง, P=เบอร์รถ)
  ข้อมูลปลายทาง      → พิกัดปลายทาง   (col A=ชื่อ ตรงกับแผนงาน M, col G=lat,lng)
  Google Routes API  → ETA จริงพร้อม traffic → รู้ล่วงหน้าว่าจะช้ากี่นาที
"""

from __future__ import annotations

import base64
import hashlib
import hmac
import json
import os
import re
import traceback
from datetime import datetime, timedelta, timezone
from math import atan2, cos, radians, sin, sqrt
from time import time
from typing import Optional

import httpx
import gspread
from fastapi import FastAPI, Form, HTTPException, Query, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse, JSONResponse, RedirectResponse
from google.oauth2.service_account import Credentials
from pydantic import BaseModel

# ─── CONFIG — ปรับคอลัมน์ที่นี่ถ้า Sheet เปลี่ยน ─────────────────────────────

# Sheet 1: PTGL — ตำแหน่งรถ live
PTGL_ID    = "1FIXB3TT3b68ho2pc0lrYi4IOuXmCw4_BBDot2kp-XC4"
PTGL_TAB   = "PTGL"
PTGL_LICNO = 0   # A  LicenseNO  เช่น "No.465(63-3530)"
PTGL_LAT   = 4   # E  Latitude
PTGL_LNG   = 5   # F  Longitude
PTGL_LOC   = 12  # M  LocalLocation (ที่อยู่ปัจจุบัน)

# Sheet 2a: ไฟล์ต้นทางจริง "แผนงานแก๊สบัลค์ใหม่" — คนหน้างานแก้ไขแผนงานที่ไฟล์นี้โดยตรง
# ใช้อ่าน "รายการทริป" + "ข้อมูลปลายทาง" เท่านั้น (ยังไม่มีสิทธิ์เขียน แค่ Viewer)
SOURCE_ID    = "1bwBmxGy1mlnAEIUm5ZNNV71tud3NCyPZlHesIwP4tUs"

# Sheet 2b: "Test Report Ontime PTGLG" — ยังใช้ไฟล์นี้สำหรับไทม์ไลน์ตำแหน่งรายชั่วโมง
# (แท็บรายวัน dd.mm.yyyy) กับ ChaseLog (ประวัติสะสมอยู่ที่นี่แล้ว) เท่านั้น ไม่ใช้อ่านทริปอีกต่อไป
PLAN_ID      = "1kksFntsGH0SuJUeF2ChAury-yyF6EorzgBpyl5mggdk"
PLAN_TAB     = "แผนงาน Gasbulk"
PLAN_DATE    = 2   # C  วันที่
PLAN_DUE     = 5   # F  วันที่ส่งมอบ  ← ใช้คู่กับ G เป็นกำหนดจริง (อาจข้ามวันจาก C)
PLAN_SCHED   = 6   # G  เวลาส่งมอบ (HH:MM)
PLAN_TRIP    = 4   # E  เที่ยววิ่ง
PLAN_INVOICE = 7   # H  เลขที่ใบกำกับ
PLAN_VOLUME  = 9   # J  ปริมาณ
PLAN_SOURCE  = 11  # L  คลังต้นทาง
PLAN_DEST    = 12  # M  ลูกค้าปลายทาง  ← จับคู่กับ ข้อมูลปลายทาง col A
PLAN_DROP    = 13  # N  Drop
PLAN_VTYPE   = 16  # Q  ประเภทรถ (08 Tons / 10 Tons / Trailer)
PLAN_CARNO   = 15  # P  เบอร์รถ         ← จับคู่กับ PTGL LicenseNO
PLAN_PLATE   = 17  # R  ทะเบียนรถ
PLAN_DRIVER  = 18  # S  พขร.1
PLAN_DRIVER2 = 19  # T  พขร.2
PLAN_PHONE   = 20  # U  เบอร์โทร.1  ← ใช้ทำปุ่มโทร
PLAN_PHONE2  = 21  # V  เบอร์โทร.2
# แผน (P) — เวลาที่ตั้งไว้ล่วงหน้า รูปแบบ "15/08/2026, 05:30"
PLAN_P_OUT   = 23  # X  เวลาออกจากฟรีโอ (P)
PLAN_P_LOAD  = 24  # Y  เวลาเข้าโหลด (P)
PLAN_P_CALL  = 25  # Z  เวลาโทรตาม พขร (P)  ← ใช้เตือนว่าถึงเวลาไล่รถ
PLAN_STATUS  = 26  # AA สถานะจัดส่ง (กรอกมือ: โหลดเก็บ / ยกเลิก)
# เวลาจริงที่บันทึกไว้ในชีต รูปแบบ "15/8/2026, 6:00:44"
PLAN_YARD    = 27  # AB เวลาเข้าลานจอด
PLAN_LOAD_IN = 28  # AC เวลาเข้าโหลด
PLAN_LOAD_OUT= 29  # AD เวลาออกจากโหลด
PLAN_DEPART  = 30  # AE เวลาออกจากคลัง/สาขา
PLAN_ARRIVE  = 31  # AF เวลาเข้าปลายทาง  ← เวลาถึงจริง
PLAN_LEAVE   = 32  # AG เวลาออกปลายทาง
PLAN_GPS_ST  = 33  # AH สถานะจัดส่ง GPS
PLAN_ONTIME  = 47  # AV On Time  (PASS / Delay) — ผลตัดสินจากชีตเอง
PLAN_ONTIME_M= 48  # AW On Time(m) จำนวนนาทีที่ช้า

# Sheet 3: ข้อมูลปลายทาง — พิกัดของแต่ละจุดส่ง (อยู่ในไฟล์ต้นทางเดียวกับแผนงาน SOURCE_ID)
DEST_ID      = SOURCE_ID
DEST_TAB     = "ข้อมูลปลายทาง"
DEST_NAME    = 0   # A  ชื่อปลายทาง (ตรงกับ PLAN_DEST)
DEST_COORD   = 6   # G  พิกัด "lat,lng"  เช่น "13.802396,102.091462"

# ─── พิกัดคลังต้นทาง — ใส่ตรงนี้เลยครับ ──────────────────────────────────────
# ค้นหาพิกัดจาก Google Maps → คลิกขวาที่คลัง → copy ตัวเลข 2 ตัว
# ชื่อคลังต้องตรงกับ col L ของ Sheet แผนงาน Gasbulk ทุกตัวอักษร
DEPOTS: dict[str, tuple[float, float]] = {
    "SC BPK":   (13.49744653169782,  100.97405072586537),
    "BSRC":     (13.096395594198446, 100.88592594081439),
    "IRPC":     (12.660675601097862, 101.29956486587231),
    "PTT TANK": (12.669715573765938, 101.13763760405689),
    "UAC":      (17.009648,          100.015937),
    # เพิ่มคลังใหม่: "ชื่อคลัง": (lat, lng),
}

# ค่าประมาณเวลาเดินทางแบบไม่ใช้ API (ปรับได้ตามหน้างานจริง)
ROAD_FACTOR   = 1.35  # ถนนจริงอ้อมกว่าเส้นตรงประมาณ 35%
AVG_SPEED_KMH = 45    # ความเร็วเฉลี่ยรถบรรทุกแก๊ส รวมติดไฟแดง/จราจร
LOAD_MINS     = 45    # เวลาโหลดสำรอง ใช้เมื่อไม่พบในตาราง DEPOT_TIMES
UNLOAD_MINS   = 45    # เวลาลงของที่ลูกค้า ใช้ต่อ ETA ระหว่าง Drop

# จำนวนครั้งสูงสุดที่ยอมเรียก ORS ต่อ 1 request
# กันทั้ง timeout ของ Vercel (~10 วิ) และ rate limit ของ ORS (40 ครั้ง/นาที)
# ทริปที่เกินโควตาจะใช้สูตรคำนวณเอง (เร็วมาก ไม่ต้องต่อเน็ต)
MAX_ROUTE_CALLS = 12

# ─── เวลามาตรฐานที่คลัง (นาที) ───────────────────────────────────────────────
# โครงสร้าง: (คลัง, ประเภทรถ) → (เวลาลานจอด, เวลาโรงจ่าย)
#   ลานจอด  = Sequence 1 (รอคิว)
#   โรงจ่าย = Sequence 2 (โหลดจริง)
# ประเภทรถ: "08" = 08 Tons, "10" = 10 Tons, "TR" = Trailer
DEPOT_TIMES: dict[tuple[str, str], tuple[int, int]] = {
    ("SC BPK",   "08"): (30, 60),
    ("SC BPK",   "10"): (30, 60),
    ("SC BPK",   "TR"): (30, 90),
    ("PTT TANK", "08"): (60, 60),
    ("PTT TANK", "10"): (60, 60),
    ("PTT TANK", "TR"): (60, 120),
    ("BSRC",     "08"): (60, 60),
    ("BSRC",     "10"): (60, 60),
    ("BSRC",     "TR"): (60, 90),
    ("UAC",      "TR"): (20, 120),
    ("IRPC",     "08"): (60, 60),
    ("IRPC",     "10"): (60, 60),
    ("IRPC",     "TR"): (60, 120),
}

# คำในคอลัมน์สถานะ GPS ที่แปลว่า "ส่งเสร็จแล้ว" (เพิ่มคำใหม่ได้ที่นี่)
DONE_KEYWORDS = [
    "สำเร็จ", "เสร็จ", "จัดส่งแล้ว", "ส่งแล้ว", "จบงาน",
    "ถึงปลายทาง", "ถึงลูกค้า", "delivered", "complete",
]

# คำที่แปลว่างานนี้ไม่ต้องไล่แล้ว (ยกเลิก / ยกไปวันอื่น)
CANCEL_KEYWORDS = ["ยกเลิก", "โหลดเก็บ", "cancel"]

TZ_OFFSET     = 7    # UTC+7
CACHE_TTL     = 300  # cache Sheet 5 นาที
ETA_CACHE_TTL = 3600  # cache ETA 1 ชม. (ตรงกับรอบไล่รถ + ประหยัดโควตา ORS)

# ต้องใช้สิทธิ์เขียน เพราะบันทึก "ไล่แล้ว" ลงแท็บ ChaseLog
# (แตะเฉพาะแท็บ ChaseLog เท่านั้น ไม่ยุ่งกับแผนงาน Gasbulk)
SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets",
    "https://www.googleapis.com/auth/drive.readonly",
]
CHASE_TAB = "ChaseLog"

# ─── ล็อกอิน ─────────────────────────────────────────────────────────────────
# ตั้งรหัสผ่านที่ Vercel → Settings → Environment Variables → APP_PASSWORD
# ถ้ายังไม่ตั้ง เว็บจะเปิดให้เข้าได้เหมือนเดิม แต่ขึ้นแถบเตือนสีแดง
COOKIE_NAME    = "gb_session"
SESSION_HOURS  = 12          # ล็อกอินครั้งเดียวใช้ได้ 1 กะ


def _app_password() -> str:
    return os.environ.get("APP_PASSWORD", "")


CRON_SECRET = os.environ.get("CRON_SECRET", "")   # ตั้งที่ Vercel — ใช้กันคนนอกยิง /api/cron/hourly-status เล่น


def _secret() -> bytes:
    """คีย์สำหรับเซ็น token — ตั้ง SESSION_SECRET เองได้ ไม่ตั้งก็ใช้รหัสผ่านแทน"""
    return (os.environ.get("SESSION_SECRET") or _app_password() or "dev").encode()


def _make_token() -> str:
    exp  = str(int(time()) + SESSION_HOURS * 3600)
    sig  = hmac.new(_secret(), exp.encode(), hashlib.sha256).digest()
    return exp + "." + base64.urlsafe_b64encode(sig).decode().rstrip("=")


def _token_ok(token: str) -> bool:
    try:
        exp, sig = (token or "").split(".", 1)
        if int(exp) < int(time()):
            return False
        want = hmac.new(_secret(), exp.encode(), hashlib.sha256).digest()
        want = base64.urlsafe_b64encode(want).decode().rstrip("=")
        return hmac.compare_digest(sig, want)
    except (ValueError, AttributeError):
        return False

# ─── APP ─────────────────────────────────────────────────────────────────────

app = FastAPI(
    title="Gasbulk Track API",
    description="ติดตามรถ Gasbulk — รู้ล่วงหน้าว่าจะถึงช้าหรือเร็ว",
    version="2.0.0",
)
app.add_middleware(
    CORSMiddleware, allow_origins=["*"], allow_methods=["GET"], allow_headers=["*"]
)

OPEN_PATHS = {"/login", "/api/login", "/favicon.ico", "/api/cron/hourly-status"}


@app.middleware("http")
async def require_login(request: Request, call_next):
    """กันไม่ให้คนที่ไม่ได้ล็อกอินเข้าถึงข้อมูล"""
    path = request.url.path
    if not _app_password() or path in OPEN_PATHS:
        return await call_next(request)          # ยังไม่ตั้งรหัส → เปิดตามเดิม

    if _token_ok(request.cookies.get(COOKIE_NAME, "")):
        return await call_next(request)

    if path.startswith("/api/"):
        return JSONResponse({"detail": "ต้องล็อกอินก่อน"}, status_code=401)
    return RedirectResponse("/login", status_code=303)

# ─── MODELS ──────────────────────────────────────────────────────────────────

class TripOut(BaseModel):
    id:           int
    date:         str
    car_no:       str
    plate:        str
    trip_no:      str
    drop:         str
    customer:     str
    source:       str
    volume:       str
    invoice_no:   str
    sched_time:   str           # เวลากำหนด HH:MM
    gps_status:   str           # สถานะจาก Sheet (คอลัมน์ AH)
    ontime:       str = ""      # AV ผลตัดสิน On Time จากชีต (PASS / Delay)
    ontime_min:   str = ""      # AW ช้ากี่นาที (ตามชีต)
    driver:       str = ""      # S  ชื่อ พขร
    phone:        str = ""      # U  เบอร์โทร พขร
    # เวลาจริงจากชีต (คอลัมน์ AB–AG) — ว่างแปลว่ายังไม่ถึงขั้นนั้น
    yard_time:    Optional[str]   = None   # AB เข้าลานจอด
    load_out:     Optional[str]   = None   # AD ออกจากโหลด
    depart_time:  Optional[str]   = None   # AE ออกจากคลัง
    arrive_time:  Optional[str]   = None   # AF เข้าปลายทาง (เวลาถึงจริง)
    # ตำแหน่งปัจจุบัน (จาก PTGL)
    current_lat:  Optional[float] = None
    current_lng:  Optional[float] = None
    current_loc:  Optional[str]   = None
    # ETA (จาก Routes API)
    travel_mins:  Optional[int]   = None   # นาทีจากตำแหน่งปัจจุบัน → ปลายทาง
    eta_time:     Optional[str]   = None   # เวลาถึงโดยประมาณ "HH:MM"
    # สรุป
    status:       str                      # early|late|transit|pending|arrived|cancelled
    diff_minutes: Optional[int]   = None   # บวก=ช้า  ลบ=เร็ว
    actual:       bool            = False  # True = วัดจากเวลาถึงจริง ไม่ใช่ประมาณการ
    prediction:   str             = ""     # ข้อความอ่านง่าย

class SummaryResponse(BaseModel):
    date:       str
    fetched_at: str
    total:      int
    arrived:    int
    in_transit: int
    late:       int
    pending:    int
    cancelled:  int = 0
    trips:      list[TripOut]

# ─── CACHE ───────────────────────────────────────────────────────────────────

_sheet_cache: dict[str, tuple[float, list]] = {}
_eta_cache:   dict[str, tuple[float, int]]  = {}

# ─── SUPABASE (แคชถาวรของข้อมูล Sheet — กัน Vercel รีเซ็ตแคชในหน่วยความจำบ่อยเกิน) ──
SUPABASE_URL         = os.environ.get("SUPABASE_URL", "").rstrip("/")
SUPABASE_SERVICE_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")


def _supabase_headers() -> dict:
    return {
        "apikey": SUPABASE_SERVICE_KEY,
        "Authorization": f"Bearer {SUPABASE_SERVICE_KEY}",
        "Content-Type": "application/json",
    }


def _supabase_get_cache(key: str):
    """คืนข้อมูลแคชจาก Supabase ถ้ายังไม่หมดอายุ (CACHE_TTL) ไม่งั้นคืน None"""
    if not (SUPABASE_URL and SUPABASE_SERVICE_KEY):
        return None
    try:
        r = httpx.get(
            f"{SUPABASE_URL}/rest/v1/sheet_cache",
            params={"cache_key": f"eq.{key}", "select": "data,updated_at"},
            headers=_supabase_headers(),
            timeout=5,
        )
        r.raise_for_status()
        rows = r.json()
        if not rows:
            return None
        updated_at = datetime.fromisoformat(rows[0]["updated_at"].replace("Z", "+00:00"))
        age = (datetime.now(timezone.utc) - updated_at).total_seconds()
        if age > CACHE_TTL:
            return None
        return rows[0]["data"]
    except Exception:
        return None   # Supabase ล่ม/ตั้งค่าไม่ครบ → เงียบไว้ ไปอ่าน Sheet ตรงแทน


def _supabase_set_cache(key: str, data: list) -> None:
    if not (SUPABASE_URL and SUPABASE_SERVICE_KEY):
        return
    try:
        httpx.post(
            f"{SUPABASE_URL}/rest/v1/sheet_cache",
            params={"on_conflict": "cache_key"},
            headers={**_supabase_headers(), "Prefer": "resolution=merge-duplicates"},
            json={"cache_key": key, "data": data, "updated_at": datetime.now(timezone.utc).isoformat()},
            timeout=5,
        )
    except Exception:
        pass   # เขียนแคชไม่สำเร็จไม่เป็นไร ครั้งหน้าจะลองใหม่เอง

# ─── UTILITIES ───────────────────────────────────────────────────────────────

def _build_creds() -> Credentials:
    env = os.environ.get("GOOGLE_CREDENTIALS")
    if env:
        return Credentials.from_service_account_info(json.loads(env), scopes=SCOPES)
    local = os.path.join(os.path.dirname(__file__), "..", "credentials.json")
    return Credentials.from_service_account_file(local, scopes=SCOPES)


def _fetch_sheet(sheet_id: str, tab: str) -> list[list]:
    """อ่าน Sheet พร้อมแคช 5 นาที — เช็คแคชในหน่วยความจำก่อน (เร็วสุด) แล้วค่อยเช็ค
    แคชถาวรใน Supabase (กันแคชหายตอน Vercel สร้าง server ใหม่) สุดท้ายค่อยอ่าน Sheet จริง"""
    key = f"{sheet_id}:{tab}"
    if key in _sheet_cache:
        ts, data = _sheet_cache[key]
        if time() - ts < CACHE_TTL:
            return data

    cached = _supabase_get_cache(key)
    if cached is not None:
        _sheet_cache[key] = (time(), cached)
        return cached

    gc   = gspread.authorize(_build_creds())
    data = gc.open_by_key(sheet_id).worksheet(tab).get_all_values()
    _sheet_cache[key] = (time(), data)
    _supabase_set_cache(key, data)
    return data


def _cell(row: list, idx: int) -> str:
    return str(row[idx]).strip() if idx < len(row) else ""


def _extract_car_no(raw: str) -> str:
    """
    ดึงเลขรถชุดแรกออกมาเป็นคีย์จับคู่ ใช้ได้ทั้ง 2 ชีต
      'No.465(63-3530)' → '465'
      'PTL.403'         → '403'
      '0465'            → '465'
    """
    m = re.search(r"\d+", raw or "")
    return m.group(0).lstrip("0") or m.group(0) if m else ""


def _parse_coords(raw: str) -> Optional[tuple[float, float]]:
    """'13.756, 100.501' → (13.756, 100.501)"""
    nums = re.findall(r"[-+]?\d+\.\d+", raw)
    if len(nums) >= 2:
        try:
            return float(nums[0]), float(nums[1])
        except ValueError:
            pass
    return None


def _parse_date(raw: str) -> Optional[str]:
    """รองรับ 15/08/2026, 15-08-2026, 15.08.2026, 2026-08-15 และปี พ.ศ. (2569)"""
    if not raw:
        return None
    token = raw.strip().split(" ")[0].replace(".", "/").replace("-", "/")
    for fmt in ("%d/%m/%Y", "%Y/%m/%d", "%m/%d/%Y", "%d/%m/%y"):
        try:
            d = datetime.strptime(token, fmt)
        except ValueError:
            continue
        if d.year > 2400:                       # ปี พ.ศ. → ค.ศ.
            d = d.replace(year=d.year - 543)
        return d.strftime("%Y-%m-%d")
    return None


def _vehicle_type(raw: str) -> str:
    """'Trailer' → 'TR'   '10 Tons' → '10'   '08 Tons' → '08'"""
    s = (raw or "").lower()
    if "trail" in s or "พ่วง" in s or "เทรล" in s:
        return "TR"
    m = re.search(r"\d+", s)
    if m:
        n = int(m.group(0))
        if n >= 1000:            # เผลอส่งปริมาณมา เช่น 8,000 → แปลงเป็นตัน
            n //= 1000
        return "10" if n >= 10 else "08"
    return ""


def _depot_minutes(depot: str, vtype: str) -> tuple[int, int]:
    """คืน (เวลาลานจอด, เวลาโรงจ่าย) — ถ้าไม่พบประเภทรถ ใช้ค่าที่ช้าที่สุดของคลังนั้น"""
    hit = DEPOT_TIMES.get((depot, vtype))
    if hit:
        return hit
    rows = [v for (d, _), v in DEPOT_TIMES.items() if d == depot]
    if rows:
        return max(rows, key=lambda x: x[0] + x[1])
    return (0, LOAD_MINS)


def _cell_time(raw: str) -> Optional[str]:
    """'15/8/2026, 6:00:44' → '06:00'   ว่าง/ไม่ใช่เวลา → None"""
    m = re.search(r"(\d{1,2}):(\d{2})", raw or "")
    return f"{int(m.group(1)):02d}:{m.group(2)}" if m else None


def _cell_dt(raw: str) -> Optional[datetime]:
    """'15/8/2026, 6:00:44' → datetime(2026,8,15,6,0)  (รองรับปี พ.ศ.)"""
    m = re.search(r"(\d{1,2})[/.\-](\d{1,2})[/.\-](\d{4})\D+(\d{1,2}):(\d{2})", raw or "")
    if not m:
        return None
    d, mo, y, h, mi = (int(m.group(i)) for i in (1, 2, 3, 4, 5))
    if y > 2400:
        y -= 543
    try:
        return datetime(y, mo, d, h, mi)
    except ValueError:
        return None


def _sched_dt(due_date: Optional[str], hhmm: str) -> Optional[datetime]:
    """รวม 'วันที่ส่งมอบ' (F) กับ 'เวลาส่งมอบ' (G) เป็นกำหนดจริง"""
    if not due_date or not hhmm:
        return None
    try:
        return datetime.strptime(f"{due_date} {hhmm[:5]}", "%Y-%m-%d %H:%M")
    except ValueError:
        return None


def _to_mins(t: str) -> Optional[int]:
    if not t or ":" not in t:
        return None
    try:
        parts = t.strip().split(":")
        return int(parts[0]) * 60 + int(parts[1])
    except (ValueError, IndexError):
        return None


def _thai_now() -> datetime:
    return datetime.utcnow() + timedelta(hours=TZ_OFFSET)


def _now_mins() -> int:
    n = _thai_now()
    return n.hour * 60 + n.minute


def _today_thai() -> str:
    return _thai_now().strftime("%Y-%m-%d")


def _mins_to_hhmm(total_mins: int) -> str:
    h, m = divmod(total_mins % 1440, 60)
    return f"{h:02d}:{m:02d}"

# ─── ETA PROVIDERS ───────────────────────────────────────────────────────────

def _haversine_km(lat1: float, lng1: float, lat2: float, lng2: float) -> float:
    """ระยะทางเส้นตรงบนผิวโลก (กิโลเมตร)"""
    r    = 6371.0
    p1, p2 = radians(lat1), radians(lat2)
    dp   = radians(lat2 - lat1)
    dl   = radians(lng2 - lng1)
    a    = sin(dp / 2) ** 2 + cos(p1) * cos(p2) * sin(dl / 2) ** 2
    return r * 2 * atan2(sqrt(a), sqrt(1 - a))


def _estimate_minutes(orig_lat, orig_lng, dest_lat, dest_lng) -> int:
    """
    ประมาณเวลาเดินทางแบบไม่ง้อ API
    ระยะเส้นตรง × ROAD_FACTOR (ถนนจริงอ้อมกว่าเส้นตรง) ÷ ความเร็วเฉลี่ย
    """
    km = _haversine_km(orig_lat, orig_lng, dest_lat, dest_lng) * ROAD_FACTOR
    return max(1, int(km / AVG_SPEED_KMH * 60))


def _ors_minutes(orig_lat, orig_lng, dest_lat, dest_lng) -> Optional[int]:
    """OpenRouteService — ฟรี 2,000 ครั้ง/วัน ไม่ต้องผูกบัตร (ไม่มี traffic)"""
    api_key = os.environ.get("ORS_KEY")
    if not api_key:
        return None
    try:
        resp = httpx.post(
            "https://api.openrouteservice.org/v2/directions/driving-hgv",
            json={"coordinates": [[orig_lng, orig_lat], [dest_lng, dest_lat]]},
            headers={"Authorization": api_key, "Content-Type": "application/json"},
            timeout=6,
        )
        resp.raise_for_status()
        secs = resp.json()["routes"][0]["summary"]["duration"]
        return max(1, int(secs) // 60)
    except Exception:
        return None


def _get_travel_minutes(
    orig_lat: float, orig_lng: float,
    dest_lat: float, dest_lng: float,
    allow_api: bool = True,
) -> Optional[int]:
    """
    เรียก Google Routes API → นาทีที่จะถึงปลายทาง (รวม traffic จริง)
    cache 10 นาที เพื่อลดค่าใช้จ่าย API
    """
    # ปัดตำแหน่ง 3 ทศนิยม (~111m) สำหรับ cache key
    key = f"{orig_lat:.3f},{orig_lng:.3f}->{dest_lat:.4f},{dest_lng:.4f}"
    if key in _eta_cache:
        ts, mins = _eta_cache[key]
        if time() - ts < ETA_CACHE_TTL:
            return mins

    if not allow_api:
        # เกินโควตาเรียก API ของ request นี้ → ใช้สูตรคำนวณ (ไม่ต่อเน็ต เร็วมาก)
        return _estimate_minutes(orig_lat, orig_lng, dest_lat, dest_lng)

    api_key = os.environ.get("GOOGLE_ROUTES_KEY")
    if not api_key:
        mins = _ors_minutes(orig_lat, orig_lng, dest_lat, dest_lng) \
               or _estimate_minutes(orig_lat, orig_lng, dest_lat, dest_lng)
        _eta_cache[key] = (time(), mins)
        return mins

    try:
        resp = httpx.post(
            "https://routes.googleapis.com/directions/v2:computeRoutes",
            json={
                "origin":      {"location": {"latLng": {"latitude": orig_lat, "longitude": orig_lng}}},
                "destination": {"location": {"latLng": {"latitude": dest_lat, "longitude": dest_lng}}},
                "travelMode":  "DRIVE",
                "routingPreference": "TRAFFIC_AWARE",
                "departureTime": _thai_now().strftime("%Y-%m-%dT%H:%M:%SZ"),
            },
            headers={
                "X-Goog-Api-Key":  api_key,
                "X-Goog-FieldMask": "routes.duration",
                "Content-Type":    "application/json",
            },
            timeout=10,
        )
        resp.raise_for_status()
        duration_s  = resp.json()["routes"][0]["duration"]   # "1234s"
        travel_mins = int(duration_s.replace("s", "")) // 60
        _eta_cache[key] = (time(), travel_mins)
        return travel_mins
    except Exception:
        # Google ใช้ไม่ได้ (key ผิด / ยังไม่เปิดบิล) → ถอยไปใช้ตัวสำรอง
        mins = _ors_minutes(orig_lat, orig_lng, dest_lat, dest_lng) \
               or _estimate_minutes(orig_lat, orig_lng, dest_lat, dest_lng)
        _eta_cache[key] = (time(), mins)
        return mins

# ─── DATA FETCHERS ───────────────────────────────────────────────────────────

def fetch_ptgl() -> dict[str, dict]:
    """
    คืน dict: car_no (str) → {lat, lng, location}
    เช่น {"465": {"lat": 13.75, "lng": 100.50, "location": "ถนนพระราม 9"}}
    """
    rows   = _fetch_sheet(PTGL_ID, PTGL_TAB)
    result: dict[str, dict] = {}
    for row in rows[1:]:
        car_no = _extract_car_no(_cell(row, PTGL_LICNO))
        if not car_no:
            continue
        try:
            lat = float(_cell(row, PTGL_LAT))
            lng = float(_cell(row, PTGL_LNG))
        except ValueError:
            continue
        if not (-90 <= lat <= 90 and -180 <= lng <= 180):
            continue
        result[car_no] = {
            "lat":      lat,
            "lng":      lng,
            "location": _cell(row, PTGL_LOC),
        }
    return result


def fetch_destinations() -> dict[str, tuple[float, float]]:
    """
    คืน dict: ชื่อปลายทาง → (lat, lng)
    เช่น {"สถานีบางนา": (13.661, 100.609)}
    """
    rows   = _fetch_sheet(DEST_ID, DEST_TAB)
    result: dict[str, tuple[float, float]] = {}
    for row in rows[1:]:
        name  = _cell(row, DEST_NAME)
        coord = _parse_coords(_cell(row, DEST_COORD))
        if name and coord:
            result[name] = coord
    return result


def fetch_trips(target_date: str) -> list[dict]:
    """คืนรายการทริปทั้งหมดของวันที่ระบุ"""
    rows  = _fetch_sheet(SOURCE_ID, PLAN_TAB)
    trips = []
    for i, row in enumerate(rows[1:], start=1):
        if _parse_date(_cell(row, PLAN_DATE)) != target_date:
            continue
        car_no = _cell(row, PLAN_CARNO)
        trips.append({
            "id":         i,
            "car_no":     car_no,                      # แสดงผลตามที่กรอกจริง
            "car_key":    _extract_car_no(car_no),     # ใช้จับคู่กับ PTGL
            "plate":      _cell(row, PLAN_PLATE),
            "trip_no":    _cell(row, PLAN_TRIP),
            "drop":       _cell(row, PLAN_DROP),
            "customer":   _cell(row, PLAN_DEST),
            "source":     _cell(row, PLAN_SOURCE),
            "volume":     _cell(row, PLAN_VOLUME),
            "invoice_no": _cell(row, PLAN_INVOICE),
            "sched_time": _cell(row, PLAN_SCHED),
            "gps_status": _cell(row, PLAN_GPS_ST),
            "ontime":     _cell(row, PLAN_ONTIME),                 # AV PASS / Delay
            "ontime_min": _cell(row, PLAN_ONTIME_M),               # AW นาทีที่ช้า
            "status_man": _cell(row, PLAN_STATUS),                 # AA กรอกมือ
            "call_time":  _cell_time(_cell(row, PLAN_P_CALL)),     # Z  ถึงเวลาโทรตาม
            "call_dt":    _cell_dt(_cell(row, PLAN_P_CALL)),       # Z  พร้อมวันที่ (อาจเป็นเมื่อวาน)
            "load_plan":  _cell_time(_cell(row, PLAN_P_LOAD)),     # Y  เวลาเข้าโหลด (แผน)
            "vtype":      _cell(row, PLAN_VTYPE),                  # ประเภทรถ
            "driver":     _cell(row, PLAN_DRIVER) or _cell(row, PLAN_DRIVER2),
            "phone":      _cell(row, PLAN_PHONE)  or _cell(row, PLAN_PHONE2),
            "due_date":   _parse_date(_cell(row, PLAN_DUE)) or target_date,   # F
            "arrive_dt":  _cell_dt(_cell(row, PLAN_ARRIVE)),       # AF พร้อมวันที่
            "yard_time":  _cell_time(_cell(row, PLAN_YARD)),       # AB
            "load_out":   _cell_time(_cell(row, PLAN_LOAD_OUT)),   # AD
            "depart":     _cell_time(_cell(row, PLAN_DEPART)),     # AE ออกคลังจริง
            "arrive":     _cell_time(_cell(row, PLAN_ARRIVE)),     # AF ถึงจริง
        })
    return trips

# ─── ENDPOINT ────────────────────────────────────────────────────────────────

@app.get("/api/trips", response_model=SummaryResponse, summary="ดึงทริป+ETA ตามวันที่")
def get_trips(
    date_str: str = Query(None, alias="date", description="yyyy-MM-dd (default=วันนี้)", example="2025-08-14")
):
    target = date_str or _today_thai()
    try:
        datetime.strptime(target, "%Y-%m-%d")
    except ValueError:
        raise HTTPException(400, "รูปแบบวันที่ต้องเป็น yyyy-MM-dd")

    try:
        ptgl_map = fetch_ptgl()
        dest_map = fetch_destinations()
        trips    = fetch_trips(target)
    except Exception as e:
        raise HTTPException(502, f"ดึงข้อมูล Google Sheet ไม่ได้: {type(e).__name__}: {e}")

    # ETA มีความหมายเฉพาะทริปของ "วันนี้" เท่านั้น
    # (พิกัดรถใน PTGL เป็นตำแหน่งปัจจุบัน เอาไปเทียบวันอื่นไม่ได้)
    is_today = target == _today_thai()

    # ให้สิทธิ์เรียก ORS เฉพาะทริปที่ใกล้ถึงกำหนดที่สุด (ที่เหลือใช้สูตรคำนวณ)
    # กัน Vercel timeout และ rate limit ของ ORS
    pending_ids = [
        t["id"] for t in sorted(
            (t for t in trips
             if not any(k in (t["gps_status"] + " " + t["status_man"]).lower()
                        for k in CANCEL_KEYWORDS + DONE_KEYWORDS)
             and not t["arrive"]),
            key=lambda t: _to_mins(t["sched_time"]) or 9999,
        )
    ]
    api_budget = set(pending_ids[:MAX_ROUTE_CALLS])

    results: list[TripOut] = []
    now_dt = _thai_now().replace(second=0, microsecond=0)

    for t in trips:
        use_api = t["id"] in api_budget
        sched_dt    = _sched_dt(t["due_date"], t["sched_time"])
        sched_mins  = _to_mins(t["sched_time"])

        def eta_of(mins: int) -> tuple[str, Optional[int]]:
            """นาทีเดินทาง → (เวลาถึง 'HH:MM', ช้ากี่นาทีเทียบกำหนดจริง)"""
            e = now_dt + timedelta(minutes=mins)
            d = int((e - sched_dt).total_seconds() // 60) if sched_dt else None
            return e.strftime("%H:%M"), d
        pos         = ptgl_map.get(t["car_key"])
        dest_coord  = dest_map.get(t["customer"])

        travel_mins   = None
        eta_time_str  = None
        diff_min      = None
        status        = "pending"
        prediction    = ""

        # ถ้าไม่พบใน PTGL ให้ลองใช้พิกัดคลังต้นทางแทน (รถยังอยู่คลัง)
        origin = pos or (
            {"lat": DEPOTS[t["source"]][0], "lng": DEPOTS[t["source"]][1], "location": t["source"]}
            if t["source"] in DEPOTS else None
        )

        actual   = False
        state_tx = (t["gps_status"] + " " + t["status_man"]).lower()
        done     = any(k in state_tx for k in DONE_KEYWORDS)

        if any(k in state_tx for k in CANCEL_KEYWORDS):
            # ─ ยกเลิก/โหลดเก็บ → ไม่นับเป็นงานค้าง ─
            status     = "cancelled"
            prediction = t["status_man"] or t["gps_status"] or "ยกเลิก"

        elif t["arrive"]:
            # ─ มีเวลาเข้าปลายทางจริง → วัดช้า/เร็วจากของจริง ไม่ใช่ประมาณการ ─
            status     = "arrived"
            actual     = True
            if t["arrive_dt"] is not None and sched_dt is not None:
                diff_min = int((t["arrive_dt"] - sched_dt).total_seconds() // 60)
                if diff_min > 15:
                    prediction = f"ถึง {t['arrive']} — ช้ากว่ากำหนด {diff_min} นาที"
                elif diff_min < -10:
                    prediction = f"ถึง {t['arrive']} — เร็วกว่ากำหนด {abs(diff_min)} นาที ✓"
                else:
                    prediction = f"ถึง {t['arrive']} — ตรงเวลา ✓"
            else:
                prediction = f"ถึงปลายทางแล้ว ({t['arrive']})"

        elif done:
            # ─ ชีตบอกว่าส่งเสร็จ แต่ไม่มีเวลาเข้าปลายทาง ─
            status     = "arrived"
            prediction = "จัดส่งเสร็จแล้ว"

        elif not is_today:
            # ─ ทริปวันอื่น: ดูสถานะจากชีตอย่างเดียว ไม่คำนวณ ETA ─
            status     = "pending"
            prediction = t["gps_status"] or "ไม่มีข้อมูลสถานะ"

        elif not t["yard_time"] and pos and t["source"] in DEPOTS and dest_coord:
            # ─ ช่วงที่ 1: ยังไม่เข้าลานจอด (AB ว่าง)
            #   คำนวณเส้นทางเต็ม: รถอยู่ตรงไหน → คลังต้นทาง → ปลายทาง ─
            depot = DEPOTS[t["source"]]
            to_depot = _get_travel_minutes(pos["lat"], pos["lng"], depot[0], depot[1], use_api)
            to_dest  = _get_travel_minutes(depot[0], depot[1],
                                           dest_coord[0], dest_coord[1], use_api)

            if to_depot is not None and to_dest is not None and sched_dt is not None:
                yard_m, load_m = _depot_minutes(t["source"], _vehicle_type(t["vtype"]))
                travel_mins  = to_depot + yard_m + load_m + to_dest
                eta_time_str, diff_min = eta_of(travel_mins)
                depot_eta    = eta_of(to_depot)[0]
                route        = (f"ถึงคลัง {t['source']} ~{depot_eta} "
                                f"(ลานจอด {yard_m} + โหลด {load_m} น.) "
                                f"แล้ววิ่งต่ออีก {to_dest} น.")
                if diff_min > 15:
                    status     = "late"
                    prediction = f"⚠ คาดว่าจะช้า {diff_min} นาที — {route}"
                elif diff_min < -10:
                    status     = "early"
                    prediction = f"จะถึงเร็วกว่ากำหนด {abs(diff_min)} นาที ✓ — {route}"
                else:
                    status     = "transit"
                    prediction = f"น่าจะถึงตรงเวลา — {route}"
            else:
                status     = "pending"
                prediction = f"ยังไม่เข้าคลัง {t['source']}"

        elif origin and dest_coord:
            # ─ ช่วงที่ 2: อยู่คลังแล้วหรือออกเดินทางแล้ว → ETA ถึง "ปลายทาง" ─
            travel = _get_travel_minutes(
                origin["lat"], origin["lng"],
                dest_coord[0], dest_coord[1],
                use_api,
            )
            # ยังโหลดไม่เสร็จ (AD ว่าง) → บวกเวลาที่ต้องใช้ในคลังเข้าไปด้วย
            if travel is not None and not t["load_out"]:
                yard_m, load_m = _depot_minutes(t["source"], _vehicle_type(t["vtype"]))
                travel += load_m if t["yard_time"] else yard_m + load_m

            if travel is not None and sched_dt is not None:
                travel_mins  = travel
                eta_time_str, diff_min = eta_of(travel)

                if diff_min < -10:
                    status     = "early"
                    prediction = f"จะถึงเร็วกว่ากำหนด {abs(diff_min)} นาที ✓"
                elif diff_min <= 15:
                    status     = "transit"
                    prediction = f"น่าจะถึงตรงเวลา (ห่างอีก {travel} นาที)"
                else:
                    status     = "late"
                    prediction = f"⚠ คาดว่าจะช้า {diff_min} นาที"
            else:
                status     = "transit"
                prediction = f"กำลังเดินทาง (ยังไม่มี ETA)"

        else:
            # ─ ไม่พบทั้ง PTGL และ DEPOTS → ดูจากเวลากำหนด ─
            if sched_mins and _now_mins() > sched_mins + 20:
                status     = "late"
                prediction = "⚠ เกินเวลากำหนดแล้ว (ไม่พบสัญญาณ GPS)"
            else:
                status     = "pending"
                prediction = "รอออกรถ"

        # ─ ยังไม่ออกจากคลัง และเลยเวลาโทรตาม พขร แล้ว → เตือนให้โทร ─
        # เทียบวันที่ด้วย เพราะเวลานัดโทรอาจเป็นของเมื่อวาน เช่น "19/08/2026, 22:00"
        if (status not in ("arrived", "cancelled") and not t["depart"]
                and t["call_dt"] is not None and now_dt >= t["call_dt"]):
            late_call = int((now_dt - t["call_dt"]).total_seconds() // 60)
            prediction = (f"📞 ถึงเวลาโทรตาม พขร (นัดไว้ {t['call_time']}"
                          + (f", เลยมา {late_call // 60} ชม." if late_call >= 60 else "")
                          + ") — ") + prediction

        results.append(TripOut(
            id           = t["id"],
            date         = target,
            car_no       = t["car_no"],
            plate        = t["plate"],
            trip_no      = t["trip_no"],
            drop         = t["drop"],
            customer     = t["customer"],
            source       = t["source"],
            volume       = t["volume"],
            invoice_no   = t["invoice_no"],
            sched_time   = t["sched_time"],
            gps_status   = t["status_man"] or t["gps_status"],
            ontime       = t["ontime"],
            ontime_min   = t["ontime_min"],
            driver       = t["driver"],
            phone        = t["phone"],
            yard_time    = t["yard_time"],
            load_out     = t["load_out"],
            depart_time  = t["depart"],
            arrive_time  = t["arrive"],
            current_lat  = pos["lat"]      if pos else None,
            current_lng  = pos["lng"]      if pos else None,
            current_loc  = pos["location"] if pos else None,
            travel_mins  = travel_mins,
            eta_time     = eta_time_str,
            status       = status,
            diff_minutes = diff_min,
            actual       = actual,
            prediction   = prediction,
        ))

    # ─── ทริปหลาย Drop ของรถคันเดียวกัน ───────────────────────────────────
    # Drop 2 ต้องเริ่มนับหลังส่ง Drop 1 เสร็จ ไม่ใช่คิดจากตำแหน่งปัจจุบันซ้ำ
    LIVE = ("late", "transit", "early", "pending")
    by_car: dict[str, list[int]] = {}
    for i, r in enumerate(results):
        if r.status in LIVE and trips[i]["car_key"]:
            by_car.setdefault(trips[i]["car_key"], []).append(i)

    for idxs in by_car.values():
        if len(idxs) < 2:
            continue
        idxs.sort(key=lambda i: (int(_extract_car_no(trips[i]["drop"]) or 0),
                                 _to_mins(trips[i]["sched_time"]) or 0))
        for prev_i, cur_i in zip(idxs, idxs[1:]):
            prev, cur = results[prev_i], results[cur_i]
            a = dest_map.get(trips[prev_i]["customer"])
            b = dest_map.get(trips[cur_i]["customer"])
            if prev.travel_mins is None or not a or not b:
                continue
            leg = _get_travel_minutes(a[0], a[1], b[0], b[1], False)
            if leg is None:
                continue
            total = prev.travel_mins + UNLOAD_MINS + leg
            sd    = _sched_dt(trips[cur_i]["due_date"], trips[cur_i]["sched_time"])
            e     = now_dt + timedelta(minutes=total)
            cur.travel_mins = total
            cur.eta_time    = e.strftime("%H:%M")
            note = (f"ต่อจาก Drop {trips[prev_i]['drop']} "
                    f"(ถึง ~{prev.eta_time} + ลงของ {UNLOAD_MINS} น. + วิ่ง {leg} น.)")
            if sd is None:
                cur.prediction = note
                continue
            cur.diff_minutes = int((e - sd).total_seconds() // 60)
            if cur.diff_minutes > 15:
                cur.status     = "late"
                cur.prediction = f"⚠ คาดว่าจะช้า {cur.diff_minutes} นาที — {note}"
            elif cur.diff_minutes < -10:
                cur.status     = "early"
                cur.prediction = f"จะถึงเร็วกว่ากำหนด {abs(cur.diff_minutes)} นาที ✓ — {note}"
            else:
                cur.status     = "transit"
                cur.prediction = f"น่าจะถึงตรงเวลา — {note}"

    arrived    = sum(1 for r in results if r.status == "arrived")
    in_transit = sum(1 for r in results if r.status in ("transit", "early"))
    late       = sum(1 for r in results if r.status == "late")
    pending    = sum(1 for r in results if r.status == "pending")
    cancelled  = sum(1 for r in results if r.status == "cancelled")

    return SummaryResponse(
        date       = target,
        fetched_at = _thai_now().strftime("%Y-%m-%dT%H:%M:%S+07:00"),
        total      = len(results),
        arrived    = arrived,
        in_transit = in_transit,
        late       = late,
        pending    = pending,
        cancelled  = cancelled,
        trips      = results,
    )


@app.get("/api/health")
def health():
    return {
        "status": "ok",
        "time_thai": _thai_now().strftime("%Y-%m-%d %H:%M:%S"),
        "sheet_cache_keys": list(_sheet_cache.keys()),
        "eta_cache_size":   len(_eta_cache),
    }


@app.get("/api/debug")
def debug():
    """ตรวจทีละขั้น ว่าติดตรงไหน"""
    out: dict = {}

    # 1. env var
    env = os.environ.get("GOOGLE_CREDENTIALS")
    out["has_GOOGLE_CREDENTIALS"]  = bool(env)
    out["has_GOOGLE_ROUTES_KEY"]   = bool(os.environ.get("GOOGLE_ROUTES_KEY"))
    out["has_SUPABASE_URL"]        = bool(SUPABASE_URL)
    out["has_SUPABASE_SERVICE_KEY"]= bool(SUPABASE_SERVICE_KEY)

    # 2. credentials parse
    try:
        creds = _build_creds()
        out["service_account_email"] = getattr(creds, "service_account_email", "?")
    except Exception as e:
        out["creds_error"] = f"{type(e).__name__}: {e}"
        return out

    # 3. เปิดแต่ละ Sheet / แต่ละแท็บ
    for label, sid, tab in (
        ("PTGL",   PTGL_ID, PTGL_TAB),
        ("SOURCE", SOURCE_ID, PLAN_TAB),   # ไฟล์ต้นทางจริง — รายการทริป
        ("DEST",   DEST_ID, DEST_TAB),     # พิกัดปลายทาง (ไฟล์เดียวกับ SOURCE)
        ("PLAN",   PLAN_ID, PLAN_TAB),     # Test Report Ontime PTGLG — ไทม์ไลน์/ChaseLog เท่านั้น
    ):
        try:
            gc = gspread.authorize(creds)
            sh = gc.open_by_key(sid)
            out[f"{label}_title"] = sh.title
            out[f"{label}_tabs"]  = [w.title for w in sh.worksheets()]
            rows = sh.worksheet(tab).get_all_values()
            out[f"{label}_rows"]  = len(rows)
        except Exception as e:
            out[f"{label}_error"] = f"{type(e).__name__}: {e!r}"
            out[f"{label}_trace"] = traceback.format_exc().splitlines()[-12:]

    return out


# ─── ChaseLog — บันทึกว่าไล่รถคันไหนไปแล้ว ────────────────────────────────
# เก็บแยกแท็บ "ChaseLog_dd.mm.yyyy" ต่อวัน (เหมือนแท็บ GPS รายวัน) แทนแท็บเดียวยาวๆ
# โครงสร้าง: A=key B=วันที่ C=เบอร์รถ D=ปลายทาง E=ไล่เมื่อ F=สถานะ G=พิกัดตอนกด H=โดย

CHASE_HEADER = ["key", "date", "car_no", "customer", "chased_at", "status", "location", "by"]


def _chase_tab_name(date_str: str) -> str:
    try:
        d = datetime.strptime(date_str, "%Y-%m-%d")
        return f"{CHASE_TAB}_{d.strftime('%d.%m.%Y')}"
    except ValueError:
        return f"{CHASE_TAB}_{date_str}"


def _chase_ws(date_str: str):
    """เปิดแท็บ ChaseLog ของวันนั้นๆ ถ้ายังไม่มีก็สร้างให้"""
    sh  = gspread.authorize(_build_creds()).open_by_key(PLAN_ID)
    tab = _chase_tab_name(date_str)
    try:
        return sh.worksheet(tab)
    except gspread.WorksheetNotFound:
        ws = sh.add_worksheet(title=tab, rows=2000, cols=8)
        ws.update("A1:H1", [CHASE_HEADER])
        return ws


def _update_daily_status(key: str, date_str: str, status: str) -> None:
    """เขียนสถานะลงคอลัมน์ L "สถานะปัจจุบัน" ของแท็บรายวัน (dd.mm.yyyy) ตรงแถวทริปนั้นด้วย
    เพิ่มเติมจาก ChaseLog — เป็น best-effort เท่านั้น หาไม่เจอ/แท็บไม่มีก็แค่ข้าม ไม่ throw"""
    try:
        parts = key.split("|")
        if len(parts) < 4:
            return
        car_no, trip_no, drop = parts[1], parts[2], parts[3]
        d = datetime.strptime(date_str, "%Y-%m-%d")
        tab_name = d.strftime("%d.%m.%Y")
        # อ่านผ่านแคช (5 นาที) แทนการอ่านสดทุกครั้ง — กัน quota "Read requests/min" หมด
        # ตอนมีคนกดอัปเดตสถานะหลายคันรวดเดียว (เขียนยังเป็นของสดเสมอ)
        rows = _fetch_sheet(PLAN_ID, tab_name)
        car_key = _extract_car_no(car_no)
        row_i = None
        for i, row in enumerate(rows[1:], start=2):
            if (_extract_car_no(_cell(row, 5)) == car_key
                    and _cell(row, 2).strip() == trip_no.strip()
                    and _cell(row, 3).strip() == drop.strip()):
                row_i = i
                break
        if row_i is None:
            return
        sh = gspread.authorize(_build_creds()).open_by_key(PLAN_ID)
        ws = sh.worksheet(tab_name)
        ws.update_cell(row_i, 12, status)   # col L = 12 (1-based)
    except Exception:
        pass


@app.get("/api/chase", include_in_schema=False)
def chase_list(date_str: str = Query(None, alias="date")):
    """คืนรายการที่ไล่แล้วของวันนั้น {key: {"at": "17:54", "status": "...", "loc": "...", "by": "..."}}"""
    target = date_str or _today_thai()
    try:
        rows = _chase_ws(target).get_all_values()
    except Exception as e:
        raise HTTPException(502, f"อ่าน ChaseLog ไม่ได้: {type(e).__name__}: {e}")
    out = {}
    for r in rows[1:]:
        if _cell(r, 0):
            out[_cell(r, 0)] = {
                "at": _cell(r, 4), "status": _cell(r, 5),
                "loc": _cell(r, 6), "by": _cell(r, 7),
            }
    return out


@app.post("/api/chase", include_in_schema=False)
def chase_set(
    key:      str = Form(...),
    date_str: str = Form(..., alias="date"),
    car_no:   str = Form(""),
    customer: str = Form(""),
    status:   str = Form(""),
    location: str = Form(""),
    by:       str = Form(""),
    clear:    str = Form(""),
):
    """ติ๊ก = บันทึกเวลาไล่  /  เอาติ๊กออก = ลบแถวนั้น"""
    try:
        ws   = _chase_ws(date_str)
        # อ่านผ่านแคชแทนอ่านสด — กัน quota หมดตอนมีคนกดอัปเดตหลายคันรวดเดียว
        # (เผื่อกดซ้ำคันเดิมในเครื่องกัน 5 นาที อาจได้แถวใหม่ซ้ำแทนอัปเดตแถวเดิม ไม่ใช่ปัญหาใหญ่)
        rows = _fetch_sheet(PLAN_ID, _chase_tab_name(date_str))
        hit  = next((i for i, r in enumerate(rows[1:], start=2)
                     if _cell(r, 0) == key), None)

        chase_cache_key = f"{PLAN_ID}:{_chase_tab_name(date_str)}"

        if clear:
            if hit:
                ws.delete_rows(hit)
            _sheet_cache.pop(chase_cache_key, None)   # เคลียร์แคช ครั้งหน้าจะอ่านของสด
            _update_daily_status(key, date_str, "")
            return {"ok": True, "cleared": True}

        at = _thai_now().strftime("%H:%M")
        row = [key, date_str, car_no, customer, at, status, location, by]
        if hit:
            ws.update(f"A{hit}:H{hit}", [row])
        else:
            ws.append_row(row, value_input_option="USER_ENTERED")
        _sheet_cache.pop(chase_cache_key, None)
        _update_daily_status(key, date_str, status)
        return {"ok": True, "at": at}
    except Exception as e:
        raise HTTPException(502, f"บันทึก ChaseLog ไม่ได้: {type(e).__name__}: {e}")


@app.get("/api/cron/hourly-status", include_in_schema=False)
def cron_hourly_status(secret: str = Query("")):
    """เรียกจาก Apps Script (trigger ทุกชั่วโมง) — เก็บพิกัดปัจจุบันของทุกคันที่ยังไม่ถึง/ยังไม่ยกเลิก
    ลง ChaseLog เป็นแถวใหม่ทุกครั้ง และเขียนพิกัดล่าสุดทับคอลัมน์ L ในแท็บรายวันด้วย"""
    if not CRON_SECRET or secret != CRON_SECRET:
        raise HTTPException(401, "unauthorized")

    target = _today_thai()
    result = get_trips(date_str=target)
    at     = _thai_now().strftime("%H:%M")
    saved  = 0
    for t in result.trips:
        if t.status in ("arrived", "cancelled"):
            continue
        loc = t.current_loc or (
            f"{t.current_lat:.5f}, {t.current_lng:.5f}" if t.current_lat is not None else ""
        )
        if not loc:
            continue
        key = f"{t.date}|{t.car_no}|{t.trip_no}|{t.drop}|{t.invoice_no}"
        row = [key, target, t.car_no, t.customer, at, "", loc, "ระบบ (ทุกชั่วโมง)"]
        _update_daily_status(key, target, loc)   # อัปเดตคอลัมน์ L ด้วยพิกัดล่าสุด (best-effort)
        try:
            _chase_ws(target).append_row(row, value_input_option="USER_ENTERED")
            saved += 1
        except Exception:
            continue
    return {"ok": True, "date": target, "saved": saved, "checked": len(result.trips)}


@app.get("/api/peek")
def peek():
    """ดูข้อมูลดิบ 5 แถวแรกของแผนงาน เพื่อเช็คว่าคอลัมน์/วันที่ตรงไหม"""
    rows = _fetch_sheet(SOURCE_ID, PLAN_TAB)
    return {
        "header": rows[0] if rows else [],
        "sample": [
            {
                "row":        i,
                "date_raw":   _cell(r, PLAN_DATE),
                "date_parsed": _parse_date(_cell(r, PLAN_DATE)),
                "sched":      _cell(r, PLAN_SCHED),
                "customer":   _cell(r, PLAN_DEST),
                "car_no":     _cell(r, PLAN_CARNO),
            }
            for i, r in enumerate(rows[1:6], start=2)
        ],
        "all_dates_found": sorted({
            _parse_date(_cell(r, PLAN_DATE)) or _cell(r, PLAN_DATE)
            for r in rows[1:] if _cell(r, PLAN_DATE)
        })[:30],
    }


@app.get("/api/peekdest")
def peekdest():
    """ดูข้อมูลดิบแท็บ ข้อมูลปลายทาง เพื่อหาว่าคอลัมน์ไหนคือชื่อ/พิกัด"""
    rows = _fetch_sheet(DEST_ID, DEST_TAB)
    def label(r):
        return {f"col_{chr(65+i)}": v for i, v in enumerate(r[:14])}
    return {
        "total_rows": len(rows),
        "header":     label(rows[0]) if rows else {},
        "sample":     [label(r) for r in rows[1:6]],
    }


@app.get("/api/tab")
def peek_tab(
    sheet: str = Query("plan", description="plan | ptgl"),
    tab:   str = Query(..., description="ชื่อแท็บ"),
    rows:  int = Query(3, ge=1, le=10),
):
    """ส่องหัวตาราง+ตัวอย่างข้อมูลของแท็บใดก็ได้ (ใช้หาว่าคอลัมน์ไหนเก็บอะไร)"""
    sid  = PTGL_ID if sheet == "ptgl" else PLAN_ID
    data = _fetch_sheet(sid, tab)
    def label(r):
        out = {}
        for i, v in enumerate(r[:26]):
            col = chr(65 + i) if i < 26 else "A" + chr(65 + i - 26)
            if str(v).strip():
                out[col] = v
        return out
    return {"tab": tab, "total_rows": len(data),
            "header": label(data[0]) if data else {},
            "sample": [label(r) for r in data[1:1 + rows]]}


# ตำแหน่งย้อนหลังรายชั่วโมงต่อคัน -- Gasbulk Track เองไม่มีที่เก็บประวัติ
# (PTGL เป็น "ตำแหน่งปัจจุบัน" อย่างเดียว บันทึกซ้ำก็ยังเป็นค่าล่าสุดเสมอ)
# แต่สเปรดชีตเดียวกับ PLAN_ID มีแท็บรายวัน (ชื่อแท็บ = dd.MM.yyyy เช่น
# "29.08.2026") ที่ Apps Script อีกตัว (Test Report Ontime PTGLG) คอย
# บันทึกตำแหน่งทุกชั่วโมงลงไว้อยู่แล้ว เลยอ่านจากตรงนั้นแทนการสร้างระบบ
# เก็บประวัติของตัวเอง
TIMELINE_CARNO_COL = 5  # F "เบอร์รถ" ในแท็บรายวัน (0-based)


@app.get("/api/timeline")
def timeline(
    car_no:   str = Query(..., description="เบอร์รถ เช่น PTL.403 หรือ NO.418"),
    date_str: str = Query(None, alias="date", description="yyyy-MM-dd (default=วันนี้)", example="2026-08-29"),
):
    """ตำแหน่งรายชั่วโมงของรถคันเดียวในวันที่ระบุ จากแท็บรายวันในสเปรดชีต PLAN"""
    if date_str:
        try:
            d = datetime.strptime(date_str, "%Y-%m-%d")
        except ValueError:
            raise HTTPException(400, "date ต้องเป็นรูปแบบ yyyy-MM-dd")
    else:
        d = datetime.strptime(_today_thai(), "%Y-%m-%d")
    tab_name = d.strftime("%d.%m.%Y")

    try:
        rows = _fetch_sheet(PLAN_ID, tab_name)
    except Exception as e:
        return {"tab": tab_name, "car_no": car_no, "found": False,
                "error": f"ไม่พบแท็บ {tab_name} (ยังไม่มีข้อมูลของวันนี้ หรือยังไม่ได้รันบันทึกตำแหน่ง): {type(e).__name__}",
                "timeline": []}

    if not rows:
        return {"tab": tab_name, "car_no": car_no, "found": False, "timeline": []}

    header = rows[0]
    hour_cols: list[tuple[int, str]] = []
    for i, h in enumerate(header):
        m = re.match(r"^(\d{1,2}):00\s*น\.?", str(h).strip())
        if m:
            hour_cols.append((i, str(h).strip()))

    car_key = _extract_car_no(car_no)
    match_row = None
    if car_key:
        for r in rows[1:]:
            if _extract_car_no(_cell(r, TIMELINE_CARNO_COL)) == car_key:
                match_row = r
                break

    if match_row is None:
        return {"tab": tab_name, "car_no": car_no, "found": False, "timeline": []}

    entries = []
    for idx, label in hour_cols:
        val = _cell(match_row, idx)
        if val:
            entries.append({"hour": label, "raw": val})

    return {"tab": tab_name, "car_no": car_no, "found": True, "timeline": entries}


@app.get("/api/match")
def match(date_str: str = Query(None, alias="date")):
    """เช็คว่าเบอร์รถ / ชื่อปลายทาง จับคู่กันได้กี่รายการ"""
    target   = date_str or _today_thai()
    ptgl_map = fetch_ptgl()
    dest_map = fetch_destinations()
    trips    = fetch_trips(target)

    car_hit  = [t["car_no"]   for t in trips if t["car_key"] in ptgl_map]
    car_miss = [t["car_no"]   for t in trips if t["car_key"] not in ptgl_map]
    dst_hit  = [t["customer"] for t in trips if t["customer"] in dest_map]
    dst_miss = [t["customer"] for t in trips if t["customer"] not in dest_map]

    return {
        "date":            target,
        "trips":           len(trips),
        "car_matched":     len(car_hit),
        "car_unmatched":   sorted(set(car_miss))[:20],
        "dest_matched":    len(dst_hit),
        "dest_unmatched":  sorted(set(dst_miss))[:20],
        "ptgl_keys_sample":  sorted(ptgl_map.keys())[:20],
        "dest_names_sample": sorted(dest_map.keys())[:20],
    }


@app.get("/", response_class=HTMLResponse, include_in_schema=False)
def dashboard():
    warn = "" if _app_password() else "1"
    return DASHBOARD_HTML.replace("__NOPASS__", warn)


@app.get("/login", response_class=HTMLResponse, include_in_schema=False)
def login_page(error: str = ""):
    if not _app_password():
        return RedirectResponse("/", status_code=303)
    msg = ('<p class="err">รหัสผ่านไม่ถูกต้อง</p>' if error else "")
    return LOGIN_HTML.replace("__ERR__", msg)


@app.post("/api/login", include_in_schema=False)
def do_login(password: str = Form("")):
    pw = _app_password()
    if not pw or not hmac.compare_digest(password, pw):
        return RedirectResponse("/login?error=1", status_code=303)

    resp = RedirectResponse("/", status_code=303)
    resp.set_cookie(
        COOKIE_NAME, _make_token(),
        max_age=SESSION_HOURS * 3600,
        httponly=True, secure=True, samesite="lax", path="/",
    )
    return resp


@app.get("/logout", include_in_schema=False)
def logout():
    resp = RedirectResponse("/login", status_code=303)
    resp.delete_cookie(COOKIE_NAME, path="/")
    return resp


@app.get("/settings", response_class=HTMLResponse, include_in_schema=False)
def settings_page():
    return SETTINGS_HTML.replace("__PWSET__", "ตั้งแล้ว ✓" if _app_password() else "ยังไม่ได้ตั้ง")


LOGIN_HTML = """<!doctype html>
<html lang="th"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>เข้าสู่ระบบ — Gasbulk Track</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;600;700&display=swap" rel="stylesheet">
<style>
  :root{--bg:#f1f5f9;--card:#fff;--line:#e2e8f0;--ink:#0f172a;--mut:#64748b}
  @media (prefers-color-scheme:dark){
    :root{--bg:#0b1220;--card:#131c2e;--line:#243044;--ink:#e8eef8;--mut:#93a3b8}}
  *{box-sizing:border-box}
  body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;
       background:var(--bg);color:var(--ink);padding:20px;
       font-family:'Noto Sans Thai',system-ui,sans-serif}
  form{background:var(--card);border:1px solid var(--line);border-radius:16px;
       padding:30px 26px;width:100%;max-width:360px}
  h1{font-size:21px;margin:0 0 6px}
  p.sub{color:var(--mut);font-size:14px;margin:0 0 22px}
  label{display:block;font-size:13.5px;font-weight:600;margin-bottom:7px}
  input{width:100%;padding:12px 14px;font-size:16px;font-family:inherit;
        border:1px solid var(--line);border-radius:10px;background:var(--bg);color:var(--ink)}
  button{width:100%;margin-top:16px;padding:12px;font-size:15px;font-weight:700;
         font-family:inherit;border:0;border-radius:10px;background:#2563eb;color:#fff;cursor:pointer}
  button:hover{background:#1d4ed8}
  .err{color:#dc2626;font-size:13.5px;margin:0 0 14px;font-weight:600}
</style></head>
<body>
  <form method="post" action="/api/login">
    <h1>🚛 Gasbulk Track</h1>
    <p class="sub">ระบบติดตามรถขนส่ง — กรุณาเข้าสู่ระบบ</p>
    __ERR__
    <label for="pw">รหัสผ่าน</label>
    <input id="pw" name="password" type="password" autofocus required
           autocomplete="current-password" placeholder="ใส่รหัสผ่าน">
    <button type="submit">เข้าสู่ระบบ</button>
  </form>
</body></html>
"""


SETTINGS_HTML = """<!doctype html>
<html lang="th"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>ตั้งค่า — Gasbulk Track</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root{--bg:#f1f5f9;--card:#fff;--line:#e2e8f0;--ink:#0f172a;--mut:#64748b}
  @media (prefers-color-scheme:dark){
    :root{--bg:#0b1220;--card:#131c2e;--line:#243044;--ink:#e8eef8;--mut:#93a3b8}}
  *{box-sizing:border-box}
  body{margin:0;background:var(--bg);color:var(--ink);padding:20px;
       font-family:'Noto Sans Thai',system-ui,sans-serif;font-size:15px}
  .box{max-width:640px;margin:0 auto}
  h1{font-size:20px;margin:0 0 18px}
  section{background:var(--card);border:1px solid var(--line);border-radius:14px;
          padding:18px 20px;margin-bottom:16px}
  h2{font-size:15px;margin:0 0 14px}
  label{display:block;font-size:13.5px;color:var(--mut);margin:12px 0 6px;font-weight:500}
  select,input{width:100%;padding:10px 12px;font-size:15px;font-family:inherit;
        border:1px solid var(--line);border-radius:9px;background:var(--bg);color:var(--ink)}
  button{padding:10px 18px;font-size:14px;font-weight:700;font-family:inherit;
         border:0;border-radius:9px;background:#2563eb;color:#fff;cursor:pointer;margin-top:16px}
  a.back{color:#2563eb;text-decoration:none;font-weight:600}
  a.out{color:#dc2626;text-decoration:none;font-weight:600}
  .row{display:flex;justify-content:space-between;padding:9px 0;
       border-bottom:1px solid var(--line);font-size:14px}
  .row:last-child{border:0}
  .row span{color:var(--mut)}
  .ok{color:#16a34a;font-weight:600}
  .btns{display:flex;flex-wrap:wrap;gap:8px}
  .pbtn{padding:8px 14px;border-radius:999px;border:1px solid var(--line);background:var(--bg);
        color:var(--ink);cursor:pointer;font-size:13.5px;font-weight:600;font-family:inherit;margin:0}
  .pbtn:hover{border-color:#2563eb;color:#2563eb}
  .pbtn.on{background:#2563eb;border-color:#2563eb;color:#fff}
</style></head>
<body><div class="box">
  <p><a class="back" href="/">&larr; กลับหน้าตาราง</a></p>
  <h1>⚙️ ตั้งค่า</h1>

  <section>
    <h2>การแสดงผล</h2>
    <label>รีเฟรชข้อมูลอัตโนมัติทุก</label>
    <div class="btns" id="ivBtns">
      <button type="button" class="pbtn" data-v="5">5 นาที</button>
      <button type="button" class="pbtn" data-v="10">10 นาที</button>
      <button type="button" class="pbtn" data-v="15">15 นาที</button>
      <button type="button" class="pbtn" data-v="30">30 นาที</button>
      <button type="button" class="pbtn" data-v="60">1 ชั่วโมง</button>
      <button type="button" class="pbtn" data-v="120">2 ชั่วโมง</button>
      <button type="button" class="pbtn" data-v="0">ไม่รีเฟรชอัตโนมัติ</button>
    </div>
    <label for="ft">มุมมองเริ่มต้นเมื่อเปิดหน้า</label>
    <select id="ft">
      <option value="hour">⏰ ต้องไล่ชั่วโมงนี้</option>
      <option value="late">🔴 ช้า</option>
      <option value="active">🚚 ยังไม่ถึง</option>
      <option value="all">ทั้งหมด</option>
    </select>
    <label>บันทึกสถานะที่แก้ไข (จากปุ่มอัปเดตสถานะ) ลง Sheet ทุก</label>
    <div class="btns" id="svBtns">
      <button type="button" class="pbtn" data-v="5">5 นาที</button>
      <button type="button" class="pbtn" data-v="10">10 นาที</button>
      <button type="button" class="pbtn" data-v="15">15 นาที</button>
      <button type="button" class="pbtn" data-v="20">20 นาที</button>
      <button type="button" class="pbtn" data-v="30">30 นาที</button>
      <button type="button" class="pbtn" data-v="60">1 ชั่วโมง</button>
    </div>
    <button id="save">บันทึก</button>
    <span id="done" class="ok" style="margin-left:10px"></span>
  </section>

  <section>
    <h2>ระบบ</h2>
    <div class="row"><span>รหัสผ่านเข้าระบบ</span><b>__PWSET__</b></div>
    <div class="row"><span>แหล่งข้อมูล ETA</span><b>OpenRouteService</b></div>
    <div class="row"><span>เวลาโหลดที่คลัง</span><b>ตามตารางมาตรฐาน</b></div>
    <div class="row"><span>อายุการล็อกอิน</span><b>12 ชั่วโมง</b></div>
    <p style="color:var(--mut);font-size:13px;margin:14px 0 0">
      ค่าเหล่านี้แก้ที่ Vercel → Settings → Environment Variables
      (APP_PASSWORD, ORS_KEY) หรือในไฟล์ main.py
    </p>
  </section>

  <section>
    <h2>บัญชี</h2>
    <p style="margin:0"><a class="out" href="/logout">ออกจากระบบ</a></p>
  </section>
</div>
<script>
  const ft = document.getElementById('ft');
  let ivValue = localStorage.getItem('gb_interval') || '60';
  ft.value = localStorage.getItem('gb_filter') || 'hour';

  const ivBtns = document.querySelectorAll('#ivBtns .pbtn');
  function paintIvBtns(){
    ivBtns.forEach(b => b.classList.toggle('on', b.dataset.v === ivValue));
  }
  paintIvBtns();
  ivBtns.forEach(b => b.onclick = () => { ivValue = b.dataset.v; paintIvBtns(); });

  let svValue = localStorage.getItem('gb_save_interval') || '20';
  const svBtns = document.querySelectorAll('#svBtns .pbtn');
  function paintSvBtns(){
    svBtns.forEach(b => b.classList.toggle('on', b.dataset.v === svValue));
  }
  paintSvBtns();
  svBtns.forEach(b => b.onclick = () => { svValue = b.dataset.v; paintSvBtns(); });

  document.getElementById('save').onclick = () => {
    localStorage.setItem('gb_interval', ivValue);
    localStorage.setItem('gb_filter',   ft.value);
    localStorage.setItem('gb_save_interval', svValue);
    document.getElementById('done').textContent = 'บันทึกแล้ว ✓';
    setTimeout(() => document.getElementById('done').textContent = '', 2000);
  };
</script>
</body></html>
"""


# ─── DASHBOARD ───────────────────────────────────────────────────────────────

DASHBOARD_HTML = """<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Gasbulk Track — ติดตามรถขนส่ง</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root{
    --bg:#f1f5f9; --card:#fff; --line:#e2e8f0; --ink:#0f172a; --mut:#64748b;
    --late:#dc2626; --late-bg:#fef2f2; --ok:#16a34a; --ok-bg:#f0fdf4;
    --tr:#2563eb;  --tr-bg:#eff6ff;  --pd:#64748b; --pd-bg:#f8fafc;
    --early:#0891b2; --early-bg:#ecfeff;
  }
  @media (prefers-color-scheme:dark){
    :root{ --bg:#0b1220; --card:#131c2e; --line:#243044; --ink:#e8eef8; --mut:#93a3b8;
           --late-bg:#3b1418; --ok-bg:#0e2a19; --tr-bg:#0f2340; --pd-bg:#1a2434; --early-bg:#0c2b31; }
  }
  *{box-sizing:border-box}
  body{margin:0;background:var(--bg);color:var(--ink);
       font-family:'Noto Sans Thai',system-ui,-apple-system,sans-serif;font-size:15px}
  header{background:var(--card);border-bottom:1px solid var(--line);padding:14px 18px;
         position:sticky;top:0;z-index:10}
  .bar{display:flex;flex-wrap:wrap;gap:10px;align-items:center;width:100%}
  h1{font-size:19px;margin:0;font-weight:700;letter-spacing:-.2px}
  .grow{flex:1}
  input,button{font-family:inherit;font-size:14px;padding:8px 12px;border-radius:9px;
               border:1px solid var(--line);background:var(--card);color:var(--ink)}
  input[type=search]{min-width:190px}
  button{cursor:pointer;font-weight:600}
  button.primary{background:#2563eb;border-color:#2563eb;color:#fff}
  button.primary:hover{background:#1d4ed8}
  button.save-now{background:var(--late-bg);border-color:var(--late);color:var(--late)}
  button.save-now:hover{background:var(--late);color:#fff}
  main{width:100%;padding:16px}
  .pin{position:sticky;top:var(--hh,60px);z-index:9;background:var(--bg);padding-top:2px;margin:0 -16px;
       padding-left:16px;padding-right:16px}
  .cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:12px;margin-bottom:18px}
  .c{background:var(--card);border:1px solid var(--line);border-radius:13px;padding:14px 16px}
  .c b{display:block;font-size:27px;font-weight:700;line-height:1.15}
  .c span{color:var(--mut);font-size:13px;font-weight:500}
  .c.late b{color:var(--late)} .c.ok b{color:var(--ok)} .c.tr b{color:var(--tr)}
  .wrap{background:var(--card);border:1px solid var(--line);border-radius:13px;
        overflow:auto;height:calc(100vh - 280px)}
  table{border-collapse:separate;border-spacing:0;width:100%;min-width:1010px}
  th,td{padding:3px 6px;text-align:left;border-bottom:1px solid var(--line);white-space:nowrap;font-size:12.5px}
  th{font-size:12.5px;color:var(--mut);font-weight:600;text-transform:uppercase;
     letter-spacing:.4px;background:var(--card);position:sticky;top:0;z-index:2}
  tbody tr:hover{background:var(--pd-bg)}
  /* บีบให้ทุกแถวสูงบรรทัดเดียว อ่านง่ายขึ้นมาก */
  td.wide{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:170px}
  td.cust{max-width:200px;font-weight:500;white-space:normal;overflow:visible;text-overflow:clip;
          word-break:break-word;line-height:1.2}
  tbody tr:nth-child(even){background:var(--pd-bg)}
  tbody tr:nth-child(even):hover,tbody tr:hover{background:var(--tr-bg)}
  /* ซ่อนคอลัมน์ On Time ถ้าทั้งวันยังไม่มีข้อมูล */
  table.hide-ot th:nth-child(15),table.hide-ot td:nth-child(15){display:none}
  .badge{display:inline-block;padding:2px 8px;border-radius:999px;font-size:12px;font-weight:600}
  .s-late{background:var(--late-bg);color:var(--late)}
  .s-arrived{background:var(--ok-bg);color:var(--ok)}
  .s-transit{background:var(--tr-bg);color:var(--tr)}
  .s-early{background:var(--early-bg);color:#0891b2}
  .s-pending{background:var(--pd-bg);color:var(--pd)}
  .s-cancelled{background:var(--pd-bg);color:var(--pd);text-decoration:line-through}
  .mut{color:var(--mut)}
  .mono{font-variant-numeric:tabular-nums}
  .chips{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:14px}
  .chip{padding:7px 15px;border-radius:999px;border:1px solid var(--line);background:var(--card);
        color:var(--mut);cursor:pointer;font-size:13.5px;font-weight:600}
  .chip:hover{border-color:#2563eb;color:#2563eb}
  .chip.on{background:#2563eb;border-color:#2563eb;color:#fff}
  .note{color:var(--mut);font-size:13px;margin:10px 2px}
  .empty{padding:48px;text-align:center;color:var(--mut)}
  .dot{display:inline-block;width:7px;height:7px;border-radius:50%;background:var(--ok);margin-right:6px}
  .chk select{padding:4px 6px;border-radius:8px;border:1px solid var(--line);
              background:var(--card);color:var(--ink);font-family:inherit;font-size:12.5px;
              min-width:118px;cursor:pointer}
  .chk select:hover{border-color:#2563eb}
  .donebtn{padding:4px 9px;border-radius:8px;border:1px solid var(--line);background:var(--card);
           color:var(--mut);font-family:inherit;font-size:12px;font-weight:600;cursor:pointer;
           white-space:nowrap}
  .donebtn:hover{border-color:#16a34a;color:#16a34a}
  .donebtn.on{background:var(--ok-bg);border-color:var(--ok);color:var(--ok)}
  .cursts{font-size:13px;font-weight:700;color:var(--ok);margin-bottom:4px}
  .at{font-size:12px;color:var(--mut);margin-top:3px;white-space:nowrap}
  tr.done{opacity:.55}
  tr.done .at{color:var(--ok);font-weight:600}
  .callnow{display:inline-block;margin-left:6px;font-size:12px;color:var(--late);font-weight:600}
  .gear{text-decoration:none;font-size:19px;padding:6px 9px;border-radius:9px;
        border:1px solid var(--line);line-height:1}
  .gear:hover{border-color:#2563eb}
  .warn{background:#fef2f2;color:#b91c1c;border-bottom:1px solid #fecaca;
        padding:10px 18px;font-size:13.5px}

  /* ── มือถือ: เปลี่ยนตารางเป็นการ์ด อ่านง่ายไม่ต้องเลื่อนซ้ายขวา ── */
  @media (max-width:820px){
    body{font-size:15px}
    header{padding:11px 12px}
    h1{font-size:17px}
    main{padding:12px}
    .pin{margin:0 -12px;padding-left:12px;padding-right:12px}
    input[type=search],input[type=date]{flex:1 1 130px;min-width:0}
    .cards{grid-template-columns:repeat(3,1fr);gap:8px}
    .c{padding:10px}
    .c b{font-size:21px}
    .c span{font-size:11.5px}
    .chips{overflow-x:auto;flex-wrap:nowrap;padding-bottom:4px}
    .chip{flex:0 0 auto}

    .wrap{background:none;border:0;overflow:visible;height:auto}
    table,thead,tbody,tr,td{display:block;width:auto}
    table{min-width:0}
    thead{display:none}
    tr{background:var(--card);border:1px solid var(--line);border-radius:13px;
       padding:12px 14px;margin-bottom:11px}
    tbody tr:hover{background:var(--card)}
    td{border:0;padding:3px 0;white-space:normal;display:flex;gap:10px;
       align-items:flex-start;justify-content:space-between}
    td::before{content:attr(data-l);color:var(--mut);font-size:12.5px;
               flex:0 0 40%;font-weight:500}
    td.wide,td.cust{max-width:none;min-width:0}
    /* เบอร์รถ + ลูกค้า + สถานะ = ข้อมูลหลัก ทำให้เด่น */
    td.carno{font-size:20px;padding-bottom:2px}
    td.carno::before{align-self:center}
    td.cust{font-weight:600}
    /* ชื่อลูกค้า/ปลายทางยาวเกิน ตัดให้อยู่บรรทัดเดียวด้วย ... แทนที่จะล้นออกนอกการ์ด */
    td.cust .v{flex:1 1 0%;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;text-align:right}
    td.st{padding-top:7px}
    .call{padding:9px 15px;font-size:15px}
    .copy{padding:9px 11px}
  }
  .call{display:inline-block;margin-top:2px;padding:3px 8px;border-radius:8px;
        background:var(--ok-bg);color:var(--ok);font-weight:600;font-size:12px;
        text-decoration:none;white-space:nowrap}
  .call:hover{background:var(--ok);color:#fff}
  .copy{padding:3px 6px;border-radius:8px;border:1px solid var(--line);
        background:var(--card);cursor:pointer;font-size:12px;line-height:1}
  .copy:hover{border-color:#2563eb}

  /* ── Timeline modal (คลิกเบอร์รถ → ตำแหน่งย้อนหลังรายชั่วโมง) ── */
  td.carno{cursor:pointer}
  td.carno b{text-decoration:underline;text-decoration-color:var(--line);text-underline-offset:3px}
  td.carno:hover b{text-decoration-color:#2563eb;color:#2563eb}
  .tl-backdrop{position:fixed;inset:0;background:rgba(15,23,42,.5);z-index:50;
               display:flex;align-items:flex-start;justify-content:center;padding:40px 16px;overflow:auto}
  .tl-backdrop.hidden{display:none}
  .tl-modal{background:var(--card);border:1px solid var(--line);border-radius:14px;
            width:100%;max-width:520px;padding:18px 20px;max-height:calc(100vh - 80px);
            display:flex;flex-direction:column}
  .tl-head{display:flex;align-items:center;justify-content:space-between;margin-bottom:4px}
  .tl-head h2{font-size:17px;margin:0;font-weight:700}
  .tl-head button{border:none;background:none;font-size:20px;cursor:pointer;color:var(--mut);padding:2px 6px}
  .tl-sub{color:var(--mut);font-size:13px;margin-bottom:12px}
  .tl-list{overflow-y:auto;padding-right:2px}
  .tl-row{display:flex;gap:12px;padding:9px 0;border-bottom:1px solid var(--line)}
  .tl-row:last-child{border-bottom:0}
  .tl-hr{flex:0 0 60px;font-weight:700;color:#2563eb;font-size:14px}
  .tl-val{flex:1;font-size:13.5px;line-height:1.5;color:var(--ink)}
  .tl-empty{color:var(--mut);font-size:14px;padding:20px 0;text-align:center}
</style>
</head>
<body>
<header>
  <div class="bar">
    <h1>🚛 Gasbulk Track</h1>
    <span class="mut" id="stamp"></span>
    <span class="grow"></span>
    <input type="date" id="date">
    <input type="search" id="q" placeholder="ค้นหา รถ / ลูกค้า / ทะเบียน">
    <button class="primary" id="go">รีเฟรช</button>
    <button class="save-now" id="saveNow" title="ส่งสถานะที่เลือกไว้ลง Sheet ทันที (ปกติรอ 20 นาที)" hidden>
      💾 บันทึกลง Sheet (<span id="pendCount">0</span>)
    </button>
    <a class="gear" href="/settings" title="ตั้งค่า">⚙️</a>
  </div>
</header>

<div id="nopass" class="warn" hidden>
  ⚠️ ยังไม่ได้ตั้งรหัสผ่าน — ใครมีลิงก์ก็เปิดดูข้อมูลลูกค้าและเบอร์ พขร ได้
  ตั้งที่ Vercel → Settings → Environment Variables → เพิ่ม <b>APP_PASSWORD</b>
</div>

<main>
  <div class="pin">
    <div class="cards" id="cards"></div>
    <div class="chips">
      <button class="chip on" data-f="hour">⏰ ต้องไล่ชั่วโมงนี้</button>
      <button class="chip" data-f="late">🔴 ช้า</button>
      <button class="chip" data-f="active">🚚 ยังไม่ถึง</button>
      <button class="chip" data-f="all">ทั้งหมด</button>
    </div>
  </div>
  <div class="wrap">
    <table id="tbl">
      <thead><tr>
        <th>ประจำวันที่</th><th>คลังต้นทาง</th><th>เที่ยววิ่ง</th><th>Drop</th>
        <th>ลูกค้าปลายทาง</th><th>เบอร์รถ</th><th>ทะเบียน</th><th>ปริมาณ</th>
        <th>พขร. / โทร</th>
        <th>เวลา</th><th>เลขที่ใบกำกับการขนส่ง</th><th>สถานะ GPS</th>
        <th>ETA / ถึงจริง</th><th>ต่าง</th><th>On Time</th><th>สถานะ</th><th>ตำแหน่งปัจจุบัน</th><th>อัปเดตสถานะ</th>
      </tr></thead>
      <tbody id="rows"></tbody>
    </table>
  </div>
  <p class="note" id="foot"></p>
</main>

<div class="tl-backdrop hidden" id="tlBackdrop" onclick="if(event.target===this)closeTimeline()">
  <div class="tl-modal">
    <div class="tl-head">
      <h2 id="tlTitle">ตำแหน่งย้อนหลัง</h2>
      <button onclick="closeTimeline()">✕</button>
    </div>
    <div class="tl-sub" id="tlSub"></div>
    <div class="tl-list" id="tlList"></div>
  </div>
</div>

<script>
const LABEL = {late:'ช้า', arrived:'ส่งแล้ว', transit:'กำลังไป',
               early:'เร็วกว่ากำหนด', pending:'รอออกรถ', cancelled:'ยกเลิก'};
let ALL = [], DATA = [], FILTER = localStorage.getItem('gb_filter') || 'hour';
if(('__NOPASS__') === '1') document.getElementById('nopass').hidden = false;

function thaiNow(){                    // เวลาไทย (UTC+7) — อ่านค่าด้วย getUTC* เท่านั้น
  return new Date(Date.now() + 7*3600*1000);
}

function todayISO(){
  return thaiNow().toISOString().slice(0,10);
}

function card(n, label, cls){
  return '<div class="c '+(cls||'')+'"><b>'+n+'</b><span>'+label+'</span></div>';
}

function esc(s){
  return String(s == null ? '' : s).replace(/[&<>"]/g, c =>
    ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
}

function dur(m){                      // 1447 → "24 ชม. 7 น."   45 → "45 น."
  m = Math.abs(Math.round(m));
  if(m < 60) return m + ' น.';
  const h = Math.floor(m/60), r = m % 60;
  return h + ' ชม.' + (r ? ' ' + r + ' น.' : '');
}

// รายการสถานะให้เลือก — ตรงกับที่ใช้ในชีต
const STATUS_LIST = [
  'จอดที่ฟรีต', 'รอรถเที่ยว 1', 'กำลังไปโหลดแก๊ส', 'กำลังโหลด',
  'จัดส่งดรอป 1', 'จัดส่งดรอป 2', 'โหลดเก็บ', 'จบงาน', 'ยกเลิกออเดอร์',
];
// สถานะจบงานจริง ๆ — จางค้างถาวร ไม่ต้องไล่ซ้ำ ส่วนสถานะอื่นถ้าเกิน 1 ชม.
// จากที่ไล่ล่าสุด จะกลับมาเด่นใหม่ให้ไล่รอบต่อไป
const FINAL_STATUSES = new Set(['จัดส่งดรอป 1', 'จัดส่งดรอป 2', 'โหลดเก็บ', 'จบงาน', 'ยกเลิกออเดอร์']);

function isChaseDone(k){
  const cur = CHASED[k];
  if(!cur || !cur.status) return false;
  if(FINAL_STATUSES.has(cur.status)) return true;
  const at = mins(cur.at);
  if(at == null) return true;
  let elapsed = nowMins() - at;
  if(elapsed < 0) elapsed += 24*60;   // ข้ามเที่ยงคืน
  return elapsed < 60;
}

function pick(t, k){                  // ดรอปดาวน์เลือกสถานะ + ปุ่มจบงาน + เวลาที่บันทึก
  const cur = CHASED[k] || {};
  const opts = ['<option value="">— เลือกสถานะ —</option>'].concat(
    STATUS_LIST.map(s => '<option value="'+esc(s)+'"'
                       + (cur.status === s ? ' selected' : '') + '>'+esc(s)+'</option>')
  ).join('');
  const doneBtn = cur.status === 'จบงาน'
    ? '<button type="button" class="donebtn on" title="จบงานแล้ว">✅ จบงาน</button>'
    : '<button type="button" class="donebtn" title="กดจบงาน">จบงาน</button>';
  const nowLabel = cur.status
    ? '<div class="cursts">✓ สถานะ: '+esc(cur.status)+'</div>' : '';
  return nowLabel
       + '<div style="display:flex;gap:5px;align-items:center">'
       + '<select class="pickst" data-k="'+esc(k)+'">'+opts+'</select>'
       + doneBtn + '</div>'
       + (cur.at ? '<div class="at">🕐 '+esc(cur.at)+'</div>' : '');
}

function tel(t){                      // ชื่อ พขร + ปุ่มโทร + ปุ่มคัดลอกเบอร์
  const num = String(t.phone||'').replace(/[^0-9+]/g,'');
  const nm  = t.driver ? '<div>'+esc(t.driver)+'</div>' : '';
  if(!num) return nm || '<span class="mut">—</span>';
  return nm
    + '<div style="display:flex;gap:5px;align-items:center;margin-top:3px">'
    + '<a class="call" href="tel:'+num+'">📞 '+esc(t.phone)+'</a>'
    + '<button class="copy" data-num="'+num+'" title="คัดลอกเบอร์">📋</button>'
    + '</div>';
}

// คัดลอกเบอร์ (ใช้บนคอมที่กดโทรไม่ได้) — ก๊อปไปวางใน LINE หรือมือถือได้
document.addEventListener('click', e => {
  const b = e.target.closest('.copy');
  if(!b) return;
  navigator.clipboard.writeText(b.dataset.num).then(() => {
    const old = b.textContent;
    b.textContent = '✓';
    setTimeout(() => { b.textContent = old; }, 1200);
  });
});

function ot(t){                       // ผลตัดสิน On Time ที่ชีตคำนวณไว้เอง
  const v = String(t.ontime||'').trim();
  if(!v) return '<span class="mut">—</span>';
  const pass = /pass|ontime|on time|ตรงเวลา/i.test(v);
  const m    = String(t.ontime_min||'').trim();
  return '<span class="badge '+(pass?'s-arrived':'s-late')+'">'+esc(v)+'</span>'
       + (m && !pass ? '<div style="font-size:12px;color:var(--mut);margin-top:3px">'+esc(m)+' น.</div>' : '');
}

function eta(t){                      // ถึงจริงแล้วโชว์เวลาจริง ไม่งั้นโชว์ประมาณการ
  if(t.arrive_time) return '<b style="color:var(--ok)">'+esc(t.arrive_time)+'</b>';
  if(t.eta_time)    return '~'+esc(t.eta_time);
  return '<span class="mut">—</span>';
}

function loc(t){
  if(t.current_lat == null || t.current_lng == null) return '—';
  const url  = 'https://www.google.com/maps?q=' + t.current_lat + ',' + t.current_lng;
  const text = t.current_loc || (t.current_lat.toFixed(5) + ', ' + t.current_lng.toFixed(5));
  return '<a href="'+url+'" target="_blank" rel="noopener" style="color:var(--tr)">📍 '+esc(text)+'</a>';
}

// ── บันทึกว่าไล่รถคันไหนไปแล้ว → เก็บลงแท็บ ChaseLog ใน Google Sheet ──────
// ทุกคนที่เปิดเว็บเห็นตรงกัน  ถ้าเขียนไม่ได้จะเก็บในเครื่องไว้ก่อนและแจ้งเตือน
let CHASED = {};

function key(t){                      // คีย์ประจำทริป ใช้ข้ามการรีเฟรชได้
  return [t.date, t.car_no, t.trip_no, t.drop, t.invoice_no].join('|');
}

function curDate(){ return document.getElementById('date').value || todayISO(); }

async function loadChased(){
  try{
    const r = await fetch('/api/chase?date=' + curDate());
    if(!r.ok) throw new Error('load failed');
    const j = await r.json();
    CHASED = j;
  }catch(e){
    try{ CHASED = JSON.parse(localStorage.getItem('gb_chased_'+curDate()) || '{}'); }
    catch(e2){ CHASED = {}; }
  }
}

function getMyName(){                 // ถามชื่อครั้งแรกแล้วจำไว้ในเครื่องนี้ ไม่ต้องพิมพ์อีก
  let name = localStorage.getItem('gb_by');
  if(!name){
    name = (prompt('กรุณาใส่ชื่อของคุณ (จำไว้ในเครื่องนี้ครั้งเดียว)') || '').trim();
    if(name) localStorage.setItem('gb_by', name);
  }
  return name || '';
}

function tripLoc(t){                  // ข้อความ "วันที่ เวลา / ตำแหน่งปัจจุบัน" ตอนกดอัปเดตสถานะ
  const place = t.current_loc || (t.current_lat != null && t.current_lng != null
    ? t.current_lat.toFixed(5) + ', ' + t.current_lng.toFixed(5) : '');
  if(!place) return '';
  const d = thaiNow();
  const stamp = d.getUTCDate() + '/' + (d.getUTCMonth()+1) + '/' + d.getUTCFullYear()
    + ' ' + String(d.getUTCHours()).padStart(2,'0') + ':' + String(d.getUTCMinutes()).padStart(2,'0')
    + ':' + String(d.getUTCSeconds()).padStart(2,'0');
  return stamp + ' / ' + place;
}

async function saveStatus(k, status, t, loc, by){
  const body = new URLSearchParams({ key:k, date:curDate(), status:status,
                                     car_no:t.car_no||'', customer:t.customer||'',
                                     location: loc||'', by: by||'' });
  if(!status) body.set('clear','1');
  const r = await fetch('/api/chase', {method:'POST', body});
  if(!r.ok) throw new Error((await r.json().catch(()=>({}))).detail || 'save failed');
  return (await r.json()).at;
}

// ไม่ยิงบันทึกลง Sheet ทันทีทุกครั้งที่เลือก — พักไว้ในเครื่องก่อน แล้วค่อยส่งรวม
// (กันยิง API ถี่เกินไป) หน้าจอผู้ใช้เองยังอัปเดตทันทีเสมอ ปรับรอบได้ที่หน้า ⚙️ ตั้งค่า
const PENDING_SAVE_MS = parseInt(localStorage.getItem('gb_save_interval') || '20', 10) * 60 * 1000;
let pendingSaves = {};   // {k: {status, t}}

document.addEventListener('click', e => {          // ปุ่ม "จบงาน" ลัด — ไม่ต้องเปิดดรอปดาวน์เอง
  const btn = e.target.closest('.donebtn');
  if(!btn) return;
  const sel = btn.closest('div').querySelector('.pickst');
  if(!sel) return;
  sel.value = 'จบงาน';
  sel.dispatchEvent(new Event('change', {bubbles: true}));
});

document.addEventListener('change', e => {
  const b = e.target.closest('.pickst');
  if(!b) return;
  const k = b.dataset.k;
  const t = ALL.find(x => key(x) === k) || {};
  const d = thaiNow();
  const now = String(d.getUTCHours()).padStart(2,'0')+':'+String(d.getUTCMinutes()).padStart(2,'0');

  if(b.value) CHASED[k] = {at: now, status: b.value}; else delete CHASED[k];
  render();
  localStorage.setItem('gb_chased_'+curDate(), JSON.stringify(CHASED));

  // ถามชื่อ/อ่านพิกัด ณ ตอนกด (ไม่ใช่ตอน flush เพราะอาจรันตอนไม่มีใครอยู่หน้าจอ)
  const by  = b.value ? getMyName() : '';
  const loc = tripLoc(t);
  pendingSaves[k] = {status: b.value, t: t, by: by, loc: loc};   // ทับของเดิมถ้าเลือกซ้ำก่อนถึงรอบบันทึก
  updateSaveNowBtn();
});

function updateSaveNowBtn(){
  const n = Object.keys(pendingSaves).length;
  const btn = document.getElementById('saveNow');
  document.getElementById('pendCount').textContent = n;
  btn.hidden = n === 0;
}

document.getElementById('saveNow').onclick = () => flushPendingSaves();

async function flushPendingSaves(){
  const keys = Object.keys(pendingSaves);
  if(!keys.length) return;
  const batch = pendingSaves;
  pendingSaves = {};
  updateSaveNowBtn();
  for(const k of keys){
    const {status, t, loc, by} = batch[k];
    try{
      const at = await saveStatus(k, status, t, loc, by);
      if(status && at){ CHASED[k] = {at: at, status: status}; }
      localStorage.setItem('gb_chased_'+curDate(), JSON.stringify(CHASED));
    }catch(err){
      pendingSaves[k] = batch[k];   // ล้มเหลว เก็บไว้ลองรอบหน้าใหม่
      const w = document.getElementById('nopass');
      w.hidden = false;
      w.innerHTML = '⚠️ บันทึกลง Google Sheet ไม่ได้ (' + esc(err.message) + ')<br>'
        + 'เก็บไว้ในเครื่องนี้ก่อน — ต้องแชร์ไฟล์แผนงานให้ '
        + '<b>tms-249@tms-bult.iam.gserviceaccount.com</b> เป็น <b>ผู้แก้ไข</b>';
    }
  }
  updateSaveNowBtn();
  render();
}
setInterval(flushPendingSaves, PENDING_SAVE_MS);
window.addEventListener('beforeunload', () => { if(Object.keys(pendingSaves).length) flushPendingSaves(); });

function mins(hhmm){                  // "14:30" → 870
  const m = /^(\d{1,2}):(\d{2})/.exec(String(hhmm||''));
  return m ? (+m[1])*60 + (+m[2]) : null;
}

function nowMins(){
  const d = thaiNow();
  return d.getUTCHours()*60 + d.getUTCMinutes();
}

function keep(t){                     // กรองตามชิปที่เลือก
  if(FILTER === 'all')    return true;
  if(FILTER === 'late')   return t.status === 'late';
  if(FILTER === 'active') return t.status !== 'arrived' && t.status !== 'cancelled';
  // 'hour' = ต้องจัดการในชั่วโมงนี้: ถึงเวลาโทรตาม / ช้าอยู่แล้ว / ครบกำหนดใน 60 นาที
  if(t.status === 'arrived' || t.status === 'cancelled') return false;
  if(CHASED[key(t)] && CHASED[key(t)].status === 'จบงาน') return false;   // กดจบงานแล้ว ไม่ต้องไล่อีก
  if(String(t.prediction||'').startsWith('📞')) return true;
  if(t.status === 'late')    return true;
  const s = mins(t.sched_time);
  return s != null && s - nowMins() <= 60;
}

function render(){
  const q = document.getElementById('q').value.trim().toLowerCase();
  DATA = ALL.filter(keep);
  const list = (!q ? DATA : DATA.filter(t =>
    [t.car_no, t.plate, t.customer, t.source, t.invoice_no]
      .some(v => String(v||'').toLowerCase().includes(q))))
    .slice()
    .sort((a,b) => {           // ช้าที่สุดขึ้นก่อน แล้วค่อยเรียงตามเวลากำหนด
      const ck = x => isChaseDone(key(x)) ? 1 : 0;          // ที่ไล่แล้ว (ยังไม่ครบ 1 ชม./จบงานจริง) ลงไปอยู่ล่าง
      if (ck(a) !== ck(b)) return ck(a) - ck(b);
      const rank = s => ({late:0, transit:1, early:2, pending:3, arrived:4, cancelled:5}[s] ?? 6);
      if (rank(a.status) !== rank(b.status)) return rank(a.status) - rank(b.status);
      if (a.status === 'late') return (b.diff_minutes||0) - (a.diff_minutes||0);
      return String(a.sched_time||'').localeCompare(String(b.sched_time||''));
    });

  document.getElementById('rows').innerHTML = list.length ? list.map(t => {
    const k    = key(t);
    const call = String(t.prediction||'').startsWith('📞');
    const diff = t.diff_minutes == null ? '<span class="mut">—</span>'
      : (t.diff_minutes > 0
          ? '<span style="color:var(--late)">+'+dur(t.diff_minutes)+'</span>'
          : '<span style="color:var(--ok)">-'+dur(-t.diff_minutes)+'</span>');
    const badge = '<span class="badge s-'+esc(t.status)+'">'
                + (LABEL[t.status]||esc(t.status))+'</span>'
                + (call ? '<span class="callnow">📞 ถึงเวลาโทร</span>' : '');
    return '<tr class="'+(isChaseDone(k)?'done':'')+'">'
      + '<td data-l="ประจำวันที่" class="mono mut">'+esc(t.date)+'</td>'
      + '<td data-l="คลังต้นทาง">'+esc(t.source)+'</td>'
      + '<td data-l="เที่ยววิ่ง">'+esc(t.trip_no)+'</td>'
      + '<td data-l="Drop">'+esc(t.drop)+'</td>'
      + '<td data-l="ลูกค้าปลายทาง" class="wide cust"><span class="v">'+esc(t.customer)+'</span></td>'
      + '<td data-l="เบอร์รถ" class="carno" data-carno="'+esc(t.car_no)+'" title="คลิกดูตำแหน่งย้อนหลังรายชั่วโมง"><b>'+esc(t.car_no)+'</b></td>'
      + '<td data-l="ทะเบียน" class="wide mut" style="max-width:120px">'+esc(t.plate)+'</td>'
      + '<td data-l="ปริมาณ" class="mono">'+esc(t.volume)+'</td>'
      + '<td data-l="พขร. / โทร">'+tel(t)+'</td>'
      + '<td data-l="เวลาส่งมอบ" class="mono">'+esc(t.sched_time)+'</td>'
      + '<td data-l="เลขที่ใบกำกับ" class="mut">'+esc(t.invoice_no)+'</td>'
      + '<td data-l="สถานะ GPS" class="mut">'+esc(t.gps_status)+'</td>'
      + '<td data-l="ETA / ถึงจริง" class="mono">'+eta(t)+'</td>'
      + '<td data-l="ต่าง" class="mono">'+diff+'</td>'
      + '<td data-l="On Time (ชีต)">'+ot(t)+'</td>'
      + '<td data-l="สถานะ" class="st">'+badge+'</td>'
      + '<td data-l="ตำแหน่งปัจจุบัน" class="wide mut">'+loc(t)+'</td>'
      + '<td data-l="อัปเดตสถานะ" class="chk">'+pick(t, k)+'</td>'
      + '</tr>';
  }).join('') : '<tr><td colspan="18" class="empty">'
      + (ALL.length
          ? 'ไม่มีทริปที่ตรงกับมุมมองนี้ (วันนี้มี ' + ALL.length + ' ทริป)<br>'
            + '<span style="font-size:13px">ลองกดชิป <b>ทั้งหมด</b> ด้านบน หรือเปลี่ยนวันที่</span>'
          : 'ไม่มีทริปในวันที่เลือก')
      + '</td></tr>';

  document.getElementById('tbl').classList.toggle('hide-ot',
    !ALL.some(t => String(t.ontime||'').trim()));   // ไม่มีข้อมูล On Time ก็ซ่อนคอลัมน์ไป

  document.getElementById('foot').textContent =
    'แสดง ' + list.length + ' ทริป (จากทั้งวัน ' + ALL.length + ' ทริป)';
}

async function load(){
  const d  = document.getElementById('date').value || todayISO();
  const el = document.getElementById('rows');
  el.innerHTML = '<tr><td colspan="18" class="empty">กำลังโหลด…</td></tr>';
  try{
    const r = await fetch('/api/trips?date=' + d);
    if(!r.ok) throw new Error((await r.json()).detail || r.statusText);
    const j = await r.json();
    ALL = j.trips || [];
    await loadChased();
    document.getElementById('cards').innerHTML =
        card(j.total,'ทริปทั้งหมด','')
      + card(j.arrived,'ส่งเสร็จแล้ว','ok')
      + card(j.in_transit,'กำลังเดินทาง','tr')
      + card(j.late,'คาดว่าจะช้า','late')
      + card(j.pending,'รอออกรถ','')
      + card(j.cancelled || 0,'ยกเลิก/โหลดเก็บ','');
    document.getElementById('stamp').innerHTML =
      '<span class="dot"></span>อัปเดต ' + String(j.fetched_at).slice(11,16) + ' น.';
    render();
    syncStickyOffset();
  }catch(e){
    el.innerHTML = '<tr><td colspan="18" class="empty">เกิดข้อผิดพลาด: ' + esc(e.message) + '</td></tr>';
  }
}

// ── ตำแหน่งย้อนหลังรายชั่วโมง (คลิกที่เบอร์รถ) ──────────────────────────
// อ่านจากแท็บรายวันของสเปรดชีตเดียวกัน (ชื่อแท็บ = dd.MM.yyyy) ที่ Apps
// Script อีกตัวคอยบันทึกตำแหน่งทุกชั่วโมงไว้ให้อยู่แล้ว -- Gasbulk Track
// เองไม่มีที่เก็บประวัติของตัวเอง (ดู /api/timeline ฝั่ง main.py)
async function openTimeline(carNo){
  const d  = document.getElementById('date').value || todayISO();
  const backdrop = document.getElementById('tlBackdrop');
  const list = document.getElementById('tlList');
  document.getElementById('tlTitle').textContent = '🚛 ' + carNo;
  document.getElementById('tlSub').textContent = 'กำลังโหลด...';
  list.innerHTML = '';
  backdrop.classList.remove('hidden');

  try{
    const r = await fetch('/api/timeline?car_no=' + encodeURIComponent(carNo) + '&date=' + d);
    const j = await r.json();
    if(!r.ok) throw new Error(j.detail || 'โหลดไม่สำเร็จ');

    document.getElementById('tlSub').textContent = 'วันที่ ' + d
      + (j.found ? '' : ' — ยังไม่พบข้อมูลตำแหน่งของคันนี้ในวันนี้');

    if(!j.timeline || j.timeline.length === 0){
      list.innerHTML = '<div class="tl-empty">ยังไม่มีข้อมูลตำแหน่งบันทึกไว้'
        + (j.error ? '<br><span style="font-size:12px">'+esc(j.error)+'</span>' : '') + '</div>';
      return;
    }
    list.innerHTML = j.timeline.map(function(e){
      return '<div class="tl-row"><div class="tl-hr">'+esc(e.hour)+'</div>'
           + '<div class="tl-val">'+esc(e.raw)+'</div></div>';
    }).join('');
  }catch(err){
    document.getElementById('tlSub').textContent = '';
    list.innerHTML = '<div class="tl-empty">โหลดไม่สำเร็จ: ' + esc(err.message) + '</div>';
  }
}
function closeTimeline(){
  document.getElementById('tlBackdrop').classList.add('hidden');
}
document.addEventListener('click', e => {
  const td = e.target.closest('.carno');
  if(td && td.dataset.carno) openTimeline(td.dataset.carno);
});
document.addEventListener('keydown', e => {
  if(e.key === 'Escape') closeTimeline();
});

document.getElementById('date').value = todayISO();
document.getElementById('go').onclick    = load;
document.getElementById('date').onchange = load;
document.getElementById('q').oninput     = render;

document.querySelectorAll('.chip').forEach(b => {
  b.classList.toggle('on', b.dataset.f === FILTER);
  b.onclick = () => {
    FILTER = b.dataset.f;
    document.querySelectorAll('.chip').forEach(x => x.classList.toggle('on', x === b));
    render();
  };
});

load();

// ล็อค header + การ์ด/ปุ่มกรอง ไว้ให้เห็นตลอดตอนเลื่อนดูรายการยาวๆ
function syncStickyOffset(){
  document.documentElement.style.setProperty('--hh', document.querySelector('header').offsetHeight + 'px');
}
window.addEventListener('resize', syncStickyOffset);
syncStickyOffset();

// รอบรีเฟรชอัตโนมัติ ตั้งได้ที่หน้า ⚙️ ตั้งค่า (ค่าเริ่มต้น 1 ชั่วโมง)
const IV = parseInt(localStorage.getItem('gb_interval') || '60', 10);
if(IV > 0) setInterval(load, IV * 60 * 1000);
</script>
</body>
</html>
"""

# Vercel entry point
handler = app
