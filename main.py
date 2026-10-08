"""
Gasbulk Track API v3
Sources:
  eZView API (ตรง)   → ตำแหน่งรถ live  (ไม่ได้ตั้ง EZ_POS_USER/PASS หรือเรียกไม่สำเร็จ → อ่านชีต PTGL แบบเดิม)
  PTGL Sheet         → ตำแหน่งรถสำรอง  (col A=LicenseNO, D=GPSDateTime, E=Lat, F=Lng, M=Location)
  แผนงาน Gasbulk     → ทริปประจำวัน   (col C=วันที่, G=เวลากำหนด, M=ปลายทาง, P=เบอร์รถ)
  TripDetails (TMS)  → เวลาเข้า-ออกจริง เติมช่อง AB–AF ที่ว่าง (ตั้ง TMS_SHEET_ID ก่อนถึงจะใช้)
  ข้อมูลปลายทาง      → พิกัดปลายทาง   (col A=ชื่อ ตรงกับแผนงาน M, col G=lat,lng)
  Routes API / ORS   → ETA จริงพร้อม traffic → รู้ล่วงหน้าว่าจะช้ากี่นาที
"""

from __future__ import annotations

import base64
import hashlib
import hmac
import io
import json
import os
import random
import re
import traceback
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from math import atan2, cos, radians, sin, sqrt
from time import sleep, time
from typing import Optional

import httpx
import gspread
from fastapi import FastAPI, File, Form, HTTPException, Query, Request, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse, JSONResponse, RedirectResponse
from google.oauth2.service_account import Credentials
from pydantic import BaseModel

# ─── CONFIG — ปรับคอลัมน์ที่นี่ถ้า Sheet เปลี่ยน ─────────────────────────────

# Sheet 1: PTGL — ตำแหน่งรถ live (ตัวสำรอง ถ้าดึง eZView API ตรงไม่ได้)
PTGL_ID    = "1FIXB3TT3b68ho2pc0lrYi4IOuXmCw4_BBDot2kp-XC4"
PTGL_TAB   = "PTGL"
PTGL_LICNO = 0   # A  LicenseNO  เช่น "No.465(63-3530)"
PTGL_GPSDT = 3   # D  GPSDateTime  ← ใช้เช็กว่าพิกัดเก่าหรือยัง
PTGL_LAT   = 4   # E  Latitude
PTGL_LNG   = 5   # F  Longitude
PTGL_SPEED = 6   # G  Speed
PTGL_LOC   = 12  # M  LocalLocation (ที่อยู่ปัจจุบัน)

# ─── eZView API ตำแหน่งรถ — ดึงตรง ไม่ผ่านชีต PTGL ─────────────────────────
# ตั้งที่ Vercel → Settings → Environment Variables:
#   EZ_POS_USER, EZ_POS_PASS  บัญชีเดียวกับที่สคริปต์ getAllVehicleLocations ใช้ (หรือบัญชีแยกที่ขอจาก eZView)
#   EZ_POS_URL                ลิงก์ API ตำแหน่ง (ลิงก์เดียวกับในสคริปต์ getAllVehicleLocations)
#                             ไม่ใส่ไว้ในโค้ดเพราะ repo เป็น Public — ถ้า eZView เปิด https แล้ว ใช้ลิงก์ https
# ยังไม่ได้ตั้ง / เรียกไม่สำเร็จ → ถอยไปอ่านชีต PTGL แบบเดิมอัตโนมัติ หน้าจอไม่ดับ
EZ_POS_URL     = os.environ.get("EZ_POS_URL", "")
POS_CACHE_TTL  = 60      # วินาที — ดึงตำแหน่งใหม่ไม่เกินนาทีละครั้ง
GPS_STALE_MINS = 20      # พิกัดเก่ากว่านี้ = "GPS ไม่อัปเดต" ขึ้นเตือน และไม่ใช้ตัดสินว่าถึงปลายทาง
NEAR_DEST_KM   = 3.0     # GPS อยู่ห่างลูกค้าไม่เกินนี้ = ถือว่าถึงปลายทางแล้ว (แก้เคส NO.626 ขึ้นช้า 30 ชม.)

# ─── เวลาเข้า-ออกจริงจาก TMS — อ่านแท็บ TripDetails ที่สคริปต์ MLSTMS ดึงลงไว้ ─────
# ตั้ง TMS_SHEET_ID = ไอดีไฟล์ Google Sheet ที่มีแท็บ TripDetails
# แล้วแชร์ไฟล์นั้นให้ service account เป็น "ผู้มีสิทธิ์อ่าน" — ไม่ได้ตั้ง = ข้ามส่วนนี้ ทำงานแบบเดิม
# ใช้เติมเฉพาะช่องที่ว่างในแผนงาน (AB/AD/AE/AF) — ถ้าคนกรอกไว้แล้ว ยึดค่าที่กรอกเสมอ
TMS_SHEET_ID = os.environ.get("TMS_SHEET_ID", "")
TMS_TAB      = "TripDetails"
# ลำดับจุดในทริป TMS (ตามคอมเมนต์ DEPOT_TIMES: Sequence 1 = ลานจอด, 2 = โรงจ่าย)
# จุดที่ 3 เป็นต้นไป = ลูกค้า (Drop) — ถ้าหน้างานจริงไม่ใช่แบบนี้ แก้ 2 ค่านี้
TMS_WP_YARD  = 1
TMS_WP_LOAD  = 2

# Sheet 2a: ไฟล์ต้นทางจริง "แผนงานแก๊สบัลค์ใหม่" — คนหน้างานแก้ไขแผนงานที่ไฟล์นี้โดยตรง
# ใช้อ่าน "รายการทริป" + "ข้อมูลปลายทาง" เท่านั้น (ยังไม่มีสิทธิ์เขียน แค่ Viewer)
# ตั้ง Environment Variable "SOURCE_ID" เพื่อชี้ไปไฟล์ชีตทดลองได้ (ไม่ตั้ง = ใช้ไฟล์จริงเหมือนเดิม)
SOURCE_ID    = os.environ.get("SOURCE_ID", "1bwBmxGy1mlnAEIUm5ZNNV71tud3NCyPZlHesIwP4tUs")

# Sheet 2b: ไฟล์ปลายทางที่ระบบเขียนลง — แท็บรายวัน (dd.mm.yyyy) + ChaseLog + Master
# ไม่ได้ใช้อ่านรายการทริปแล้ว (ย้ายไปอ่านจาก SOURCE_ID ตรง ๆ)
#
# ตั้งผ่าน Environment Variable "PLAN_ID" บน Vercel ได้ เผื่อย้ายไปไฟล์อื่น
# (เช่น ไฟล์ที่ลูกค้าเปิดดู) จะได้ไม่ต้องแก้โค้ด — ไฟล์ปลายทางใหม่ต้องมีแท็บ
# "Master" (แม่แบบ พร้อม dropdown/หัวคอลัมน์รายชั่วโมง) และแชร์ให้ service account
# เป็นผู้แก้ไขก่อน ไม่งั้นระบบจะสร้างแท็บรายวันไม่ได้
PLAN_ID      = os.environ.get("PLAN_ID", "1kksFntsGH0SuJUeF2ChAury-yyF6EorzgBpyl5mggdk")
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
# เช็กทั้งคอลัมน์สถานะ (AA/AH) และช่องลูกค้าปลายทาง (M) — เคยเจอของจริง: เขียน "โหลดเก็บ"
# ไว้ในช่องลูกค้า แต่ระบบเช็กแค่ช่องสถานะ เลยยังขึ้น "รอออกรถ + ถึงเวลาโทร"
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
    version="3.0.0",
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
    # เวลาจริงจากชีต (คอลัมน์ AB–AG) หรือจาก TMS ถ้าชีตยังว่าง — ว่างแปลว่ายังไม่ถึงขั้นนั้น
    yard_time:    Optional[str]   = None   # AB เข้าลานจอด
    load_out:     Optional[str]   = None   # AD ออกจากโหลด
    depart_time:  Optional[str]   = None   # AE ออกจากคลัง
    arrive_time:  Optional[str]   = None   # AF เข้าปลายทาง (เวลาถึงจริง)
    tms_filled:   bool            = False  # True = มีเวลาบางช่องเติมมาจาก TMS
    # ตำแหน่งปัจจุบัน (จาก eZView API หรือ PTGL)
    current_lat:  Optional[float] = None
    current_lng:  Optional[float] = None
    current_loc:  Optional[str]   = None
    gps_time:     Optional[str]   = None   # เวลาของพิกัด "dd/mm HH:MM"
    gps_stale:    bool            = False  # True = พิกัดเก่าเกิน GPS_STALE_MINS
    # พิกัดปลายทาง (จากชีต "ข้อมูลปลายทาง") — ใช้เปิดเส้นทางใน Google Maps
    dest_lat:     Optional[float] = None
    dest_lng:     Optional[float] = None
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
_pos_cache:   dict[str, tuple[float, dict]] = {}   # ตำแหน่งจาก eZView API
_last_good_pos: dict[str, dict] = {}               # ตำแหน่งชุดล่าสุดที่ไม่ว่าง — กันชีต PTGL ว่างชั่วขณะ
_pos_source = "—"                                  # "eZView API" / "ชีต PTGL" — โชว์ที่ /api/health

def _drop_sheet_cache(sheet_id: str, tab: str) -> None:
    """ล้างแคชในหน่วยความจำของแท็บนั้น — ใช้หลังเขียนชีตเอง กันอ่านซ้ำเจอของเก่า"""
    _sheet_cache.pop(f"{sheet_id}:{tab}", None)

# ─── UTILITIES ───────────────────────────────────────────────────────────────

def _build_creds() -> Credentials:
    env = os.environ.get("GOOGLE_CREDENTIALS")
    if env:
        return Credentials.from_service_account_info(json.loads(env), scopes=SCOPES)
    local = os.path.join(os.path.dirname(__file__), "..", "credentials.json")
    return Credentials.from_service_account_file(local, scopes=SCOPES)


# error ที่เป็นแค่อาการชั่วคราวฝั่ง Google — เจอแล้วรอสักครู่แล้วลองใหม่มักผ่าน
# 429 = เรียกถี่เกินโควตา, 500/502/503/504 = ฝั่ง Google เองขัดข้องชั่วคราว
_RETRY_STATUS = (429, 500, 502, 503, 504)


def _is_transient(err: Exception) -> bool:
    code = getattr(getattr(err, "response", None), "status_code", None)
    if code in _RETRY_STATUS:
        return True
    return any(str(c) in str(err) for c in _RETRY_STATUS)


def _with_retry(fn, tries: int = 3, wait: float = 2.0):
    """เรียก fn() ใหม่เมื่อเจอ error ชั่วคราว (รอ 2 → 4 วินาที)

    เคยเจอของจริง: รอบ 01:34 Google ตอบ 503 กลับมา ทั้งรอบเลยล้มทั้งชั่วโมง
    ข้อมูลพิกัดของชั่วโมงนั้นหายไปเลย ทั้งที่รอถัดไปไม่กี่วินาทีก็ใช้ได้แล้ว"""
    for attempt in range(tries):
        try:
            return fn()
        except Exception as e:
            if attempt == tries - 1 or not _is_transient(e):
                raise
            sleep(wait * (2 ** attempt))


# สุ่มยืดอายุแคชเพิ่มอีก 0-150 วินาที ต่างกันไปในแต่ละ server และแต่ละชีต
#
# ถ้าทุกที่หมดอายุพร้อมกันเป๊ะทุก 5 นาที พอถึงวินาทีนั้นทุก server ที่กำลังรับ
# request อยู่จะเห็นว่าแคชหมดอายุพร้อมกันหมด แล้วแห่กันไปอ่าน Sheet สดพร้อมกัน
# หลายไฟล์หลายคน = ทะลุโควตา 60 ครั้ง/นาที ทันที แล้ววนแบบนี้ทุก 5 นาที
# เหลื่อมเวลาออกจากกันแล้วการอ่านจะกระจายตัว ไม่กระจุกเป็นช่วง ๆ
_JITTER_SEED = random.random()          # ต่างกันทุกครั้งที่ Vercel สร้าง server ใหม่


def _ttl_jitter(key: str) -> float:
    return ((hash(key) % 100) / 100 + _JITTER_SEED) % 1 * 150


def _fetch_sheet(sheet_id: str, tab: str) -> list[list]:
    """อ่าน Sheet พร้อมแคชในหน่วยความจำ (ไม่พึ่ง Supabase แล้ว — อ่านจาก Google ตรง ๆ
    เสมอเมื่อแคชหมดอายุ ข้อมูลจึงอัปเดตตามไฟล์ต้นทางเร็วขึ้น)"""
    key = f"{sheet_id}:{tab}"
    ttl = CACHE_TTL + _ttl_jitter(key)
    if key in _sheet_cache:
        ts, data = _sheet_cache[key]
        if time() - ts < ttl:
            return data

    def _read():
        gc = gspread.authorize(_build_creds())
        return gc.open_by_key(sheet_id).worksheet(tab).get_all_values()

    try:
        data = _with_retry(_read)
    except Exception:
        # อ่านสดไม่ได้ (ส่วนใหญ่คือ 429 quota เต็ม) — เอาของเก่าในแคชมาใช้แทน
        # ข้อมูลเก่าไม่กี่นาทียังมีประโยชน์กว่าหน้าจอว่างเปล่ามาก
        stale = _sheet_cache.get(key)
        if stale is not None:
            return stale[1]
        raise

    _sheet_cache[key] = (time(), data)
    return data


def _refresh_sheet_cache(sheet_id: str, tab: str, ws) -> None:
    """อ่านค่าล่าสุดจริงจาก ws แล้วยัดใส่แคชในหน่วยความจำทับของเก่า — ใช้หลังเขียนชีตเอง
    กัน _fetch_sheet ตัวถัดไปในคำขอเดียวกันเจอแคชเก่า"""
    fresh = ws.get_all_values()
    _sheet_cache[f"{sheet_id}:{tab}"] = (time(), fresh)


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


def _car_key(raw: str) -> str:
    """คีย์จับคู่รถแบบรวม "อักษรนำหน้า + เลข" — กันคนละคันที่เลขซ้ำกันจับคู่ผิด
      'PTL.456(61-1566)' → 'PTL456'
      'PTL.456'          → 'PTL456'
      'No.456(63-3248)'  → 'NO456'
      '0465'             → '465'      (ไม่มีอักษรนำหน้า)

    เคยเจอของจริง: ชีต GPS มีทั้ง PTL.456 กับ No.456 คนละคันกัน พอตัดเหลือแต่เลข
    '456' ทั้งคู่ ตำแหน่งของอีกคันเลยไปแสดงผิดคัน (PTL.456 ไปโชว์พิกัดของ No.456)"""
    s = re.sub(r"\(.*", "", raw or "")            # ตัดวงเล็บทะเบียนท้ายชื่อออก
    m = re.match(r"\s*([A-Za-z]*)\s*\.?\s*0*(\d+)", s)
    if not m:
        return _extract_car_no(raw)
    prefix, num = m.group(1).upper(), (m.group(2).lstrip("0") or m.group(2))
    return f"{prefix}{num}"


def _plate_key(raw: str) -> str:
    """ทะเบียนหัวลาก เหลือแต่ตัวเลข ใช้จับคู่กับ TMS ที่บางทีเขียนแค่ทะเบียน
      'No.626(67-4709)'   → '674709'
      '67-4709/69-4677'   → '674709'   (หัวลาก/หาง เอาเฉพาะคันแรก)
      'PTL.411'           → ''         (ไม่มีทะเบียนในข้อความ)"""
    s = raw or ""
    m = re.search(r"\(([^)]*)\)", s)
    if m:
        s = m.group(1)
    s = re.split(r"[/,]", s)[0]
    m = re.search(r"\d{1,3}\s*-\s*\d{3,4}", s)
    return re.sub(r"\D", "", m.group(0)) if m else ""


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


def _any_dt(raw) -> Optional[datetime]:
    """เวลาจาก API/ชีต หลายรูปแบบ → datetime เวลาไทย (ไม่มี timezone เหมือน _thai_now)
      '2026-09-28T10:40:12'       → เวลาไทยตามที่เขียน
      '2026-09-28T03:40:12Z'      → บวก 7 ชม. (เป็นเวลา UTC)
      '/Date(1790567013000)/'     → แปลงจาก epoch
      '28/09/2026 10:40:12'       → ส่งต่อให้ _cell_dt"""
    s = str(raw or "").strip()
    if not s:
        return None
    m = re.search(r"/Date\((\d+)", s)
    if m:
        return datetime.utcfromtimestamp(int(m.group(1)) / 1000) + timedelta(hours=TZ_OFFSET)
    m = re.match(r"(\d{4})-(\d{2})-(\d{2})[T ](\d{1,2}):(\d{2})", s)
    if m:
        try:
            d = datetime(*(int(x) for x in m.groups()))
        except ValueError:
            return None
        if re.search(r"(Z|[+\-]00:?00)$", s):
            d += timedelta(hours=TZ_OFFSET)
        return d
    return _cell_dt(s)


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


def _dur(m: int) -> str:
    """1831 → '30 ชม. 31 น.'   45 → '45 น.'
    ใช้กับทุกข้อความอธิบาย จะได้หน่วยเดียวกับคอลัมน์ "ต่าง" บนหน้าเว็บ
    (เคยปนกัน: ข้อความเขียน "1831 นาที" แต่คอลัมน์ต่างเขียน "30 ชม. 31 น.")"""
    m = abs(int(m))
    if m < 60:
        return f"{m} น."
    h, r = divmod(m, 60)
    return f"{h} ชม." + (f" {r} น." if r else "")


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


def _state_text(t: dict) -> str:
    return (t["gps_status"] + " " + t["status_man"]).lower()


def _is_cancelled(t: dict) -> bool:
    return any(k in _state_text(t) + " " + t["customer"].lower() for k in CANCEL_KEYWORDS)


def _is_done(t: dict) -> bool:
    return any(k in _state_text(t) for k in DONE_KEYWORDS)

# ─── ETA PROVIDERS ───────────────────────────────────────────────────────────

def _haversine_km(lat1: float, lng1: float, lat2: float, lng2: float) -> float:
    """ระยะทางเส้นตรงบนผิวโลก (กิโลเมตร)"""
    r    = 6371.0
    p1, p2 = radians(lat1), radians(lat2)
    dp   = radians(lat2 - lat1)
    dl   = radians(lng2 - lng1)
    a    = sin(dp / 2) ** 2 + cos(p1) * cos(p2) * sin(dl / 2) ** 2
    return r * 2 * atan2(sqrt(a), sqrt(1 - a))


def _past_depot(pos: Optional[dict], depot: Optional[tuple], dest: Optional[tuple]) -> bool:
    """รถอยู่ใกล้ลูกค้ามากกว่าคลังชัดเจน = โหลดและออกจากคลังมาแล้ว แม้ชีตยังไม่มีเวลา

    เคยเจอของจริง: NO.626 อยู่พิจิตรแล้ว แต่ช่อง AB ว่าง ระบบเลยคำนวณให้วิ่งกลับคลัง
    PTT TANK ระยอง (805 น.) + โหลด + วิ่งกลับมาอีก 805 น. → ขึ้น "ช้า 30 ชม." ผิด"""
    if not (pos and depot and dest):
        return False
    to_dest    = _haversine_km(pos["lat"], pos["lng"], dest[0], dest[1])
    to_depot   = _haversine_km(pos["lat"], pos["lng"], depot[0], depot[1])
    depot_dest = _haversine_km(depot[0], depot[1], dest[0], dest[1])
    return to_depot > 20 and to_dest < depot_dest * 0.5


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
            timeout=4,    # เกินนี้รอไม่ไหว ถอยไปใช้สูตรคำนวณเร็วกว่า
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
                # ไม่ส่ง departureTime = Google ใช้ "ตอนนี้" เอง — เดิมส่งเวลาไทยแต่ติด Z ไว้ท้าย
                # กลายเป็นคำนวณ traffic ของอีก 7 ชม. ข้างหน้า
            },
            headers={
                "X-Goog-Api-Key":  api_key,
                "X-Goog-FieldMask": "routes.duration",
                "Content-Type":    "application/json",
            },
            timeout=5,    # เกินนี้รอไม่ไหว ถอยไปใช้สูตรคำนวณเร็วกว่า
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

def _build_pos_map(records) -> dict[str, dict]:
    """
    records = [(LicenseNO, lat, lng, location, GPSDateTime, speed), ...]
    คืน dict: คีย์รถ → {lat, lng, location, gps_dt, speed}
    ใส่ไว้ 2 คีย์ต่อคัน: แบบมีอักษรนำหน้า ('PTL456') กับแบบเลขล้วน ('456')

    แบบมีอักษรนำหน้าเป็นตัวหลัก — กันกรณีคนละคันเลขซ้ำกัน (PTL.456 กับ No.456)
    ส่วนแบบเลขล้วนไว้เป็นตัวสำรอง เผื่อชีตฝั่งใดเขียนเลขเปล่า ๆ ไม่มีอักษรนำหน้า
    และจะใส่ให้เฉพาะเลขที่ไม่ซ้ำกับคันอื่นเท่านั้น ถ้าซ้ำจะไม่ใส่ ให้จับคู่ด้วย
    อักษรนำหน้าอย่างเดียว ดีกว่าเสี่ยงหยิบผิดคัน
    """
    result: dict[str, dict] = {}
    by_num: dict[str, list[str]] = {}          # เลขล้วน → คีย์เต็มของทุกคันที่ใช้เลขนี้

    for raw, lat_raw, lng_raw, loc, dt_raw, speed_raw in records:
        raw  = str(raw or "").strip()
        ckey = _car_key(raw)
        if not ckey:
            continue
        try:
            lat = float(str(lat_raw).strip())
            lng = float(str(lng_raw).strip())
        except (TypeError, ValueError):
            continue
        if not (-90 <= lat <= 90 and -180 <= lng <= 180) or (lat == 0 and lng == 0):
            continue
        try:
            speed = float(str(speed_raw).strip())
        except (TypeError, ValueError):
            speed = None
        result[ckey] = {
            "lat":      lat,
            "lng":      lng,
            "location": str(loc or "").strip(),
            "gps_dt":   _any_dt(dt_raw),
            "speed":    speed,
        }
        by_num.setdefault(_extract_car_no(raw), []).append(ckey)

    for num, keys in by_num.items():
        if num and len(keys) == 1 and num not in result:
            result[num] = result[keys[0]]
    return result


def _fetch_positions_api() -> Optional[dict[str, dict]]:
    """ดึงตำแหน่งล่าสุดทุกคันจาก eZView API ตรง (endpoint เดียวกับสคริปต์ getAllVehicleLocations)
    คืน None ถ้ายังไม่ได้ตั้งบัญชี หรือเรียกไม่สำเร็จและไม่มีของเก่าในแคช → ผู้เรียกถอยไปใช้ชีต PTGL"""
    user, pw = os.environ.get("EZ_POS_USER"), os.environ.get("EZ_POS_PASS")
    if not user or not pw or not EZ_POS_URL:
        return None
    hit = _pos_cache.get("all")
    if hit and time() - hit[0] < POS_CACHE_TTL:
        return hit[1]
    try:
        resp = httpx.post(EZ_POS_URL, json={}, auth=(user, pw), timeout=6)
        resp.raise_for_status()
        body = resp.json()
        if body.get("A") is not True:                    # A = สำเร็จไหม, B = ข้อความ, C = รายการรถ
            raise ValueError(f"eZView ตอบไม่สำเร็จ: {body.get('B')}")
        vehicles = body.get("C") or []
    except Exception:
        return hit[1] if hit else None
    # ฟิลด์ตามสคริปต์เดิม: A=LicenseNO D=GPSDateTime E=Lat F=Lng G=Speed M=LocalLocation
    data = _build_pos_map(
        (v.get("A"), v.get("E"), v.get("F"), v.get("M"), v.get("D"), v.get("G"))
        for v in vehicles if isinstance(v, dict)
    )
    if not data:
        return hit[1] if hit else None
    _pos_cache["all"] = (time(), data)
    return data


def fetch_ptgl() -> dict[str, dict]:
    """ตำแหน่งรถปัจจุบัน: ลอง eZView API ตรงก่อน ไม่ได้ค่อยอ่านชีต PTGL

    ชีต PTGL ถูกสคริปต์ล้างก่อนเขียนใหม่ทุกรอบ ถ้าอ่านเจอตอนว่างพอดี จะได้ "ไม่มีรถเลย"
    แล้วหน้าจอขึ้นไม่พบ GPS ทุกคันนานหลายนาที — จึงเก็บชุดล่าสุดที่ไม่ว่างไว้ใช้แทน"""
    global _pos_source, _last_good_pos
    api = _fetch_positions_api()
    if api:
        _pos_source = "eZView API"
        _last_good_pos = api
        return api

    rows = _fetch_sheet(PTGL_ID, PTGL_TAB)
    data = _build_pos_map(
        (_cell(r, PTGL_LICNO), _cell(r, PTGL_LAT), _cell(r, PTGL_LNG),
         _cell(r, PTGL_LOC), _cell(r, PTGL_GPSDT), _cell(r, PTGL_SPEED))
        for r in rows[1:]
    )
    if data:
        _pos_source = "ชีต PTGL"
        _last_good_pos = data
        return data
    _pos_source = "ชีต PTGL (ว่าง — ใช้ชุดก่อนหน้า)"
    return _last_good_pos


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
            "car_key":    _car_key(car_no),            # ใช้จับคู่กับ PTGL (รวมอักษรนำหน้า)
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
            "tms_filled": False,                                   # เติมจาก TMS ด้านล่าง
        })
    return trips

# ─── TMS: เวลาเข้า-ออกจริง ────────────────────────────────────────────────

# คำทั่วไปในชื่อลูกค้าที่ใช้แยกลูกค้าไม่ได้ — ไม่เอามาจับคู่ชื่อ
_GENERIC_WORDS = {
    "โรงบรรจุ", "โรงบรรจุก๊าซ", "โรงบรรจุแก๊ส", "คลังก๊าซ", "คลังแก๊ส", "สถานี", "สถานีบริการ",
    "โรงงาน", "บริษัท", "จำกัด", "มหาชน", "สาขา", "ห้างหุ้นส่วน", "หจก",
}


def _norm_name(s: str) -> str:
    return re.sub(r"[\s.\-_/(),]+", "", (s or "").lower())


def _same_place(customer: str, wp_name: str) -> bool:
    """ชื่อลูกค้าในแผนงาน กับชื่อจุดใน TMS เป็นที่เดียวกันไหม — สะกดไม่ตรงกันเป๊ะก็จับได้
      'โรงบรรจุ วชิรบารมี'  กับ  'โรงบรรจุก๊าซ วชิรบารมี (สาขา 2)'  → True (คำ 'วชิรบารมี' ตรง)"""
    c, w = _norm_name(customer), _norm_name(wp_name)
    if not c or not w:
        return False
    if c in w or w in c:
        return True
    tokens = [t for t in re.split(r"[\s/(),.\-]+", customer or "")
              if len(t) >= 4 and t.lower() not in _GENERIC_WORDS]
    return any(_norm_name(t) in w for t in tokens)


def fetch_tms(target_date: str) -> dict[str, list[dict]]:
    """แท็บ TripDetails (สคริปต์ MLSTMS ดึงลงไว้) → {'P:<ทะเบียน>' / 'C:<เบอร์รถ>': [ทริป, ...]}
    เอาเฉพาะทริปที่เปิดวันนั้นหรือเมื่อวาน — ทริปส่งเช้ามักเปิดตั้งแต่คืนก่อน
    (เช่น NO.626 เข้าลานจอด 22:05 ของเมื่อวาน แล้วส่ง 10:00 วันนี้)
    อ่านคอลัมน์ตามชื่อหัวตาราง ไม่ใช่ตำแหน่ง — สคริปต์ MLSTMS แทรกคอลัมน์ใหม่ได้โดยไม่พัง"""
    if not TMS_SHEET_ID:
        return {}
    rows = _fetch_sheet(TMS_SHEET_ID, TMS_TAB)
    if len(rows) < 2:
        return {}
    col = {str(h).strip(): i for i, h in enumerate(rows[0])}
    c_lic, c_open, c_st = col.get("License No"), col.get("Trip Open DateTime"), col.get("Status Name")
    if c_lic is None or c_open is None:
        return {}

    day  = datetime.strptime(target_date, "%Y-%m-%d").date()
    days = {day, day - timedelta(days=1)}
    wp_cols = []
    for n in range(1, 21):
        c_name = col.get(f"WP{n} Name")
        if c_name is None:
            break
        wp_cols.append((n, c_name, col.get(f"WP{n} Actual Arrival"), col.get(f"WP{n} Actual Departure")))

    out: dict[str, list[dict]] = {}
    for r in rows[1:]:
        if c_st is not None and _cell(r, c_st).lower() in ("canceled", "cancelled", "deleted"):
            continue
        opened = _any_dt(_cell(r, c_open))
        if opened is None or opened.date() not in days:
            continue
        wps: dict[int, dict] = {}
        for n, cn, ca, cd in wp_cols:
            name = _cell(r, cn)
            if not name:
                continue
            wps[n] = {
                "name": name,
                "arr":  _any_dt(_cell(r, ca)) if ca is not None else None,
                "dep":  _any_dt(_cell(r, cd)) if cd is not None else None,
            }
        trip = {"open": opened, "wps": wps}
        lic  = _cell(r, c_lic)
        pk   = _plate_key(lic)
        if pk:
            out.setdefault("P:" + pk, []).append(trip)
        # ใช้เบอร์รถเป็นคีย์ได้เฉพาะเมื่อมีอักษรนำหน้า (No./PTL.) — ถ้าเป็นทะเบียนล้วน
        # เช่น '67-4709' _car_key จะได้ '67' ซึ่งไม่ใช่เบอร์รถ
        if re.search(r"[A-Za-z]", re.sub(r"\(.*", "", lic)):
            out.setdefault("C:" + _car_key(lic), []).append(trip)
    return out


def _enrich_from_tms(trips: list[dict], target_date: str) -> int:
    """เติมเวลาเข้าลานจอด / ออกจากโหลด / ออกคลัง / ถึงลูกค้า จาก TMS ให้ทริปที่ชีตยังว่าง
    ยึดค่าที่คนกรอกไว้ในชีตก่อนเสมอ — เติมเฉพาะช่องว่าง คืนจำนวนทริปที่ได้เติม
    พังตรงไหนก็แค่ไม่เติม ไม่ทำให้หน้าจอหลักล้ม"""
    try:
        tms = fetch_tms(target_date)
    except Exception:
        return 0
    if not tms:
        return 0

    def hm(d: Optional[datetime]) -> Optional[str]:
        return d.strftime("%H:%M") if d else None

    filled = 0
    for t in trips:
        cands = tms.get("P:" + _plate_key(t["plate"])) or tms.get("C:" + t["car_key"]) or []
        if not cands:
            continue
        pick = None
        # ทริปล่าสุดก่อน — หาจุดลูกค้าที่ชื่อตรงกับแผนงาน (จุดที่ 3 เป็นต้นไป)
        for tr in sorted(cands, key=lambda x: x["open"], reverse=True):
            cust = next((w for n, w in sorted(tr["wps"].items())
                         if n > TMS_WP_LOAD and _same_place(t["customer"], w["name"])), None)
            if cust:
                pick = (tr, cust)
                break
        # ชื่อไม่ตรงเลย แต่รถคันนี้มีทริปเดียว → เดาจุดลูกค้าจากเลข Drop
        if pick is None and len(cands) == 1:
            tr = cands[0]
            drop_no = int(_extract_car_no(t["drop"]) or 1)
            pick = (tr, tr["wps"].get(TMS_WP_LOAD + drop_no))
        if pick is None:
            continue

        tr, cust = pick
        yard = tr["wps"].get(TMS_WP_YARD) or {}
        load = tr["wps"].get(TMS_WP_LOAD) or {}
        got  = False
        if not t["yard_time"] and yard.get("arr"):
            t["yard_time"] = hm(yard["arr"]); got = True
        if not t["load_out"] and load.get("dep"):
            t["load_out"] = hm(load["dep"]); got = True
        if not t["depart"] and load.get("dep"):
            t["depart"] = hm(load["dep"]); got = True
        if not t["arrive"] and cust and cust.get("arr"):
            t["arrive"], t["arrive_dt"] = hm(cust["arr"]), cust["arr"]; got = True
        if got:
            t["tms_filled"] = True
            filled += 1
    return filled

def _prefetch_routes(trips, api_budget, ptgl_map, dest_map, is_today) -> None:
    """ยิง API เส้นทางของทุกทริปที่ได้สิทธิ์ "พร้อมกัน" แล้วเก็บผลไว้ใน _eta_cache
    ก่อนเข้าลูปคำนวณจริง — พอถึงลูป ทุกเส้นทางอยู่ในแคชหมดแล้ว ไม่ต้องรอเน็ตอีก

    เดิมยิงทีละเส้นเรียงกันในลูป 12 เส้นก็รอ 12 รอบ (วัดได้ ~30-40 วินาที)
    ยิงพร้อมกันแล้วเวลารวมเท่ากับเส้นที่ช้าที่สุดเส้นเดียว

    เงื่อนไขว่าทริปไหนต้องใช้เส้นทางไหน ต้องตรงกับลูปคำนวณด้านล่าง ถ้าเผลอไม่ตรง
    ผลไม่ผิด แค่เส้นที่ไม่ได้ดึงล่วงหน้าจะกลับไปยิงทีละเส้นแบบเดิมเท่านั้น
    """
    if not api_budget or not is_today:
        return

    jobs: dict[str, tuple[float, float, float, float]] = {}   # cache key → พิกัด 2 จุด
    for t in trips:
        if t["id"] not in api_budget:
            continue
        if t["arrive"] or _is_cancelled(t) or _is_done(t):
            continue

        pos        = ptgl_map.get(t["car_key"])
        dest_coord = dest_map.get(t["customer"])
        depot      = DEPOTS.get(t["source"])
        origin     = pos or ({"lat": depot[0], "lng": depot[1]} if depot else None)

        def add(a_lat, a_lng, b_lat, b_lng):
            key = f"{a_lat:.3f},{a_lng:.3f}->{b_lat:.4f},{b_lng:.4f}"
            if key not in _eta_cache:
                jobs[key] = (a_lat, a_lng, b_lat, b_lng)

        if not t["yard_time"] and pos and depot and dest_coord and not _past_depot(pos, depot, dest_coord):
            add(pos["lat"], pos["lng"], depot[0], depot[1])          # รถ → คลัง
            add(depot[0], depot[1], dest_coord[0], dest_coord[1])    # คลัง → ปลายทาง
        elif origin and dest_coord:
            add(origin["lat"], origin["lng"], dest_coord[0], dest_coord[1])

    if not jobs:
        return

    # ThreadPool ไม่ใช่ async เพราะ httpx ที่ใช้อยู่เป็นแบบ sync ทั้งไฟล์
    # งานพวกนี้เป็น "รอเน็ต" ล้วน ๆ เธรดจึงทำงานพร้อมกันได้จริงแม้ติด GIL
    with ThreadPoolExecutor(max_workers=min(len(jobs), MAX_ROUTE_CALLS)) as pool:
        futures = {
            pool.submit(_get_travel_minutes, a, b, c, d, True): key
            for key, (a, b, c, d) in jobs.items()
        }
        for fut in futures:
            try:
                fut.result(timeout=15)
            except Exception:
                pass        # เส้นไหนพลาด ลูปข้างล่างจะยิงเองแบบเดิม


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

    # เติมเวลาเข้า-ออกจริงจาก TMS ให้ช่องที่ชีตยังว่าง (ต้องทำก่อนเลือกทริปที่ต้องคำนวณ ETA)
    _enrich_from_tms(trips, target)

    # ETA มีความหมายเฉพาะทริปของ "วันนี้" เท่านั้น
    # (พิกัดรถใน PTGL เป็นตำแหน่งปัจจุบัน เอาไปเทียบวันอื่นไม่ได้)
    is_today = target == _today_thai()

    # ให้สิทธิ์เรียก ORS เฉพาะทริปที่ใกล้ถึงกำหนดที่สุด (ที่เหลือใช้สูตรคำนวณ)
    # กัน Vercel timeout และ rate limit ของ ORS
    pending_ids = [
        t["id"] for t in sorted(
            (t for t in trips
             if not _is_cancelled(t) and not _is_done(t) and not t["arrive"]),
            key=lambda t: _to_mins(t["sched_time"]) or 9999,
        )
    ]
    api_budget = set(pending_ids[:MAX_ROUTE_CALLS])

    _prefetch_routes(trips, api_budget, ptgl_map, dest_map, is_today)

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
        depot       = DEPOTS.get(t["source"])

        # พิกัดเก่าเกินไป (สคริปต์/API ค้าง) — ยังโชว์ได้ แต่ไม่เอาไปตัดสินว่าถึงปลายทาง
        gps_dt   = pos.get("gps_dt") if pos else None
        stale    = bool(gps_dt and now_dt - gps_dt > timedelta(minutes=GPS_STALE_MINS))
        past_dep = _past_depot(pos, depot, dest_coord)
        near_km  = (_haversine_km(pos["lat"], pos["lng"], dest_coord[0], dest_coord[1])
                    if pos and dest_coord else None)
        at_depot = bool(pos and depot and
                        _haversine_km(pos["lat"], pos["lng"], depot[0], depot[1]) <= NEAR_DEST_KM)

        travel_mins   = None
        eta_time_str  = None
        diff_min      = None
        status        = "pending"
        prediction    = ""

        # ถ้าไม่พบใน PTGL ให้ลองใช้พิกัดคลังต้นทางแทน (รถยังอยู่คลัง)
        origin = pos or (
            {"lat": depot[0], "lng": depot[1], "location": t["source"]} if depot else None
        )

        actual   = False
        done     = _is_done(t)

        if _is_cancelled(t):
            # ─ ยกเลิก/โหลดเก็บ → ไม่นับเป็นงานค้าง (เช็กช่องลูกค้าด้วย) ─
            status     = "cancelled"
            prediction = t["status_man"] or t["gps_status"] or t["customer"] or "ยกเลิก"

        elif t["arrive"]:
            # ─ มีเวลาเข้าปลายทางจริง (จากชีต หรือ TMS) → วัดช้า/เร็วจากของจริง ─
            status     = "arrived"
            actual     = True
            src        = " (เวลาจาก TMS)" if t["tms_filled"] else ""
            if t["arrive_dt"] is not None and sched_dt is not None:
                diff_min = int((t["arrive_dt"] - sched_dt).total_seconds() // 60)
                if diff_min > 15:
                    prediction = f"ถึง {t['arrive']} — ช้ากว่ากำหนด {_dur(diff_min)}{src}"
                elif diff_min < -10:
                    prediction = f"ถึง {t['arrive']} — เร็วกว่ากำหนด {_dur(diff_min)} ✓{src}"
                else:
                    prediction = f"ถึง {t['arrive']} — ตรงเวลา ✓{src}"
            else:
                prediction = f"ถึงปลายทางแล้ว ({t['arrive']}){src}"

        elif done:
            # ─ ชีตบอกว่าส่งเสร็จ แต่ไม่มีเวลาเข้าปลายทาง ─
            status     = "arrived"
            prediction = "จัดส่งเสร็จแล้ว"

        elif not is_today:
            # ─ ทริปวันอื่น: ดูสถานะจากชีตอย่างเดียว ไม่คำนวณ ETA ─
            status     = "pending"
            prediction = t["gps_status"] or "ไม่มีข้อมูลสถานะ"

        elif (near_km is not None and near_km <= NEAR_DEST_KM and not stale and not at_depot
              and (t["yard_time"] or t["load_out"] or t["depart"]
                   or (sched_dt is not None and now_dt >= sched_dt - timedelta(hours=3)))):
            # ─ GPS บอกว่ารถอยู่ที่ลูกค้าแล้ว แต่ยังไม่มีเวลาถึงจริง → ถือว่าถึง ─
            # (ต้องโหลดมาแล้ว หรือใกล้เวลาส่ง กันกรณีรถจอดพักใกล้ลูกค้าก่อนไปโหลด)
            status     = "arrived"
            prediction = f"ถึงปลายทางแล้วตาม GPS (ห่างลูกค้า {near_km:.1f} กม.) — รอเวลาถึงจริงจาก TMS"

        elif not t["yard_time"] and pos and depot and dest_coord and not past_dep:
            # ─ ช่วงที่ 1: ยังไม่เข้าลานจอด (AB ว่าง) และรถยังไม่ได้ผ่านคลังมาแล้ว
            #   คำนวณเส้นทางเต็ม: รถอยู่ตรงไหน → คลังต้นทาง → ปลายทาง ─
            to_depot = _get_travel_minutes(pos["lat"], pos["lng"], depot[0], depot[1], use_api)
            to_dest  = _get_travel_minutes(depot[0], depot[1],
                                           dest_coord[0], dest_coord[1], use_api)

            if to_depot is not None and to_dest is not None and sched_dt is not None:
                yard_m, load_m = _depot_minutes(t["source"], _vehicle_type(t["vtype"]))
                travel_mins  = to_depot + yard_m + load_m + to_dest
                eta_time_str, diff_min = eta_of(travel_mins)
                depot_eta    = eta_of(to_depot)[0]
                route        = (f"ถึงคลัง {t['source']} ~{depot_eta} "
                                f"(ลานจอด {_dur(yard_m)} + โหลด {_dur(load_m)}) "
                                f"แล้ววิ่งต่ออีก {_dur(to_dest)}")
                if diff_min > 15:
                    status     = "late"
                    prediction = f"⚠ คาดว่าจะช้า {_dur(diff_min)} — {route}"
                elif diff_min < -10:
                    status     = "early"
                    prediction = f"จะถึงเร็วกว่ากำหนด {_dur(diff_min)} ✓ — {route}"
                else:
                    status     = "transit"
                    prediction = f"น่าจะถึงตรงเวลา — {route}"
            else:
                status     = "pending"
                prediction = f"ยังไม่เข้าคลัง {t['source']}"

        elif origin and dest_coord:
            # ─ ช่วงที่ 2: อยู่คลังแล้ว / ออกเดินทางแล้ว / รถผ่านคลังมาแล้ว → ETA ถึง "ปลายทาง" ─
            travel = _get_travel_minutes(
                origin["lat"], origin["lng"],
                dest_coord[0], dest_coord[1],
                use_api,
            )
            # ยังโหลดไม่เสร็จ (AD ว่าง) → บวกเวลาที่ต้องใช้ในคลังเข้าไปด้วย
            # ยกเว้นรถอยู่ใกล้ลูกค้ามากกว่าคลังชัดเจน = โหลดมาแล้ว แค่ชีตยังไม่มีเวลา
            if travel is not None and not t["load_out"] and not past_dep:
                yard_m, load_m = _depot_minutes(t["source"], _vehicle_type(t["vtype"]))
                travel += load_m if t["yard_time"] else yard_m + load_m

            if travel is not None and sched_dt is not None:
                travel_mins  = travel
                eta_time_str, diff_min = eta_of(travel)

                if diff_min < -10:
                    status     = "early"
                    prediction = f"จะถึงเร็วกว่ากำหนด {_dur(diff_min)} ✓"
                elif diff_min <= 15:
                    status     = "transit"
                    prediction = f"น่าจะถึงตรงเวลา (ห่างอีก {_dur(travel)})"
                else:
                    status     = "late"
                    prediction = f"⚠ คาดว่าจะช้า {_dur(diff_min)}"
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
        # ข้อความขึ้นต้นด้วย 📞 เสมอ — หน้าเว็บใช้ตัวนี้เช็กว่า "ต้องไล่ชั่วโมงนี้"
        if (status not in ("arrived", "cancelled") and not t["depart"]
                and t["call_dt"] is not None and now_dt >= t["call_dt"]):
            late_call = int((now_dt - t["call_dt"]).total_seconds() // 60)
            prediction = (f"📞 ยังไม่ออกจากคลัง — ถึงเวลาโทรตาม พขร (นัดไว้ {t['call_time']}"
                          + (f", เลยมา {_dur(late_call)}" if late_call >= 60 else "")
                          + ") · ") + prediction

        if stale and gps_dt is not None and status not in ("cancelled",):
            prediction += f" · ⚠ GPS ไม่อัปเดต (ล่าสุด {gps_dt:%H:%M})"

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
            tms_filled   = t["tms_filled"],
            current_lat  = pos["lat"]      if pos else None,
            current_lng  = pos["lng"]      if pos else None,
            current_loc  = pos["location"] if pos else None,
            gps_time     = gps_dt.strftime("%d/%m %H:%M") if gps_dt else None,
            gps_stale    = stale,
            dest_lat     = dest_coord[0] if dest_coord else None,
            dest_lng     = dest_coord[1] if dest_coord else None,
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
                    f"(ถึง ~{prev.eta_time} + ลงของ {_dur(UNLOAD_MINS)} + วิ่ง {_dur(leg)})")
            if sd is None:
                cur.prediction = note
                continue
            cur.diff_minutes = int((e - sd).total_seconds() // 60)
            if cur.diff_minutes > 15:
                cur.status     = "late"
                cur.prediction = f"⚠ คาดว่าจะช้า {_dur(cur.diff_minutes)} — {note}"
            elif cur.diff_minutes < -10:
                cur.status     = "early"
                cur.prediction = f"จะถึงเร็วกว่ากำหนด {_dur(cur.diff_minutes)} ✓ — {note}"
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
        "position_source": _pos_source,
        "has_EZ_POS_USER": bool(os.environ.get("EZ_POS_USER")),
        "has_TMS_SHEET_ID": bool(TMS_SHEET_ID),
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
    out["has_EZ_POS_USER"]         = bool(os.environ.get("EZ_POS_USER"))
    out["has_TMS_SHEET_ID"]        = bool(TMS_SHEET_ID)

    # 2. eZView API ตำแหน่ง (ไม่โชว์รหัสผ่าน โชว์แค่ผล)
    if os.environ.get("EZ_POS_USER"):
        _pos_cache.pop("all", None)
        api = _fetch_positions_api()
        out["ezview_pos_ok"]   = api is not None
        out["ezview_pos_cars"] = len({id(v) for v in (api or {}).values()})

    # 3. credentials parse
    try:
        creds = _build_creds()
        out["service_account_email"] = getattr(creds, "service_account_email", "?")
    except Exception as e:
        out["creds_error"] = f"{type(e).__name__}: {e}"
        return out

    # 4. เปิดแต่ละ Sheet / แต่ละแท็บ
    sheets = [
        ("PTGL",   PTGL_ID, PTGL_TAB),
        ("SOURCE", SOURCE_ID, PLAN_TAB),   # ไฟล์ต้นทางจริง — รายการทริป
        ("DEST",   DEST_ID, DEST_TAB),     # พิกัดปลายทาง (ไฟล์เดียวกับ SOURCE)
        ("PLAN",   PLAN_ID, PLAN_TAB),     # Test Report Ontime PTGLG — ไทม์ไลน์/ChaseLog เท่านั้น
    ]
    if TMS_SHEET_ID:
        sheets.append(("TMS", TMS_SHEET_ID, TMS_TAB))   # เวลาเข้า-ออกจริงจาก MLSTMS
    for label, sid, tab in sheets:
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
# 1 ทริป = 1 แถว — ตำแหน่งรายชั่วโมงไล่ไปทางขวา (0:00 น. ถึง 23:00 น.)
# โครงสร้าง: A=key B=วันที่ C=คลังต้นทาง D=เที่ยววิ่ง E=Drop F=เบอร์รถ G=ปลายทาง
#            H=ปริมาณ I=เลขที่ใบกำกับ J=สถานะ K=พิกัดตอนกด L=โดย M=ไล่เมื่อ N.. = รายชั่วโมง

CHASE_HEADER = [
    "key", "date", "คลังต้นทาง", "เที่ยววิ่ง", "Drop", "car_no", "customer",
    "ปริมาณ", "เลขที่ใบกำกับการขนส่ง", "status", "location", "by", "chased_at",
] + [f"{h}:00 น." for h in range(0, 24)]

# ตำแหน่ง (0-based) ของช่องที่โค้ดอ่าน/เขียนบ่อย — อ้างชื่อแทนเลข กันพลาดเวลาสลับคอลัมน์
CH_KEY, CH_DATE, CH_SOURCE, CH_TRIP, CH_DROP, CH_CARNO, CH_CUSTOMER = 0, 1, 2, 3, 4, 5, 6
CH_VOLUME, CH_INVOICE, CH_STATUS, CH_LOC, CH_BY, CH_AT = 7, 8, 9, 10, 11, 12
CH_DESC_FIRST, CH_DESC_LAST = CH_SOURCE, CH_INVOICE   # ช่วงคอลัมน์ "รายละเอียดทริป" C:I


def _col_letter(n: int) -> str:
    """เลขคอลัมน์ (1-based) → ตัวอักษรแบบ A1 notation  27 → 'AA'"""
    s = ""
    while n > 0:
        n, r = divmod(n - 1, 26)
        s = chr(65 + r) + s
    return s


def _chase_tab_name(date_str: str) -> str:
    try:
        d = datetime.strptime(date_str, "%Y-%m-%d")
        return f"{CHASE_TAB}_{d.strftime('%d.%m.%Y')}"
    except ValueError:
        return f"{CHASE_TAB}_{date_str}"


def _chase_ws(date_str: str, sh=None):
    """เปิดแท็บ ChaseLog ของวันนั้นๆ ถ้ายังไม่มีก็สร้างให้ — ส่ง sh (Spreadsheet ที่เปิดไว้แล้ว) มาได้ กันเปิดไฟล์ซ้ำ"""
    sh  = sh or gspread.authorize(_build_creds()).open_by_key(PLAN_ID)
    tab = _chase_tab_name(date_str)
    try:
        return sh.worksheet(tab)
    except gspread.WorksheetNotFound:
        ncols = len(CHASE_HEADER)
        ws = sh.add_worksheet(title=tab, rows=2000, cols=ncols)
        ws.update(f"A1:{_col_letter(ncols)}1", [CHASE_HEADER])
        return ws



@app.get("/api/chase", include_in_schema=False)
def chase_list(date_str: str = Query(None, alias="date")):
    """คืนรายการที่ไล่แล้วของวันนั้น {key: {"at": "17:54", "status": "...", "loc": "...", "by": "..."}}"""
    target = date_str or _today_thai()
    # อ่านผ่านแคช (5 นาที) — หน้าเว็บเรียกทุกครั้งที่โหลด/รีเฟรช ถ้าอ่านสดทุกครั้ง
    # จะกิน quota "Read requests/min" หนักที่สุดในระบบ (ยิ่ง ChaseLog กว้าง 37 คอลัมน์)
    # ยังไม่มีแท็บของวันนั้น = ยังไม่มีใครไล่ คืนค่าว่างไปเลย ไม่ต้องสร้างแท็บให้เสียเวลา
    try:
        rows = _fetch_sheet(PLAN_ID, _chase_tab_name(target))
    except gspread.WorksheetNotFound:
        return {}
    except Exception as e:
        raise HTTPException(502, f"อ่าน ChaseLog ไม่ได้: {type(e).__name__}: {e}")
    out = {}
    for r in rows[1:]:
        if _cell(r, CH_KEY):
            out[_cell(r, CH_KEY)] = {
                "status": _cell(r, CH_STATUS), "loc": _cell(r, CH_LOC),
                "by": _cell(r, CH_BY), "at": _cell(r, CH_AT),
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
                     if _cell(r, CH_KEY) == key), None)

        chase_tab = _chase_tab_name(date_str)

        if clear:
            if hit:
                ws.delete_rows(hit)
            _drop_sheet_cache(PLAN_ID, chase_tab)     # เคลียร์แคช ครั้งหน้าจะอ่านของสด
            return {"ok": True, "cleared": True}

        at = _thai_now().strftime("%H:%M")
        if hit:
            # เขียนทับเฉพาะช่วง "สถานะ" (J:M) เท่านั้น — ไม่แตะคอลัมน์รายละเอียดทริป (C:I)
            # กับคอลัมน์รายชั่วโมง (N เป็นต้นไป) ที่ระบบอัตโนมัติเขียนไว้
            ws.update(
                f"{_col_letter(CH_STATUS + 1)}{hit}:{_col_letter(CH_AT + 1)}{hit}",
                [[status, location, by, at]],
                value_input_option="USER_ENTERED",
            )
        else:
            # แถวใหม่ (ยังไม่เคยมีรอบอัตโนมัติเขียนไว้) — เติมเท่าที่รู้จาก key
            # key = date|car_no|trip_no|drop|invoice_no ; คลังต้นทาง/ปริมาณ ไม่มีใน key
            # ปล่อยว่างไว้ก่อน เดี๋ยวรอบอัตโนมัติชั่วโมงถัดไปเติมให้เอง
            p = key.split("|")
            row = [""] * len(CHASE_HEADER)
            row[CH_KEY], row[CH_DATE] = key, date_str
            row[CH_TRIP]    = p[2] if len(p) > 2 else ""
            row[CH_DROP]    = p[3] if len(p) > 3 else ""
            row[CH_INVOICE] = p[4] if len(p) > 4 else ""
            row[CH_CARNO], row[CH_CUSTOMER] = car_no, customer
            row[CH_STATUS], row[CH_LOC], row[CH_BY], row[CH_AT] = status, location, by, at
            ws.append_row(row, value_input_option="USER_ENTERED")
        _drop_sheet_cache(PLAN_ID, chase_tab)
        return {"ok": True, "at": at}
    except Exception as e:
        raise HTTPException(502, f"บันทึก ChaseLog ไม่ได้: {type(e).__name__}: {e}")


@app.get("/api/cron/hourly-status", include_in_schema=False)
def cron_hourly_status(secret: str = Query("")):
    """เรียกจาก Apps Script (trigger ทุกชั่วโมง) — ทำทุกอย่างที่เคยเป็นหน้าที่ Apps Script ในไฟล์เดียวนี้:
    1) ซิงก์แท็บรายวัน (dd.mm.yyyy) จากไฟล์ต้นทาง  2) เก็บพิกัดปัจจุบันของทุกคันที่ยังไม่ถึง/ยังไม่ยกเลิก
    ลง ChaseLog แบบแนวนอน (ทริปละ 1 แถว ตำแหน่งรายชั่วโมงไปทางขวา)  3) เขียนพิกัด+สถานะลงคอลัมน์รายชั่วโมง
    (H:00 น. / H:00 สถานะ) ของแท็บรายวัน — ข้อมูลทั้งหมดอยู่ใน Google Sheet เท่านั้น ไม่มีที่เก็บภายนอกอีก"""
    if not CRON_SECRET or secret != CRON_SECRET:
        raise HTTPException(401, "unauthorized")

    try:
        return _cron_hourly_status_impl()
    except Exception as e:
        return JSONResponse(
            {"ok": False, "error": f"{type(e).__name__}: {e}",
             "trace": traceback.format_exc().splitlines()[-15:]},
            status_code=200,
        )


def _chase_hour_col(hour: int, header_row: list = None) -> Optional[int]:
    """คืนคอลัมน์ (1-based) ของชั่วโมงนั้นใน ChaseLog — หาจากหัวตารางจริงของชีตก่อน
    (กันกรณีแท็บเก่ายังเรียงคอลัมน์ไม่ตรงกับ CHASE_HEADER ปัจจุบัน) ไม่เจอค่อยใช้ CHASE_HEADER"""
    label = f"{hour}:00 น."
    if header_row:
        for i, cell in enumerate(header_row, start=1):
            if str(cell).strip() == label:
                return i
    try:
        return CHASE_HEADER.index(label) + 1   # 1-based
    except ValueError:
        return None


def _cron_hourly_status_impl():
    target = _today_thai()
    # เปิดไฟล์ครั้งเดียว ใช้ซ้ำทั้งคำขอ กัน quota อ่านหมด — ใส่ retry เพราะถ้าพลาดตรงนี้
    # จะล้มทั้งรอบ ข้อมูลของชั่วโมงนั้นหายไปเลย (เคยเจอ 503 ตอนตี 1)
    sh = _with_retry(lambda: gspread.authorize(_build_creds()).open_by_key(PLAN_ID))
    chase_ws = _chase_ws(target, sh=sh)

    result = get_trips(date_str=target)
    at     = _thai_now().strftime("%H:%M")
    hour   = _thai_now().hour
    saved  = 0

    # อ่าน ChaseLog ที่มีอยู่ → สร้าง lookup key → row number
    chase_tab = _chase_tab_name(target)
    chase_rows = _fetch_sheet(PLAN_ID, chase_tab)
    chase_key_to_row: dict[str, int] = {}
    chase_row_by_key: dict[str, list] = {}
    for ci, cr in enumerate(chase_rows[1:], start=2):
        ck = _cell(cr, CH_KEY)
        if ck:
            chase_key_to_row[ck] = ci
            chase_row_by_key[ck] = cr

    chase_header  = chase_rows[0] if chase_rows else []
    chase_hour_col = _chase_hour_col(hour, chase_header)   # คอลัมน์ชั่วโมงนี้ (1-based)
    chase_updates = []
    chase_new_rows = []

    for t in result.trips:
        if t.status in ("arrived", "cancelled"):
            continue
        loc = t.current_loc or (
            f"{t.current_lat:.5f}, {t.current_lng:.5f}" if t.current_lat is not None else ""
        )
        if not loc:
            continue
        key = f"{t.date}|{t.car_no}|{t.trip_no}|{t.drop}|{t.invoice_no}"
        loc_text_chase = f"{_thai_now().strftime('%d/%m/%Y %H:%M:%S')} / {loc}"

        # รายละเอียดทริป C:I — คลังต้นทาง / เที่ยววิ่ง / Drop / เบอร์รถ / ปลายทาง / ปริมาณ / เลขที่ใบกำกับ
        desc = [t.source, t.trip_no, t.drop, t.car_no, t.customer, t.volume, t.invoice_no]

        # ── ChaseLog แนวนอน: หาแถวเดิม → เขียนคอลัมน์ชั่วโมง ──
        chase_row_i = chase_key_to_row.get(key)
        if chase_row_i:
            if chase_hour_col:
                chase_updates.append({
                    "range": f"{_col_letter(chase_hour_col)}{chase_row_i}",
                    "values": [[loc_text_chase]],
                })
            # เติมรายละเอียดทริปให้แถวเดิมที่ยังว่าง (แท็บที่สร้างก่อนเพิ่มคอลัมน์พวกนี้)
            old = chase_row_by_key.get(key, [])
            if [_cell(old, i) for i in range(CH_DESC_FIRST, CH_DESC_LAST + 1)] != [str(d).strip() for d in desc]:
                chase_updates.append({
                    "range": f"{_col_letter(CH_DESC_FIRST + 1)}{chase_row_i}:{_col_letter(CH_DESC_LAST + 1)}{chase_row_i}",
                    "values": [desc],
                })
        else:
            new_row = [""] * len(CHASE_HEADER)
            new_row[CH_KEY], new_row[CH_DATE] = key, target
            new_row[CH_DESC_FIRST:CH_DESC_LAST + 1] = desc
            new_row[CH_LOC], new_row[CH_BY], new_row[CH_AT] = loc, "ระบบ (ทุกชั่วโมง)", at
            if chase_hour_col:
                while len(new_row) < chase_hour_col:
                    new_row.append("")
                new_row[chase_hour_col - 1] = loc_text_chase
            chase_new_rows.append(new_row)
            chase_key_to_row[key] = len(chase_rows) + len(chase_new_rows)
        saved += 1

    # เขียน ChaseLog — batch update แถวเดิม + append แถวใหม่
    chase_written = False
    chase_error   = None
    try:
        if chase_updates:
            _with_retry(lambda: chase_ws.batch_update(chase_updates, value_input_option="USER_ENTERED"))
        if chase_new_rows:
            ncols = len(CHASE_HEADER)
            for nr in chase_new_rows:
                while len(nr) < ncols:
                    nr.append("")
            start = chase_ws.row_count + 1 if not chase_rows else len(chase_rows) + 1
            rng = f"A{start}:{_col_letter(ncols)}{start + len(chase_new_rows) - 1}"
            _with_retry(lambda: chase_ws.update(rng, chase_new_rows, value_input_option="USER_ENTERED"))
        chase_written = True
        _refresh_sheet_cache(PLAN_ID, chase_tab, chase_ws)
    except Exception as e:
        chase_error = f"{type(e).__name__}: {e}"

    return {
        "ok": True, "date": target, "saved": saved, "checked": len(result.trips),
        "chase_written": chase_written, "chase_error": chase_error,
    }


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


# ตำแหน่งย้อนหลังรายชั่วโมงต่อคัน -- PTGL เป็น "ตำแหน่งปัจจุบัน" อย่างเดียว
# บันทึกซ้ำก็ยังเป็นค่าล่าสุดเสมอ จึงอ่านประวัติจากคอลัมน์รายชั่วโมงใน ChaseLog
# ที่รอบอัตโนมัติเขียนสะสมไว้ให้ทุกชั่วโมงแทน


@app.get("/api/timeline")
def timeline(
    car_no:   str = Query(..., description="เบอร์รถ เช่น PTL.403 หรือ NO.418"),
    date_str: str = Query(None, alias="date", description="yyyy-MM-dd (default=วันนี้)", example="2026-08-29"),
):
    """ตำแหน่งรายชั่วโมงของรถคันเดียวในวันที่ระบุ — อ่านจากแท็บ ChaseLog ของวันนั้น

    รถคันเดียวมีได้หลายทริปในวันเดียว (คนละแถวใน ChaseLog) แต่ตำแหน่งรายชั่วโมง
    เป็นของ "รถ" ไม่ใช่ของทริป จึงรวมทุกแถวของรถคันนั้นเข้าด้วยกัน
    ชั่วโมงไหนมีค่าในแถวใดก็ใช้ค่านั้น"""
    if date_str:
        try:
            d = datetime.strptime(date_str, "%Y-%m-%d")
        except ValueError:
            raise HTTPException(400, "date ต้องเป็นรูปแบบ yyyy-MM-dd")
    else:
        d = datetime.strptime(_today_thai(), "%Y-%m-%d")
    target   = d.strftime("%Y-%m-%d")
    tab_name = _chase_tab_name(target)

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

    car_key   = _car_key(car_no)
    car_rows  = [r for r in rows[1:]
                 if car_key and _car_key(_cell(r, CH_CARNO)) == car_key]
    if not car_rows:
        return {"tab": tab_name, "car_no": car_no, "found": False, "timeline": []}

    entries = []
    for idx, label in hour_cols:
        val = next((_cell(r, idx) for r in car_rows if _cell(r, idx)), "")
        if val:
            entries.append({"hour": label, "raw": val})

    return {"tab": tab_name, "car_no": car_no, "found": True, "timeline": entries}


@app.get("/api/match")
def match(date_str: str = Query(None, alias="date")):
    """เช็คว่าเบอร์รถ / ชื่อปลายทาง / ทริป TMS จับคู่กันได้กี่รายการ"""
    target   = date_str or _today_thai()
    ptgl_map = fetch_ptgl()
    dest_map = fetch_destinations()
    trips    = fetch_trips(target)
    tms_n    = _enrich_from_tms(trips, target)

    car_hit  = [t["car_no"]   for t in trips if t["car_key"] in ptgl_map]
    car_miss = [t["car_no"]   for t in trips if t["car_key"] not in ptgl_map]
    dst_hit  = [t["customer"] for t in trips if t["customer"] in dest_map]
    dst_miss = [t["customer"] for t in trips if t["customer"] not in dest_map]

    return {
        "date":            target,
        "trips":           len(trips),
        "position_source": _pos_source,
        "car_matched":     len(car_hit),
        "car_unmatched":   sorted(set(car_miss))[:20],
        "dest_matched":    len(dst_hit),
        "dest_unmatched":  sorted(set(dst_miss))[:20],
        "tms_filled":      tms_n,
        "tms_not_filled":  sorted({t["car_no"] for t in trips
                                   if not t["tms_filled"] and not t["arrive"]})[:20],
        "ptgl_keys_sample":  sorted(ptgl_map.keys())[:20],
        "dest_names_sample": sorted(dest_map.keys())[:20],
    }


@app.get("/", response_class=HTMLResponse, include_in_schema=False)
def dashboard():
    warn = "" if _app_password() else "1"
    return DASHBOARD_HTML.replace("__NOPASS__", warn)


PLAN_LAST_COL = 26   # แสดงคอลัมน์ A–Z ของชีตแผนงาน
PLAN_FRESH_MIN_SECS = 15   # ปุ่มรีเฟรชอ่านชีตสดได้ไม่ถี่กว่านี้ (วินาที)
# ชีตที่หน้าแผนงาน (/plan) อ่าน — แยกจาก SOURCE_ID ที่หน้าเช็กรถใช้ จะได้ทดลองกับชีต DEMO ได้
# โดยไม่กระทบหน้าเช็กรถ ตั้ง PLAN_PAGE_ID / PLAN_PAGE_TAB ที่ Vercel (ไม่ตั้ง = ใช้ชีตเดิม)
PLAN_PAGE_ID  = os.environ.get("PLAN_PAGE_ID")  or SOURCE_ID
PLAN_PAGE_TAB = os.environ.get("PLAN_PAGE_TAB") or PLAN_TAB


def _col_name(i: int) -> str:
    """0→A ... 25→Z (ใช้แสดงเหนือหัวตาราง ให้ตรงกับตัวอักษรคอลัมน์ในชีต)"""
    return chr(ord("A") + i)


def _plan_header_row(rows: list[list]) -> int:
    """หาแถวหัวตาราง — ในชีตจริงแถว 1 เป็นป้าย Formula/Manual แถว 2 ว่าง หัวจริงอยู่แถว 3
    แถว 1 กับแถว 3 มีช่องเต็มพอกัน จึงนับจำนวนช่องไม่ได้ ใช้หัวคอลัมน์วันที่ ("ประจำวันที่")
    เป็นตัวระบุแทน แล้วค่อยถอยไปใช้แถวที่ช่องเยอะสุดถ้าไม่เจอ"""
    for i, row in enumerate(rows[:6]):
        if "วันที่" in _cell(row, PLAN_DATE) and not _parse_date(_cell(row, PLAN_DATE)):
            return i
    best, best_n = 0, -1
    for i, row in enumerate(rows[:6]):
        n = sum(1 for c in row[:PLAN_LAST_COL] if str(c).strip())
        if n > best_n:
            best, best_n = i, n
    return best


@app.get("/api/plan", include_in_schema=False)
def plan_rows(date_str: str = Query(None, alias="date"), fresh: int = Query(0)):
    """แผนงานของวันที่ระบุ คอลัมน์ A–Z ตามชีต "แผนงาน Gasbulk" (อ่านอย่างเดียว)

    fresh=1 (ปุ่มรีเฟรช) = ข้ามแคชแล้วอ่านชีตสด แต่ไม่ถี่เกิน PLAN_FRESH_MIN_SECS วินาที
    กันคนกดรัวจนทะลุโควตา Google Sheets (60 ครั้ง/นาที) ซึ่งใช้ร่วมกับหน้าเช็กรถ"""
    target = date_str or _today_thai()
    key = f"{PLAN_PAGE_ID}:{PLAN_PAGE_TAB}"
    old = _sheet_cache.get(key)
    throttled = bool(fresh and old and time() - old[0] < PLAN_FRESH_MIN_SECS)
    if fresh and not throttled:
        _drop_sheet_cache(PLAN_PAGE_ID, PLAN_PAGE_TAB)
    try:
        rows = _fetch_sheet(PLAN_PAGE_ID, PLAN_PAGE_TAB)
    except Exception as e:
        if not old:
            # บอกสาเหตุให้อ่านออก แทน 500 เปล่าๆ (ข้อความ error ของ gspread/creds ไม่มีรหัสลับ)
            raise HTTPException(status_code=502, detail=f"อ่านชีตแผนงานไม่ได้ — {type(e).__name__}: {e}")
        _sheet_cache[key] = old          # อ่านสดไม่ได้ (เช่น quota เต็ม) — ใช้ของเดิมแทนหน้าจอว่าง
        rows = old[1]
    read_ts = _sheet_cache.get(key, (time(), None))[0]
    read_at = datetime.fromtimestamp(read_ts, timezone(timedelta(hours=TZ_OFFSET))).strftime("%H:%M:%S")
    h = _plan_header_row(rows)
    headers = [{"col": _col_name(i), "name": _cell(rows[h], i) if rows else ""}
               for i in range(PLAN_LAST_COL)]
    out = []
    for i in range(h + 1, len(rows)):
        row = rows[i]
        if _parse_date(_cell(row, PLAN_DATE)) != target:
            continue
        cells = [_cell(row, c) for c in range(PLAN_LAST_COL)]
        # สถานะ AA อยู่นอกช่วง A–Z จึงอ่านจากแถวเต็ม ไม่ใช่จาก cells
        flag = (_cell(row, PLAN_STATUS) + " " + _cell(row, PLAN_DEST)).lower()
        cancelled = any(k in flag for k in CANCEL_KEYWORDS)
        out.append({"row": i + 1, "cells": cells, "cancelled": cancelled})
    edit_block = _write_block_reason("PLAN_EDIT_ENABLED")
    return {"date": target, "fetched_at": _thai_now().strftime("%H:%M:%S"),
            "sheet_read_at": read_at, "throttled": throttled,
            "alt_source": PLAN_PAGE_ID != SOURCE_ID,      # True = กำลังอ่านชีตทดลอง ไม่ใช่ชีตจริง
            "can_edit": not edit_block, "edit_block_reason": edit_block,
            "headers": headers, "total": len(out), "rows": out}


# ─── นำเข้าใบจัดรถจาก Excel → ชีตแผนงาน (ทดลอง) ─────────────────────────────
# ไฟล์ Excel ใบจัดรถ: ชีต "ข้อมูลการจัดส่ง" คอลัมน์ E–AD (26 ช่อง) = คอลัมน์ A–Z ของชีตแผนงาน Gasbulk
# พอดี ตัวไฟล์มีสูตรคำนวณ (เลข JOB, พขร., เวลาแผน ฯลฯ) อยู่แล้ว จึงอ่าน "ค่าที่คำนวณแล้ว" มาลงทั้ง 26 ช่อง
# ปลอดภัยไว้ก่อน: ดูตัวอย่างได้เสมอ แต่เขียนลงชีตได้เมื่อ (1) ตั้ง PLAN_IMPORT_ENABLED=1 และ
# (2) ชีตปลายทางไม่ใช่ชีตจริง (SOURCE_ID) หรือไฟล์ ChaseLog (PLAN_ID)
IMPORT_SHEET     = "ข้อมูลการจัดส่ง"
IMPORT_COL_FIRST = 4            # คอลัมน์ E (นับจาก 0)
IMPORT_MAX_BYTES = 4 * 1024 * 1024   # Vercel รับ body ได้ราว 4.5MB
# ตำแหน่งในช่วง A–Z ที่ต้องจัดรูปแบบพิเศษ (นับจาก 0)
_IMP_DATE_COLS = (2, 5)         # C ประจำวันที่, F วันที่ส่งมอบ → dd/mm/yyyy
_IMP_STAMP_COLS = (23, 24, 25)  # X, Y, Z เวลาแผน (P) → dd/mm/yyyy HH:MM:SS


def _xl_cell(v, idx: int) -> str:
    """ค่าจาก Excel → ข้อความรูปแบบที่คนอ่าน (dd/mm/yyyy) ใช้โชว์ในตัวอย่าง; ตอนเขียนลงชีตจะถูกแปลงเป็น ISO
    โดย _edit_value (กันชีตที่ตั้งโลแคลแบบสหรัฐอ่านวัน/เดือนสลับกัน)"""
    if v is None:
        return ""
    if isinstance(v, datetime):
        if idx in _IMP_DATE_COLS:
            return v.strftime("%d/%m/%Y")
        if idx in _IMP_STAMP_COLS or v.hour or v.minute or v.second:
            return v.strftime("%d/%m/%Y %H:%M:%S")
        return v.strftime("%d/%m/%Y")
    if hasattr(v, "hour") and hasattr(v, "minute") and not hasattr(v, "year"):   # datetime.time
        return v.strftime("%H:%M:%S")
    if isinstance(v, bool):
        return str(v)
    if isinstance(v, float):
        return str(int(v)) if v.is_integer() else str(round(v, 4))
    s = str(v).replace("\n", " ").strip()
    return "" if s.startswith("#") else s     # #VALUE! / #N/A จากสูตร = ถือว่าว่าง


def _sheet_safe(s: str) -> str:
    """กันสูตรแฝงในไฟล์ที่อัปโหลด: เขียนด้วย USER_ENTERED ข้อความที่ขึ้นต้นด้วย = + - @ จะถูกชีตตีความเป็นสูตร
    (เช่น หมายเหตุ "=IMPORTXML(...)") จึงนำหน้าด้วย ' ให้เป็นข้อความธรรมดา ยกเว้นตัวเลขจริง"""
    if s[:1] in ("=", "+", "@") or (s[:1] == "-" and not re.fullmatch(r"-?[0-9][0-9,]*(\.[0-9]+)?", s)):
        return "'" + s
    return s


def _parse_dispatch_xlsx(data: bytes) -> dict:
    """อ่านใบจัดรถ → {headers, rows, notes} (rows เป็นข้อความรูปแบบที่คนอ่าน) ยังไม่ตรวจและไม่เขียนอะไรที่ไหน"""
    try:
        import openpyxl
        wb = openpyxl.load_workbook(io.BytesIO(data), data_only=True, read_only=True)
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"เปิดไฟล์ Excel ไม่ได้ ({type(e).__name__}) — ต้องเป็นไฟล์ .xlsx")
    if IMPORT_SHEET not in wb.sheetnames:
        raise HTTPException(status_code=400,
            detail=f'ไม่พบชีต "{IMPORT_SHEET}" ในไฟล์ (มีชีต: {", ".join(wb.sheetnames)})')
    grid = [list(r) for r in wb[IMPORT_SHEET].iter_rows(values_only=True)]

    # แถวหัวตาราง = แถวที่คอลัมน์ F เขียนว่า "เลข JOB"
    hdr = next((i for i, r in enumerate(grid[:12])
                if len(r) > 5 and str(r[5] or "").replace("\n", " ").strip() == "เลข JOB"), None)
    if hdr is None:
        raise HTTPException(status_code=400, detail='หาแถวหัวตาราง (คอลัมน์ F = "เลข JOB") ไม่เจอ — ไฟล์ผิดรูปแบบ?')
    headers = [str(c or "").replace("\n", " ").strip()
               for c in (grid[hdr] + [None] * 40)[IMPORT_COL_FIRST:IMPORT_COL_FIRST + PLAN_LAST_COL]]

    rows, uncomputed = [], 0
    for r in grid[hdr + 1:]:
        cells = (list(r) + [None] * 40)[IMPORT_COL_FIRST:IMPORT_COL_FIRST + PLAN_LAST_COL]
        out = [_xl_cell(v, i) for i, v in enumerate(cells)]
        if not out[1]:                 # คอลัมน์ B = เลข JOB ว่าง = แถวว่าง/ไม่มีงาน
            if out[16] or out[15] or out[12]:
                uncomputed += 1        # มีข้อมูลแต่สูตรไม่มีค่า (ไฟล์ไม่เคยถูกคำนวณ/บันทึกใน Excel)
            continue
        rows.append(out)
    notes = []
    if uncomputed:
        notes.append(f"มี {uncomputed} แถวที่มีข้อมูลแต่ช่องเลข JOB ว่าง — ถ้าไฟล์เพิ่งแก้ ให้เปิดแล้วกดบันทึกใน Excel ก่อนอัปโหลดใหม่")
    return {"headers": headers, "rows": rows, "notes": notes}


def _review_rows(rows: list, notes=None) -> dict:
    """ตรวจชุดแถวที่จะนำเข้า (มาจากไฟล์ หรือที่แก้แล้วในหน้าต่างนำเข้า)
    คืน rows ที่จัดรูปแล้ว, sheet_rows (ค่าที่จะเขียนลงชีต), errors (ช่องที่ผิด — ห้ามเขียนจนกว่าจะแก้),
    warnings (ควรตรวจ แต่เขียนได้), date (วันที่ส่วนใหญ่ของชุด)"""
    rows = [[("" if v is None else str(v)) for v in (list(r) + [""] * PLAN_LAST_COL)[:PLAN_LAST_COL]] for r in rows]
    sheet_rows, errors, warnings, seen, marks = [], [], list(notes or []), {}, []
    first_date = None
    for n, out in enumerate(rows, start=1):
        conv = []
        for c, v in enumerate(out):
            try:
                conv.append(_edit_value(c, v))        # กติกาเดียวกับการแก้ทีละช่อง (วันที่/เวลา/น้ำหนัก/รายการเลือก)
            except HTTPException as e:
                errors.append({"r": n - 1, "c": c, "msg": str(e.detail)})
                conv.append("")
        sheet_rows.append(conv)
        tag = f"แถวที่ {n}"

        def flag(c: int, msg: str, listed: bool = True) -> None:
            marks.append({"r": n - 1, "c": c, "msg": msg})      # ช่องนี้ต้องทำสีแดงในตาราง
            if listed:
                warnings.append(f"{tag}: {msg}")

        if not out[15]:
            flag(15, "ยังไม่ใส่เบอร์รถ")
        if not out[12]:
            flag(12, "ยังไม่ใส่ปลายทาง")
        for c, v in enumerate(out):
            if v == "Check":
                flag(c, 'Excel ขึ้น "Check" (ข้อมูลอ้างอิงไม่พบ เช่น เบอร์รถไม่อยู่ในชีตข้อมูลรถ)')
        wt = out[9].replace(",", "")
        if out[16].startswith("08") and wt.replace(".", "", 1).isdigit() and float(wt) > 8000:
            flag(9, f"น้ำหนัก {int(float(wt)):,} กก. เกิน 8,000 สำหรับรถ 08 Tons")
        key = (out[1], out[13])
        if out[1] and key in seen:
            flag(13, f"เลข JOB + Drop ซ้ำกับแถวที่ {seen[key]}")
        seen[key] = n
        if not out[24]:
            flag(24, "ยังไม่ใส่เวลาเข้าโหลด (P) — เวลาออกจากฟรีต/เวลาโทรตาม พขร จะว่างด้วย", listed=False)
    no_load = sum(1 for r in rows if not r[24])
    if no_load:
        warnings.append(f"{no_load} แถวยังไม่ใส่เวลาเข้าโหลด (P) — เวลาออกจากฟรีต/เวลาโทรตาม พขร ของแถวนั้นจะว่างด้วย")
    counts: dict = {}
    for r in rows:
        iso = _parse_date(r[2])
        if iso:
            counts[iso] = counts.get(iso, 0) + 1
    date_iso = max(counts, key=counts.get) if counts else None
    if len(counts) > 1:
        warnings.append("มีหลายวันที่ในคอลัมน์ ประจำวันที่: " + ", ".join(sorted(counts)))
        for i, r in enumerate(rows):                  # แถวที่วันที่ไม่ตรงกับวันส่วนใหญ่ของชุด
            if _parse_date(r[2]) != date_iso:
                marks.append({"r": i, "c": 2, "msg": f"วันที่ไม่ตรงกับวันส่วนใหญ่ของไฟล์ ({date_iso})"})
    return {"rows": rows, "sheet_rows": sheet_rows, "errors": errors[:200], "errors_total": len(errors),
            "marks": marks[:1500], "warnings": warnings[:40], "warnings_total": len(warnings), "date": date_iso}


def _flag_on(name: str) -> bool:
    """สวิตช์เปิด = 1/true/yes/on (ไม่สนตัวพิมพ์เล็กใหญ่ ตัดช่องว่าง/ขึ้นบรรทัดใหม่/เครื่องหมายคำพูดที่ติดมาตอนวางค่า)"""
    return os.environ.get(name, "").strip().strip("\"'").strip().lower() in ("1", "true", "yes", "on")


def _write_block_reason(flag: str) -> str:
    """ว่าง = เขียนได้ ถ้ามีข้อความ = เขียนไม่ได้เพราะอะไร
    flag = ชื่อสวิตช์ที่ต้องเปิด (PLAN_IMPORT_ENABLED สำหรับนำเข้า, PLAN_EDIT_ENABLED สำหรับแก้ทีละช่อง)"""
    if not _flag_on(flag):
        seen = os.environ.get(flag)           # สวิตช์พวกนี้ไม่ใช่ความลับ โชว์ค่าที่เห็นจริงเพื่อไล่หาว่าตั้งผิดตรงไหน
        hint = " [ระบบไม่เห็นตัวแปรนี้เลย — ตั้งแล้วต้อง Redeploy]" if seen is None else f" [ระบบเห็นค่า {seen!r} — ต้องเป็น 1]"
        return f"ยังไม่เปิดการเขียนลงชีต (ตั้ง {flag}=1 ที่ Vercel){hint} — ตอนนี้ดูได้อย่างเดียว"
    if PLAN_PAGE_ID in (SOURCE_ID, PLAN_ID):
        return "ชีตปลายทางเป็นชีตจริง — ระบบยอมเขียนเฉพาะชีตทดลอง ตั้ง PLAN_PAGE_ID เป็นชีต DEMO ก่อน"
    return ""


def _import_block_reason() -> str:
    return _write_block_reason("PLAN_IMPORT_ENABLED")


def _head_index(col_c: list) -> int:
    """แถวหัวตาราง (นับจาก 0) จากคอลัมน์ C — ไม่เจอใช้แถวที่ 3 ตามชีตจริง"""
    return next((i for i, v in enumerate(col_c[:6]) if "วันที่" in v and not _parse_date(v)), 2)


def _array_cols(ws, head: int) -> set:
    """คอลัมน์ A–Z ที่ชีตเติมลงมาด้วยสูตรอาร์เรย์ (ARRAYFORMULA) จากแถวบน — ช่องล่างๆ ดูเหมือนว่างเปล่า
    แต่เขียนทับแล้วสูตรอาร์เรย์พัง (#REF!) จึงห้ามเขียนทั้งคอลัมน์"""
    try:
        top = ws.get(f"A1:Z{head + 4}", value_render_option=gspread.utils.ValueRenderOption.formula)
    except Exception:
        return set()
    out: set = set()
    for row in top or []:
        for c, v in enumerate(list(row)[:PLAN_LAST_COL]):
            u = str(v).upper()
            if u.startswith("=") and "ARRAYFORMULA(" in u:
                out.add(c)
    return out


@app.post("/api/plan/import", include_in_schema=False)
async def plan_import(file: Optional[UploadFile] = File(None), rows_json: str = Form(""),
                      commit: int = Form(0), replace: int = Form(1)):
    """ครั้งแรกส่ง file (อ่านใบจัดรถ) ครั้งต่อไปส่ง rows_json (แถวที่แก้ในหน้าต่างนำเข้า) เพื่อตรวจซ้ำ/เขียนจริง"""
    headers = None
    if rows_json:
        try:
            rows_in = json.loads(rows_json)
            assert isinstance(rows_in, list) and len(rows_in) <= 2000 and all(isinstance(r, list) for r in rows_in)
        except Exception:
            raise HTTPException(status_code=400, detail="ข้อมูลแถวที่ส่งมาไม่ถูกต้อง")
        notes: list = []
    else:
        if file is None:
            raise HTTPException(status_code=400, detail="ไม่ได้แนบไฟล์")
        data = await file.read()
        if len(data) > IMPORT_MAX_BYTES:
            raise HTTPException(status_code=413, detail="ไฟล์ใหญ่เกิน 4MB")
        parsed = _parse_dispatch_xlsx(data)
        rows_in, headers, notes = parsed["rows"], parsed["headers"], parsed["notes"]
    rv = _review_rows(rows_in, notes)
    sheet_rows = rv.pop("sheet_rows")
    block = _import_block_reason()
    info = {**rv, "headers": headers, "total": len(rv["rows"]), "can_commit": not block, "block_reason": block,
            "target": "ชีตทดลอง" if PLAN_PAGE_ID != SOURCE_ID else "ชีตจริง", "existing": None}

    # ในชีตปลายทางมีงานของวันนี้อยู่แล้วกี่แถว (ถ้าอ่านได้) — เอาไว้เตือนก่อนแทนที่
    if rv["date"]:
        try:
            sheet = _fetch_sheet(PLAN_PAGE_ID, PLAN_PAGE_TAB)
            info["existing"] = sum(1 for r in sheet if _parse_date(_cell(r, PLAN_DATE)) == rv["date"])
        except Exception:
            info["existing"] = None
    if not commit:
        return info

    # ── เขียนจริง ──
    if block:
        raise HTTPException(status_code=403, detail=block)
    if rv["errors_total"]:
        e0 = rv["errors"][0]
        raise HTTPException(status_code=400, detail=f"ยังมี {rv['errors_total']} ช่องที่ไม่ถูกต้อง (เช่น แถวที่ {e0['r'] + 1} "
                            f"คอลัมน์ {_col_name(e0['c'])}: {e0['msg']}) — แก้ในตารางก่อนเขียนลงชีต")
    if not rv["rows"] or not rv["date"]:
        raise HTTPException(status_code=400, detail="ไม่มีแถวงาน หรืออ่านวันที่ไม่ได้ — ไม่เขียนอะไรลงชีต")
    try:
        ws = gspread.authorize(_build_creds()).open_by_key(PLAN_PAGE_ID).worksheet(PLAN_PAGE_TAB)
        col_c = ws.col_values(PLAN_DATE + 1)
        head = _head_index(col_c)
        removed = 0
        if replace:
            # ลบแถวของวันเดียวกัน (ไล่จากล่างขึ้นบน กันเลขแถวเลื่อน) แล้วค่อยลงชุดใหม่
            hit = [i + 1 for i, v in enumerate(col_c) if i > head and _parse_date(v) == rv["date"]]
            blocks: list = []
            for r in hit:
                if blocks and r == blocks[-1][1] + 1:
                    blocks[-1][1] = r
                else:
                    blocks.append([r, r])
            for a, b in reversed(blocks):
                ws.delete_rows(a, b)
            removed = len(hit)
            col_c = ws.col_values(PLAN_DATE + 1)
        last = max([i + 1 for i, v in enumerate(col_c) if str(v).strip()] + [head + 1])
        start = last + 1
        need = start + len(sheet_rows) - 1
        if need > ws.row_count:
            ws.add_rows(need - ws.row_count)
        # ห้ามเขียนทับสูตรในชีต: ตรวจ "ทุกช่อง" ของช่วงที่จะเขียน (A–Z × ทุกแถวปลายทาง) ถ้าช่องไหนเป็นสูตร
        # หรืออยู่ในคอลัมน์ที่เติมด้วย ARRAYFORMULA ให้ส่ง None (Google Sheets API ข้ามช่องที่เป็น null ไม่แตะ)
        end = start + len(sheet_rows) - 1
        arr = _array_cols(ws, head)
        try:
            fm = ws.get(f"A{start}:Z{end}", value_render_option=gspread.utils.ValueRenderOption.formula) or []
        except Exception:
            fm = []

        def has_formula(ri: int, c: int) -> bool:
            try:
                return str(fm[ri][c]).startswith("=")
            except IndexError:
                return False

        values, kept = [], set()
        for ri, r in enumerate(sheet_rows):
            out_row = []
            for c in range(PLAN_LAST_COL):
                if c in arr or has_formula(ri, c):
                    out_row.append(None)
                    kept.add(c)
                else:
                    out_row.append(r[c])
            values.append(out_row)
        ws.update(values=values, range_name=f"A{start}", value_input_option="USER_ENTERED")
        kept_cols = "".join(_col_name(c) + " " for c in sorted(kept)).split()
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=502, detail=f"เขียนลงชีตไม่สำเร็จ — {type(e).__name__}: {e}")
    _drop_sheet_cache(PLAN_PAGE_ID, PLAN_PAGE_TAB)
    return {**info, "written": len(sheet_rows), "removed": removed, "first_row": start,
            "last_row": start + len(sheet_rows) - 1, "kept_formula_cols": kept_cols}


# ─── แก้ไขทีละช่องบนหน้าแผนงาน (ทดลอง) ───────────────────────────────────────────
# เปิดได้ต่อเมื่อ PLAN_EDIT_ENABLED=1 และชีตปลายทางไม่ใช่ชีตจริง (กติกาเดียวกับการนำเข้า Excel)
# กันชนกัน: ก่อนเขียนจะอ่านแถวนั้นสดจากชีต ถ้าค่าในช่องไม่ตรงกับที่คนแก้เห็นอยู่ (มีคนแก้ไปก่อน)
# หรือแถวเลื่อนไปแล้ว จะไม่เขียนทับ แต่ส่งค่าปัจจุบันกลับไปให้ตัดสินใจ
# ทุกครั้งที่แก้สำเร็จจะบันทึกประวัติ (เวลา/ผู้แก้/ค่าเดิม→ค่าใหม่) ลงแท็บ EditLog ของไฟล์ปลายทาง
EDIT_LOG_TAB = "EditLog"
_EDIT_TIME_RE = re.compile(r"^(\d{1,2})[:.](\d{2})(?::(\d{2}))?$")


class PlanEdit(BaseModel):
    row: int            # เลขแถวในชีต (เริ่มที่ 1)
    col: int            # ตำแหน่งคอลัมน์ 0..25 (A..Z)
    old: str = ""       # ค่าที่คนแก้เห็นก่อนแก้
    value: str = ""     # ค่าใหม่ที่พิมพ์
    key: str = ""       # "เลข JOB|Drop" ของแถวที่เห็น กันแถวเลื่อน
    by: str = ""        # ชื่อผู้แก้ (ไว้บันทึกประวัติ)
    override: bool = False   # ยืนยันเขียนทับ "สูตร" ในช่องนั้นด้วยค่าที่พิมพ์


def _edit_value(col: int, value: str) -> str:
    """ค่าที่พิมพ์ → ค่าที่เขียนลงชีต (วันที่เขียนเป็น ISO กันสลับวัน/เดือน); ผิดรูปแบบ = 400"""
    v = value.strip()
    if not v:
        return ""
    if col in _IMP_DATE_COLS:
        iso = _parse_date(v)
        if not iso:
            raise HTTPException(400, "วันที่ไม่ถูกต้อง — พิมพ์เป็น วัน/เดือน/ปี เช่น 08/10/2026")
        return iso
    if col == 6:
        m = _EDIT_TIME_RE.match(v)
        if not m or int(m.group(1)) > 23 or int(m.group(2)) > 59:
            raise HTTPException(400, "เวลาไม่ถูกต้อง — พิมพ์เป็น ชั่วโมง:นาที เช่น 13:30")
        return f"{int(m.group(1)):02d}:{m.group(2)}:{m.group(3) or '00'}"
    if col in _IMP_STAMP_COLS:
        parts = v.replace(",", " ").split()
        iso = _parse_date(parts[0]) if parts else None
        m = _EDIT_TIME_RE.match(parts[1]) if len(parts) == 2 else None
        if not iso or not m or int(m.group(1)) > 23 or int(m.group(2)) > 59:
            raise HTTPException(400, "ต้องเป็น วัน/เดือน/ปี ชั่วโมง:นาที เช่น 08/10/2026 07:30")
        return f"{iso} {int(m.group(1)):02d}:{m.group(2)}:{m.group(3) or '00'}"
    if col in (9, 10):
        n = v.replace(",", "")
        if not re.fullmatch(r"[0-9]+(\.[0-9]+)?", n):
            raise HTTPException(400, "น้ำหนักต้องเป็นตัวเลข เช่น 8000")
        return n
    allowed = _plan_options()["strict"].get(str(col))
    if allowed is not None and v not in allowed:        # ช่องเลือกอย่างเดียว: กันพิมพ์ผิดแม้ข้ามหน้าเว็บมาเรียกตรง
        raise HTTPException(400, "ช่องนี้ต้องเลือกจากรายการ: " + ", ".join(allowed[:15]) + (" …" if len(allowed) > 15 else ""))
    return _sheet_safe(v[:500])


# รายการให้เลือกตอนแก้ไข — อ่านจากแท็บในไฟล์แผนงานของหน้านี้ (PLAN_PAGE_ID) ไฟล์เดียว ไม่อ่านไฟล์อื่น แคช 10 นาที
#   ต้นทาง  ← แท็บ "List" คอลัมน์ A          เบอร์รถ ← แท็บ "ข้อมูลรถ" คอลัมน์ B
#   พขร.    ← แท็บ "ข้อมูลพขร." คอลัมน์ C (ไม่นับคนที่มีวันพ้นสภาพ)
#   ปลายทาง ← แท็บ "ข้อมูลสาขา" หรือ "ข้อมูลปลายทาง" คอลัมน์ A
# ช่อง "เลือกอย่างเดียว" (strict) = ต้นทาง/เที่ยววิ่ง/Drop/ประเภทรถ, ช่อง "พิมพ์ค้นหา" (suggest) = ปลายทาง/เบอร์รถ/พขร.
# ถ้าอ่านแท็บไม่ได้ ใช้รายการสำรองด้านล่างแทน (ต้นทางสำรองตรงกับชีต List ในไฟล์ Excel ใบจัดรถ)
PLAN_DEPOT_FALLBACK = ["SC BPK", "IRPC", "BSRC", "PTT TANK", "PTT KK", "PTT NSW", "PTT SRT",
                       "PTT  LP", "ATL พิจิตร", "ATL อุบลราชธานี", "UAC"]
_FIXED_STRICT = {
    "4":  ["เที่ยว 1", "เที่ยว 2", "เที่ยว 3"],      # E เที่ยววิ่ง
    "13": ["1", "2", "3", "4", "5"],                  # N Drop
    "16": ["08 Tons", "10 Tons", "Trailer"],          # Q ประเภทรถ
}
_SUGGEST_COLS = (12, 15, 18, 19)       # M ปลายทาง, P เบอร์รถ, S พขร.1, T พขร.2
_OPTS_TTL = 600
_opts_cache: tuple = (0.0, None)


def _first_tab_values(tabs, col: int, ok=None):
    """อ่านคอลัมน์ col ของแท็บแรกที่อ่านได้ → (รายการไม่ซ้ำเรียงตามไฟล์, ที่มา)
    อ่าน "เฉพาะไฟล์แผนงานของหน้านี้" (PLAN_PAGE_ID) เท่านั้น ไม่แอบไปอ่านไฟล์อื่น"""
    for tab in tabs:
        try:
            rows = _fetch_sheet(PLAN_PAGE_ID, tab)
        except Exception:
            continue
        vals: list = []
        for r in rows[1:]:
            v = _cell(r, col)
            if v and (ok is None or ok(r)) and v not in vals:
                vals.append(v)
        if vals:
            return vals, f"แท็บ {tab}"
    return [], ""


def _plan_options() -> dict:
    global _opts_cache
    ts, hit = _opts_cache
    if hit is not None and time() - ts < _OPTS_TTL:
        return hit
    src: dict = {}
    origins, src["ต้นทาง"] = _first_tab_values(["List"], 0)
    cars, src["เบอร์รถ"] = _first_tab_values(["ข้อมูลรถ"], 1, ok=lambda r: _cell(r, 1) != "เบอร์รถ")
    drivers, src["พขร."] = _first_tab_values(["ข้อมูลพขร."], 2, ok=lambda r: not _cell(r, 6) and _cell(r, 2) != "ชื่อ-สกุล")
    dests, src["ปลายทาง"] = _first_tab_values(["ข้อมูลสาขา", DEST_TAB], 0, ok=lambda r: _cell(r, 0) not in ("ปลางทาง", "ปลายทาง"))
    if not origins:
        origins, src["ต้นทาง"] = list(PLAN_DEPOT_FALLBACK), "รายการสำรองในระบบ"
    for d in DEPOTS:                    # คลังที่ระบบรู้จัก ต้องเลือกได้เสมอ
        if d not in origins:
            origins.append(d)

    seen: dict = {c: {} for c in _SUGGEST_COLS}       # ค่าที่มีอยู่แล้วในแผนงาน (เรียงตามที่พบบ่อย) เติมท้ายรายการ
    try:
        rows = _fetch_sheet(PLAN_PAGE_ID, PLAN_PAGE_TAB)
        for r in rows[_plan_header_row(rows) + 1:]:
            for c in _SUGGEST_COLS:
                v = _cell(r, c)
                if v:
                    seen[c][v] = seen[c].get(v, 0) + 1
    except Exception:
        pass
    def merged(base: list, c: int) -> list:
        extra = [v for v, _ in sorted(seen[c].items(), key=lambda kv: (-kv[1], kv[0])) if v not in base]
        return (base + extra)[:3000]
    result = {
        "strict": {**_FIXED_STRICT, "11": origins},
        "suggest": {"12": merged(dests, 12), "15": merged(cars, 15), "18": merged(drivers, 18), "19": merged(drivers, 19)},
        "from": src,
    }
    _opts_cache = (time(), result)
    return result


@app.get("/api/plan/options", include_in_schema=False)
def plan_options():
    """รายการตัวเลือกของช่อง: strict = ต้องเลือกจากรายการ, suggest = ค้นหา/พิมพ์ชื่อใหม่ได้ ('from' = อ่านมาจากแท็บไหน)"""
    return _plan_options()


@app.post("/api/plan/edit", include_in_schema=False)
def plan_edit(p: PlanEdit):
    block = _write_block_reason("PLAN_EDIT_ENABLED")
    if block:
        raise HTTPException(403, block)
    if not (0 <= p.col < PLAN_LAST_COL) or p.row < 2:
        raise HTTPException(400, "ตำแหน่งช่องไม่ถูกต้อง")
    new = _edit_value(p.col, p.value)
    try:
        sh = gspread.authorize(_build_creds()).open_by_key(PLAN_PAGE_ID)
        ws = sh.worksheet(PLAN_PAGE_TAB)
        cur = list(ws.row_values(p.row)) + [""] * PLAN_LAST_COL      # อ่านแถวนี้สดจากชีต
    except Exception as e:
        raise HTTPException(502, f"อ่านชีตไม่ได้ — {type(e).__name__}: {e}")
    cur_key = f"{cur[1]}|{cur[13]}" if cur[1] else ""
    if not any(str(x).strip() for x in cur[:PLAN_LAST_COL]):
        # แถวว่างทั้งแถว (ถูกลบ/ล้างไปแล้ว) — ไม่เขียนลงแถวว่างเพราะหน้าเว็บที่เปิดค้างไว้ยังเห็นข้อมูลเก่า
        return JSONResponse(status_code=409, content={"detail":
            "แถวนี้ถูกลบหรือว่างไปแล้วในชีต — กดรีเฟรชก่อน", "current": ""})
    if p.key != cur_key:
        return JSONResponse(status_code=409, content={"detail":
            "แถวนี้ในชีตเปลี่ยนไปแล้ว (มีคนแก้หรือแทรกแถว) — กดรีเฟรชแล้วแก้ใหม่", "current": cur[p.col]})
    if str(cur[p.col]).strip() != p.old.strip():
        return JSONResponse(status_code=409, content={"detail":
            "ช่องนี้มีคนแก้ไปก่อนแล้ว — ยังไม่เขียนทับ", "current": cur[p.col]})

    letter = _col_name(p.col)
    # ช่องที่เป็นสูตร: เขียนทับแล้วสูตรของแถวนั้นหายถาวร จึงไม่เขียนเว้นแต่คนแก้ยืนยัน (override)
    formula = ""
    try:
        fm = ws.get(f"{letter}{p.row}", value_render_option=gspread.utils.ValueRenderOption.formula)
        formula = str(fm[0][0]) if fm and fm[0] else ""
    except Exception:
        formula = ""
    in_array = False
    try:
        in_array = p.col in _array_cols(ws, _head_index(ws.col_values(PLAN_DATE + 1)))
    except Exception:
        in_array = False
    is_formula = formula.startswith("=") or in_array
    if is_formula and not p.override:
        return JSONResponse(status_code=423, content={"detail":
            "ช่องนี้เป็นสูตรในชีต (ค่าถูกคำนวณจากช่องอื่น)", "formula": True, "current": cur[p.col]})
    try:
        ws.update(values=[[new]], range_name=f"{letter}{p.row}", value_input_option="USER_ENTERED")
        got = ws.get(f"{letter}{p.row}")                              # อ่านกลับ = ค่าที่ชีตแสดงจริง
        shown = got[0][0] if got and got[0] else ""
        fresh_row = (list(ws.row_values(p.row)) + [""] * PLAN_LAST_COL)[:PLAN_LAST_COL]   # ช่องสูตรที่พึ่งช่องนี้คำนวณใหม่แล้ว
    except Exception as e:
        raise HTTPException(502, f"เขียนลงชีตไม่สำเร็จ — {type(e).__name__}: {e}")

    hit = _sheet_cache.get(f"{PLAN_PAGE_ID}:{PLAN_PAGE_TAB}")         # แก้แคชในช่องเดียว ไม่ต้องอ่านทั้งชีตใหม่
    if hit and p.row - 1 < len(hit[1]):
        r = hit[1][p.row - 1]
        r.extend([""] * (PLAN_LAST_COL - len(r)))
        r[:PLAN_LAST_COL] = fresh_row

    logged = True
    try:                                                              # ประวัติการแก้ไข (ล้มเหลวไม่กระทบการแก้)
        try:
            lg = sh.worksheet(EDIT_LOG_TAB)
        except gspread.WorksheetNotFound:
            lg = sh.add_worksheet(EDIT_LOG_TAB, rows=2000, cols=8)
            lg.append_row(["เวลา", "ผู้แก้", "แถว", "คอลัมน์", "ค่าเดิม", "ค่าใหม่", "JOB|Drop", "หมายเหตุ"])
        lg.append_row([_thai_now().strftime("%Y-%m-%d %H:%M:%S"), p.by[:60], p.row, letter,
                       p.old, shown, cur_key, ("เขียนทับสูตร: " + (formula[:80] or "ARRAYFORMULA ของคอลัมน์")) if is_formula else ""],
                      value_input_option="RAW")
    except Exception:
        logged = False
    return {"ok": True, "value": shown, "row": p.row, "col": p.col, "cells": fresh_row,
            "overwrote_formula": is_formula, "logged": logged}


@app.get("/plan", response_class=HTMLResponse, include_in_schema=False)
def plan_page():
    return PLAN_HTML


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
    return (SETTINGS_HTML
            .replace("__PWSET__", "ตั้งแล้ว ✓" if _app_password() else "ยังไม่ได้ตั้ง")
            .replace("__POSSRC__", "eZView API (ดึงตรง)" if os.environ.get("EZ_POS_USER") and EZ_POS_URL else "ชีต PTGL")
            .replace("__TMSSRC__", "เปิด (แท็บ TripDetails)" if TMS_SHEET_ID else "ปิด — ยังไม่ได้ตั้ง TMS_SHEET_ID"))


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
    <div class="row"><span>แหล่งข้อมูลตำแหน่งรถ</span><b>__POSSRC__</b></div>
    <div class="row"><span>เวลาเข้า-ออกจริงจาก TMS</span><b>__TMSSRC__</b></div>
    <div class="row"><span>แหล่งข้อมูล ETA</span><b>OpenRouteService</b></div>
    <div class="row"><span>เวลาโหลดที่คลัง</span><b>ตามตารางมาตรฐาน</b></div>
    <div class="row"><span>อายุการล็อกอิน</span><b>12 ชั่วโมง</b></div>
    <p style="color:var(--mut);font-size:13px;margin:14px 0 0">
      ค่าเหล่านี้แก้ที่ Vercel → Settings → Environment Variables
      (APP_PASSWORD, ORS_KEY, EZ_POS_USER, EZ_POS_PASS, TMS_SHEET_ID) หรือในไฟล์ main.py
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


PLAN_HTML = """<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>แผนงาน — Gasbulk Track</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root{--bg:#f1f5f9;--card:#fff;--line:#e2e8f0;--ink:#0f172a;--mut:#64748b;
        --late:#dc2626;--late-bg:#fef2f2;--pd-bg:#f8fafc;--tr-bg:#eff6ff;
        --chg-bg:#fffbeb;--chg-line:#fcd34d;--chg-ink:#92400e;--cc-bg:#fde68a}
  @media (prefers-color-scheme:dark){
    :root{--bg:#0b1220;--card:#131c2e;--line:#243044;--ink:#e8eef8;--mut:#93a3b8;
          --late-bg:#3b1418;--pd-bg:#1a2434;--tr-bg:#0f2340;
          --chg-bg:#2b2410;--chg-line:#92400e;--chg-ink:#fcd34d;--cc-bg:#5b4a14}}
  *{box-sizing:border-box}
  body{margin:0;background:var(--bg);color:var(--ink);
       font-family:'Noto Sans Thai',system-ui,-apple-system,sans-serif;font-size:15px}
  header{background:var(--card);border-bottom:1px solid var(--line);padding:14px 18px;
         position:sticky;top:0;z-index:10}
  .bar{display:flex;flex-wrap:wrap;gap:10px;align-items:center}
  h1{font-size:19px;margin:0;font-weight:700}
  .grow{flex:1}
  input,select,button{font-family:inherit;font-size:14px;padding:8px 12px;border-radius:9px;
        border:1px solid var(--line);background:var(--card);color:var(--ink)}
  input[type=search]{min-width:190px}
  button{cursor:pointer;font-weight:600}
  button.primary{background:#2563eb;border-color:#2563eb;color:#fff}
  /* เมนูหลักด้านซ้าย — จอเล็กย้ายขึ้นเป็นแถบแนวนอนด้านบน */
  body{padding-left:148px}
  .side{position:fixed;left:0;top:0;bottom:0;width:148px;background:var(--card);
        border-right:1px solid var(--line);padding:14px 10px;display:flex;flex-direction:column;
        gap:6px;z-index:20}
  .side .menu{display:flex;align-items:center;gap:9px;text-decoration:none;font-weight:700;
              font-size:15px;color:var(--ink);padding:11px 12px;border-radius:10px}
  .side .menu:hover{background:var(--tr-bg)}
  .side .menu.on{background:#2563eb;color:#fff}
  @media (max-width:820px){
    body{padding-left:0}
    .side{position:static;width:auto;flex-direction:row;border-right:0;
          border-bottom:1px solid var(--line);padding:8px 10px}
    .side .menu{flex:1;justify-content:center;padding:9px 8px}
  }
  main{padding:16px}
  .mut{color:var(--mut)}
  .cards{display:flex;flex-wrap:wrap;gap:10px;margin-bottom:12px}
  .c{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:10px 16px;min-width:120px}
  .c b{display:block;font-size:24px;line-height:1.1}
  .c span{font-size:12.5px;color:var(--mut)}
  .wrap{background:var(--card);border:1px solid var(--line);border-radius:12px;
        overflow:auto;max-height:calc(100vh - 250px)}
  table{border-collapse:separate;border-spacing:0;width:100%;font-size:14px}
  th,td{padding:9px 12px;border-bottom:1px solid var(--line);text-align:left;white-space:nowrap}
  thead th{position:sticky;background:var(--card);z-index:2;font-weight:600}
  thead tr.g th{top:0;text-align:center;font-size:12.5px;letter-spacing:.2px;color:#fff;padding:0 12px;height:28px}
  thead tr.h th{top:28px;border-bottom:2px solid var(--line)}
  thead th small{display:block;font-weight:500;color:var(--mut);font-size:11px}
  .g-job{background:#2563eb}.g-prod{background:#0891b2}.g-car{background:#7c3aed}.g-plan{background:#d97706}
  tbody tr:nth-child(even) td{background:var(--pd-bg)}
  tbody tr:hover td{background:var(--tr-bg)}
  tr.cx td{background:var(--late-bg) !important;color:var(--late)}
  tr.cx td.cust{text-decoration:line-through}
  /* ตรึงคอลัมน์ "แถว" กับ "เลข JOB" ไว้ซ้าย เลื่อนขวาแล้วยังรู้ว่าเป็นงานไหน */
  th.sk,td.sk{position:sticky;background:var(--card);z-index:1}
  thead th.sk{z-index:3}
  th.sk1,td.sk1{left:0;min-width:52px}
  th.sk2,td.sk2{left:52px;border-right:2px solid var(--line)}
  td.rn{color:var(--mut);font-size:12px}
  td.tm{font-weight:700;font-variant-numeric:tabular-nums}
  td.cust{font-weight:600;max-width:280px;overflow:hidden;text-overflow:ellipsis}
  td.car{font-weight:700;color:#7c3aed}
  td.num{text-align:right;font-variant-numeric:tabular-nums}
  td.pt{font-size:13px;color:var(--mut)}
  .pill{display:inline-block;padding:2px 10px;border-radius:999px;background:var(--tr-bg);
        color:#2563eb;font-weight:600;font-size:12.5px}
  /* ── แถวที่เปลี่ยนตั้งแต่ครั้งก่อนที่ดู ── */
  .chgbar{display:flex;flex-wrap:wrap;gap:8px 14px;align-items:center;background:var(--chg-bg);
          border:1px solid var(--chg-line);color:var(--chg-ink);border-radius:12px;
          padding:10px 14px;margin-bottom:12px;font-weight:600}
  .chgbar[hidden]{display:none}
  .chgbar label{font-weight:600;cursor:pointer}
  .chgbar button{border-color:var(--chg-line);color:var(--chg-ink);padding:6px 12px}
  .tag{display:inline-block;background:#f59e0b;color:#fff;border-radius:6px;padding:1px 8px;
       font-size:12px;font-weight:700;margin-right:6px}
  .job.chg{background:var(--chg-bg);box-shadow:inset 4px 0 0 #f59e0b}
  tbody tr.chg td{background:var(--chg-bg)}
  td[data-cc]{background:var(--cc-bg) !important;font-weight:700}
  /* ── โหมดแก้ไขทีละช่อง ── */
  .wrap.edit-on td[data-r]{cursor:cell}
  .wrap.edit-on td[data-r]:hover{outline:2px solid #2563eb;outline-offset:-2px}
  input.cellin{width:100%;min-width:110px;font:inherit;padding:3px 6px;border:2px solid #2563eb;
               border-radius:6px;background:var(--card);color:var(--ink)}
  #editBtn.on{background:#f59e0b;border-color:#f59e0b;color:#fff}
  .toast{position:fixed;right:18px;bottom:18px;background:#16a34a;color:#fff;padding:10px 16px;
         border-radius:10px;font-weight:600;z-index:80;box-shadow:0 4px 14px rgba(0,0,0,.25);max-width:420px}
  .toast.bad{background:var(--late)}
  /* ── หน้าต่างนำเข้า Excel ── */
  .imp-back{position:fixed;inset:0;background:rgba(15,23,42,.5);z-index:60;display:flex;
            align-items:flex-start;justify-content:center;padding:30px 16px;overflow:auto}
  .imp-back[hidden]{display:none}
  .imp{background:var(--card);border:1px solid var(--line);border-radius:14px;width:100%;
       max-width:1240px;padding:18px 20px}
  .imp-h{display:flex;justify-content:space-between;align-items:center;margin-bottom:8px}
  .imp-h b{font-size:18px}
  .imp-h button{border:0;background:none;font-size:20px;padding:2px 8px}
  .imp .box{border:1px solid var(--line);border-radius:10px;padding:10px 14px;margin:10px 0}
  .imp .ok{color:#16a34a;font-weight:700}
  .imp .bad{color:var(--late);font-weight:700}
  .imp ul{margin:6px 0 0;padding-left:20px;font-size:13.5px;max-height:130px;overflow:auto}
  .imp .tbl{max-height:420px;overflow:auto;border:1px solid var(--line);border-radius:10px}
  .imp table{font-size:13px;min-width:0;width:100%}
  .imp th,.imp td{padding:6px 9px}
  .imp thead th{position:sticky;top:0;background:var(--card);z-index:1}
  .imp td[data-ir]{cursor:cell}
  .imp td[data-ir]:hover{outline:2px solid #2563eb;outline-offset:-2px}
  .imp td.ied{background:var(--cc-bg);font-weight:700}
  .imp td.ierr{background:#fca5a5;color:#7f1d1d;outline:2px solid var(--late);outline-offset:-2px;font-weight:700}
  .imp td.iwarn{background:#fee2e2;color:#991b1b;outline:2px dashed #ef4444;outline-offset:-2px}
  .imp td.rn{color:var(--mut);font-size:11.5px}
  .imp button.go{background:#16a34a;border-color:#16a34a;color:#fff}
  .imp button.go:disabled{background:var(--pd-bg);border-color:var(--line);color:var(--mut);cursor:not-allowed}
  td.tm .mut{font-weight:500;font-size:12.5px}
  td.tm .xday{font-weight:700;font-size:12.5px;color:#d97706}
  a.tel{color:#16a34a;text-decoration:none;font-weight:600}
  a.tel:hover{text-decoration:underline}
  .chips{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:12px;align-items:center}
  .chips[hidden]{display:none}
  .chip{padding:6px 14px;border-radius:999px;border:1px solid var(--line);background:var(--card);
        color:var(--mut);cursor:pointer;font-size:13px;font-weight:600}
  .chip.on{color:#fff;border-color:transparent}
  .chip[data-g=job].on{background:#2563eb}.chip[data-g=prod].on{background:#0891b2}
  .chip[data-g=car].on{background:#7c3aed}.chip[data-g=plan].on{background:#d97706}
  .empty{padding:48px;text-align:center;color:var(--mut)}
  .warn{background:var(--late-bg);color:var(--late);padding:10px 14px;border-radius:10px;margin-bottom:12px}
  @media (max-width:820px){header{padding:11px 12px}main{padding:12px}
    input[type=search],input[type=date]{flex:1 1 130px;min-width:0}}
</style>
</head>
<body>
<aside class="side">
  <a class="menu" href="/">🚛 เช็กรถ</a>
  <a class="menu on" href="/plan">📋 แผนงาน</a>
</aside>
<header><div class="bar">
  <h1>📋 แผนงาน</h1>
  <span class="mut" id="stamp"></span>
  <span class="grow"></span>
  <button id="prev" title="วันก่อนหน้า">&lsaquo;</button>
  <input type="date" id="date">
  <button id="next" title="วันถัดไป">&rsaquo;</button>
  <b id="dlabel" style="font-size:14px"></b>
  <select id="depot"><option value="">ทุกคลัง</option></select>
  <input type="search" id="q" placeholder="ค้นหา รถ / ลูกค้า / ทะเบียน / ออเดอร์">
  <button id="editBtn" hidden title="แก้ไขข้อมูลทีละช่อง (ดับเบิลคลิกที่ช่อง)">✏️ โหมดแก้ไข</button>
  <button id="impOpen" title="อัปโหลดใบจัดรถ Excel เพื่อตรวจและนำเข้า">📥 นำเข้า Excel</button>
  <button class="primary" id="go">รีเฟรช</button>
</div></header>
<main>
  <div class="cards" id="cards"></div>
  <div class="chgbar" id="edithint" hidden>
    <span>✏️ <b>กำลังอยู่ในโหมดแก้ไข</b> — ดับเบิลคลิกที่ช่องเพื่อแก้ · Enter = บันทึกลงชีต · Esc = ยกเลิก ·
      แก้ได้ทุกช่อง A–Z (ช่องที่เป็นสูตรในชีตจะถูกแทนที่ด้วยค่าที่พิมพ์)</span>
  </div>
  <div class="chgbar" id="chgbar" hidden>
    <span id="chgtxt"></span>
    <label><input type="checkbox" id="onlychg"> ดูเฉพาะที่เปลี่ยน</label>
    <button id="ack">รับทราบทั้งหมด</button>
  </div>
  <div class="chips" id="chips"><span class="mut" style="font-size:13px">แสดงคอลัมน์:</span></div>
  <div id="err" class="warn" hidden></div>
  <div class="wrap"><table>
    <thead id="head"></thead>
    <tbody id="rows"></tbody>
  </table></div>
  <p class="mut" style="font-size:13px">ข้อมูลจากชีต "แผนงาน Gasbulk" คอลัมน์ A–Z (อ่านอย่างเดียว) &middot; สีแดง = ยกเลิก/โหลดเก็บ</p>
</main>

<div class="imp-back" id="impBack" hidden><div class="imp">
  <div class="imp-h"><b>📥 นำเข้าใบจัดรถจาก Excel</b><button id="impClose" title="ปิด">✕</button></div>
  <p class="mut" style="margin:0 0 8px;font-size:14px">
    เลือกไฟล์ใบจัดรถ (.xlsx) ระบบอ่านชีต "ข้อมูลการจัดส่ง" คอลัมน์ E–AD แล้วแสดงเป็นตาราง
    <b>แก้ข้อมูลในตารางนี้ได้เลยก่อนนำเข้า</b> ยังไม่เขียนอะไรลงชีตจนกว่าคุณจะกดยืนยัน</p>
  <input type="file" id="impFile" accept=".xlsx">
  <div id="impBody"></div>
</div></div>
<script>
const SRC_COL = 11;   // L คลังต้นทาง
let DATA = null;

function esc(s){
  return String(s == null ? '' : s).replace(/[&<>"]/g, c =>
    ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
}
function todayISO(){ return new Date(Date.now() + 7*3600*1000).toISOString().slice(0,10); }
function shift(iso, n){
  const d = new Date(iso + 'T00:00:00Z'); d.setUTCDate(d.getUTCDate() + n);
  return d.toISOString().slice(0,10);
}

async function load(fresh){
  const date = document.getElementById('date').value || todayISO();
  const btn = document.getElementById('go');
  if(fresh){ btn.disabled = true; btn.textContent = 'กำลังอ่านชีต...'; }
  // ช่องวันที่ของเบราว์เซอร์อาจโชว์เป็น เดือน/วัน/ปี จึงบอกวันที่แบบไทยกำกับอีกที กันอ่านสลับ
  const wd = ['อาทิตย์','จันทร์','อังคาร','พุธ','พฤหัสบดี','ศุกร์','เสาร์'];
  const dd = new Date(date + 'T00:00:00Z');
  document.getElementById('dlabel').textContent = isNaN(dd) ? '' :
    'วัน' + wd[dd.getUTCDay()] + ' ' + date.slice(8,10) + '/' + date.slice(5,7) + '/' + date.slice(0,4);
  const err = document.getElementById('err'); err.hidden = true;
  try{
    const r = await fetch('/api/plan?date=' + encodeURIComponent(date) + (fresh ? '&fresh=1' : ''));
    if(r.status === 401){ location.href = '/login'; return; }
    if(!r.ok){
      let why = '';
      try{ why = (await r.json()).detail || ''; }catch(x){}
      throw new Error(why || ('HTTP ' + r.status));
    }
    DATA = await r.json();
  }catch(e){
    err.textContent = 'โหลดแผนงานไม่สำเร็จ: ' + e.message; err.hidden = false; return;
  }finally{
    btn.disabled = false; btn.textContent = 'รีเฟรช';
  }
  // บอกว่าข้อมูลมาจากชีตตอนไหน (ไม่ใช่เวลาที่เปิดหน้า) จะได้รู้ว่าเห็นของล่าสุดหรือยัง
  document.getElementById('stamp').textContent = 'ข้อมูลจากชีตเมื่อ ' + DATA.sheet_read_at +
    (DATA.alt_source ? ' · 🧪 ชีตทดลอง (DEMO)' : '') +
    (fresh && DATA.throttled ? ' (เพิ่งอ่านสดไปไม่นาน รออีกสักครู่แล้วกดใหม่)' : '');
  computeChanges();
  document.getElementById('editBtn').hidden = !DATA.can_edit;      // ปุ่มแก้ไขขึ้นเฉพาะเมื่อเซิร์ฟเวอร์อนุญาต
  if(!DATA.can_edit && EDITING) setEditing(false);
  const sel = document.getElementById('depot'), keep = sel.value;
  const depots = [...new Set(DATA.rows.map(x => x.cells[SRC_COL]).filter(Boolean))].sort();
  sel.innerHTML = '<option value="">ทุกคลัง</option>' +
    depots.map(d => '<option>' + esc(d) + '</option>').join('');
  sel.value = depots.includes(keep) ? keep : '';
  render();
}

function render(){
  if(!DATA) return;
  const q = document.getElementById('q').value.trim().toLowerCase();
  const depot = document.getElementById('depot').value;
  updateBar();
  const rows = DATA.rows.filter(x =>
    (!depot || x.cells[SRC_COL] === depot) && (!ONLYCHG || x.chg) &&
    (!q || x.cells.join(' ').toLowerCase().includes(q)));
  const cx = rows.filter(x => x.cancelled).length;
  document.getElementById('cards').innerHTML =
    '<div class="c"><b>' + rows.length + '</b><span>แถวแผนงาน</span></div>' +
    '<div class="c"><b>' + (rows.length - cx) + '</b><span>ใช้งานจริง</span></div>' +
    '<div class="c"><b style="color:var(--late)">' + cx + '</b><span>ยกเลิก/โหลดเก็บ</span></div>';
  // เลือกเฉพาะคอลัมน์ในกลุ่มที่เปิดอยู่ (B = เลข JOB ตรึงไว้เสมอ)
  const shown = [];
  GROUPS.forEach(g => { if(ON[g.id]) g.cols.forEach(i => shown.push(i)); });
  let band = '<th class="sk sk1" rowspan="2">แถว</th>';
  GROUPS.forEach(g => {
    if(!ON[g.id]) return;
    band += '<th class="g-' + g.id + '" colspan="' + g.cols.length + '">' + g.name + '</th>';
  });
  document.getElementById('head').innerHTML = '<tr class="g">' + band + '</tr><tr class="h">' +
    shown.map(i => '<th' + (i === 1 ? ' class="sk sk2"' : '') + '><small>' + DATA.headers[i].col +
      '</small>' + esc(DATA.headers[i].name) + '</th>').join('') + '</tr>';
  document.getElementById('rows').innerHTML = rows.length
    ? rows.map(x => '<tr class="' + (x.cancelled ? 'cx ' : '') + (x.chg ? 'chg' : '') + '"><td class="sk sk1 rn">' +
        x.row + (x.chg ? '<br><span class="tag">' + (x.chg.type === 'new' ? 'ใหม่' : 'แก้') + '</span>' : '') + '</td>' +
        shown.map(i => {
          const h = cell(x.cells[i], i).replace('<td', '<td data-r="' + x.row + '" data-c="' + i + '"');
          return x.chg && x.chg.cols.includes(i)
            ? h.replace('<td', '<td data-cc="1" title="' + esc('เดิม: ' + (x.chg.old[i] || 'ว่าง')) + '"') : h;
        }).join('') + '</tr>').join('')
    : '<tr><td colspan="30" class="empty">ไม่มีแผนงานของวันที่เลือก</td></tr>';
}

// ── เทียบกับที่เห็นครั้งก่อน (เก็บในเบราว์เซอร์ของแต่ละคน ไม่เขียนลงชีต) ──
// ข้ามคอลัมน์ A (ลำดับ) เพราะเป็นสูตรรันเลข แทรกแถวทีเดียวเลขเลื่อนทั้งตาราง จะขึ้นว่าแก้ทุกแถว
const SEEN_PREFIX = 'gb_plan_seen_';
let ONLYCHG = false, GONE = 0;

function rowKeys(rows){                 // คีย์แถว = เลข JOB + Drop (JOB เดียวกันมีหลาย Drop) ถ้าซ้ำ/ว่างใช้เลขแถวในชีต
  const used = {};
  return rows.map(x => {
    let k = x.cells[1] ? x.cells[1] + '|' + x.cells[13] : ('r' + x.row);
    if(used[k]){ k = k + '#' + x.row; }
    used[k] = 1;
    return k;
  });
}
function readSeen(date){
  try{ return JSON.parse(localStorage.getItem(SEEN_PREFIX + date)); }catch(e){ return null; }
}
function saveSeen(){                    // จำค่าที่เห็นตอนนี้ไว้เป็นฐานเทียบครั้งหน้า
  const snap = {};
  DATA.rows.forEach(x => { snap[x.key] = x.cells; });
  try{
    localStorage.setItem(SEEN_PREFIX + DATA.date, JSON.stringify(snap));
    // เก็บไว้ไม่เกิน 10 วัน กันเต็มโควตาเบราว์เซอร์
    const ks = Object.keys(localStorage).filter(k => k.indexOf(SEEN_PREFIX) === 0).sort();
    while(ks.length > 10){ localStorage.removeItem(ks.shift()); }
  }catch(e){}
}
function computeChanges(){
  const keys = rowKeys(DATA.rows);
  DATA.rows.forEach((x, i) => { x.key = keys[i]; x.chg = null; });
  GONE = 0;
  const base = readSeen(DATA.date);
  if(!base){ saveSeen(); return; }          // ครั้งแรกของวันนี้ = จำไว้เฉยๆ ไม่ขึ้นว่ามีอะไรเปลี่ยน
  const seen = {};
  DATA.rows.forEach(x => {
    seen[x.key] = 1;
    const old = base[x.key];
    if(!old){ x.chg = {type:'new', cols:[], old:{}}; return; }
    const cols = [], oldv = {};
    x.cells.forEach((c, i) => { if(i > 0 && c !== (old[i] || '')){ cols.push(i); oldv[i] = old[i] || ''; } });
    if(cols.length) x.chg = {type:'edit', cols, old: oldv};
  });
  GONE = Object.keys(base).filter(k => !seen[k]).length;
}
function chgName(i){ return DATA.headers[i].name || DATA.headers[i].col; }
function chgTag(x){                     // ป้ายบอกว่าแถวนี้ใหม่/แก้อะไร พร้อมค่าเดิม → ค่าใหม่
  if(!x.chg) return '';
  if(x.chg.type === 'new') return '<span class="tag">ใหม่</span>';
  const shown = x.chg.cols.slice(0, 4).map(i =>
    esc(chgName(i)) + ' "' + esc(x.chg.old[i] || 'ว่าง') + '" → "' + esc(x.cells[i] || 'ว่าง') + '"');
  const more = x.chg.cols.length > 4 ? ' และอีก ' + (x.chg.cols.length - 4) + ' ช่อง' : '';
  return '<span class="tag">แก้</span><span>' + shown.join(' · ') + more + '</span>';
}
function updateBar(){
  const n = DATA.rows.filter(x => x.chg && x.chg.type === 'new').length;
  const e = DATA.rows.filter(x => x.chg && x.chg.type === 'edit').length;
  const bar = document.getElementById('chgbar');
  bar.hidden = !(n || e || GONE);
  if(bar.hidden) ONLYCHG = false;
  document.getElementById('chgtxt').textContent = '🔔 เปลี่ยนตั้งแต่ครั้งก่อนที่คุณดู: ใหม่ ' + n +
    ' · แก้ไข ' + e + (GONE ? ' · หายไป ' + GONE : '') + ' แถว';
  document.getElementById('onlychg').checked = ONLYCHG;
}

// กลุ่มคอลัมน์ — ปิดกลุ่มที่ไม่ใช้ ตารางจะแคบลงจนไม่ต้องเลื่อนซ้ายขวา
const GROUPS = [
  {id:'job',  name:'ใบงาน',           cols:[0,1,2,3,4,5,6,7]},
  {id:'prod', name:'สินค้า / จุดส่ง', cols:[8,9,10,11,12,13,14]},   // I เลขโหลด … N Drop, O หมายเหตุ
  {id:'car',  name:'รถ / พขร.',       cols:[15,16,17,18,19,20,21]},
  {id:'plan', name:'แผนเวลา',         cols:[22,23,24,25]},
];
let ON = {job:true, prod:true, car:true, plan:true};
try{ Object.assign(ON, JSON.parse(localStorage.getItem('gb_plan_groups') || '{}')); }catch(e){}

function buildChips(){
  const box = document.getElementById('chips');
  GROUPS.forEach(g => {
    const b = document.createElement('button');
    b.className = 'chip'; b.dataset.g = g.id; b.textContent = g.name;
    const sync = () => b.classList.toggle('on', !!ON[g.id]);
    b.onclick = () => {
      ON[g.id] = !ON[g.id]; sync(); render();
      try{ localStorage.setItem('gb_plan_groups', JSON.stringify(ON)); }catch(e){}
    };
    sync(); box.appendChild(b);
  });
}

// "06/10/2026, 03:00" → "03:00" (ถ้าเป็นคนละวันกับที่เลือก ใส่ "05/10 03:00" ให้รู้ว่าข้ามวัน)
function shortDT(s){
  const parts = String(s || '').split(', ');            // ["06/10/2026", "03:00"]
  const d = (parts[0] || '').split('/');                // ["06", "10", "2026"]
  if(parts.length < 2 || d.length !== 3) return esc(s);
  const sameDay = DATA && (d[2] + '-' + d[1].padStart(2,'0') + '-' + d[0].padStart(2,'0')) === DATA.date;
  // แสดงเหมือนในชีตเดิม "02/10/2026, 17:00" — วันที่จางถ้าเป็นวันเดียวกับที่เลือก, ส้มถ้าข้ามวัน
  const day = '<span class="' + (sameDay ? 'mut' : 'xday') + '">' + d[0] + '/' + d[1] + '/' + d[2] + ',</span> ';
  return day + esc(parts[1]);
}

function cell(v, i){
  if(v === '') return '<td></td>';
  if(i === 1)  return '<td class="sk sk2">' + esc(v) + '</td>';
  if(i === 6)  return '<td class="tm">' + esc(v) + '</td>';
  if(i === 9 || i === 10){ const n = Number(String(v).replace(/,/g, ''));
    return '<td class="num">' + (isNaN(n) ? esc(v) : n.toLocaleString('en-US')) + '</td>'; }
  if(i === 11) return '<td><span class="pill">' + esc(v) + '</span></td>';
  if(i === 12) return '<td class="cust" title="' + esc(v) + '">' + esc(v) + '</td>';
  if(i === 15) return '<td class="car">' + esc(v) + '</td>';
  if(i === 20 || i === 21){
    const tel = String(v).replace(/[^0-9+]/g, '');
    return '<td><a class="tel" href="tel:' + tel + '">' + esc(v) + '</a></td>'; }
  if(i >= 23)  return '<td class="tm">' + shortDT(v) + '</td>';
  return '<td>' + esc(v) + '</td>';
}

const dateEl = document.getElementById('date');
dateEl.value = todayISO();
dateEl.addEventListener('change', () => load(false));
document.getElementById('prev').onclick = () => { dateEl.value = shift(dateEl.value || todayISO(), -1); load(); };
document.getElementById('next').onclick = () => { dateEl.value = shift(dateEl.value || todayISO(), 1); load(); };
document.getElementById('go').onclick = () => load(true);
document.getElementById('depot').addEventListener('change', render);
document.getElementById('q').addEventListener('input', render);
document.getElementById('onlychg').onchange = e => { ONLYCHG = e.target.checked; render(); };
document.getElementById('ack').onclick = () => {          // รับทราบ = ใช้ข้อมูลตอนนี้เป็นฐานเทียบใหม่
  if(!DATA) return;
  saveSeen(); computeChanges(); ONLYCHG = false; render();
};
// ── แก้ไขทีละช่อง: ดับเบิลคลิก → พิมพ์ → Enter บันทึกลงชีต (เซิร์ฟเวอร์ตรวจชนกันก่อนเขียน) ──
let EDITING = false;

function toast(msg, bad){
  const t = document.createElement('div');
  t.className = 'toast' + (bad ? ' bad' : ''); t.textContent = msg;
  document.body.appendChild(t);
  setTimeout(() => t.remove(), bad ? 6000 : 2500);
}

function editorName(){                  // ชื่อผู้แก้ ไว้บันทึกประวัติ (จำไว้ในเบราว์เซอร์)
  let n = '';
  try{ n = localStorage.getItem('gb_plan_editor') || ''; }catch(e){}
  if(!n){
    n = (prompt('ชื่อผู้แก้ไข (ใช้บันทึกประวัติการแก้ไขในชีต EditLog):') || '').trim();
    if(n){ try{ localStorage.setItem('gb_plan_editor', n); }catch(e){} }
  }
  return n;
}

function setEditing(on){
  if(on && !editorName()) return;       // ต้องบอกชื่อก่อนถึงเปิดโหมดแก้ไขได้
  EDITING = on;
  if(on) loadOpts();                    // โหลดรายการตัวเลือกล่วงหน้า
  const b = document.getElementById('editBtn');
  b.classList.toggle('on', on);
  b.textContent = on ? '✏️ กำลังแก้ไข (กดเพื่อปิด)' : '✏️ โหมดแก้ไข';
  document.querySelector('.wrap').classList.toggle('edit-on', on);
  document.getElementById('edithint').hidden = !on;
}

function ownEdit(x, i, val, cells){    // แก้เองสำเร็จ → ไม่นับเป็น "เปลี่ยนตั้งแต่ครั้งก่อน" ของตัวเอง
  const base = readSeen(DATA.date);
  const oldKey = x.key;
  if(cells && cells.length) x.cells = cells.slice(0, 26);      // ช่องสูตรที่พึ่งช่องนี้ถูกคำนวณใหม่ในชีตแล้ว
  else x.cells[i] = val;
  x.cancelled = /ยกเลิก|โหลดเก็บ|cancel/i.test(x.cells[12]);
  const newKey = x.cells[1] ? x.cells[1] + '|' + x.cells[13] : ('r' + x.row);
  if(base){
    if(oldKey !== newKey && base[oldKey]){ base[newKey] = base[oldKey]; delete base[oldKey]; }
    base[newKey] = x.cells.slice();                            // ฐานเทียบของแถวนี้ = ค่าล่าสุดหลังแก้ (รวมช่องสูตรที่เปลี่ยนตาม)
    try{ localStorage.setItem(SEEN_PREFIX + DATA.date, JSON.stringify(base)); }catch(e){}
  }
  computeChanges();
}

async function saveCell(x, i, old, value, override){
  if(value.trim() === String(old).trim()){ render(); return; }
  const td = document.querySelector('td[data-r="' + x.row + '"][data-c="' + i + '"]');
  if(td) td.textContent = 'กำลังบันทึก...';
  try{
    const r = await fetch('/api/plan/edit', {method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({row: x.row, col: i, old: old, value: value,
                            key: x.cells[1] ? x.cells[1] + '|' + x.cells[13] : '', by: editorName(),
                            override: !!override})});
    if(r.status === 401){ location.href = '/login'; return; }
    let j = {};
    try{ j = await r.json(); }catch(e){}
    if(r.status === 423){                       // ช่องนี้เป็นสูตรในชีต — ถามก่อนเขียนทับ
      if(confirm((j.detail || 'ช่องนี้เป็นสูตร') + ' — ค่าตอนนี้: "' + (j.current || 'ว่าง') + '" — '
                 + 'ถ้าแก้ตรงนี้ สูตรในช่องนี้ของแถวนี้จะหาย แทนที่ด้วยค่าที่พิมพ์ ต้องการเขียนทับ?')){
        return saveCell(x, i, old, value, true);
      }
    }else if(r.status === 409){                 // มีคนแก้ไปก่อน — ไม่เขียนทับ โชว์ค่าปัจจุบันให้เห็น
      if(j.current !== undefined) x.cells[i] = j.current;
      computeChanges();
      toast((j.detail || 'ชนกับคนอื่น') + ' ค่าตอนนี้: "' + (j.current || 'ว่าง') + '"', true);
    }else if(!r.ok){
      toast(j.detail || ('HTTP ' + r.status), true);
    }else{
      ownEdit(x, i, j.value, j.cells);
      toast('บันทึกแล้ว ✓' + (j.overwrote_formula ? ' (เขียนทับสูตร)' : '') + (j.logged ? '' : ' (บันทึกประวัติ EditLog ไม่ได้)'));
    }
  }catch(e){ toast('บันทึกไม่สำเร็จ: ' + e.message, true); }
  render();
}

let OPTS = null;
async function loadOpts(){              // รายการตัวเลือกของช่อง (อ่านจากไฟล์ต้นทางฝั่งเซิร์ฟเวอร์)
  if(OPTS) return;
  try{
    const r = await fetch('/api/plan/options');
    if(!r.ok) return;
    OPTS = await r.json();
    let box = document.getElementById('dls');
    if(!box){ box = document.createElement('div'); box.id = 'dls'; box.hidden = true; document.body.appendChild(box); }
    box.innerHTML = Object.keys(OPTS.suggest).map(c => '<datalist id="dl' + c + '">' +
      OPTS.suggest[c].map(v => '<option value="' + esc(v) + '"></option>').join('') + '</datalist>').join('');
  }catch(e){}
}

// ตัวแก้ค่าในช่อง (ใช้ทั้งตารางหลักและตารางในหน้าต่างนำเข้า): เลือกอย่างเดียว / พิมพ์ค้นหา / พิมพ์อิสระ
function openEditor(td, i, old, onSave, onCancel){
  const strict = OPTS && OPTS.strict[String(i)];            // ต้นทาง/เที่ยววิ่ง/Drop/ประเภทรถ = เลือกอย่างเดียว
  const sug = OPTS && OPTS.suggest[String(i)];              // ปลายทาง/เบอร์รถ/พขร. = พิมพ์ค้นหาแล้วเลือก
  let el, done = false;
  const finish = fn => { if(done) return; done = true; fn(); };
  if(strict){
    el = document.createElement('select'); el.className = 'cellin';
    const list = strict.slice();
    if(old && list.indexOf(old) < 0) list.unshift(old);     // ค่าเดิมที่ไม่อยู่ในรายการ ยังเห็นและเลือกคืนได้
    el.innerHTML = '<option value="">(ว่าง)</option>' + list.map(v => '<option>' + esc(v) + '</option>').join('');
    el.value = old;
    el.addEventListener('change', () => finish(() => onSave(el.value)));              // เลือกแล้วบันทึกเลย
    el.addEventListener('keydown', ev => { if(ev.key === 'Escape'){ ev.preventDefault(); finish(onCancel); } });
    el.addEventListener('blur', () => setTimeout(() => finish(onCancel), 250));
  }else{
    el = document.createElement('input'); el.className = 'cellin'; el.value = old;
    if(sug && sug.length){
      el.setAttribute('list', 'dl' + i);
      el.value = ''; el.placeholder = old || 'พิมพ์เพื่อค้นหา';   // ล้างไว้ก่อน รายการถึงจะเด้งครบ ไม่ถูกกรองด้วยค่าเดิม
    }
    el.addEventListener('keydown', ev => {
      if(ev.key === 'Escape'){ ev.preventDefault(); finish(onCancel); }
      else if(ev.key === 'Enter'){
        ev.preventDefault();
        if(sug && sug.length && !el.value.trim()) finish(onCancel);          // ไม่ได้พิมพ์/เลือกอะไร = ไม่เปลี่ยน
        else finish(() => onSave(el.value));
      }
    });
    el.addEventListener('blur', () => finish(onCancel));      // คลิกที่อื่น = ยกเลิก ไม่บันทึกโดยไม่ตั้งใจ
  }
  td.textContent = ''; td.appendChild(el); el.focus();
  if(el.select && el.tagName === 'INPUT') el.select();
}

function startEdit(td, x, i){
  const old = x.cells[i];
  openEditor(td, i, old, v => saveCell(x, i, old, v), render);
}

document.getElementById('rows').addEventListener('dblclick', e => {
  if(!EDITING) return;
  const td = e.target.closest('td[data-r]');
  if(!td || td.querySelector('input')) return;
  const x = DATA.rows.find(r => r.row === Number(td.dataset.r));
  if(x) (OPTS ? Promise.resolve() : loadOpts()).then(() => startEdit(td, x, Number(td.dataset.c)));
});
document.getElementById('editBtn').onclick = () => setEditing(!EDITING);

// ── นำเข้าใบจัดรถจาก Excel: อัปโหลด → ตรวจ/แก้ในตาราง → ยืนยันถึงเขียนลงชีต ──
let IMPFILE = null;
let IMP = null;                          // {rows, headers, errs, edited, info, replace}
const COLS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.split('');
function impBody(html){ document.getElementById('impBody').innerHTML = html; }
function dmy(iso){ return iso ? iso.slice(8,10) + '/' + iso.slice(5,7) + '/' + iso.slice(0,4) : '?'; }

async function impSend(o){               // o = {rows?, commit?, replace?}  ไม่มี rows = ส่งไฟล์ที่เลือก
  const fd = new FormData();
  if(o.rows) fd.append('rows_json', JSON.stringify(o.rows)); else fd.append('file', IMPFILE);
  fd.append('commit', o.commit ? '1' : '0');
  fd.append('replace', o.replace ? '1' : '0');
  const r = await fetch('/api/plan/import', {method:'POST', body: fd});
  if(r.status === 401){ location.href = '/login'; return null; }
  let j = null;
  try{ j = await r.json(); }catch(e){}
  if(!r.ok) throw new Error((j && j.detail) || ('HTTP ' + r.status));
  return j;
}

function impMarkErrors(j){
  IMP.errs = {}; IMP.warns = {};
  (j.errors || []).forEach(e => { IMP.errs[e.r + ',' + e.c] = e.msg; });          // ผิดรูปแบบ: ห้ามเขียนจนกว่าจะแก้
  (j.marks || []).forEach(m => { const k = m.r + ',' + m.c; IMP.warns[k] = IMP.warns[k] ? IMP.warns[k] + ' / ' + m.msg : m.msg; });
}
function impBadRows(){                   // แถวที่มีช่องแดงอย่างน้อย 1 ช่อง
  const set = {};
  Object.keys(IMP.errs).concat(Object.keys(IMP.warns)).forEach(k => { set[k.split(',')[0]] = 1; });
  return set;
}

async function impPreview(){             // อ่านไฟล์ครั้งแรก
  impBody('<p class="mut">กำลังอ่านไฟล์...</p>');
  try{
    await loadOpts();                    // รายการเลือก (ต้นทาง/ปลายทาง/รถ ฯลฯ) ไว้ใช้ตอนแก้ในตาราง
    const j = await impSend({});
    if(!j) return;
    IMP = {rows: j.rows, headers: j.headers, edited: {}, errs: {}, warns: {}, info: j, replace: true, onlyBad: false};
    impMarkErrors(j);
    impRender();
  }catch(e){ impBody('<div class="box bad">อ่านไฟล์ไม่ได้: ' + esc(e.message) + '</div>'); }
}

async function impRecheck(){             // ตรวจซ้ำหลังแก้ (ส่งแถวที่แก้ไปให้เซิร์ฟเวอร์ตรวจด้วยกติกาเดียวกับตอนเขียน)
  try{
    const j = await impSend({rows: IMP.rows});
    if(j){ IMP.info = j; IMP.rows = j.rows; impMarkErrors(j); }
  }catch(e){ toast('ตรวจซ้ำไม่สำเร็จ: ' + e.message, true); }
  impRender();
}

function impRender(){
  const j = IMP.info, nerr = j.errors_total || 0;
  const oldTbl = document.querySelector('#impBody .tbl');
  const sx = oldTbl ? oldTbl.scrollLeft : 0, sy = oldTbl ? oldTbl.scrollTop : 0;
  const w = j.warnings.length
    ? '<div class="box"><b class="bad">⚠ ควรตรวจ ' + j.warnings_total + ' เรื่อง (เขียนลงชีตได้ แต่ควรดูก่อน)</b><ul>' +
      j.warnings.map(x => '<li>' + esc(x) + '</li>').join('') + '</ul></div>'
    : '<div class="box ok">✓ ไม่พบเรื่องที่ควรตรวจ</div>';
  const er = nerr
    ? '<div class="box"><b class="bad">✖ มี ' + nerr + ' ช่องที่ไม่ถูกต้อง (ช่องสีแดงในตาราง เอาเมาส์ชี้ดูสาเหตุ) — ต้องแก้ก่อนเขียนลงชีต</b></div>' : '';
  const head = '<tr><th>#</th>' + IMP.headers.map((h, c) => '<th><small>' + COLS[c] + '</small>' + esc(h) + '</th>').join('') + '</tr>';
  const bad = impBadRows(), nbad = Object.keys(bad).length;
  const body = IMP.rows.map((r, ri) => (IMP.onlyBad && !bad[ri]) ? '' : '<tr><td class="rn">' + (ri + 1) + '</td>' + r.map((v, c) => {
    const k = ri + ',' + c;
    const cls = IMP.errs[k] ? ' class="ierr" title="' + esc(IMP.errs[k]) + '"'
      : IMP.warns[k] ? ' class="iwarn" title="' + esc(IMP.warns[k]) + '"'
      : IMP.edited[k] ? ' class="ied"' : '';
    return '<td data-ir="' + ri + '" data-ic="' + c + '"' + cls + '>' + esc(v) + '</td>';
  }).join('') + '</tr>').join('');
  const nedit = Object.keys(IMP.edited).length;
  const ex = '<label><input type="checkbox" id="impReplace"' + (IMP.replace ? ' checked' : '') + '> ' + (j.existing
    ? 'แทนที่งานเดิมของวันที่ ' + dmy(j.date) + ' (ชีตมีอยู่แล้ว ' + j.existing + ' แถว จะถูกลบก่อนลงชุดใหม่)'
    : 'ลบงานเดิมของวันที่ ' + dmy(j.date) + ' ก่อนลงชุดใหม่ (ถ้ามี)') + '</label>';
  const ok = j.can_commit && j.total && !nerr;
  impBody(
    '<div class="box"><b>วันที่ ' + dmy(j.date) + '</b> · ' + j.total + ' แถวงาน · ปลายทาง: <b>' + esc(j.target) + '</b>' +
    (nedit ? ' · <span class="ied" style="padding:1px 8px;border-radius:6px">แก้แล้ว ' + nedit + ' ช่อง</span>' : '') + '</div>' +
    '<p class="mut" style="margin:6px 2px;font-size:13px">✏️ ดับเบิลคลิกช่องในตารางเพื่อแก้ก่อนเขียนลงชีต · Enter = ตกลง · Esc = ยกเลิก · ' +
    '<b class="bad">ช่องสีแดง = มีปัญหา (เอาเมาส์ชี้ดูสาเหตุ)</b> · ช่องสีเหลือง = ที่คุณแก้</p>' + er + w +
    '<label style="display:block;margin:6px 2px"><input type="checkbox" id="impOnlyBad"' + (IMP.onlyBad ? ' checked' : '') +
    '> ดูเฉพาะแถวที่มีช่องสีแดง (' + nbad + ' แถว)</label>' +
    '<div class="tbl"><table><thead>' + head + '</thead><tbody>' + body + '</tbody></table></div>' +
    '<div class="box">' + ex + '</div>' +
    (j.can_commit ? '' : '<div class="box bad">เขียนลงชีตไม่ได้ตอนนี้: ' + esc(j.block_reason) + '</div>') +
    '<button class="go" id="impGo"' + (ok ? '' : ' disabled') + '>เขียน ' + j.total + ' แถวลงชีต</button>');
  const t = document.querySelector('#impBody .tbl');
  if(t){ t.scrollLeft = sx; t.scrollTop = sy; }
  document.getElementById('impReplace').onchange = e => { IMP.replace = e.target.checked; };
  document.getElementById('impOnlyBad').onchange = e => { IMP.onlyBad = e.target.checked; impRender(); };
  document.getElementById('impGo').onclick = impCommit;
}

function impSet(r, c, v){                // แก้ช่องในตารางนำเข้า แล้วตรวจซ้ำ
  if(v === IMP.rows[r][c]){ impRender(); return; }
  IMP.rows[r][c] = v; IMP.edited[r + ',' + c] = 1;
  impRecheck();
}

document.getElementById('impBody').addEventListener('dblclick', e => {
  const td = e.target.closest('td[data-ir]');
  if(!td || !IMP || td.querySelector('input,select')) return;
  const r = Number(td.dataset.ir), c = Number(td.dataset.ic);
  openEditor(td, c, IMP.rows[r][c], v => impSet(r, c, v), impRender);
});

async function impCommit(){
  const j = IMP.info, replace = IMP.replace;
  if(!confirm('เขียน ' + j.total + ' แถวของวันที่ ' + dmy(j.date) + ' ลง' + j.target +
              (replace ? ' และลบงานเดิมของวันนั้นก่อน' : '') + ' — ยืนยัน?')) return;
  const btn = document.getElementById('impGo'); btn.disabled = true; btn.textContent = 'กำลังเขียนลงชีต...';
  try{
    const r = await impSend({rows: IMP.rows, commit: true, replace: replace});
    if(!r) return;
    impBody('<div class="box ok">✓ เขียนแล้ว ' + r.written + ' แถว (แถวที่ ' + r.first_row + '–' + r.last_row + ' ในชีต)' +
      (r.removed ? ' · ลบงานเดิม ' + r.removed + ' แถว' : '') +
      (r.kept_formula_cols && r.kept_formula_cols.length ? ' · ช่องที่เป็นสูตรในคอลัมน์ ' + r.kept_formula_cols.join(', ') + ' ระบบไม่ได้เขียนทับ ให้ชีตคำนวณเอง' : '') + '</div>' +
      '<p class="mut">ปิดหน้าต่างนี้เพื่อดูผลในหน้าแผนงาน (เปลี่ยนไปวันที่ ' + dmy(r.date) + ' ให้แล้ว)</p>');
    document.getElementById('date').value = r.date; load(true);
  }catch(e){ impBody('<div class="box bad">เขียนไม่สำเร็จ: ' + esc(e.message) + '</div>'); }
}

document.getElementById('impOpen').onclick = () => { document.getElementById('impBack').hidden = false; };
document.getElementById('impClose').onclick = () => { document.getElementById('impBack').hidden = true; };
document.getElementById('impFile').onchange = e => { IMPFILE = e.target.files[0] || null; if(IMPFILE) impPreview(); };

buildChips();
load();
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
  .c[data-f]{cursor:pointer;transition:border-color .15s,transform .1s}
  .c[data-f]:hover{border-color:#2563eb}
  .c[data-f]:active{transform:scale(.98)}
  .c[data-f].on{border-color:#2563eb;border-width:2px;box-shadow:0 0 0 1px #2563eb inset}
  .wrap{background:var(--card);border:1px solid var(--line);border-radius:13px;
        overflow:auto;height:calc(100vh - 280px)}
  table{border-collapse:separate;border-spacing:0;width:100%;min-width:1010px}
  th,td{padding:3px 6px;text-align:left;border-bottom:1px solid var(--line);white-space:nowrap;font-size:12.5px}
  th{font-size:12.5px;color:var(--mut);font-weight:600;text-transform:uppercase;
     letter-spacing:.4px;background:var(--card);position:sticky;top:0;z-index:2}
  /* กดหัวคอลัมน์เพื่อเรียง — กดซ้ำสลับ น้อย→มาก / มาก→น้อย / กลับเป็นลำดับไฟล์ต้นทาง */
  th[data-col]{cursor:pointer;user-select:none;white-space:nowrap}
  th[data-col]:hover{color:var(--tr)}
  th[data-col] .ar{opacity:.3;font-size:9px;margin-left:3px}
  th[data-col].sorted{color:var(--tr)}
  th[data-col].sorted .ar{opacity:1}
  tbody tr:hover{background:var(--pd-bg)}
  /* บีบให้ทุกแถวสูงบรรทัดเดียว อ่านง่ายขึ้นมาก */
  td.wide{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:170px}
  /* ตำแหน่งปัจจุบันเป็นชื่อสถานที่ยาว (ถนน/ตำบล/อำเภอ/จังหวัด) 170px สั้นไปมาก
     ให้กว้างขึ้นและตัดขึ้นบรรทัดที่ 2 ได้ อ่านออกโดยไม่ต้องเอาเมาส์ไปชี้ */
  td.loc{max-width:360px;min-width:240px;white-space:normal;word-break:break-word;
         line-height:1.25;overflow:hidden}
  .routebtn{display:inline-block;margin-left:6px;padding:1px 7px;border-radius:999px;
     border:1px solid var(--tr);color:var(--tr);text-decoration:none;
     font-size:11px;white-space:nowrap}
  .routebtn:hover{background:var(--tr);color:#fff}
  /* พิกัดเก่าเกินกำหนด — บอกให้รู้ว่าตำแหน่งนี้ไม่ใช่ตอนนี้ */
  .stale{display:inline-block;margin-left:6px;padding:1px 7px;border-radius:999px;
     background:var(--late-bg);color:var(--late);font-size:11px;font-weight:600;white-space:nowrap}
  .tms{display:inline-block;margin-left:6px;padding:0 6px;border-radius:999px;
     border:1px solid var(--line);color:var(--mut);font-size:10.5px;font-weight:600;vertical-align:1px}
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
  .linkbtn{background:none;border:0;padding:0;font:inherit;color:var(--tr);
     cursor:pointer;text-decoration:underline}
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
  /* บรรทัดอธิบายว่าทำไม ETA ถึงออกมาแบบนั้น -- โชว์เฉพาะแถวที่ช้า/ผิดปกติ
     แถวปกติไม่โชว์ เพื่อไม่ให้ตารางรก (เอาเมาส์ชี้ที่ช่อง ETA ก็เห็นได้) */
  .why{margin-top:5px;font-size:12px;line-height:1.45;color:var(--mut);white-space:normal;max-width:360px}
  /* วันที่ต่อท้าย ETA ที่ข้ามไปวันอื่น เช่น ~01:38 (13/09) */
  .etaday{color:var(--mut);font-size:12px;margin-left:3px}
  /* เมนูหลักด้านซ้าย — จอเล็กย้ายขึ้นเป็นแถบแนวนอนด้านบน */
  body{padding-left:148px}
  .side{position:fixed;left:0;top:0;bottom:0;width:148px;background:var(--card);
        border-right:1px solid var(--line);padding:14px 10px;display:flex;flex-direction:column;
        gap:6px;z-index:20}
  .side .menu{display:flex;align-items:center;gap:9px;text-decoration:none;font-weight:700;
              font-size:15px;color:var(--ink);padding:11px 12px;border-radius:10px}
  .side .menu:hover{background:var(--tr-bg)}
  .side .menu.on{background:#2563eb;color:#fff}
  @media (max-width:820px){
    body{padding-left:0}
    .side{position:static;width:auto;flex-direction:row;border-right:0;
          border-bottom:1px solid var(--line);padding:8px 10px}
    .side .menu{flex:1;justify-content:center;padding:9px 8px}
  }
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
    td.wide,td.cust,td.loc{max-width:none;min-width:0}
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
<aside class="side">
  <a class="menu on" href="/">🚛 เช็กรถ</a>
  <a class="menu" href="/plan">📋 แผนงาน</a>
</aside>
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
      <thead><tr id="headRow">
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
// ซ่อนคันที่ปิดงานแล้วเป็นค่าเริ่มต้น — จำค่าที่เลือกไว้ในเครื่อง
let SHOW_DONE = localStorage.getItem('gb_show_done') === '1';
if(('__NOPASS__') === '1') document.getElementById('nopass').hidden = false;

function thaiNow(){                    // เวลาไทย (UTC+7) — อ่านค่าด้วย getUTC* เท่านั้น
  return new Date(Date.now() + 7*3600*1000);
}

function todayISO(){
  return thaiNow().toISOString().slice(0,10);
}

function card(n, label, cls, f){
  const on = (f && FILTER === f) ? ' on' : '';
  const attr = f ? ' data-f="'+f+'" title="คลิกเพื่อกรองตาราง"' : '';
  return '<div class="c '+(cls||'')+on+'"'+attr+'><b>'+n+'</b><span>'+label+'</span></div>';
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

// รายการสถานะให้เลือก — ต้องตรงกับ dropdown คอลัมน์ L ในชีตทุกตัวอักษรและเรียงลำดับเดียวกัน
// ถ้าสะกดไม่ตรง ค่าที่เขียนกลับไปจะไม่ตรงกับ data validation ของชีต แล้วขึ้นเตือนสีแดง
const STATUS_LIST = [
  'จอดที่ฟรีต', 'กำลังโหลด', 'กำลังเดินทาง', 'ถึงปลายทาง',
  'จัดส่งดรอป 1', 'จัดส่งดรอป 2', 'โหลดเก็บ', 'ยกเลิกออเดอร์',
  'รอรถเที่ยว 1', 'จบงาน', 'กำลังไปโหลดแก๊ส',
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

// ETA ที่เลยเที่ยงคืนไปแล้วต้องบอกวันที่กำกับด้วย ไม่งั้นเห็น "01:38" เฉยๆ
// จะนึกว่าตี 1 ของวันนี้ซึ่งผ่านไปแล้ว ทั้งที่หมายถึงตี 1 ของคืนนี้
//
// ฝั่ง Python คำนวณด้วยวันที่+เวลาเต็มอยู่แล้ว แต่ส่งมาให้แค่ "HH:MM"
// (eta_time) จึงคำนวณย้อนกลับว่าข้ามไปกี่วัน จาก (เวลานัด + ต่าง − ETA) ÷ 1440
// เช่น นัด 21:00 (1260) + ช้า 278 น. − ETA 01:38 (98) = 1440 → ข้ามไป 1 วัน
function etaDayShift(t){
  const s = mins(t.sched_time), e = mins(t.eta_time);
  if(s == null || e == null || t.diff_minutes == null) return 0;
  return Math.round((s + t.diff_minutes - e) / 1440);
}

function etaDayLabel(t){                 // 1 → " (13/09)"   0 → ""
  const shift = etaDayShift(t);
  if(!shift) return '';
  const d = new Date(String(t.date || '') + 'T00:00:00');
  if(isNaN(d.getTime())) return '';
  d.setDate(d.getDate() + shift);
  const dd = ('0' + d.getDate()).slice(-2), mm = ('0' + (d.getMonth() + 1)).slice(-2);
  return '<span class="etaday">(' + dd + '/' + mm + ')</span>';
}

function eta(t){                      // ถึงจริงแล้วโชว์เวลาจริง ไม่งั้นโชว์ประมาณการ
  if(t.arrive_time) return '<b style="color:var(--ok)">'+esc(t.arrive_time)+'</b>'
    + (t.tms_filled ? '<span class="tms" title="เวลาถึงจริงจาก TMS (ชีตยังไม่ได้กรอก)">TMS</span>' : '');
  if(t.eta_time)    return '~'+esc(t.eta_time)+etaDayLabel(t);
  return '<span class="mut">—</span>';
}

// คำอธิบายเหตุผลของ ETA/สถานะ (ตัวแปร prediction ฝั่ง Python)
// เดิมค่านี้ส่งมาถึงเบราว์เซอร์อยู่แล้วแต่ไม่เคยถูกแสดง ใช้แค่เช็ค 📞 อย่างเดียว
// ทำให้เวลา ETA ออกมาแปลกๆ ไม่มีทางรู้เลยว่าเวลาไปโผล่ตรงไหน
// โชว์เป็นบรรทัดเล็กเฉพาะแถวที่ช้า/ยังไม่ออกรถ/มีคำเตือน ส่วนแถวปกติดูได้จาก
// tooltip ที่ช่อง ETA แทน
function why(t){
  const p = String(t.prediction || '').trim();
  if(!p) return '';
  const odd = t.status === 'late' || t.status === 'pending' || /^[⚠📞]/.test(p) || t.gps_stale;
  return odd ? '<div class="why">' + esc(p) + '</div>' : '';
}

// คอลัมน์ "ต่าง" -- เดิมใช้เครื่องหมาย + / - ซึ่งอ่านแล้วต้องแปลในหัวอีกที
// ว่าบวกคือช้าหรือเร็ว แถมเครื่องหมาย - ยังไปคล้ายกับ ~ ที่นำหน้าเวลา ETA
// จนดูเหมือนเวลาติดลบ เลยเปลี่ยนมาบอกเป็นคำไปเลยว่า "ช้า"/"เร็ว"/"ตรงเวลา"
function diffText(t){
  const m = t.diff_minutes;
  if(m == null) return '<span class="mut">—</span>';
  if(m > 0)     return '<span style="color:var(--late)">ช้า ' + dur(m) + '</span>';
  if(m < 0)     return '<span style="color:var(--ok)">เร็ว ' + dur(-m) + '</span>';
  return '<span style="color:var(--ok)">ตรงเวลา</span>';
}

function loc(t){
  if(t.current_lat == null || t.current_lng == null) return '—';
  const url  = 'https://www.google.com/maps?q=' + t.current_lat + ',' + t.current_lng;
  const text = t.current_loc || (t.current_lat.toFixed(5) + ', ' + t.current_lng.toFixed(5));
  let out = '<a href="'+url+'" target="_blank" rel="noopener" style="color:var(--tr)">📍 '+esc(text)+'</a>';
  // พิกัดเก่าเกินกำหนด (สคริปต์/API ค้าง) — บอกเวลาล่าสุด ไม่ให้เข้าใจผิดว่าเป็นตำแหน่งตอนนี้
  if(t.gps_stale) out += '<span class="stale" title="เวลาของพิกัดนี้">⚠ GPS ล่าสุด '+esc(t.gps_time||'')+'</span>';
  // ปุ่มดูเส้นทาง: ตำแหน่งรถตอนนี้ → ปลายทาง เปิดใน Google Maps (มีเส้นทาง+ระยะเวลาจริง)
  // ต้องมีพิกัดปลายทางในชีต "ข้อมูลปลายทาง" ถึงจะขึ้นปุ่มนี้
  if(t.dest_lat != null && t.dest_lng != null){
    const dir = 'https://www.google.com/maps/dir/?api=1'
      + '&origin=' + t.current_lat + ',' + t.current_lng
      + '&destination=' + t.dest_lat + ',' + t.dest_lng
      + '&travelmode=driving';
    out += '<a class="routebtn" href="'+dir+'" target="_blank" rel="noopener"'
         + ' title="ดูเส้นทางจากตำแหน่งรถตอนนี้ไปปลายทาง">🗺️ เส้นทาง</a>';
  }
  return out;
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
      const isQuota = /429|quota/i.test(err.message || '');
      w.innerHTML = isQuota
        ? '⚠️ ระบบใช้งาน Google Sheet ถี่เกินไปชั่วคราว (Quota exceeded)<br>'
          + 'เก็บไว้ในเครื่องนี้ก่อน — เดี๋ยวลองบันทึกซ้ำให้เองใน 1-2 นาที ไม่ต้องทำอะไรเพิ่ม'
        : '⚠️ บันทึกลง Google Sheet ไม่ได้ (' + esc(err.message) + ')<br>'
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

// งานปิดแล้ว = ไม่ต้องไล่อีก ทั้งที่กด "จบงาน" เอง และที่ชีตขึ้นว่าส่งถึงแล้ว
function isDone(t){
  if(t.status === 'arrived') return true;                                  // ส่งแล้ว / จัดส่งสำเร็จ
  return !!(CHASED[key(t)] && CHASED[key(t)].status === 'จบงาน');          // กดจบงานเอง
}

// กรองที่เจาะจงสถานะเดียว (จากคลิกการ์ดสรุป) — ต้องเห็นครบตามจำนวนบนการ์ด
// จึงไม่เอาการ์ดปิดงานแล้ว (isDone) มาบังผลลัพธ์เหมือนมุมมองอื่น
const STATUS_FILTERS = {
  arrived:   t => t.status === 'arrived',
  transit:   t => t.status === 'transit' || t.status === 'early',
  pending:   t => t.status === 'pending',
  cancelled: t => t.status === 'cancelled',
};

function keep(t){                     // กรองตามชิป/การ์ดที่เลือก
  if(STATUS_FILTERS[FILTER]) return STATUS_FILTERS[FILTER](t);
  // คันที่ปิดงานแล้วเอาออกจากตารางทุกมุมมอง (กดปุ่มใต้ตารางเพื่อดูย้อนหลังได้)
  // เพราะเรียงตามไฟล์ต้นทาง คันที่ยังต้องไล่จะกระจายอยู่ทั่วตาราง ถ้าคันที่ปิดงาน
  // แล้วยังค้างอยู่ด้วยจะหาคันที่ต้องทำจริงยากมาก
  if(isDone(t) && !SHOW_DONE) return false;
  if(FILTER === 'all')    return true;
  if(FILTER === 'late')   return t.status === 'late';
  if(FILTER === 'active') return t.status !== 'arrived' && t.status !== 'cancelled';
  // 'hour' = ต้องจัดการในชั่วโมงนี้: ถึงเวลาโทรตาม / ช้าอยู่แล้ว / ครบกำหนดใน 60 นาที
  if(t.status === 'arrived' || t.status === 'cancelled') return false;
  if(String(t.prediction||'').startsWith('📞')) return true;
  if(t.status === 'late')    return true;
  const s = mins(t.sched_time);
  return s != null && s - nowMins() <= 60;
}

// ── กดหัวคอลัมน์เพื่อเรียงลำดับ ────────────────────────────────────────────
// ลำดับต้องตรงกับ <th> และ <td> ในตาราง (0-based)
// val = ค่าที่เอาไปเทียบ คืน number สำหรับคอลัมน์ตัวเลข/เวลา คืน string สำหรับข้อความ
const SORT_COLS = {
   0:{ val:t => t.date || ''                 },
   1:{ val:t => t.source || ''               },
   2:{ val:t => t.trip_no || ''              },
   3:{ val:t => t.drop || ''                 },
   4:{ val:t => t.customer || ''             },
   5:{ val:t => t.car_no || ''               },
   6:{ val:t => t.plate || ''                },
   7:{ val:t => num(t.volume)                },
   8:{ val:t => t.driver || ''               },
   9:{ val:t => mins(t.sched_time) ?? 1e9    },
  10:{ val:t => t.invoice_no || ''           },
  11:{ val:t => t.gps_status || ''           },
  12:{ val:t => mins(t.arrive_time || t.eta_time) ?? 1e9 },
  13:{ val:t => t.diff_minutes == null ? 1e9 : t.diff_minutes },
  14:{ val:t => t.ontime || ''               },
  15:{ val:t => LABEL[t.status] || t.status || '' },
  16:{ val:t => t.current_loc || ''          },
};
function num(v){                       // '22,000' -> 22000 ; ไม่ใช่ตัวเลขให้ไปท้ายสุด
  const n = parseFloat(String(v ?? '').replace(/[^\d.-]/g, ''));
  return isNaN(n) ? Infinity : n;
}
let SORT = { col:null, dir:1 };        // col=null คือเรียงตามลำดับไฟล์ต้นทาง

function buildHead(){
  const row = document.getElementById('headRow');
  if(!row) return;
  [...row.children].forEach((th, i) => {
    if(!SORT_COLS[i]) return;          // คอลัมน์อัปเดตสถานะ กดเรียงไม่ได้
    th.setAttribute('data-col', i);
    const on  = SORT.col === i;
    th.className = on ? 'sorted' : '';
    const base = th.getAttribute('data-label') || th.textContent.replace(/[▲▼↕]/g,'').trim();
    th.setAttribute('data-label', base);
    th.innerHTML = esc(base) + '<span class="ar">' + (on ? (SORT.dir>0?'▲':'▼') : '↕') + '</span>';
    th.onclick = () => {
      // กดคอลัมน์เดิมซ้ำ: น้อย→มาก → มาก→น้อย → กลับเป็นลำดับไฟล์ต้นทาง
      if(SORT.col !== i)        SORT = { col:i, dir:1 };
      else if(SORT.dir === 1)   SORT = { col:i, dir:-1 };
      else                      SORT = { col:null, dir:1 };
      render();
    };
  });
}

function render(){
  const q = document.getElementById('q').value.trim().toLowerCase();
  DATA = ALL.filter(keep);
  const list = (!q ? DATA : DATA.filter(t =>
    [t.car_no, t.plate, t.customer, t.source, t.invoice_no]
      .some(v => String(v||'').toLowerCase().includes(q))))
    .slice();

  const sc = SORT.col != null ? SORT_COLS[SORT.col] : null;
  if(sc){
    list.sort((a,b) => {
      const x = sc.val(a), y = sc.val(b);
      const c = (typeof x === 'number' && typeof y === 'number')
        ? x - y
        : String(x).localeCompare(String(y), 'th', {numeric:true});
      return (c || (a.id||0) - (b.id||0)) * SORT.dir;   // ค่าเท่ากันให้ยึดลำดับไฟล์ต้นทาง
    });
  }else{
    // ค่าเริ่มต้น: เรียงตามลำดับเดิมในไฟล์ต้นทาง (t.id = ลำดับแถวที่อ่านมาจากแผนงาน)
    list.sort((a,b) => (a.id||0) - (b.id||0));
  }
  buildHead();

  document.getElementById('rows').innerHTML = list.length ? list.map(t => {
    const k    = key(t);
    const call = String(t.prediction||'').startsWith('📞');
    const diff = diffText(t);
    const badge = '<span class="badge s-'+esc(t.status)+'">'
                + (LABEL[t.status]||esc(t.status))+'</span>'
                + (call ? '<span class="callnow">📞 ยังไม่ออกคลัง · โทรตาม</span>' : '');
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
      + '<td data-l="ETA / ถึงจริง" class="mono" title="'+esc(t.prediction||'')+'">'+eta(t)+'</td>'
      + '<td data-l="ต่าง" class="mono">'+diff+'</td>'
      + '<td data-l="On Time (ชีต)">'+ot(t)+'</td>'
      + '<td data-l="สถานะ" class="st">'+badge+why(t)+'</td>'
      + '<td data-l="ตำแหน่งปัจจุบัน" class="loc">'+loc(t)+'</td>'
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

  const doneCount = ALL.filter(isDone).length;
  const foot = document.getElementById('foot');
  foot.innerHTML = 'แสดง ' + list.length + ' ทริป (จากทั้งวัน ' + ALL.length + ' ทริป)'
    + (doneCount
        ? ' · <button type="button" id="toggleDone" class="linkbtn">'
          + (SHOW_DONE ? 'ซ่อนคันที่ปิดงานแล้ว (' + doneCount + ')'
                       : 'ปิดงานแล้ว ' + doneCount + ' คัน — แสดง')
          + '</button>'
        : '');
  const td = document.getElementById('toggleDone');
  if(td) td.onclick = () => {
    SHOW_DONE = !SHOW_DONE;
    localStorage.setItem('gb_show_done', SHOW_DONE ? '1' : '0');
    render();
  };
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
        card(j.total,'ทริปทั้งหมด','','all')
      + card(j.arrived,'ส่งเสร็จแล้ว','ok','arrived')
      + card(j.in_transit,'กำลังเดินทาง','tr','transit')
      + card(j.late,'คาดว่าจะช้า','late','late')
      + card(j.pending,'รอออกรถ','','pending')
      + card(j.cancelled || 0,'ยกเลิก/โหลดเก็บ','','cancelled');
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

function setFilter(f){                // ใช้ร่วมกันทั้งชิปด้านบนและการ์ดสรุปตัวเลข
  FILTER = f;
  document.querySelectorAll('.chip').forEach(x => x.classList.toggle('on', x.dataset.f === FILTER));
  document.querySelectorAll('.c[data-f]').forEach(x => x.classList.toggle('on', x.dataset.f === FILTER));
  render();
}

document.querySelectorAll('.chip').forEach(b => {
  b.classList.toggle('on', b.dataset.f === FILTER);
  b.onclick = () => setFilter(b.dataset.f);
});

// คลิกการ์ดสรุปตัวเลขด้านบน (ทั้งหมด/ส่งเสร็จแล้ว/กำลังเดินทาง/ช้า/รอออกรถ/ยกเลิก) → กรองตารางทันที
document.addEventListener('click', e => {
  const c = e.target.closest('.c[data-f]');
  if(c && c.dataset.f) setFilter(c.dataset.f);
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
