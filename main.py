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
PLAN_TYPE    = 103 # CZ TYPE (Station / Industry / โรงบรรจุ / Tranfer)
PLAN_WHY     = 96  # CS สาเหตุ On Time (เช่น ฝนตก, จราจรติดขัด, ระบบคลังล่ม)
PLAN_FIXWHY  = 101 # CX สาเหตุแก้ไขงาน (เช่น ลูกค้ายกเลิก, ปลายทางใหม่, คู่พ่วงใหม่)
PLAN_JOBTYPE = 105 # DB ประเภทงาน (เช่น "OLP : Station", "ลูกค้า : Industry", "ATL : โรงบรรจุ")

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


# ผู้ใช้แต่ละคนอยู่ในแท็บ "User" ของไฟล์ ChaseLog (PLAN_ID) — อ่านอย่างเดียว ไม่เขียนกลับ
# หัวตาราง: ชื่อผู้ใช้ | รหัสผ่าน | เช็กรถ | แผนงาน | รายงาน | ใช้งาน   (ติ๊ก = เปิดหน้านั้นได้)
# รหัสกลาง APP_PASSWORD ยังเข้าได้ทุกหน้าเสมอ (กันล็อกตัวเองออกถ้าชีตมีปัญหา)
USERS_TAB  = os.environ.get("USERS_TAB", "User")
USERS_TTL  = 60                                      # อ่านชีตผู้ใช้ใหม่ทุก 1 นาที (ปิดบัญชีแล้วมีผลเร็ว)
PERMS_ALL  = frozenset({"car", "plan", "report"})
PERM_PAGES = [("car", "/"), ("plan", "/plan"), ("report", "/report")]
_TRUE_MARKS = {"✓", "✔", "☑", "true", "yes", "y", "1", "x", "ใช่", "/"}
_users_cache: dict = {"ts": 0.0, "data": None}


def _users_sheet_id() -> str:
    return os.environ.get("USERS_SHEET_ID") or PLAN_ID


def _load_users_rows() -> list:
    gc = gspread.authorize(_build_creds())
    return gc.open_by_key(_users_sheet_id()).worksheet(USERS_TAB).get_all_values()


def _parse_users(rows: list) -> dict:
    """แถวจากชีต → {ชื่อผู้ใช้ (ตัวเล็ก): {"pw": รหัส, "perms": {...}}} — ข้ามคนที่ไม่ได้ติ๊ก "ใช้งาน" หรือไม่ได้ติ๊กหน้าไหนเลย"""
    hdr = next((n for n, r in enumerate(rows[:10]) if any("ชื่อผู้ใช้" in c or c.strip().lower() in ("user", "username") for c in r)), None)
    if hdr is None:
        return {}
    h = [c.strip().lower() for c in rows[hdr]]
    find = lambda *keys: next((n for n, c in enumerate(h) if any(k in c for k in keys)), None)
    cu, cp, ca = find("ชื่อผู้ใช้", "user"), find("รหัส", "pass"), find("ใช้งาน", "active")
    cols = {"car": find("เช็กรถ", "เช็ครถ"), "plan": find("แผนงาน"), "report": find("รายงาน")}
    if cu is None or cp is None:
        return {}
    out = {}
    for r in rows[hdr + 1:]:
        cell = lambda n: r[n].strip() if n is not None and n < len(r) else ""
        on = lambda n: cell(n).lower() in _TRUE_MARKS
        user, pw = cell(cu).lower(), cell(cp)
        if not user or not pw or (ca is not None and not on(ca)):
            continue
        perms = frozenset(k for k, n in cols.items() if on(n))
        if perms:
            out[user] = {"pw": pw, "perms": perms}
    return out


def _users() -> dict:
    """ผู้ใช้จากชีต (แคช 1 นาที) — อ่านไม่ได้ใช้ของเดิม ถ้าไม่เคยอ่านได้เลย = ไม่มีผู้ใช้"""
    now = time()
    if _users_cache["data"] is not None and now - _users_cache["ts"] < USERS_TTL:
        return _users_cache["data"]
    try:
        data = _parse_users(_with_retry(_load_users_rows))
    except Exception:
        return _users_cache["data"] or {}
    _users_cache.update(ts=now, data=data)
    return data


def _need_perm(path: str) -> str:
    """หน้า/API นี้ต้องมีสิทธิ์อะไร: car / plan / report / "" (ทุกคน) / admin (ต้องมีครบทุกหน้า)"""
    if path in ("/logout", "/favicon.ico"):
        return ""
    if path == "/" or path in ("/api/trips", "/api/chase", "/api/timeline", "/api/match"):
        return "car"
    if path in ("/plan", "/api/plan") or path.startswith("/api/plan/"):
        return "plan"
    if path == "/report" or path.startswith("/api/report/"):
        return "report"
    return "admin"                                   # ตั้งค่า / debug / docs ฯลฯ


def _home_for(perms) -> str:
    return next((url for k, url in PERM_PAGES if k in perms), "/logout")


CRON_SECRET = os.environ.get("CRON_SECRET", "")   # ตั้งที่ Vercel — ใช้กันคนนอกยิง /api/cron/hourly-status เล่น


def _secret() -> bytes:
    """คีย์สำหรับเซ็น token — ตั้ง SESSION_SECRET เองได้ ไม่ตั้งก็ใช้รหัสผ่านแทน"""
    return (os.environ.get("SESSION_SECRET") or _app_password() or "dev").encode()


def _sign(msg: str) -> str:
    sig = hmac.new(_secret(), msg.encode(), hashlib.sha256).digest()
    return base64.urlsafe_b64encode(sig).decode().rstrip("=")


def _make_token(user: str = "") -> str:
    """token = "หมดอายุ.ลายเซ็น" (รหัสกลาง เข้าได้ทุกหน้า) หรือ "หมดอายุ.u.ชื่อผู้ใช้.ลายเซ็น" (ผู้ใช้จากชีต)
    ชื่อผู้ใช้อยู่ในลายเซ็น แก้เองไม่ได้ · สิทธิ์ดูจากชีตทุกครั้ง (ปิดในชีต = หลุดภายใน 1 นาที)"""
    exp = str(int(time()) + SESSION_HOURS * 3600)
    if user:
        u = base64.urlsafe_b64encode(user.encode()).decode().rstrip("=")
        return exp + ".u." + u + "." + _sign(exp + "|u|" + user)
    return exp + "." + _sign(exp)


def _token_user(token: str) -> Optional[str]:
    """"" = รหัสกลาง (ทุกหน้า) · "ชื่อ" = ผู้ใช้จากชีต · None = ไม่ผ่าน/หมดอายุ"""
    try:
        parts = (token or "").split(".")
        if len(parts) == 2:
            exp, sig = parts
            user, msg = "", exp
        elif len(parts) == 4 and parts[1] == "u":
            exp, _, u, sig = parts
            user = base64.urlsafe_b64decode(u + "=" * (-len(u) % 4)).decode()
            if not user:
                return None
            msg = exp + "|u|" + user
        else:
            return None
        if int(exp) < int(time()):
            return None
        return user if hmac.compare_digest(sig, _sign(msg)) else None
    except (ValueError, AttributeError, UnicodeDecodeError):
        return None


def _token_ok(token: str) -> bool:
    return _token_user(token) == ""


def _perms_of(token: str):
    """สิทธิ์ของ cookie นี้ — None = ยังไม่ได้ล็อกอิน / บัญชีถูกปิด"""
    user = _token_user(token)
    if user == "":
        return PERMS_ALL
    if user:
        u = _users().get(user)
        return u["perms"] if u else None
    return None


def _nav(html: str, request: Request) -> str:
    """ซ่อนเมนูหน้าที่ผู้ใช้ไม่มีสิทธิ์"""
    perms = getattr(request.state, "perms", PERMS_ALL)
    for k, url in PERM_PAGES + [("admin", "/settings")]:
        if (k == "admin" and not perms >= PERMS_ALL) or (k != "admin" and k not in perms):
            html = re.sub(r'<a\b[^>]*\bhref="' + re.escape(url) + r'"[^>]*>.*?</a>\s*', "", html)
    return html

# ─── APP ─────────────────────────────────────────────────────────────────────

app = FastAPI(
    title="Gasbulk Track API",
    description="ติดตามรถ Gasbulk — รู้ล่วงหน้าว่าจะถึงช้าหรือเร็ว",
    version="3.0.0",
)

OPEN_PATHS = {"/login", "/api/login", "/favicon.ico", "/api/cron/hourly-status"}

SECURITY_HEADERS = {
    "X-Content-Type-Options": "nosniff",                                   # ห้ามเบราว์เซอร์เดาชนิดไฟล์เอง
    "X-Frame-Options": "DENY",                                             # ห้ามเว็บอื่นเอาหน้านี้ไปครอบ (clickjacking)
    "Referrer-Policy": "same-origin",                                      # ไม่ส่งที่อยู่หน้าเราไปเว็บอื่น
    "Permissions-Policy": "camera=(), microphone=(), geolocation=(), payment=()",
    "Strict-Transport-Security": "max-age=31536000; includeSubDomains",    # บังคับ https
    "Content-Security-Policy": "frame-ancestors 'none'; base-uri 'self'; form-action 'self'; object-src 'none'",
}
SAFE_METHODS = {"GET", "HEAD", "OPTIONS"}


def _same_origin(request: Request) -> bool:
    """คำขอที่แก้ข้อมูล (POST ฯลฯ) ต้องมาจากหน้าเว็บของเราเอง — เบราว์เซอร์ใส่ Origin/Referer มาให้เสมอ
    ถ้าชี้ไปโดเมนอื่น = มีคนพยายามให้ผู้ใช้กดจากเว็บอื่น (CSRF) → ปฏิเสธ"""
    src = request.headers.get("origin") or request.headers.get("referer") or ""
    if not src:
        return True                                  # ไม่ใช่เบราว์เซอร์ (เช่น สคริปต์) — ยังต้องผ่านด่านล็อกอินอยู่ดี
    host = (request.headers.get("host") or "").lower()
    try:
        from urllib.parse import urlsplit
        return urlsplit(src).netloc.lower() == host
    except Exception:
        return False




@app.middleware("http")
async def require_login(request: Request, call_next):
    """กันไม่ให้คนที่ไม่ได้ล็อกอินเข้าถึงข้อมูล"""
    path = request.url.path
    if not _app_password() or path in OPEN_PATHS:
        return await call_next(request)          # ยังไม่ตั้งรหัส → เปิดตามเดิม

    perms = _perms_of(request.cookies.get(COOKIE_NAME, ""))
    if perms is not None:
        request.state.perms = perms
        need = _need_perm(path)
        if not need or need in perms or (need == "admin" and perms >= PERMS_ALL):
            return await call_next(request)
        if path.startswith("/api/"):
            return JSONResponse({"detail": "บัญชีนี้ไม่มีสิทธิ์ดูส่วนนี้"}, status_code=403)
        return RedirectResponse(_home_for(perms), status_code=303)

    if path.startswith("/api/"):
        return JSONResponse({"detail": "ต้องล็อกอินก่อน"}, status_code=401)
    return RedirectResponse("/login", status_code=303)


@app.middleware("http")
async def security_layer(request: Request, call_next):
    if request.method not in SAFE_METHODS and not _same_origin(request):
        resp = JSONResponse({"detail": "คำขอไม่ได้มาจากหน้าเว็บนี้"}, status_code=403)
    else:
        resp = await call_next(request)
    for k, v in SECURITY_HEADERS.items():
        resp.headers.setdefault(k, v)
    path = request.url.path
    if path.startswith("/api/") or path in ("/", "/plan", "/settings", "/login"):
        resp.headers["Cache-Control"] = "no-store"   # เครื่องกลางที่หลายคนใช้ — กันเบราว์เซอร์/พร็อกซีเก็บข้อมูลไว้
    return resp

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
def dashboard(request: Request):
    warn = "" if _app_password() else "1"
    return _nav(DASHBOARD_HTML.replace("__NOPASS__", warn), request)


PLAN_LAST_COL = 26   # แสดงคอลัมน์ A–Z ของชีตแผนงาน
PLAN_FRESH_MIN_SECS = 15   # ปุ่มรีเฟรชอ่านชีตสดได้ไม่ถี่กว่านี้ (วินาที)
# ชีตที่หน้าแผนงาน (/plan) อ่าน — แยกจาก SOURCE_ID ที่หน้าเช็กรถใช้ จะได้ทดลองกับชีต DEMO ได้
# โดยไม่กระทบหน้าเช็กรถ ตั้ง PLAN_PAGE_ID / PLAN_PAGE_TAB ที่ Vercel (ไม่ตั้ง = ใช้ชีตเดิม)
PLAN_PAGE_ID  = os.environ.get("PLAN_PAGE_ID")  or SOURCE_ID
# ชีต "ข้อมูลรถ+พขร (แก๊สบัลค์)" — ใช้ "อ่านอย่างเดียว" เพื่อเติมข้อมูลรถ/พขร. อัตโนมัติ (ไม่ตั้ง = ไม่อ่าน)
# ใส่ลิงก์เต็มหรือเฉพาะ id ก็ได้; ต้องแชร์ชีตให้บัญชีของเว็บแบบ "ผู้ดู (Viewer)" ชีตนี้ห้ามมีโค้ดส่วนไหนเขียน
_m_cars = re.search(r"/d/([A-Za-z0-9_-]{20,})", os.environ.get("CARS_SHEET_ID", ""))
CARS_SHEET_ID = _m_cars.group(1) if _m_cars else os.environ.get("CARS_SHEET_ID", "").strip().strip("\"'").strip()
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
    tabs = {}                                  # ข้อมูลรถ/พขร. ที่อยู่ในไฟล์เดียวกัน (เก็บไว้เติมอัตโนมัติ) อ่านไม่ได้ = ข้ามไป ไม่กระทบการนำเข้า
    for name in ("ข้อมูลรถ", "พขร.ประจำรถ", "ข้อมูลพขร."):
        try:
            if name in wb.sheetnames:
                tabs[name] = [[_xl_cell(v, -1) for v in r] for r in wb[name].iter_rows(values_only=True, max_row=3000)]
        except Exception:
            pass
    try:
        master = _build_cars(tabs)
    except Exception:
        master = {}
    return {"headers": headers, "rows": rows, "notes": notes, "master": master}


def _review_rows(rows: list, notes=None, skip_load: bool = False) -> dict:
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
        if not out[24] and not skip_load:
            flag(24, "ยังไม่ใส่เวลาเข้าโหลด (P) — เวลาออกจากฟรีต/เวลาโทรตาม พขร จะว่างด้วย", listed=False)
    no_load = 0 if skip_load else sum(1 for r in rows if not r[24])
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
    if PLAN_PAGE_ID in (SOURCE_ID, PLAN_ID) or (CARS_SHEET_ID and PLAN_PAGE_ID == CARS_SHEET_ID):
        return "ชีตปลายทางเป็นชีตจริง — ระบบยอมเขียนเฉพาะชีตทดลอง ตั้ง PLAN_PAGE_ID เป็นชีต DEMO ก่อน"
    return ""


def _import_block_reason() -> str:
    return _write_block_reason("PLAN_IMPORT_ENABLED")


_gs_cache: dict = {}                       # {"gc": client, "ws": {(id, แท็บ): (เวลา, ws, sh)}, "log": {id: ws}}
_GS_TTL = 600


def _gc():
    """gspread client ตัวเดียวใช้ซ้ำ (เดิมสร้างใหม่ทุกคำขอ = ขอ token ใหม่ทุกครั้ง)"""
    if "gc" not in _gs_cache:
        _gs_cache["gc"] = gspread.authorize(_build_creds())
    return _gs_cache["gc"]


def _plan_ws(force: bool = False):
    """(ws, sh) ของแท็บแผนงานในไฟล์ PLAN_PAGE_ID — เก็บไว้ 10 นาที ลดการเรียก Google ที่ต้องเปิดไฟล์/แท็บซ้ำ"""
    key = (PLAN_PAGE_ID, PLAN_PAGE_TAB)
    hit = _gs_cache.setdefault("ws", {}).get(key)
    if hit and not force and time() - hit[0] < _GS_TTL:
        return hit[1], hit[2]
    sh = _gc().open_by_key(PLAN_PAGE_ID)
    ws = sh.worksheet(PLAN_PAGE_TAB)
    _gs_cache["ws"][key] = (time(), ws, sh)
    return ws, sh


def _gs_forget() -> None:
    """ล้างตัวที่เก็บไว้ (เมื่อมี error เช่นแท็บถูกเปลี่ยนชื่อ/ลบ แล้วเปิดใหม่ในรอบถัดไป)"""
    _gs_cache.pop("ws", None)
    _gs_cache.pop("log", None)


def _editlog_ws(sh):
    """แท็บ EditLog (สร้างให้ถ้ายังไม่มี) เก็บไว้ใช้ซ้ำ เพื่อเขียนประวัติด้วยคำสั่งเดียว"""
    lg = _gs_cache.setdefault("log", {}).get(PLAN_PAGE_ID)
    if lg is None:
        try:
            lg = sh.worksheet(EDIT_LOG_TAB)
        except gspread.WorksheetNotFound:
            lg = sh.add_worksheet(EDIT_LOG_TAB, rows=2000, cols=8)
            lg.append_row(["เวลา", "ผู้แก้", "แถว", "คอลัมน์", "ค่าเดิม", "ค่าใหม่", "JOB|Drop", "หมายเหตุ"])
        _gs_cache["log"][PLAN_PAGE_ID] = lg
    return lg


def _pad_row(vals) -> list:
    row = [("" if v is None else str(v)) for v in (list(vals[0]) if vals else [])]
    return (row + [""] * PLAN_LAST_COL)[:PLAN_LAST_COL]


def _cached_head() -> int:
    """แถวหัวตาราง (นับจาก 0) จากข้อมูลแผนงานที่แคชไว้แล้ว ไม่ต้องอ่านทั้งคอลัมน์ C ใหม่"""
    hit = _sheet_cache.get(f"{PLAN_PAGE_ID}:{PLAN_PAGE_TAB}")
    try:
        return _plan_header_row(hit[1]) if hit else 2
    except Exception:
        return 2


def _head_index(col_c: list) -> int:
    """แถวหัวตาราง (นับจาก 0) จากคอลัมน์ C — ไม่เจอใช้แถวที่ 3 ตามชีตจริง"""
    return next((i for i, v in enumerate(col_c[:6]) if "วันที่" in v and not _parse_date(v)), 2)


def _array_cols_from(top) -> set:
    out: set = set()
    for row in top or []:
        for c, v in enumerate(list(row)[:PLAN_LAST_COL]):
            u = str(v).upper()
            if u.startswith("=") and "ARRAYFORMULA(" in u:
                out.add(c)
    return out


def _array_cols(ws, head: int) -> set:
    """คอลัมน์ A–Z ที่ชีตเติมลงมาด้วยสูตรอาร์เรย์ (ARRAYFORMULA) จากแถวบน — ช่องล่างๆ ดูเหมือนว่างเปล่า
    แต่เขียนทับแล้วสูตรอาร์เรย์พัง (#REF!) จึงห้ามเขียนทั้งคอลัมน์"""
    try:
        top = ws.get(f"A1:Z{head + 4}", value_render_option=gspread.utils.ValueRenderOption.formula)
    except Exception:
        return set()
    return _array_cols_from(top)


def _row_is_dark(ws, row: int):
    """แถวนี้พื้นหลังสีเข้ม (แถวสีดำคั่นระหว่างวัน) ไหม — อ่านสีพื้นของช่อง A–Z; อ่านไม่ได้ = None"""
    try:
        meta = ws.spreadsheet.fetch_sheet_metadata(params={
            "ranges": [f"'{ws.title}'!A{row}:Z{row}"], "includeGridData": "true",
            "fields": "sheets.data.rowData.values.effectiveFormat.backgroundColor"})
        vals = meta["sheets"][0]["data"][0]["rowData"][0]["values"]
        lums = []
        for v in vals:
            bg = (v.get("effectiveFormat") or {}).get("backgroundColor")
            lums.append(1.0 if not bg else (bg.get("red", 0) + bg.get("green", 0) + bg.get("blue", 0)) / 3)
        lums.sort()
        return bool(lums) and lums[len(lums) // 2] < 0.35        # ช่องส่วนใหญ่ในแถวเป็นสีเข้ม
    except Exception:
        return None


def _insert_blank_rows(ws, row: int, n: int) -> None:
    """แทรกแถวว่าง n แถวที่ตำแหน่ง row โดยสั่ง insertDimension ตรงๆ (inheritFromBefore = รับรูปแบบจากแถวบน)
    ไม่ใช้ Worksheet.insert_rows เพราะมันตามด้วย values.append ซึ่งตำแหน่งที่ Google ลงขึ้นกับการค้นหา "ตาราง" เดาไม่ได้"""
    ws.spreadsheet.batch_update({"requests": [{"insertDimension": {
        "range": {"sheetId": ws.id, "dimension": "ROWS", "startIndex": row - 1, "endIndex": row - 1 + n},
        "inheritFromBefore": True}}]})
    try:                                                      # ให้ ws.row_count ตรงกับของจริงหลังแทรก
        ws._properties["gridProperties"]["rowCount"] += n
    except Exception:
        pass


def _copy_down(ws, src_row: int, first: int, last: int) -> None:
    """แถวที่แทรกใหม่ (first..last) คัดลอกสูตรของคอลัมน์ที่เป็นสูตรในแถวต้นแบบ (src_row) และดรอปลิสต์ทั้งแถว
    ทำเต็มที่ ถ้า Google ไม่ยอมก็ข้าม ไม่กระทบการเขียนค่า"""
    try:
        top = ws.get(f"A{src_row}:Z{src_row}", value_render_option=gspread.utils.ValueRenderOption.formula) or [[]]
        cols = [c for c, v in enumerate(list(top[0])[:PLAN_LAST_COL]) if str(v).startswith("=")]

        def rng(r0: int, r1: int, c0: int, c1: int) -> dict:
            return {"sheetId": ws.id, "startRowIndex": r0 - 1, "endRowIndex": r1,
                    "startColumnIndex": c0, "endColumnIndex": c1}
        reqs = [{"copyPaste": {"source": rng(src_row, src_row, c, c + 1), "destination": rng(first, last, c, c + 1),
                               "pasteType": "PASTE_FORMULA"}} for c in cols]
        reqs.append({"copyPaste": {"source": rng(src_row, src_row, 0, PLAN_LAST_COL),
                                   "destination": rng(first, last, 0, PLAN_LAST_COL), "pasteType": "PASTE_DATA_VALIDATION"}})
        ws.spreadsheet.batch_update({"requests": reqs})
    except Exception:
        pass


def _dup_key(r: list):
    """กุญแจบอกว่าเป็นงานเดียวกัน: เลขออเดอร์ + เลขโหลด + ต้นทาง + ปลายทาง + Drop ("ATL-" เฉยๆ = ไม่มีเลขออเดอร์; ไม่มีทั้งเลขออเดอร์และเลขโหลด = เทียบไม่ได้)"""
    h = str(r[7]).strip() if len(r) > 13 else ""
    i = str(r[8]).strip() if len(r) > 13 else ""
    if len(h) <= 4:
        h = ""
    if not h and not i:
        return None
    return (h, i, str(r[11]).strip(), str(r[12]).strip(), str(r[13]).strip())


def _dup_rows(rows: list, date_iso: str) -> list:
    """ลำดับแถว (นับจาก 0) ของชุดที่วาง ที่ซ้ำกับงานของวันเดียวกันที่มีในชีตอยู่แล้ว (อ่านจากแคชของแผนงาน)"""
    try:
        sheet = _fetch_sheet(PLAN_PAGE_ID, PLAN_PAGE_TAB)
    except Exception:
        return []
    have = set()
    for r in sheet:
        if _parse_date(_cell(r, PLAN_DATE)) == date_iso:
            k = _dup_key([_cell(r, c) for c in range(PLAN_LAST_COL)])
            if k:
                have.add(k)
    return [n for n, r in enumerate(rows) if (_dup_key(r) in have and _dup_key(r) is not None)]


def _triple(r: list):
    car, trip, drop = str(r[15]).strip(), str(r[4]).strip(), str(r[13]).strip() or "1"
    return (car, trip, drop) if car and trip else None


def _triple_conflicts(rows: list, date_iso: str) -> list:
    """[(ลำดับแถวที่วาง, ซ้ำกับอะไร)] — รถ+เที่ยว+Drop ซ้ำกับงานในชีตของวันนั้น หรือซ้ำกันเองในชุดที่วาง"""
    seen: dict = {}
    try:
        for i, r in enumerate(_fetch_sheet(PLAN_PAGE_ID, PLAN_PAGE_TAB), start=1):
            if _parse_date(_cell(r, PLAN_DATE)) == date_iso:
                t = _triple([_cell(r, c) for c in range(PLAN_LAST_COL)])
                if t:
                    seen.setdefault(t, f"แถวที่ {i} ในชีต")
    except Exception:
        pass
    out = []
    for n, r in enumerate(rows):
        t = _triple(r)
        if not t:
            continue
        if t in seen:
            out.append((n, seen[t]))
        else:
            seen[t] = f"แถวที่ {n + 1} ของชุดที่วาง"
    return out


def _write_near(ws, head: int, hit: list, sheet_rows: list) -> dict:
    """เพิ่มงานเข้าวันที่มีอยู่แล้ว โดยไม่ลบงานเดิม: งานของรถคันที่มีแถวอยู่ในวันนั้น แทรกต่อท้ายกลุ่มแถวของรถคันนั้น
    ส่วนงานที่ยังไม่มีเบอร์รถ/เป็นรถคันใหม่ ต่อท้ายวัน (ก่อนแถวสีดำคั่นวัน) — แทรกแถว+คัดลอกสูตร+เขียนค่า รวมเป็น 3 คำสั่งเรียก Google
    ช่องที่เป็นสูตร (หรือคอลัมน์ ARRAYFORMULA) ไม่เขียนทับ ส่ง None ให้ชีตข้ามช่องนั้น"""
    f, l = hit[0], hit[-1]
    if len(hit) != l - f + 1:
        raise HTTPException(status_code=409, detail=f"แถวของวันนี้ในชีตกระจายหลายช่วง (แถว {f}–{l} มีวันอื่นคั่น) "
                            "ระบบไม่แทรกให้เพราะอาจทับข้อมูลวันอื่น — แก้ในชีตให้เป็นช่วงเดียวก่อน")
    colp = ws.col_values(PLAN_CARNO + 1)
    last_of: dict = {}                                   # เบอร์รถ → แถวสุดท้ายของรถคันนั้นในวันนี้
    for r in range(f, l + 1):
        car = str(colp[r - 1]).strip() if r - 1 < len(colp) else ""
        if car:
            last_of[car] = r
    groups: dict = {}                                    # แทรกหลังแถวที่ … → ลำดับแถวใหม่ (คงลำดับที่วาง)
    near_n = 0
    for i, row in enumerate(sheet_rows):
        car = str(row[PLAN_CARNO]).strip()
        if car and car in last_of:
            groups.setdefault(last_of[car], []).append(i); near_n += 1
        else:
            groups.setdefault(l, []).append(i)
    order = sorted(groups)
    try:
        top = ws.get(f"A{l}:Z{l}", value_render_option=gspread.utils.ValueRenderOption.formula) or [[]]
    except Exception:
        top = [[]]
    copy_cols = [c for c, v in enumerate(list(top[0])[:PLAN_LAST_COL]) if str(v).startswith("=")]
    protect = set(copy_cols) | _array_cols(ws, head)
    placed, off = [], 0
    for after in order:
        placed.append((after, groups[after], after + 1 + off)); off += len(groups[after])
    src_final = l + sum(len(groups[a]) for a in order if a < l)   # แถวต้นแบบสูตรเลื่อนลงตามแถวที่แทรกไว้เหนือมัน
    reqs = [{"insertDimension": {"range": {"sheetId": ws.id, "dimension": "ROWS", "startIndex": a, "endIndex": a + len(groups[a])},
                                 "inheritFromBefore": True}} for a in sorted(order, reverse=True)]   # แทรกจากล่างขึ้นบน เลขแถวบนจะได้ไม่เลื่อน

    def rng(r0: int, r1: int, c0: int, c1: int) -> dict:
        return {"sheetId": ws.id, "startRowIndex": r0 - 1, "endRowIndex": r1, "startColumnIndex": c0, "endColumnIndex": c1}
    for _a, idx, first in placed:
        last = first + len(idx) - 1
        for c in copy_cols:
            reqs.append({"copyPaste": {"source": rng(src_final, src_final, c, c + 1), "destination": rng(first, last, c, c + 1),
                                       "pasteType": "PASTE_FORMULA"}})
        reqs.append({"copyPaste": {"source": rng(src_final, src_final, 0, PLAN_LAST_COL),
                                   "destination": rng(first, last, 0, PLAN_LAST_COL), "pasteType": "PASTE_DATA_VALIDATION"}})
    ws.spreadsheet.batch_update({"requests": reqs})
    try:
        ws._properties["gridProperties"]["rowCount"] += len(sheet_rows)
    except Exception:
        pass
    data = [{"range": f"A{first}", "values": [[None if c in protect else sheet_rows[i][c] for c in range(PLAN_LAST_COL)] for i in idx]}
            for _a, idx, first in placed]
    try:
        ws.batch_update(data, value_input_option="USER_ENTERED")
    except Exception as e:
        raise HTTPException(status_code=502, detail=f"แทรกแถวในชีตแล้วแต่เขียนค่าไม่สำเร็จ ({type(e).__name__}) — ตรวจแถวว่างในวันนั้นแล้วลองใหม่")
    firsts = [pl[2] for pl in placed]
    end_n = len(sheet_rows) - near_n
    note = (f"แทรก {len(sheet_rows)} แถวเข้าวัน (ไม่ลบงานเดิม): {near_n} แถวติดกับแถวรถคันเดิม"
            + (f" และ {end_n} แถวต่อท้ายวัน (รถคันใหม่/ยังไม่มีเบอร์รถ)" if end_n else ""))
    return {"first": min(firsts), "last": max(pl[2] + len(pl[1]) - 1 for pl in placed), "inserted": len(sheet_rows),
            "kept": [_col_name(c) for c in sorted(protect)], "note": note}


@app.post("/api/plan/import", include_in_schema=False)
async def plan_import(file: Optional[UploadFile] = File(None), rows_json: str = Form(""),
                      commit: int = Form(0), replace: int = Form(1), master_json: str = Form(""), near: int = Form(0),
                      skip_dups: int = Form(0)):
    """ครั้งแรกส่ง file (อ่านใบจัดรถ) ครั้งต่อไปส่ง rows_json (แถวที่แก้ในหน้าต่างนำเข้า) เพื่อตรวจซ้ำ/เขียนจริง"""
    headers = None
    if rows_json:
        try:
            rows_in = json.loads(rows_json)
            assert isinstance(rows_in, list) and len(rows_in) <= 2000 and all(isinstance(r, list) for r in rows_in)
        except Exception:
            raise HTTPException(status_code=400, detail="ข้อมูลแถวที่ส่งมาไม่ถูกต้อง")
        notes: list = []
        master = None
        if master_json:
            try:
                master = _clean_master(json.loads(master_json))
            except HTTPException:
                raise
            except Exception:
                raise HTTPException(status_code=400, detail="ข้อมูลรถ/พขร. ที่ส่งมาไม่ถูกต้อง")
    else:
        if file is None:
            raise HTTPException(status_code=400, detail="ไม่ได้แนบไฟล์")
        data = await file.read()
        if len(data) > IMPORT_MAX_BYTES:
            raise HTTPException(status_code=413, detail="ไฟล์ใหญ่เกิน 4MB")
        parsed = _parse_dispatch_xlsx(data)
        rows_in, headers, notes = parsed["rows"], parsed["headers"], parsed["notes"]
        master = parsed["master"]
    rv = _review_rows(rows_in, notes, skip_load=bool(near))
    sheet_rows = rv.pop("sheet_rows")
    block = _import_block_reason()
    info = {**rv, "headers": headers, "total": len(rv["rows"]), "can_commit": not block, "block_reason": block,
            "target": "ชีตทดลอง" if PLAN_PAGE_ID != SOURCE_ID else "ชีตจริง", "existing": None,
            "master": master if file is not None and not rows_json else None, "master_n": len(master or {})}

    # ในชีตปลายทางมีงานของวันนี้อยู่แล้วกี่แถว (ถ้าอ่านได้) — เอาไว้เตือนก่อนแทนที่
    if rv["date"]:
        try:
            sheet = _fetch_sheet(PLAN_PAGE_ID, PLAN_PAGE_TAB)
            info["existing"] = sum(1 for r in sheet if _parse_date(_cell(r, PLAN_DATE)) == rv["date"])
        except Exception:
            info["existing"] = None
    dups: list = []
    if near and rv["date"]:                       # โหมดวางข้อมูล: เตือนงานที่ซ้ำกับในชีต (ไม่เช็กตอนนำเข้าไฟล์ เพราะนั้นแทนที่ทั้งวันอยู่แล้ว)
        dups = _dup_rows(rv["rows"], rv["date"])
        info["dups"] = dups
        if dups:
            info["marks"] = (info.get("marks") or []) + [{"r": i, "c": 7, "msg": "ซ้ำกับงานที่มีในชีตของวันนี้แล้ว"} for i in dups]
            info["warnings"] = [f"{len(dups)} แถวซ้ำกับงานที่มีในชีตของวันนี้อยู่แล้ว (เลขออเดอร์/เลขโหลด/ต้นทาง/ปลายทาง/Drop เหมือนกัน) "
                                "— ติ๊ก \"ข้ามแถวที่ซ้ำ\" เพื่อไม่ให้งานซ้ำ"] + list(info.get("warnings") or [])
            info["warnings_total"] = int(info.get("warnings_total") or 0) + 1
    if near and rv["date"]:
        tc = _triple_conflicts(rv["rows"], rv["date"])
        if tc:
            info["marks"] = (info.get("marks") or []) + [{"r": n, "c": 4, "msg": f"รถ+เที่ยว+Drop ซ้ำกับ{src}"} for n, src in tc]
            info["warnings"] = [f"{len(tc)} แถวมี รถ+เที่ยววิ่ง+Drop ซ้ำกับงานอื่นของวันนี้ (เลข JOB จะชนกัน) — แก้เที่ยววิ่งหรือ Drop ในช่องสีแดง"] + list(info.get("warnings") or [])
            info["warnings_total"] = int(info.get("warnings_total") or 0) + 1
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
    if near and skip_dups and dups:                # ข้ามแถวที่ซ้ำกับชีต (อ่านสดอีกรอบก่อนตัดสิน)
        _drop_sheet_cache(PLAN_PAGE_ID, PLAN_PAGE_TAB)
        dups = _dup_rows(rv["rows"], rv["date"])
        skip = set(dups)
        sheet_rows = [r for i, r in enumerate(sheet_rows) if i not in skip]
        if not sheet_rows:
            raise HTTPException(status_code=400, detail="ทุกแถวที่วางซ้ำกับงานที่มีในชีตแล้ว — ไม่มีอะไรให้เพิ่ม ไม่เขียนอะไรลงชีต")
    try:
        ws, _sh = _plan_ws()
        col_c = ws.col_values(PLAN_DATE + 1)
        head = _head_index(col_c)
        n_new = len(sheet_rows)
        removed = inserted = 0
        hit = [i + 1 for i, v in enumerate(col_c) if i > head and _parse_date(v) == rv["date"]]   # แถวของวันนี้ (อ้างอิงคอลัมน์ C)
        if near and hit:                                  # วางข้อมูลลูกค้าเข้าวันที่มีอยู่แล้ว: เพิ่มโดยไม่ลบ แทรกติดรถคันเดิม
            res = _write_near(ws, head, hit, sheet_rows)
            _drop_sheet_cache(PLAN_PAGE_ID, PLAN_PAGE_TAB)
            return {**info, "written": len(sheet_rows), "removed": 0, "inserted": res["inserted"], "first_row": res["first"],
                    "last_row": res["last"], "kept_formula_cols": res["kept"], "note": res["note"],
                    "master_saved": 0, "master_note": ""}
        if hit and replace:
            f, l = hit[0], hit[-1]
            if len(hit) != l - f + 1:
                raise HTTPException(status_code=409, detail=f"แถวของวันที่ {rv['date']} ในชีตกระจายหลายช่วง (แถว {f}–{l} มีวันอื่นคั่น) "
                                    "ระบบไม่แทนที่ให้เพราะอาจทับข้อมูลวันอื่น — แก้ในชีตให้เป็นช่วงเดียวก่อน")
            old = l - f + 1
            start = f
            if n_new > old:                                   # แถวใหม่มากกว่าเดิม → แทรกเพิ่มท้ายบล็อก (ก่อนแถวสีดำ)
                inserted = n_new - old
                _insert_blank_rows(ws, l + 1, inserted)
                _copy_down(ws, l, l + 1, l + inserted)
            elif n_new < old:                                 # น้อยกว่าเดิม → ลบส่วนเกินท้ายบล็อก
                removed = old - n_new
                ws.delete_rows(f + n_new, l)
            note = f"แทนที่บล็อกวันที่ {rv['date']} ที่ตำแหน่งเดิม (แถว {f}) แถวสีดำคั่นวันไม่ถูกแตะ"
        else:
            last = max([i + 1 for i, v in enumerate(col_c) if str(v).strip()] + [head + 1])
            dark = _row_is_dark(ws, last + 1)                  # แถวถัดจากวันสุดท้ายเป็นแถวสีดำคั่นวันไหม
            start = last + 2 if dark is not False else last + 1   # อ่านสีไม่ได้ = ถือว่าเป็นแถวสีดำ (ข้ามไว้ก่อนดีกว่าทับ)
            last_day = max((d for d in (_parse_date(v) for v in col_c[head + 1:]) if d), default=None)
            note = (f"วันที่ {rv['date']} ต่อท้ายวันสุดท้ายในชีต (แถว {start}) โดยข้ามแถวสีดำ" if start > last + 1
                    else f"วันที่ {rv['date']} ต่อท้ายวันสุดท้ายในชีต (แถว {start})")
            if last_day and rv["date"] < last_day:
                note += f" — ระวัง: ในชีตมีวันที่ใหม่กว่า ({last_day}) อยู่แล้ว ระบบไม่ได้แทรกตามลำดับวัน"
            if hit and not replace:
                note += " — ไม่ได้ติ๊กแทนที่ จึงมีแถวของวันนี้ซ้ำ 2 ชุดในชีต"
        need = start + n_new - 1
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
    master_saved, master_note = 0, ""
    if master:                                 # เก็บข้อมูลรถ/พขร. ไว้เติมอัตโนมัติ — พลาดตรงนี้ไม่ทำให้การนำเข้าแผนงานล้ม
        try:
            master_saved = _save_master(master)
        except Exception as e:
            master_note = f"นำเข้าแผนงานสำเร็จ แต่เก็บข้อมูลรถ/พขร. ไม่ได้ ({type(e).__name__})"
    return {**info, "written": len(sheet_rows), "removed": removed, "inserted": inserted, "first_row": start,
            "last_row": start + len(sheet_rows) - 1, "kept_formula_cols": kept_cols, "note": note,
            "master_saved": master_saved, "master_note": master_note}


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
    hint_car: str = ""       # เจตนา: เบอร์รถหลังแก้ครบ (ตอนเปลี่ยนรถ+เที่ยวพร้อมกัน ช่องแรกที่ส่งยังไม่ซ้ำกลางทาง)
    hint_trip: str = ""      # เจตนา: เที่ยววิ่งหลังแก้ครบ


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


# ข้อมูลรถ+พขร. สำหรับเติมอัตโนมัติ — อ่านอย่างเดียวจากแท็บในไฟล์แผนงานของหน้านี้ (PLAN_PAGE_ID) เท่านั้น ไม่เขียนอะไร
#   ข้อมูลรถ     : หัว เบอร์รถ / ทะเบียนรถ / ประเภทรถ
#   พขร.ประจำรถ  : หัว เบอร์รถ / พขร.1 / พขร.2 (ประเภทรถ)
#   ข้อมูลพขร.   : หัว ชื่อ-สกุล / เบอร์ติดต่อ (วันที่พ้นสภาพ ถ้ามี = ข้ามคนที่ออกแล้ว)
# หาคอลัมน์จาก "ชื่อหัวตาราง" ไม่ใช้ตำแหน่งตายตัว ถ้าไม่มีแท็บ/หัวไม่ตรง = ว่าง (หน้าเว็บก็แค่ไม่เติมให้)
_cars_cache: tuple = (0.0, None)
_CAR_RE = re.compile(r"^[A-Za-z]{2,4}\.?\s?\d")
_NO_PERSON = {"", "-", "—", "ยังไม่มีรถ", "ไม่มี", "ว่าง", "ผ่านแล้ว"}


def _hdr_cells(row: list) -> list:
    return [str(c).replace("\n", " ").strip() for c in row]


def _hdr_find(rows: list, need: list, limit: int = 40):
    """แถวหัวตาราง (ใน limit แถวแรก) ที่มีชื่อครบ → (เลขแถว, {ชื่อ: คอลัมน์แรกที่เจอ}) ไม่เจอ = (None, {})"""
    for i, r in enumerate(rows[:limit]):
        cells = _hdr_cells(r)
        if all(n in cells for n in need):
            return i, {n: cells.index(n) for n in need}
    return None, {}


MASTER_TAB = "MasterCarDriver"            # แท็บของเว็บเอง: เก็บข้อมูลรถ/พขร. ที่อ่านจากไฟล์จัดงานตอนนำเข้า (เขียนทับทั้งแท็บทุกครั้งที่นำเข้า)
MASTER_HEADER = ["เบอร์รถ", "ประเภทรถ", "ทะเบียนรถ", "พขร.1", "พขร.2", "เบอร์โทร.1", "เบอร์โทร.2", "อัปเดตเมื่อ"]
_MASTER_KEYS = ("t", "plate", "d1", "d2", "p1", "p2")


def _build_cars(tabs: dict, phones_out=None, names_out=None) -> dict:
    """tabs = {ชื่อแท็บ: แถว (list ของข้อความ)} → {เบอร์รถ: {t, plate, d1, d2, p1, p2}}
    หาคอลัมน์จาก "ชื่อหัวตาราง" ไม่ใช้ตำแหน่งตายตัว แท็บที่ไม่มี/หัวไม่ตรง = ข้ามไป"""
    def norm_type(t: str) -> str:             # "08 Tons" / "10 Tons" / "Trailer (สำรอง)" → ค่าที่ช่อง Q รับ
        t = (t or "").strip().lower()
        return next((v for v in _FIXED_STRICT["16"] if t.startswith(v.lower())), "")

    def person(v: str) -> str:
        v = (v or "").strip()
        return "" if v in _NO_PERSON else v

    def blank() -> dict:
        return {k: "" for k in _MASTER_KEYS}

    cars: dict = {}
    rows = tabs.get("ข้อมูลรถ") or []
    h, ix = _hdr_find(rows, ["เบอร์รถ", "ทะเบียนรถ"])
    if h is not None:
        hc = _hdr_cells(rows[h])
        tcol = hc.index("ประเภทรถ") if "ประเภทรถ" in hc else (hc.index("น้ำหนัก") if "น้ำหนัก" in hc else None)   # ชีตต้นฉบับเก็บ "10 Tons/Trailer" ไว้ในคอลัมน์ น้ำหนัก
        for r in rows[h + 1:]:
            car = _cell(r, ix["เบอร์รถ"])
            if _CAR_RE.match(car):
                e = cars.setdefault(car, blank())
                e["plate"] = _cell(r, ix["ทะเบียนรถ"])
                e["t"] = norm_type(_cell(r, tcol)) if tcol is not None else ""

    phones: dict = {}
    rows = tabs.get("ข้อมูลพขร.") or []
    h, ix = _hdr_find(rows, ["ชื่อ-สกุล", "เบอร์ติดต่อ"])
    if h is not None:
        hc = _hdr_cells(rows[h])
        leave = hc.index("วันที่พ้นสภาพ") if "วันที่พ้นสภาพ" in hc else None
        for r in rows[h + 1:]:
            name, ph = _cell(r, ix["ชื่อ-สกุล"]), _cell(r, ix["เบอร์ติดต่อ"])
            gone = leave is not None and bool(_cell(r, leave))                 # มีวันพ้นสภาพ = ไม่นับ
            if name and not gone and names_out is not None and name not in names_out:
                names_out.append(name)
            if name and ph and not gone and name not in phones:
                phones[name] = ph
        if phones_out is not None:
            phones_out.update(phones)

    rows = tabs.get("พขร.ประจำรถ") or []
    for h, r0 in enumerate(rows[:40]):
        cells = _hdr_cells(r0)
        blocks = []                            # ตารางเรียงข้างกันได้หลายชุด (เช่น บางปะกง | ศรีราชา)
        for j, c in enumerate(cells):
            if c != "เบอร์รถ":
                continue
            nxt = lambda name: next((k for k in range(j + 1, len(cells)) if cells[k] == name), None)
            if nxt("พขร.1") is not None:
                blocks.append((j, nxt("พขร.1"), nxt("พขร.2"), nxt("ประเภทรถ")))
        if not blocks:
            continue
        for r in rows[h + 1:]:
            for jc, j1, j2, jt in blocks:
                car = _cell(r, jc)
                if not _CAR_RE.match(car):
                    continue
                e = cars.setdefault(car, blank())
                e["d1"], e["d2"] = person(_cell(r, j1)), (person(_cell(r, j2)) if j2 is not None else "")
                e["p1"], e["p2"] = phones.get(e["d1"], ""), phones.get(e["d2"], "")
                if not e["t"] and jt is not None:
                    e["t"] = norm_type(_cell(r, jt))
        break
    return cars


def _clean_master(obj) -> dict:
    """ข้อมูลรถที่หน้าเว็บส่งกลับมาตอนยืนยันนำเข้า → ตรวจรูปแบบ/ขนาดก่อนเก็บ (ไม่ไว้ใจค่าจากฝั่งผู้ใช้)"""
    if not isinstance(obj, dict) or len(obj) > 800:
        raise HTTPException(status_code=400, detail="ข้อมูลรถ/พขร. ที่ส่งมาไม่ถูกต้อง")
    out: dict = {}
    for car, e in obj.items():
        if not isinstance(car, str) or len(car) > 20 or not _CAR_RE.match(car) or not isinstance(e, dict):
            continue
        row = {k: str(e.get(k, "") or "").replace("\n", " ").strip()[:100] for k in _MASTER_KEYS}
        if row["t"] not in ("",) + tuple(_FIXED_STRICT["16"]):
            row["t"] = ""
        out[car] = row
    return out


def _save_master(cars: dict) -> int:
    """เก็บข้อมูลรถ/พขร. ลงแท็บ MasterCarDriver ของไฟล์แผนงาน (ไฟล์ทดลองเท่านั้น — ต้องผ่านด่านเดียวกับการนำเข้า)
    สร้างแท็บใหม่ถ้ายังไม่มี และเขียนทับ "เฉพาะแท็บนี้" ไม่แตะแท็บแผนงานหรือแท็บอื่นเลย"""
    block = _import_block_reason()
    if block:
        raise HTTPException(status_code=403, detail=block)
    global _cars_cache
    _, sh = _plan_ws()
    try:
        mws = sh.worksheet(MASTER_TAB)
    except gspread.WorksheetNotFound:
        mws = sh.add_worksheet(title=MASTER_TAB, rows=max(len(cars) + 20, 100), cols=len(MASTER_HEADER))
    stamp = _thai_now().strftime("%Y-%m-%d %H:%M")
    rows = [MASTER_HEADER] + [[car] + [e[k] for k in _MASTER_KEYS] + [stamp] for car, e in sorted(cars.items())]
    mws.clear()
    if mws.row_count < len(rows):
        mws.add_rows(len(rows) - mws.row_count)
    mws.update(values=rows, range_name="A1", value_input_option="RAW")      # RAW = ไม่ตีความเป็นสูตร
    _drop_sheet_cache(PLAN_PAGE_ID, MASTER_TAB)
    _cars_cache = (0.0, None)
    return len(cars)


def _plan_cars() -> dict:
    global _cars_cache
    ts, hit = _cars_cache
    if hit is not None and time() - ts < _OPTS_TTL:
        return hit

    def tab(name: str) -> list:
        try:
            return _fetch_sheet(PLAN_PAGE_ID, name)
        except Exception:
            return []

    # 1) แท็บข้อมูลรถ/พขร. ที่วางไว้ในชีตเอง  2) แท็บ MasterCarDriver ที่เว็บเก็บไว้ตอนนำเข้าไฟล์จัดงาน (ใหม่กว่า — ทับ)
    phones_all: dict = {}
    names_all: list = []
    cars = _build_cars({n: tab(n) for n in ("ข้อมูลรถ", "พขร.ประจำรถ", "ข้อมูลพขร.")}, phones_all, names_all)
    rows = tab(MASTER_TAB)
    h, ix = _hdr_find(rows, ["เบอร์รถ", "ทะเบียนรถ", "พขร.1"])
    if h is not None:
        names = _hdr_cells(rows[h])
        cols = {"t": "ประเภทรถ", "plate": "ทะเบียนรถ", "d1": "พขร.1", "d2": "พขร.2", "p1": "เบอร์โทร.1", "p2": "เบอร์โทร.2"}
        for r in rows[h + 1:]:
            car = _cell(r, ix["เบอร์รถ"])
            if _CAR_RE.match(car):
                cars[car] = {k: (_cell(r, names.index(v)) if v in names else "") for k, v in cols.items()}
                for dk, pk in (("d1", "p1"), ("d2", "p2")):
                    if cars[car][dk] and cars[car][pk]:
                        phones_all.setdefault(cars[car][dk], cars[car][pk])
    src = {"live": "ไม่ได้ตั้งค่า" if not CARS_SHEET_ID else "", "live_n": 0}
    if CARS_SHEET_ID:                          # 3) ชีตข้อมูลรถ+พขร. (อ่านอย่างเดียว) — ใหม่สุด ทับชั้นอื่น
        live_tabs, errs = {}, []
        for name in ("ข้อมูลรถ", "พขร.ประจำรถ", "ข้อมูลพขร."):
            try:
                live_tabs[name] = _fetch_sheet(CARS_SHEET_ID, name)
            except Exception as e:
                errs.append(f"{name}: {type(e).__name__}")
        ph_live: dict = {}
        nm_live: list = []
        live = _build_cars(live_tabs, ph_live, nm_live) if live_tabs else {}
        cars.update(live)
        phones_all.update(ph_live)
        if nm_live:                           # ชีตข้อมูลรถ+พขร. อ่านได้ → รายชื่อคนขับใช้ของชีตนี้ (คนเท่านั้น ไม่รวมคนที่พ้นสภาพ)
            names_all = nm_live
        src["live_n"] = len(live)
        src["live"] = ("อ่านได้" if live else "อ่านแล้วไม่พบรถ") + (" · แท็บที่อ่านไม่ได้: " + ", ".join(errs) if errs else "")
    result = {"cars": cars, "n": len(cars), "from": src, "phones": phones_all, "drivers": sorted(set(names_all))}
    _cars_cache = (time(), result)
    return result


@app.get("/api/plan/cars", include_in_schema=False)
def plan_cars():
    """เบอร์รถ → {t ประเภทรถ, plate ทะเบียน, d1/d2 พขร.1-2, p1/p2 เบอร์โทร} ไว้เติมอัตโนมัติตอนเลือกเบอร์รถ (อ่านอย่างเดียว)"""
    return _plan_cars()


def _job_conflict(ws, p, new: str, cur: list):
    """คืนเลขแถวของงานอื่นในวันเดียวกันที่ รถ+เที่ยว+Drop ซ้ำกับที่จะเป็นหลังแก้ (ไม่ซ้ำ = None)
    เลข JOB (วันที่+รถ+เที่ยว) ซ้ำกันได้ถ้า Drop ต่างกัน (งานหลายจุดส่งของเที่ยวเดียวกัน) แต่ รถ+เที่ยว+Drop ห้ามซ้ำ
    อ่านเฉพาะคอลัมน์ C,E,N,P สดจากชีต 1 คำขอ; อ่านไม่ได้ = ไม่บล็อก"""
    car = p.hint_car.strip() or (new if p.col == 15 else str(cur[15]).strip())
    trip = p.hint_trip.strip() or (new if p.col == 4 else str(cur[4]).strip())
    drop = (new if p.col == 13 else str(cur[13])).strip() or "1"
    day = _parse_date(str(cur[2]))
    if not (car and trip and day):
        return None
    try:
        rc = max(int(ws.row_count), 2)
        cols = ws.batch_get([f"C1:C{rc}", f"E1:E{rc}", f"N1:N{rc}", f"P1:P{rc}"])
    except Exception:
        return None

    def col(k: int, i: int) -> str:
        vr = cols[k]
        return str(vr[i][0]).strip() if i < len(vr) and vr[i] else ""
    for i in range(max(len(c) for c in cols)):
        if i + 1 == p.row or _parse_date(col(0, i)) != day:
            continue
        if col(3, i) == car and col(1, i) == trip and (col(2, i) or "1") == drop:
            return i + 1
    return None


class PresenceIn(BaseModel):
    name: str = ""       # ผู้แก้ (ว่าง = แค่ดู ไม่ลงชื่อ)
    date: str = ""
    row: int = 0         # แถวที่กำลังแก้ (0 = ไม่ได้แก้ช่องไหน)
    col: int = -1


_presence: dict = {}
PRESENCE_TTL = 20        # วินาที — ไม่ส่งสัญญาณเกินนี้ถือว่าออกไปแล้ว


@app.post("/api/plan/presence", include_in_schema=False)
def plan_presence(p: PresenceIn):
    """หน้าเว็บส่งสัญญาณทุก ~7 วินาที: ผู้แก้ลงชื่อว่ากำลังอยู่ที่ช่องไหน ได้รายชื่อคนอื่นที่ออนไลน์ในวันเดียวกันกลับไป"""
    now, day, name = time(), p.date[:10], p.name.strip()[:40]
    for k in [k for k, v in _presence.items() if now - v["t"] > PRESENCE_TTL]:
        _presence.pop(k, None)
    if name and (name in _presence or len(_presence) < 60):
        _presence[name] = {"t": now, "date": day, "row": max(p.row, 0), "col": p.col}
    return {"others": [{"name": k, "row": v["row"], "col": v["col"]} for k, v in _presence.items()
                       if k != name and v["date"] == day]}


@app.post("/api/plan/edit", include_in_schema=False)
def plan_edit(p: PlanEdit):
    """แก้ 1 ช่อง — ยิง Google ประมาณ 5 ครั้งต่อช่อง: อ่านแถว, อ่านสูตร (รวมบรรทัดหัว), เขียน, อ่านแถวกลับ, เขียนประวัติ
    (client/ไฟล์/แท็บ EditLog เก็บไว้ใช้ซ้ำ ไม่ล็อกอินและเปิดใหม่ทุกครั้ง)"""
    block = _write_block_reason("PLAN_EDIT_ENABLED")
    if block:
        raise HTTPException(403, block)
    if not (0 <= p.col < PLAN_LAST_COL) or p.row < 2:
        raise HTTPException(400, "ตำแหน่งช่องไม่ถูกต้อง")
    new = _edit_value(p.col, p.value)
    letter = _col_name(p.col)
    rng = f"A{p.row}:Z{p.row}"
    V = gspread.utils.ValueRenderOption

    for attempt in (0, 1):                      # ถ้าของที่เก็บไว้เสีย (เช่นแท็บถูกเปลี่ยนชื่อ) เปิดใหม่แล้วลองอีกครั้ง
        try:
            ws, sh = _plan_ws(force=bool(attempt))
            cur = _pad_row(ws.get(rng))        # อ่านแถวนี้สดจากชีต
            break
        except Exception as e:
            _gs_forget()
            if attempt:
                raise HTTPException(502, f"อ่านชีตไม่ได้ — {type(e).__name__}: {e}")

    cur_key = f"{cur[1]}|{cur[13]}" if cur[1] else ""
    if not any(str(x).strip() for x in cur):
        # แถวว่างทั้งแถว (ถูกลบ/ล้างไปแล้ว) — ไม่เขียนลงแถวว่างเพราะหน้าเว็บที่เปิดค้างไว้ยังเห็นข้อมูลเก่า
        return JSONResponse(status_code=409, content={"detail":
            "แถวนี้ถูกลบหรือว่างไปแล้วในชีต — กดรีเฟรชก่อน", "current": ""})
    if p.key != cur_key:
        return JSONResponse(status_code=409, content={"detail":
            "แถวนี้ในชีตเปลี่ยนไปแล้ว (มีคนแก้หรือแทรกแถว) — กดรีเฟรชแล้วแก้ใหม่", "current": cur[p.col]})
    if str(cur[p.col]).strip() != p.old.strip():
        return JSONResponse(status_code=409, content={"detail":
            "ช่องนี้มีคนแก้ไปก่อนแล้ว — ยังไม่เขียนทับ", "current": cur[p.col]})

    if p.col in (4, 13, 15) and new:                  # เบอร์รถ/เที่ยววิ่ง/Drop: กัน รถ+เที่ยว+Drop ซ้ำกับงานอื่นของวันนั้น (กรณีจัดรถพร้อมกัน)
        other = _job_conflict(ws, p, new, cur)
        if other:
            return JSONResponse(status_code=409, content={"code": "job-dup", "row": other, "current": cur[p.col], "detail":
                f"รถ+เที่ยววิ่ง+Drop นี้ของวันนี้มีอยู่แล้วที่แถว {other} (มีคนใช้ไปก่อน) — เลือกเที่ยวหรือรถอื่น"})

    # ช่องที่เป็นสูตร (หรืออยู่ในคอลัมน์ ARRAYFORMULA): เขียนทับแล้วสูตรหายถาวร จึงไม่เขียนเว้นแต่คนแก้ยืนยัน (override)
    formula, in_array = "", False
    try:
        top, rowf = ws.batch_get([f"A1:Z{_cached_head() + 4}", rng], value_render_option=V.formula)   # สูตร 2 ช่วง ในคำขอเดียว
        in_array = p.col in _array_cols_from(top)
        rf = list(rowf[0]) if rowf else []
        formula = str(rf[p.col]) if p.col < len(rf) else ""
    except Exception:
        formula, in_array = "", False
    is_formula = formula.startswith("=") or in_array
    if is_formula and not p.override:
        return JSONResponse(status_code=423, content={"detail":
            "ช่องนี้เป็นสูตรในชีต (ค่าถูกคำนวณจากช่องอื่น)", "formula": True, "current": cur[p.col]})
    try:
        ws.update(values=[[new]], range_name=f"{letter}{p.row}", value_input_option="USER_ENTERED")
        fresh_row = _pad_row(ws.get(rng))       # อ่านทั้งแถวกลับครั้งเดียว: ได้ทั้งค่าที่ชีตแสดงจริงและช่องสูตรที่คำนวณใหม่
        shown = fresh_row[p.col]
    except Exception as e:
        _gs_forget()
        raise HTTPException(502, f"เขียนลงชีตไม่สำเร็จ — {type(e).__name__}: {e}")

    hit = _sheet_cache.get(f"{PLAN_PAGE_ID}:{PLAN_PAGE_TAB}")         # แก้แคชในแถวเดียว ไม่ต้องอ่านทั้งชีตใหม่
    if hit and p.row - 1 < len(hit[1]):
        r = hit[1][p.row - 1]
        r.extend([""] * (PLAN_LAST_COL - len(r)))
        r[:PLAN_LAST_COL] = fresh_row

    logged = True
    try:                                                              # ประวัติการแก้ไข (ล้มเหลวไม่กระทบการแก้)
        _editlog_ws(sh).append_row([_thai_now().strftime("%Y-%m-%d %H:%M:%S"), p.by[:60], p.row, letter,
                                    p.old, shown, cur_key,
                                    ("เขียนทับสูตร: " + (formula[:80] or "ARRAYFORMULA ของคอลัมน์")) if is_formula else ""],
                                   value_input_option="RAW")
    except Exception:
        logged = False
        _gs_cache.pop("log", None)
    global _recent_cache
    _recent_cache = (0.0, None)
    return {"ok": True, "value": shown, "row": p.row, "col": p.col, "cells": fresh_row,
            "overwrote_formula": is_formula, "logged": logged}


_recent_cache: tuple = (0.0, None)


@app.get("/api/plan/recent", include_in_schema=False)
def plan_recent(n: int = Query(300)):
    """การแก้ไขล่าสุดจากแท็บ EditLog (เวลา/ผู้แก้/แถว/คอลัมน์/ค่าเดิม→ใหม่) ไว้บอกอีกคนว่า "เพื่อนแก้ไปแล้ว"
    อ่านอย่างเดียว ไม่สร้างแท็บ EditLog ถ้ายังไม่มี; แคช 8 วินาที กันหลายคนเปิดพร้อมกันแล้วอ่านชีตซ้ำ"""
    global _recent_cache
    ts, hit = _recent_cache
    if hit is not None and time() - ts < 8:
        return {"edits": hit[-n:]}
    out: list = []
    try:
        _ws, sh = _plan_ws()
        try:
            lg = sh.worksheet(EDIT_LOG_TAB)
        except gspread.WorksheetNotFound:
            lg = None
        if lg is not None:
            for r in (lg.get(f"A2:H{max(lg.row_count, 2)}") or [])[-400:]:
                r = list(r) + [""] * 8
                if not r[0]:
                    continue
                out.append({"t": r[0], "by": r[1], "row": int(r[2]) if str(r[2]).isdigit() else 0,
                            "col": r[3], "old": r[4], "new": r[5], "note": r[7]})
    except Exception:
        out = []
    _recent_cache = (time(), out)
    return {"edits": out[-n:]}


# ─── รายงาน On Time (อ่านอย่างเดียวจากชีตแผนงานจริง ไม่มีการเขียนใดๆ) ───────────────────────────────
# เวลาในชีตรูปแบบ "19/10/2026, 8:56:04" (นับถึงวินาที) · คอลัมน์: AB เข้าลาน, AC เข้าโหลด, AD ออกโหลด, AE ออกคลัง, AF เข้าปลายทาง, AG ออกปลายทาง,
# AV On Time (PASS/Delay), AW นาทีที่ช้า
ONTIME_TARGET = float(os.environ.get("ONTIME_TARGET", "95") or 95)   # เป้า On Time (%) — การ์ดบอก ดี/แย่ เทียบเป้านี้
REPORT_MAX_MIN = 24 * 60          # ช่วงเวลาที่เกินนี้ถือว่าบันทึกผิด ไม่นำมาเฉลี่ย
_rep_dist_cache: tuple = (0.0, None)


def _rep_dt(raw: str):
    """'19/10/2026, 8:56:04' / '2026-10-19 08:56:04' → datetime (รวมวินาที รองรับปี พ.ศ.) ไม่ใช่เวลา = None"""
    t = str(raw or "").strip()
    m = re.search(r"(\d{1,2})[/.\-](\d{1,2})[/.\-](\d{4})\D+(\d{1,2}):(\d{2})(?::(\d{2}))?", t)
    if m:
        d, mo, y, h, mi, sec = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6) or 0)
    else:
        m = re.match(r"(\d{4})-(\d{2})-(\d{2})[T ](\d{1,2}):(\d{2})(?::(\d{2}))?", t)
        if not m:
            return None
        y, mo, d, h, mi, sec = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6) or 0)
    if y > 2400:
        y -= 543
    try:
        return datetime(y, mo, d, h, mi, sec)
    except ValueError:
        return None


def _rep_gap(a, b):
    """นาที (b − a) ถ้าเป็นช่วงที่สมเหตุสมผล (0..24 ชม.) ไม่งั้น None"""
    if not a or not b:
        return None
    m = (b - a).total_seconds() / 60
    return round(m, 2) if 0 <= m <= REPORT_MAX_MIN else None


def _rep_distances() -> dict:
    """ปลายทาง → {คลังต้นทาง: กม.} จากแท็บ "ข้อมูลปลายทาง" (หัวคอลัมน์ที่เป็นชื่อคลัง) — ไม่มี/อ่านไม่ได้ = ว่าง"""
    global _rep_dist_cache
    ts, hit = _rep_dist_cache
    if hit is not None and time() - ts < 600:
        return hit
    out: dict = {}
    try:
        rows = _fetch_sheet(DEST_ID, DEST_TAB)
        head = [str(c).strip() for c in (rows[0] if rows else [])]
        cols = {i: h for i, h in enumerate(head) if h in DEPOTS}
        for r in rows[1:]:
            name = _cell(r, DEST_NAME)
            if not name:
                continue
            d = {}
            for i, dep in cols.items():
                v = _cell(r, i).replace(",", "")
                if re.fullmatch(r"\d+(\.\d+)?", v):
                    d[dep] = float(v)
            if d:
                out[name] = d
    except Exception:
        out = {}
    _rep_dist_cache = (time(), out)
    return out


def _rep_ontime(raw: str) -> str:
    """ช่อง On Time (AV) → "PASS" / "Delay" / "" (ยังไม่ตัดสิน)
    อ่านแบบยืดหยุ่น: มีคำว่า pass/ผ่าน (แต่ไม่ใช่ "ไม่ผ่าน") = PASS; delay/late/ช้า/ไม่ผ่าน/fail = Delay"""
    t = str(raw or "").strip().lower()
    if not t or t in ("-", "n/a", "#n/a", "null"):
        return ""
    if "ไม่ผ่าน" in t or "not pass" in t or "fail" in t or "delay" in t or "late" in t or "ช้า" in t:
        return "Delay"
    if "pass" in t or "ผ่าน" in t or "ตรงเวลา" in t or "on time" in t or "ontime" in t:
        return "PASS"
    return ""


def _rep_class(km):
    return "ไม่ทราบระยะ" if km is None else ("สายใกล้" if km <= 80 else ("สายกลาง" if km <= 250 else "สายไกล"))


def _stat(vals: list) -> dict:
    return {"n": len(vals), "min": round(min(vals), 1) if vals else None, "max": round(max(vals), 1) if vals else None,
            "avg": round(sum(vals) / len(vals), 1) if vals else None}


def _group(items: list, key: str) -> dict:
    out: dict = {}
    for x in items:
        out.setdefault(x[key], []).append(x)
    return out


def build_ontime_report(rows: list, d_from: str, d_to: str, f: dict) -> dict:
    """rows = แถวของชีตแผนงาน (รวมหัวตาราง) → สรุปรายงาน On Time ของวันที่ d_from..d_to ตามตัวกรอง f"""
    dist = _rep_distances()
    items = []
    av_seen: dict = {}                    # คำที่พบในช่อง On Time (AV) → จำนวน ไว้ตรวจว่าชีตใช้คำอะไร
    for i, r in enumerate(rows[1:], start=2):
        day = _parse_date(_cell(r, PLAN_DATE))
        if not day or day < d_from or day > d_to:
            continue
        car, origin, vt, drop = _cell(r, PLAN_CARNO), _cell(r, PLAN_SOURCE), _cell(r, PLAN_VTYPE), _cell(r, PLAN_DROP)
        status = _cell(r, PLAN_STATUS)
        if not (car or origin or _cell(r, PLAN_DEST)):
            continue
        if f.get("origin") and origin != f["origin"]:
            continue
        if f.get("vtype") and vt != f["vtype"]:
            continue
        if f.get("car") and car != f["car"]:
            continue
        if f.get("drop") and drop != f["drop"]:
            continue
        yard, lin, lout = _rep_dt(_cell(r, PLAN_YARD)), _rep_dt(_cell(r, PLAN_LOAD_IN)), _rep_dt(_cell(r, PLAN_LOAD_OUT))
        dep, arr, leave = _rep_dt(_cell(r, PLAN_DEPART)), _rep_dt(_cell(r, PLAN_ARRIVE)), _rep_dt(_cell(r, PLAN_LEAVE))
        raw_ot = _cell(r, PLAN_ONTIME).strip()
        av_seen[raw_ot] = av_seen.get(raw_ot, 0) + 1
        ontime = _rep_ontime(raw_ot)      # PASS/Delay อ่านจากชีต (AV) ตรงๆ — ชีตตัดสินเอง (ช้าเกิน 30 นาที = Delay)
        dest = _cell(r, PLAN_DEST)
        km = (dist.get(dest) or {}).get(origin)
        it = {"row": i, "date": day, "job": _cell(r, 1), "car": car, "origin": origin, "dest": dest, "vtype": vt, "drop": drop,
              "order": _cell(r, PLAN_INVOICE), "weight": _cell(r, PLAN_VOLUME), "sched": _cell(r, PLAN_SCHED), "status": status,
              "arrive": arr.strftime("%d/%m/%Y %H:%M:%S") if arr else "", "ontime": ontime,
              "late": _cell(r, PLAN_ONTIME_M),
              "wait": _rep_gap(yard, lin), "load": _rep_gap(lin, lout), "travel": _rep_gap(dep, arr), "unload": _rep_gap(arr, leave),
              "km": km, "cls": _rep_class(km),
              "jtype": _cell(r, PLAN_JOBTYPE).strip() or _cell(r, PLAN_TYPE).strip(),
              "why": _cell(r, PLAN_WHY).strip(), "fix": _cell(r, PLAN_FIXWHY).strip()}
        if f.get("status") and ontime != f["status"]:
            continue
        if f.get("dest") and dest != f["dest"]:
            continue
        if f.get("cls") and it["cls"] != f["cls"]:
            continue
        if f.get("why") and it["why"] != f["why"]:
            continue
        if f.get("fix") and it["fix"] != f["fix"]:
            continue
        if f.get("jtype") is not None and f.get("jtype") != "" and it["jtype"] != (f["jtype"] if f["jtype"] != "(ไม่ระบุ)" else ""):
            continue
        items.append(it)

    def col(key: str, rowset=None) -> list:
        return [x[key] for x in (rowset if rowset is not None else items) if x[key] is not None]
    trips = {x["job"] or f'{x["car"]}|{x["date"]}|{x["row"]}' for x in items if x["car"] and not x["status"].strip()}
    judged = [x for x in items if x["ontime"]]
    by_origin: dict = {}
    for x in items:
        if x["origin"]:
            by_origin.setdefault(x["origin"], []).append(x)
    by_vtype: dict = {}
    by_dest: dict = {}
    by_class: dict = {}
    for x in items:
        if x["vtype"]:
            by_vtype.setdefault(x["vtype"], set()).add(x["job"] or x["row"])
        if x["dest"]:
            by_dest.setdefault((x["jtype"], x["dest"]), []).append(x)
        if x["ontime"] or x["travel"] is not None:
            by_class[x["cls"]] = by_class.get(x["cls"], 0) + 1
    avg = lambda vals: round(sum(vals) / len(vals), 1) if vals else None
    by_day, day_items = [], _group(items, "date")
    d0 = datetime.strptime(d_from, "%Y-%m-%d")
    for k in range((datetime.strptime(d_to, "%Y-%m-%d") - d0).days + 1):       # ทุกวันในช่วง (วันไม่มีงาน = ว่าง)
        ds = (d0 + timedelta(days=k)).strftime("%Y-%m-%d")
        v = day_items.get(ds, [])
        jd = [x for x in v if x["ontime"]]
        ps = sum(1 for x in jd if x["ontime"] == "PASS")
        by_day.append({"date": ds, "drops": len(jd), "pass": ps, "delay": len(jd) - ps,
                       "pct": round(ps / len(jd) * 100, 1) if jd else None,
                       "trips": len({x["job"] or f'{x["car"]}|{x["date"]}|{x["row"]}' for x in v if x["car"] and not x["status"].strip()}),
                       "wait": avg(col("wait", v)), "load": avg(col("load", v))})
    return {
        "from": d_from, "to": d_to, "n_rows": len(items), "by_day": by_day,
        "kpi": {"trips": len(trips), "drops": len(judged), "pass": sum(1 for x in judged if x["ontime"] == "PASS"),
                "delay": sum(1 for x in judged if x["ontime"] == "Delay"),
                "wait": avg(col("wait")), "load": avg(col("load")), "travel": avg(col("travel")), "unload": avg(col("unload"))},
        "by_origin": [{"origin": k, "trips": len({y["job"] or y["row"] for y in v}),
                       "wait": _stat(col("wait", v)), "load": _stat(col("load", v))} for k, v in sorted(by_origin.items())],
        "by_vtype": [{"vtype": k, "trips": len(v)} for k, v in sorted(by_vtype.items())],
        "by_dest": sorted([{"jtype": k[0], "dest": k[1], "drops": len(v), "n": len(col("unload", v)), "travel": avg(col("travel", v)),
                            "unload": avg(col("unload", v))} for k, v in by_dest.items() if col("unload", v)],
                          key=lambda d: -(d["unload"] or 0))[:400],
        "by_why": sorted([{"why": k, "n": len(v), "delay": sum(1 for y in v if y["ontime"] == "Delay"),
                           "pass": sum(1 for y in v if y["ontime"] == "PASS")}
                          for k, v in _group(items, "why").items() if k], key=lambda d: (-d["n"], d["why"])),
        "by_fix": sorted([{"why": k, "n": len(v), "delay": sum(1 for y in v if y["ontime"] == "Delay"),
                           "pass": sum(1 for y in v if y["ontime"] == "PASS"), "cancel": sum(1 for y in v if y["status"].strip())}
                          for k, v in _group(items, "fix").items() if k], key=lambda d: (-d["n"], d["why"])),
        "by_jtype": sorted([{"jtype": jt, "drops": len(v), "n": len(col("unload", v)), "unload": avg(col("unload", v))}
                            for jt, v in _group(items, "jtype").items()], key=lambda d: -d["drops"]),
        "by_class": [{"cls": k, "n": v} for k, v in sorted(by_class.items())],
        "rows": sorted(items, key=lambda x: (x["date"], x["origin"], x["car"], x["row"]))[:600],
        "av_values": sorted(([k or "(ว่าง)", v] for k, v in av_seen.items()), key=lambda kv: -kv[1])[:12],
        "filters": {"origins": sorted({x["origin"] for x in items if x["origin"]}),
                    "vtypes": sorted({x["vtype"] for x in items if x["vtype"]}),
                    "cars": sorted({x["car"] for x in items if x["car"]}),
                    "drops": sorted({x["drop"] for x in items if x["drop"]})},
    }


@app.get("/api/report/ontime", include_in_schema=False)
def report_ontime(date_from: str = Query(None, alias="from"), date_to: str = Query(None, alias="to"),
                  origin: str = "", vtype: str = "", car: str = "", drop: str = "", status: str = "",
                  dest: str = "", cls: str = "", jtype: str = "", why: str = "", fix: str = ""):
    """รายงาน On Time ของช่วงวันที่ (ค่าเริ่มต้น = วันนี้) — อ่านชีตแผนงานจริงอย่างเดียว แคช 5 นาทีตามปกติ"""
    d_from = _parse_date(date_from or "") or _today_thai()
    d_to = _parse_date(date_to or "") or d_from
    if d_to < d_from:
        d_from, d_to = d_to, d_from
    if (datetime.strptime(d_to, "%Y-%m-%d") - datetime.strptime(d_from, "%Y-%m-%d")).days > 93:
        raise HTTPException(400, "เลือกช่วงวันที่ได้ไม่เกิน 3 เดือน")
    try:
        rows = _fetch_sheet(SOURCE_ID, PLAN_TAB)
    except Exception as e:
        raise HTTPException(502, f"อ่านชีตแผนงานไม่ได้ — {type(e).__name__}")
    f = {"origin": origin, "vtype": vtype, "car": car, "drop": drop, "status": status,
         "dest": dest, "cls": cls, "jtype": jtype, "why": why, "fix": fix}
    rep = build_ontime_report(rows, d_from, d_to, f)
    # ช่วงก่อนหน้า ยาวเท่ากัน ต่อกันพอดี (เช่น 7 วันล่าสุด เทียบกับ 7 วันก่อนหน้านั้น) — ใช้ตัวกรองเดียวกัน
    n = (datetime.strptime(d_to, "%Y-%m-%d") - datetime.strptime(d_from, "%Y-%m-%d")).days + 1
    p_to = (datetime.strptime(d_from, "%Y-%m-%d") - timedelta(days=1)).strftime("%Y-%m-%d")
    p_from = (datetime.strptime(d_from, "%Y-%m-%d") - timedelta(days=n)).strftime("%Y-%m-%d")
    prev = build_ontime_report(rows, p_from, p_to, f)
    rep["prev"] = {"from": p_from, "to": p_to, "n_rows": prev["n_rows"], "kpi": prev["kpi"]}
    rep["target"] = ONTIME_TARGET
    return rep


@app.get("/report", response_class=HTMLResponse, include_in_schema=False)
def report_page(request: Request):
    return _nav(REPORT_HTML, request)


@app.get("/plan", response_class=HTMLResponse, include_in_schema=False)
def plan_page(request: Request):
    return _nav(PLAN_HTML, request)


@app.get("/login", response_class=HTMLResponse, include_in_schema=False)
def login_page(error: str = ""):
    if not _app_password():
        return RedirectResponse("/", status_code=303)
    msg = ('<p class="err">ลองผิดหลายครั้งเกินไป — รอ 5 นาทีแล้วลองใหม่</p>' if error == "2"
           else '<p class="err">ชื่อผู้ใช้หรือรหัสผ่านไม่ถูกต้อง</p>' if error else "")
    return LOGIN_HTML.replace("__ERR__", msg)


# กันเดารหัสผ่าน: ผิด LOGIN_MAX_FAILS ครั้งภายใน LOGIN_WINDOW_SECS → ล็อกที่อยู่ IP นั้นชั่วคราว
# (เก็บในหน่วยความจำของแต่ละเครื่อง Vercel — ไม่ได้กันได้ 100% แต่ทำให้เดาทีละหลายพันครั้งไม่ได้)
LOGIN_MAX_FAILS, LOGIN_WINDOW_SECS, LOGIN_LOCK_SECS = 5, 300, 300
_login_fails: dict = {}      # ip → [เวลาที่ผิดแต่ละครั้ง]
_login_locked: dict = {}     # ip → เวลาที่ปลดล็อก


def _client_ip(request: Request) -> str:
    fwd = request.headers.get("x-forwarded-for", "")
    return (fwd.split(",")[0].strip() or (request.client.host if request.client else "?"))[:64]


def _login_gate(ip: str) -> int:
    """คืนจำนวนวินาทีที่ยังถูกล็อกอยู่ (0 = ลองได้)"""
    left = int(_login_locked.get(ip, 0) - time())
    if left <= 0:
        _login_locked.pop(ip, None)
        return 0
    return left


def _login_failed(ip: str) -> None:
    now = time()
    hits = [t for t in _login_fails.get(ip, []) if now - t < LOGIN_WINDOW_SECS] + [now]
    _login_fails[ip] = hits
    if len(hits) >= LOGIN_MAX_FAILS:
        _login_locked[ip] = now + LOGIN_LOCK_SECS
        _login_fails.pop(ip, None)
    if len(_login_fails) > 2000:                     # กันหน่วยความจำบวม
        _login_fails.clear(); _login_locked.clear()


def _pw_equal(a: str, b: str) -> bool:
    """เทียบรหัสแบบเวลาคงที่ — เทียบเป็น bytes เพราะ compare_digest กับ str ที่มีอักษรไทยจะ error (500)"""
    return hmac.compare_digest(a.encode("utf-8"), b.encode("utf-8"))


@app.post("/api/login", include_in_schema=False)
def do_login(request: Request, password: str = Form(""), username: str = Form("")):
    pw = _app_password()
    ip = _client_ip(request)
    wait = _login_gate(ip)
    if wait:
        return RedirectResponse("/login?error=2", status_code=303)
    uname = (username or "").strip().lower()
    u = _users().get(uname) if (pw and uname) else None
    if u and _pw_equal(password, u["pw"]):
        role, dest = uname, _home_for(u["perms"])    # ผู้ใช้จากชีต → หน้าแรกที่มีสิทธิ์
    elif pw and _pw_equal(password, pw):
        role, dest = "", "/"                         # รหัสกลาง → ทุกหน้า
    else:
        _login_failed(ip)
        sleep(0.8)                                   # หน่วงเล็กน้อยทุกครั้งที่ผิด ให้เดาได้ช้าลง
        return RedirectResponse("/login?error=1", status_code=303)
    _login_fails.pop(ip, None)

    resp = RedirectResponse(dest, status_code=303)
    resp.set_cookie(
        COOKIE_NAME, _make_token(role),
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
    <label for="un">ชื่อผู้ใช้</label>
    <input id="un" name="username" type="text" autofocus autocomplete="username" autocapitalize="none"
           placeholder="ชื่อผู้ใช้ (เว้นว่างได้ถ้าใช้รหัสกลาง)" style="margin-bottom:14px">
    <label for="pw">รหัสผ่าน</label>
    <input id="pw" name="password" type="password" required
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


REPORT_HTML = """<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>รายงาน On Time — Gasbulk Track</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root{color-scheme:light;
    --plane:#f4f5f7;--card:#ffffff;--surface:#fcfcfb;--line:#e6e8ec;--hair:#eceae4;--axis:#c3c2b7;
    --ink:#0b0b0b;--ink2:#3f3e3b;--mut:#6b6964;--hover:#f3f6fb;
    --s1:#2a78d6;--s1-soft:#cde2fb;--acc:#2563eb;
    --good:#0ca30c;--good-ink:#006300;--good-bg:#e9f7e9;--crit:#d03b3b;--crit-ink:#b42318;--crit-bg:#fdecec;
    --o1:#86b6ef;--o2:#3987e5;--o3:#184f95;--o0:#c3c2b7;
    --h1:#dcf3dc;--h2:#fff0bf;--h3:#ffd9c2;--h4:#f9c9c9;
    --shadow:0 1px 2px rgba(16,24,40,.06),0 1px 3px rgba(16,24,40,.08)}
  @media (prefers-color-scheme:dark){
    :root:where(:not([data-theme="light"])){color-scheme:dark;
      --plane:#0d0d0d;--card:#161616;--surface:#1a1a19;--line:#2a2a28;--hair:#2c2c2a;--axis:#383835;
      --ink:#f0efec;--ink2:#d6d5cc;--mut:#a9a7a0;--hover:#1f2733;
      --s1:#3987e5;--s1-soft:#1c3554;--acc:#3b82f6;
      --good:#0ca30c;--good-ink:#3fcf3f;--good-bg:#10260f;--crit:#d03b3b;--crit-ink:#ff8a80;--crit-bg:#2d1414;
      --o1:#9ec5f4;--o2:#3987e5;--o3:#1c5cab;--o0:#4a4a46;
      --h1:#143a1c;--h2:#3d3210;--h3:#45260f;--h4:#4a1a1c;--shadow:none}}
  :root[data-theme="dark"]{color-scheme:dark;
      --plane:#0d0d0d;--card:#161616;--surface:#1a1a19;--line:#2a2a28;--hair:#2c2c2a;--axis:#383835;
      --ink:#f0efec;--ink2:#d6d5cc;--mut:#a9a7a0;--hover:#1f2733;
      --s1:#3987e5;--s1-soft:#1c3554;--acc:#3b82f6;
      --good:#0ca30c;--good-ink:#3fcf3f;--good-bg:#10260f;--crit:#d03b3b;--crit-ink:#ff8a80;--crit-bg:#2d1414;
      --o1:#9ec5f4;--o2:#3987e5;--o3:#1c5cab;--o0:#4a4a46;
      --h1:#143a1c;--h2:#3d3210;--h3:#45260f;--h4:#4a1a1c;--shadow:none}
  *{box-sizing:border-box}
  body{margin:0;background:var(--plane);color:var(--ink);font-family:'Noto Sans Thai',system-ui,-apple-system,"Segoe UI",sans-serif;font-size:15.5px;padding-left:148px}
  /* เมนูหลัก (เหมือนหน้าอื่น) */
  .side{position:fixed;left:0;top:0;bottom:0;width:148px;background:var(--card);border-right:1px solid var(--line);padding:14px 10px;display:flex;flex-direction:column;gap:6px;z-index:20}
  .side .menu{display:flex;align-items:center;gap:9px;text-decoration:none;font-weight:700;font-size:16px;color:var(--ink);padding:11px 12px;border-radius:10px}
  .side .menu:hover{background:var(--hover)}
  .side .menu.on{background:#2563eb;color:#fff}
  @media (max-width:820px){body{padding-left:0}
    .side{position:static;width:auto;flex-direction:row;border-right:0;border-bottom:1px solid var(--line);padding:8px 10px}
    .side .menu{flex:1;justify-content:center;padding:9px 6px;font-size:14.5px}}
  header{background:var(--card);border-bottom:1px solid var(--line);padding:14px 22px;position:sticky;top:0;z-index:10}
  .hd{display:flex;flex-wrap:wrap;gap:12px 18px;align-items:center}
  .ttl h1{font-size:21px;margin:0;font-weight:700;letter-spacing:-.2px}
  .ttl p{margin:2px 0 0;font-size:14px;color:var(--mut)}
  .grow{flex:1}
  .seg{display:inline-flex;background:var(--plane);border:1px solid var(--line);border-radius:10px;padding:3px}
  .seg button{border:0;background:transparent;padding:6px 12px;border-radius:7px;font:inherit;font-size:14.5px;font-weight:600;color:var(--ink2);cursor:pointer}
  .seg button.on{background:var(--card);color:var(--ink);box-shadow:var(--shadow)}
  .rng{display:flex;align-items:center;gap:6px}
  input,select{font:inherit;font-size:15px;padding:7px 10px;border-radius:9px;border:1px solid var(--line);background:var(--card);color:var(--ink)}
  .btn{font:inherit;font-size:15px;font-weight:600;padding:7px 14px;border-radius:9px;border:1px solid var(--acc);background:var(--acc);color:#fff;cursor:pointer}
  main{padding:18px 22px 40px;transition:opacity .15s}
  main.busy{opacity:.55;pointer-events:none}
  .fbar{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin-bottom:10px}
  .fbar .lbl{font-size:14px;color:var(--mut);margin-right:2px}
  .chips{display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin-bottom:14px;min-height:4px}
  .chip{font:inherit;font-size:14px;font-weight:600;border-radius:999px;padding:4px 10px;border:1px solid var(--line);background:var(--card);color:var(--ink2);cursor:pointer}
  .chip.f{background:#eaf1fe;border-color:#bfd5fb;color:#1d4ed8}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])) .chip.f{background:#14243a;border-color:#24497a;color:#9ec5f4}}
  /* การ์ด */
  .tiles{display:grid;grid-template-columns:minmax(300px,1.4fr) repeat(3,minmax(0,1fr));gap:12px;margin-bottom:12px}
  .tile{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:14px 16px;box-shadow:var(--shadow);min-width:0}
  .tile .l{font-size:14px;color:var(--ink2);font-weight:600}
  .tile .v{font-size:28.5px;font-weight:700;line-height:1.15;margin-top:6px;letter-spacing:-.3px}
  .tile .v small{font-size:14.5px;font-weight:600;color:var(--mut);margin-left:4px;letter-spacing:0}
  .tile .s{font-size:13.5px;color:var(--mut);margin-top:3px}
  .tile.hero{grid-row:span 2;display:flex;flex-direction:column;justify-content:center}
  .hero .v{font-size:42.5px}
  .pbar{display:flex;gap:2px;height:8px;border-radius:4px;overflow:hidden;background:var(--hair);margin:10px 0 8px}
  .pbar i{display:block;height:100%}
  .leg2{display:flex;flex-wrap:wrap;gap:6px 16px;font-size:14.5px;color:var(--ink2)}
  .leg2 span{cursor:pointer;border-radius:6px;padding:1px 4px}
  .leg2 span:hover{background:var(--hover)}
  .leg2 b{color:var(--ink);font-variant-numeric:tabular-nums}
  .ico{display:inline-flex;align-items:center;justify-content:center;width:16px;height:16px;border-radius:50%;font-size:11px;font-weight:700;color:#fff;margin-right:5px;vertical-align:-2px}
  @media (max-width:1100px){.tiles{grid-template-columns:repeat(3,minmax(0,1fr))}.tile.hero{grid-column:1/-1;grid-row:auto}}
  @media (max-width:640px){.tiles{grid-template-columns:repeat(2,minmax(0,1fr))}}
  .panels{display:grid;grid-template-columns:repeat(12,1fr);gap:12px;margin-bottom:12px}
  .panel{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px 18px;box-shadow:var(--shadow);min-width:0}
  .w8{grid-column:span 8}.w4{grid-column:span 4}.w12{grid-column:span 12}
  .col2{display:flex;flex-direction:column;gap:12px;min-width:0}
  .col2 .panel{flex:1}
  @media (max-width:1100px){.w8,.w4{grid-column:span 12}}
  .ph{display:flex;align-items:baseline;gap:10px;flex-wrap:wrap;margin-bottom:12px}
  .ph h3{margin:0;font-size:16px;font-weight:700}
  .ph .sub{font-size:14px;color:var(--mut)}
  .legend{display:flex;flex-wrap:wrap;gap:4px 14px;font-size:14px;color:var(--ink2);margin-left:auto}
  .legend i{display:inline-block;vertical-align:-1px;margin-right:6px}
  /* กราฟช่วงเวลา (ต่ำสุด–สูงสุด + จุดเฉลี่ย) */
  .rc{display:grid;grid-template-columns:110px 1fr 150px;align-items:center;gap:12px}
  .rrow{display:contents}
  .rrow > *{padding:9px 0;border-bottom:1px solid var(--hair)}
  .rrow:hover > *{background:var(--hover)}
  .rrow.on > *{background:#eaf1fe}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])) .rrow.on > *{background:#14243a}}
  .rname{font-weight:700;font-size:15px;padding-left:6px !important;cursor:pointer}
  .rplot{position:relative;height:30px;cursor:pointer}
  .grid i{position:absolute;top:0;bottom:0;width:1px;background:var(--hair)}
  .rband{position:absolute;top:12px;height:6px;border-radius:3px;background:var(--s1-soft)}
  .rdot{position:absolute;top:9px;width:12px;height:12px;margin-left:-6px;border-radius:50%;background:var(--s1);box-shadow:0 0 0 2px var(--card)}
  .rend{position:absolute;top:10px;width:2px;height:10px;background:var(--s1);opacity:.55;margin-left:-1px}
  .rstat{font-size:14px;color:var(--ink2);text-align:right;padding-right:6px !important;font-variant-numeric:tabular-nums;cursor:pointer}
  .rstat b{color:var(--ink)}
  .axis{position:relative;height:18px;font-size:12.5px;color:var(--mut);font-variant-numeric:tabular-nums}
  .axis span{position:absolute;transform:translateX(-50%)}
  /* แท่งแนวนอนชุดเดียว */
  .bars{display:grid;grid-template-columns:minmax(80px,180px) 1fr 84px;align-items:center;column-gap:12px}
  .brow{display:contents}
  .brow > *{padding:7px 0;border-bottom:1px solid var(--hair)}
  .brow:hover > *{background:var(--hover)}
  .brow.on > *{background:#eaf1fe}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])) .brow.on > *{background:#14243a}}
  .blab{font-size:14.5px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;padding-left:6px !important;cursor:pointer}
  .btrack{position:relative;height:24px;cursor:pointer}
  .bfill{position:absolute;left:0;top:7px;height:10px;background:var(--s1);border-radius:0 4px 4px 0;min-width:2px}
  .bval{font-size:14px;color:var(--ink2);text-align:right;padding-right:6px !important;font-variant-numeric:tabular-nums;white-space:nowrap}
  .bval b{color:var(--ink)}
  /* สัดส่วนสาย */
  .stack{display:flex;gap:2px;height:14px;border-radius:4px;overflow:hidden;margin:6px 0 14px}
  .stack i{display:block;height:100%;cursor:pointer}
  .clist{display:grid;grid-template-columns:auto 1fr auto auto;gap:8px 12px;font-size:14.5px;align-items:center}
  .clist .sw{width:11px;height:11px;border-radius:3px}
  .clist .n{font-variant-numeric:tabular-nums;font-weight:700;text-align:right}
  .clist .p{font-variant-numeric:tabular-nums;color:var(--mut);text-align:right;min-width:40px}
  .clist .row{display:contents;cursor:pointer}
  .clist .row:hover > *{background:var(--hover)}
  .clist .row.on > *{text-decoration:underline}
  /* ตาราง */
  .tw{border:1px solid var(--line);border-radius:10px;overflow:auto;max-height:560px;background:var(--card)}
  table{border-collapse:separate;border-spacing:0;width:100%;font-size:14.5px}
  th,td{padding:8px 11px;border-bottom:1px solid var(--hair);text-align:left;white-space:nowrap}
  th{position:sticky;top:0;background:var(--card);z-index:1;font-size:13px;font-weight:700;color:var(--mut);letter-spacing:.3px;border-bottom:1px solid var(--line)}
  tbody tr:hover td{background:var(--hover)}
  td.n,th.n{text-align:right}
  td.n{font-variant-numeric:tabular-nums}
  td.k{cursor:pointer;font-weight:700}
  td.k:hover{text-decoration:underline}
  .pill{display:inline-flex;align-items:center;gap:4px;font-size:13px;font-weight:700;padding:2px 8px;border-radius:999px}
  .pill.ok{background:var(--good-bg);color:var(--good-ink)}
  .pill.bad{background:var(--crit-bg);color:var(--crit-ink)}
  td.h1{background:var(--h1)}td.h2{background:var(--h2)}td.h3{background:var(--h3)}td.h4{background:var(--h4)}
  .tools{display:flex;align-items:center;gap:10px;margin-bottom:10px;flex-wrap:wrap}
  .empty{padding:30px;text-align:center;color:var(--mut);font-size:15px}
  .err{background:var(--crit-bg);color:var(--crit-ink);padding:10px 14px;border-radius:10px;margin-bottom:12px}
  .note{color:var(--mut);font-size:14px;margin:4px 0 0}
  @media (max-width:820px){
    header{padding:10px 12px;position:static}
    .hd{gap:8px}
    .ttl h1{font-size:19px}
    .hd .grow{display:none}
    .seg{width:100%}.seg button{flex:1;padding:7px 4px}
    .rng{width:100%}.rng input{flex:1;min-width:0}
    .btn{width:100%}
    main{padding:12px 10px 30px}
    .fbar select{flex:1 1 45%;min-width:0}
    .fbar .lbl{width:100%}
    .tile{padding:12px}.tile .v{font-size:24.5px}.hero .v{font-size:36px}
    .panel{padding:12px}
    .rc{grid-template-columns:72px 1fr 92px;gap:8px}
    .rname{font-size:14px}.rstat{font-size:13px}
    .bars{grid-template-columns:minmax(70px,110px) 1fr 72px;column-gap:8px}
    .blab{font-size:13.5px}.bval{font-size:13px}
    .legend{margin-left:0;width:100%}
    #q{min-width:0 !important;width:100%}
  }
  #tip{position:fixed;z-index:50;pointer-events:none;background:#111827;color:#f9fafb;font-size:14px;line-height:1.5;padding:7px 10px;border-radius:8px;box-shadow:0 4px 14px rgba(0,0,0,.25);max-width:280px;display:none}
  /* สีแยกตามสิ่งที่แสดง (สีติดตัวต้นทาง/ประเภทรถ เสมอ ไม่เปลี่ยนตามลำดับ) + แถบสีบนการ์ด */
  .tile{position:relative;overflow:hidden}
  .tile::before{content:"";position:absolute;left:0;right:0;top:0;height:3px;background:var(--tc,#2a78d6)}
  .tile .l{display:flex;align-items:center;gap:8px}
  .tile .ic{width:28px;height:28px;border-radius:8px;display:inline-flex;align-items:center;justify-content:center;font-size:16px;
            background:color-mix(in srgb,var(--tc,#2a78d6) 14%,transparent)}
  .tile.hero{background:linear-gradient(135deg,var(--hb,var(--good-bg)) 0%,var(--card) 70%)}
  .tile.hero::before{background:var(--hc,var(--good))}
  .rband{background:color-mix(in srgb,var(--oc,var(--s1)) 28%,transparent)}
  .rdot{background:var(--oc,var(--s1))}
  .rend{background:var(--oc,var(--s1))}
  .rname i,.blab i{display:inline-block;width:9px;height:9px;border-radius:50%;margin-right:7px;vertical-align:1px;background:var(--oc,var(--s1))}
  .bfill{background:var(--oc,var(--s1))}
  /* หัวคอลัมน์: กดครั้งแรกเรียงน้อย→มาก กดอีกครั้งมาก→น้อย */
  th.cs{cursor:pointer;user-select:none}
  th.cs:hover{color:var(--ink)}
  th.cs .ar{display:inline-block;width:12px;margin-left:3px;font-size:11px;opacity:.35}
  th.cs:hover .ar{opacity:.7}
  th.cs.act{color:#1d4ed8}
  th.cs.act .ar{opacity:1}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])) th.cs.act{color:#9ec5f4}}
  /* เวลาอยู่ในสถานี: แยกกลุ่มตามประเภทงาน */
  /* กลุ่มเรียงแบบคอลัมน์ไหล (ไม่มีช่องว่าง) · กว้างพอ = 2 คอลัมน์ · มือถือ = 1 */
  .dgrid{display:flex;gap:24px;align-items:stretch}
  .dcol{flex:1 1 0;min-width:0;display:flex;flex-direction:column;gap:16px}
  .dcol .dgrp:last-child{flex:1 1 auto}
  .dgrp{border:1px solid var(--line);border-radius:12px;overflow:hidden;background:var(--card)}
  .dgh{display:flex;align-items:center;gap:10px;padding:10px 14px;cursor:pointer;border-top:4px solid var(--oc);
       background:color-mix(in srgb,var(--oc) 9%,var(--card))}
  .dgh:hover{background:color-mix(in srgb,var(--oc) 16%,var(--card))}
  .dgh.on{box-shadow:inset 0 0 0 2px #2563eb}
  .dgh .nm{font-size:15.5px;font-weight:700;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
  .dgh .st{margin-left:auto;text-align:right;line-height:1.25;white-space:nowrap}
  .dgh .st b{font-size:18px}
  .dgh .st small{display:block;font-size:13px;color:var(--mut)}
  .dgrp .bars{grid-template-columns:minmax(150px,42%) 1fr 78px;column-gap:0;padding:4px 6px 6px}
  .dgrp .brow > *{padding:8px 0}
  .dgrp .brow:last-child > *{border-bottom:0}
  .dgrp .blab{white-space:normal;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;line-height:1.35;padding:6px 12px 6px 8px !important}
  .dgrp .btrack{height:auto;align-self:stretch}
  .dgrp .bfill{top:50%;margin-top:-5px}
  .dgrp .bval{padding-left:10px !important}
  .dmore{font-size:13.5px;color:var(--mut);padding:2px 14px 10px}
  @media (max-width:820px){ .dgrid{flex-direction:column;gap:16px} .dgrp .bars{grid-template-columns:minmax(96px,40%) 1fr 66px} .dgh .st b{font-size:16px} }
  /* เวลารอโหลดแยกต้นทาง: แถวละต้นทาง ตัวเลขชัด แท่ง = เฉลี่ย ใต้แท่ง = ต่ำสุด/สูงสุด · แถวยืดเต็มการ์ด */
  .fillp{display:flex;flex-direction:column}
  .fillp > #cOrigin{flex:1;display:flex;flex-direction:column}
  .oc{flex:1;display:flex;flex-direction:column;gap:8px}
  .orow{flex:1 1 auto;min-height:64px;display:grid;grid-template-columns:minmax(110px,170px) 1fr 165px;align-items:center;gap:16px;
        padding:10px 14px;border:1px solid var(--line);border-radius:10px;cursor:pointer;background:var(--card)}
  .orow:hover{background:var(--hover)}
  .orow.on{box-shadow:0 0 0 2px #2563eb}
  .orow .on1{font-size:16px;font-weight:700}
  .orow .on2{font-size:13.5px;color:var(--mut);margin-top:2px}
  .orow .otr{display:flex;height:24px;border-radius:7px;background:var(--plane);overflow:hidden}
  .orow .osg{height:100%;display:flex;align-items:center;justify-content:center;font-size:14px;font-weight:700;color:#fff;white-space:nowrap;overflow:hidden;min-width:2px}
  .orow .osg.w{background:var(--wc)}
  .orow .osg.l{background:var(--lc);box-shadow:inset 2px 0 0 var(--card)}
  .orow .omm .w b{color:var(--wc)} .orow .omm .l b{color:var(--lc)}
  .legend i.lw{width:12px;height:12px;border-radius:3px;background:var(--wc)}
  .legend i.ll{width:12px;height:12px;border-radius:3px;background:var(--lc)}
  .orow .omm{display:flex;justify-content:space-between;font-size:13.5px;color:var(--ink2);margin-top:6px}
  .orow .omm b{font-weight:700;color:var(--ink)}
  .orow .oav{text-align:right;line-height:1.15}
  .orow .oav b{font-size:25.5px;font-weight:700}
  .orow .oav small{display:block;font-size:13px;color:var(--mut)}
  @media (max-width:820px){ .orow{grid-template-columns:1fr 92px;gap:6px 10px} .orow .obar{grid-column:1 / -1;grid-row:2} .orow .oav b{font-size:21px} }
  /* คำอธิบายใต้หัวกราฟ ให้คนอ่านครั้งแรกเข้าใจ */
  .hint{margin:-4px 0 12px;font-size:14px;line-height:1.55;color:var(--ink2);background:var(--plane);border-radius:8px;padding:7px 11px}
  .hint b{color:var(--ink)}
  .hk{display:inline-block;padding:0 7px;border-radius:5px;margin:0 2px;color:var(--ink);font-weight:600}
  /* แยกสีกลุ่มคอลัมน์แบบ Looker: รอโหลด = ม่วงอ่อน · โหลด = ชมพู */
  :root{--cw:#f1eafb;--cwh:#dccbf5;--cl:#fdebf2;--clh:#f8c9dc;--wc:#7c5cd6;--lc:#d6487f}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])){--cw:#241d36;--cwh:#3b2f5c;--cl:#33192a;--clh:#552a42}}
  :root[data-theme="dark"]{--cw:#241d36;--cwh:#3b2f5c;--cl:#33192a;--clh:#552a42}
  th.gw{background:var(--cwh) !important;color:var(--ink) !important}
  th.gl{background:var(--clh) !important;color:var(--ink) !important}
  td.cw{background:var(--cw)}
  td.cl{background:var(--cl)}
  tr.grp th{position:static;text-align:center;font-size:13.5px;border-bottom:0}
  .w6{grid-column:span 6}
  @media (max-width:1100px){.w6{grid-column:span 12}}
  .pie{display:flex;align-items:center;gap:22px;flex-wrap:wrap}
  .pie svg{flex:0 0 auto;width:190px;height:190px}
  .pie svg circle{cursor:pointer;transition:opacity .15s}
  .pie svg:hover circle{opacity:.55}
  .pie svg circle:hover{opacity:1}
  .pie .ctr1{font-size:27.5px;font-weight:700;fill:var(--ink)}
  .pie .ctr2{font-size:13.5px;fill:var(--mut)}
  .plist{flex:1;min-width:220px;display:flex;flex-direction:column;gap:2px}
  .plist .pr{display:grid;grid-template-columns:14px 1fr auto 46px;gap:8px;align-items:center;padding:6px 8px;border-radius:8px;font-size:14.5px;cursor:pointer}
  .plist .pr:hover{background:var(--hover)}
  .plist .pr.on{background:#eaf1fe}
  .plist .pr .sw{width:12px;height:12px;border-radius:3px}
  .plist .pr .n{font-weight:700;text-align:right}
  .plist .pr .pc{color:var(--mut);text-align:right}
  .pdly{display:inline-block;margin-left:6px;padding:0 6px;border-radius:999px;font-size:12.5px;font-weight:700;background:var(--crit-bg);color:var(--crit)}
  .btn2{font:inherit;font-size:15px;font-weight:600;padding:7px 14px;border-radius:9px;border:1px solid var(--line);background:var(--card);color:var(--ink);cursor:pointer;white-space:nowrap}
  .btn2:hover{background:var(--hover)}
  .btn2:disabled{opacity:.6;cursor:wait}
  @media (max-width:820px){ .btn2{width:100%} }
  .snapcap{display:flex;justify-content:space-between;gap:12px;flex-wrap:wrap;align-items:baseline;padding:4px 2px 12px}
  .snapcap b{font-size:19px}
  .snapcap span{font-size:14px;color:var(--mut)}
  .side .menu.out{margin-top:auto;color:var(--mut);font-size:14.5px;white-space:nowrap}
  @media (max-width:820px){ .side .menu.out{flex:0 0 auto;margin-top:0} .side .menu.out span{display:none} }
  /* เทียบช่วงก่อน ▲▼ : สีบอกดี/แย่ + ลูกศร + ข้อความ (ไม่ใช้สีอย่างเดียว) */
  .dl{margin-top:5px;font-size:13px;font-weight:600;display:flex;gap:6px;align-items:baseline;flex-wrap:wrap}
  .dl.good{color:#0a8a0a}.dl.bad{color:#c62f2f}.dl.same,.dl.nt{color:var(--ink2)}
  .dl small{font-weight:400;color:var(--mut);font-size:12px}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])) .dl.good{color:#2fc22f} :root:where(:not([data-theme="light"])) .dl.bad{color:#f06a6a}}
  .cmpnote{font-size:13px;color:var(--mut);margin:-2px 2px 8px}
  /* แนวโน้มรายวัน: 2 กราฟเส้นแยกกัน (หน่วยต่างกัน ไม่ใช้แกนคู่) */
  .tgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(420px,100%),1fr));gap:18px 28px}
  .tchart h4{margin:0 0 6px;font-size:14.5px}
  .tchart svg{width:100%;height:auto;display:block;overflow:visible}
  .tchart .gl{stroke:var(--line);stroke-width:1}
  .tchart .ax{fill:var(--mut);font-size:11px}
  .tchart .pt{cursor:pointer}
  .tchart .lg{display:flex;gap:14px;font-size:13px;color:var(--ink2);margin-top:4px}
  .tchart .lg i{display:inline-block;width:14px;height:3px;border-radius:2px;vertical-align:middle;margin-right:6px}
  [hidden]{display:none !important}
</style>
</head>
<body>
<aside class="side">
  <a class="menu" href="/">🚛 เช็กรถ</a>
  <a class="menu" href="/plan">📋 แผนงาน</a>
  <a class="menu on" href="/report">📊 รายงาน On Time</a>
  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>
</aside>
<header><div class="hd">
  <div class="ttl"><h1>รายงาน On Time</h1><p id="stamp">ข้อมูลจากชีตแผนงานจริง · อ่านอย่างเดียว</p></div>
  <span class="grow"></span>
  <div class="seg" id="presets">
    <button data-p="0">วันนี้</button><button data-p="1">เมื่อวาน</button><button data-p="7">7 วัน</button><button data-p="30">30 วัน</button>
  </div>
  <div class="rng"><input type="date" id="dFrom" aria-label="ตั้งแต่วันที่"><span style="color:var(--mut)">–</span><input type="date" id="dTo" aria-label="ถึงวันที่"></div>
  <button class="btn" id="go">ดูรายงาน</button>
  <button class="btn2" id="snap" title="บันทึกหน้ารายงานเป็นรูป เพื่อส่งต่อทาง LINE / อีเมล">📷 แคปส่ง</button>
</div></header>
<main id="main">
  <div class="fbar" data-nosnap="1">
    <span class="lbl">ตัวกรอง</span>
    <select id="fOrigin"><option value="">ต้นทาง: ทั้งหมด</option></select>
    <select id="fVtype"><option value="">ประเภทรถ: ทั้งหมด</option></select>
    <select id="fCar"><option value="">เบอร์รถ: ทั้งหมด</option></select>
    <select id="fDrop"><option value="">Drop: ทั้งหมด</option></select>
    <select id="fStatus"><option value="">On Time: ทั้งหมด</option><option value="PASS">PASS</option><option value="Delay">Delay</option></select>
  </div>
  <div class="chips" id="active" data-nosnap="1"></div>
  <div id="err" class="err" hidden></div>
  <div class="cmpnote" id="cmpNote"></div>
  <div class="tiles" id="tiles"></div>
  <section class="panel" id="trendP" hidden style="margin-bottom:12px"><div class="ph"><h3>แนวโน้มรายวัน</h3><span class="sub" id="trendSub"></span></div>
    <p class="hint">💡 ดูว่าแต่ละวันเพิ่มขึ้นหรือลดลง · <b>On Time ยิ่งสูงยิ่งดี</b> · <b>เวลารอโหลด/โหลด ยิ่งต่ำยิ่งดี</b> · ชี้ที่จุดเพื่อดูตัวเลข</p>
    <div class="tgrid"><div class="tchart" id="tOt"></div><div class="tchart" id="tWl"></div></div></section>
  <div class="panels">
    <section class="panel w8 fillp"><div class="ph"><h3>เวลารอโหลด + โหลดสินค้า แยกตามต้นทาง</h3><span class="sub">นาที (เฉลี่ย)</span>
      <div class="legend"><span><i class="lw"></i>รอโหลดสินค้า</span><span><i class="ll"></i>โหลดสินค้า</span></div></div>
      <p class="hint">💡 แท่งเดียวต่อกัน: <b style="color:var(--wc)">ม่วง = รอโหลด</b> (เข้าลาน → เริ่มโหลด) ต่อด้วย <b style="color:var(--lc)">ชมพู = โหลด</b> (เริ่มโหลด → โหลดเสร็จ) · ตัวเลขขวา = รวมเวลาอยู่ที่ต้นทาง · <b>แท่งยิ่งยาว = อยู่นาน</b> · กดแถวเพื่อกรอง</p>
      <div id="cOrigin"></div></section>
    <div class="w4 col2">
      <section class="panel"><div class="ph"><h3>สัดส่วนตามระยะทาง</h3></div>
        <p class="hint">💡 งานแบ่งตามระยะทางต้นทาง → ปลายทาง: <b>ใกล้</b> ไม่เกิน 80 กม. · <b>กลาง</b> 81–250 · <b>ไกล</b> เกิน 250 กม. · กดสีเพื่อกรอง</p>
        <div id="cClass"></div></section>
      <section class="panel"><div class="ph"><h3>จำนวนเที่ยวตามประเภทรถ</h3></div><p class="hint">💡 รถแต่ละขนาดวิ่งไปกี่เที่ยวในช่วงวันที่ที่เลือก</p><div id="cVtype"></div></section>
    </div>
    <section class="panel w12"><div class="ph"><h3>สรุปตามต้นทาง</h3><span class="sub">นาที</span></div><p class="hint">💡 <b>รอโหลด</b> = เข้าลาน → เริ่มโหลด · <b>โหลด</b> = เริ่มโหลด → โหลดเสร็จ · ต่ำสุด / สูงสุด / เฉลี่ย ของแต่ละต้นทาง · กดหัวคอลัมน์เพื่อเรียง</p>
      <div class="tw" style="max-height:none"><table><thead><tr class="grp"><th colspan="2"></th><th colspan="3" class="gw">⏳ เวลารอโหลดสินค้า (นาที)</th><th colspan="3" class="gl">⛽ เวลาโหลดสินค้า (นาที)</th></tr><tr id="oHead"></tr></thead><tbody id="tOrigin"></tbody></table></div></section>
    <section class="panel w6"><div class="ph"><h3>สาเหตุ On Time / ล่าช้า</h3><span class="sub" id="whySub"></span></div><p class="hint">💡 จากคอลัมน์ <b>สาเหตุ On Time</b> ในชีต · นับเป็นจำนวนงาน · กดชื่อสาเหตุเพื่อดูงานนั้น</p><div id="cWhy"></div></section>
    <section class="panel w6"><div class="ph"><h3>สาเหตุแก้ไขงาน</h3><span class="sub" id="fixSub"></span></div><p class="hint">💡 จากคอลัมน์ <b>สาเหตุแก้ไขงาน</b> ในชีต · เช่น ลูกค้ายกเลิก, ปลายทางใหม่ · กดชื่อสาเหตุเพื่อดูงานนั้น</p><div id="cFix"></div></section>
    <section class="panel w12"><div class="ph"><h3>เวลาที่อยู่ในสถานี (เฉลี่ย)</h3><span class="sub">นาที</span></div><p class="hint">💡 รถจอดอยู่ที่ปลายทางนานเท่าไร (<b>ถึงปลายทาง → ออกจากปลายทาง</b>) แยกตามประเภทงาน · <b>ตัวเลขมาก = ลงของนาน</b> · เรียงจากนานสุดลงมา · กดหัวการ์ดหรือชื่อปลายทางเพื่อกรอง</p><div id="cDest"></div></section>
    <section class="panel w12" data-nosnap="1"><div class="tools"><h3 style="margin:0;font-size:16px">รายการทั้งหมด</h3><span class="sub" id="rowCount" style="font-size:14px;color:var(--mut)"></span><span class="grow"></span>
      <input type="search" id="q" placeholder="ค้นหา รถ / ปลายทาง / ออเดอร์" style="min-width:260px"></div>
      <p class="hint">💡 ทุกงาน (drop) ในช่วงวันที่ที่เลือก · <b>กดหัวคอลัมน์</b> เพื่อเรียงน้อย→มาก / มาก→น้อย · <b>กดเบอร์รถ</b> เพื่อดูเฉพาะคันนั้น · ช่องค้นหาด้านบนพิมพ์เบอร์รถ/ปลายทาง/ออเดอร์ได้</p>
      <div class="tw"><table><thead><tr id="rowsHead"></tr></thead>
        <tbody id="rows"></tbody></table></div>
</section>
  </div>
</main>
<div id="tip"></div>
<script>
let REP = null;
const XF = {dest: '', cls: '', jtype: '', why: '', fix: ''};
const SELMAP = {origin: 'fOrigin', vtype: 'fVtype', car: 'fCar', drop: 'fDrop', status: 'fStatus'};
const FNAME = {origin: 'ต้นทาง', vtype: 'ประเภทรถ', car: 'เบอร์รถ', drop: 'Drop', status: 'On Time', jtype: 'ประเภทงาน', why: 'สาเหตุ On Time', fix: 'สาเหตุแก้ไขงาน', dest: 'ปลายทาง', cls: 'สาย'};
const CLS = [['สายใกล้', '#1baf7a'], ['สายกลาง', '#eda100'], ['สายไกล', '#6250d6'], ['ไม่ทราบระยะ', 'var(--o0)']];
const CAT = ['#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#e87ba4', '#008300', '#6250d6', '#e34948'];   // ชุดสีที่ผ่านการตรวจตาบอดสี (ลำดับคงที่)
const ORIGINS = ['SC BPK', 'BSRC', 'PTT TANK', 'IRPC', 'UAC', 'PTT KK', 'PTT NSW', 'PTT SRT'];
const VCOL = {'08 Tons': '#1baf7a', '10 Tons': '#2a78d6', 'Trailer': '#eb6834'};
function hashc(s){ let h = 0; for(let i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) % 997; return CAT[h % CAT.length]; }
function ocol(o){ const i = ORIGINS.indexOf(o); return i >= 0 ? CAT[i] : hashc(o); }          // สีติดตัวต้นทาง
function vcol(v){ return VCOL[v] || hashc(v); }
function esc(s){ return String(s == null ? '' : s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c])); }
function iso(d){ return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'); }
function cm(v){ return v == null ? null : Math.ceil(Number(v) - 1e-9) + 0; }     // นาที: ปัดขึ้นเป็นจำนวนเต็ม (12.1 → 13)
function num(v, d){ if(v == null) return '–'; if(d == null) return cm(v).toLocaleString('en-US'); return Number(v).toLocaleString('en-US', {maximumFractionDigits: d}); }
function sub2(what, v){ return what + (hm(v) ? ' · ' + hm(v) : ''); }
function hm(v){ if(v == null) return ''; const m = cm(v); return m >= 60 ? '≈ ' + Math.floor(m / 60) + ' ชม. ' + (m % 60) + ' นาที' : ''; }
function getF(k){ return SELMAP[k] ? document.getElementById(SELMAP[k]).value : XF[k]; }
function setF(k, v){
  if(SELMAP[k]){
    const el = document.getElementById(SELMAP[k]);
    if(v && ![...el.options].some(o => o.value === v)){ const o = document.createElement('option'); o.value = v; o.textContent = v; el.appendChild(o); }
    el.value = v;
  }else XF[k] = v;
}
function fill(sel, vals, label){
  const el = document.getElementById(sel), cur = el.value;
  el.innerHTML = '<option value="">' + label + ': ทั้งหมด</option>' + vals.map(v => '<option>' + esc(v) + '</option>').join('');
  el.value = vals.indexOf(cur) >= 0 ? cur : '';
}
function setRange(a, b){ document.getElementById('dFrom').value = iso(a); document.getElementById('dTo').value = iso(b); markPreset(); }
function markPreset(){
  const f = document.getElementById('dFrom').value, t = document.getElementById('dTo').value, today = iso(new Date());
  document.querySelectorAll('#presets button').forEach(b => {
    const p = Number(b.dataset.p), a = new Date(), z = new Date();
    if(p === 1){ a.setDate(a.getDate() - 1); z.setDate(z.getDate() - 1); } else if(p > 1) a.setDate(a.getDate() - (p - 1));
    b.classList.toggle('on', iso(a) === f && iso(z) === t);
  });
}
async function load(keepFilters){
  const q = new URLSearchParams({from: document.getElementById('dFrom').value, to: document.getElementById('dTo').value,
    origin: getF('origin'), vtype: getF('vtype'), car: getF('car'), drop: getF('drop'), status: getF('status'), dest: XF.dest, cls: XF.cls, jtype: XF.jtype, why: XF.why, fix: XF.fix});
  const err = document.getElementById('err'); err.hidden = true;
  const main = document.getElementById('main'); main.classList.add('busy');
  try{
    const r = await fetch('/api/report/ontime?' + q.toString());
    if(r.status === 401){ location.href = '/login'; return; }
    if(!r.ok){ let m = 'HTTP ' + r.status; try{ m = (await r.json()).detail || m; }catch(e){} throw new Error(m); }
    REP = await r.json();
    if(!keepFilters){
      fill('fOrigin', REP.filters.origins, 'ต้นทาง'); fill('fVtype', REP.filters.vtypes, 'ประเภทรถ');
      fill('fCar', REP.filters.cars, 'เบอร์รถ'); fill('fDrop', REP.filters.drops, 'Drop');
    }
    render();
    document.getElementById('stamp').textContent = 'ข้อมูลจากชีตแผนงานจริง · อ่านอย่างเดียว · อัปเดต ' + new Date().toLocaleTimeString('th-TH', {hour: '2-digit', minute: '2-digit'});
  }catch(e){ err.textContent = 'โหลดรายงานไม่สำเร็จ: ' + e.message; err.hidden = false; }
  finally{ main.classList.remove('busy'); }
}
function renderActive(){
  const keys = Object.keys(FNAME).filter(k => getF(k));
  document.getElementById('active').innerHTML = keys.length ?
    keys.map(k => '<button class="chip f" data-clr="' + k + '">' + FNAME[k] + ': ' + esc(getF(k)) + '  ✕</button>').join('') +
    '<button class="chip" data-clr="*">ล้างตัวกรองทั้งหมด</button>' : '';
}
function tile(label, value, unit, sub, extra, color, icon, delta){
  return '<div class="tile' + (extra || '') + '" style="--tc:' + (color || '#2a78d6') + '"><div class="l">' + (icon ? '<span class="ic">' + icon + '</span>' : '') + label + '</div><div class="v">' + value + (unit ? '<small>' + unit + '</small>' : '') + '</div>' +
    (sub ? '<div class="s">' + sub + '</div>' : '') + (delta || '') + '</div>';
}
// เทียบกับช่วงก่อน: better = 'low' (ต่ำดี เช่น นาที) / 'high' (สูงดี เช่น %) / '' (แค่บอกขึ้นลง)
function delta(cur, prev, unit, better, dp){      // "เพิ่มขึ้น X นาที" (แดง) / "ลดลง X นาที" (เขียว) / "เท่าเดิม" · เที่ยว/drop ไม่ใส่สี
  if(!REP.prev || cur == null || prev == null) return '';
  const r = v => dp ? Math.round(v * 10) / 10 : cm(v);
  const d = Math.round((r(cur) - r(prev)) * 10) / 10, tip = esc('ช่วงก่อน ' + num(prev, dp ? 1 : null) + unit);
  if(d === 0) return '<div class="dl same" data-tip="' + tip + '">เท่าเดิม</div>';
  const cls = better === 'low' ? (d < 0 ? 'good' : 'bad') : 'nt';
  return '<div class="dl ' + cls + '" data-tip="' + tip + '">' + (d > 0 ? 'เพิ่มขึ้น ' : 'ลดลง ') + Math.abs(d).toLocaleString('en-US') + unit + '</div>';
}
function pctOf(k){ const j = k.pass + k.delay; return j ? k.pass / j * 100 : null; }
// กราฟเส้นรายวัน (SVG) — series: [{name, color, get}] · fmt: แสดงค่า
function lineChart(elId, title, days, series, unit, yMax){
  const W = 600, H = 210, L = 38, R = 10, T = 10, B = 26, iw = W - L - R, ih = H - T - B;
  const vals = []; series.forEach(sr => days.forEach(d => { const v = sr.get(d); if(v != null) vals.push(v); }));
  const mx0 = Math.max.apply(null, vals.concat([1])), st = yMax ? 25 : niceStep(mx0), top = yMax || Math.ceil(mx0 / st) * st;
  const x = i => L + (days.length > 1 ? i / (days.length - 1) * iw : iw / 2), y = v => T + ih - v / top * ih;
  let g = '';
  for(let v = 0; v <= top + 1e-9; v += st){ const yy = y(v); g += '<line class="gl" x1="' + L + '" x2="' + (W - R) + '" y1="' + yy + '" y2="' + yy + '"/><text class="ax" x="' + (L - 6) + '" y="' + (yy + 4) + '" text-anchor="end">' + Math.round(v) + '</text>'; }
  const step = Math.max(1, Math.ceil(days.length / 8));
  days.forEach((d, i) => { if(i % step === 0 || i === days.length - 1) g += '<text class="ax" x="' + x(i) + '" y="' + (H - 6) + '" text-anchor="middle">' + d.date.slice(8, 10) + '/' + d.date.slice(5, 7) + '</text>'; });
  series.forEach(sr => {
    let path = '', pen = false;
    days.forEach((d, i) => { const v = sr.get(d); if(v == null){ pen = false; return; } path += (pen ? 'L' : 'M') + x(i).toFixed(1) + ' ' + y(v).toFixed(1); pen = true; });
    g += '<path d="' + path + '" fill="none" stroke="' + sr.color + '" stroke-width="2.5" stroke-linejoin="round" stroke-linecap="round"/>';
    days.forEach((d, i) => { const v = sr.get(d); if(v == null) return;
      const tip = dmy(d.date) + ' · ' + sr.name + ' ' + (unit === '%' ? num(v, 1) : num(v)) + unit + (sr.extra ? ' · ' + sr.extra(d) : '');
      g += '<circle class="pt" cx="' + x(i) + '" cy="' + y(v) + '" r="4" fill="' + sr.color + '" style="stroke:var(--card)" stroke-width="2" data-tip="' + esc(tip) + '"/>' +
           '<circle cx="' + x(i) + '" cy="' + y(v) + '" r="12" fill="transparent" data-tip="' + esc(tip) + '"/>'; });
  });
  document.getElementById(elId).innerHTML = '<h4>' + title + '</h4><svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' + esc(title) + '">' + g + '</svg>' +
    (series.length > 1 ? '<div class="lg">' + series.map(sr => '<span><i style="background:' + sr.color + '"></i>' + sr.name + '</span>').join('') + '</div>' : '');
}
function drawTrend(){
  const days = REP.by_day || [], P = document.getElementById('trendP');
  P.hidden = days.length < 2;
  if(P.hidden) return;
  document.getElementById('trendSub').textContent = dmy(days[0].date) + ' – ' + dmy(days[days.length - 1].date);
  lineChart('tOt', 'On Time (%) รายวัน', days, [{name: 'On Time', color: '#0a8a0a', get: d => d.pct, extra: d => 'PASS ' + d.pass + ' · Delay ' + d.delay}], '%', 100);
  lineChart('tWl', 'เวลารอโหลด / โหลด เฉลี่ยรายวัน (นาที)', days,
    [{name: 'รอโหลด', color: '#7c5cd6', get: d => d.wait == null ? null : cm(d.wait)}, {name: 'โหลด', color: '#d6487f', get: d => d.load == null ? null : cm(d.load)}], ' นาที');
}
function niceStep(mx){
  const steps = [5, 10, 15, 20, 30, 60, 90, 120, 180, 240, 360, 480, 720, 960, 1440];
  return steps.find(s => mx / s <= 6) || 1440;
}
function render(){
  renderActive();
  const k = REP.kpi, judged = k.pass + k.delay, pct = judged ? k.pass / judged * 100 : null, pk = REP.prev ? REP.prev.kpi : {}, tgt = REP.target || 95;
  document.getElementById('cmpNote').textContent = REP.prev ? 'เพิ่มขึ้น / ลดลง = เทียบกับช่วงก่อน: ' + (REP.prev.from === REP.prev.to ? dmy(REP.prev.from) : dmy(REP.prev.from) + ' – ' + dmy(REP.prev.to)) : '';
  document.getElementById('tiles').innerHTML =
    '<div class="tile hero" style="' + (pct != null && pct < tgt ? '--hb:var(--crit-bg);--hc:var(--crit)' : '') + '"><div class="l"><span class="ic" style="background:var(--good-bg)">⏱️</span>On Time</div><div class="v">' + (pct == null ? '–' : Math.round(pct * 10) / 10 + '%') + '</div>' +
      '<div class="pbar" data-tip="PASS ' + k.pass + ' · Delay ' + k.delay + '"><i style="width:' + (pct || 0) + '%;background:var(--good)"></i><i style="width:' + (judged ? 100 - pct : 0) + '%;background:var(--crit)"></i></div>' +
      '<div class="leg2"><span data-k="status" data-v="PASS"><span class="ico" style="background:var(--good)">✓</span>PASS <b>' + num(k.pass, 0) + '</b></span>' +
      '<span data-k="status" data-v="Delay"><span class="ico" style="background:var(--crit)">!</span>Delay <b>' + num(k.delay, 0) + '</b></span>' +
      '<span style="cursor:default;color:var(--mut)">จาก ' + num(judged, 0) + ' drop ที่มีผลในชีต</span></div>' +
      (pct == null ? '' : '<div class="dl ' + (pct >= tgt ? 'good' : 'bad') + '" data-tip="' + esc('เป้า On Time ' + tgt + '% ขึ้นไป' + (REP.prev && pctOf(REP.prev.kpi) != null ? ' · ช่วงก่อน ' + num(pctOf(REP.prev.kpi), 1) + '%' : '')) + '">' +
        (pct >= tgt ? 'ผ่านเป้า ' + tgt + '%' : 'ต่ำกว่าเป้า ' + tgt + '%') + '</div>') +
      '<div class="s" style="margin-top:6px">💡 <b>PASS</b> = ส่งถึงลูกค้าไม่ช้าเกิน 30 นาที · <b>Delay</b> = ช้าเกิน 30 นาที · <b>เป้า ' + tgt + '% ขึ้นไป</b></div></div>' +
    tile('จำนวนเที่ยว', num(k.trips, 0), '', REP.from === REP.to ? dmy(REP.from) : dmy(REP.from) + ' – ' + dmy(REP.to), '', '#2a78d6', '🚚', delta(k.trips, pk.trips, ' เที่ยว', 'high')) +
    tile('งานทั้งหมด (drop)', num(REP.n_rows, 0), '', 'จุดส่งทั้งหมด · มีผล On Time ' + num(judged, 0), '', '#6250d6', '📦', delta(REP.n_rows, REP.prev && REP.prev.n_rows, ' drop', 'high')) +
    tile('รอโหลดสินค้า (เฉลี่ย)', num(k.wait), 'นาที', sub2('เข้าลาน → เริ่มโหลด', k.wait), '', '#7c5cd6', '⏳', delta(k.wait, pk.wait, ' นาที', 'low')) +
    tile('โหลดสินค้า (เฉลี่ย)', num(k.load), 'นาที', sub2('เริ่มโหลด → โหลดเสร็จ', k.load), '', '#d6487f', '⛽', delta(k.load, pk.load, ' นาที', 'low')) +
    tile('เดินทางไปปลายทาง (เฉลี่ย)', num(k.travel), 'นาที', sub2('ออกคลัง → ถึงปลายทาง', k.travel), '', '#1baf7a', '🛣️', delta(k.travel, pk.travel, ' นาที', 'low')) +
    tile('อยู่ที่สถานี / ส่งสินค้า (เฉลี่ย)', num(k.unload), 'นาที', sub2('ถึงปลายทาง → ออกปลายทาง', k.unload), '', '#eda100', '🏁', delta(k.unload, pk.unload, ' นาที', 'low'));
  drawOrigin(); drawClass();
  bars('cVtype', REP.by_vtype, x => x.vtype, x => x.trips, ' เที่ยว', 'vtype', x => x.vtype + ': ' + x.trips + ' เที่ยว', x => vcol(x.vtype));
  drawDest(); drawWhy(); drawTrend();
  drawOriginTable();
  drawRows();
}
// ── เรียงตาราง: กดหัวคอลัมน์ ครั้งแรก น้อย→มาก · อีกครั้ง มาก→น้อย (ค่าว่างอยู่ท้ายเสมอ) ──
function toNum(v){ if(v == null || v === '') return null; const n = Number(String(v).replace(/,/g, '')); return isNaN(n) ? null : n; }
function hhmm(v){ const m = String(v || '').split(':'); return m.length > 1 ? String(m[0]).trim().padStart(2, '0') + ':' + m[1].slice(0, 2) : String(v || ''); }
const SORTS = {o: null, r: null};
function sortList(list, cols, st){
  if(!st) return list;
  const c = cols.find(x => x.k === st.k);
  return list.slice().sort((a, b) => {
    const va = c.v(a), vb = c.v(b), ea = va == null || va === '', eb = vb == null || vb === '';
    if(ea || eb) return ea === eb ? 0 : ea ? 1 : -1;
    return (c.n ? va - vb : String(va).localeCompare(String(vb), 'th', {numeric: true})) * st.dir;
  });
}
function headHtml(cols, tbl){
  const st = SORTS[tbl];
  return cols.map(c => '<th class="cs' + (c.n ? ' n' : '') + (c.g ? ' g' + c.g : '') + (st && st.k === c.k ? ' act' : '') + '" data-tbl="' + tbl + '" data-col="' + c.k + '" title="กดเพื่อเรียง">' +
    c.t + '<span class="ar">' + (st && st.k === c.k ? (st.dir > 0 ? '▲' : '▼') : '⇅') + '</span></th>').join('');
}
const OCOLS = [
  {k: 'origin', t: 'ต้นทาง', v: o => o.origin}, {k: 'trips', t: 'เที่ยว', n: 1, v: o => o.trips},
  {k: 'wmin', t: 'ต่ำสุด', n: 1, g: 'w', v: o => o.wait.min}, {k: 'wmax', t: 'สูงสุด', n: 1, g: 'w', v: o => o.wait.max}, {k: 'wavg', t: 'เฉลี่ย', n: 1, g: 'w', v: o => o.wait.avg},
  {k: 'lmin', t: 'ต่ำสุด', n: 1, g: 'l', v: o => o.load.min}, {k: 'lmax', t: 'สูงสุด', n: 1, g: 'l', v: o => o.load.max}, {k: 'lavg', t: 'เฉลี่ย', n: 1, g: 'l', v: o => o.load.avg}];
const RCOLS = [
  {k: 'car', t: 'เบอร์รถ', v: x => x.car}, {k: 'date', t: 'วันที่', v: x => x.date}, {k: 'order', t: 'เลขออเดอร์', v: x => x.order},
  {k: 'origin', t: 'ต้นทาง', v: x => x.origin}, {k: 'jtype', t: 'ประเภทงาน', v: x => x.jtype}, {k: 'dest', t: 'ปลายทาง', v: x => x.dest}, {k: 'vtype', t: 'ประเภท', v: x => x.vtype},
  {k: 'drop', t: 'Drop', n: 1, v: x => toNum(x.drop)}, {k: 'weight', t: 'น้ำหนัก', n: 1, v: x => toNum(x.weight)},
  {k: 'sched', t: 'เวลาส่ง', v: x => hhmm(x.sched)},
  {k: 'arrive', t: 'ถึงปลายทาง', v: x => x.arrive ? x.arrive.slice(6, 10) + x.arrive.slice(3, 5) + x.arrive.slice(0, 2) + x.arrive.slice(10) : ''},
  {k: 'ontime', t: 'On Time', v: x => x.ontime}, {k: 'late', t: 'ช้า (นาที)', n: 1, v: x => toNum(x.late)},
  {k: 'wait', t: 'รอโหลด', n: 1, v: x => x.wait}, {k: 'load', t: 'โหลด', n: 1, v: x => x.load},
  {k: 'travel', t: 'เดินทาง', n: 1, v: x => x.travel}, {k: 'unload', t: 'ส่งสินค้า', n: 1, v: x => x.unload}];
document.addEventListener('click', e => {
  const th = e.target.closest ? e.target.closest('th.cs') : null;
  if(!th || !REP) return;
  const t = th.dataset.tbl, k = th.dataset.col, st = SORTS[t];
  SORTS[t] = {k: k, dir: st && st.k === k && st.dir > 0 ? -1 : 1};
  if(t === 'o') drawOriginTable(); else drawRows();
});
function drawOriginTable(){
  document.getElementById('oHead').innerHTML = headHtml(OCOLS, 'o');
  document.getElementById('tOrigin').innerHTML = sortList(REP.by_origin, OCOLS, SORTS.o).map(o => '<tr><td class="k" data-k="origin" data-v="' + esc(o.origin) + '">' + esc(o.origin) + '</td><td class="n">' + o.trips + '</td>' +
    '<td class="n cw">' + num(o.wait.min) + '</td><td class="n cw">' + num(o.wait.max) + '</td><td class="n cw"><b>' + num(o.wait.avg) + '</b></td>' +
    '<td class="n cl">' + num(o.load.min) + '</td><td class="n cl">' + num(o.load.max) + '</td><td class="n cl"><b>' + num(o.load.avg) + '</b></td></tr>').join('') ||
    '<tr><td colspan="8" class="empty">ไม่มีข้อมูล</td></tr>';
}
function dmy(s){ return s ? s.slice(8, 10) + '/' + s.slice(5, 7) + '/' + s.slice(0, 4) : ''; }
function drawOrigin(){
  const list = REP.by_origin.filter(o => o.wait.n || o.load.n);
  if(!list.length){ document.getElementById('cOrigin').innerHTML = '<div class="empty">ไม่มีข้อมูลเวลารอโหลด/โหลด</div>'; return; }
  const tot = o => (cm(o.wait.avg) || 0) + (cm(o.load.avg) || 0);      // รวม = ผลรวมของตัวเลขที่ปัดแล้ว ให้บวกกันตรงกับที่เห็น
  const mx = Math.max.apply(null, list.map(tot).concat([1])), sel = getF('origin');
  const seg = (cls, v, t) => { const w = v / mx * 100; return v ? '<div class="osg ' + cls + '" style="width:' + w + '%">' + (w > 9 ? num(v) : '') + '</div>' : ''; };
  document.getElementById('cOrigin').innerHTML = '<div class="oc">' + list.map(o => {
    const w = o.wait, l = o.load, t = tot(o);
    const tip = o.origin + ' · ' + o.trips + ' เที่ยว · รอโหลดเฉลี่ย ' + num(w.avg) + ' (ต่ำสุด ' + num(w.min) + ' / สูงสุด ' + num(w.max) + ') · โหลดเฉลี่ย ' + num(l.avg) + ' (ต่ำสุด ' + num(l.min) + ' / สูงสุด ' + num(l.max) + ') นาที';
    return '<div class="orow' + (sel === o.origin ? ' on' : '') + '" data-k="origin" data-v="' + esc(o.origin) + '" data-tip="' + esc(tip) + '">' +
      '<div><div class="on1">' + esc(o.origin) + '</div><div class="on2">' + o.trips + ' เที่ยว</div></div>' +
      '<div class="obar"><div class="otr">' + seg('w', w.avg, 'รอโหลด') + seg('l', l.avg, 'โหลด') + '</div>' +
        '<div class="omm"><span class="w">รอโหลด <b>' + num(w.avg) + '</b> <small>(' + num(w.min) + '–' + num(w.max) + ')</small></span>' +
        '<span class="l">โหลด <b>' + num(l.avg) + '</b> <small>(' + num(l.min) + '–' + num(l.max) + ')</small></span></div></div>' +
      '<div class="oav"><b>' + num(t) + '</b> นาที<small>รวมที่ต้นทาง' + (hm(t) ? ' ' + hm(t) : '') + '</small></div></div>';
  }).join('') + '</div>';
}
function drawClass(){
  const m = {}; REP.by_class.forEach(c => { m[c.cls] = c.n; });
  const tot = REP.by_class.reduce((a, c) => a + c.n, 0), sel = XF.cls;
  if(!tot){ document.getElementById('cClass').innerHTML = '<div class="empty">ไม่มีข้อมูล</div>'; return; }
  const parts = CLS.filter(c => m[c[0]]);
  document.getElementById('cClass').innerHTML =
    '<div class="stack">' + parts.map(c => '<i data-k="cls" data-v="' + c[0] + '" data-tip="' + c[0] + ': ' + m[c[0]] + ' (' + Math.round(m[c[0]] / tot * 100) + '%)" style="flex:' + m[c[0]] + ';background:' + c[1] + '"></i>').join('') + '</div>' +
    '<div class="clist">' + parts.map(c => '<div class="row' + (sel === c[0] ? ' on' : '') + '" data-k="cls" data-v="' + c[0] + '"><span class="sw" style="background:' + c[1] + '"></span><span>' + c[0] +
      '</span><span class="n">' + num(m[c[0]], 0) + '</span><span class="p">' + Math.round(m[c[0]] / tot * 100) + '%</span></div>').join('') + '</div>';
}
// สีประจำประเภทงาน (ติดตัวประเภท ไม่เปลี่ยนตามลำดับ)
const JCOL = {'OLP : Station': '#2a78d6', 'ลูกค้า : Industry': '#eb6834', 'ATL : โรงบรรจุ': '#1baf7a', 'ATL : Tranfer': '#eda100',
              'ลูกค้า : Station': '#e87ba4', 'ลูกค้า : โรงบรรจุ': '#008300'};
function jname(j){ return j || '(ไม่ระบุ)'; }
function jcol(j){ return j ? (JCOL[j] || hashc(j)) : '#9ca3af'; }
// กราฟวงกลม (โดนัท) สาเหตุ: 5 อันดับแรก + อื่นๆ (ชี้ที่ "อื่นๆ" เพื่อดูรายการ)
const PCOL = ['#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#e87ba4', '#9ca3af'];
function donut(elId, subId, list, key, unitWord){
  const el = document.getElementById(elId), tot = list.reduce((a, x) => a + x.n, 0), sel = getF(key);
  document.getElementById(subId).textContent = tot ? num(tot, 0) + ' งาน · ' + list.length + ' สาเหตุ' : '';
  if(!tot){ el.innerHTML = '<div class="empty">ไม่มีการบันทึกสาเหตุในช่วงวันที่นี้</div>'; return; }
  const top = list.slice(0, 5), rest = list.slice(5);
  const parts = top.map((x, i) => ({t: x.why, n: x.n, c: PCOL[i], k: key, x: x}));
  if(rest.length) parts.push({t: 'อื่นๆ (' + rest.length + ' สาเหตุ)', n: rest.reduce((a, x) => a + x.n, 0), c: PCOL[5],
    tip: rest.map(x => x.why + ' ' + x.n).join(' · ')});
  const R = 70, C = 2 * Math.PI * R; let off = 0;
  const arcs = parts.map(p => {
    const len = p.n / tot * C, gap = parts.length > 1 ? Math.min(2, len / 3) : 0;
    const tip = p.tip || (p.t + ' · ' + p.n + ' งาน (' + Math.round(p.n / tot * 100) + '%)' + (p.x && p.x.delay != null ? ' · Delay ' + p.x.delay : '') + (p.x && p.x.cancel ? ' · ยกเลิก ' + p.x.cancel : ''));
    const h = '<circle r="' + R + '" cx="95" cy="95" fill="none" stroke="' + p.c + '" stroke-width="' + (sel && sel === p.t ? 34 : 28) + '" stroke-dasharray="' + Math.max(0.5, len - gap) + ' ' + (C - len + gap) +
      '" stroke-dashoffset="' + (-off) + '" transform="rotate(-90 95 95)"' + (p.k ? ' data-k="' + p.k + '" data-v="' + esc(p.t) + '"' : '') + ' data-tip="' + esc(tip) + '"></circle>';
    off += len; return h;
  }).join('');
  el.innerHTML = '<div class="pie"><svg viewBox="0 0 190 190" role="img" aria-label="สาเหตุ">' + arcs +
    '<text x="95" y="93" text-anchor="middle" class="ctr1">' + num(tot, 0) + '</text><text x="95" y="113" text-anchor="middle" class="ctr2">' + unitWord + '</text></svg>' +
    '<div class="plist">' + parts.map(p => '<div class="pr' + (sel && sel === p.t ? ' on' : '') + '"' + (p.k ? ' data-k="' + p.k + '" data-v="' + esc(p.t) + '"' : '') + (p.tip ? ' data-tip="' + esc(p.tip) + '"' : '') + '>' +
      '<span class="sw" style="background:' + p.c + '"></span><span>' + esc(p.t) + '</span><span class="n">' + p.n + '</span><span class="pc">' + Math.round(p.n / tot * 100) + '%</span></div>').join('') + '</div></div>';
}
function drawWhy(){ donut('cWhy', 'whySub', REP.by_why || [], 'why', 'งานที่มีสาเหตุ'); donut('cFix', 'fixSub', REP.by_fix || [], 'fix', 'งานที่แก้ไข'); }
function drawDest(){
  const el = document.getElementById('cDest'), TOP = 8;
  const list = REP.by_dest.filter(d => d.unload != null);
  if(!list.length){ el.innerHTML = '<div class="empty">ไม่มีข้อมูลเวลาเข้า–ออกปลายทาง</div>'; return; }
  const mx = Math.max.apply(null, list.map(d => d.unload).concat([1])), sel = getF('dest'), jsel = getF('jtype');
  const groups = (REP.by_jtype || []).filter(g => list.some(d => d.jtype === g.jtype));
  const card = g => {
    const ds = list.filter(d => d.jtype === g.jtype), c = jcol(g.jtype), nm = jname(g.jtype), gmx = Math.max.apply(null, ds.map(d => d.unload).concat([1]));
    return '<div class="dgrp" style="--oc:' + c + '">' +
      '<div class="dgh' + (jsel === nm ? ' on' : '') + '" data-k="jtype" data-v="' + esc(nm) + '" data-tip="' + esc(nm + ' · อยู่ที่สถานีเฉลี่ย ' + num(g.unload) + ' นาที · ' + g.drops + ' drop') + '">' +
        '<span class="nm">' + esc(nm) + '</span><span class="st"><b>' + num(g.unload) + '</b> นาที<small>เฉลี่ย · ' + ds.length + ' ปลายทาง · ' + g.drops + ' drop</small></span></div>' +
      '<div class="bars">' + ds.slice(0, TOP).map(x =>
        '<div class="brow' + (sel === x.dest ? ' on' : '') + '" style="--oc:' + c + '" data-k="dest" data-v="' + esc(x.dest) + '" data-tip="' + esc(nm + ' · ' + x.dest + ' · อยู่ที่สถานีเฉลี่ย ' + num(x.unload) + ' นาที · ' + x.n + ' drop') + '">' +
        '<div class="blab" title="' + esc(x.dest) + '"><i></i>' + esc(x.dest) + '</div><div class="btrack"><div class="bfill" style="width:' + Math.max(0.5, x.unload / gmx * 100) + '%"></div></div>' +
        '<div class="bval"><b>' + num(x.unload) + '</b> นาที</div></div>').join('') + '</div>' +
      (ds.length > TOP ? '<div class="dmore">+ อีก ' + (ds.length - TOP) + ' ปลายทาง (ดูในตารางด้านล่าง)</div>' : '') + '</div>';
  };
  // แบ่ง 2 คอลัมน์ให้สูงใกล้กัน (กลุ่มใหญ่ลงคอลัมน์ที่เตี้ยกว่า) แล้วยืดการ์ดสุดท้ายให้จบเสมอกัน
  const cols = [[], []], hgt = [0, 0];
  groups.map(g => ({g: g, h: 2 + Math.min(TOP, list.filter(d => d.jtype === g.jtype).length)})).sort((a, b) => b.h - a.h)
    .forEach(x => { const i = hgt[0] <= hgt[1] ? 0 : 1; cols[i].push(x.g); hgt[i] += x.h; });
  cols.forEach(c => c.sort((a, b) => b.drops - a.drops));
  el.innerHTML = '<div class="dgrid">' + cols.filter(c => c.length).map(c => '<div class="dcol">' + c.map(card).join('') + '</div>').join('') + '</div>';
}
function bars(el, list, label, val, unit, key, tip, color){
  if(!list.length){ document.getElementById(el).innerHTML = '<div class="empty">ไม่มีข้อมูล</div>'; return; }
  const mx = Math.max.apply(null, list.map(val).concat([1])), sel = getF(key);
  document.getElementById(el).innerHTML = '<div class="bars">' + list.map(x => {
    const v = val(x);
    return '<div class="brow' + (sel === label(x) ? ' on' : '') + '" style="--oc:' + color(x) + '" data-k="' + key + '" data-v="' + esc(label(x)) + '" data-tip="' + esc(tip(x)) + '">' +
      '<div class="blab"><i></i>' + esc(label(x)) + '</div><div class="btrack"><div class="bfill" style="width:' + Math.max(0.5, v / mx * 100) + '%"></div></div>' +
      '<div class="bval"><b>' + num(v) + '</b>' + unit + '</div></div>';
  }).join('') + '</div>';
}
function drawRows(){
  const q = document.getElementById('q').value.trim().toLowerCase();
  document.getElementById('rowsHead').innerHTML = headHtml(RCOLS, 'r');
  const rows = sortList(REP.rows.filter(x => !q || [x.car, x.dest, x.order, x.origin, x.job].join(' ').toLowerCase().indexOf(q) >= 0), RCOLS, SORTS.r);
  document.getElementById('rowCount').textContent = 'แสดง ' + num(rows.length, 0) + ' จาก ' + num(REP.n_rows, 0) + ' แถว' + (REP.n_rows > REP.rows.length ? ' (สูงสุด ' + REP.rows.length + ' แถวแรก)' : '');
  document.getElementById('rows').innerHTML = rows.map(x => '<tr><td class="k" data-k="car" data-v="' + esc(x.car) + '">' + esc(x.car) + '</td><td>' + dmy(x.date) + '</td><td>' + esc(x.order) +
    '</td><td>' + esc(x.origin) + '</td><td><span style="display:inline-block;width:8px;height:8px;border-radius:50%;margin-right:6px;background:' + jcol(x.jtype) + '"></span>' + esc(jname(x.jtype)) + '</td><td title="' + esc(x.dest) + '">' + esc(x.dest.length > 30 ? x.dest.slice(0, 29) + '…' : x.dest) + '</td><td>' + esc(x.vtype) + '</td><td class="n">' + esc(x.drop) +
    '</td><td class="n">' + esc(x.weight) + '</td><td>' + esc(x.sched) + '</td><td>' + esc(x.arrive) + '</td><td>' +
    (x.ontime === 'PASS' ? '<span class="pill ok">✓ PASS</span>' : x.ontime === 'Delay' ? '<span class="pill bad">! Delay</span>' : '<span style="color:var(--mut)">–</span>') +
    '</td><td class="n">' + esc(x.late) + '</td><td class="n">' + num(x.wait) + '</td><td class="n">' + num(x.load) +
    '</td><td class="n">' + num(x.travel) + '</td><td class="n">' + num(x.unload) + '</td></tr>').join('') ||
    '<tr><td colspan="17" class="empty">ไม่มีงานในช่วงวันที่/ตัวกรองที่เลือก</td></tr>';
}
// ทูลทิป: ชี้ที่กราฟ/แท่งเพื่อดูตัวเลข (ตัวเลขเดียวกันมีในตารางด้านล่างด้วย)
const TIP = document.getElementById('tip');
document.addEventListener('mousemove', e => {
  const t = e.target.closest ? e.target.closest('[data-tip]') : null;
  if(!t){ TIP.style.display = 'none'; return; }
  TIP.textContent = t.dataset.tip; TIP.style.display = 'block';
  const x = Math.min(e.clientX + 14, innerWidth - TIP.offsetWidth - 8), y = e.clientY + 16 + TIP.offsetHeight > innerHeight ? e.clientY - TIP.offsetHeight - 10 : e.clientY + 16;
  TIP.style.left = x + 'px'; TIP.style.top = y + 'px';
});
// คลิกกราฟ/ตาราง = กรองทั้งหน้า (คลิกซ้ำ = ยกเลิก)
document.getElementById('main').addEventListener('click', e => {
  const c = e.target.closest('[data-clr]');
  if(c){ const k = c.dataset.clr; if(k === '*') Object.keys(FNAME).forEach(x => setF(x, '')); else setF(k, ''); load(true); return; }
  const t = e.target.closest('[data-k]');
  if(!t) return;
  const k = t.dataset.k, v = t.dataset.v;
  setF(k, getF(k) === v ? '' : v); load(true);
});
document.querySelectorAll('#presets button').forEach(b => { b.onclick = () => {
  const p = Number(b.dataset.p), a = new Date(), z = new Date();
  if(p === 1){ a.setDate(a.getDate() - 1); z.setDate(z.getDate() - 1); } else if(p > 1) a.setDate(a.getDate() - (p - 1));
  setRange(a, z); load();
}; });
document.getElementById('go').onclick = () => load();
// ── แคปส่ง: บันทึกหน้ารายงาน (การ์ด + กราฟ + ตารางสรุป) เป็นรูป PNG · มือถือเปิดหน้าแชร์ (LINE ฯลฯ) ได้เลย ──
let H2I = null;
function loadH2I(){
  if(H2I) return H2I;
  H2I = new Promise((ok, bad) => {
    const sc = document.createElement('script');
    sc.src = 'https://cdn.jsdelivr.net/npm/html-to-image@1.11.11/dist/html-to-image.js';
    sc.integrity = 'sha384-UbfRVKN3/elS1r7JcK2FhmPP+KlJ4CvYwbyYD7tH+uTkbT9bNJr9eJeQ0FoFbAgz';
    sc.crossOrigin = 'anonymous';
    sc.onload = () => ok(window.htmlToImage);
    sc.onerror = () => { H2I = null; bad(new Error('โหลดตัวแคปไม่ได้')); };
    document.head.appendChild(sc);
  });
  return H2I;
}
document.getElementById('snap').onclick = async () => {
  if(!REP) return;
  const b = document.getElementById('snap'), main = document.getElementById('main');
  b.disabled = true; b.textContent = '⏳ กำลังแคป…';
  const keys = Object.keys(FNAME).filter(k => getF(k));
  const cap = document.createElement('div'); cap.className = 'snapcap';
  const rng = REP.from === REP.to ? dmy(REP.from) : dmy(REP.from) + ' – ' + dmy(REP.to);
  cap.innerHTML = '<b>รายงาน On Time · ' + rng + '</b><span>' + (keys.length ? 'กรอง: ' + keys.map(k => FNAME[k] + ' ' + esc(getF(k))).join(' · ') + ' · ' : '') +
    'แคปเมื่อ ' + new Date().toLocaleString('th-TH', {dateStyle: 'short', timeStyle: 'short'}) + '</span>';
  main.insertBefore(cap, main.firstChild);
  try{
    const lib = await loadH2I();
    const blob = await lib.toBlob(main, {pixelRatio: 2, skipFonts: true, backgroundColor: getComputedStyle(document.body).backgroundColor,
      filter: n => !(n.dataset && n.dataset.nosnap)});
    const name = 'ontime_' + REP.from + (REP.to !== REP.from ? '_' + REP.to : '') + '.png';
    const file = new File([blob], name, {type: 'image/png'});
    if(navigator.canShare && navigator.canShare({files: [file]}) && matchMedia('(pointer:coarse)').matches){
      try{ await navigator.share({files: [file], title: 'รายงาน On Time ' + rng}); }catch(e){}
    }else{
      const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name;
      document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1500);
    }
  }catch(e){
    alert('แคปไม่สำเร็จ: ' + (e && e.message ? e.message : e) + ' — ลองใหม่อีกครั้ง หรือใช้ปุ่มแคปหน้าจอของเครื่องแทน');
  }finally{
    cap.remove(); b.disabled = false; b.textContent = '📷 แคปส่ง';
  }
};
['dFrom', 'dTo'].forEach(id => { document.getElementById(id).onchange = () => { markPreset(); load(); }; });
['fOrigin', 'fVtype', 'fCar', 'fDrop', 'fStatus'].forEach(id => { document.getElementById(id).onchange = () => load(true); });
document.getElementById('q').oninput = () => { if(REP) drawRows(); };
setRange(new Date(), new Date());
load();
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
  .side .menu.out{margin-top:auto;color:var(--mut);font-size:13px;white-space:nowrap}
  @media (max-width:820px){ .side .menu.out{flex:0 0 auto;margin-top:0} .side .menu.out span{display:none} }
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
  .nt{white-space:normal;line-height:1.35;font-size:13px;display:-webkit-box;-webkit-line-clamp:3;-webkit-box-orient:vertical;overflow:hidden;word-break:break-word}
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
  td[data-pend]{opacity:.6;font-style:italic}
  td.pres{outline:2px solid #f59e0b;outline-offset:-2px;position:relative}
  td.pres::after{content:attr(data-who);position:absolute;top:-1px;right:0;background:#f59e0b;color:#fff;font-size:10px;line-height:13px;padding:0 4px;border-radius:3px;white-space:nowrap;font-style:normal;font-weight:600}
  .savebadge{position:fixed;left:164px;bottom:18px;background:#f59e0b;color:#fff;padding:8px 14px;border-radius:10px;
             font-weight:700;z-index:80;box-shadow:0 4px 14px rgba(0,0,0,.25)}
  .savebadge.ok{background:#16a34a}
  .savebadge[hidden]{display:none}
  @media (max-width:820px){.savebadge{left:12px}}
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
  .imp td[data-sel]{outline:2px solid #2563eb;outline-offset:-2px;position:relative}
  .imp td[data-sel] .fh{position:absolute;right:0;bottom:0;width:11px;height:11px;background:#2563eb;border:1px solid #fff;cursor:crosshair}
  .imp td.idrag{background:#dbeafe}
  .imp .impsearch{display:flex;align-items:center;gap:8px;margin:8px 0;flex-wrap:wrap}
  .imp .impsearch .sw{position:relative;display:inline-flex;align-items:center}
  .imp .impsearch .ico{position:absolute;left:11px;pointer-events:none;opacity:.65}
  .imp .impsearch input[type=search]{min-width:300px;padding-left:34px;padding-right:34px}
  .imp .impsearch .clr{position:absolute;right:6px;border:0;background:transparent;padding:2px 7px;border-radius:999px;cursor:pointer;color:var(--mut)}
  .imp .impsearch .clr:hover{background:var(--line)}
  .imp .impsearch .cnt{background:var(--chg-bg);color:var(--chg-ink);border:1px solid var(--chg-line);border-radius:999px;padding:3px 12px;font-size:12.5px;font-weight:600}
  .imp mark{background:#fde047;color:#111;border-radius:3px;padding:0 1px}
  .imp td[data-ir]{user-select:none}
  .imp td.idsrc{background:#fef3c7;outline:2px dashed #d97706;outline-offset:-2px}
  .imp .undo{margin:0 0 6px 8px;padding:3px 10px;border:1px solid var(--line);border-radius:8px;background:var(--card);cursor:pointer}
  .imp .undo:disabled{opacity:.45;cursor:default}
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
  #colmode .chip{color:var(--ink)}
  #colmode .chip.on{background:#2563eb;color:#fff}          /* ปุ่มสลับมุมมองตาราง: อันที่เลือกอยู่ = พื้นน้ำเงินตัวขาว */
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
  <a class="menu" href="/report">📊 รายงาน On Time</a>
  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>
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
  <button id="editBtn" hidden title="แก้ไขข้อมูลทีละช่อง (คลิกที่ช่อง)">✏️ โหมดแก้ไข</button>
  <button id="impOpen" title="อัปโหลดใบจัดรถ Excel เพื่อตรวจและนำเข้า">📥 นำเข้า Excel</button>
  <button id="pasteOpen" title="คัดลอกตารางที่ลูกค้าให้มา (Excel/อีเมล) แล้ววางเป็นชุด">📋 วางข้อมูลลูกค้า</button>
  <button class="primary" id="go">รีเฟรช</button>
</div></header>
<main>
  <div class="cards" id="cards"></div>
  <div class="chgbar" id="presbar" hidden></div>
  <div class="chgbar" id="edithint" hidden>
    <span>✏️ <b>กำลังอยู่ในโหมดแก้ไข</b> — คลิกที่ช่องเพื่อแก้ · <b>Enter</b> = บันทึกแล้วลงช่องล่าง · <b>Tab</b> = บันทึกแล้วไปช่องขวา · <b>Esc</b> = ยกเลิก ·
      แก้ได้ทุกช่อง A–Z (ช่องที่เป็นสูตรในชีตจะถูกแทนที่ด้วยค่าที่พิมพ์)</span>
  </div>
  <div class="chgbar" id="chgbar" hidden>
    <span id="chgtxt"></span>
    <label><input type="checkbox" id="onlychg"> ดูเฉพาะที่เปลี่ยน</label>
    <button id="ack">รับทราบทั้งหมด</button>
  </div>
  <div class="chips" id="colmode">
    <span class="mut" style="font-size:13px">มุมมองตาราง:</span>
    <button class="chip" id="colCompact" title="แสดงเฉพาะคอลัมน์ที่ใช้จัดรถ ไม่ต้องเลื่อนซ้ายขวา">ย่อ (เฉพาะที่ใช้จัดรถ)</button>
    <button class="chip" id="colAll" title="แสดงครบทุกคอลัมน์ A–Z เหมือนในชีต">ทั้งหมด A–Z</button>
  </div>
  <div class="chips" id="chips"><span class="mut" style="font-size:13px">แสดงคอลัมน์:</span></div>
  <div id="err" class="warn" hidden></div>
  <div class="wrap"><table>
    <thead id="head"></thead>
    <tbody id="rows"></tbody>
  </table></div>
  <p class="mut" style="font-size:13px">ข้อมูลจากชีต "แผนงาน Gasbulk" คอลัมน์ A–Z (อ่านอย่างเดียว) &middot; สีแดง = ยกเลิก/โหลดเก็บ</p>
</main>

<div class="savebadge" id="savebadge" hidden></div>
<div class="imp-back" id="impBack" hidden><div class="imp">
  <div class="imp-h"><b>📥 นำเข้า Excel / 📋 วางข้อมูลลูกค้า</b><button id="impClose" title="ปิด">✕</button></div>
  <p class="mut" style="margin:0 0 8px;font-size:14px">
    เลือกไฟล์ใบจัดรถ (.xlsx) ระบบอ่านชีต "ข้อมูลการจัดส่ง" คอลัมน์ E–AD แล้วแสดงเป็นตาราง
    <b>แก้ข้อมูลในตารางนี้ได้เลยก่อนนำเข้า</b> ยังไม่เขียนอะไรลงชีตจนกว่าคุณจะกดยืนยัน</p>
  <input type="file" id="impFile" accept=".xlsx">
  <div id="pasteBox" style="margin:10px 0;padding:10px;border:1px dashed #94a3b8;border-radius:10px">
    <b>📋 หรือ วางข้อมูลที่ลูกค้าให้มา</b>
    <p class="mut" style="margin:4px 0 6px;font-size:13px">คัดลอกตารางจาก Excel/อีเมล แล้ววางในกล่องนี้ (Ctrl+V) ตามลำดับ 10 คอลัมน์:
      เวลาส่งมอบ · เลขออเดอร์ · เลขโหลด · น้ำหนักบรรทุก · น้ำหนักสุทธิ · ต้นทาง · ปลายทาง · Drop · หมายเหตุ · เบอร์รถ
      (จะมีบรรทัดหัวตารางมาด้วยหรือไม่ก็ได้) ระบบเติมวันที่ เที่ยววิ่ง ทะเบียน และคนขับให้ แล้วให้ตรวจ/แก้ก่อนเขียนลงชีต<br>
      ถ้าวางพร้อมหัวตาราง จะใส่คอลัมน์เพิ่มได้ เช่น <b>เวลาเข้าโหลด (P)</b> · เวลาออกจากฟรีต (P) · เวลาโทรตาม พขร (P) · พขร.1 · พขร.2 · ประเภทรถ
      (ถ้ามีแต่เวลาเข้าโหลด ระบบคำนวณอีกสองช่องให้: ออกจากฟรีต = เข้าโหลด − 30 นาที, โทรตาม พขร = ออกจากฟรีต − 1 ชม.)</p>
    <textarea id="pasteTxt" rows="5" style="width:100%;box-sizing:border-box;font:inherit" placeholder="วางข้อมูลที่นี่ (Ctrl+V)"></textarea>
    <div style="margin-top:6px">วันที่ของงาน: <input type="date" id="pasteDate"> <button id="pasteGo" class="go">ตรวจข้อมูลที่วาง</button></div>
  </div>
  <div id="impBody"></div>
</div></div>
<script>
const SRC_COL = 11;   // L คลังต้นทาง
(function(){                             // สร้าง CSS ความกว้างคอลัมน์ A–Z (ใช้กับหัว+ช่องของตารางหลักและตารางตรวจข้อมูล)
  const W = [[56, 66, 'center'], [150, 200], [100, 116], [60, 76, 'center'], [76, 92, 'center'], [100, 116], [70, 84, 'center'], [130, 170],
             [96, 120], [80, 104, 'right'], [80, 104, 'right'], [84, 104, 'center'], [150, 210], [52, 64, 'center'], [150, 230], [74, 92, 'center'],
             [76, 96, 'center'], [126, 176], [128, 170], [128, 170], [108, 126], [108, 126], [118, 170], [128, 160, 'center'], [128, 160, 'center'], [128, 160, 'center']];
  let css = 'th[data-c],.imp th[data-ic]{white-space:normal;line-height:1.25;vertical-align:bottom}';      // หัวคอลัมน์ขึ้นบรรทัดใหม่ได้ ไม่ต้องกว้างเท่าความยาวของชื่อ
  W.forEach((w, i) => {
    css += 'th[data-c="' + i + '"],td[data-c="' + i + '"],.imp th[data-ic="' + i + '"],.imp td[data-ic="' + i + '"]{min-width:' + w[0] + 'px;max-width:' + w[1] + 'px;' +
           (w[2] ? 'text-align:' + w[2] + ';' : '') + 'overflow:hidden;text-overflow:ellipsis}';
  });
  const st = document.createElement('style'); st.id = 'colw'; st.textContent = css; document.head.appendChild(st);
})();
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

async function load(fresh, quiet){
  if(SAVEQ.length) await PUMP;           // รอให้คิวที่ค้างลงชีตให้หมดก่อน แล้วค่อยอ่านชีตใหม่
  const date = document.getElementById('date').value || todayISO();
  const btn = document.getElementById('go');
  if(fresh && !quiet){ btn.disabled = true; btn.textContent = 'กำลังอ่านชีต...'; }
  // ช่องวันที่ของเบราว์เซอร์อาจโชว์เป็น เดือน/วัน/ปี จึงบอกวันที่แบบไทยกำกับอีกที กันอ่านสลับ
  const wd = ['อาทิตย์','จันทร์','อังคาร','พุธ','พฤหัสบดี','ศุกร์','เสาร์'];
  const dd = new Date(date + 'T00:00:00Z');
  document.getElementById('dlabel').textContent = isNaN(dd) ? '' :
    'วัน' + wd[dd.getUTCDay()] + ' ' + date.slice(8,10) + '/' + date.slice(5,7) + '/' + date.slice(0,4);
  const err = document.getElementById('err'); if(!quiet) err.hidden = true;
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
    if(!quiet){ err.textContent = 'โหลดแผนงานไม่สำเร็จ: ' + e.message; err.hidden = false; }
    return;
  }finally{
    if(!quiet){ btn.disabled = false; btn.textContent = 'รีเฟรช'; }
  }
  // บอกว่าข้อมูลมาจากชีตตอนไหน (ไม่ใช่เวลาที่เปิดหน้า) จะได้รู้ว่าเห็นของล่าสุดหรือยัง
  document.getElementById('stamp').textContent = 'ข้อมูลจากชีตเมื่อ ' + DATA.sheet_read_at +
    (DATA.alt_source ? ' · 🧪 ชีตทดลอง (DEMO)' : '') +
    (fresh && DATA.throttled ? ' (เพิ่งอ่านสดไปไม่นาน รออีกสักครู่แล้วกดใหม่)' : '');
  SAVEQ.forEach(q => {                   // ค่าที่ยังรอลงชีตอยู่ ต้องไม่ถูกข้อมูลที่เพิ่งอ่านใหม่ทับ
    const cur = DATA.rows.find(r => r.row === q.row);
    if(cur){ cur.cells[q.col] = q.value; PENDING[q.row + ',' + q.col] = true; }
  });
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
  const compact = COLMODE === 'compact';
  document.getElementById('chips').hidden = compact;                       // ปุ่มกลุ่มคอลัมน์ใช้เฉพาะมุมมอง "ทั้งหมด"
  document.getElementById('colCompact').classList.toggle('on', compact);
  document.getElementById('colAll').classList.toggle('on', !compact);
  const shown = [];
  if(compact) COMPACT.forEach(i => shown.push(i));
  else GROUPS.forEach(g => { if(ON[g.id]) g.cols.forEach(i => shown.push(i)); });
  let band = '<th class="sk sk1" rowspan="2">แถว</th>';
  if(compact) band += '<th class="g-job" colspan="' + shown.length + '">จัดรถ</th>';
  else GROUPS.forEach(g => {
    if(!ON[g.id]) return;
    band += '<th class="g-' + g.id + '" colspan="' + g.cols.length + '">' + g.name + '</th>';
  });
  document.getElementById('head').innerHTML = '<tr class="g">' + band + '</tr><tr class="h">' +
    shown.map(i => '<th data-c="' + i + '"' + (i === 1 ? ' class="sk sk2"' : '') + '><small>' + DATA.headers[i].col +
      '</small>' + esc(DATA.headers[i].name) + '</th>').join('') + '</tr>';
  document.getElementById('rows').innerHTML = rows.length
    ? rows.map(x => '<tr class="' + (x.cancelled ? 'cx ' : '') + (x.chg ? 'chg' : '') + '"><td class="sk sk1 rn">' +
        x.row + (x.chg ? '<br><span class="tag">' + (x.chg.type === 'new' ? 'ใหม่' : 'แก้') + '</span>' : '') + '</td>' +
        shown.map(i => tdHtml(x, i)).join('') + '</tr>').join('')
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
let WHO = {};                            // "แถว,คอลัมน์" → การแก้ล่าสุดจาก EditLog {by, t, old, new}
function whoChanged(){                   // ชื่อคนที่แก้ช่องที่ไฮไลต์เหลืองอยู่ (ไม่ซ้ำ)
  const set = {};
  DATA.rows.forEach(x => { if(x.chg && x.chg.cols) x.chg.cols.forEach(c => { const w = WHO[x.row + ',' + c]; if(w) set[w.by || 'ไม่ระบุชื่อ'] = 1; }); });
  return Object.keys(set);
}
function changedCount(){                 // จำนวนช่องที่เปลี่ยน + แถวใหม่
  let n = 0;
  DATA.rows.forEach(x => { if(x.chg) n += x.chg.type === 'new' ? 1 : x.chg.cols.length; });
  return n;
}
async function loadWho(){
  try{
    const r = await fetch('/api/plan/recent');
    if(!r.ok) return;
    WHO = {};
    ((await r.json()).edits || []).forEach(e => { WHO[e.row + ',' + COLS.indexOf(e.col)] = e; });   // เรียงเก่า→ใหม่ ตัวล่าสุดทับ
  }catch(e){}
}

// ── รีเฟรชอัตโนมัติ: เพื่อนแก้อะไรไป หน้าเว็บบอกเอง (ไม่ต้องกดรีเฟรช) ──
const AUTO = {ms: 15000, last: 0};
async function autoTick(){
  if(document.hidden || SAVEQ.length || SAVING || !DATA) return;                        // ซ่อนแท็บ/มีคิวค้าง = ข้าม
  if(document.querySelector('#rows input, #rows select')) return;                       // กำลังพิมพ์อยู่ = ไม่รบกวน
  if(!document.getElementById('impBack').hidden) return;                                // เปิดหน้าต่างนำเข้าอยู่ = ข้าม
  const before = changedCount();
  await loadWho();                                                                       // ชื่อผู้แก้ต้องมาก่อน render ใน load
  await load(true, true);
  if(!DATA) return;
  const now = changedCount();
  if(now > before){
    const names = whoChanged();
    toast('👥 ' + (names.length ? names.join(', ') : 'มีคน') + ' แก้ไปแล้ว ' + (now - before) + ' ช่อง (ดูช่องสีเหลืองในตาราง)', false);
  }
}
setInterval(autoTick, AUTO.ms);
document.addEventListener('visibilitychange', () => { if(!document.hidden) autoTick(); });   // กลับมาที่แท็บนี้ = ตรวจทันที

function updateBar(){
  const n = DATA.rows.filter(x => x.chg && x.chg.type === 'new').length;
  const e = DATA.rows.filter(x => x.chg && x.chg.type === 'edit').length;
  const bar = document.getElementById('chgbar');
  bar.hidden = !(n || e || GONE);
  if(bar.hidden) ONLYCHG = false;
  const names = whoChanged();
  document.getElementById('chgtxt').textContent = '🔔 เปลี่ยนตั้งแต่ครั้งก่อนที่คุณดู: ใหม่ ' + n +
    ' · แก้ไข ' + e + (GONE ? ' · หายไป ' + GONE : '') + ' แถว' + (names.length ? ' · แก้โดย ' + names.join(', ') : '');
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

// มุมมองตารางย่อ: เฉพาะคอลัมน์ที่ใช้จัดรถ (เรียงตามลำดับในชีต) — B เลข JOB ตรึงซ้ายเสมอ
const COMPACT = [1, 4, 6, 9, 11, 12, 13, 14, 15, 18, 24];   // B JOB, E เที่ยววิ่ง, G เวลาส่ง, J น้ำหนัก, L ต้นทาง, M ปลายทาง, N Drop, O หมายเหตุ, P เบอร์รถ, S พขร.1, Y เวลาเข้าโหลด(P)
let COLMODE = 'compact';
try{ COLMODE = localStorage.getItem('gb_plan_colmode') === 'all' ? 'all' : 'compact'; }catch(e){}
function setColMode(m){
  COLMODE = m;
  try{ localStorage.setItem('gb_plan_colmode', m); }catch(e){}
  render();
}
document.getElementById('colCompact').onclick = () => setColMode('compact');
document.getElementById('colAll').onclick = () => setColMode('all');

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
  if(i === 14) return '<td><div class="nt" title="' + esc(v) + '">' + esc(v) + '</div></td>';
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
// ── แก้ไขทีละช่อง: คลิก → พิมพ์ → Enter บันทึกลงชีตแล้วลงช่องล่าง / Tab ไปช่องขวา (เซิร์ฟเวอร์ตรวจชนกันก่อนเขียน) ──
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

function tdHtml(x, i){                  // HTML ของช่อง (แถว x คอลัมน์ i) — ใช้ทั้งตอนวาดทั้งตารางและตอนวาดซ้ำเฉพาะแถว
  let h = cell(x.cells[i], i).replace('<td', '<td data-r="' + x.row + '" data-c="' + i + '"' +
                                           (PENDING[x.row + ',' + i] ? ' data-pend="1"' : ''));
  if(x.chg && x.chg.cols.includes(i)){
    const w = WHO[x.row + ',' + i];
    h = h.replace('<td', '<td data-cc="1" title="' + esc('เดิม: ' + (x.chg.old[i] || 'ว่าง') +
      (w ? ' · แก้โดย ' + (w.by || 'ไม่ระบุชื่อ') + ' เวลา ' + String(w.t).slice(11, 16) : '')) + '"');
  }
  return h;
}

function repaintRow(x){                 // วาดซ้ำเฉพาะแถวนี้ ข้ามช่องที่กำลังมีตัวแก้เปิดอยู่
  const first = document.querySelector('td[data-r="' + x.row + '"]');
  if(!first) return;
  const tr = first.parentElement;
  tr.className = (x.cancelled ? 'cx ' : '') + (x.chg ? 'chg' : '');
  tr.querySelectorAll('td[data-c]').forEach(td => {
    if(td.querySelector('input,select')) return;
    const tmp = document.createElement('tbody');
    tmp.innerHTML = '<tr>' + tdHtml(x, Number(td.dataset.c)) + '</tr>';
    td.replaceWith(tmp.querySelector('td'));
  });
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

function advance(x, i, dir){            // เลื่อนไปแก้ช่องถัดไป: down = แถวถัดลงมาคอลัมน์เดิม, right = คอลัมน์ถัดไปแถวเดิม
  const td = document.querySelector('td[data-r="' + x.row + '"][data-c="' + i + '"]');
  if(!td) return;
  let nx = null;
  if(dir === 'down'){
    const tr = td.parentElement.nextElementSibling;
    if(tr) nx = tr.querySelector('td[data-c="' + i + '"]');
  }else{
    nx = td.nextElementSibling;
    while(nx && !nx.dataset.c) nx = nx.nextElementSibling;
  }
  if(!nx || !nx.dataset.r) return;
  const row = DATA.rows.find(r => r.row === Number(nx.dataset.r));
  if(!row) return;
  nx.scrollIntoView({block: 'nearest', inline: 'nearest'});
  startEdit(nx, row, Number(nx.dataset.c));
}

// ── บันทึกที่หน้าเว็บก่อน แล้วส่งลงชีตตามหลัง ──
// พิมพ์เสร็จ = ค่าขึ้นในตารางและเลื่อนไปช่องถัดไปทันที ส่วนการเขียนลงชีตทำเป็นคิวเรียงทีละช่องเบื้องหลัง
// คิวที่ยังไม่ได้ลงชีตเก็บไว้ในเบราว์เซอร์ (localStorage) ถ้าเน็ตหลุดหรือปิดหน้าไปก่อน เปิดใหม่ระบบส่งต่อให้
let SAVEQ = [], SAVING = false, PENDING = {}, PUMP = Promise.resolve(), DONEN = 0;
const OUTBOX_KEY = 'gb_plan_outbox';

function outboxSave(){
  try{
    if(!SAVEQ.length){ localStorage.removeItem(OUTBOX_KEY); return; }
    localStorage.setItem(OUTBOX_KEY, JSON.stringify({date: DATA && DATA.date, jobs: SAVEQ}));
  }catch(e){}
}

function badge(){
  const b = document.getElementById('savebadge');
  if(SAVEQ.length){ b.hidden = false; b.className = 'savebadge'; b.textContent = '⏳ กำลังบันทึกลงชีต ' + SAVEQ.length + ' ช่อง…'; }
  else if(DONEN){
    b.hidden = false; b.className = 'savebadge ok'; b.textContent = '✓ บันทึกลงชีตครบแล้ว ' + DONEN + ' ช่อง';
    setTimeout(() => { if(!SAVEQ.length){ b.hidden = true; DONEN = 0; } }, 2500);
  }else b.hidden = true;
}

let CARS = null;                         // เบอร์รถ → ข้อมูลรถ/พขร. จากแท็บในชีตทดลอง (อ่านอย่างเดียว)
let PHONES = {}, DRIVERS = [];           // ชื่อ พขร. → เบอร์โทร / รายชื่อ พขร. (คนเท่านั้น) สำหรับดรอปลิสต์
function buildDatalists(){               // รายชื่อที่เด้งให้เลือกตอนพิมพ์ (ปลายทาง/เบอร์รถ/พขร.)
  if(!OPTS) return;
  let box = document.getElementById('dls');
  if(!box){ box = document.createElement('div'); box.id = 'dls'; box.hidden = true; document.body.appendChild(box); }
  box.innerHTML = Object.keys(OPTS.suggest).map(c => '<datalist id="dl' + c + '">' +
    OPTS.suggest[c].map(v => '<option value="' + esc(v) + '"></option>').join('') + '</datalist>').join('');
}
function applyDrivers(){                 // ช่อง พขร.1/พขร.2 = พิมพ์ได้ (พิมพ์บางส่วนของชื่อ รายชื่อคนขับที่ยังทำงานเด้งให้เลือก)
  if(OPTS && DRIVERS.length){
    OPTS.suggest['18'] = DRIVERS; OPTS.suggest['19'] = DRIVERS;
    delete OPTS.strict['18']; delete OPTS.strict['19'];
    buildDatalists();
  }
}
function resolveDriver(v){               // ชื่อที่พิมพ์ → ตรงเป๊ะ / ตรงส่วนหนึ่งของชื่อเดียว (เติมชื่อเต็มให้) / หลายคน / ไม่มีในรายชื่อ
  v = String(v).trim();
  if(!v || !DRIVERS.length) return {name: v, ok: true};
  if(DRIVERS.indexOf(v) >= 0) return {name: v, ok: true};
  const ql = v.toLowerCase(), m = DRIVERS.filter(n => n.toLowerCase().indexOf(ql) >= 0);
  if(m.length === 1) return {name: m[0], ok: true, fixed: true};
  return m.length > 1 ? {name: v, ok: false, many: m.slice(0, 4)} : {name: v, ok: false, none: true};
}
function driverOk(r, v){                 // คืนชื่อที่ใช้บันทึก หรือ null ถ้าให้ยกเลิก (มีหลายคนที่ตรง ต้องเลือกจากรายการ)
  if(r.many){ toast('"' + v + '" ตรงกับหลายคน เช่น ' + r.many.join(', ') + ' — พิมพ์ให้ยาวขึ้นหรือเลือกจากรายการ', true); return null; }
  if(r.none) toast('⚠ ไม่พบ "' + v + '" ในรายชื่อ พขร. — บันทึกตามที่พิมพ์ (เบอร์โทรจะไม่ถูกเติมให้)', true);
  else if(r.fixed) toast('เลือก ' + r.name, false);
  return r.name;
}
function autoPhone(x, i, oldName, newName){
  // เปลี่ยนชื่อ พขร. → เบอร์โทรต้องตรงกับชื่อใหม่ (อิงตามชื่อในรายชื่อคนขับ): ชื่อใหม่มีเบอร์ = ใส่เบอร์นั้น, ไม่มีเบอร์ = เคลียร์เฉพาะเบอร์ที่เป็นของคนเดิม
  const pc = i === 18 ? 20 : 21, cur = String(x.cells[pc] || '').trim();
  const oldPh = PHONES[String(oldName).trim()] || '', nw = PHONES[String(newName).trim()] || '';
  if(cur === nw) return;
  if(!nw && !(cur && cur === oldPh)) return;
  saveCell(x, pc, cur, nw, false, null, true);
  toast(nw ? 'เบอร์โทรตาม ' + newName + ': ' + nw : 'ไม่พบเบอร์ของ ' + (newName || 'พขร. ที่เลือก') + ' — เคลียร์เบอร์ของคนเดิมให้', false);
}
const CAR_COL = 15, CAR_FILL = [['t', 16, 'ประเภทรถ'], ['plate', 17, 'ทะเบียน'], ['d1', 18, 'พขร.1'], ['d2', 19, 'พขร.2'],
                                ['p1', 20, 'เบอร์โทร.1'], ['p2', 21, 'เบอร์โทร.2']];
function autofillCar(x, oldCar, newCar){
  // เลือกเบอร์รถแล้ว เติมประเภท/ทะเบียน/พขร./เบอร์โทรให้ — เฉพาะช่องที่ว่าง หรือยังเป็นค่าเดิมของรถคันก่อน (ไม่ทับที่คนกรอกเอง)
  if(!CARS || !CARS[newCar]) return;
  const nw = CARS[newCar], od = CARS[oldCar] || {}, done = [];
  CAR_FILL.forEach(f => {
    const k = f[0], c = f[1], want = nw[k] || '', cur = String(x.cells[c] || '').trim();
    if(!want || cur === want) return;
    if(cur && cur !== (od[k] || '')) return;
    saveCell(x, c, cur, want, false, null, true);
    done.push(f[2]);
  });
  if(done.length) toast('เติมจากข้อมูลรถ ' + newCar + ': ' + done.join(', '), false);
}

function pickTrip(list, drop, mine){     // list = งานอื่นของรถคันนี้ [{t เที่ยว, d Drop}] → เที่ยวที่ใช้ได้ (0 = ครบ 3 เที่ยวแล้ว)
  const has = (t, d) => list.some(o => o.t === t && o.d === d);
  if(mine && !has(mine, drop)) return mine;                                  // ไม่ซ้ำ ใช้เที่ยวเดิม (เช่น Drop 2 ของเที่ยวเดียวกัน)
  if(drop > 1){ for(let n = 1; n <= 3; n++) if(has(n, drop - 1) && !has(n, drop)) return n; }   // Drop 2+ ต่อเที่ยวที่มี Drop ก่อนหน้า
  for(let n = 1; n <= 3; n++) if(!has(n, drop)) return n;
  return 0;
}
function tripFor(x, car){                // เที่ยววิ่งที่ควรเป็นเมื่อแถวนี้ใช้รถ car: {value, change, full}
  const list = [];
  DATA.rows.forEach(r => { if(r !== x && String(r.cells[CAR_COL] || '').trim() === car)
    list.push({t: parseInt(String(r.cells[4] || '').split(' ')[1], 10) || 0, d: parseInt(String(r.cells[13] || ''), 10) || 1}); });
  const mine = parseInt(String(x.cells[4] || '').split(' ')[1], 10) || 0, drop = parseInt(String(x.cells[13] || ''), 10) || 1;
  const n = pickTrip(list, drop, mine);
  if(!n) return {value: String(x.cells[4] || ''), change: false, full: true};
  return {value: 'เที่ยว ' + n, change: n !== mine, full: false};
}

function saveCell(x, i, old, value, override, dir, auto, hints){
  value = String(value).trim();
  if(value === String(old).trim()){ render(); if(dir) advance(x, i, dir); return; }
  let plan = null;
  if(i === CAR_COL && !auto && value){ plan = tripFor(x, value); hints = {trip: plan.value}; }      // เลือกรถ: คำนวณเที่ยวที่ไม่ซ้ำก่อน แล้วส่งเป็น "เจตนา" ไปให้เซิร์ฟเวอร์เช็ก
  const job = {row: x.row, col: i, old: old, value: value, override: !!override, auto: !!auto,
               hintCar: (hints && hints.car) || '', hintTrip: (hints && hints.trip) || '',
               key: x.cells[1] ? x.cells[1] + '|' + x.cells[13] : '', tries: 0};
  x.cells[i] = value;                                   // แสดงค่าที่พิมพ์ทันที (จางๆ จนกว่าชีตยืนยัน)
  PENDING[x.row + ',' + i] = true;
  SAVEQ.push(job); outboxSave(); badge();
  if((i === 18 || i === 19) && !auto) autoPhone(x, i, old, value);                           // เปลี่ยน พขร. → เบอร์โทรตามชื่อ
  if(plan){                                                                                    // เลือกเบอร์รถ → เที่ยววิ่งไม่ซ้ำ + เติมช่องที่เกี่ยวกับรถให้
    if(plan.full) toast('รถ ' + value + ' ใช้ครบ 3 เที่ยวแล้วในวันนี้ — เลือกเที่ยววิ่งเอง', true);
    else if(plan.change){
      saveCell(x, 4, String(x.cells[4] || ''), plan.value, false, null, true, {car: value});
      toast('ปรับเที่ยววิ่งเป็น ' + plan.value + ' (รถ ' + value + ' เที่ยวเดิม/Drop นี้มีงานอยู่แล้ว)', false);
    }
    autofillCar(x, old, value);
  }
  render();
  if(dir) advance(x, i, dir);                           // ไปช่องถัดไปเลย ไม่รอเซิร์ฟเวอร์
  pump();
}

function dropDependents(job){                           // เลือกรถไม่ผ่าน → งานเติมข้อมูลรถ/ปรับเที่ยวที่รออยู่ในคิวของแถวนี้ ยกเลิกด้วย (ไม่ให้ข้อมูลของรถคันใหม่ไปลงแถวที่ยังเป็นรถเดิม)
  if(job.col !== CAR_COL || job.auto) return;
  const cur = DATA && DATA.rows.find(q => q.row === job.row), keep = [];
  SAVEQ.forEach((q, i) => { if(i > 0 && q.row === job.row && q.auto) revertJob(q, cur); else keep.push(q); });
  SAVEQ.length = 0; keep.forEach(q => SAVEQ.push(q)); outboxSave(); badge();
}
function revertJob(job, cur){                           // ชีตไม่รับ → คืนค่าเดิม
  delete PENDING[job.row + ',' + job.col];
  if(cur){ cur.cells[job.col] = job.old; computeChanges(); repaintRow(cur); }
}

async function runJob(job){                             // คืนค่าเมื่อชีตตัดสินแล้ว (สำเร็จ/ไม่รับ) โยน error เมื่อต้องลองใหม่
  const q0 = DATA && DATA.rows.find(q => q.row === job.row);
  if(q0 && job.col !== 1 && job.col !== 13) job.key = q0.cells[1] ? q0.cells[1] + '|' + q0.cells[13] : '';   // ช่อง JOB/Drop เป็นตัวกำหนดกุญแจเอง ไม่ปรับ
  const r = await fetch('/api/plan/edit', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({row: job.row, col: job.col, old: job.old, value: job.value, key: job.key,
                          by: editorName(), override: job.override, hint_car: job.hintCar || '', hint_trip: job.hintTrip || ''})});
  if(r.status === 401){ location.href = '/login'; throw new Error('ต้องล็อกอินใหม่'); }
  if(r.status >= 500) throw new Error('เซิร์ฟเวอร์/Google ตอบ ' + r.status);
  let j = {};
  try{ j = await r.json(); }catch(e){}
  const cur = DATA && DATA.rows.find(q => q.row === job.row);
  const k = job.row + ',' + job.col;
  if(r.status === 423 && job.auto){ revertJob(job, cur); return; }   // เติมอัตโนมัติชนช่องสูตร = ข้ามเงียบๆ ไม่ถามเขียนทับ
  if(r.status === 423){                                 // ช่องนี้เป็นสูตรในชีต — ถามก่อนเขียนทับ
    if(confirm((j.detail || 'ช่องนี้เป็นสูตร') + ' — ค่าตอนนี้: "' + (j.current || 'ว่าง') + '" — '
               + 'ถ้าแก้ตรงนี้ สูตรในช่องนี้ของแถวนี้จะหาย แทนที่ด้วยค่าที่พิมพ์ ต้องการเขียนทับ?')){
      job.override = true; return runJob(job);
    }
    revertJob(job, cur); return;
  }
  if(r.status === 409){                                 // มีคนแก้ไปก่อน — ไม่เขียนทับ โชว์ค่าปัจจุบันให้เห็น
    delete PENDING[k];
    if(cur && j.current !== undefined) cur.cells[job.col] = j.current;
    computeChanges(); if(cur) repaintRow(cur);
    dropDependents(job);
    toast((j.detail || 'ชนกับคนอื่น') + ' ค่าตอนนี้: "' + (j.current || 'ว่าง') + '"', true); return;
  }
  if(!r.ok){ revertJob(job, cur); dropDependents(job); toast(j.detail || ('HTTP ' + r.status), true); return; }
  delete PENDING[k]; DONEN++;
  if(cur){
    ownEdit(cur, job.col, j.value, j.cells);
    SAVEQ.slice(1).filter(q => q.row === job.row).forEach(q => { cur.cells[q.col] = q.value; });   // ช่องอื่นในแถวที่ยังรอคิว คงค่าที่พิมพ์ไว้
    repaintRow(cur);
  }
  if(!j.logged) toast('บันทึกแล้ว แต่เขียนประวัติ EditLog ไม่ได้', true);
}

function pump(){
  if(SAVING) return PUMP;
  SAVING = true;
  PUMP = (async () => {
    while(SAVEQ.length){
      const job = SAVEQ[0];
      try{
        await runJob(job);
      }catch(e){                                        // เน็ตหลุด/เซิร์ฟเวอร์ล่ม: เก็บไว้ในคิวแล้วลองใหม่ ครบ 3 ครั้งถึงยอมแพ้
        job.tries = (job.tries || 0) + 1;
        if(job.tries >= 3){
          SAVEQ.shift(); outboxSave();
          revertJob(job, DATA && DATA.rows.find(q => q.row === job.row));
          toast('บันทึกลงชีตไม่สำเร็จ (' + e.message + ') — คืนค่าเดิมให้แล้ว ลองแก้ใหม่อีกครั้ง', true);
          continue;
        }
        outboxSave(); badge();
        toast('ยังส่งลงชีตไม่ได้ (' + e.message + ') เก็บไว้แล้ว จะลองใหม่ใน 6 วินาที', true);
        SAVING = false;
        setTimeout(pump, 6000);
        return;
      }
      SAVEQ.shift(); outboxSave(); badge();
    }
    SAVING = false; badge();
  })();
  return PUMP;
}

function resumeOutbox(){                                // เปิดหน้ามาใหม่แล้วมีงานค้างจากรอบก่อน → ส่งต่อให้
  let box = null;
  try{ box = JSON.parse(localStorage.getItem(OUTBOX_KEY) || 'null'); }catch(e){}
  if(!box || !box.jobs || !box.jobs.length || SAVEQ.length) return;
  if(!DATA || !DATA.can_edit){ try{ localStorage.removeItem(OUTBOX_KEY); }catch(e){} return; }
  box.jobs.forEach(job => {
    const cur = DATA.rows.find(q => q.row === job.row);
    if(cur && box.date === DATA.date && String(cur.cells[job.col]).trim() === String(job.old).trim()){
      cur.cells[job.col] = job.value; PENDING[job.row + ',' + job.col] = true;
    }
    SAVEQ.push(job);
  });
  toast('มี ' + SAVEQ.length + ' ช่องที่แก้ไว้แล้วยังไม่ได้ลงชีต กำลังส่งต่อให้', false);
  badge(); render(); pump();
}
window.addEventListener('beforeunload', e => { if(SAVEQ.length){ e.preventDefault(); e.returnValue = ''; } });
window.addEventListener('online', () => { if(SAVEQ.length) pump(); });

let OPTS = null;
async function loadCars(){
  try{
    const r = await fetch('/api/plan/cars');
    if(r.ok){ const j = await r.json(); CARS = j.cars || {}; PHONES = j.phones || {}; DRIVERS = j.drivers || []; applyDrivers(); }
  }catch(e){}
}
async function loadOpts(){              // รายการตัวเลือกของช่อง (อ่านจากไฟล์ต้นทางฝั่งเซิร์ฟเวอร์)
  if(OPTS) return;
  loadCars();
  try{
    const r = await fetch('/api/plan/options');
    if(!r.ok) return;
    OPTS = await r.json();
    buildDatalists();
    applyDrivers();
  }catch(e){}
}

// ตัวแก้ค่าในช่อง (ใช้ทั้งตารางหลักและตารางในหน้าต่างนำเข้า): เลือกอย่างเดียว / พิมพ์ค้นหา / พิมพ์อิสระ
function openEditor(td, i, old, onSave, onCancel, onSkip){
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
    el.addEventListener('change', () => finish(() => onSave(el.value, 'down')));      // เลือกแล้วบันทึกเลย แล้วเลื่อนลง
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
      else if(ev.key === 'Enter' || ev.key === 'Tab'){
        ev.preventDefault();
        const dir = ev.key === 'Enter' ? 'down' : 'right';                   // Enter = ช่องล่าง, Tab = ช่องขวา
        if(sug && sug.length && !el.value.trim()) finish(() => (onSkip ? onSkip(dir) : onCancel()));   // ไม่ได้พิมพ์/เลือก = ไม่เปลี่ยน ข้ามไปช่องถัดไป
        else finish(() => onSave(el.value, dir));
      }
    });
    el.addEventListener('blur', () => finish(onCancel));      // คลิกที่อื่น = ยกเลิก ไม่บันทึกโดยไม่ตั้งใจ
  }
  td.textContent = ''; td.appendChild(el); el.focus();
  if(el.select && el.tagName === 'INPUT') el.select();
}

let CURSEL = {row: 0, col: -1}, PRES = [];       // ช่องที่ฉันกำลังแก้ / คนอื่นที่ออนไลน์ [{name,row,col}]
function startEdit(td, x, i){
  const old = x.cells[i];
  const who = PRES.find(o => o.row === x.row && o.col === i);
  if(who) toast('⚠ ' + who.name + ' กำลังแก้ช่องนี้อยู่ — ถ้าแก้พร้อมกัน ระบบจะไม่ทับกัน แต่คนที่บันทึกทีหลังจะถูกแจ้งว่ามีคนแก้ไปก่อน', true);
  CURSEL = {row: x.row, col: i};
  const idle = () => { CURSEL = {row: 0, col: -1}; };
  openEditor(td, i, old, (v, dir) => {
    idle();
    if(i === 18 || i === 19){ const nm = driverOk(resolveDriver(v), v); if(nm === null){ render(); return; } v = nm; }
    saveCell(x, i, old, v, false, dir);
  }, () => { idle(); render(); },
             dir => { idle(); render(); advance(x, i, dir); });
}
function paintPresence(){
  document.querySelectorAll('td.pres').forEach(t => { t.classList.remove('pres'); t.removeAttribute('data-who'); });
  PRES.forEach(o => {
    if(!o.row) return;
    const t = document.querySelector('td[data-r="' + o.row + '"][data-c="' + o.col + '"]');
    if(t){ t.classList.add('pres'); t.setAttribute('data-who', o.name); }
  });
  const bar = document.getElementById('presbar');
  bar.hidden = !PRES.length;
  bar.textContent = PRES.length ? '👥 ออนไลน์ตอนนี้: ' + PRES.map(o => o.name + (o.row ? ' (กำลังแก้แถว ' + o.row + ')' : '')).join(' · ') : '';
}
const _renderBase = render;
render = function(){ _renderBase(); paintPresence(); };
async function beat(){                   // ส่งสัญญาณ + รับรายชื่อคนอื่น (ไม่ยิง Google)
  if(document.hidden || !DATA) return;
  let name = '';
  try{ name = EDITING ? (localStorage.getItem('gb_plan_editor') || '') : ''; }catch(e){}
  try{
    const r = await fetch('/api/plan/presence', {method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({name: name, date: DATA.date, row: CURSEL.row, col: CURSEL.col})});
    if(r.ok){ PRES = (await r.json()).others || []; paintPresence(); }
  }catch(e){}
}
setInterval(beat, 7000);
setTimeout(beat, 1500);

document.getElementById('rows').addEventListener('click', e => {
  if(!EDITING) return;
  if(e.target.closest('a')) e.preventDefault();       // คลิกเบอร์โทรในโหมดแก้ไข = แก้ ไม่ใช่โทรออก
  const td = e.target.closest('td[data-r]');
  if(!td || td.querySelector('input,select')) return;       // ช่องที่มีตัวแก้เปิดอยู่แล้ว (รวมกล่องเลือก) ห้ามเปิดซ้ำ ไม่งั้นรายการที่กำลังเปิดหาย
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
  if(o.master) fd.append('master_json', JSON.stringify(o.master));
  if(o.near) fd.append('near', '1');
  if(o.skip) fd.append('skip_dups', '1');
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
    IMP = {rows: j.rows, headers: j.headers, edited: {}, errs: {}, warns: {}, info: j, replace: true, onlyBad: false, master: j.master || null};
    impMarkErrors(j);
    impRender();
  }catch(e){ impBody('<div class="box bad">อ่านไฟล์ไม่ได้: ' + esc(e.message) + '</div>'); }
}

let IMP_CHECKING = false, IMP_AGAIN = false;
async function impRecheck(){             // แสดงผลที่แก้ทันที แล้วตรวจกับเซิร์ฟเวอร์เบื้องหลัง (ช่องแดง/คำเตือนอัปเดตตามหลัง)
  IMP.checking = true;
  impRender();
  if(IMP_CHECKING){ IMP_AGAIN = true; return; }   // กำลังตรวจอยู่ — แก้ซ้ำระหว่างรอ ให้ตรวจรอบเดียวหลังรอบนี้จบ
  IMP_CHECKING = true;
  try{
    do{
      IMP_AGAIN = false;
      const sent = JSON.stringify(IMP.rows);
      const j = await impSend({rows: IMP.rows, near: IMP.near});
      if(!j) break;
      IMP.info = j; impMarkErrors(j);
      if(JSON.stringify(IMP.rows) === sent) IMP.rows = j.rows;   // ระหว่างรอมีแก้เพิ่ม = ไม่ทับด้วยผลเก่า (ตรวจอีกรอบ)
      else IMP_AGAIN = true;
    }while(IMP_AGAIN);
  }catch(e){ toast('ตรวจซ้ำไม่สำเร็จ: ' + e.message, true); }
  IMP_CHECKING = false; IMP.checking = false;
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
  const head = '<tr><th>#</th>' + IMP.headers.map((h, c) => '<th data-ic="' + c + '"><small>' + COLS[c] + '</small>' + esc(h) + '</th>').join('') + '</tr>';
  const bad = impBadRows(), nbad = Object.keys(bad).length;
  const qEl = document.getElementById('impQ'), qHad = !!qEl && document.activeElement === qEl, qPos = qHad ? qEl.selectionStart : 0;   // พิมพ์ค้นหาอยู่ → วาดใหม่แล้วคืนเคอร์เซอร์ให้
  const hide = ri => (IMP.onlyBad && !bad[ri]) || impHidden(ri);
  const shown = IMP.rows.filter((_, i) => !hide(i)).length;
  const body = IMP.rows.map((r, ri) => hide(ri) ? '' : '<tr><td class="rn">' + (ri + 1) + '</td>' + r.map((v, c) => {
    const k = ri + ',' + c;
    const cls = IMP.errs[k] ? ' class="ierr" title="' + esc(IMP.errs[k]) + '"'
      : IMP.warns[k] ? ' class="iwarn" title="' + esc(IMP.warns[k]) + '"'
      : IMP.edited[k] ? ' class="ied"' : '';
    const sel = IMP.sel && IMP.sel.r === ri && IMP.sel.c === c;
    return '<td data-ir="' + ri + '" data-ic="' + c + '"' + cls + (sel ? ' data-sel="1"' : '') + '>' + (c === 14 ? '<div class="nt" title="' + esc(v) + '">' + impHl(v) + '</div>' : impHl(v)) + (sel ? '<i class="fh" title="ลากลงเพื่อคัดลอกค่าไปแถวล่าง"></i>' : '') + '</td>';
  }).join('') + '</tr>').join('');
  const nedit = Object.keys(IMP.edited).length;
  const ex = IMP.near ? (j.existing
    ? 'งานที่วางจะ<b>เพิ่มเข้าวันที่ ' + dmy(j.date) + '</b> (ชีตมีอยู่แล้ว ' + j.existing + ' แถว) โดยไม่ลบงานเดิม — แทรกติดกับแถวของรถคันเดียวกัน คันใหม่/ยังไม่มีเบอร์รถต่อท้ายวัน'
    : 'วันที่ ' + dmy(j.date) + ' ยังไม่มีในชีต จะลงต่อท้ายวันสุดท้าย ข้ามแถวสีดำ')
    : '<label><input type="checkbox" id="impReplace"' + (IMP.replace ? ' checked' : '') + '> ' + (j.existing
    ? 'แทนที่งานเดิมของวันที่ ' + dmy(j.date) + ' (ชีตมีอยู่แล้ว ' + j.existing + ' แถว) ที่ตำแหน่งเดิม ไม่แตะแถวสีดำคั่นวัน'
    : 'วันที่ ' + dmy(j.date) + ' ยังไม่มีในชีต จะลงต่อท้ายวันสุดท้าย ข้ามแถวสีดำ') + '</label>';
  const ndup = (j.dups || []).length;
  if(IMP.skip === undefined) IMP.skip = ndup > 0;
  const nw = j.total - (IMP.near && IMP.skip ? ndup : 0);
  const ok = j.can_commit && nw > 0 && !nerr && !IMP.checking;
  const nmaster = IMP.master ? Object.keys(IMP.master).length : 0;
  impBody(
    '<div class="box"><b>วันที่ ' + dmy(j.date) + '</b> · ' + j.total + ' แถวงาน · ปลายทาง: <b>' + esc(j.target) + '</b>' +
    (nedit ? ' · <span class="ied" style="padding:1px 8px;border-radius:6px">แก้แล้ว ' + nedit + ' ช่อง</span>' : '') + '</div>' +
    '<p class="mut" style="margin:6px 2px;font-size:13px">✏️ คลิกช่องในตารางเพื่อแก้ก่อนเขียนลงชีต · Enter = ตกลง · Esc = ยกเลิก · ' +
    '<b class="bad">ช่องสีแดง = มีปัญหา (เอาเมาส์ชี้ดูสาเหตุ)</b> · ช่องสีเหลือง = ที่คุณแก้</p>' + er + w +
    '<label style="display:block;margin:6px 2px"><input type="checkbox" id="impOnlyBad"' + (IMP.onlyBad ? ' checked' : '') +
    '> ดูเฉพาะแถวที่มีช่องสีแดง (' + nbad + ' แถว)</label>' +
    '<div class="impsearch"><span class="sw"><span class="ico">🔍</span><input type="search" id="impQ" placeholder="ค้นหาในตาราง (รถ / ปลายทาง / ออเดอร์ / ชื่อคนขับ)" value="' + esc(IMP.q || '') +
    '">' + (IMP.q ? '<button type="button" class="clr" id="impQx" title="ล้างคำค้น">✕</button>' : '') + '</span><span class="cnt">' +
    (String(IMP.q || '').trim() ? 'พบ ' + shown + ' จาก ' + IMP.rows.length + ' แถว' : 'ทั้งหมด ' + IMP.rows.length + ' แถว') + '</span>' +
    (IMP.near ? ' <button class="undo" id="impRenum" title="จัดเที่ยววิ่งของทุกแถวใหม่ตาม Drop (Drop 1 = เที่ยวใหม่, Drop 2+ ต่อเที่ยวเดิม) ไม่ให้ซ้ำกับงานในชีตของวันนั้น">🔢 จัดเที่ยววิ่งใหม่ตาม Drop</button>' : '') + '</div>' +
    '<span class="mut" style="font-size:12.5px">ลากช่องไปวางบนอีกช่อง = สลับค่า · ลากจุดสีน้ำเงินที่มุมช่อง = คัดลอกลงแถวล่าง</span>' +
    '<button class="undo" id="impUndo"' + (IMP.hist && IMP.hist.length ? '' : ' disabled') + ' title="ย้อนกลับการแก้ล่าสุด (Ctrl+Z)">↶ ย้อนกลับ</button>' +
    (IMP.checking ? ' <span class="mut" style="font-size:12.5px">⏳ กำลังตรวจข้อมูล…</span>' : '') +
    '<div class="tbl"><table><thead>' + head + '</thead><tbody>' + body + '</tbody></table></div>' +
    '<div class="box">' + ex + '</div>' +
    (ndup ? '<div class="box"><label><input type="checkbox" id="impSkip"' + (IMP.skip ? ' checked' : '') + '> <b>ข้ามแถวที่ซ้ำกับชีต (' + ndup +
      ' แถว)</b> — งานที่มีเลขออเดอร์/เลขโหลด/ปลายทางเหมือนที่อยู่ในชีตวันนี้แล้ว จะไม่ถูกเพิ่มซ้ำ (แถวสีเหลืองในช่องเลขออเดอร์)</label></div>' : '') +
    (IMP.near ? '' : '<div class="box ' + (nmaster ? 'ok' : '') + '">' + (nmaster
      ? '🚚 พบข้อมูลรถ/พขร. ' + nmaster + ' คันในไฟล์นี้ — จะเก็บไว้ใช้เติมประเภท/ทะเบียน/พขร./เบอร์โทรอัตโนมัติตอนเลือกเบอร์รถ'
      : 'ไม่พบแท็บข้อมูลรถ/พขร. ในไฟล์นี้ — ถ้าเคยนำเข้าไว้แล้ว ระบบใช้ข้อมูลเดิมต่อ') + '</div>') +
    (j.can_commit ? '' : '<div class="box bad">เขียนลงชีตไม่ได้ตอนนี้: ' + esc(j.block_reason) + '</div>') +
    '<button class="go" id="impGo"' + (ok ? '' : ' disabled') + '>เขียน ' + nw + ' แถวลงชีต</button>');
  const t = document.querySelector('#impBody .tbl');
  if(t){ t.scrollLeft = sx; t.scrollTop = sy; }
  const rp = document.getElementById('impReplace'); if(rp) rp.onchange = e => { IMP.replace = e.target.checked; };
  const sk = document.getElementById('impSkip'); if(sk) sk.onchange = e => { IMP.skip = e.target.checked; impRender(); };
  document.getElementById('impOnlyBad').onchange = e => { IMP.onlyBad = e.target.checked; impRender(); };
  document.getElementById('impUndo').onclick = impUndo;
  document.getElementById('impGo').onclick = impCommit;
  const qi = document.getElementById('impQ');
  qi.oninput = e => { IMP.q = e.target.value; clearTimeout(IMP.qt); IMP.qt = setTimeout(impRender, 160); };
  if(qHad){ qi.focus(); try{ qi.setSelectionRange(qPos, qPos); }catch(e){} }
  const rn = document.getElementById('impRenum'); if(rn) rn.onclick = impRenumber;
  const qx = document.getElementById('impQx'); if(qx) qx.onclick = () => { IMP.q = ''; impRender(); document.getElementById('impQ').focus(); };
}
function impHl(v){                       // แสดงค่าในช่อง พร้อมเน้นสีคำที่ค้นเจอ
  const q = String(IMP.q || '').trim();
  if(!q) return esc(v);
  const s = String(v), low = s.toLowerCase(), ql = q.toLowerCase();
  let out = '', i = 0;
  for(;;){
    const k = low.indexOf(ql, i);
    if(k < 0){ out += esc(s.slice(i)); break; }
    out += esc(s.slice(i, k)) + '<mark>' + esc(s.slice(k, k + q.length)) + '</mark>';
    i = k + q.length;
  }
  return out;
}
function impHidden(ri){                  // ถูกซ่อนด้วยช่องค้นหาไหม (ค้นในทุกช่องของแถว ไม่สนตัวพิมพ์เล็กใหญ่)
  const q = String(IMP.q || '').trim().toLowerCase();
  return !!q && IMP.rows[ri].join(' ').toLowerCase().indexOf(q) < 0;
}
function impRenumber(){                  // จัดเที่ยววิ่งของทุกแถวที่วางใหม่ตาม Drop: Drop 1 เริ่มเที่ยวใหม่ Drop 2+ ต่อเที่ยวเดิม ไม่ซ้ำกับในชีต
  impSnap();
  const used = JSON.parse(JSON.stringify(IMP.usedSheet || {})), last = {};
  IMP.rows.forEach((o, r) => {
    const car = String(o[15] || '').trim();
    if(!car) return;
    const dropNo = parseInt(String(o[13]).trim(), 10) || 1, u = used[car] = used[car] || {};
    let n = 1;
    if(dropNo > 1){
      if(last[car]) n = last[car];
      else { n = 0; for(let k = 1; k <= 3; k++) if(u[k] && u[k][dropNo - 1] && !u[k][dropNo]){ n = k; break; } if(!n) n = 1; }
    }
    while(u[n] && u[n][dropNo]) n++;
    (u[n] = u[n] || {})[dropNo] = 1; last[car] = n;
    const val = n > 3 ? '' : 'เที่ยว ' + n;
    if(o[4] !== val){ o[4] = val; IMP.edited[r + ',4'] = 1; }
  });
  impRecheck();
}

function impTrip(r, car){                // เที่ยววิ่งของแถวนี้: Drop 1 เริ่มเที่ยวใหม่ Drop 2+ ต่อเที่ยวเดิม ห้ามซ้ำเฉพาะ รถ+เที่ยว+Drop (ดูทั้งในชีตของวันนั้นและในชุดที่วาง)
  const list = [];
  const us = (IMP.usedSheet || {})[car] || {};
  Object.keys(us).forEach(t => Object.keys(us[t]).forEach(d => list.push({t: Number(t), d: Number(d)})));
  IMP.rows.forEach((o, i) => { if(i !== r && String(o[15] || '').trim() === car)
    list.push({t: parseInt(String(o[4] || '').split(' ')[1], 10) || 0, d: parseInt(String(o[13] || ''), 10) || 1}); });
  const mine = parseInt(String(IMP.rows[r][4] || '').split(' ')[1], 10) || 0, drop = parseInt(String(IMP.rows[r][13] || ''), 10) || 1;
  const n = pickTrip(list, drop, mine), val = n ? 'เที่ยว ' + n : '';
  if(IMP.rows[r][4] !== val){ IMP.rows[r][4] = val; IMP.edited[r + ',4'] = 1; }
}
function impApply(r, c, v){              // ใส่ค่าในแถว r ช่อง c พร้อมผลที่ตามมา
  const row = IMP.rows[r], old = row[c];
  if(v === old) return;
  row[c] = v; IMP.edited[r + ',' + c] = 1;
  if(c === 18 || c === 19){              // เปลี่ยนชื่อ พขร. → เบอร์โทรตามชื่อ (เบอร์ว่างหรือเป็นของคนเดิมถึงแก้/เคลียร์)
    const pc = c === 18 ? 20 : 21, cur = String(row[pc] || '').trim();
    const oldPh = PHONES[String(old).trim()] || '', nw = PHONES[String(v).trim()] || '';
    if(cur !== nw && (nw || (cur && cur === oldPh))){ row[pc] = nw; IMP.edited[r + ',' + pc] = 1; }
  }
  if(c === 15 && v && CARS && CARS[v]){  // ใส่เบอร์รถ → เติมประเภท/ทะเบียน/พขร. (ช่องว่างหรือยังเป็นของรถคันเดิม) + เบอร์โทรตามชื่อ + เที่ยววิ่งไม่ซ้ำ
    const nc = CARS[v], oc = (CARS && CARS[old]) || {};
    [[16, 't'], [17, 'plate'], [18, 'd1'], [19, 'd2']].forEach(f => {
      const cur = String(row[f[0]] || '').trim(), want = nc[f[1]] || '';
      if(want && cur !== want && (!cur || cur === (oc[f[1]] || ''))){ row[f[0]] = want; IMP.edited[r + ',' + f[0]] = 1; }
    });
    [[18, 20], [19, 21]].forEach(f => {
      const nm = String(row[f[0]] || '').trim(), ph = PHONES[nm] || '';
      if(nm && ph && String(row[f[1]] || '').trim() !== ph){ row[f[1]] = ph; IMP.edited[r + ',' + f[1]] = 1; }
    });
    if(IMP.near) impTrip(r, v);
  }
}
function impSnap(){                     // เก็บสภาพตารางก่อนแก้ไว้ย้อนกลับ (สูงสุด 30 ครั้ง)
  IMP.hist = IMP.hist || [];
  IMP.hist.push(JSON.stringify([IMP.rows, IMP.edited]));
  if(IMP.hist.length > 30) IMP.hist.shift();
}
function impUndo(){
  if(!IMP || !IMP.hist || !IMP.hist.length) return;
  const st = JSON.parse(IMP.hist.pop());
  IMP.rows = st[0]; IMP.edited = st[1];
  impRecheck();
}
function impSwap(r1, c1, r2, c2){        // ลากช่องไปวางบนอีกช่อง = สลับค่าของสองช่อง (เบอร์โทร/ข้อมูลรถตามชื่อ-เบอร์รถ)
  const a = IMP.rows[r1][c1], b = IMP.rows[r2][c2];
  if(a === b) return;
  impSnap();
  impApply(r1, c1, b); impApply(r2, c2, a);
  IMP.sel = {r: r2, c: c2};
  toast('สลับ "' + (a || 'ว่าง') + '" กับ "' + (b || 'ว่าง') + '" แล้ว (กด ↶ ย้อนกลับ ได้)', false);
  impRecheck();
}
function impSet(r, c, v){                // แก้ช่องในตารางนำเข้า แล้วตรวจซ้ำ
  IMP.sel = {r: r, c: c};
  if(c === 18 || c === 19){ const nm = driverOk(resolveDriver(v), v); if(nm === null){ impRender(); return; } v = nm; }
  if(v === IMP.rows[r][c]){ impRender(); return; }
  impSnap();
  impApply(r, c, v);
  impRecheck();
}
function impFill(from, col, a, b){       // ลากคัดลอกค่าของช่อง (from, col) ไปแถว a..b ของคอลัมน์เดียวกัน (ทับค่าเดิมในช่องปลายทาง)
  const v = IMP.rows[from][col];
  impSnap();
  const car = String(IMP.rows[from][15] || '').trim();
  const carCol = col >= 16 && col <= 21;  // ประเภทรถ/ทะเบียน/พขร./เบอร์โทร เป็นของรถแต่ละคัน → ลากผ่านแถวของรถคันอื่นให้ข้าม ไม่ทับ
  let skipped = 0, done = 0;
  for(let r = a; r <= b; r++){
    if(r === from) continue;
    if(impHidden(r) || (IMP.onlyBad && !impBadRows()[r])) continue;                     // แถวที่ซ่อนอยู่ ไม่ทับ
    if(carCol && String(IMP.rows[r][15] || '').trim() !== car){ skipped++; continue; }
    impApply(r, col, v); done++;
  }
  if(skipped) toast('ใส่ให้ ' + done + ' แถว · ข้าม ' + skipped + ' แถวที่เป็นรถคันอื่น', false);
  impRecheck();
}

document.getElementById('impBody').addEventListener('click', e => {
  if(e.target.closest('.fh') || (IMP && IMP.justDragged)) return;
  const td = e.target.closest('td[data-ir]');
  if(!td || !IMP || td.querySelector('input,select')) return;
  const r = Number(td.dataset.ir), c = Number(td.dataset.ic);
  IMP.sel = {r: r, c: c};
  openEditor(td, c, IMP.rows[r][c], v => impSet(r, c, v), impRender);
});
// ลากตัวช่อง (ไม่ใช่จุดสีน้ำเงิน) ไปวางบนอีกช่อง = สลับค่า: คอลัมน์เดียวกันข้ามแถวได้ หรือ พขร.1 ↔ พขร.2
document.getElementById('impBody').addEventListener('mousedown', e => {
  if(e.target.closest('.fh') || e.button !== 0 || !IMP) return;
  const src = e.target.closest('td[data-ir]');
  if(!src || src.querySelector('input,select')) return;
  const r1 = Number(src.dataset.ir), c1 = Number(src.dataset.ic), x0 = e.clientX, y0 = e.clientY;
  let on = false, tgt = null;
  const clear = () => document.querySelectorAll('#impBody td.idrag, #impBody td.idsrc').forEach(t => t.classList.remove('idrag', 'idsrc'));
  const move = ev => {
    if(!on){ if(Math.abs(ev.clientX - x0) + Math.abs(ev.clientY - y0) < 8) return; on = true; src.classList.add('idsrc'); }
    const el = document.elementFromPoint(ev.clientX, ev.clientY), td = el && el.closest ? el.closest('td[data-ir]') : null;
    document.querySelectorAll('#impBody td.idrag').forEach(t => t.classList.remove('idrag'));
    tgt = td && td !== src ? td : null;
    if(tgt) tgt.classList.add('idrag');
  };
  const up = () => {
    document.removeEventListener('mousemove', move); document.removeEventListener('mouseup', up);
    if(!on) return;                                                         // ไม่ได้ลาก = คลิกธรรมดา (เปิดช่องแก้)
    clear();
    IMP.justDragged = true; setTimeout(() => { if(IMP) IMP.justDragged = false; }, 300);
    if(!tgt) return;
    const r2 = Number(tgt.dataset.ir), c2 = Number(tgt.dataset.ic), pair = (c1 === 18 || c1 === 19) && (c2 === 18 || c2 === 19);
    if(c1 !== c2 && !pair){ toast('สลับได้เฉพาะช่องคอลัมน์เดียวกัน หรือ พขร.1 ↔ พขร.2', true); return; }
    impSwap(r1, c1, r2, c2);
  };
  document.addEventListener('mousemove', move); document.addEventListener('mouseup', up);
});
// ลากจุดสีน้ำเงินมุมขวาล่างของช่องที่เลือก ลงไปแถวล่าง (หรือขึ้นไปแถวบน) = คัดลอกค่าไปทุกช่องที่ลากผ่าน แล้วตรวจซ้ำครั้งเดียว
document.getElementById('impBody').addEventListener('mousedown', e => {
  if(!e.target.closest('.fh') || !IMP || !IMP.sel) return;
  e.preventDefault();
  const from = IMP.sel.r, col = IMP.sel.c, tbl = document.querySelector('#impBody .tbl');
  let to = from;
  const mark = () => {
    document.querySelectorAll('#impBody td.idrag').forEach(t => t.classList.remove('idrag'));
    for(let r = Math.min(from, to); r <= Math.max(from, to); r++){
      const t = document.querySelector('#impBody td[data-ir="' + r + '"][data-ic="' + col + '"]');
      if(t && r !== from) t.classList.add('idrag');
    }
  };
  const move = ev => {
    if(tbl){ const rc = tbl.getBoundingClientRect(); if(ev.clientY > rc.bottom - 28) tbl.scrollTop += 24; else if(ev.clientY < rc.top + 44) tbl.scrollTop -= 24; }
    const el = document.elementFromPoint(ev.clientX, ev.clientY), td = el && el.closest ? el.closest('td[data-ir]') : null;
    if(td){ to = Number(td.dataset.ir); mark(); }
  };
  const up = () => {
    document.removeEventListener('mousemove', move); document.removeEventListener('mouseup', up);
    IMP.justDragged = true; setTimeout(() => { if(IMP) IMP.justDragged = false; }, 300);   // กันคลิกหลังปล่อยเมาส์เปิดช่องแก้
    if(to === from){ impRender(); return; }
    impFill(from, col, Math.min(from, to), Math.max(from, to));
  };
  document.addEventListener('mousemove', move); document.addEventListener('mouseup', up);
});

async function impCommit(){
  const j = IMP.info, replace = IMP.replace;
  const nd = (j.dups || []).length, nw = j.total - (IMP.near && IMP.skip ? nd : 0);
  if(!confirm('เขียน ' + nw + ' แถวของวันที่ ' + dmy(j.date) + ' ลง' + j.target + (IMP.near && !IMP.skip && nd ? ' (⚠ รวม ' + nd + ' แถวที่ซ้ำกับชีต)' : '') +
              (IMP.near ? ' (เพิ่มเข้าไป ไม่ลบงานเดิม)' : replace ? ' และลบงานเดิมของวันนั้นก่อน' : '') + ' — ยืนยัน?')) return;
  const btn = document.getElementById('impGo'); btn.disabled = true; btn.textContent = 'กำลังเขียนลงชีต...';
  try{
    const r = await impSend({rows: IMP.rows, commit: true, replace: replace, master: IMP.master, near: IMP.near, skip: IMP.near && IMP.skip});
    if(!r) return;
    impBody('<div class="box ok">✓ เขียนแล้ว ' + r.written + ' แถว (แถวที่ ' + r.first_row + '–' + r.last_row + ' ในชีต)' +
      (r.removed ? ' · ลบแถวส่วนเกิน ' + r.removed + ' แถว' : '') + (r.inserted ? ' · แทรกเพิ่ม ' + r.inserted + ' แถว' : '') +
      (r.kept_formula_cols && r.kept_formula_cols.length ? ' · ช่องที่เป็นสูตรในคอลัมน์ ' + r.kept_formula_cols.join(', ') + ' ระบบไม่ได้เขียนทับ ให้ชีตคำนวณเอง' : '') + '</div>' +
      (r.master_saved ? '<p class="mut">🚚 เก็บข้อมูลรถ/พขร. ' + r.master_saved + ' คันแล้ว (ใช้เติมอัตโนมัติ)</p>' : '') +
      (r.master_note ? '<div class="box bad">' + esc(r.master_note) + '</div>' : '') +
      '<p class="mut">' + esc(r.note || '') + '</p><p class="mut">ปิดหน้าต่างนี้เพื่อดูผลในหน้าแผนงาน (เปลี่ยนไปวันที่ ' + dmy(r.date) + ' ให้แล้ว)</p>');
    document.getElementById('date').value = r.date; load(true);
    if(r.master_saved){ CARS = null; loadCars(); }
  }catch(e){ impBody('<div class="box bad">เขียนไม่สำเร็จ: ' + esc(e.message) + '</div>'); }
}

// ── วางข้อมูลที่ลูกค้าให้มา (10 คอลัมน์ G–P) → แถวเต็ม A–Z → ตรวจ/แก้ในหน้าต่างเดียวกับนำเข้า Excel ──
const PASTE_MAP = [['เวลาส่งมอบ', 6], ['เลขออเดอร์', 7], ['เลขโหลด', 8], ['น้ำหนักบรรทุก', 9], ['น้ำหนักสุทธิ', 10],
                   ['ต้นทาง', 11], ['ปลายทาง', 12], ['Drop', 13], ['หมายเหตุ', 14], ['เบอร์รถ', 15]];
function parseTsv(txt){                  // Tab คั่นช่อง, ขึ้นบรรทัดใหม่คั่นแถว; ช่องที่ครอบด้วย "..." ขึ้นบรรทัดใหม่/Tab ข้างในได้ ("" = เครื่องหมายคำพูด)
  const TAB = String.fromCharCode(9), NL = String.fromCharCode(10), CR = String.fromCharCode(13), Q = String.fromCharCode(34);
  const rows = []; let row = [], cell = '', inq = false, started = false;
  const endCell = () => { row.push(cell.split(NL).join(' ').split(CR).join('').trim()); cell = ''; started = false; };
  const endRow = () => { endCell(); if(row.some(c => c !== '')) rows.push(row); row = []; };
  for(let i = 0; i < txt.length; i++){
    const ch = txt[i];
    if(inq){
      if(ch === Q){ if(txt[i + 1] === Q){ cell += Q; i++; } else inq = false; }
      else cell += ch;
    }else if(ch === Q && !started){ inq = true; started = true; }
    else if(ch === TAB){ endCell(); }
    else if(ch === NL){ endRow(); }
    else if(ch === CR){ /* ข้าม */ }
    else { cell += ch; started = true; }
  }
  if(cell !== '' || row.length) endRow();
  return rows;
}
const PASTE_EXTRA = [['เที่ยววิ่ง', 4], ['ประเภทรถ', 16], ['ทะเบียนรถ', 17], ['พขร.1', 18], ['พขร.2', 19], ['เบอร์โทร.1', 20], ['เบอร์โทร.2', 21],
                     ['เวลาออกจากฟรีต', 23], ['เวลาเข้าโหลด', 24], ['เวลาโทรตามพขร', 25]];     // ใส่มาในหัวตารางก็ได้ ไม่ใส่ก็ได้
function tp(s){                          // 'HH:MM[:SS]' → [ชม., นาที, วินาที] ไม่ใช่เวลา = null
  const p = String(s).trim().split(':');
  if(p.length < 2 || p.length > 3 || p.some(x => x === '' || isNaN(Number(x)))) return null;
  return [Number(p[0]), Number(p[1]), Number(p[2] || 0)];
}
function pad2(n){ return (n < 10 ? '0' : '') + n; }
function fmtStamp(d){ return pad2(d.getDate()) + '/' + pad2(d.getMonth() + 1) + '/' + d.getFullYear() + ' ' + pad2(d.getHours()) + ':' + pad2(d.getMinutes()) + ':' + pad2(d.getSeconds()); }
function parseStamp(s){                  // 'dd/mm/yyyy HH:MM[:SS]' (คั่นด้วยเครื่องหมายจุลภาคก็ได้)
  const parts = String(s).split(',').join(' ').split(' ').filter(x => x !== '');
  if(parts.length !== 2) return null;
  const dm = parts[0].split('/'), t = tp(parts[1]);
  if(dm.length !== 3 || !t) return null;
  const y = Number(dm[2]) > 2400 ? Number(dm[2]) - 543 : Number(dm[2]);
  return new Date(y, Number(dm[1]) - 1, Number(dm[0]), t[0], t[1], t[2]);
}
function stampFrom(v, ref){              // ค่าที่วางมาเป็นเวลาล้วน (เช่น 08:00) → วันที่เต็ม: วันเดียวกับ ref ถ้าไม่เลยเวลา ref ไม่งั้นเลื่อนเป็นวันก่อนหน้า
  const t = tp(v);
  if(!t){ const d = parseStamp(v); return d; }
  const d = new Date(ref.getFullYear(), ref.getMonth(), ref.getDate(), t[0], t[1], t[2]);
  if(d > ref) d.setDate(d.getDate() - 1);
  return d;
}
function pasteParse(txt, iso, used){
  const TAB = String.fromCharCode(9), NL = String.fromCharCode(10), CR = String.fromCharCode(13);
  const grid = parseTsv(txt);
  if(!grid.length) return {err: 'ยังไม่ได้วางข้อมูล'};
  const norm = c => String(c).split(' ').join('');
  let pos = PASTE_MAP.map(m => m[1] - 6), body = grid;                 // ไม่มีหัวตาราง: เรียงตามลำดับ 10 คอลัมน์
  let epos = PASTE_EXTRA.map(() => -1);
  const head = grid[0].map(norm);
  if(head.some(c => c.indexOf('เบอร์รถ') === 0 || c.indexOf('เวลาส่งมอบ') === 0 || c.indexOf('เลขออเดอร์') === 0)){
    pos = PASTE_MAP.map(m => head.findIndex(c => c.indexOf(norm(m[0])) === 0));   // มีหัวตาราง: จับคู่ตามชื่อ ลำดับสลับได้
    epos = PASTE_EXTRA.map(m => head.findIndex(c => c.indexOf(norm(m[0])) === 0));
    body = grid.slice(1);
    if(pos[6] < 0) return {err: 'ไม่พบคอลัมน์ "ปลายทาง" ในหัวตารางที่วาง'};
  }else if(Math.max.apply(null, grid.map(r => r.length)) > 10){
    return {err: 'ข้อมูลที่วางมี ' + Math.max.apply(null, grid.map(r => r.length)) + ' คอลัมน์ แต่ต้องเป็น 10 คอลัมน์ตามลำดับ (หรือวางพร้อมบรรทัดหัวตาราง)'};
  }
  const last = {}, rows = []; let tripFull = 0; used = used || {};
  body.forEach(r => {
    const out = new Array(26).fill('');
    PASTE_MAP.forEach((m, k) => { if(pos[k] >= 0 && pos[k] < r.length) out[m[1]] = r[pos[k]]; });
    if(!out.some((v, i) => i >= 6 && i <= 15 && v !== '')) return;      // แถวว่างทั้งแถว
    PASTE_EXTRA.forEach((m, k) => { if(epos[k] >= 0 && epos[k] < r.length && r[epos[k]] !== '') out[m[1]] = r[epos[k]]; });
    const car = out[15];
    let n = 1;
    const given = parseInt(String(out[4]).split(' ')[1], 10);           // ถ้าลูกค้า/คุณใส่เที่ยววิ่งมาในหัวตาราง ใช้ตามนั้น
    const dropNo = parseInt(String(out[13]).trim(), 10) || 1;
    if(car){
      const u = used[car] = used[car] || {};                            // u[เที่ยว][Drop] = ใช้แล้ว (จากชีตของวันนั้น + แถวที่วางมาก่อนหน้า)
      if(given){ n = given; }
      else{
        if(dropNo > 1){                                                 // Drop 2+ = จุดส่งถัดไปของเที่ยวเดิม: ต่อเที่ยวล่าสุดของรถคันนี้ในชุดที่วาง หรือเที่ยวที่มี Drop ก่อนหน้าแต่ยังไม่มี Drop นี้
          if(last[car]) n = last[car];
          else { n = 0; for(let k = 1; k <= 3; k++) if(u[k] && u[k][dropNo - 1] && !u[k][dropNo]){ n = k; break; } if(!n) n = 1; }
        }
        while(u[n] && u[n][dropNo]) n++;                                // เที่ยวนี้ Drop นี้ถูกใช้แล้ว → เที่ยวถัดไป
      }
      (u[n] = u[n] || {})[dropNo] = 1; last[car] = n;
    }
    if(!given){
      if(n > 3) tripFull++;                                             // เกิน 3 เที่ยว: เว้นว่างให้เลือกเอง ดีกว่าให้เลข JOB ซ้ำ
      out[4] = n > 3 ? '' : 'เที่ยว ' + n;
    }
    out[2] = dmy(iso); out[5] = dmy(iso);
    const c = CARS && car && CARS[car];                                 // เติมประเภท/ทะเบียน/พขร. จากข้อมูลรถ (เฉพาะช่องที่ยังว่าง ไม่ทับที่วางมา)
    if(c){ [[16, 't'], [17, 'plate'], [18, 'd1'], [19, 'd2']].forEach(f => { if(!out[f[0]]) out[f[0]] = c[f[1]] || ''; }); }
    [[18, 20, 'p1'], [19, 21, 'p2']].forEach(f => {                     // เบอร์โทรอิงตามชื่อ พขร. (ตรงกันเสมอ)
      if(out[f[0]] && !out[f[1]]) out[f[1]] = PHONES[out[f[0]]] || ((c && c['d' + f[2][1]] === out[f[0]]) ? c[f[2]] : '') || '';
    });
    // เวลา (P): วางมาเป็นเวลาล้วนก็ได้ ระบบเติมวันที่ให้ — ถ้ามีเวลาเข้าโหลด แต่ช่องออกจากฟรีต/โทรตามว่าง คำนวณตามสูตรในไฟล์จัดงาน (เข้าโหลด − 30 นาที, แล้ว − 1 ชม.)
    const tdel = tp(out[6]), ref0 = tdel ? new Date(Number(iso.slice(0, 4)), Number(iso.slice(5, 7)) - 1, Number(iso.slice(8, 10)), tdel[0], tdel[1], tdel[2]) : null;
    let dY = null, dX = null, dZ = null;
    if(ref0){
      if(out[24]) dY = stampFrom(out[24], ref0);
      if(out[23]) dX = stampFrom(out[23], dY || ref0);
      if(out[25]) dZ = stampFrom(out[25], dX || dY || ref0);
      if(dY && !out[23]) dX = new Date(dY.getTime() - 30 * 60000);
      if(dX && !out[25]) dZ = new Date(dX.getTime() - 60 * 60000);
      if(dY) out[24] = fmtStamp(dY);
      if(dX) out[23] = fmtStamp(dX);
      if(dZ) out[25] = fmtStamp(dZ);
    }
    rows.push(out);
  });
  if(!rows.length) return {err: 'ไม่พบแถวข้อมูลในที่วาง'};
  return {rows: rows, tripFull: tripFull};
}
async function pasteGo(){
  const iso = document.getElementById('pasteDate').value;
  if(!iso){ impBody('<div class="box bad">เลือกวันที่ของงานก่อน</div>'); return; }
  impBody('<p class="mut">กำลังตรวจข้อมูล...</p>');
  try{
    await loadOpts();
    if(!CARS) await loadCars();
    const used = {};                                                    // เที่ยวที่รถแต่ละคันมีอยู่แล้วในชีตของวันนั้น (กันเลข JOB ซ้ำ)
    try{
      const pr = await fetch('/api/plan?date=' + iso);
      if(pr.ok) ((await pr.json()).rows || []).forEach(x => {
        const car = String(x.cells[15] || '').trim(), t = parseInt(String(x.cells[4] || '').split(' ')[1], 10);
        const dn = parseInt(String(x.cells[13] || ''), 10) || 1;
        if(car && t) ((used[car] = used[car] || {})[t] = used[car][t] || {})[dn] = 1;      // used[รถ][เที่ยว][Drop]
      });
    }catch(e){}
    const usedSheet = JSON.parse(JSON.stringify(used));
    const res = pasteParse(document.getElementById('pasteTxt').value, iso, used);
    if(res.err){ impBody('<div class="box bad">' + esc(res.err) + '</div>'); return; }
    const j = await impSend({rows: res.rows, near: true});
    if(!j) return;
    if(res.tripFull){ j.warnings = ['รถบางคันมีครบ 3 เที่ยวแล้ว ' + res.tripFull + ' แถว — เว้นช่องเที่ยววิ่งไว้ให้เลือกเอง (กันเลข JOB ซ้ำ)'].concat(j.warnings || []); j.warnings_total = (j.warnings_total || 0) + 1; }
    IMP = {rows: j.rows, headers: DATA.headers.map(h => h.name || h.col), edited: {}, errs: {}, warns: {}, info: j, replace: false,
           onlyBad: false, master: null, near: true, usedSheet: usedSheet};
    impMarkErrors(j);
    impRender();
  }catch(e){ impBody('<div class="box bad">ตรวจข้อมูลไม่ได้: ' + esc(e.message) + '</div>'); }
}
function openImp(paste){
  document.getElementById('impBack').hidden = false;
  if(paste){
    const d = document.getElementById('pasteDate'); if(!d.value) d.value = DATA ? DATA.date : '';
    document.getElementById('pasteTxt').focus();
  }
}
document.addEventListener('keydown', e => {                       // Ctrl+Z ในหน้าต่างตรวจข้อมูล (ไม่ใช่ตอนกำลังพิมพ์ในช่อง)
  if(!IMP || document.getElementById('impBack').hidden || !(e.ctrlKey || e.metaKey) || e.key !== 'z') return;
  if(e.target.closest && e.target.closest('input,select,textarea')) return;
  e.preventDefault(); impUndo();
});
document.getElementById('pasteGo').onclick = pasteGo;
document.getElementById('pasteOpen').onclick = () => openImp(true);
document.getElementById('impOpen').onclick = () => openImp(false);
document.getElementById('impClose').onclick = () => { document.getElementById('impBack').hidden = true; };
document.getElementById('impFile').onchange = e => { IMPFILE = e.target.files[0] || null; if(IMPFILE) impPreview(); };

buildChips();
loadWho().then(() => load()).then(resumeOutbox);
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
  .side .menu.out{margin-top:auto;color:var(--mut);font-size:13px;white-space:nowrap}
  @media (max-width:820px){ .side .menu.out{flex:0 0 auto;margin-top:0} .side .menu.out span{display:none} }
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
  <a class="menu" href="/report">📊 รายงาน On Time</a>
  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>
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
