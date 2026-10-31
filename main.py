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
PLAN_TRIP_SEQ= 3   # D  ลำดับเที่ยว (เลขเที่ยวของวัน — drop ของเที่ยวเดียวกันได้เลขเดียวกัน)
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


# ผู้ใช้แต่ละคนอยู่ในแท็บ "User" ของไฟล์ ChaseLog (PLAN_ID) — แก้ได้ทั้งในชีตและหน้า /users บนเว็บ (เฉพาะผู้ดูแล)
# หัวตาราง: ชื่อผู้ใช้ | รหัสผ่าน | เช็กรถ | แผนงาน | รายงาน | รถ/คนพร้อมใช้ | ผู้ดูแล | ใช้งาน   (ติ๊ก = เปิดหน้านั้นได้)
#   ชีตเก่าที่ยังไม่มีคอลัมน์ "รถ/คนพร้อมใช้" = ใช้สิทธิ์เดียวกับ "รายงาน" · ยังไม่มี "ผู้ดูแล" = ผู้ดูแลคือคนที่ติ๊กครบทุกหน้า
#   รหัสผ่านที่ตั้งจากเว็บเก็บแบบ hash (pbkdf2_sha256$...) — รหัสตัวอักษรตรงๆ ที่พิมพ์ในชีตเองยังใช้ได้
# รหัสกลาง APP_PASSWORD ยังเข้าได้ทุกหน้าเสมอ (กันล็อกตัวเองออกถ้าชีตมีปัญหา)
USERS_TAB  = os.environ.get("USERS_TAB", "User")
USERS_TTL  = 60                                      # อ่านชีตผู้ใช้ใหม่ทุก 1 นาที (ปิดบัญชีแล้วมีผลเร็ว)
# ── หน้าเว็บทั้งหมด ── เพิ่มรายงานใหม่ = เพิ่มบรรทัดที่นี่บรรทัดเดียว แล้วได้ครบ:
#    เมนูซ้ายทุกหน้า · สิทธิ์เข้าหน้า/API · ช่องติ๊กในหน้า 👥 ผู้ใช้ · คอลัมน์ในแท็บ User (เว็บเติมให้เอง)
#    key     = ชื่อสิทธิ์ (ภาษาอังกฤษสั้นๆ ห้ามซ้ำ)        head  = หัวคอลัมน์ในแท็บ User (ห้ามซ้ำ)
#    menu    = ชื่อในเมนู + ไอคอน                        path  = ที่อยู่หน้า · api = ที่อยู่ API ที่หน้านั้นเรียก (ขึ้นต้นด้วย)
#    inherit = ตอนเพิ่มคอลัมน์ให้ครั้งแรก ใครมีสิทธิ์นี้อยู่แล้วได้ติ๊กหน้าใหม่ด้วย (None = ไม่มีใครได้ ผู้ดูแลไปติ๊กเอง)
#    alias   = หัวคอลัมน์ชื่อเก่าที่ยังให้ใช้ได้
PAGES = [
    {"key": "car",    "head": "เช็กรถ",        "alias": ("เช็ครถ",),  "menu": "🚛 เช็กรถ",          "path": "/",
     "api": ("/api/trips", "/api/chase", "/api/timeline", "/api/match"), "inherit": None},
    {"key": "plan",   "head": "แผนงาน",        "alias": (),           "menu": "📋 แผนงาน",          "path": "/plan",
     "api": ("/api/plan",), "inherit": None},
    {"key": "report", "head": "รายงาน",        "alias": (),           "menu": "📊 รายงาน On Time",  "path": "/report",
     "api": ("/api/report/ontime",), "inherit": None},
    {"key": "ready",  "head": "รถ/คนพร้อมใช้",  "alias": ("พร้อมใช้",), "menu": "🚦 รถ/คนพร้อมใช้",   "path": "/ready",
     "api": ("/api/report/ready",), "inherit": "report"},
    # ตัวอย่างรายงานใหม่ (ลบ # ออก แล้วทำหน้า /fuel กับ API /api/report/fuel):
    # {"key": "fuel", "head": "รายงานน้ำมัน", "alias": (), "menu": "⛽ รายงานน้ำมัน", "path": "/fuel",
    #  "api": ("/api/report/fuel",), "inherit": "report"},
]
ADMIN_MENU = [("/users", "👥 ผู้ใช้")]                 # หน้าของผู้ดูแล (โชว์ในเมนูเฉพาะผู้ดูแล) — /settings เข้าจากลิงก์ในหน้าเดิม
PAGE_PERMS = tuple(p["key"] for p in PAGES)
PERMS_ALL  = frozenset(PAGE_PERMS + ("admin",))
PERM_PAGES = [(p["key"], p["path"]) for p in PAGES]
PERM_HEAD  = dict({p["key"]: p["head"] for p in PAGES}, admin="ผู้ดูแล")
_PERM_API  = sorted(((a, p["key"]) for p in PAGES for a in p["api"]), key=lambda x: -len(x[0]))
_TRUE_MARKS = {"✓", "✔", "☑", "true", "yes", "y", "1", "x", "ใช่", "/"}
_users_cache: dict = {"ts": 0.0, "data": None}


def _users_sheet_id() -> str:
    return os.environ.get("USERS_SHEET_ID") or PLAN_ID


def _load_users_rows() -> list:
    gc = gspread.authorize(_build_creds())
    return gc.open_by_key(_users_sheet_id()).worksheet(USERS_TAB).get_all_values()


def _users_layout(rows: list):
    """หาแถวหัวตาราง + คอลัมน์ของแต่ละช่องในแท็บ User → (แถวหัว, {ช่อง: คอลัมน์}) · ไม่เจอ = (None, {})"""
    # แถวหัว = มีทั้งช่องชื่อผู้ใช้และช่องรหัส (กันแถวหัวเรื่องอย่าง "รายชื่อผู้ใช้ระบบ" ที่มีคำว่า ชื่อผู้ใช้ เหมือนกัน)
    is_user = lambda c: c.strip() == "ชื่อผู้ใช้" or c.strip().lower() in ("user", "username")
    is_pw = lambda c: "รหัส" in c or "pass" in c.lower()
    hdr = next((n for n, r in enumerate(rows[:10]) if any(is_user(c) for c in r) and any(is_pw(c) for c in r)), None)
    if hdr is None:
        return None, {}
    h = [c.strip().lower() for c in rows[hdr]]
    find = lambda *keys: next((n for n, c in enumerate(h) if any(k in c for k in keys)), None)
    names = {n.lower() for p in PAGES for n in (p["head"],) + tuple(p["alias"])}

    def page_col(p):
        own = [p["head"].lower()] + [a.lower() for a in p["alias"]]
        exact = next((n for n, c in enumerate(h) if c in own), None)
        if exact is not None:
            return exact
        return next((n for n, c in enumerate(h) if c not in names and any(k in c for k in own)), None)

    cols = {"user": find("ชื่อผู้ใช้", "user"), "pw": find("รหัส", "pass"), "active": find("ใช้งาน", "active"),
            "admin": find("ผู้ดูแล", "admin"), "last": find("เข้าใช้ล่าสุด", "last login")}
    cols.update({p["key"]: page_col(p) for p in PAGES})
    return hdr, cols


def _row_perms(cell, on, cols: dict) -> frozenset:
    """สิทธิ์ของแถวหนึ่ง — หน้าที่ยังไม่มีคอลัมน์ในชีต ใช้สิทธิ์ตาม inherit ของหน้านั้น · ผู้ดูแล (ไม่มีคอลัมน์) = ติ๊กครบทุกหน้า"""
    perms = set()
    for p in PAGES:
        col = cols.get(p["key"])
        if col is not None:
            if on(col):
                perms.add(p["key"])
        elif p["inherit"] and p["inherit"] in perms:
            perms.add(p["key"])
    if cols.get("admin") is None:
        if all(k in perms for k in PAGE_PERMS):
            perms.add("admin")
    elif on(cols["admin"]):
        perms.add("admin")
    return frozenset(perms)


def _parse_users(rows: list) -> dict:
    """แถวจากชีต → {ชื่อผู้ใช้ (ตัวเล็ก): {"pw": รหัส, "perms": {...}}} — ข้ามคนที่ไม่ได้ติ๊ก "ใช้งาน" หรือไม่ได้ติ๊กหน้าไหนเลย"""
    hdr, cols = _users_layout(rows)
    if hdr is None or cols["user"] is None or cols["pw"] is None:
        return {}
    out = {}
    for r in rows[hdr + 1:]:
        cell = lambda n: r[n].strip() if n is not None and n < len(r) else ""
        on = lambda n: cell(n).lower() in _TRUE_MARKS
        user, pw = cell(cols["user"]).lower(), cell(cols["pw"])
        if not user or not pw or (cols["active"] is not None and not on(cols["active"])):
            continue
        perms = _row_perms(cell, on, cols)
        if perms - {"admin"}:
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
    """หน้า/API นี้ต้องมีสิทธิ์อะไร: key ของหน้าใน PAGES / "" (ทุกคน) / admin (ผู้ดูแล: ตั้งค่า, จัดการผู้ใช้ ฯลฯ)"""
    if path in ("/logout", "/favicon.ico"):
        return ""
    page = next((p["key"] for p in PAGES if p["path"] == path), None)
    if page:
        return page
    api = next((k for a, k in _PERM_API if path == a or path.startswith(a + "/")), None)
    return api or "admin"                            # ตั้งค่า / ผู้ใช้ / debug / docs ฯลฯ


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
    """เมนูซ้ายจากทะเบียน PAGES — โชว์เฉพาะหน้าที่คนนี้มีสิทธิ์ และไฮไลต์หน้าที่เปิดอยู่"""
    perms = getattr(request.state, "perms", PERMS_ALL)
    here = request.url.path
    items = [(p["path"], p["menu"]) for p in PAGES if p["key"] in perms]
    items += [(u, t) for u, t in ADMIN_MENU if "admin" in perms]
    menu = "".join(f'  <a class="menu{" on" if u == here else ""}" href="{u}">{t}</a>\n' for u, t in items)
    side = ('<aside class="side">\n' + menu +
            '  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>\n</aside>')
    html = re.sub(r'<aside class="side">.*?</aside>', lambda _m: side, html, count=1, flags=re.S)
    if "admin" not in perms:                          # ลิงก์อื่นในหน้าที่ชี้ไปหน้าผู้ดูแล
        html = re.sub(r'<a\b[^>]*\bhref="/(?:settings|users)"[^>]*>.*?</a>\s*', "", html)
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
        if not need or need in perms:
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


def _fresh_read(pairs) -> None:
    """ปุ่ม 🔄 รีเฟรช: ให้แท็บเหล่านี้อ่านจาก Google สดรอบนี้ — เก็บของเดิมไว้ ถ้าอ่านสดไม่ได้ (โควตาเต็ม) ยังมีของเดิมโชว์
    ไม่ถี่กว่า PLAN_FRESH_MIN_SECS วินาทีต่อแท็บ กันหลายคนกดรัวจนชนโควตา Google Sheets"""
    for sid, tab in pairs:
        key = f"{sid}:{tab}"
        old = _sheet_cache.get(key)
        if old and time() - old[0] >= PLAN_FRESH_MIN_SECS:
            _sheet_cache[key] = (0.0, old[1])


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
    from collections import Counter
    have = set()
    sec_all, sec_nonum = Counter(), Counter()          # งานที่ยังไม่มีเลข: เทียบด้วย ต้นทาง+ปลายทาง+เวลาส่งมอบ+Drop (นับจำนวน กันงานเหมือนกันหลายคัน)
    for r in sheet:
        if _parse_date(_cell(r, PLAN_DATE)) == date_iso:
            cells = [_cell(r, c) for c in range(PLAN_LAST_COL)]
            k, sk = _dup_key(cells), _dup_sec(cells)
            if k:
                have.add(k)
            if sk:
                sec_all[sk] += 1
                if not k:
                    sec_nonum[sk] += 1
    out = []
    for n, r in enumerate(rows):
        k, sk = _dup_key(r), _dup_sec(r)
        if k is not None and k in have:
            out.append(n)
        elif sk and (sec_nonum if k is not None else sec_all)[sk] > 0:     # ฝั่งใดฝั่งหนึ่งยังไม่มีเลข → เทียบด้วยงาน/เวลา
            (sec_nonum if k is not None else sec_all)[sk] -= 1
            out.append(n)
    return out


def _dup_sec(r: list):
    """กุญแจสำรองสำหรับงานที่ยังไม่มีเลขออเดอร์/เลขโหลด: ต้นทาง + ปลายทาง + เวลาส่งมอบ + Drop"""
    if len(r) <= 13 or not str(r[12]).strip():
        return None
    return (str(r[11]).strip().upper(), re.sub(r"\s+", "", str(r[12])), _cell_time(str(r[6])) or str(r[6]).strip(), str(r[13]).strip() or "1")


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
    for _a, idx, first in placed:                        # มีคนแทรก/เขียนพร้อมกันจนแถวเลื่อน → แถวที่จะเขียนไม่ว่างแล้ว → หยุด ไม่เขียนทับงานคนอื่น
        try:
            got = ws.get(f"M{first}:M{first + len(idx) - 1}") or []
        except Exception:
            got = []
        if any(str(c).strip() for r in got for c in r):
            raise HTTPException(status_code=409, detail="มีคนเพิ่มงานเข้าชีตพร้อมกันพอดี ระบบหยุดไว้ไม่ให้เขียนทับงานของคนอื่น — "
                                                        "รอสักครู่แล้วกดเขียนอีกครั้ง (งานที่ลงไปแล้วระบบจะข้ามให้ ไม่ซ้ำ) และลบแถวว่างที่เกินในชีตถ้ามี")
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
    if rv["date"]:                                # ทุกโหมด (วาง/ดึงแผนรถ/Excel): เตือนงานที่ซ้ำกับในชีต (ไม่เช็กตอนนำเข้าไฟล์ เพราะนั้นแทนที่ทั้งวันอยู่แล้ว)
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
    adding = bool(near) or not replace             # เพิ่มเข้าวันเดิม (ไม่แทนที่ทั้งวัน) → งานซ้ำต้องข้าม
    if adding and skip_dups and dups:              # ข้ามแถวที่ซ้ำกับชีต (อ่านสดอีกรอบก่อนตัดสิน)
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
        if adding and hit:                                # วางข้อมูล/Excel แบบไม่แทนที่ เข้าวันที่มีอยู่แล้ว: เพิ่มโดยไม่ลบ แทรกติดรถคันเดิม
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


def _area_of(text: str) -> str:
    """ข้อความใดๆ → พื้นที่ประจำรถ: 'ศรีราชา' / 'บางปะกง' (บางประกง ก็นับ) / '' """
    t = (text or "").replace(" ", "")
    if "ศรีราชา" in t:
        return "ศรีราชา"
    if "บางปะกง" in t or "บางประกง" in t:
        return "บางปะกง"
    return ""


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
        acol = next((k for k, c in enumerate(hc) if "พื้นที่" in c), None)      # คอลัมน์ "ประจำพื้นที่" (ถ้ามี)
        for r in rows[h + 1:]:
            car = _cell(r, ix["เบอร์รถ"])
            if _CAR_RE.match(car):
                e = cars.setdefault(car, blank())
                e["plate"] = _cell(r, ix["ทะเบียนรถ"])
                e["t"] = norm_type(_cell(r, tcol)) if tcol is not None else ""
                if acol is not None and _area_of(_cell(r, acol)):
                    e["area"] = _area_of(_cell(r, acol))

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
        starts = [b[0] for b in blocks]
        block_area = {}                        # ชื่อพื้นที่เหนือ/ข้างหัวตารางแต่ละชุด เช่น "บางปะกง" | "ศรีราชา"
        for bi, jc in enumerate(starts):
            end = starts[bi + 1] if bi + 1 < len(starts) else jc + 10
            for rr in rows[max(0, h - 6): h + 1]:
                hit = next((_area_of(_cell(rr, k)) for k in range(max(0, jc - 2), end) if _area_of(_cell(rr, k))), "")
                if hit:
                    block_area[jc] = hit
        for r in rows[h + 1:]:
            for jc, j1, j2, jt in blocks:
                car = _cell(r, jc)
                if not _CAR_RE.match(car):
                    continue
                e = cars.setdefault(car, blank())
                if block_area.get(jc) and not e.get("area"):
                    e["area"] = block_area[jc]
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


# ชีต "แผนรถ PTGLG" — แท็บรายวันชื่อ "21-Oct-2026" · อ่านอย่างเดียว ไม่เขียนกลับ
# งาน SC  : E ปลายทาง · F ปริมาณ · G เวลาจัดส่ง · H เลข ATL · J เงื่อนไข · B ขนส่ง        (ต้นทาง = FLEET_SC_ORIGIN)
# งานภูมิภาค: K คลัง(ต้นทาง) · L ขนส่ง · N ปลายทาง · O ปริมาณ · P เวลาจัดส่ง · Q เลข ATL · U เลขโหลด · V เงื่อนไข
FLEET_SHEET_ID  = os.environ.get("FLEET_SHEET_ID", "1j0CLmJYxqiLghAoDzLll0ykyATWY3N1MASEUBMZmmlc")
FLEET_SC_ORIGIN = os.environ.get("FLEET_SC_ORIGIN", "SC BPK")
FLEET_CARRIER   = os.environ.get("FLEET_CARRIER", "PTGLG")     # เอาเฉพาะงานของขนส่งนี้
_MONTHS = {m: i for i, m in enumerate(["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"], 1)}
_fleet_tabs_cache: dict = {"ts": 0.0, "data": None}
FLEET_HEAD = ["เวลาส่งมอบ", "เลขออเดอร์", "เลขโหลด", "น้ำหนักบรรทุก", "ต้นทาง", "ปลายทาง", "หมายเหตุ"]


def _fleet_tab_date(title: str) -> Optional[str]:
    """'21-Oct-2026' → '2026-10-21' (ชื่อแท็บแบบอื่น = None)"""
    m = re.fullmatch(r"\s*(\d{1,2})-([A-Za-z]{3})-(\d{4})\s*", title or "")
    if not m or m.group(2).lower() not in _MONTHS:
        return None
    try:
        return datetime(int(m.group(3)), _MONTHS[m.group(2).lower()], int(m.group(1))).strftime("%Y-%m-%d")
    except ValueError:
        return None


def _load_fleet_titles() -> list:
    gc = gspread.authorize(_build_creds())
    return [ws.title for ws in gc.open_by_key(FLEET_SHEET_ID).worksheets()]


def _fleet_tabs() -> list:
    """[(วันที่ iso, ชื่อแท็บ)] เรียงใหม่ → เก่า (แคช 60 วินาที)"""
    now = time()
    if _fleet_tabs_cache["data"] is None or now - _fleet_tabs_cache["ts"] > 60:
        titles = _with_retry(_load_fleet_titles)
        _fleet_tabs_cache.update(ts=now, data=sorted(((d, t) for t in titles if (d := _fleet_tab_date(t))), reverse=True))
    return _fleet_tabs_cache["data"]


FLEET_ORIGINS = ["SC BPK", "PTT TANK", "BSRC", "UAC", "IRPC"]     # ต้นทางที่ใช้ในชีตแผนงาน


def _fleet_origin(v: str) -> str:
    """ชื่อคลังในชีตแผนรถ → ชื่อต้นทางมาตรฐาน: 'BSRC IN' → 'BSRC', 'PTT Tank' → 'PTT TANK', 'SC' → 'SC BPK' (ไม่รู้จัก = คืนตามเดิมตัวใหญ่)"""
    u = re.sub(r"\s+", " ", (v or "").upper()).strip()
    for canon in FLEET_ORIGINS:
        if u == canon or u.startswith(canon + " ") or u.split(" ")[0] == canon.split(" ")[0] and canon.split(" ")[0] != "PTT":
            return canon
    if u.startswith("PTT") and "TANK" in u:
        return "PTT TANK"
    return u


def _fleet_time(v: str) -> str:
    """'15:00:00' → '15:00' · เศษวันแบบ Excel (0.5) → '12:00' · อื่นๆ คืนตามเดิม"""
    v = (v or "").strip()
    m = re.match(r"^(\d{1,2}):(\d{2})", v)
    if m:
        return f"{int(m.group(1)):02d}:{m.group(2)}"
    try:
        f = float(v)
        if 0 <= f < 1:
            mins = round(f * 24 * 60)
            return f"{mins // 60:02d}:{mins % 60:02d}"
    except ValueError:
        pass
    return v


def _fleet_rows(grid: list) -> tuple:
    """ตารางจากแท็บแผนรถ → (แถวสำหรับวาง, จำนวนแถวที่ข้าม) — ใช้ทั้งฝั่งงาน SC และงานภูมิภาค"""
    hdr = next((i for i, r in enumerate(grid[:30]) if any((c or "").strip().lower() == "customer" for c in r)), None)
    if hdr is None:
        return [], 0
    cell = lambda r, i: re.sub(r"\s+", " ", (r[i] if i < len(r) else "") or "").strip()
    order = lambda v: v if (not v or v.upper().startswith("ATL")) else "ATL-" + v
    carrier_ok = lambda v: not FLEET_CARRIER or not v or FLEET_CARRIER.lower() in v.lower()
    out, skipped = [], 0
    for r in grid[hdr + 1:]:
        for side in ("sc", "reg"):
            if side == "sc":
                dest, qty, tm, atl, load, cond, carrier, origin = (cell(r, 4), cell(r, 5), cell(r, 6), cell(r, 7), "", cell(r, 9),
                                                                  cell(r, 1), FLEET_SC_ORIGIN)
            else:
                dest, qty, tm, atl, load, cond, carrier, origin = (cell(r, 13), cell(r, 14), cell(r, 15), cell(r, 16), cell(r, 20),
                                                                  cell(r, 21), cell(r, 11), _fleet_origin(cell(r, 10)))
            if not dest or "ยอดออก" in dest:
                continue
            if not carrier_ok(carrier):
                skipped += 1
                continue
            out.append([_fleet_time(tm), order(atl), load, qty.replace(",", ""), origin, dest, cond])
    rank = {o: n for n, o in enumerate(FLEET_ORIGINS)}
    out.sort(key=lambda r: rank.get(r[4], len(rank)))          # sort เสถียร: ภายในต้นทางเดียวกันยังเรียงตามชีต
    return out, skipped


@app.get("/api/plan/fleet", include_in_schema=False)
def plan_fleet(date: str = "", only_tabs: int = Query(0, alias="list")):
    """ดึงงานจากชีตแผนรถ PTGLG (แท็บวันที่ที่เลือก หรือวันล่าสุด) เป็นตารางสำหรับวางในหน้าแผนงาน — อ่านอย่างเดียว"""
    try:
        tabs = _fleet_tabs()
    except Exception as e:
        raise HTTPException(502, f"เปิดชีตแผนรถไม่ได้ — ตรวจว่าแชร์ให้บัญชีระบบแล้ว ({type(e).__name__})")
    if not tabs:
        raise HTTPException(404, "ไม่พบแท็บวันที่ (เช่น 21-Oct-2026) ในชีตแผนรถ")
    today = _today_thai()
    default = today if any(t[0] == today for t in tabs) else tabs[0][0]      # ค่าเริ่ม = วันนี้ (ถ้ามีแท็บ) ไม่งั้นแท็บล่าสุด
    if only_tabs:
        return {"tabs": [t[0] for t in tabs[:31]], "default": default}
    want = _parse_date(date) if date else default
    pick = next((t for t in tabs if t[0] == want), None)
    if not pick:
        raise HTTPException(404, f"ไม่พบแท็บวันที่ {want} ในชีตแผนรถ")
    try:
        grid = _fetch_sheet(FLEET_SHEET_ID, pick[1])
    except Exception as e:
        raise HTTPException(502, f"อ่านแท็บ {pick[1]} ไม่ได้ — {type(e).__name__}")
    rows, skipped = _fleet_rows(grid)
    return {"date": pick[0], "tab": pick[1], "tabs": [t[0] for t in tabs[:14]], "head": FLEET_HEAD, "rows": rows, "skipped": skipped}


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
def report_ontime(date_from: str = Query(None, alias="from"), date_to: str = Query(None, alias="to"), fresh: int = Query(0),
                  origin: str = "", vtype: str = "", car: str = "", drop: str = "", status: str = "",
                  dest: str = "", cls: str = "", jtype: str = "", why: str = "", fix: str = ""):
    """รายงาน On Time ของช่วงวันที่ (ค่าเริ่มต้น = วันนี้) — อ่านชีตแผนงานจริงอย่างเดียว แคช 5 นาทีตามปกติ"""
    d_from = _parse_date(date_from or "") or _today_thai()
    d_to = _parse_date(date_to or "") or d_from
    if d_to < d_from:
        d_from, d_to = d_to, d_from
    if (datetime.strptime(d_to, "%Y-%m-%d") - datetime.strptime(d_from, "%Y-%m-%d")).days > 93:
        raise HTTPException(400, "เลือกช่วงวันที่ได้ไม่เกิน 3 เดือน")
    if fresh:
        global _rep_dist_cache
        _fresh_read([(SOURCE_ID, PLAN_TAB), (DEST_ID, DEST_TAB)])
        _rep_dist_cache = (0.0, _rep_dist_cache[1])
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


# ─── รถ/คนพร้อมใช้งาน (อ่านอย่างเดียว — ชีตข้อมูลรถ+พขร. และชีตแผนงาน) ──────────────────────────
# แท็บ "ข้อมูลรถ" / "ข้อมูลพขร." เก็บสถานะเป็นตารางรายวัน แยกบล็อกตามเดือนเรียงไปทางขวา:
#   แถวเหนือหัวตารางเขียน "สถานะรถพร้อมใช้ ประจำเดือน ตุลาคม Y2026" แล้วหัวตารางเป็น "01 พฤ" "02 ศ" ...
#   ช่องในตารางเป็นรหัส: R รถวิ่งงาน · W รถพร้อมใช้ว่างงาน · D รถพร้อมใช้ไม่มีคนขับ · CM ซ่อมทั่วไป · BD เสียระหว่างทาง ฯลฯ
# คำอธิบายรหัสอ่านจากมุมซ้ายบนของชีตเอง (รหัส | คำอธิบาย) เพิ่ม/แก้รหัสในชีตแล้วหน้านี้รู้ตาม ไม่ต้องแก้โค้ด
# "วิ่งงาน" ยึดจากชีตแผนงานเสมอ ไม่ยึดรหัส R เพราะวันที่ยังไม่ถึงชีตยังไม่ได้ลง R (วันที่ 29–30 ยังเป็น W ทั้งคอลัมน์)
READY_CAR_TAB    = os.environ.get("READY_CAR_TAB", "ข้อมูลรถ")
READY_DRIVER_TAB = os.environ.get("READY_DRIVER_TAB", "ข้อมูลพขร.")
# แถวแรกของข้อมูล (เลขแถวในชีต) — แถวระหว่างหัวตารางกับแถวนี้ไม่ใช่รถ/คนที่ต้องนับ
READY_CAR_FIRST_ROW    = int(os.environ.get("READY_CAR_FIRST_ROW", "20") or 0)
# พขร.: นับจากคอลัมน์ "สถานะ" = พนักงาน (เหมือนกรองในชีต) ไม่ใช้เลขแถว เพราะพนักงานอยู่ปนกับคนลาออกตั้งแต่ใต้หัวตาราง
READY_DRIVER_FIRST_ROW = int(os.environ.get("READY_DRIVER_FIRST_ROW", "0") or 0)
READY_DRIVER_STATUS    = os.environ.get("READY_DRIVER_STATUS", "พนักงาน")   # นับเฉพาะ พขร. ที่คอลัมน์ "สถานะ" เป็นค่านี้
READY_TARGET     = float(os.environ.get("READY_TARGET", "2") or 2)   # เป้าเที่ยวต่อรถพร้อมใช้ 1 คันต่อวัน (หน้าเว็บแก้ได้)
READY_TREND_DAYS = 14                                                 # กราฟแนวโน้มย้อนหลังกี่วัน (นับวันที่เลือกด้วย)
_ready_parse_memo: dict = {}                                          # แท็บ → (ตารางที่อ่านมา, ผลแยกหัว/รหัส) ไม่ต้องแยกซ้ำทุกวันของกราฟ
_TH_MONTHS = {m: i for i, m in enumerate(
    ["มกราคม", "กุมภาพันธ์", "มีนาคม", "เมษายน", "พฤษภาคม", "มิถุนายน",
     "กรกฎาคม", "สิงหาคม", "กันยายน", "ตุลาคม", "พฤศจิกายน", "ธันวาคม"], 1)}
_TH_MONTHS_ABBR = {"ม.ค.": 1, "ก.พ.": 2, "มี.ค.": 3, "เม.ย.": 4, "พ.ค.": 5, "มิ.ย.": 6,
                   "ก.ค.": 7, "ส.ค.": 8, "ก.ย.": 9, "ต.ค.": 10, "พ.ย.": 11, "ธ.ค.": 12}
_THAI_RE = re.compile(r"[ก-๙]")
# คำอธิบายรหัสที่แปลว่า "ทำงานได้" — คำอื่นทั้งหมด (ซ่อม เครม ลา ขาดงาน อบรม หยุด เบรกงาน ...) = ไม่พร้อม
_READY_OK_WORDS = ("พร้อม", "วิ่งงาน", "ทำงาน", "ทำโอ", "โอที", "รองาน")


def _ready_month(text: str):
    """'สถานะรถพร้อมใช้ ประจำเดือน ตุลาคม Y2026' → (2026, 10) · ไม่ใช่หัวเดือน = None (พ.ศ. แปลงเป็น ค.ศ. ให้)"""
    t = (text or "").strip()
    if not t or "เดือน" not in t:
        return None
    mon = (next((n for name, n in _TH_MONTHS.items() if name in t), 0)
           or next((n for ab, n in _TH_MONTHS_ABBR.items() if ab in t), 0))
    m = re.search(r"(\d{4})", t)
    if not mon or not m:
        return None
    y = int(m.group(1))
    return (y - 543 if y > 2400 else y), mon


def _ready_legend(rows: list, used: set) -> dict:
    """คำอธิบายรหัสที่เขียนไว้เหนือตาราง (คู่ช่องติดกัน) → {'R': 'รถวิ่งงาน', 'H': 'พักร้อน', 'อบรม': 'อบรม', ...}

    สองแท็บเขียนไม่เหมือนกัน: ข้อมูลรถ = "รหัส | คำอธิบาย" (CM | ซ่อมทั่วไป) · ข้อมูลพขร. = "คำอธิบาย | รหัส" (ลากิจ | B)
    และรหัสเป็นภาษาไทยได้ (บ, อบรม, หยุด) จึงตัดสินว่าช่องไหนคือรหัสจาก "ค่าที่ลงอยู่ในตารางจริง" (used)
    ถ้าเดือนนี้ยังไม่มีใครใช้รหัสนั้น ถือว่าช่องที่สั้นกว่าคือรหัส
    รหัสที่ไม่มีคำอธิบาย (เช่น N, O) ไม่เก็บ — หน้าเว็บจะโชว์เป็น "ไม่ระบุ" """
    out: dict = {}
    num = lambda s: bool(re.fullmatch(r"[\d.,%\s-]*", s))
    for r in rows:
        for i in range(min(len(r), 14) - 1):
            a, b = _cell(r, i), _cell(r, i + 1)
            if not a or not b or num(a) or num(b) or "เดือน" in a + b:
                continue
            ua, ub = a.upper(), b.upper()
            if ub in used and ua not in used:
                code, desc = ub, a
            elif ua in used:
                code, desc = ua, b
            elif len(a) <= 6 and len(a) < len(b):
                code, desc = ua, b
            elif len(b) <= 6 and len(b) < len(a):
                code, desc = ub, a
            else:
                continue
            if _THAI_RE.search(desc):
                out.setdefault(code, re.sub(r"\s+", " ", desc))
    return out


def _ready_kind(desc: str) -> str:
    """คำอธิบายรหัส → 'run' วิ่งงาน · 'free' พร้อมใช้/ทำงานได้ · 'nodriver' พร้อมใช้แต่ไม่มีคนขับ · 'down' ไม่พร้อม"""
    d = (desc or "").replace(" ", "")
    if "ไม่มีคนขับ" in d:
        return "nodriver"
    if "ไม่พร้อม" in d:
        return "down"
    if "วิ่งงาน" in d:
        return "run"
    return "free" if any(w in d for w in _READY_OK_WORDS) else "down"


def _ready_grid(rows: list, need: list) -> tuple:
    """ชีตสถานะรายวัน → (แถวหัวตาราง, {ชื่อหัว: คอลัมน์}, {วันที่ iso: คอลัมน์}) · ไม่เจอหัวตาราง = (None, {}, {})

    เซลล์หัวเดือนผสานกันไว้ Google คืนค่าเฉพาะช่องซ้ายสุด จึงถือว่าหัวเดือนคุมคอลัมน์ไปทางขวา
    จนกว่าจะเจอหัวเดือนถัดไป (เดือนของคอลัมน์ไหน = หัวเดือนซ้ายสุดที่อยู่ไม่เกินคอลัมน์นั้น)"""
    h, ix = _hdr_find(rows, need, limit=40)
    if h is None:
        return None, {}, {}
    banners = sorted((i, mo) for r in rows[max(0, h - 4):h]
                     for i, c in enumerate(r) if (mo := _ready_month(c)))
    hdr, days, last, done = rows[h], {}, {}, set()
    for i in range(len(hdr)):
        m = re.match(r"^(\d{1,2})\b", _cell(hdr, i))
        b = next((b for b in reversed(banners) if b[0] <= i), None) if m else None
        if not b or b[0] in done:
            continue
        day = int(m.group(1))
        if day <= last.get(b[0], 0):  # วันวนกลับไป 01 แต่ไม่มีหัวเดือนใหม่ = บล็อกเดือนถัดไปที่อ่านหัวไม่ออก ไม่เดาเดือนให้
            done.add(b[0])
            continue
        last[b[0]] = day
        try:
            days.setdefault(datetime(b[1][0], b[1][1], day).strftime("%Y-%m-%d"), i)
        except ValueError:            # เช่น 31 ในเดือนที่มี 30 วัน — ชีตเว้นช่องไว้
            continue
    return h, ix, days


def _ready_sheet(tab: str, need: list, date_iso: str, first_row: int = 0) -> dict:
    """อ่านแท็บสถานะรายวันหนึ่งแท็บ → {rows: [{key, code, cells}], legend, head, ix, has_day, note}
    first_row = แถวแรกของข้อมูลตามเลขแถวในชีต (เช่น 20) — แถวเหนือขึ้นไปไม่นับ แม้อยู่ใต้หัวตาราง"""
    sid = CARS_SHEET_ID or PLAN_PAGE_ID
    try:
        grid = _fetch_sheet(sid, tab)
    except Exception as e:
        return {"rows": [], "legend": {}, "head": [], "ix": {}, "has_day": False,
                "note": f"อ่านแท็บ “{tab}” ไม่ได้ — {type(e).__name__} (ต้องแชร์ชีตให้บัญชีของเว็บแบบผู้ดู)"}
    memo = _ready_parse_memo.get(tab)
    if memo and memo[0] is grid and memo[2] == first_row:   # ตารางเดิมจากแคช → ใช้ผลแยกหัว/รหัสเดิม
        h, ix, days, legend = memo[1]
    else:
        h, ix, days = _ready_grid(grid, need)
        legend = {}
        if h is not None:
            day_cols = set(days.values())
            start = max(h + 1, first_row - 1)
            used = {_cell(r, c).upper() for r in grid[start:] for c in day_cols if _cell(r, c)}
            legend = _ready_legend(grid[:h], used)
        _ready_parse_memo[tab] = (grid, (h, ix, days, legend), first_row)
    if h is None:
        return {"rows": [], "legend": {}, "head": [], "ix": {}, "has_day": False,
                "note": f"แท็บ “{tab}” ไม่พบหัวตาราง ({' + '.join(need)}) จึงยังสรุปจากแท็บนี้ไม่ได้"}
    col = days.get(date_iso)
    out = []
    for r in grid[max(h + 1, first_row - 1):]:
        key = _cell(r, ix[need[0]])
        if key:
            out.append({"key": key, "cells": r, "code": (_cell(r, col).upper() if col is not None else "")})
    note = "" if col is not None else f"แท็บ “{tab}” ยังไม่มีคอลัมน์ของวันที่นี้ (ชีตลงสถานะถึงเดือนล่าสุดเท่านั้น)"
    return {"rows": out, "legend": legend, "head": _hdr_cells(grid[h]), "ix": ix, "has_day": col is not None, "note": note}


def _ready_plan(rows: list, date_iso: str) -> tuple:
    """แผนงานของวันนั้น → ({คีย์รถ: {jobs: เซ็ตเลขเที่ยว, drops: จำนวนแถว}}, {ชื่อ พขร.: เซ็ตเลขเที่ยว}, จำนวนงานที่ยกเลิก)

    1 แถว = 1 drop · 1 เที่ยว = เลข JOB เดียวกัน (คอลัมน์ B = วันที่+รถ+เที่ยว เช่น 46266PTL.451เที่ยว 1)
    นับแบบเดียวกับหน้ารายงาน On Time · งานที่ยกเลิก/โหลดเก็บไม่นับ
    แถวที่ไม่มีเลข JOB ใช้ลำดับเที่ยว (D) → รถ+เที่ยววิ่ง (E) → ถ้าไม่มีเลยนับ 1 เที่ยวต่อแถว"""
    cars: dict = {}
    people: dict = {}
    cancelled = 0
    for i, r in enumerate(rows):
        if _parse_date(_cell(r, PLAN_DATE)) != date_iso:
            continue
        if any(k in (_cell(r, PLAN_STATUS) + " " + _cell(r, PLAN_DEST)).lower() for k in CANCEL_KEYWORDS):
            cancelled += 1
            continue
        key = _car_key(_cell(r, PLAN_CARNO))
        seq = _cell(r, PLAN_TRIP_SEQ)
        job = _cell(r, 1) or (f"D{seq}" if seq else "") or (f"{key}|{_cell(r, PLAN_TRIP)}" if key and _cell(r, PLAN_TRIP) else f"row{i}")
        if key:
            e = cars.setdefault(key, {"jobs": set(), "drops": 0})
            e["jobs"].add(job)
            e["drops"] += 1
        for c in (PLAN_DRIVER, PLAN_DRIVER2):
            if (nm := _cell(r, c)) and nm not in _NO_PERSON:
                people.setdefault(nm, set()).add(job)
    return cars, people, cancelled


def _ready_col(head: list, *names: str):
    """หาคอลัมน์จากชื่อหัวตาราง — ลองตามลำดับที่ให้มา แล้วค่อยหาแบบ "มีคำนี้อยู่ในหัว" """
    for n in names:
        if n in head:
            return head.index(n)
    return next((i for i, c in enumerate(head) if any(n in c for n in names)), None)


def _ready_count(items: list, key: str) -> list:
    """[{...}] → [{'name': ค่า, 'n': จำนวน}] เรียงมาก→น้อย (ค่าว่างรวมเป็น "ไม่ระบุ")"""
    tally: dict = {}
    for it in items:
        tally[it.get(key) or "ไม่ระบุ"] = tally.get(it.get(key) or "ไม่ระบุ", 0) + 1
    return sorted(({"name": k, "n": v} for k, v in tally.items()), key=lambda d: (-d["n"], d["name"]))


def build_ready_report(date_iso: str, plan_rows: list, target: float) -> dict:
    """สรุปรถ/คนพร้อมใช้งานของวันที่ระบุ — รวมชีตสถานะรายวันเข้ากับงานจริงในชีตแผนงาน"""
    plan, driver_jobs, cancelled = _ready_plan(plan_rows, date_iso)
    trips = {k: len(v["jobs"]) for k, v in plan.items()}          # เบอร์รถ → จำนวนเที่ยว (เลข JOB ไม่ซ้ำ)
    drops = {k: v["drops"] for k, v in plan.items()}              # เบอร์รถ → จำนวน drop (แถว)
    notes: list = []

    # ── รถ ──
    cs = _ready_sheet(READY_CAR_TAB, ["เบอร์รถ", "ทะเบียนรถ"], date_iso, READY_CAR_FIRST_ROW)
    if cs["note"]:
        notes.append(cs["note"])
    legend = dict(cs["legend"])
    head = cs["head"]
    c_area = _ready_col(head, "ประจำพื้นที่", "พื้นที่")
    c_type = _ready_col(head, "ประเภทรถ", "น้ำหนัก")
    c_plate = cs["ix"].get("ทะเบียนรถ")
    cars, seen, mismatch = [], set(), 0
    for r in cs["rows"]:
        car = r["key"]
        if not _CAR_RE.match(car):
            continue
        key = _car_key(car)
        if key in seen:                       # ชีตมีรถคันเดียวกันหลายแถว (เช่น ตารางเรียงข้างกัน) นับครั้งเดียว
            continue
        seen.add(key)
        code = r["code"]
        desc = legend.get(code, "")
        kind = _ready_kind(desc) if code else "free"
        n = trips.get(key, 0)
        why = (desc or "ไม่ระบุ") if kind == "down" else ""
        if kind != "down":                    # พร้อมใช้ → วิ่งงานหรือไม่ ดูจากแผนงาน ไม่ดูรหัส R ในชีต
            if n:
                kind = "run"
            elif kind == "run":               # ชีตลง R ไว้ แต่วันนั้นไม่มีงานในแผน — บอกให้รู้ว่าไม่ตรงกัน
                kind, mismatch, why = "free", mismatch + 1, "ชีตลงวิ่งงาน แต่ไม่มีงานในแผน"
            elif kind == "nodriver":
                why = desc
        area = _cell(r["cells"], c_area) if c_area is not None else ""
        cars.append({"car": car, "key": key, "area": _area_of(area) or area,
                     "vtype": _cell(r["cells"], c_type) if c_type is not None else "",
                     "plate": _cell(r["cells"], c_plate) if c_plate is not None else "",
                     "code": code, "why": why, "kind": kind, "trips": n, "drops": drops.get(key, 0)})
    if mismatch:
        notes.append(f"มี {mismatch} คันที่ชีตลงรหัสวิ่งงานไว้ แต่วันนั้นไม่มีงานในชีตแผนงาน — นับเป็นว่างงาน")
    busy_down = [c["car"] for c in cars if c["kind"] == "down" and c["trips"]]
    if busy_down:
        notes.append(f"มี {len(busy_down)} คันที่ชีตลงว่าไม่พร้อมใช้ แต่มีงานในแผนงานวันนั้น — นับเป็นไม่พร้อมใช้ ตรวจชีตอีกครั้ง: "
                     + ", ".join(busy_down[:8]))
    ghost = sorted(set(trips) - seen)
    if ghost:
        notes.append(f"มี {len(ghost)} คันที่มีงานในแผนงาน แต่ไม่มีในแท็บ “{READY_CAR_TAB}”: " + ", ".join(ghost[:8]))

    by_kind = lambda k: [c for c in cars if c["kind"] == k]
    run, free, nodrv, down = by_kind("run"), by_kind("free"), by_kind("nodriver"), by_kind("down")
    ready = run + free + nodrv
    total_trips = len({j for v in plan.values() for j in v["jobs"]})
    total_drops = sum(drops.values())
    # เป้า = เที่ยวต่อรถพร้อมใช้ 1 คัน → ทั้งวันควรได้กี่เที่ยว และตอนนี้ขาดอีกเท่าไร
    goal = round(target * len(ready)) if target > 0 else 0

    # ── คน ──
    ds = _ready_sheet(READY_DRIVER_TAB, ["ชื่อ-สกุล"], date_iso, READY_DRIVER_FIRST_ROW)
    if ds["note"]:
        notes.append(ds["note"])
    d_legend = ds["legend"]
    d_left = _ready_col(ds["head"], "วันที่พ้นสภาพ", "พ้นสภาพ")
    d_stat = next((i for i, c in enumerate(ds["head"]) if c == "สถานะ"), None)   # คอลัมน์สถานะการจ้าง (พนักงาน / ลาออก ฯลฯ)
    if ds["head"] and d_stat is None:
        notes.append(f"แท็บ “{READY_DRIVER_TAB}” ไม่พบคอลัมน์ “สถานะ” — นับทุกคนที่ยังไม่มีวันพ้นสภาพแทน")
    people, dseen = [], set()
    for r in ds["rows"]:
        name = r["key"]
        if name in _NO_PERSON or name in dseen:
            continue
        if d_stat is not None:                                     # นับเฉพาะสถานะ "พนักงาน" ตามยอดรวมในชีต
            if _cell(r["cells"], d_stat) != READY_DRIVER_STATUS:
                continue
        elif d_left is not None and _cell(r["cells"], d_left):    # ไม่มีคอลัมน์สถานะ: มีวันพ้นสภาพ = ลาออกแล้ว ไม่นับ
            continue
        dseen.add(name)
        code = r["code"]
        desc = d_legend.get(code, "")
        kind = _ready_kind(desc) if code else "free"
        n = len(driver_jobs.get(name, ()))
        why = (desc or "ไม่ระบุ") if kind == "down" else ""
        if kind != "down":
            kind = "run" if n else "free"
        people.append({"name": name, "code": code, "why": why, "kind": kind, "trips": n})
    d_run = [p for p in people if p["kind"] == "run"]
    d_free = [p for p in people if p["kind"] == "free"]
    d_down = [p for p in people if p["kind"] == "down"]
    busy_off = [p["name"] for p in d_down if p["trips"]]
    if busy_off:
        notes.append(f"มี {len(busy_off)} คนที่ชีตลงว่าลา/หยุด แต่มีชื่อในแผนงานวันนั้น: " + ", ".join(busy_off[:6]))
    unknown = sorted(set(driver_jobs) - dseen)
    if unknown:
        notes.append(f"มี {len(unknown)} คนที่รับงานในแผนงาน แต่ไม่มีในแท็บ “{READY_DRIVER_TAB}”: " + ", ".join(unknown[:6]))

    area_rows = sorted({c["area"] or "ไม่ระบุ" for c in cars})
    return {
        "date": date_iso,
        "target": target,
        "legend": legend,
        "driver_legend": d_legend,
        "notes": notes,
        "cars": {"total": len(cars), "ready": len(ready), "run": len(run), "free": len(free),
                 "nodriver": len(nodrv), "down": len(down),
                 "pct_ready": round(len(ready) * 100 / len(cars), 1) if cars else None,
                 "pct_used": round(len(run) * 100 / len(ready), 1) if ready else None,
                 "down_by": _ready_count(down, "why"), "free_by": _ready_count(free + nodrv, "area")},
        "trips": {"total": total_trips, "drops": total_drops, "cancelled": cancelled,
                  "per_ready": round(total_trips / len(ready), 2) if ready else None,
                  "per_run": round(total_trips / len(run), 2) if run else None,
                  "goal": goal, "gap": max(0, goal - total_trips) if goal else 0},
        "people": {"total": len(people), "run": len(d_run), "free": len(d_free), "down": len(d_down),
                   "down_by": _ready_count(d_down, "why")},
        "by_area": [{"area": a,
                     "total": sum(1 for c in cars if (c["area"] or "ไม่ระบุ") == a),
                     "run": sum(1 for c in run if (c["area"] or "ไม่ระบุ") == a),
                     "free": sum(1 for c in free + nodrv if (c["area"] or "ไม่ระบุ") == a),
                     "down": sum(1 for c in down if (c["area"] or "ไม่ระบุ") == a),
                     "trips": sum(c["trips"] for c in cars if (c["area"] or "ไม่ระบุ") == a)} for a in area_rows],
        "by_type": [{"vtype": t,
                     "total": sum(1 for c in cars if (c["vtype"] or "ไม่ระบุ") == t),
                     "run": sum(1 for c in run if (c["vtype"] or "ไม่ระบุ") == t),
                     "free": sum(1 for c in free + nodrv if (c["vtype"] or "ไม่ระบุ") == t),
                     "down": sum(1 for c in down if (c["vtype"] or "ไม่ระบุ") == t),
                     "trips": sum(c["trips"] for c in cars if (c["vtype"] or "ไม่ระบุ") == t)}
                    for t in sorted({c["vtype"] or "ไม่ระบุ" for c in cars})],
        "rows": sorted(cars, key=lambda c: ({"down": 0, "nodriver": 1, "free": 2, "run": 3}[c["kind"]], -c["trips"], c["car"])),
        "people_rows": sorted(people, key=lambda p: ({"down": 0, "free": 1, "run": 2}[p["kind"]], -p["trips"], p["name"])),
    }


def _ready_merge(reps: list) -> dict:
    """รวมรายงานหลายวันเป็นหนึ่ง: รถ/คน = เฉลี่ยต่อวัน · เที่ยว/drop/เป้า = รวมทั้งช่วง · สาเหตุไม่พร้อม = นับเป็น คัน·วัน / คน·วัน
    รายคัน/รายคน: เที่ยวรวม + จำนวนวันที่วิ่ง/ว่าง/ไม่พร้อม · สถานะที่โชว์ = สถานะที่เป็นบ่อยสุดในช่วง"""
    n = len(reps)
    last = reps[-1]
    if n == 1:
        return dict(last, days=1)
    avg = lambda xs: round(sum(xs) / n, 1)

    def summed(lists):
        t: dict = {}
        for l in lists:
            for d in l:
                t[d["name"]] = t.get(d["name"], 0) + d["n"]
        return sorted(({"name": k, "n": v} for k, v in t.items()), key=lambda d: (-d["n"], d["name"]))

    cars = {k: avg([r["cars"][k] for r in reps]) for k in ("ready", "run", "free", "nodriver", "down")}
    s_tot = sum(r["cars"]["total"] for r in reps)
    s_ready = sum(r["cars"]["ready"] for r in reps)
    s_run = sum(r["cars"]["run"] for r in reps)
    cars.update(total=max(r["cars"]["total"] for r in reps),
                pct_ready=round(s_ready * 100 / s_tot, 1) if s_tot else None,
                pct_used=round(s_run * 100 / s_ready, 1) if s_ready else None,
                down_by=summed([r["cars"]["down_by"] for r in reps]), free_by=[])
    t_total = sum(r["trips"]["total"] for r in reps)
    goal = sum(r["trips"]["goal"] for r in reps)
    trips = {"total": t_total, "drops": sum(r["trips"]["drops"] for r in reps),
             "cancelled": sum(r["trips"]["cancelled"] for r in reps),
             "per_ready": round(t_total / s_ready, 2) if s_ready else None,
             "per_run": round(t_total / s_run, 2) if s_run else None,
             "goal": goal, "gap": max(0, goal - t_total) if goal else 0}
    people = {k: avg([r["people"][k] for r in reps]) for k in ("run", "free", "down")}
    people.update(total=max(r["people"]["total"] for r in reps), down_by=summed([r["people"]["down_by"] for r in reps]))

    def groups(key, name):
        out = {}
        for r in reps:
            for g in r[key]:
                e = out.setdefault(g[name], {name: g[name], "total": 0, "run": 0, "free": 0, "down": 0, "trips": 0})
                e["total"] = max(e["total"], g["total"])
                for k in ("run", "free", "down"):
                    e[k] += g[k] / n
                e["trips"] += g["trips"]
        for e in out.values():
            for k in ("run", "free", "down"):
                e[k] = round(e[k], 1)
        return sorted(out.values(), key=lambda e: e[name])

    def per_entity(key, ident, extra):
        out: dict = {}
        for r in reps:
            for x in r[key]:
                e = out.setdefault(x[ident], dict({f: x.get(f, "") for f in extra}, **{ident: x[ident], "trips": 0, "drops": 0,
                                                                                       "d_run": 0, "d_free": 0, "d_down": 0, "whys": {}}))
                e["trips"] += x["trips"]
                e["drops"] += x.get("drops", 0)
                k = {"run": "d_run", "down": "d_down"}.get(x["kind"], "d_free")
                e[k] += 1
                if x["kind"] == "down" and x["why"]:
                    e["whys"][x["why"]] = e["whys"].get(x["why"], 0) + 1
        rows = []
        for e in out.values():
            best = max((("run", e["d_run"]), ("free", e["d_free"]), ("down", e["d_down"])), key=lambda kv: kv[1])[0]
            e["kind"] = best
            e["why"] = max(e["whys"], key=e["whys"].get) if e["whys"] else ""
            e["code"] = ""
            del e["whys"]
            rows.append(e)
        return sorted(rows, key=lambda e: ({"down": 0, "free": 1, "run": 2}[e["kind"]], -e["d_down"], -e["trips"], str(e[ident])))

    # หมายเหตุ: แสดงเฉพาะของวันสุดท้ายในช่วง (ทุกวันมีเรื่องคล้ายกัน ซ้อนกันจนอ่านไม่ไหว) — อยากดูวันอื่นเลือกทีละวัน
    notes = list(last["notes"])
    return {"date": last["date"], "target": last["target"], "legend": last["legend"], "driver_legend": last["driver_legend"],
            "notes": notes, "notes_date": last["date"], "cars": cars, "trips": trips, "people": people, "days": n,
            "by_area": groups("by_area", "area"), "by_type": groups("by_type", "vtype"),
            "rows": per_entity("rows", "car", ("key", "area", "vtype", "plate")),
            "people_rows": per_entity("people_rows", "name", ())}


@app.get("/api/report/ready", include_in_schema=False)
def report_ready(date_from: str = Query(None, alias="from"), date_to: str = Query(None, alias="to"),
                 date_str: str = Query(None, alias="date"), target: float = Query(None), fresh: int = Query(0)):
    """สรุปรถ/คนพร้อมใช้งานของช่วงวันที่ (ค่าเริ่มต้น = วันนี้) — อ่านชีตอย่างเดียว
    วันเดียว = สถานะของวันนั้น · หลายวัน = รถ/คนเฉลี่ยต่อวัน + เที่ยวรวมทั้งช่วง"""
    d_from = _parse_date(date_from or date_str or "") or _today_thai()
    d_to = _parse_date(date_to or "") or d_from
    if d_to < d_from:
        d_from, d_to = d_to, d_from
    f0, t0 = datetime.strptime(d_from, "%Y-%m-%d"), datetime.strptime(d_to, "%Y-%m-%d")
    if (t0 - f0).days > 61:
        raise HTTPException(400, "เลือกช่วงวันที่ได้ไม่เกิน 62 วัน")
    if fresh:
        cars_id = CARS_SHEET_ID or PLAN_PAGE_ID
        _fresh_read([(SOURCE_ID, PLAN_TAB), (cars_id, READY_CAR_TAB), (cars_id, READY_DRIVER_TAB)])
    try:
        plan_rows = _fetch_sheet(SOURCE_ID, PLAN_TAB)
    except Exception as e:
        raise HTTPException(502, f"อ่านชีตแผนงานไม่ได้ — {type(e).__name__}")
    tg = READY_TARGET if target is None else max(0.0, min(float(target), 99.0))
    by_date: dict = {}                        # แยกแถวแผนงานตามวันครั้งเดียว ไม่ต้องไล่ทั้งชีตซ้ำทุกวัน
    for r in plan_rows:
        by_date.setdefault(_parse_date(_cell(r, PLAN_DATE)), []).append(r)
    cache: dict = {}

    def day_rep(d):
        if d not in cache:
            cache[d] = build_ready_report(d, by_date.get(d, []), tg)
        return cache[d]

    span = [(f0 + timedelta(days=k)).strftime("%Y-%m-%d") for k in range((t0 - f0).days + 1)]
    rep = _ready_merge([day_rep(d) for d in span])
    rep["from"], rep["to"] = d_from, d_to
    # กราฟรายวัน: ช่วงที่เลือก (ถ้า 7 วันขึ้นไป) หรือ 14 วันล่าสุดจนถึงวันสุดท้ายที่เลือก
    tdays = span if len(span) >= 7 else [(t0 - timedelta(days=k)).strftime("%Y-%m-%d") for k in range(READY_TREND_DAYS - 1, -1, -1)]
    trend = []
    for d in tdays:
        x = day_rep(d)
        c, t = x["cars"], x["trips"]
        trend.append({"date": d, "run": c["run"], "free": c["free"], "nodriver": c["nodriver"], "down": c["down"],
                      "trips": t["total"], "goal": t["goal"], "p_down": x["people"]["down"]})
    rep["trend"] = trend
    return rep


@app.get("/ready", response_class=HTMLResponse, include_in_schema=False)
def ready_page(request: Request):
    return _nav(READY_HTML, request)


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


PW_HASH_ITER = 200_000


def _pw_hash(pw: str) -> str:
    """รหัสผ่าน → "pbkdf2_sha256$รอบ$salt$hash" (เก็บในชีตแทนตัวรหัส — เปิดชีตก็ไม่เห็นรหัสจริง)"""
    salt = base64.b64encode(os.urandom(12)).decode()
    dk = hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), salt.encode(), PW_HASH_ITER)
    return f"pbkdf2_sha256${PW_HASH_ITER}${salt}${base64.b64encode(dk).decode()}"


def _pw_check(pw: str, stored: str) -> bool:
    """ตรวจรหัสกับค่าที่เก็บในชีต — รองรับทั้งแบบ hash (ตั้งจากเว็บ) และแบบตัวอักษรตรงๆ (พิมพ์ในชีตเอง)"""
    if stored.startswith("pbkdf2_sha256$"):
        try:
            _, it, salt, h = stored.split("$", 3)
            dk = hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), salt.encode(), int(it))
            return hmac.compare_digest(base64.b64encode(dk), h.encode())
        except (ValueError, TypeError):
            return False
    return _pw_equal(pw, stored)


@app.post("/api/login", include_in_schema=False)
def do_login(request: Request, password: str = Form(""), username: str = Form("")):
    pw = _app_password()
    ip = _client_ip(request)
    wait = _login_gate(ip)
    if wait:
        return RedirectResponse("/login?error=2", status_code=303)
    uname = (username or "").strip().lower()
    u = _users().get(uname) if (pw and uname) else None
    if u and _pw_check(password, u["pw"]):
        role, dest = uname, _home_for(u["perms"])    # ผู้ใช้จากชีต → หน้าแรกที่มีสิทธิ์
        _users_touch(uname)                          # บันทึก "เข้าใช้ล่าสุด" ลงแท็บ User
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


# ─── จัดการผู้ใช้ (หน้า /users — เฉพาะผู้ดูแล) · เขียนลงแท็บ User เดิม ─────────────────────────────
USER_RE    = re.compile(r"^[A-Za-z0-9ก-๙._-]{2,32}$")
USERS_HEAD = ["ชื่อผู้ใช้", "รหัสผ่าน", "เช็กรถ", "แผนงาน", "รายงาน", "รถ/คนพร้อมใช้", "ผู้ดูแล", "ใช้งาน", "เข้าใช้ล่าสุด"]
PW_MIN     = 6
_MARK      = "✓"


def _users_ws():
    """แท็บ User (ไม่มี = สร้างพร้อมหัวตาราง)"""
    sh = gspread.authorize(_build_creds()).open_by_key(_users_sheet_id())
    try:
        return sh.worksheet(USERS_TAB)
    except gspread.WorksheetNotFound:
        ws = sh.add_worksheet(USERS_TAB, rows=200, cols=len(USERS_HEAD))
        ws.update("A1", [USERS_HEAD], value_input_option="RAW")
        return ws


def _users_sheet(ws) -> tuple:
    """อ่านแท็บ User → (แถว, แถวหัว, คอลัมน์) และเติมคอลัมน์ที่ยังไม่มีต่อท้ายหัวตาราง
    (หน้าใหม่ในทะเบียน PAGES / ผู้ดูแล / ใช้งาน / เข้าใช้ล่าสุด) พร้อมค่าที่ทุกคนได้สิทธิ์เท่าเดิมตาม inherit"""
    rows = _with_retry(ws.get_all_values)
    hdr, cols = _users_layout(rows)
    if hdr is None:
        _with_retry(lambda: ws.update("A1", [USERS_HEAD], value_input_option="RAW"))
        rows = [USERS_HEAD]
        hdr, cols = _users_layout(rows)
    keys = [k for k in PAGE_PERMS + ("admin", "active", "last") if cols[k] is None]
    if not keys:
        return rows, hdr, cols
    head = list(rows[hdr])
    old = dict(cols)
    names = dict(PERM_HEAD, active="ใช้งาน", last="เข้าใช้ล่าสุด")
    for k in keys:
        cols[k] = len(head)
        head.append(names[k])
    if ws.col_count < len(head):
        _with_retry(lambda: ws.add_cols(len(head) - ws.col_count))
    body = []
    for r in rows[hdr + 1:]:
        cell = lambda n: r[n].strip() if n is not None and n < len(r) else ""
        on = lambda n: cell(n).lower() in _TRUE_MARKS
        perms = _row_perms(cell, on, old)
        val = {k: (_MARK if k in perms else "") for k in PERMS_ALL}
        val.update(active=_MARK if cell(old["user"]) else "", last="")
        body.append([val[k] for k in keys])
    a = gspread.utils.rowcol_to_a1(hdr + 1, cols[keys[0]] + 1)
    b = gspread.utils.rowcol_to_a1(hdr + 1 + len(body), cols[keys[-1]] + 1)
    _with_retry(lambda: ws.update(f"{a}:{b}", [[names[k] for k in keys]] + body, value_input_option="RAW"))
    _users_forget()                                  # คอลัมน์ใหม่มีผลกับสิทธิ์ทันที ไม่ต้องรอแคช 1 นาที
    rows = _with_retry(ws.get_all_values)
    return rows, hdr, cols


def _users_find(rows, hdr, cols, user: str):
    """เลขแถวในชีต (เริ่ม 1) ของผู้ใช้ — ไม่เจอ = None"""
    u = user.strip().lower()
    for i in range(hdr + 1, len(rows)):
        r = rows[i]
        if cols["user"] < len(r) and r[cols["user"]].strip().lower() == u:
            return i + 1
    return None


def _users_write(ws, row_no: int, cols: dict, values: dict) -> None:
    """เขียนเฉพาะช่องที่ให้มา {ช่อง: ค่า} ลงแถวนั้น (คำสั่งเดียว)"""
    data = [{"range": gspread.utils.rowcol_to_a1(row_no, cols[k] + 1), "values": [[v]]} for k, v in values.items()]
    _with_retry(lambda: ws.batch_update(data, value_input_option="RAW"))


def _users_forget() -> None:
    _users_cache.update(ts=0.0, data=None)          # อ่านชีตผู้ใช้ใหม่ทันที สิทธิ์ที่เพิ่งแก้มีผลเลย


def _users_touch(user: str) -> None:
    """บันทึก "เข้าใช้ล่าสุด" ของผู้ใช้ที่ล็อกอินสำเร็จ — พลาดก็ไม่เป็นไร ไม่ให้ล็อกอินล้มเพราะเรื่องนี้"""
    try:
        ws = _users_ws()
        rows, hdr, cols = _users_sheet(ws)
        row_no = _users_find(rows, hdr, cols, user)
        if row_no:
            _users_write(ws, row_no, cols, {"last": _thai_now().strftime("%d/%m/%Y %H:%M")})
    except Exception:
        pass


def _me(request: Request) -> str:
    """ชื่อผู้ใช้ที่ล็อกอินอยู่ ("" = รหัสกลาง)"""
    return _token_user(request.cookies.get(COOKIE_NAME, "")) or ""


class UserIn(BaseModel):
    user: str
    password: str = ""
    perms: Optional[list[str]] = None
    active: Optional[bool] = None


def _clean_perms(perms) -> set:
    p = {x for x in (perms or []) if x in PERMS_ALL}
    if not p & set(PAGE_PERMS):
        raise HTTPException(400, "ต้องติ๊กอย่างน้อย 1 หน้าที่ให้เข้าได้")
    return p


@app.get("/api/users", include_in_schema=False)
def users_list(request: Request):
    """รายชื่อผู้ใช้ทั้งหมด (ไม่ส่งรหัสผ่านออกไป)"""
    try:
        rows, hdr, cols = _users_sheet(_users_ws())
    except Exception as e:
        raise HTTPException(502, f"เปิดแท็บ “{USERS_TAB}” ไม่ได้ — {type(e).__name__} (ต้องแชร์ไฟล์ให้บัญชีของเว็บเป็นผู้แก้ไข)")
    out = []
    for r in rows[hdr + 1:]:
        cell = lambda n: r[n].strip() if n is not None and n < len(r) else ""
        on = lambda n: cell(n).lower() in _TRUE_MARKS
        user = cell(cols["user"])
        if not user:
            continue
        out.append({"user": user, "perms": sorted(_row_perms(cell, on, cols)), "active": on(cols["active"]),
                    "last": cell(cols["last"]), "has_pw": bool(cell(cols["pw"])),
                    "hashed": cell(cols["pw"]).startswith("pbkdf2_sha256$")})
    pages = [{"key": p["key"], "label": p["menu"].split(" ", 1)[-1]} for p in PAGES] + [{"key": "admin", "label": "ผู้ดูแล"}]
    return {"users": out, "me": _me(request), "pages": pages, "sheet": USERS_TAB}


@app.post("/api/users", include_in_schema=False)
def users_add(p: UserIn):
    user = p.user.strip()
    if not USER_RE.match(user):
        raise HTTPException(400, "ชื่อผู้ใช้ 2–32 ตัว ใช้ได้เฉพาะ ก-ฮ a-z 0-9 . _ - (ไม่มีช่องว่าง)")
    if len(p.password) < PW_MIN:
        raise HTTPException(400, f"รหัสผ่านอย่างน้อย {PW_MIN} ตัว")
    perms = _clean_perms(p.perms)
    ws = _users_ws()
    rows, hdr, cols = _users_sheet(ws)
    if _users_find(rows, hdr, cols, user):
        raise HTTPException(409, f"มีผู้ใช้ “{user}” อยู่แล้ว")
    row_no = len(rows) + 1
    if ws.row_count < row_no:
        _with_retry(lambda: ws.add_rows(20))
    vals = {"user": user, "pw": _pw_hash(p.password), "active": _MARK if p.active is not False else "", "last": ""}
    vals.update({k: (_MARK if k in perms else "") for k in PERMS_ALL if cols.get(k) is not None})
    _users_write(ws, row_no, cols, vals)
    _users_forget()
    return {"ok": True}


@app.post("/api/users/update", include_in_schema=False)
def users_update(p: UserIn, request: Request):
    me = _me(request).lower()
    ws = _users_ws()
    rows, hdr, cols = _users_sheet(ws)
    row_no = _users_find(rows, hdr, cols, p.user)
    if not row_no:
        raise HTTPException(404, f"ไม่พบผู้ใช้ “{p.user}”")
    vals: dict = {}
    if p.perms is not None:
        perms = _clean_perms(p.perms)
        if me and p.user.strip().lower() == me and "admin" not in perms:
            raise HTTPException(400, "เอาสิทธิ์ผู้ดูแลของตัวเองออกไม่ได้ (กันล็อกตัวเองออก) — ให้ผู้ดูแลคนอื่นทำ")
        vals.update({k: (_MARK if k in perms else "") for k in PERMS_ALL if cols.get(k) is not None})
    if p.active is not None:
        if me and p.user.strip().lower() == me and not p.active:
            raise HTTPException(400, "ปิดบัญชีของตัวเองไม่ได้")
        vals["active"] = _MARK if p.active else ""
    if p.password:
        if len(p.password) < PW_MIN:
            raise HTTPException(400, f"รหัสผ่านอย่างน้อย {PW_MIN} ตัว")
        vals["pw"] = _pw_hash(p.password)
    if not vals:
        raise HTTPException(400, "ไม่มีอะไรให้แก้")
    _users_write(ws, row_no, cols, vals)
    _users_forget()
    return {"ok": True}


@app.post("/api/users/delete", include_in_schema=False)
def users_delete(p: UserIn, request: Request):
    me = _me(request).lower()
    if me and p.user.strip().lower() == me:
        raise HTTPException(400, "ลบบัญชีของตัวเองไม่ได้")
    ws = _users_ws()
    rows, hdr, cols = _users_sheet(ws)
    row_no = _users_find(rows, hdr, cols, p.user)
    if not row_no:
        raise HTTPException(404, f"ไม่พบผู้ใช้ “{p.user}”")
    _with_retry(lambda: ws.delete_rows(row_no))
    _users_forget()
    return {"ok": True}


@app.get("/users", response_class=HTMLResponse, include_in_schema=False)
def users_page(request: Request):
    return _nav(USERS_HTML, request)


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


USERS_HTML = """<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>จัดการผู้ใช้ — Gasbulk Track PTGLG</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet" crossorigin="anonymous">
<style>
  :root{color-scheme:light;
    --plane:#f4f5f7;--card:#ffffff;--line:#e6e8ec;--hair:#eceae4;--track:#eef0f3;
    --ink:#0b0b0b;--ink2:#3f3e3b;--mut:#6b6964;--hover:#f3f6fb;--acc:#2563eb;
    --good:#0ca30c;--crit:#d03b3b;--crit-ink:#b42318;--crit-bg:#fdecec;--good-bg:#e9f7e9;--good-ink:#006300;
    --shadow:0 1px 2px rgba(16,24,40,.05),0 1px 3px rgba(16,24,40,.07)}
  @media (prefers-color-scheme:dark){
    :root:where(:not([data-theme="light"])){color-scheme:dark;
      --plane:#0d0d0d;--card:#161616;--line:#2a2a28;--hair:#2c2c2a;--track:#242422;
      --ink:#f0efec;--ink2:#d6d5cc;--mut:#a9a7a0;--hover:#1f2733;--acc:#3b82f6;
      --crit-ink:#ff8a80;--crit-bg:#2d1414;--good-bg:#10260f;--good-ink:#3fcf3f;--shadow:none}}
  :root[data-theme="dark"]{color-scheme:dark;
      --plane:#0d0d0d;--card:#161616;--line:#2a2a28;--hair:#2c2c2a;--track:#242422;
      --ink:#f0efec;--ink2:#d6d5cc;--mut:#a9a7a0;--hover:#1f2733;--acc:#3b82f6;
      --crit-ink:#ff8a80;--crit-bg:#2d1414;--good-bg:#10260f;--good-ink:#3fcf3f;--shadow:none}
  *{box-sizing:border-box}
  body{margin:0;background:var(--plane);color:var(--ink);font-family:'Noto Sans Thai',system-ui,-apple-system,"Segoe UI",sans-serif;font-size:15px;padding-left:148px}
  .side{position:fixed;left:0;top:0;bottom:0;width:148px;background:var(--card);border-right:1px solid var(--line);padding:14px 10px;display:flex;flex-direction:column;gap:6px;z-index:20}
  .side .menu{display:flex;align-items:center;gap:9px;text-decoration:none;font-weight:700;font-size:16px;color:var(--ink);padding:11px 12px;border-radius:10px}
  .side .menu:hover{background:var(--hover)}
  .side .menu.on{background:#2563eb;color:#fff}
  .side .menu.out{margin-top:auto;color:var(--mut);font-size:14.5px;white-space:nowrap}
  header{background:var(--card);border-bottom:1px solid var(--line);padding:14px 22px}
  header h1{font-size:21px;margin:0;font-weight:700}
  header p{margin:2px 0 0;font-size:13.5px;color:var(--mut)}
  main{padding:18px 22px 40px;display:grid;gap:12px}
  .card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px 18px;box-shadow:var(--shadow);min-width:0}
  .card h3{margin:0 0 4px;font-size:15.5px}
  .desc{font-size:13px;color:var(--mut);margin:0 0 12px;line-height:1.5}
  .addf{display:flex;flex-wrap:wrap;gap:10px 14px;align-items:flex-end}
  .fld{display:flex;flex-direction:column;gap:4px;font-size:13px;color:var(--ink2);font-weight:600}
  input[type=text],input[type=password]{font:inherit;font-size:15px;padding:8px 11px;border-radius:9px;border:1px solid var(--line);background:var(--card);color:var(--ink);min-width:200px}
  .pwrap{display:flex;gap:6px}
  .perms{display:flex;flex-wrap:wrap;gap:6px 14px;padding:8px 0}
  .perms label{display:inline-flex;align-items:center;gap:6px;font-size:14px;cursor:pointer;white-space:nowrap}
  input[type=checkbox]{width:17px;height:17px;accent-color:var(--acc);cursor:pointer}
  input[type=checkbox]:disabled{cursor:not-allowed;opacity:.5}
  .btn{font:inherit;font-size:15px;font-weight:600;padding:8px 16px;border-radius:9px;border:1px solid var(--acc);background:var(--acc);color:#fff;cursor:pointer}
  .btn2{font:inherit;font-size:13.5px;font-weight:600;padding:5px 10px;border-radius:8px;border:1px solid var(--line);background:var(--card);color:var(--ink);cursor:pointer;white-space:nowrap}
  .btn2:hover{background:var(--hover)}
  .btn2.del{color:var(--crit-ink)}
  .btn:disabled,.btn2:disabled{opacity:.55;cursor:wait}
  .tw{overflow:auto;border:1px solid var(--line);border-radius:10px}
  table{width:100%;border-collapse:collapse;font-size:14px}
  th,td{padding:9px 12px;border-bottom:1px solid var(--hair);white-space:nowrap;text-align:left}
  th.c,td.c{text-align:center}
  thead th{font-size:12.5px;color:var(--mut);font-weight:600;background:var(--card);position:sticky;top:0}
  tbody tr:hover td{background:var(--hover)}
  tr.off td{color:var(--mut)}
  tr.off td.u b{text-decoration:line-through}
  .tag{display:inline-block;font-size:11.5px;font-weight:700;border-radius:999px;padding:1px 8px;margin-left:6px;background:var(--track);color:var(--ink2)}
  .last{color:var(--mut);font-size:13px}
  .msg{border-radius:10px;padding:10px 14px;font-size:14px}
  .msg.err{background:var(--crit-bg);color:var(--crit-ink)}
  .msg.ok{background:var(--good-bg);color:var(--good-ink)}
  .note{font-size:13px;color:var(--mut);line-height:1.6}
  .note b{color:var(--ink2)}
  #toast{position:fixed;left:50%;bottom:22px;transform:translateX(-50%);background:var(--ink);color:var(--card);padding:9px 16px;border-radius:10px;font-size:14px;font-weight:600;box-shadow:0 6px 20px rgba(0,0,0,.2);z-index:60}
  [hidden]{display:none !important}
  @media (max-width:820px){body{padding-left:0}
    .side{position:static;width:auto;flex-direction:row;flex-wrap:wrap;border-right:0;border-bottom:1px solid var(--line);padding:6px 8px;gap:4px}
    .side .menu{flex:1;justify-content:center;padding:8px 4px;font-size:13px;gap:5px;text-align:center}
    .side .menu.out{flex:0 0 auto;margin-top:0} .side .menu.out span{display:none}
    main{padding:12px 12px 30px}
    input[type=text],input[type=password]{min-width:0;width:100%}
    .fld{flex:1 1 100%}}
</style>
</head>
<body>
<aside class="side">
  <a class="menu" href="/">🚛 เช็กรถ</a>
  <a class="menu" href="/plan">📋 แผนงาน</a>
  <a class="menu" href="/report">📊 รายงาน On Time</a>
  <a class="menu" href="/ready">🚦 รถ/คนพร้อมใช้</a>
  <a class="menu on" href="/users">👥 ผู้ใช้</a>
  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>
</aside>
<header><h1>จัดการผู้ใช้</h1><p id="sub">เพิ่มผู้ใช้และกำหนดว่าแต่ละคนเปิดหน้าไหนได้ · บันทึกลงแท็บ User ในชีต · เฉพาะผู้ดูแล</p></header>
<main>
  <div id="msg" class="msg" hidden></div>
  <section class="card">
    <h3>เพิ่มผู้ใช้</h3>
    <p class="desc">ชื่อผู้ใช้ 2–32 ตัว (ก-ฮ a-z 0-9 . _ -) · รหัสผ่านอย่างน้อย 6 ตัว · ติ๊กหน้าที่ให้เข้าได้อย่างน้อย 1 หน้า</p>
    <form class="addf" id="addf" autocomplete="off">
      <label class="fld">ชื่อผู้ใช้<input type="text" id="nUser" maxlength="32" required></label>
      <label class="fld">รหัสผ่าน<span class="pwrap"><input type="password" id="nPw" minlength="6" required autocomplete="new-password">
        <button type="button" class="btn2" id="gen" title="สุ่มรหัส 10 ตัว">สุ่ม</button><button type="button" class="btn2" id="eye">แสดง</button></span></label>
      <div class="fld">เข้าได้หน้า<div class="perms" id="nPerms"></div></div>
      <button class="btn" id="addBtn">+ เพิ่มผู้ใช้</button>
    </form>
  </section>
  <section class="card">
    <h3>ผู้ใช้ทั้งหมด <span class="tag" id="cnt">–</span></h3>
    <p class="desc">ติ๊กเปลี่ยนสิทธิ์แล้วบันทึกทันที · มีผลกับคนที่ล็อกอินอยู่ภายใน 1 นาที · คนที่ปิด “ใช้งาน” จะเข้าระบบไม่ได้</p>
    <div class="tw"><table><thead><tr id="head"></tr></thead><tbody id="rows"><tr><td class="last">กำลังโหลด…</td></tr></tbody></table></div>
  </section>
  <p class="note">🔑 <b>รหัสกลาง</b> (APP_PASSWORD ใน Vercel) เข้าได้ทุกหน้าเสมอ ใช้กู้คืนถ้าตั้งสิทธิ์ผิดจนเข้าไม่ได้ ·
    รหัสที่ตั้งจากหน้านี้เก็บแบบ <b>เข้ารหัส</b> เปิดชีตจะไม่เห็นรหัสจริง · “เข้าใช้ล่าสุด” บันทึกตอนล็อกอินด้วยชื่อผู้ใช้สำเร็จ</p>
</main>
<div id="toast" hidden></div>
<script>
let PAGES = [];                                    // [key, ชื่อ] — มาจากเซิร์ฟเวอร์ (เพิ่มรายงานใหม่แล้วช่องติ๊กโผล่เอง)
let DATA = null;
function esc(s){ return String(s == null ? '' : s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c])); }
function toast(t){ const el = document.getElementById('toast'); el.textContent = t; el.hidden = false; clearTimeout(toast.t); toast.t = setTimeout(() => el.hidden = true, 2200); }
function msg(t, ok){ const el = document.getElementById('msg'); el.textContent = t || ''; el.className = 'msg ' + (ok ? 'ok' : 'err'); el.hidden = !t; }
async function api(url, body){
  const r = await fetch(url, body ? {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)} : {});
  if(r.status === 401){ location.href = '/login'; throw new Error('ต้องล็อกอินก่อน'); }
  let j = {}; try{ j = await r.json(); }catch(e){}
  if(!r.ok) throw new Error(j.detail || ('HTTP ' + r.status));
  return j;
}
function permBoxes(id, on){
  document.getElementById(id).innerHTML = PAGES.map(p => '<label><input type="checkbox" value="' + p[0] + '"' + (on.includes(p[0]) ? ' checked' : '') + '>' + p[1] + '</label>').join('');
}
async function load(){
  try{
    DATA = await api('/api/users');
    const first = !PAGES.length;
    PAGES = DATA.pages.map(p => [p.key, p.label]);
    if(first) permBoxes('nPerms', ['car']);
    draw();
  }catch(e){ msg('โหลดรายชื่อไม่สำเร็จ: ' + e.message); document.getElementById('rows').innerHTML = ''; }
}
function draw(){
  const me = (DATA.me || '').toLowerCase();
  document.getElementById('cnt').textContent = DATA.users.length + ' คน';
  document.getElementById('head').innerHTML = '<th>ชื่อผู้ใช้</th>' + PAGES.map(p => '<th class="c">' + p[1] + '</th>').join('') +
    '<th class="c">ใช้งาน</th><th>เข้าใช้ล่าสุด</th><th></th>';
  document.getElementById('rows').innerHTML = DATA.users.map(u => {
    const self = me && u.user.toLowerCase() === me;
    return '<tr class="' + (u.active ? '' : 'off') + '" data-u="' + esc(u.user) + '"><td class="u"><b>' + esc(u.user) + '</b>' +
      (self ? '<span class="tag">คุณ</span>' : '') + (!u.has_pw ? '<span class="tag">ยังไม่มีรหัส</span>' : '') + '</td>' +
      PAGES.map(p => '<td class="c"><input type="checkbox" data-p="' + p[0] + '"' + (u.perms.includes(p[0]) ? ' checked' : '') +
        (self && p[0] === 'admin' ? ' disabled title="เอาสิทธิ์ผู้ดูแลของตัวเองออกไม่ได้"' : '') + '></td>').join('') +
      '<td class="c"><input type="checkbox" data-a="1"' + (u.active ? ' checked' : '') + (self ? ' disabled title="ปิดบัญชีตัวเองไม่ได้"' : '') + '></td>' +
      '<td class="last">' + (esc(u.last) || '–') + '</td>' +
      '<td><button class="btn2" data-pw="1">ตั้งรหัสใหม่</button> ' + (self ? '' : '<button class="btn2 del" data-del="1">ลบ</button>') + '</td></tr>';
  }).join('') || '<tr><td colspan="9" class="last">ยังไม่มีผู้ใช้ — เพิ่มได้จากกล่องด้านบน</td></tr>';
}
document.getElementById('rows').addEventListener('change', async e => {
  const cb = e.target, tr = cb.closest('tr[data-u]');
  if(!tr || cb.type !== 'checkbox') return;
  const user = tr.dataset.u, body = {user};
  if(cb.dataset.a){ body.active = cb.checked; }
  else body.perms = [...tr.querySelectorAll('input[data-p]')].filter(x => x.checked).map(x => x.dataset.p);
  cb.disabled = true;
  try{ await api('/api/users/update', body); toast('บันทึกแล้ว · ' + user); msg(''); await load(); }
  catch(err){ cb.checked = !cb.checked; msg('บันทึกไม่สำเร็จ: ' + err.message); cb.disabled = false; }
});
document.getElementById('rows').addEventListener('click', async e => {
  const b = e.target.closest('button'), tr = b && b.closest('tr[data-u]');
  if(!tr) return;
  const user = tr.dataset.u;
  if(b.dataset.pw){
    const pw = prompt('รหัสผ่านใหม่ของ ' + user + ' (อย่างน้อย 6 ตัว)');
    if(pw == null) return;
    b.disabled = true;
    try{ await api('/api/users/update', {user, password: pw}); toast('ตั้งรหัสใหม่แล้ว · ' + user); msg(''); await load(); }
    catch(err){ msg('ตั้งรหัสไม่สำเร็จ: ' + err.message); b.disabled = false; }
  }else if(b.dataset.del){
    if(!confirm('ลบผู้ใช้ “' + user + '” ออกจากชีต?\\nถ้าแค่ไม่ให้เข้าชั่วคราว ให้เอาติ๊ก “ใช้งาน” ออกแทน')) return;
    b.disabled = true;
    try{ await api('/api/users/delete', {user}); toast('ลบแล้ว · ' + user); msg(''); await load(); }
    catch(err){ msg('ลบไม่สำเร็จ: ' + err.message); b.disabled = false; }
  }
});
document.getElementById('addf').addEventListener('submit', async e => {
  e.preventDefault();
  const b = document.getElementById('addBtn'), user = document.getElementById('nUser').value.trim(), pw = document.getElementById('nPw').value;
  const perms = [...document.querySelectorAll('#nPerms input')].filter(x => x.checked).map(x => x.value);
  b.disabled = true;
  try{
    await api('/api/users', {user, password: pw, perms, active: true});
    msg('เพิ่มผู้ใช้ “' + user + '” แล้ว — แจ้งชื่อผู้ใช้และรหัสผ่านให้เจ้าของบัญชีได้เลย', true);
    document.getElementById('addf').reset(); document.getElementById('nPw').type = 'password'; document.getElementById('eye').textContent = 'แสดง';
    permBoxes('nPerms', ['car']); await load();
  }catch(err){ msg('เพิ่มไม่สำเร็จ: ' + err.message); }
  finally{ b.disabled = false; }
});
document.getElementById('eye').onclick = () => { const i = document.getElementById('nPw'), s = i.type === 'password'; i.type = s ? 'text' : 'password'; document.getElementById('eye').textContent = s ? 'ซ่อน' : 'แสดง'; };
document.getElementById('gen').onclick = () => {
  const cs = 'abcdefghjkmnpqrstuvwxyz23456789', a = new Uint32Array(10); crypto.getRandomValues(a);
  const i = document.getElementById('nPw'); i.value = [...a].map(x => cs[x % cs.length]).join(''); i.type = 'text'; document.getElementById('eye').textContent = 'ซ่อน';
};
load();
</script>
</body>
</html>"""


LOGIN_HTML = """<!doctype html>
<html lang="th"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>เข้าสู่ระบบ — Gasbulk Track PTGLG</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;600;700&display=swap" rel="stylesheet" crossorigin="anonymous">
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
    <h1>🚛 Gasbulk Track PTGLG</h1>
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
<title>ตั้งค่า — Gasbulk Track PTGLG</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet" crossorigin="anonymous">
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
    <p style="margin:0 0 10px"><a class="back" href="/users">👥 จัดการผู้ใช้และสิทธิ์การเข้าหน้า &rarr;</a></p>
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
<title>รายงาน On Time — Gasbulk Track PTGLG</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet" crossorigin="anonymous">
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
  .rname i,.blab i{display:inline-block;width:10px;height:10px;border-radius:3px;margin-right:8px;vertical-align:0;background:var(--oc,var(--s1))}
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
  /* ── หน้าตาชุดเดียวกับหน้า รถ/คนพร้อมใช้: การ์ดเรียบ สี่เหลี่ยมสีบอกกลุ่ม แท่งต่อกันมีช่อง 2px ปลายมน 4px ── */
  :root{--track:#eef0f3;--bar:#5b6b82}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])){--track:#242422;--bar:#8d9bb0}}
  :root[data-theme="dark"]{--track:#242422;--bar:#8d9bb0}
  body{font-size:15px}
  .key{display:inline-block;width:10px;height:10px;border-radius:3px;flex:0 0 auto}
  .tile{padding:16px 18px;border-radius:12px}
  .tile::before{display:none}
  .tile .l{font-size:13.5px;color:var(--ink2);font-weight:600;gap:8px}
  .tile .v{font-size:30px;line-height:1.1;margin-top:8px;letter-spacing:-.4px}
  .tile .v small{font-size:14px}
  .tile .s{font-size:13px;line-height:1.5;margin-top:4px}
  .tile.hero{background:var(--card)}
  .hero .v{font-size:48px;line-height:1.05;letter-spacing:-.8px}
  .hero .v small{font-size:16px;margin-left:6px}
  .pbar{gap:2px;height:22px;border-radius:0 4px 4px 0;background:none;margin:14px 0 10px}
  .pbar i{display:flex;align-items:center;justify-content:center;font-style:normal;font-size:12px;font-weight:700;min-width:3px;overflow:hidden;white-space:nowrap;cursor:pointer}
  .pbar i b{padding:0 4px}
  .leg2{gap:6px 18px;font-size:13.5px}
  .leg2 span{display:inline-flex;align-items:center;gap:7px;white-space:nowrap}
  .leg2 em{font-style:normal;color:var(--mut)}
  .panel{padding:16px 18px 14px;border-radius:12px}
  .ph{margin-bottom:2px}
  .ph h3{font-size:15.5px;white-space:nowrap}
  .ph .sub{font-size:13px}
  .legend{font-size:13.5px;gap:6px 18px;flex:0 0 auto}
  .legend span{display:inline-flex;align-items:center;white-space:nowrap}
  .hint{background:none;padding:0;margin:2px 0 12px;font-size:13px;line-height:1.5;color:var(--mut);border-radius:0}
  .hint b{color:var(--ink2);font-weight:600}
  .stack{gap:2px;height:22px;border-radius:0 4px 4px 0;margin:6px 0 14px}
  .clist{font-size:14px}
  .btrack{height:26px}
  .bfill{top:7px;height:12px;border-radius:0 4px 4px 0}
  .blab{font-size:14px}
  .bval{font-size:13.5px}
  .brow.on > *,.rrow.on > *{background:var(--hover)}
  .oc{gap:0}
  .orow{border:0;border-bottom:1px solid var(--hair);border-radius:0;padding:10px 4px;background:transparent;min-height:58px}
  .orow:last-child{border-bottom:0}
  .orow.on{box-shadow:none;background:var(--hover)}
  .orow .on1{font-size:15px}
  .orow .otr{gap:2px;height:22px;border-radius:0 4px 4px 0;background:none}
  .orow .osg{font-size:12px}
  .orow .osg.l{box-shadow:none}
  .orow .omm .w b,.orow .omm .l b{color:var(--ink)}
  .orow .omm span::before{content:'';display:inline-block;width:9px;height:9px;border-radius:3px;margin-right:6px;vertical-align:0}
  .orow .omm .w::before{background:var(--wc)} .orow .omm .l::before{background:var(--lc)}
  .orow .oav b{font-size:24px}
  .dgrid{gap:16px}
  .dgrp{border-radius:10px;box-shadow:none}
  .dgh{border-top:0;border-bottom:1px solid var(--hair);background:var(--card)}
  .dgh:hover{background:var(--hover)}
  .dgh.on{box-shadow:none;background:var(--hover)}
  .dgh .nm{display:flex;align-items:center;gap:8px}
  .dgh .nm::before{content:'';width:10px;height:10px;border-radius:3px;background:var(--oc);flex:0 0 auto}
  .dgh .st b{font-size:17px}
  .tchart h4{font-size:14px;font-weight:700}
  .tchart .lg{gap:16px}
  .tchart .lg i{width:14px;height:2px}
  #tip{background:var(--card);color:var(--ink);border:1px solid var(--line);border-radius:10px;box-shadow:0 6px 20px rgba(16,24,40,.16);padding:9px 12px;font-size:13px;line-height:1.55}
  .tw{border-radius:10px}
  th{font-size:12.5px;font-weight:600;letter-spacing:0}
  .pill{background:none !important;padding:0;color:var(--ink) !important;font-weight:600;gap:7px}
  .pill::before{content:'';width:9px;height:9px;border-radius:50%;display:inline-block}
  .pill.ok::before{background:var(--good)} .pill.bad::before{background:var(--crit)}
  .chip.f{font-size:13px}
  @media (max-width:820px){ .tile .v{font-size:26px} .hero .v{font-size:42px} .orow .oav b{font-size:20px} }
  [hidden]{display:none !important}
</style>
</head>
<body>
<aside class="side">
  <a class="menu" href="/">🚛 เช็กรถ</a>
  <a class="menu" href="/plan">📋 แผนงาน</a>
  <a class="menu on" href="/report">📊 รายงาน On Time</a>
  <a class="menu" href="/ready">🚦 รถ/คนพร้อมใช้</a>
  <a class="menu" href="/users">👥 ผู้ใช้</a>
  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>
</aside>
<header><div class="hd">
  <div class="ttl"><h1>รายงาน On Time PTGLG</h1><p id="stamp">ข้อมูลจากชีตแผนงานจริง · อ่านอย่างเดียว</p></div>
  <span class="grow"></span>
  <div class="seg" id="presets">
    <button data-p="0">วันนี้</button><button data-p="1">เมื่อวาน</button><button data-p="7">7 วัน</button><button data-p="30">30 วัน</button>
  </div>
  <div class="rng"><input type="date" id="dFrom" aria-label="ตั้งแต่วันที่"><span style="color:var(--mut)">–</span><input type="date" id="dTo" aria-label="ถึงวันที่"></div>
  <button class="btn" id="go">ดูรายงาน</button>
  <button class="btn2" id="refresh" title="อ่านข้อมูลจากชีตใหม่ทันที ไม่รอรอบ 30 นาที">🔄 รีเฟรช</button>
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
    <p class="hint">ดูว่าแต่ละวันเพิ่มขึ้นหรือลดลง · <b>On Time ยิ่งสูงยิ่งดี</b> · <b>เวลารอโหลด/โหลด ยิ่งต่ำยิ่งดี</b> · ชี้ที่จุดเพื่อดูตัวเลข</p>
    <div class="tgrid"><div class="tchart" id="tOt"></div><div class="tchart" id="tWl"></div></div></section>
  <div class="panels">
    <section class="panel w8 fillp"><div class="ph"><h3>เวลารอโหลด + โหลดสินค้า แยกตามต้นทาง</h3><span class="sub">นาที (เฉลี่ย)</span>
      <div class="legend"><span><i class="lw"></i>รอโหลดสินค้า</span><span><i class="ll"></i>โหลดสินค้า</span></div></div>
      <p class="hint">แท่งเดียวต่อกัน: <b style="color:var(--wc)">ม่วง = รอโหลด</b> (เข้าลาน → เริ่มโหลด) ต่อด้วย <b style="color:var(--lc)">ชมพู = โหลด</b> (เริ่มโหลด → โหลดเสร็จ) · ตัวเลขขวา = รวมเวลาอยู่ที่ต้นทาง · <b>แท่งยิ่งยาว = อยู่นาน</b> · กดแถวเพื่อกรอง</p>
      <div id="cOrigin"></div></section>
    <div class="w4 col2">
      <section class="panel"><div class="ph"><h3>สัดส่วนตามระยะทาง</h3></div>
        <p class="hint">งานแบ่งตามระยะทางต้นทาง → ปลายทาง: <b>ใกล้</b> ไม่เกิน 80 กม. · <b>กลาง</b> 81–250 · <b>ไกล</b> เกิน 250 กม. · กดสีเพื่อกรอง</p>
        <div id="cClass"></div></section>
      <section class="panel"><div class="ph"><h3>จำนวนเที่ยวตามประเภทรถ</h3></div><p class="hint">รถแต่ละขนาดวิ่งไปกี่เที่ยวในช่วงวันที่ที่เลือก</p><div id="cVtype"></div></section>
    </div>
    <section class="panel w12"><div class="ph"><h3>สรุปตามต้นทาง</h3><span class="sub">นาที</span></div><p class="hint"><b>รอโหลด</b> = เข้าลาน → เริ่มโหลด · <b>โหลด</b> = เริ่มโหลด → โหลดเสร็จ · ต่ำสุด / สูงสุด / เฉลี่ย ของแต่ละต้นทาง · กดหัวคอลัมน์เพื่อเรียง</p>
      <div class="tw" style="max-height:none"><table><thead><tr class="grp"><th colspan="2"></th><th colspan="3" class="gw">⏳ เวลารอโหลดสินค้า (นาที)</th><th colspan="3" class="gl">⛽ เวลาโหลดสินค้า (นาที)</th></tr><tr id="oHead"></tr></thead><tbody id="tOrigin"></tbody></table></div></section>
    <section class="panel w6"><div class="ph"><h3>สาเหตุ On Time / ล่าช้า</h3><span class="sub" id="whySub"></span></div><p class="hint">จากคอลัมน์ <b>สาเหตุ On Time</b> ในชีต · นับเป็นจำนวนงาน · กดชื่อสาเหตุเพื่อดูงานนั้น</p><div id="cWhy"></div></section>
    <section class="panel w6"><div class="ph"><h3>สาเหตุแก้ไขงาน</h3><span class="sub" id="fixSub"></span></div><p class="hint">จากคอลัมน์ <b>สาเหตุแก้ไขงาน</b> ในชีต · เช่น ลูกค้ายกเลิก, ปลายทางใหม่ · กดชื่อสาเหตุเพื่อดูงานนั้น</p><div id="cFix"></div></section>
    <section class="panel w12"><div class="ph"><h3>เวลาที่อยู่ในสถานี (เฉลี่ย)</h3><span class="sub">นาที</span></div><p class="hint">รถจอดอยู่ที่ปลายทางนานเท่าไร (<b>ถึงปลายทาง → ออกจากปลายทาง</b>) แยกตามประเภทงาน · <b>ตัวเลขมาก = ลงของนาน</b> · เรียงจากนานสุดลงมา · กดหัวการ์ดหรือชื่อปลายทางเพื่อกรอง</p><div id="cDest"></div></section>
    <section class="panel w12" data-nosnap="1"><div class="tools"><h3 style="margin:0;font-size:16px">รายการทั้งหมด</h3><span class="sub" id="rowCount" style="font-size:14px;color:var(--mut)"></span><span class="grow"></span>
      <input type="search" id="q" placeholder="ค้นหา รถ / ปลายทาง / ออเดอร์" style="min-width:260px"></div>
      <p class="hint">ทุกงาน (drop) ในช่วงวันที่ที่เลือก · <b>กดหัวคอลัมน์</b> เพื่อเรียงน้อย→มาก / มาก→น้อย · <b>กดเบอร์รถ</b> เพื่อดูเฉพาะคันนั้น · ช่องค้นหาด้านบนพิมพ์เบอร์รถ/ปลายทาง/ออเดอร์ได้</p>
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
async function load(keepFilters, fresh){
  const q = new URLSearchParams({from: document.getElementById('dFrom').value, to: document.getElementById('dTo').value,
    origin: getF('origin'), vtype: getF('vtype'), car: getF('car'), drop: getF('drop'), status: getF('status'), dest: XF.dest, cls: XF.cls, jtype: XF.jtype, why: XF.why, fix: XF.fix});
  if(fresh === true) q.set('fresh', '1');
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
    document.getElementById('stamp').textContent = 'ข้อมูลจากชีตแผนงานจริง · อ่านอย่างเดียว · อัปเดต ' + arT(new Date()) + arStamp();
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
  return '<div class="tile' + (extra || '') + '"><div class="l">' + (color ? '<i class="key" style="background:' + color + '"></i>' : '') + label + '</div><div class="v">' + value + (unit ? '<small>' + unit + '</small>' : '') + '</div>' +
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
    g += '<path d="' + path + '" fill="none" stroke="' + sr.color + '" stroke-width="2" stroke-linejoin="round" stroke-linecap="round"/>';
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
    '<div class="tile hero"><div class="l">On Time · ' + (REP.from === REP.to ? dmy(REP.from) : dmy(REP.from) + ' – ' + dmy(REP.to)) + '</div>' +
      '<div class="v">' + (pct == null ? '–' : Math.round(pct * 10) / 10 + '%') + '<small>จาก ' + num(judged, 0) + ' drop ที่มีผลในชีต</small></div>' +
      '<div class="pbar">' + (judged ? [['PASS', k.pass, 'var(--good)', '#0b0b0b'], ['Delay', k.delay, 'var(--crit)', '#fff']].filter(x => x[1] > 0).map(x =>
        '<i data-k="status" data-v="' + x[0] + '" data-tip="' + esc(x[0] + ' ' + x[1] + ' drop (' + Math.round(x[1] / judged * 100) + '%)') + '" style="flex:' + x[1] + ' 1 0;background:' + x[2] + ';color:' + x[3] + '"><b>' + x[1] + '</b></i>').join('')
        : '<i style="flex:1;background:var(--track)"></i>') + '</div>' +
      '<div class="leg2"><span data-k="status" data-v="PASS"><i class="key" style="background:var(--good)"></i>PASS <b>' + num(k.pass, 0) + '</b><em>' + (judged ? Math.round(k.pass / judged * 100) + '%' : '') + '</em></span>' +
      '<span data-k="status" data-v="Delay"><i class="key" style="background:var(--crit)"></i>Delay <b>' + num(k.delay, 0) + '</b><em>' + (judged ? Math.round(k.delay / judged * 100) + '%' : '') + '</em></span></div>' +
      (pct == null ? '' : '<div class="dl ' + (pct >= tgt ? 'good' : 'bad') + '" data-tip="' + esc('เป้า On Time ' + tgt + '% ขึ้นไป' + (REP.prev && pctOf(REP.prev.kpi) != null ? ' · ช่วงก่อน ' + num(pctOf(REP.prev.kpi), 1) + '%' : '')) + '">' +
        (pct >= tgt ? '✓ ผ่านเป้า ' + tgt + '%' : '⚠ ต่ำกว่าเป้า ' + tgt + '%') + '</div>') +
      '<div class="s" style="margin-top:6px"><b>PASS</b> = ส่งถึงลูกค้าไม่ช้าเกิน 30 นาที · <b>Delay</b> = ช้าเกิน 30 นาที · <b>เป้า ' + tgt + '% ขึ้นไป</b></div></div>' +
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
// สาเหตุ: แท่งแนวนอนเรียงมาก→น้อย 8 อันดับแรก + อื่นๆ (ชี้ที่ "อื่นๆ" เพื่อดูรายการ) · กดชื่อเพื่อกรอง
function donut(elId, subId, list, key, unitWord){
  const el = document.getElementById(elId), tot = list.reduce((a, x) => a + x.n, 0), sel = getF(key), TOP = 8;
  document.getElementById(subId).textContent = tot ? num(tot, 0) + ' งาน · ' + list.length + ' สาเหตุ' : '';
  if(!tot){ el.innerHTML = '<div class="empty">ไม่มีการบันทึกสาเหตุในช่วงวันที่นี้</div>'; return; }
  const parts = list.slice(0, TOP).map(x => ({t: x.why, n: x.n, k: key, x: x})), rest = list.slice(TOP);
  if(rest.length) parts.push({t: 'อื่นๆ (' + rest.length + ' สาเหตุ)', n: rest.reduce((a, x) => a + x.n, 0), tip: rest.map(x => x.why + ' ' + x.n).join(' · ')});
  const mx = Math.max.apply(null, parts.map(p => p.n));
  el.innerHTML = '<div class="bars">' + parts.map(p => {
    const tip = p.tip || (p.t + ' · ' + p.n + ' งาน (' + Math.round(p.n / tot * 100) + '%)' + (p.x && p.x.delay != null ? ' · Delay ' + p.x.delay : '') + (p.x && p.x.cancel ? ' · ยกเลิก ' + p.x.cancel : ''));
    return '<div class="brow' + (sel && sel === p.t ? ' on' : '') + '" style="--oc:var(--bar)"' + (p.k ? ' data-k="' + p.k + '" data-v="' + esc(p.t) + '"' : '') + ' data-tip="' + esc(tip) + '">' +
      '<div class="blab" title="' + esc(p.t) + '">' + esc(p.t) + '</div><div class="btrack"><div class="bfill" style="width:' + Math.max(0.5, p.n / mx * 100) + '%"></div></div>' +
      '<div class="bval"><b>' + p.n + '</b> · ' + Math.round(p.n / tot * 100) + '%</div></div>';
  }).join('') + '</div>';
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
  cap.innerHTML = '<b>รายงาน On Time PTGLG · ' + rng + '</b><span>' + (keys.length ? 'กรอง: ' + keys.map(k => FNAME[k] + ' ' + esc(getF(k))).join(' · ') + ' · ' : '') +
    'แคปเมื่อ ' + new Date().toLocaleString('th-TH', {dateStyle: 'short', timeStyle: 'short'}) + '</span>';
  main.insertBefore(cap, main.firstChild);
  const hide = [...main.querySelectorAll('[data-nosnap]')].filter(e => !e.hidden);   // ซ่อนจริงระหว่างแคป ไม่งั้นรูปมีที่ว่างเท่าความสูงตาราง
  hide.forEach(e => e.hidden = true);
  try{
    const lib = await loadH2I();
    let fontCss = '';
    try{ fontCss = await lib.getFontEmbedCSS(main); }catch(e){}                       // ฝังฟอนต์ไทย ตัวหนังสือในรูปจะได้กว้างเท่าบนจอ
    const blob = await lib.toBlob(main, {pixelRatio: 2, backgroundColor: getComputedStyle(document.body).backgroundColor,
      fontEmbedCSS: fontCss || undefined, skipFonts: !fontCss, filter: n => !(n.dataset && n.dataset.nosnap)});
    const name = 'PTGLG_ontime_' + REP.from + (REP.to !== REP.from ? '_' + REP.to : '') + '.png';
    const file = new File([blob], name, {type: 'image/png'});
    if(navigator.canShare && navigator.canShare({files: [file]}) && matchMedia('(pointer:coarse)').matches){
      try{ await navigator.share({files: [file], title: 'รายงาน On Time PTGLG ' + rng}); }catch(e){}
    }else{
      const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name;
      document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1500);
    }
  }catch(e){
    alert('แคปไม่สำเร็จ: ' + (e && e.message ? e.message : e) + ' — ลองใหม่อีกครั้ง หรือใช้ปุ่มแคปหน้าจอของเครื่องแทน');
  }finally{
    cap.remove(); hide.forEach(e => e.hidden = false); b.disabled = false; b.textContent = '📷 แคปส่ง';
  }
};
['dFrom', 'dTo'].forEach(id => { document.getElementById(id).onchange = () => { markPreset(); load(); }; });
['fOrigin', 'fVtype', 'fCar', 'fDrop', 'fStatus'].forEach(id => { document.getElementById(id).onchange = () => load(true); });
document.getElementById('q').oninput = () => { if(REP) drawRows(); };
// ── รีเฟรชอัตโนมัติทุก 30 นาที: เปิดทิ้งไว้ก็ได้ข้อมูลใหม่เอง (ตัวกรอง/ช่วงวันที่ที่เลือกยังอยู่) ──
// แท็บที่ซ่อนอยู่ไม่โหลด (ประหยัดโควตาชีต) กลับมาที่แท็บแล้วถ้าเลยเวลา โหลดทันที
const AR_MIN = 30;
let AR_NEXT = Date.now() + AR_MIN * 60000;
function arT(d){ return d.toLocaleTimeString('th-TH', {hour: '2-digit', minute: '2-digit'}); }
function arStamp(){ AR_NEXT = Date.now() + AR_MIN * 60000; return ' · 🔄 รีเฟรชอัตโนมัติทุก ' + AR_MIN + ' นาที (ครั้งถัดไป ' + arT(new Date(AR_NEXT)) + ')'; }
function arTick(){
  const busy = document.getElementById('main').classList.contains('busy') || document.getElementById('snap').disabled;
  if(Date.now() >= AR_NEXT && !document.hidden && !busy) load(true);
}
setInterval(arTick, 30000);
document.addEventListener('visibilitychange', () => { if(!document.hidden) arTick(); });
document.getElementById('refresh').onclick = async () => {        // อยากได้เร็ว: อ่านชีตสดทันที
  const b = document.getElementById('refresh');
  b.disabled = true; b.textContent = '⏳ กำลังอ่านชีต…';
  try{ await load(true, true); } finally{ b.disabled = false; b.textContent = '🔄 รีเฟรช'; }
};
setRange(new Date(), new Date());
load();
</script>
</body></html>
"""


READY_HTML = """<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>รถ/คนพร้อมใช้งาน — Gasbulk Track PTGLG</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet" crossorigin="anonymous">
<style>
  /* สีสถานะ: ตรวจตาบอดสีแล้ว (คู่ติดกัน ΔE ≥ 10) ทั้งโหมดสว่าง/มืด · เหลืองบนพื้นขาวคอนทราสต์ต่ำ → มีตัวเลข/ตารางกำกับเสมอ */
  :root{color-scheme:light;
    --plane:#f4f5f7;--card:#ffffff;--surface:#fcfcfb;--line:#e6e8ec;--hair:#eceae4;--track:#eef0f3;
    --ink:#0b0b0b;--ink2:#3f3e3b;--mut:#6b6964;--hover:#f3f6fb;--acc:#2563eb;
    --run:#0ca30c;--free:#2a78d6;--nod:#eda100;--down:#d03b3b;--trip:#5b6b82;--goal:#0b0b0b;
    --shadow:0 1px 2px rgba(16,24,40,.05),0 1px 3px rgba(16,24,40,.07)}
  @media (prefers-color-scheme:dark){
    :root:where(:not([data-theme="light"])){color-scheme:dark;
      --plane:#0d0d0d;--card:#161616;--surface:#1a1a19;--line:#2a2a28;--hair:#2c2c2a;--track:#242422;
      --ink:#f0efec;--ink2:#d6d5cc;--mut:#a9a7a0;--hover:#1f2733;--acc:#3b82f6;
      --run:#0ca30c;--free:#3987e5;--nod:#c98500;--down:#d03b3b;--trip:#8d9bb0;--goal:#f0efec;--shadow:none}}
  :root[data-theme="dark"]{color-scheme:dark;
      --plane:#0d0d0d;--card:#161616;--surface:#1a1a19;--line:#2a2a28;--hair:#2c2c2a;--track:#242422;
      --ink:#f0efec;--ink2:#d6d5cc;--mut:#a9a7a0;--hover:#1f2733;--acc:#3b82f6;
      --run:#0ca30c;--free:#3987e5;--nod:#c98500;--down:#d03b3b;--trip:#8d9bb0;--goal:#f0efec;--shadow:none}
  *{box-sizing:border-box}
  body{margin:0;background:var(--plane);color:var(--ink);font-family:'Noto Sans Thai',system-ui,-apple-system,"Segoe UI",sans-serif;font-size:15px;padding-left:148px}
  .side{position:fixed;left:0;top:0;bottom:0;width:148px;background:var(--card);border-right:1px solid var(--line);padding:14px 10px;display:flex;flex-direction:column;gap:6px;z-index:20}
  .side .menu{display:flex;align-items:center;gap:9px;text-decoration:none;font-weight:700;font-size:16px;color:var(--ink);padding:11px 12px;border-radius:10px}
  .side .menu:hover{background:var(--hover)}
  .side .menu.on{background:#2563eb;color:#fff}
  .side .menu.out{margin-top:auto;color:var(--mut);font-size:14.5px;white-space:nowrap}
  @media (max-width:820px){body{padding-left:0}
    .side{position:static;width:auto;flex-direction:row;flex-wrap:wrap;border-right:0;border-bottom:1px solid var(--line);padding:8px 10px}
    .side .menu{flex:1;justify-content:center;padding:9px 6px;font-size:14.5px}
    .side .menu.out{flex:0 0 auto;margin-top:0} .side .menu.out span{display:none}}
  header{background:var(--card);border-bottom:1px solid var(--line);padding:14px 22px;position:sticky;top:0;z-index:10}
  .panel{scroll-margin-top:84px}
  .hd{display:flex;flex-wrap:wrap;gap:12px 16px;align-items:center}
  .ttl h1{font-size:21px;margin:0;font-weight:700;letter-spacing:-.2px}
  .ttl p{margin:2px 0 0;font-size:13.5px;color:var(--mut)}
  .grow{flex:1}
  .seg{display:inline-flex;background:var(--plane);border:1px solid var(--line);border-radius:10px;padding:3px}
  .seg button{border:0;background:transparent;padding:6px 12px;border-radius:7px;font:inherit;font-size:14.5px;font-weight:600;color:var(--ink2);cursor:pointer}
  .seg button.on{background:var(--card);color:var(--ink);box-shadow:var(--shadow)}
  input{font:inherit;font-size:15px;padding:7px 10px;border-radius:9px;border:1px solid var(--line);background:var(--card);color:var(--ink)}
  .btn{font:inherit;font-size:15px;font-weight:600;padding:7px 14px;border-radius:9px;border:1px solid var(--acc);background:var(--acc);color:#fff;cursor:pointer}
  .btn2{font:inherit;font-size:15px;font-weight:600;padding:7px 14px;border-radius:9px;border:1px solid var(--line);background:var(--card);color:var(--ink);cursor:pointer;white-space:nowrap}
  .btn2:hover{background:var(--hover)}
  .btn2:disabled{opacity:.6;cursor:wait}
  .snapcap{display:flex;justify-content:space-between;gap:12px;flex-wrap:wrap;align-items:baseline;padding:4px 2px 12px}
  .snapcap b{font-size:19px}
  .snapcap span{font-size:13.5px;color:var(--mut)}
  .tgt{display:flex;align-items:center;gap:7px;font-size:14px;color:var(--mut)}
  .tgt input{width:68px;text-align:right}
  main{padding:18px 22px 40px;transition:opacity .15s}
  main.busy{opacity:.55;pointer-events:none}
  .err{background:#fdecec;border:1px solid #f6caca;color:#b42318;border-radius:10px;padding:10px 14px;margin-bottom:12px;font-size:14.5px}
  .note{background:var(--card);border:1px solid var(--line);border-left:4px solid var(--nod);border-radius:10px;padding:10px 14px;margin-bottom:14px;font-size:14px;color:var(--ink2)}
  .note ul{margin:4px 0 0;padding-left:20px}

  /* ── การ์ดตัวเลข ── */
  .kpis{display:grid;grid-template-columns:repeat(12,minmax(0,1fr));gap:12px;margin-bottom:12px}
  .k4{grid-column:span 4}.k3{grid-column:span 3}
  .rng{display:flex;align-items:center;gap:6px}.rng .dash{color:var(--mut)}
  .ctl{display:flex;flex-wrap:wrap;gap:10px 12px;align-items:center;justify-content:flex-end}
  .card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px 18px;box-shadow:var(--shadow);min-width:0}
  .w2{grid-column:span 2}
  .lab{font-size:13.5px;color:var(--ink2);font-weight:600;display:flex;align-items:center;gap:8px}
  .key{display:inline-block;width:10px;height:10px;border-radius:3px;flex:0 0 auto}
  .big{font-size:48px;font-weight:700;line-height:1.05;letter-spacing:-.8px;margin-top:8px}
  .big small{font-size:16px;font-weight:600;color:var(--mut);letter-spacing:0;margin-left:6px}
  .val{font-size:30px;font-weight:700;line-height:1.1;letter-spacing:-.4px;margin-top:8px}
  .val small{font-size:14px;font-weight:600;color:var(--mut);letter-spacing:0;margin-left:4px}
  .sub{font-size:13px;color:var(--mut);margin-top:4px;line-height:1.5}
  .sub b{color:var(--ink2);font-weight:600}
  @media (max-width:1100px){.k4{grid-column:span 12}.k3{grid-column:span 6}}
  @media (max-width:560px){.kpis{gap:10px}}

  /* แท่งต่อกัน (stack): ช่องว่าง 2px สีพื้นคั่นทุกช่วง · ปลายข้อมูลมน 4px ฐานเหลี่ยม */
  .stk{display:flex;gap:2px;height:14px;border-radius:0 4px 4px 0;overflow:hidden}
  .stk.tall{height:22px}
  .sg{position:relative;min-width:3px;display:flex;align-items:center;justify-content:center;font-size:12px;font-weight:700;white-space:nowrap;overflow:hidden;cursor:default}
  .sg b{font-weight:700;padding:0 4px}
  .legend{display:flex;flex-wrap:wrap;gap:6px 18px;font-size:13.5px;color:var(--ink2);margin-top:10px}
  .legend span{display:inline-flex;align-items:center;gap:7px;white-space:nowrap}
  .legend b{color:var(--ink);font-weight:600}
  .legend em{font-style:normal;color:var(--mut)}
  .meter{position:relative;height:14px;background:var(--track);border-radius:0 4px 4px 0;margin:14px 0 8px}
  .meter i{position:absolute;left:0;top:0;bottom:0;background:var(--trip);border-radius:0 4px 4px 0}
  .meter u{position:absolute;top:-5px;bottom:-5px;width:2px;background:var(--goal);text-decoration:none}
  .meter u::after{content:'เป้า';position:absolute;top:-17px;left:50%;transform:translateX(-50%);font-size:11.5px;color:var(--ink2);font-weight:600}
  .ok{color:var(--ink);font-weight:700}

  /* ── แผงกราฟ ── */
  .panels{display:grid;grid-template-columns:repeat(12,minmax(0,1fr));gap:12px}
  .panel{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px 18px 14px;box-shadow:var(--shadow);min-width:0}
  .c7{grid-column:span 7}.c5{grid-column:span 5}.c6{grid-column:span 6}.c12{grid-column:span 12}
  @media (max-width:1100px){.c7,.c5,.c6{grid-column:span 12}}
  .ph{display:flex;align-items:baseline;gap:10px;flex-wrap:wrap;margin-bottom:2px}
  .ph h3{margin:0;font-size:15.5px;font-weight:700;white-space:nowrap}
  .ph .s2{font-size:13px;color:var(--mut)}
  .ph .legend{margin:0 0 0 auto;flex:0 0 auto;flex-wrap:nowrap}
  .desc{font-size:13px;color:var(--mut);margin:2px 0 12px}
  .chart{position:relative;width:100%}
  .chart svg{display:block;overflow:visible}
  .chart .gl{stroke:var(--line);stroke-width:1}
  .chart .ax{fill:var(--mut);font-size:11px;font-variant-numeric:tabular-nums}
  .chart .ax.sel{fill:var(--ink);font-weight:700}
  .chart .hit{fill:transparent;cursor:pointer}
  .chart .hit:hover{fill:var(--hover);fill-opacity:.6}
  .chart .vl{fill:var(--ink);font-size:11.5px;font-weight:700}
  /* แถวแท่งแนวนอน */
  .rows{display:grid;grid-template-columns:minmax(96px,150px) 1fr auto;align-items:center;column-gap:14px}
  .rw{display:contents}
  .rw > *{padding:9px 0;border-bottom:1px solid var(--hair)}
  .rw:last-child > *{border-bottom:0}
  .rn{font-size:14.5px;font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
  .rn small{display:block;font-size:12.5px;font-weight:400;color:var(--mut)}
  .rv{font-size:13.5px;color:var(--ink2);text-align:right;white-space:nowrap;font-variant-numeric:tabular-nums}
  .rv b{color:var(--ink);font-size:14.5px}
  .bar{height:12px;border-radius:0 4px 4px 0;background:var(--down);min-width:3px}
  .divider{height:1px;background:var(--hair);margin:14px 0 10px}
  .empty{color:var(--mut);font-size:14px;padding:10px 2px}

  /* ── ตาราง ── */
  .tools{display:flex;align-items:baseline;gap:10px;flex-wrap:wrap;margin-bottom:10px}
  .tw{max-height:460px;overflow:auto;border:1px solid var(--line);border-radius:10px}
  table{width:100%;border-collapse:collapse;font-size:14px}
  th,td{text-align:left;padding:8px 12px;border-bottom:1px solid var(--hair);white-space:nowrap}
  th.n,td.n{text-align:right;font-variant-numeric:tabular-nums}
  thead th{font-size:12.5px;color:var(--mut);font-weight:600;position:sticky;top:0;background:var(--card);text-transform:none}
  tbody tr:hover td{background:var(--hover)}
  .st{display:inline-flex;align-items:center;gap:7px;font-weight:600}
  .st i{width:9px;height:9px;border-radius:50%;display:inline-block}
  .code{color:var(--mut);font-size:12.5px;margin-left:4px}

  /* กดกราฟ → กรองตาราง */
  [data-f]{cursor:pointer}
  .card[data-f]:hover{border-color:var(--acc)}
  .rw[data-f]:hover > *{background:var(--hover)}
  .legend span[data-f]{border-radius:6px;padding:1px 5px;margin:-1px -5px}
  .legend span[data-f]:hover{background:var(--hover)}
  .sg:hover,.bar:hover{filter:brightness(1.08)}
  .chips{display:flex;flex-wrap:wrap;gap:6px;align-items:center}
  .chip{font:inherit;font-size:13px;font-weight:600;border-radius:999px;padding:3px 10px;border:1px solid #bfd5fb;background:#eaf1fe;color:#1d4ed8;cursor:pointer}
  .chip.clr{background:var(--card);border-color:var(--line);color:var(--ink2)}
  @media (prefers-color-scheme:dark){:root:where(:not([data-theme="light"])) .chip:not(.clr){background:#14243a;border-color:#24497a;color:#9ec5f4}}
  :root[data-theme="dark"] .chip:not(.clr){background:#14243a;border-color:#24497a;color:#9ec5f4}
  .flash{animation:flash 1.2s ease-out}
  @keyframes flash{0%{box-shadow:0 0 0 3px var(--acc)}100%{box-shadow:var(--shadow)}}
  #tip{position:fixed;z-index:50;pointer-events:none;background:var(--card);color:var(--ink);border:1px solid var(--line);border-radius:10px;
       box-shadow:0 6px 20px rgba(16,24,40,.16);padding:9px 12px;font-size:13px;line-height:1.55;max-width:280px}
  #tip .t{font-weight:700;margin-bottom:3px}
  #tip .r{display:flex;align-items:center;gap:8px;justify-content:space-between}
  #tip .r span{display:inline-flex;align-items:center;gap:7px;color:var(--ink2)}
  #tip .r b{font-variant-numeric:tabular-nums}
  @media (max-width:700px){
    body{font-size:14.5px}
    .side{gap:4px;padding:6px 8px}
    .side .menu{font-size:13px;padding:8px 4px;gap:5px;text-align:center}
    header{position:static;padding:12px 14px}
    .hd{gap:8px}
    .ttl{flex:1 1 100%}
    .ctl{flex:1 1 100%;justify-content:stretch;gap:8px}
    .ttl h1{font-size:19px}
    .seg{flex:1 1 100%}.seg button{flex:1}
    .rng{flex:1 1 100%}.rng input{flex:1;min-width:0}
    .tgt{flex:0 0 auto}
    .btn,.btn2{flex:1 1 40%}
    main{padding:12px 12px 32px}
    .card,.panel{padding:14px 14px 12px;border-radius:11px}
    .big{font-size:42px}
    .val{font-size:26px}
    .ph .legend{margin:6px 0 0;flex:1 1 100%}
    .rows{grid-template-columns:minmax(78px,110px) 1fr auto;column-gap:10px}
    .tools input[type=search]{min-width:0 !important;flex:1 1 100%}
    th,td{padding:7px 9px}
    .m-hide{display:none}
    .tw{max-height:70vh !important}
  }
  [hidden]{display:none !important}
</style>
</head>
<body>
<aside class="side">
  <a class="menu" href="/">🚛 เช็กรถ</a>
  <a class="menu" href="/plan">📋 แผนงาน</a>
  <a class="menu" href="/report">📊 รายงาน On Time</a>
  <a class="menu on" href="/ready">🚦 รถ/คนพร้อมใช้</a>
  <a class="menu" href="/users">👥 ผู้ใช้</a>
  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>
</aside>
<header><div class="hd">
  <div class="ttl"><h1>รถ/คนพร้อมใช้งาน PTGLG</h1><p id="stamp">สถานะจากชีตข้อมูลรถ+พขร. · งานจากชีตแผนงาน · อ่านอย่างเดียว</p></div>
  <span class="grow"></span>
  <div class="ctl">
  <div class="seg" id="presets"><button data-a="-1" data-b="-1">เมื่อวาน</button><button data-a="0" data-b="0">วันนี้</button><button data-a="1" data-b="1">พรุ่งนี้</button><button data-a="-6" data-b="0">7 วัน</button><button data-a="-29" data-b="0">30 วัน</button></div>
  <div class="rng"><input type="date" id="dFrom" aria-label="ตั้งแต่วันที่"><span class="dash">–</span><input type="date" id="dTo" aria-label="ถึงวันที่"></div>
  <label class="tgt">เป้า <input type="number" id="tg" min="0" max="20" step="0.5" aria-label="เป้าเที่ยวต่อคันต่อวัน"> เที่ยว/คัน</label>
  <button class="btn" id="go">ดูรายงาน</button>
  <button class="btn2" id="refresh" title="อ่านข้อมูลจากชีตใหม่ทันที ไม่รอรอบ 30 นาที">🔄 รีเฟรช</button>
  <button class="btn2" id="snap" title="บันทึกหน้านี้เป็นรูป เพื่อส่งต่อทาง LINE / อีเมล">📷 แคปส่ง</button>
  </div>
</div></header>
<main id="main">
  <div id="err" class="err" hidden></div>
  <div id="notes" class="note" hidden data-nosnap="1"></div>
  <div class="kpis" id="kpis"></div>
  <div class="panels">
    <section class="panel c7"><div class="ph"><h3>สถานะรถรายวัน</h3><span class="s2" id="trSub"></span><div class="legend" id="trLeg"></div></div>
      <p class="desc" id="trDesc">จำนวนรถแต่ละสถานะรายวัน · ชี้ที่แท่งเพื่อดูตัวเลข · กดแท่งเพื่อดูวันนั้น</p>
      <div class="chart" id="cTrend"></div></section>
    <section class="panel c5"><div class="ph"><h3>เที่ยวต่อวัน เทียบเป้า</h3><div class="legend"><span><i class="key" style="background:var(--trip)"></i>เที่ยว</span><span><i class="key" style="background:var(--goal);height:2px;width:14px;border-radius:0"></i>เป้า</span></div></div>
      <p class="desc">นับเที่ยวจาก “เลข JOB” ในแผนงาน (หลาย drop ในเที่ยวเดียวกัน = 1 เที่ยว) · เป้า = เป้าเที่ยวต่อคัน × รถพร้อมใช้</p>
      <div class="chart" id="cTrips"></div></section>
    <section class="panel c6"><div class="ph"><h3>แยกตามพื้นที่ประจำรถ</h3></div>
      <p class="desc">ความยาวแท่ง = จำนวนรถของพื้นที่ · ตัวเลขขวา = เที่ยวที่วิ่ง</p><div id="cArea"></div></section>
    <section class="panel c6"><div class="ph"><h3>แยกตามประเภทรถ</h3></div>
      <p class="desc">ดูว่ารถขนาดไหนยังว่าง รับงานเพิ่มได้</p><div id="cType"></div></section>
    <section class="panel c6"><div class="ph"><h3>รถไม่พร้อมใช้</h3><span class="s2" id="downSub"></span></div>
      <p class="desc">แยกตามรหัสที่ลงในชีตของวันนั้น</p><div id="cDown"></div></section>
    <section class="panel c6"><div class="ph"><h3>พนักงานขับรถ</h3><span class="s2" id="pplSub"></span></div>
      <p class="desc">มีงาน = มีชื่อในแผนงานของวันนั้น · ไม่พร้อม = ลา / หยุด / อบรม ฯลฯ ตามชีต</p><div id="cPpl"></div></section>
    <section class="panel c12" id="carsP" data-nosnap="1"><div class="tools"><div class="ph" style="margin:0"><h3>รายคัน</h3><span class="s2" id="rowSub"></span></div>
      <div class="chips" id="carChips"></div>
      <span class="grow"></span><input type="search" id="q" placeholder="ค้นหา เบอร์รถ / ทะเบียน / สถานะ" style="min-width:240px"></div>
      <div class="tw"><table><thead><tr><th>เบอร์รถ</th><th>พื้นที่</th><th>ประเภท</th><th class="m-hide">ทะเบียน</th><th>สถานะ</th><th>เหตุผล</th><th class="n">เที่ยว</th><th class="n">Drop</th></tr></thead>
        <tbody id="rows"></tbody></table></div></section>
    <section class="panel c12" id="pplP" data-nosnap="1"><div class="tools"><div class="ph" style="margin:0"><h3>รายชื่อ พขร.</h3><span class="s2" id="pSub"></span></div>
      <div class="chips" id="pplChips"></div></div>
      <div class="tw" style="max-height:360px"><table><thead><tr><th>ชื่อ-สกุล</th><th>สถานะ</th><th>เหตุผล</th><th class="n">เที่ยว</th></tr></thead>
        <tbody id="prows"></tbody></table></div></section>
  </div>
</main>
<div id="tip" hidden></div>
<script>
// สีตามสถานะ + สีตัวอักษรที่อ่านออกบนสีนั้น (เขียว/เหลือง → ตัวดำ · ฟ้า/แดง → ตัวขาว)
const K = {run: {t: 'วิ่งงาน', c: 'var(--run)', ink: '#0b0b0b'}, free: {t: 'ว่างงาน', c: 'var(--free)', ink: '#fff'},
           nodriver: {t: 'ไม่มีคนขับ', c: 'var(--nod)', ink: '#0b0b0b'}, down: {t: 'ไม่พร้อมใช้', c: 'var(--down)', ink: '#fff'}};
const PK = {run: {t: 'มีงาน', c: 'var(--run)', ink: '#0b0b0b'}, free: {t: 'ว่าง', c: 'var(--free)', ink: '#fff'}, down: {t: 'ไม่พร้อม', c: 'var(--down)', ink: '#fff'}};
K.idle = {t: 'ว่างงาน', c: 'var(--free)', ink: '#fff'};          // ในแท่งพื้นที่/ประเภทรถ: ว่างงาน + ไม่มีคนขับ รวมกัน
const ORDER = ['run', 'free', 'nodriver', 'down'];
// ตัวกรองตารางที่มาจากการกดกราฟ: c = รายคัน · p = รายชื่อ พขร.
let FC = {}, FP = {};
const FNAME = {kind: 'สถานะ', area: 'พื้นที่', vtype: 'ประเภท', why: 'เหตุผล'};
function fattr(o){ return o ? ' data-f="' + esc(JSON.stringify(o)) + '"' : ''; }
function kindOk(f, k){ return !f.kind || f.kind === k || (f.kind === 'idle' && (k === 'free' || k === 'nodriver')); }
function chips(f, map, id){
  const ks = Object.keys(f);
  document.getElementById(id).innerHTML = ks.map(k => '<button class="chip" data-clr="' + id + '|' + k + '">' + FNAME[k] + ': ' +
    esc(k === 'kind' ? map[f[k]].t : f[k]) + ' ✕</button>').join('') + (ks.length ? '<button class="chip clr" data-clr="' + id + '|*">ล้าง</button>' : '');
}
const DOW = ['อา', 'จ', 'อ', 'พ', 'พฤ', 'ศ', 'ส'];
const MON = ['ม.ค.', 'ก.พ.', 'มี.ค.', 'เม.ย.', 'พ.ค.', 'มิ.ย.', 'ก.ค.', 'ส.ค.', 'ก.ย.', 'ต.ค.', 'พ.ย.', 'ธ.ค.'];
let REP = null;
function esc(s){ return String(s == null ? '' : s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c])); }
function iso(d){ return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'); }
function n(v){ return v == null ? '–' : (Math.round(Number(v) * 10) / 10).toLocaleString('en-US'); }
let MULTI = false;                                   // เลือกหลายวัน: รถ/คน = เฉลี่ยต่อวัน · เที่ยว = รวมทั้งช่วง
function rangeText(){ return REP.from === REP.to ? thaiDate(REP.from) : thaiDate(REP.from) + ' – ' + thaiDate(REP.to); }
function shift(k){ const t = new Date(); t.setDate(t.getDate() + k); return iso(t); }
function pct(a, b){ return b ? Math.round(a * 100 / b) + '%' : '–'; }
function dt(s){ return new Date(s + 'T00:00:00'); }
function thaiDate(s){ const d = dt(s); return DOW[d.getDay()] + ' ' + d.getDate() + ' ' + MON[d.getMonth()]; }
function key(c){ return '<i class="key" style="background:' + c + '"></i>'; }
// ข้อความ tooltip: หัว + แถว [สี, ชื่อ, ค่า]
function tipHtml(title, rows){
  return '<div class="t">' + esc(title) + '</div>' + rows.map(r => '<div class="r"><span>' + (r[0] ? key(r[0]) : '') + esc(r[1]) + '</span><b>' + esc(r[2]) + '</b></div>').join('');
}
// แท่งต่อกัน: กว้างตาม flex-grow (= จำนวน) ช่องว่าง 2px · ตัวเลขในช่วงแสดงเฉพาะเมื่อพอดี (fitLabels วัดให้)
// fb = ตัวกรองพื้นฐานของแท่งนี้ (เช่น {t:'c', area:'บางปะกง'}) — กดช่วงไหนก็กรองตารางตามสถานะของช่วงนั้นเพิ่ม
function stack(segs, map, total, title, tall, fb){
  const live = segs.filter(s => s[1] > 0);
  if(!live.length) return '<div class="stk' + (tall ? ' tall' : '') + '" style="background:var(--track)"></div>';
  const tip = esc(tipHtml(title, live.map(s => [map[s[0]].c, map[s[0]].t, n(s[1]) + ' (' + pct(s[1], total) + ')']).concat(fb ? [['', 'กดเพื่อดูรายการ', '']] : [])));
  return '<div class="stk' + (tall ? ' tall' : '') + '">' + live.map(s =>
    '<span class="sg" style="flex:' + s[1] + ' 1 0;background:' + map[s[0]].c + ';color:' + map[s[0]].ink + '" data-tip="' + tip + '"' +
    fattr(fb && Object.assign({}, fb, {kind: s[0]})) + '><b>' + n(s[1]) + '</b></span>').join('') + '</div>';
}
function legend(segs, map, total, fb){
  return '<div class="legend">' + segs.map(s => '<span' + fattr(fb && s[1] && Object.assign({}, fb, {kind: s[0]})) + '>' + key(map[s[0]].c) + map[s[0]].t +
    ' <b>' + n(s[1]) + '</b><em>' + pct(s[1], total) + '</em></span>').join('') + '</div>';
}
function fitLabels(){
  document.querySelectorAll('.sg b').forEach(b => { b.style.visibility = (b.scrollWidth + 6 <= b.parentElement.clientWidth) ? 'visible' : 'hidden'; });
}
// แกน y ตัวเลขกลมๆ (0 / 20 / 40 / 60) ไม่เกิน 5 เส้น
function scale(max){
  const raw = Math.max(max, 1) / 4, p = Math.pow(10, Math.floor(Math.log10(raw)));
  const st = Math.max(1, [1, 2, 2.5, 5, 10].map(m => m * p).find(s => s >= raw));
  return {top: Math.ceil(Math.max(max, 1) / st) * st, st};
}
function topRounded(x, y, w, h, r){
  if(h <= 0) return '';
  r = Math.min(r, h, w / 2);
  return 'M' + x + ',' + (y + h) + 'V' + (y + r) + 'Q' + x + ',' + y + ' ' + (x + r) + ',' + y + 'H' + (x + w - r) + 'Q' + (x + w) + ',' + y + ' ' + (x + w) + ',' + (y + r) + 'V' + (y + h) + 'Z';
}
// กราฟแท่งแนวตั้งรายวัน — stacks = [[key, สี], ...] จากล่างขึ้นบน · goal = เส้นเป้าสั้นๆ บนแต่ละแท่ง
function columns(el, days, stacks, opt){
  const W = Math.max(el.clientWidth, 280), H = 230, L = 34, R = 6, T = 14, B = 40;
  const pw = W - L - R, ph = H - T - B, slot = pw / days.length, bw = Math.min(24, slot * 0.62);
  const max = Math.max(...days.map(d => Math.max(stacks.reduce((a, s) => a + (d[s[0]] || 0), 0), opt.goal ? d.goal || 0 : 0)));
  const sc = scale(max), y = v => T + ph - v / sc.top * ph;
  let g = '';
  for(let v = 0; v <= sc.top + 1e-9; v += sc.st){
    g += '<line class="gl" x1="' + L + '" x2="' + (W - R) + '" y1="' + y(v) + '" y2="' + y(v) + '"/>' +
         '<text class="ax" x="' + (L - 6) + '" y="' + (y(v) + 4) + '" text-anchor="end">' + n(v) + '</text>';
  }
  days.forEach((d, i) => {
    const cx = L + slot * i + slot / 2, x0 = cx - bw / 2, sel = d.date >= REP.from && d.date <= REP.to;
    const lstep = Math.max(1, Math.ceil(24 / slot)), showx = i % lstep === 0 || i === days.length - 1;
    let base = T + ph, live = stacks.filter(s => (d[s[0]] || 0) > 0), tot = 0;
    live.forEach((s, j) => {
      const h = d[s[0]] / sc.top * ph, gap = j ? 2 : 0, top = base - h;
      tot += d[s[0]];
      g += j === live.length - 1
        ? '<path d="' + topRounded(x0, top + gap, bw, h - gap, 4) + '" fill="' + s[1] + '"/>'
        : '<rect x="' + x0 + '" y="' + (top + gap) + '" width="' + bw + '" height="' + Math.max(0, h - gap) + '" fill="' + s[1] + '"/>';
      base = top;
    });
    if(opt.goal && d.goal) g += '<line x1="' + (x0 - 4) + '" x2="' + (x0 + bw + 4) + '" y1="' + y(d.goal) + '" y2="' + y(d.goal) + '" stroke="var(--goal)" stroke-width="2" stroke-linecap="round"/>';
    if(sel && opt.label && !MULTI) g += '<text class="vl" x="' + cx + '" y="' + (Math.min(base, opt.goal && d.goal ? y(d.goal) : base) - 6) + '" text-anchor="middle">' + n(tot) + '</text>';
    const dd = dt(d.date);
    if(showx) g += '<text class="ax' + (sel ? ' sel' : '') + '" x="' + cx + '" y="' + (H - B + 16) + '" text-anchor="middle">' + dd.getDate() + '</text>' +
         '<text class="ax' + (sel ? ' sel' : '') + '" x="' + cx + '" y="' + (H - B + 30) + '" text-anchor="middle">' + DOW[dd.getDay()] + '</text>';
    if(sel){ const mw = Math.min(22, slot - 2); g += '<rect x="' + (cx - mw / 2) + '" y="' + (H - 3) + '" width="' + mw + '" height="3" rx="1.5" fill="var(--acc)"/>'; }
    g += '<rect class="hit" x="' + (L + slot * i) + '" y="' + T + '" width="' + slot + '" height="' + (ph + B - 4) + '" rx="6" data-date="' + d.date + '" data-tip="' + esc(opt.tip(d)) + '"/>';
  });
  el.innerHTML = '<svg width="' + W + '" height="' + H + '" viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' + esc(opt.aria) + '">' + g + '</svg>';
}
// แถวแท่งต่อกันแนวนอน (พื้นที่ / ประเภทรถ) ความยาวเทียบกับแถวที่มีรถมากสุด
function rowsChart(items, nameKey){
  if(!items.length) return '<div class="empty">ไม่มีข้อมูล</div>';
  const mx = Math.max(...items.map(i => i.total));
  return '<div class="rows">' + items.map(i => {
    const segs = [['run', i.run], ['idle', i.free], ['down', i.down]], fb = {t: 'c'};
    fb[nameKey] = i[nameKey];
    return '<div class="rw"><div class="rn"' + fattr(fb) + '>' + esc(i[nameKey]) + '<small>รถ ' + i.total + ' คัน</small></div>' +
      '<div><div style="width:' + (i.total / mx * 100) + '%">' + stack(segs, K, i.total, i[nameKey] + ' · รถ ' + i.total + ' คัน', true, fb) + '</div></div>' +
      '<div class="rv"' + fattr(fb) + '><b>' + n(i.trips) + '</b> เที่ยว</div></div>';
  }).join('') + '</div>';
}
function bars(items, total, unit, fb){
  if(!items.length) return '<div class="empty">ไม่มี — พร้อมครบทุก' + unit + '</div>';
  const mx = Math.max(...items.map(i => i.n));
  return '<div class="rows">' + items.map(i => {
    const f = fattr(Object.assign({}, fb, {kind: 'down', why: i.name}));
    return '<div class="rw"' + f + '><div class="rn" title="' + esc(i.name) + '">' + esc(i.name) + '</div>' +
    '<div><div class="bar" style="width:' + (i.n / mx * 100) + '%" data-tip="' + esc(tipHtml(i.name, [['var(--down)', 'จำนวน', i.n + ' ' + unit + ' (' + pct(i.n, total) + ' ของทั้งหมด)'], ['', 'กดเพื่อดูรายชื่อ', '']])) + '"></div></div>' +
    '<div class="rv"><b>' + i.n + '</b> ' + unit + '</div></div>';
  }).join('') + '</div>';
}
function render(){
  const r = REP, c = r.cars, t = r.trips, p = r.people;
  const segs = ORDER.map(k => [k, c[k]]);
  const goalLine = t.goal ? Math.min(100, t.goal / Math.max(t.goal, t.total) * 100) : 0;
  const fill = t.goal ? t.total / Math.max(t.goal, t.total) * 100 : 100;
  const top = c.down_by[0], avg = MULTI ? ' · เฉลี่ยต่อวัน' : '', cu = MULTI ? 'คัน·วัน' : 'คัน';
  const ps = [['run', p.run], ['free', p.free], ['down', p.down]];
  document.getElementById('kpis').innerHTML =
    '<div class="card k4"><div class="lab">รถพร้อมใช้งาน · ' + esc(rangeText()) + avg + '</div>' +
      '<div class="big">' + n(c.ready) + '<small>จาก ' + n(c.total) + ' คัน · ' + pct(c.ready, c.total) + '</small></div>' +
      '<div style="margin-top:14px">' + stack(segs, K, c.total, 'รถทั้งหมด ' + c.total + ' คัน', true, {t: 'c'}) + '</div>' + legend(segs, K, c.total, {t: 'c'}) + '</div>' +
    '<div class="card k4"><div class="lab">พขร. พร้อมทำงาน' + avg + '</div>' +
      '<div class="big">' + n(p.run + p.free) + '<small>จาก ' + n(p.total) + ' คน · ' + pct(p.run + p.free, p.total) + '</small></div>' +
      '<div style="margin-top:14px">' + stack(ps, PK, p.total, 'พขร. ทั้งหมด ' + p.total + ' คน', true, {t: 'p'}) + '</div>' + legend(ps, PK, p.total, {t: 'p'}) + '</div>' +
    '<div class="card k4"><div class="lab">เที่ยววิ่งงาน' + (MULTI ? ' · รวม ' + r.days + ' วัน' : '') + '</div>' +
      '<div class="big">' + n(t.total) + '<small>' + (t.goal ? 'จากเป้า ' + n(t.goal) + ' เที่ยว' : 'เที่ยว') + '</small></div>' +
      '<div class="meter"><i style="width:' + fill + '%"></i>' + (t.goal ? '<u style="left:calc(' + goalLine + '% - 1px)"></u>' : '') + '</div>' +
      '<div class="sub">' + (t.goal ? (t.gap ? 'ขาดอีก <b>' + n(t.gap) + '</b> เที่ยวถึงเป้า (' + r.target + ' เที่ยว/คัน)' : '<span class="ok">✓ ถึงเป้าแล้ว</span> เกินเป้า ' + n(t.total - t.goal) + ' เที่ยว') : 'ยังไม่ได้ตั้งเป้า') +
        ' · <b>' + n(t.drops) + '</b> drop · เฉลี่ย <b>' + (t.per_ready == null ? '–' : t.per_ready) + '</b> เที่ยว/คันพร้อมใช้' + (MULTI ? '/วัน' : '') + ' · <b>' + (t.per_run == null ? '–' : t.per_run) + '</b> เที่ยว/คันที่วิ่ง' + (MULTI ? '/วัน' : '') +
        (t.cancelled ? ' · ยกเลิก ' + t.cancelled + ' งาน' : '') + '</div></div>' +
    '<div class="card k3"' + fattr({t: 'c', kind: 'run'}) + '><div class="lab">' + key(K.run.c) + 'วิ่งงาน</div><div class="val">' + n(c.run) + '<small>คัน</small></div>' +
      '<div class="sub">ใช้รถ <b>' + pct(c.run, c.ready) + '</b> ของรถพร้อมใช้</div></div>' +
    '<div class="card k3"' + fattr({t: 'c', kind: 'free'}) + '><div class="lab">' + key(K.free.c) + 'ว่างงาน</div><div class="val">' + n(c.free) + '<small>คัน</small></div>' +
      '<div class="sub">พร้อมใช้ แต่ยังไม่มีงานในแผน</div></div>' +
    '<div class="card k3"' + fattr({t: 'c', kind: 'nodriver'}) + '><div class="lab">' + key(K.nodriver.c) + 'ไม่มีคนขับ</div><div class="val">' + n(c.nodriver) + '<small>คัน</small></div>' +
      '<div class="sub">รถพร้อม · พขร. ว่าง <b>' + n(p.free) + '</b> คน</div></div>' +
    '<div class="card k3"' + fattr({t: 'c', kind: 'down'}) + '><div class="lab">' + key(K.down.c) + 'ไม่พร้อมใช้</div><div class="val">' + n(c.down) + '<small>คัน</small></div>' +
      '<div class="sub">' + (top ? 'มากสุด: <b>' + esc(top.name) + '</b> ' + top.n + ' ' + cu : 'ไม่มีรถเสีย/ซ่อม') + '</div></div>';

  const tr = r.trend || [];
  document.getElementById('trLeg').innerHTML = ORDER.map(k => '<span>' + key(K[k].c) + K[k].t + '</span>').join('');
  document.getElementById('trSub').textContent = tr.length ? thaiDate(tr[0].date) + ' – ' + thaiDate(tr[tr.length - 1].date) : '';
  document.getElementById('trDesc').textContent = 'จำนวนรถแต่ละสถานะรายวัน ' + tr.length + ' วัน' + (MULTI ? ' (ช่วงที่เลือก)' : ' (ย้อนหลังถึงวันที่เลือก)') + ' · ชี้ที่แท่งเพื่อดูตัวเลข · กดแท่งเพื่อดูวันนั้น';
  columns(document.getElementById('cTrend'), tr, ORDER.map(k => [k, K[k].c]), {aria: 'สถานะรถรายวัน', label: false,
    tip: d => tipHtml(thaiDate(d.date), ORDER.map(k => [K[k].c, K[k].t, d[k] + ' คัน']).concat([['', 'พขร. ไม่พร้อม', d.p_down + ' คน']]))});
  columns(document.getElementById('cTrips'), tr, [['trips', 'var(--trip)']], {aria: 'เที่ยวต่อวันเทียบเป้า', goal: true, label: true,
    tip: d => tipHtml(thaiDate(d.date), [['var(--trip)', 'เที่ยว', n(d.trips)], ['var(--goal)', 'เป้า', d.goal ? n(d.goal) : '–'],
      ['', d.goal ? (d.trips >= d.goal ? 'ถึงเป้า' : 'ขาด') : '', d.goal ? (d.trips >= d.goal ? '✓' : n(d.goal - d.trips)) : '']])});

  document.getElementById('cArea').innerHTML = rowsChart(r.by_area, 'area');
  document.getElementById('cType').innerHTML = rowsChart(r.by_type, 'vtype');
  document.getElementById('cDown').innerHTML = bars(c.down_by, c.total * (r.days || 1), cu, {t: 'c'});
  document.getElementById('downSub').textContent = c.down ? (MULTI ? 'เฉลี่ย ' + n(c.down) + ' คัน/วัน' : 'รวม ' + c.down + ' คัน') + ' จาก ' + c.total : '';
  document.getElementById('cPpl').innerHTML = (p.total ? stack(ps, PK, p.total, 'พขร. ทั้งหมด ' + p.total + ' คน', true, {t: 'p'}) + legend(ps, PK, p.total, {t: 'p'}) : '<div class="empty">ไม่มีข้อมูล พขร.</div>') +
    (p.down_by.length ? '<div class="divider"></div>' + bars(p.down_by, p.total * (r.days || 1), MULTI ? 'คน·วัน' : 'คน', {t: 'p'}) : '');
  document.getElementById('pplSub').textContent = p.total ? 'ทั้งหมด ' + p.total + ' คน · พร้อมทำงาน ' + n(p.run + p.free) + (MULTI ? ' (เฉลี่ย/วัน)' : '') : '';
  drawRows();
  drawPeople();
  const nt = document.getElementById('notes');
  nt.innerHTML = r.notes.length ? '<b>หมายเหตุจากการอ่านชีต' + (r.notes_date ? ' · วันที่ ' + esc(thaiDate(r.notes_date)) + ' (วันสุดท้ายในช่วง — เลือกทีละวันเพื่อดูวันอื่น)' : '') + '</b><ul>' + r.notes.map(x => '<li>' + esc(x) + '</li>').join('') + '</ul>' : '';
  nt.hidden = !r.notes.length;
  fitLabels();
}
function days(x){ return MULTI ? '<span class="code">วิ่ง ' + x.d_run + ' · ว่าง ' + x.d_free + ' · ไม่พร้อม ' + x.d_down + ' วัน</span>' : ''; }
function drawPeople(){
  const list = REP.people_rows.filter(x => kindOk(FP, x.kind) && (!FP.why || x.why === FP.why));
  chips(FP, PK, 'pplChips');
  document.getElementById('pSub').textContent = list.length + ' คน' + (Object.keys(FP).length ? ' (จาก ' + REP.people_rows.length + ')' : '');
  document.getElementById('prows').innerHTML = list.map(x =>
    '<tr><td>' + esc(x.name) + '</td><td><span class="st"><i style="background:' + PK[x.kind].c + '"></i>' + PK[x.kind].t + '</span>' + days(x) + '</td><td>' + esc(x.why) + '</td><td class="n">' + (x.trips || '–') + '</td></tr>').join('')
    || '<tr><td colspan="4" class="empty">ไม่มี พขร. ที่ตรงกับตัวกรอง</td></tr>';
}
function drawRows(){
  const q = document.getElementById('q').value.trim().toLowerCase();
  const list = REP.rows.filter(x => kindOk(FC, x.kind) && (!FC.area || (x.area || 'ไม่ระบุ') === FC.area) &&
    (!FC.vtype || (x.vtype || 'ไม่ระบุ') === FC.vtype) && (!FC.why || x.why === FC.why) &&
    (!q || (x.car + ' ' + x.plate + ' ' + x.why + ' ' + K[x.kind].t + ' ' + x.area + ' ' + x.vtype).toLowerCase().includes(q)));
  chips(FC, K, 'carChips');
  document.getElementById('rowSub').textContent = list.length + ' คัน' + (q || Object.keys(FC).length ? ' (จาก ' + REP.rows.length + ')' : '');
  document.getElementById('rows').innerHTML = list.map(x =>
    '<tr><td><b>' + esc(x.car) + '</b></td><td>' + esc(x.area) + '</td><td>' + esc(x.vtype) + '</td><td class="m-hide">' + esc(x.plate) + '</td>' +
    '<td><span class="st"><i style="background:' + K[x.kind].c + '"></i>' + K[x.kind].t + '</span>' + days(x) + '</td><td>' + esc(x.why) + (x.why && x.code ? '<span class="code">' + esc(x.code) + '</span>' : '') + '</td>' +
    '<td class="n">' + (x.trips || '–') + '</td><td class="n">' + (x.drops || '–') + '</td></tr>').join('') || '<tr><td colspan="8" class="empty">ไม่พบรถที่ตรงกับคำค้น</td></tr>';
}
function markPreset(){
  const f = document.getElementById('dFrom').value, t = document.getElementById('dTo').value;
  document.querySelectorAll('#presets button').forEach(b => b.classList.toggle('on', shift(+b.dataset.a) === f && shift(+b.dataset.b) === t));
}
function setRange(f, t){ document.getElementById('dFrom').value = f; document.getElementById('dTo').value = t; markPreset(); }
async function load(keep, fresh){
  const main = document.getElementById('main'), err = document.getElementById('err');
  err.hidden = true; main.classList.add('busy');
  const tg = document.getElementById('tg').value;
  try{ localStorage.setItem('readyTarget', tg); }catch(e){}
  try{
    const res = await fetch('/api/report/ready?from=' + document.getElementById('dFrom').value + '&to=' + document.getElementById('dTo').value + '&target=' + encodeURIComponent(tg) + (fresh === true ? '&fresh=1' : ''));
    if(res.status === 401){ location.href = '/login'; return; }
    if(!res.ok){ let m = 'HTTP ' + res.status; try{ m = (await res.json()).detail || m; }catch(e){} throw new Error(m); }
    REP = await res.json();
    MULTI = (REP.days || 1) > 1;
    if(keep !== true){ FC = {}; FP = {}; }
    markPreset();
    render();
    document.getElementById('stamp').textContent = 'สถานะจากชีตข้อมูลรถ+พขร. · งานจากชีตแผนงาน · อัปเดต ' + arT(new Date()) + arStamp();
  }catch(e){ err.textContent = 'โหลดไม่สำเร็จ: ' + e.message; err.hidden = false; }
  finally{ main.classList.remove('busy'); }
}
// tooltip เดียวใช้ทั้งหน้า: อะไรที่มี data-tip ชี้แล้วขึ้น
const tip = document.getElementById('tip');
document.addEventListener('mousemove', e => {
  const el = e.target.closest && e.target.closest('[data-tip]');
  if(!el){ tip.hidden = true; return; }
  if(tip.dataset.src !== el.dataset.tip){ tip.innerHTML = el.dataset.tip; tip.dataset.src = el.dataset.tip; }
  tip.hidden = false;
  const w = tip.offsetWidth, h = tip.offsetHeight;
  tip.style.left = Math.min(e.clientX + 14, innerWidth - w - 8) + 'px';
  tip.style.top = (e.clientY + 16 + h > innerHeight ? e.clientY - h - 12 : e.clientY + 16) + 'px';
});
document.addEventListener('click', e => {
  const el = e.target.closest && e.target.closest('.hit[data-date]');
  if(el){ setRange(el.dataset.date, el.dataset.date); load(); return; }
  const cl = e.target.closest && e.target.closest('[data-clr]');
  if(cl){                                                   // ปุ่ม ✕ บนชิปตัวกรอง
    const [id, k] = cl.dataset.clr.split('|'), f = id === 'carChips' ? FC : FP;
    if(k === '*') Object.keys(f).forEach(x => delete f[x]); else delete f[k];
    id === 'carChips' ? drawRows() : drawPeople();
    return;
  }
  const fe = e.target.closest && e.target.closest('[data-f]');
  if(!fe || !REP) return;
  const f = JSON.parse(fe.dataset.f), t = f.t;            // กดกราฟ → กรองตารางนั้นใหม่ทั้งชุด แล้วเลื่อนลงไปให้เห็น
  delete f.t;
  if(t === 'p'){ FP = f; drawPeople(); } else { FC = f; document.getElementById('q').value = ''; drawRows(); }
  const sec = document.getElementById(t === 'p' ? 'pplP' : 'carsP');
  tip.hidden = true;
  sec.scrollIntoView({behavior: 'smooth', block: 'start'});
  sec.classList.remove('flash'); void sec.offsetWidth; sec.classList.add('flash');
});
// แคปส่ง: ถ่ายส่วนกราฟเป็นรูป (ไม่รวมหมายเหตุ/ตารางยาว) — มือถือเปิดเมนูแชร์, คอมดาวน์โหลดไฟล์
let H2I = null;
function loadH2I(){
  if(window.htmlToImage) return Promise.resolve(window.htmlToImage);
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
  b.disabled = true; b.textContent = '⏳ กำลังแคป…'; tip.hidden = true;
  const cap = document.createElement('div'); cap.className = 'snapcap';
  const day = rangeText() + ' ' + (dt(REP.to).getFullYear() + 543);
  cap.innerHTML = '<b>รถ/คนพร้อมใช้งาน PTGLG · ' + esc(day) + '</b><span>เป้า ' + esc(REP.target) + ' เที่ยว/คัน · แคปเมื่อ ' +
    new Date().toLocaleString('th-TH', {dateStyle: 'short', timeStyle: 'short'}) + '</span>';
  main.insertBefore(cap, main.firstChild);
  const hide = [...main.querySelectorAll('[data-nosnap]')].filter(e => !e.hidden);   // ซ่อนจริงระหว่างแคป ไม่งั้นรูปมีที่ว่างเท่าความสูงตาราง
  hide.forEach(e => e.hidden = true);
  try{
    const lib = await loadH2I();
    let fontCss = '';
    try{ fontCss = await lib.getFontEmbedCSS(main); }catch(e){}                       // ฝังฟอนต์ไทย ตัวหนังสือในรูปจะได้กว้างเท่าบนจอ
    const blob = await lib.toBlob(main, {pixelRatio: 2, backgroundColor: getComputedStyle(document.body).backgroundColor,
      fontEmbedCSS: fontCss || undefined, skipFonts: !fontCss});
    const name = 'PTGLG_ready_' + REP.from + (REP.to !== REP.from ? '_' + REP.to : '') + '.png';
    const file = new File([blob], name, {type: 'image/png'});
    if(navigator.canShare && navigator.canShare({files: [file]}) && matchMedia('(pointer:coarse)').matches){
      try{ await navigator.share({files: [file], title: 'รถ/คนพร้อมใช้งาน PTGLG ' + day}); }catch(e){}
    }else{
      const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name;
      document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1500);
    }
  }catch(e){
    alert('แคปไม่สำเร็จ: ' + (e && e.message ? e.message : e) + ' — ลองใหม่อีกครั้ง หรือใช้ปุ่มแคปหน้าจอของเครื่องแทน');
  }finally{
    cap.remove(); hide.forEach(e => e.hidden = false); b.disabled = false; b.textContent = '📷 แคปส่ง';
  }
};
let rz = 0;
addEventListener('resize', () => { clearTimeout(rz); rz = setTimeout(() => { if(REP) render(); }, 150); });
setRange(iso(new Date()), iso(new Date()));
let saved = ''; try{ saved = localStorage.getItem('readyTarget') || ''; }catch(e){}
document.getElementById('tg').value = saved || '2';
document.getElementById('go').onclick = load;
document.getElementById('q').oninput = () => { if(REP) drawRows(); };
['dFrom', 'dTo'].forEach(id => { document.getElementById(id).onchange = () => { markPreset(); load(); }; });
document.getElementById('tg').onchange = load;
document.querySelectorAll('#presets button').forEach(b => b.onclick = () => { setRange(shift(+b.dataset.a), shift(+b.dataset.b)); load(); });
// ── รีเฟรชอัตโนมัติทุก 30 นาที: เปิดทิ้งไว้ก็ได้ข้อมูลใหม่เอง (ตัวกรอง/ช่วงวันที่ที่เลือกยังอยู่) ──
// แท็บที่ซ่อนอยู่ไม่โหลด (ประหยัดโควตาชีต) กลับมาที่แท็บแล้วถ้าเลยเวลา โหลดทันที
const AR_MIN = 30;
let AR_NEXT = Date.now() + AR_MIN * 60000;
function arT(d){ return d.toLocaleTimeString('th-TH', {hour: '2-digit', minute: '2-digit'}); }
function arStamp(){ AR_NEXT = Date.now() + AR_MIN * 60000; return ' · 🔄 รีเฟรชอัตโนมัติทุก ' + AR_MIN + ' นาที (ครั้งถัดไป ' + arT(new Date(AR_NEXT)) + ')'; }
function arTick(){
  const busy = document.getElementById('main').classList.contains('busy') || document.getElementById('snap').disabled;
  if(Date.now() >= AR_NEXT && !document.hidden && !busy) load(true);
}
setInterval(arTick, 30000);
document.addEventListener('visibilitychange', () => { if(!document.hidden) arTick(); });
document.getElementById('refresh').onclick = async () => {        // อยากได้เร็ว: อ่านชีตสดทันที
  const b = document.getElementById('refresh');
  b.disabled = true; b.textContent = '⏳ กำลังอ่านชีต…';
  try{ await load(true, true); } finally{ b.disabled = false; b.textContent = '🔄 รีเฟรช'; }
};
markPreset(); load();
</script>
</body>
</html>"""


PLAN_HTML = """<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>แผนงาน — Gasbulk Track PTGLG</title>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet" crossorigin="anonymous">
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
  /* แผงรถซ้ายของตาราง: ว่าง / จัดแล้ว — ลากชื่อรถไปวางบนแถว = ใส่เบอร์รถ */
  .tblrow{display:flex;gap:12px;align-items:flex-start}
  .tblrow > .wrap{flex:1;min-width:0}
  .carbar{flex:0 0 210px;max-height:calc(100vh - 250px);overflow:auto;padding:10px 10px 12px;border:1px solid var(--line);border-radius:12px;background:var(--card);font-size:14px;position:sticky;top:8px}
  .carbar .hd2{font-weight:700;font-size:15px;margin-bottom:4px}
  .carbar .sum2{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:6px}
  .carbar .on{color:#1d4ed8}.carbar .free{color:#15803d}
  .carbar .tipd{font-size:12px;color:var(--mut);margin:0 0 8px;line-height:1.4}
  .carbar h4{margin:10px 0 6px;font-size:13px;color:var(--mut)}
  .carbar .g2{display:grid;grid-template-columns:1fr 1fr;gap:5px}
  .carbar .g2 .cp{margin:0;justify-content:center}
  .carbar .cp{display:flex;justify-content:space-between;gap:6px;align-items:center;font-size:14px;padding:5px 8px;margin-bottom:5px;border-radius:8px;border:1px solid var(--line);cursor:grab;user-select:none}
  .carbar .cp:active{cursor:grabbing}
  .carbar .cp.f{background:#ecfdf5;border-color:#a7f3d0;color:#166534}
  .carbar .cp.u{background:#eff6ff;border-color:#bfdbfe;color:#1e3a8a}
  .carbar .cp small{font-size:11.5px;opacity:.8;white-space:nowrap}
  .carbar .cp.sel{outline:2px solid #2563eb}
  tr.dropok td{background:#dbeafe !important}
  @media (max-width:820px){ .tblrow{flex-direction:column} .carbar{position:static;flex:none;width:100%;max-height:220px} }
  .imp-back{position:fixed;inset:0;background:rgba(15,23,42,.5);z-index:60;display:flex;
            align-items:flex-start;justify-content:center;padding:12px 10px;overflow:auto}
  .imp-back[hidden]{display:none}
  .imp{background:var(--card);border:1px solid var(--line);border-radius:14px;width:100%;
       max-width:min(1900px, 98vw);padding:18px 20px}
  .imp-h{display:flex;justify-content:space-between;align-items:center;margin-bottom:8px}
  .imp-wait{border-left:4px solid #2563eb}
  .imp-wait .ibar{height:4px;border-radius:2px;background:rgba(37,99,235,.18);overflow:hidden;margin-top:8px}
  .imp-wait .ibar i{display:block;height:100%;width:35%;background:#2563eb;border-radius:2px;animation:ibar 1.2s ease-in-out infinite}
  @keyframes ibar{0%{transform:translateX(-100%)}100%{transform:translateX(300%)}}
  .imp-done{border-left:4px solid #16a34a}
  .imp-h b{font-size:18px}
  .imp-h button{border:0;background:none;font-size:20px;padding:2px 8px}
  .imp .box{border:1px solid var(--line);border-radius:10px;padding:10px 14px;margin:10px 0}
  .imp .ok{color:#16a34a;font-weight:700}
  .imp .bad{color:var(--late);font-weight:700}
  .imp ul{margin:6px 0 0;padding-left:20px;font-size:13.5px;max-height:130px;overflow:auto}
  .imp .tbl{max-height:max(420px, calc(100vh - 230px));overflow:auto;border:1px solid var(--line);border-radius:10px}
  .imp table{font-size:15px;min-width:0;width:100%}
  .imp th,.imp td{padding:9px 11px}
  .imp thead th{font-size:13.5px}
  .imp thead th{position:sticky;top:0;background:var(--card);z-index:1}
  .imp td[data-ir]{cursor:cell}
  .imp td[data-ir]:hover{outline:2px solid #2563eb;outline-offset:-2px}
  .imp td.ied{background:var(--cc-bg);font-weight:700}
  .imp td[data-sel]{outline:2px solid #2563eb;outline-offset:-2px;position:relative}
  .imp td[data-sel] .fh{position:absolute;right:0;bottom:0;width:11px;height:11px;background:#2563eb;border:1px solid #fff;cursor:crosshair}
  .imp td.idrag{background:#dbeafe}
  .imp td[data-ic="15"]{position:relative}
  .imp .xcar{position:absolute;right:3px;top:50%;margin-top:-10px;width:20px;height:20px;line-height:20px;text-align:center;border-radius:50%;
             font-size:11px;background:#fee2e2;color:#b91c1c;cursor:pointer;opacity:.35}
  .imp td:hover .xcar{opacity:1}
  .imp .pv{color:var(--mut);font-style:italic;font-size:.9em}
  .imp .iorg{display:flex;gap:6px;flex-wrap:wrap;align-items:center;margin:10px 0 2px}
  .imp .iorg .chip{font-size:14px;padding:6px 14px}
  .imp .iorg .chip.on{background:#2563eb;border-color:#2563eb;color:#fff}
  .imp .iorg .chip:disabled{opacity:.45;cursor:default}
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
  #addBox{margin:4px 0 10px}
  .addwrap{overflow-x:auto;-webkit-overflow-scrolling:touch}
  .addt{border-collapse:collapse}
  .addt th{font-size:12.5px;font-weight:600;color:var(--mut);text-align:left;padding:2px 4px;white-space:nowrap}
  .addt th i{color:#dc2626;font-style:normal}
  .addt td{padding:2px}
  .addt input,.addt select{font:inherit;font-size:14px;padding:6px 7px;border:1px solid var(--line);border-radius:7px;background:var(--card);color:inherit;box-sizing:border-box}
  .addt .addx{padding:4px 9px}
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
  <a class="menu" href="/ready">🚦 รถ/คนพร้อมใช้</a>
  <a class="menu" href="/users">👥 ผู้ใช้</a>
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
  <button id="addOpen" title="กรอกงานที่เพิ่มเข้ามาเองบนเว็บ ทีละแถว — เพิ่มเข้าวันเดิม ไม่ลบงานเก่า">➕ เพิ่มงาน</button>
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
  <div class="tblrow">
    <aside id="carbar" class="carbar" hidden></aside>
    <div class="wrap"><table>
      <thead id="head"></thead>
      <tbody id="rows"></tbody>
    </table></div>
  </div>
  <p class="mut" style="font-size:13px">ข้อมูลจากชีต "แผนงาน Gasbulk" คอลัมน์ A–Z (อ่านอย่างเดียว) &middot; สีแดง = ยกเลิก/โหลดเก็บ</p>
</main>

<div class="savebadge" id="savebadge" hidden></div>
<div class="imp-back" id="impBack" hidden><div class="imp">
  <div class="imp-h"><b id="impTitle">📥 นำเข้า Excel / 📋 วางข้อมูลลูกค้า</b><button id="impClose" title="ปิด">✕</button></div>
  <p class="mut" id="impIntro" style="margin:0 0 8px;font-size:14px">
    เลือกไฟล์ใบจัดรถ (.xlsx) ระบบอ่านชีต "ข้อมูลการจัดส่ง" คอลัมน์ E–AD แล้วแสดงเป็นตาราง
    <b>แก้ข้อมูลในตารางนี้ได้เลยก่อนนำเข้า</b> ยังไม่เขียนอะไรลงชีตจนกว่าคุณจะกดยืนยัน</p>
  <input type="file" id="impFile" accept=".xlsx">
  <div id="pasteBox" style="margin:10px 0">
    <div style="margin:0 0 10px;padding:10px;border-radius:10px;background:#ecfdf5;border:1px solid #a7f3d0">
      <button id="fleetGo" class="go">📄 ดึงงานจากชีตแผนรถ PTGLG</button>
      <button id="fleetSync" class="go" style="background:#0e7490" title="งานที่ลงชีตแล้ว: เติมเลขออเดอร์/เลขโหลดที่มาทีหลัง · งานที่เพิ่มในแผนรถ: นำไปจัดรถ">🔄 เทียบกับชีต (เติมเลข / งานเพิ่ม)</button>
      แท็บวันที่: <select id="fleetDate" style="font:inherit;padding:6px 8px;border-radius:8px"><option value="">กำลังโหลด...</option></select>
      <span class="mut" style="font-size:13px">งาน SC + งานภูมิภาค แสดงให้ตรวจ/แก้ก่อน · ยังไม่เขียนอะไรจนกว่าจะกดยืนยัน</span>
      <div id="fleetMsg" class="mut" style="font-size:13px;margin-top:4px"></div>
    </div>
    <div id="pasteManual" hidden>                 <!-- ซ่อน: ปุ่มดึงจากแผนรถยังใช้กล่องนี้อยู่เบื้องหลัง -->
    <b>📋 หรือ วางข้อมูลที่ลูกค้าให้มา</b>
    <p class="mut" style="margin:4px 0 6px;font-size:13px">คัดลอกตารางจาก Excel/อีเมล แล้ววางในกล่องนี้ (Ctrl+V) ตามลำดับ 10 คอลัมน์:
      เวลาส่งมอบ · เลขออเดอร์ · เลขโหลด · น้ำหนักบรรทุก · น้ำหนักสุทธิ · ต้นทาง · ปลายทาง · Drop · หมายเหตุ · เบอร์รถ
      (จะมีบรรทัดหัวตารางมาด้วยหรือไม่ก็ได้) ระบบเติมวันที่ เที่ยววิ่ง ทะเบียน และคนขับให้ แล้วให้ตรวจ/แก้ก่อนเขียนลงชีต<br>
      ถ้าวางพร้อมหัวตาราง จะใส่คอลัมน์เพิ่มได้ เช่น <b>เวลาเข้าโหลด (P)</b> · เวลาออกจากฟรีต (P) · เวลาโทรตาม พขร (P) · พขร.1 · พขร.2 · ประเภทรถ
      (ถ้ามีแต่เวลาเข้าโหลด ระบบคำนวณอีกสองช่องให้: ออกจากฟรีต = เข้าโหลด − 30 นาที, โทรตาม พขร = ออกจากฟรีต − 1 ชม.)</p>
    <textarea id="pasteTxt" rows="5" style="width:100%;box-sizing:border-box;font:inherit" placeholder="วางข้อมูลที่นี่ (Ctrl+V)"></textarea>
    <div style="margin-top:6px">วันที่ของงาน: <input type="date" id="pasteDate"> <button id="pasteGo" class="go">ตรวจข้อมูลที่วาง</button></div>
    </div>
  </div>
  <div id="addBox" hidden>
    <p class="mut" style="margin:0 0 8px;font-size:14px">กรอกงานที่เพิ่มเข้ามา <b>1 แถว = 1 งาน (1 Drop)</b> · ต้องมีอย่างน้อย <b>ปลายทาง</b> ·
      ระบบเติมเที่ยววิ่ง ทะเบียน พขร. เบอร์โทร และเวลาออกจากฟรีต/โทรตาม พขร (จากเวลาเข้าโหลด) ให้เอง แล้วให้ตรวจ/แก้ในตารางก่อนเขียนลงชีต ·
      <b>เพิ่มเข้าวันเดิม ไม่ลบงานเก่า</b> (แทรกติดรถคันเดียวกัน · งานที่มีในชีตแล้วจะเตือนว่าซ้ำ)</p>
    <div style="margin-bottom:8px">วันที่ของงาน: <input type="date" id="addDate"></div>
    <div class="addwrap"><table class="addt"><thead><tr id="addHead"></tr></thead><tbody id="addRows"></tbody></table></div>
    <div style="margin-top:8px;display:flex;gap:8px;flex-wrap:wrap;align-items:center">
      <button id="addMore">＋ เพิ่มอีกแถว</button> <button id="addGo" class="go">ตรวจข้อมูล →</button> <span id="addMsg" style="color:#dc2626;font-size:14px"></span></div>
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

// ── รถคันไหนจัดงานแล้ว: นับจากแถวของวันนั้น (ไม่นับแถวยกเลิก) ──
function carUse(cellRows){                     // → {เบอร์รถ: {trips: ['เที่ยว 1', ...], drops: n}}
  const m = {};
  cellRows.forEach(c => {
    const car = String(c[15] || '').trim();
    if(!car || /ยกเลิก|cancel/i.test(String(c[12] || ''))) return;
    const u = m[car] = m[car] || {trips: [], drops: 0};
    const t = String(c[4] || '').trim();
    if(t && u.trips.indexOf(t) < 0) u.trips.push(t);
    u.drops++;
  });
  Object.keys(m).forEach(k => m[k].trips.sort());
  return m;
}
function useText(u){ return u ? 'มีงานแล้ว · ' + (u.trips.length ? u.trips.join(', ') + ' · ' : '') + u.drops + ' drop' : 'ว่าง'; }
function allCars(){
  const set = {};
  Object.keys(CARS || {}).forEach(k => { set[k] = 1; });
  ((OPTS && OPTS.suggest && OPTS.suggest['15']) || []).forEach(k => { set[k] = 1; });
  return Object.keys(set).sort((a, b) => a.localeCompare(b, 'th', {numeric: true}));
}
function refreshCarList(cellRows){             // รายการเบอร์รถในช่องเลือก: รถว่างขึ้นก่อน + ป้ายสถานะ
  const dl = document.getElementById('dl15');
  if(!dl) return;
  const use = carUse(cellRows), cars = allCars();
  Object.keys(use).forEach(k => { if(cars.indexOf(k) < 0) cars.push(k); });
  const free = cars.filter(k => !use[k]), busy = cars.filter(k => use[k]);
  dl.innerHTML = free.concat(busy).map(k => '<option value="' + esc(k) + '" label="' + esc(useText(use[k])) + '"></option>').join('');
}
function updateCarBar(){
  const bar = document.getElementById('carbar');
  if(!bar || !DATA) return;
  const cars = allCars();
  if(!cars.length){                                    // รายชื่อรถยังโหลดไม่เสร็จ (ครั้งแรกอาจช้า) — บอกไว้ ไม่ซ่อนแผง
    bar.hidden = false;
    bar.innerHTML = '<div class="hd2">🚛 รถวันที่ ' + dmy(DATA.date) + '</div><p class="tipd">' + (CARS ? 'ไม่พบรายชื่อรถในชีตข้อมูลรถ' : '⏳ กำลังโหลดรายชื่อรถ…') + '</p>';
    return;
  }
  const use = carUse(DATA.rows.map(x => x.cells));
  const busy = cars.filter(k => use[k]), free = cars.filter(k => !use[k]);
  Object.keys(use).forEach(k => { if(cars.indexOf(k) < 0) busy.push(k); });
  const q = document.getElementById('q').value.trim();
  const chip = (k, cls, sub) => '<div class="cp ' + cls + (q === k ? ' sel' : '') + '" draggable="true" data-car="' + esc(k) + '" title="' +
    esc(k + ' · ' + useText(use[k]) + ' — ลากไปวางบนแถวในตาราง หรือกดเพื่อดูงานของคันนี้') + '"><span>' + esc(k) + '</span>' + (sub ? '<small>' + esc(sub) + '</small>' : '') + '</div>';
  bar.hidden = false;
  bar.innerHTML = '<div class="hd2">🚛 รถวันที่ ' + dmy(DATA.date) + '</div>' +
    '<div class="sum2"><span class="on">จัดแล้ว <b>' + busy.length + '</b></span><span class="free">ว่าง <b>' + free.length + '</b></span><span class="mut">/ ' + cars.length + ' คัน</span></div>' +
    '<p class="tipd">' + (EDITING ? '✋ ลากรถไปวางบนแถวในตาราง = ใส่เบอร์รถ' : '✋ กด "โหมดแก้ไข" ก่อน แล้วลากรถไปวางบนแถวได้') + ' · กดชื่อรถ = ดูงานของคันนั้น</p>' +
    '<h4>🟢 ว่าง (' + free.length + ')</h4>' + (free.length ? '<div class="g2">' + free.map(k => chip(k, 'f', '')).join('') + '</div>' : '<div class="mut">ไม่มีรถว่าง</div>') +
    '<h4>🔵 จัดแล้ว (' + busy.length + ')</h4>' + (busy.map(k => chip(k, 'u', (use[k].trips.map(t => t.replace('เที่ยว ', 'ท.')).join(',') || '') + ' · ' + use[k].drops + 'd')).join('') || '<div class="mut">ยังไม่มี</div>');
}
document.addEventListener('click', e => {
  const cp = e.target.closest && e.target.closest('#carbar .cp');
  if(cp){ const q = document.getElementById('q'); q.value = q.value === cp.dataset.car ? '' : cp.dataset.car; render(); }   // กดชื่อรถ = ค้นหาแถวของคันนั้น (กดซ้ำ = ล้าง)
});
// ลากชื่อรถ → วางบนแถวในตารางหลัก = ใส่เบอร์รถในแถวนั้น (ผ่าน saveCell เหมือนพิมพ์เอง: เติมทะเบียน/พขร./เที่ยววิ่งให้)
document.addEventListener('dragstart', e => {
  const cp = e.target.closest && e.target.closest('.carbar .cp');
  if(!cp) return;
  e.dataTransfer.setData('text/plain', cp.dataset.car); e.dataTransfer.effectAllowed = 'copy';
  document.body.dataset.dragcar = cp.dataset.car;
});
document.addEventListener('dragend', () => { delete document.body.dataset.dragcar; document.querySelectorAll('tr.dropok').forEach(t => t.classList.remove('dropok')); });
const ROWS_EL = document.getElementById('rows');
ROWS_EL.addEventListener('dragover', e => {
  if(!document.body.dataset.dragcar) return;
  const tr = e.target.closest('tr'); if(!tr || !tr.querySelector('td[data-r]')) return;
  e.preventDefault(); e.dataTransfer.dropEffect = 'copy';
  document.querySelectorAll('tr.dropok').forEach(t => { if(t !== tr) t.classList.remove('dropok'); });
  tr.classList.add('dropok');
});
ROWS_EL.addEventListener('dragleave', e => { const tr = e.target.closest('tr'); if(tr && !tr.contains(e.relatedTarget)) tr.classList.remove('dropok'); });
ROWS_EL.addEventListener('drop', e => {
  const car = document.body.dataset.dragcar || e.dataTransfer.getData('text/plain');
  const td = e.target.closest('tr') && e.target.closest('tr').querySelector('td[data-r]');
  if(!car || !td) return;
  e.preventDefault();
  document.querySelectorAll('tr.dropok').forEach(t => t.classList.remove('dropok'));
  if(!EDITING){ toast('กด "โหมดแก้ไข" ก่อน แล้วค่อยลากรถมาวาง', true); return; }
  const x = DATA.rows.find(r => r.row === Number(td.dataset.r));
  if(!x) return;
  if(x.cancelled){ toast('แถวนี้ยกเลิก/โหลดเก็บ — ไม่ใส่รถให้', true); return; }
  const old = x.cells[15] || '';
  if(old === car) return;
  if(old && !confirm('แถว ' + x.row + ' มีรถ ' + old + ' อยู่แล้ว — เปลี่ยนเป็น ' + car + ' ?')) return;
  saveCell(x, 15, old, car, false);
});

function render(){
  if(!DATA) return;
  updateCarBar();
  if(!CARS && !render._cars){ render._cars = 1; loadCars().then(() => updateCarBar()); }
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
    OPTS.suggest['18'] = DRIVERS; OPTS.suggest['19'] = DRIVERS; OPTS.suggest['22'] = DRIVERS;
    delete OPTS.strict['18']; delete OPTS.strict['19']; delete OPTS.strict['22'];
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
let OPTS_P = null;                      // กำลังโหลดอยู่ — เรียกซ้ำระหว่างรอ ใช้คำขอเดิม ไม่ยิงซ้ำ
async function loadOpts(){              // รายการตัวเลือกของช่อง (อ่านจากไฟล์ต้นทางฝั่งเซิร์ฟเวอร์)
  if(OPTS) return;
  if(OPTS_P) return OPTS_P;
  OPTS_P = (async () => {
    loadCars();
    try{
      const r = await fetch('/api/plan/options');
      if(!r.ok) return;
      OPTS = await r.json();
      buildDatalists();
      applyDrivers();
    }catch(e){}
  })();
  try{ await OPTS_P; } finally{ OPTS_P = null; }
}

// ตัวแก้ค่าในช่อง (ใช้ทั้งตารางหลักและตารางในหน้าต่างนำเข้า): เลือกอย่างเดียว / พิมพ์ค้นหา / พิมพ์อิสระ
let CARCTX = null;                                    // แถวของวันที่ใช้คำนวณสถานะรถตอนเปิดช่องเบอร์รถ
function openEditor(td, i, old, onSave, onCancel, onSkip){
  if(i === 15) refreshCarList(CARCTX ? CARCTX() : (DATA ? DATA.rows.map(x => x.cells) : []));
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
    if(sug && sug.length && old) el.placeholder = old + '  (กด Delete = ลบ)';
    el.addEventListener('keydown', ev => {
      if(ev.key === 'Escape'){ ev.preventDefault(); finish(onCancel); }
      else if(ev.key === 'Delete' && !el.value && old){ ev.preventDefault(); finish(() => onSave('', 'down')); }   // ลบค่าในช่อง
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
let IMPDAY = {date: '', rows: []};                    // แถวในชีตของวันที่กำลังนำเข้า (ใช้บอกว่ารถคันไหนมีงานแล้ว)
function impDayRows(skip){                             // แถวในชีตวันนั้น + แถวอื่นในตารางตรวจ (ไม่นับแถวที่กำลังแก้)
  const d = (IMP && IMP.info && IMP.info.date) || '';
  const base = IMPDAY.date === d ? IMPDAY.rows : (DATA && DATA.date === d ? DATA.rows.map(x => x.cells) : []);
  return base.concat((IMP ? IMP.rows : []).filter((_, k) => k !== skip));
}
function impCarPane(){                               // แผงรถในหน้าต่างตรวจ: ว่าง / มีงานแล้ว (นับชีตวันนั้น + แถวที่กำลังตรวจ)
  const cars = allCars();
  if(!cars.length) return '<div class="hd2">🚛 รถ</div><p class="tipd">' + (CARS ? 'ไม่พบรายชื่อรถ' : '⏳ กำลังโหลดรายชื่อรถ…') + '</p>';
  const use = carUse(impDayRows(-1)), q = String(IMP && IMP.q || '').trim();
  const busy = cars.filter(k => use[k]), free = cars.filter(k => !use[k]);
  Object.keys(use).forEach(k => { if(cars.indexOf(k) < 0) busy.push(k); });
  const chip = (k, cls, sub) => '<div class="cp ' + cls + (q === k ? ' sel' : '') + '" draggable="true" data-car="' + esc(k) + '" title="' +
    esc(k + ' · ' + useText(use[k]) + ' — ลากไปวางบนแถว หรือกดเพื่อค้นหาในตาราง') + '"><span>' + esc(k) + '</span>' + (sub ? '<small>' + esc(sub) + '</small>' : '') + '</div>';
  return '<div class="hd2">🚛 รถ</div><div class="sum2"><span class="on">มีงาน <b>' + busy.length + '</b></span><span class="free">ว่าง <b>' + free.length + '</b></span></div>' +
    '<p class="tipd">✋ ลากรถไปวางบนแถว = ใส่เบอร์รถ · นับรวมงานในชีตวันนั้น + แถวในตารางนี้</p>' +
    '<h4>🟢 ว่าง (' + free.length + ')</h4>' + (free.length ? '<div class="g2">' + free.map(k => chip(k, 'f', '')).join('') + '</div>' : '<div class="mut">ไม่มีรถว่าง</div>') +
    '<h4>🔵 มีงานแล้ว (' + busy.length + ')</h4>' + (busy.map(k => chip(k, 'u', (use[k].trips.map(t => t.replace('เที่ยว ', 'ท.')).join(',') || '') + ' · ' + use[k].drops + 'd')).join('') || '<div class="mut">ยังไม่มี</div>');
}
(function(){                                           // ลากรถ → วางบนแถวในตารางตรวจ = ใส่เบอร์รถแถวนั้น (ผ่าน impSet: เติมทะเบียน/พขร.)
  const box = document.getElementById('impBody');
  const rowOf = e => { const tr = e.target.closest && e.target.closest('tr'); return tr && tr.querySelector('td[data-ir]') ? tr : null; };
  box.addEventListener('dragover', e => {
    if(!document.body.dataset.dragcar) return;
    const tr = rowOf(e); if(!tr) return;
    e.preventDefault(); e.dataTransfer.dropEffect = 'copy';
    box.querySelectorAll('tr.dropok').forEach(t => { if(t !== tr) t.classList.remove('dropok'); });
    tr.classList.add('dropok');
  });
  box.addEventListener('drop', e => {
    const car = document.body.dataset.dragcar, tr = rowOf(e);
    if(!car || !tr || !IMP) return;
    e.preventDefault();
    const r = Number(tr.querySelector('td[data-ir]').dataset.ir), old = String(IMP.rows[r][15] || '').trim();
    if(old === car) return;
    if(old && !confirm('แถว ' + (r + 1) + ' มีรถ ' + old + ' อยู่แล้ว — เปลี่ยนเป็น ' + car + ' ?')) return;
    impSet(r, 15, car);
  });
  box.addEventListener('click', e => {                  // กดชื่อรถในแผง = ค้นหาในตารางตรวจ (กดซ้ำ = ล้าง)
    const cp = e.target.closest && e.target.closest('#impCars .cp');
    if(!cp || !IMP) return;
    e.stopPropagation();
    IMP.q = String(IMP.q || '').trim() === cp.dataset.car ? '' : cp.dataset.car; impRender();
  });
})();
function impBody(html){ document.getElementById('impBody').innerHTML = html; }
function dmy(iso){ return iso ? iso.slice(8,10) + '/' + iso.slice(5,7) + '/' + iso.slice(0,4) : '?'; }

async function impSend(o, ms){           // o = {rows?, commit?, replace?}  ไม่มี rows = ส่งไฟล์ที่เลือก · ms = รอนานสุด (มิลลิวินาที)
  const fd = new FormData();
  if(o.rows) fd.append('rows_json', JSON.stringify(o.rows)); else fd.append('file', IMPFILE);
  if(o.master) fd.append('master_json', JSON.stringify(o.master));
  if(o.near) fd.append('near', '1');
  if(o.skip) fd.append('skip_dups', '1');
  fd.append('commit', o.commit ? '1' : '0');
  fd.append('replace', o.replace ? '1' : '0');
  const ac = ms ? new AbortController() : null, to = ms ? setTimeout(() => ac.abort(), ms) : 0;
  let r;
  try{ r = await fetch('/api/plan/import', {method:'POST', body: fd, signal: ac ? ac.signal : undefined}); }
  catch(e){
    if(e.name === 'AbortError') throw new Error('รอเกิน ' + Math.round(ms / 1000) + ' วินาทีแล้วเซิร์ฟเวอร์ยังไม่ตอบ — Google Sheets อาจช้าหรือโควตาเต็ม รอ 1 นาทีแล้วเลือกไฟล์ใหม่อีกครั้ง');
    throw new Error('ส่งไฟล์ไม่สำเร็จ — ตรวจอินเทอร์เน็ตแล้วลองใหม่');
  }finally{ clearTimeout(to); }
  if(r.status === 401){ location.href = '/login'; return null; }
  let j = null;
  try{ j = await r.json(); }catch(e){}
  if(!r.ok){
    const why = (j && j.detail) || (r.status === 413 ? 'ไฟล์ใหญ่เกินที่เว็บรับได้ (4 MB)'
      : r.status === 504 || r.status === 502 ? 'เซิร์ฟเวอร์ตอบไม่ทันเวลา (Google Sheets อาจช้าหรือโควตาเต็ม) — รอ 1 นาทีแล้วลองใหม่' : 'HTTP ' + r.status);
    throw new Error(why);
  }
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

const IMP_WAIT_MS = 90000;               // รอเซิร์ฟเวอร์อ่านไฟล์ได้นานสุด 90 วินาที
async function impPreview(){             // อ่านไฟล์ครั้งแรก
  const f = IMPFILE, t0 = Date.now(), sec = () => Math.round((Date.now() - t0) / 1000);
  const size = f.size < 1048576 ? Math.max(1, Math.round(f.size / 1024)) + ' KB' : (f.size / 1048576).toFixed(1) + ' MB';
  if(f.size > 4 * 1048576){
    impBody('<div class="box bad">ไฟล์ “' + esc(f.name) + '” ขนาด ' + size + ' ใหญ่เกิน 4 MB ที่เว็บรับได้ — ลบชีตที่ไม่ใช้ออกแล้วบันทึกใหม่ (ต้องมีชีต “ข้อมูลการจัดส่ง”)</div>');
    return;
  }
  const draw = () => impBody('<div class="box imp-wait"><b>⏳ กำลังอ่านไฟล์ “' + esc(f.name) + '”</b> (' + size + ') · ' + sec() + ' วินาที' +
    '<div class="mut" style="font-size:13px;margin-top:3px">ส่งไฟล์ให้เซิร์ฟเวอร์ → อ่านชีต “ข้อมูลการจัดส่ง” → ตรวจกับชีตแผนงาน' +
    (sec() >= 20 ? ' · <b>ช้ากว่าปกติ</b> (Google Sheets อาจตอบช้า) รอได้ถึง ' + IMP_WAIT_MS / 1000 + ' วินาที' : '') + '</div><div class="ibar"><i></i></div></div>');
  draw();
  const tick = setInterval(draw, 1000);
  loadOpts();                            // รายการเลือก (ต้นทาง/ปลายทาง/รถ ฯลฯ) โหลดคู่กันไป ไม่ต้องรอก่อนส่งไฟล์
  try{
    const j = await impSend({}, IMP_WAIT_MS);
    clearInterval(tick);
    if(!j) return;
    IMP = {rows: j.rows, headers: j.headers, edited: {}, errs: {}, warns: {}, info: j, replace: !j.existing, onlyBad: false, master: j.master || null,
           readMsg: '✅ อ่านไฟล์ “' + f.name + '” เสร็จใน ' + Math.max(1, sec()) + ' วินาที — พบ <b>' + j.total + ' งาน</b> ของวันที่ <b>' + dmy(j.date) + '</b>' +
                    (j.master_n ? ' · ข้อมูลรถ/พขร. ' + j.master_n + ' คัน' : '') + ' · ตรวจในตารางด้านล่างก่อนกดยืนยัน'};
    impMarkErrors(j);
    impRender();
  }catch(e){
    clearInterval(tick);
    impBody('<div class="box bad">อ่านไฟล์ไม่ได้ (' + sec() + ' วินาที): ' + esc(e.message) + '</div>');
  }
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

function serialDay(iso){                  // วันที่ → เลขวันแบบชีต (เช่น 2026-10-06 = 46301) ใช้ในเลข JOB
  if(!iso) return '';
  return String(Math.round((Date.UTC(Number(iso.slice(0, 4)), Number(iso.slice(5, 7)) - 1, Number(iso.slice(8, 10))) - Date.UTC(1899, 11, 30)) / 86400000));
}
function impAutoD(){                      // D ลำดับเที่ยว: นับเที่ยว (รถ+เที่ยววิ่ง) ไม่ซ้ำของวัน ต่อจากที่มีในชีต — ช่องที่คุณพิมพ์เองไม่แตะ
  IMP.autoD = IMP.autoD || {}; IMP.prevA = {};
  const known = {}; let mx = 0, amx = 0;
  (IMPDAY.date === (IMP.info && IMP.info.date) ? IMPDAY.rows : []).forEach(c => {
    const n = parseInt(String(c[3] || ''), 10), k = String(c[15] || '').trim() + '|' + String(c[4] || '').trim();
    if(n > 0){ mx = Math.max(mx, n); if(String(c[15] || '').trim() && !known[k]) known[k] = n; }
    amx = Math.max(amx, parseInt(String(c[0] || ''), 10) || 0);
  });
  IMP.rows.forEach((row, r) => { if(String(row[15] || '').trim()) IMP.prevA[r] = ++amx; });   // A = ลำดับรันต่อจากของวันนั้น (ชีตนับเฉพาะแถวที่มีเบอร์รถ)
  IMP.rows.forEach((row, r) => {
    const car = String(row[15] || '').trim(), trip = String(row[4] || '').trim();
    if(String(row[3] || '').trim() && !IMP.autoD[r]) return;                 // มีค่าอยู่แล้ว (ไม่ได้มาจากระบบ) = คงไว้
    let v = '';
    if(car && trip){ const k = car + '|' + trip; if(!known[k]) known[k] = ++mx; v = String(known[k]); }
    if(row[3] !== v){ row[3] = v; }
    IMP.autoD[r] = 1;
  });
}
function impGhost(row, ri, c){            // A/B ว่าง (สูตรในชีต) → แสดงตัวอย่างสีจาง (ชื่อห้ามซ้ำ impPreview — เคยทับกันจนเลือกไฟล์แล้วไม่อ่าน)
  if(c === 1){
    const car = String(row[15] || '').trim(), trip = String(row[4] || '').trim();
    return car && trip ? '<span class="pv" title="ตัวอย่าง — ชีตคำนวณเองตอนลง (วันที่+เบอร์รถ+เที่ยว)">' + esc(serialDay((IMP.info && IMP.info.date) || '') + car + trip) + '</span>' : '';
  }
  if(c === 0) return IMP.prevA && IMP.prevA[ri] ? '<span class="pv" title="ตัวอย่าง — ชีตรันลำดับให้เองตอนลง">' + IMP.prevA[ri] + '</span>' : '';
  return '';
}
function impRender(){
  impAutoD();
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
    return '<td data-ir="' + ri + '" data-ic="' + c + '"' + cls + (sel ? ' data-sel="1"' : '') + '>' + (c === 14 ? '<div class="nt" title="' + esc(v) + '">' + impHl(v) + '</div>' : (c <= 1 && !String(v || '').trim() ? impGhost(r, ri, c) : impHl(v))) +
      (c === 15 && String(v || '').trim() ? '<b class="xcar" data-xr="' + ri + '" title="เอารถออกจากแถวนี้">✕</b>' : '') + (sel ? '<i class="fh" title="ลากลงเพื่อคัดลอกค่าไปแถวล่าง"></i>' : '') + '</td>';
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
  const PL = impPlan(), adding = PL.adding, nw = PL.nw;
  const ok = j.can_commit && nw > 0 && !nerr && !IMP.checking;
  const nmaster = IMP.master ? Object.keys(IMP.master).length : 0;
  impBody(
    (IMP.readMsg ? '<div class="box imp-done">' + IMP.readMsg.replace(/“([^”]*)”/, (m0, n) => '“' + esc(n) + '”') + '</div>' : '') +
    '<div class="box"><b>วันที่ ' + dmy(j.date) + '</b> · ' + j.total + ' แถวงาน · ปลายทาง: <b>' + esc(j.target) + '</b>' +
    (nedit ? ' · <span class="ied" style="padding:1px 8px;border-radius:6px">แก้แล้ว ' + nedit + ' ช่อง</span>' : '') + '</div>' +
    er + w +
    '<label style="display:block;margin:6px 2px"><input type="checkbox" id="impOnlyBad"' + (IMP.onlyBad ? ' checked' : '') +
    '> ดูเฉพาะแถวที่มีช่องสีแดง (' + nbad + ' แถว)</label>' +
    impOriginBar() +
    '<div class="impsearch"><span class="sw"><span class="ico">🔍</span><input type="search" id="impQ" placeholder="ค้นหาในตาราง (รถ / ปลายทาง / ออเดอร์ / ชื่อคนขับ)" value="' + esc(IMP.q || '') +
    '">' + (IMP.q ? '<button type="button" class="clr" id="impQx" title="ล้างคำค้น">✕</button>' : '') + '</span><span class="cnt">' +
    (String(IMP.q || '').trim() || IMP.origin ? 'พบ ' + shown + ' จาก ' + IMP.rows.length + ' แถว' : 'ทั้งหมด ' + IMP.rows.length + ' แถว') + '</span>' +
    (IMP.near ? ' <button class="undo" id="impRenum" title="จัดเที่ยววิ่งของทุกแถวใหม่ตาม Drop (Drop 1 = เที่ยวใหม่, Drop 2+ ต่อเที่ยวเดิม) ไม่ให้ซ้ำกับงานในชีตของวันนั้น">🔢 จัดเที่ยววิ่งใหม่ตาม Drop</button>' : '') + '</div>' +
    '<span class="mut" style="font-size:12.5px">ลากช่องไปวางบนอีกช่อง = สลับค่า · ลากจุดสีน้ำเงินที่มุมช่อง = คัดลอกลงแถวล่าง</span>' +
    '<button class="undo" id="impUndo"' + (IMP.hist && IMP.hist.length ? '' : ' disabled') + ' title="ย้อนกลับการแก้ล่าสุด (Ctrl+Z)">↶ ย้อนกลับ</button>' +
    (IMP.checking ? ' <span class="mut" style="font-size:12.5px">⏳ กำลังตรวจข้อมูล…</span>' : '') +
    '<div class="tblrow"><aside class="carbar" id="impCars">' + impCarPane() + '</aside>' +
    '<div class="tbl" style="flex:1;min-width:0"><table><thead>' + head + '</thead><tbody>' + body + '</tbody></table></div></div>' +
    '<div class="box">' + ex + '</div>' +
    (ndup && !(IMP.near || !IMP.replace) ? '<div class="box ok">🔁 พบ ' + ndup + ' แถวที่มีในชีตแล้ว — เลือก "แทนที่งานเดิมทั้งวัน" อยู่ จึงไม่เกิดงานซ้ำ</div>' : '') +
    (ndup && (IMP.near || !IMP.replace) ? '<div class="box" style="border-color:#f59e0b;background:#fffbeb"><b style="color:#b45309">🔁 พบ ' + ndup + ' แถวที่มีในชีตแล้ว (นำเข้าซ้ำ)</b><br>' +
      '<label><input type="checkbox" id="impSkip"' + (IMP.skip ? ' checked' : '') + '> <b>ข้ามแถวที่ซ้ำกับชีต (' + ndup +
      ' แถว)</b> — งานที่มีเลขออเดอร์/เลขโหลด/ปลายทางเหมือนที่อยู่ในชีตวันนี้แล้ว จะไม่ถูกเพิ่มซ้ำ (แถวสีเหลืองในช่องเลขออเดอร์)</label></div>' : '') +
    (IMP.near ? '' : '<div class="box ' + (nmaster ? 'ok' : '') + '">' + (nmaster
      ? '🚚 พบข้อมูลรถ/พขร. ' + nmaster + ' คันในไฟล์นี้ — จะเก็บไว้ใช้เติมประเภท/ทะเบียน/พขร./เบอร์โทรอัตโนมัติตอนเลือกเบอร์รถ'
      : 'ไม่พบแท็บข้อมูลรถ/พขร. ในไฟล์นี้ — ถ้าเคยนำเข้าไว้แล้ว ระบบใช้ข้อมูลเดิมต่อ') + '</div>') +
    (j.can_commit ? '' : '<div class="box bad">เขียนลงชีตไม่ได้ตอนนี้: ' + esc(j.block_reason) + '</div>') +
    (IMP.origin && IMP.replace ? '<div class="box">ℹ️ เขียนทีละกลุ่มต้นทาง = เพิ่มเข้าไป ไม่แทนที่ทั้งวัน (กันงานของกลุ่มอื่นหาย)</div>' : '') +
    '<button class="go" id="impGo"' + (ok ? '' : ' disabled') + '>เขียน ' + nw + ' แถว' + PL.label + 'ลงชีต</button>');
  const t = document.querySelector('#impBody .tbl');
  if(t){ t.scrollLeft = sx; t.scrollTop = sy; }
  const rp = document.getElementById('impReplace'); if(rp) rp.onchange = e => { IMP.replace = e.target.checked; impRender(); };
  const sk = document.getElementById('impSkip'); if(sk) sk.onchange = e => { IMP.skip = e.target.checked; impRender(); };
  document.getElementById('impOnlyBad').onchange = e => { IMP.onlyBad = e.target.checked; impRender(); };
  document.querySelectorAll('#impBody [data-iorg]').forEach(bt => { bt.onclick = () => { IMP.origin = bt.dataset.iorg; impRender(); }; });
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
const IMP_ORIGINS = ['SC BPK', 'PTT TANK', 'BSRC', 'UAC', 'IRPC'];
function impOriginBar(){                  // ปุ่มแยกต้นทาง 5 แห่ง (+ ทั้งหมด) พร้อมจำนวนแถว
  const cnt = {}; IMP.rows.forEach(r => { const o = String(r[11] || '').trim(); cnt[o] = (cnt[o] || 0) + 1; });
  const other = IMP.rows.length - IMP_ORIGINS.reduce((a, o) => a + (cnt[o] || 0), 0), cur = IMP.origin || '';
  const b = (v, label, n) => '<button type="button" class="chip' + (cur === v ? ' on' : '') + '" data-iorg="' + esc(v) + '"' + (n ? '' : ' disabled') + '>' + label + ' <b>' + n + '</b></button>';
  return '<div class="iorg"><span class="mut" style="font-size:13px">ต้นทาง:</span>' + b('', 'ทั้งหมด', IMP.rows.length) +
    IMP_ORIGINS.map(o => b(o, esc(o), cnt[o] || 0)).join('') + (other ? b('*', 'อื่นๆ', other) : '') + '</div>';
}
function impGroupIdx(){                  // แถวที่จะเขียน: เลือกต้นทางอยู่ = เฉพาะกลุ่มนั้น (หัวหน้างานแต่ละคนเขียนกลุ่มตัวเอง)
  const o = IMP.origin || '';
  return IMP.rows.map((_, i) => i).filter(i => {
    const org = String(IMP.rows[i][11] || '').trim();
    return !o || (o === '*' ? IMP_ORIGINS.indexOf(org) < 0 : org === o);
  });
}
function impPlan(){                       // → {idx, nw, nd, adding, replace, label}
  const j = IMP.info, idx = impGroupIdx(), grp = !!IMP.origin;
  const replace = IMP.replace && !grp;    // เขียนทีละกลุ่ม = ห้ามแทนที่ทั้งวัน (จะลบงานกลุ่มอื่น)
  const adding = IMP.near || !replace, dset = {}; (j.dups || []).forEach(i => { dset[i] = 1; });
  const nd = idx.filter(i => dset[i]).length;
  return {idx: idx, nd: nd, adding: adding, replace: replace, nw: idx.length - (adding && IMP.skip ? nd : 0),
          label: grp ? ' (เฉพาะ ' + (IMP.origin === '*' ? 'ต้นทางอื่นๆ' : IMP.origin) + ') ' : ' '};
}
function impHidden(ri){                  // ถูกซ่อนด้วยช่องค้นหา / ปุ่มต้นทางไหม
  const o = IMP.origin || '', org = String(IMP.rows[ri][11] || '').trim();
  if(o === '*' ? IMP_ORIGINS.indexOf(org) >= 0 : (o && org !== o)) return true;      // แล้วค่อยกรองด้วยคำค้น
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
function impAutoXZ(r){
  IMP.autoXZ = IMP.autoXZ || {};
  const row = IMP.rows[r], d = (IMP.info && IMP.info.date) || '';
  const manual = !IMP.autoXZ[r] && (String(row[23] || '').trim() || String(row[25] || '').trim()) && IMP.userXZ && IMP.userXZ[r];
  if(manual) return;
  const v = xzFrom(row, d);
  if(!v) return;
  if(row[24] !== v[2]){ row[24] = v[2]; IMP.edited[r + ',24'] = 1; }     // พิมพ์แค่ 08:00 → เติมวันที่ให้เหมือนช่องอื่น
  if(row[23] !== v[0]){ row[23] = v[0]; IMP.edited[r + ',23'] = 1; }
  if(row[25] !== v[1]){ row[25] = v[1]; IMP.edited[r + ',25'] = 1; }
  IMP.autoXZ[r] = 1;
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
  const oldCar = c === 15 ? String(IMP.rows[r][15] || '').trim() : '';
  impApply(r, c, v);
  if(c === 15 && !v && oldCar) impUnfillCar(r, oldCar);
  if(c === 23 || c === 25){ IMP.userXZ = IMP.userXZ || {}; IMP.userXZ[r] = 1; if(IMP.autoXZ) delete IMP.autoXZ[r]; }   // พิมพ์ X/Z เอง = ไม่คำนวณทับ
  if(c === 24 || c === 15 || c === 11) impAutoXZ(r);
  impRecheck();
}
function impUnfillCar(r, oldCar){         // เอารถออก → ล้างช่องที่เติมมาจากรถคันนั้น (ช่องที่พิมพ์เองค่าอื่นไม่แตะ)
  const c = (CARS && CARS[oldCar]) || {}, row = IMP.rows[r];
  [[16, 't'], [17, 'plate'], [18, 'd1'], [19, 'd2'], [20, 'p1'], [21, 'p2']].forEach(f => {
    const cur = String(row[f[0]] || '').trim();
    if(cur && (cur === String(c[f[1]] || '').trim() || (f[0] >= 20 && PHONES[String(row[f[0] - 2] || '').trim()] === cur))){ row[f[0]] = ''; IMP.edited[r + ',' + f[0]] = 1; }
  });
}
function impClearCar(r){                  // ปุ่ม ✕ ในช่องเบอร์รถ
  if(!IMP || !String(IMP.rows[r][15] || '').trim()) return;
  impSet(r, 15, '');
  toast('เอารถออกจากแถว ' + (r + 1) + ' แล้ว (กด ↶ ย้อนกลับ ได้)', false);
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

['mousedown', 'click'].forEach(ev => document.getElementById('impBody').addEventListener(ev, e => {   // ✕ เอารถออก (ก่อนตัวแก้/ลากสลับช่อง)
  const x = e.target.closest && e.target.closest('.xcar');
  if(!x) return;
  e.preventDefault(); e.stopPropagation();
  if(ev === 'click') impClearCar(Number(x.dataset.xr));
}, true));
document.getElementById('impBody').addEventListener('click', e => {
  if(e.target.closest('.fh') || (IMP && IMP.justDragged)) return;
  const td = e.target.closest('td[data-ir]');
  if(!td || !IMP || td.querySelector('input,select')) return;
  const r = Number(td.dataset.ir), c = Number(td.dataset.ic);
  IMP.sel = {r: r, c: c};
  CARCTX = () => impDayRows(r);
  openEditor(td, c, IMP.rows[r][c], v => impSet(r, c, v), impRender);
  CARCTX = null;
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
  const j = IMP.info, PL = impPlan(), replace = PL.replace, adding = PL.adding, nd = PL.nd, nw = PL.nw;
  if(!nw){ toast('ไม่มีแถวที่จะเขียน' + PL.label, true); return; }
  if(!confirm('เขียน ' + nw + ' แถว' + PL.label + 'ของวันที่ ' + dmy(j.date) + ' ลง' + j.target + (adding && !IMP.skip && nd ? ' (⚠ รวม ' + nd + ' แถวที่ซ้ำกับชีต)' : '') +
              (IMP.near ? ' (เพิ่มเข้าไป ไม่ลบงานเดิม)' : replace ? ' และลบงานเดิมของวันนั้นก่อน' : '') + ' — ยืนยัน?')) return;
  const btn = document.getElementById('impGo'); btn.disabled = true; btn.textContent = 'กำลังเขียนลงชีต...';
  try{
    const r = await impSend({rows: PL.idx.map(i => IMP.rows[i]), commit: true, replace: replace, master: IMP.master, near: IMP.near, skip: adding && IMP.skip});
    if(!r) return;
    const left = IMP.rows.length - PL.idx.length;
    impBody('<div class="box ok">✓ เขียนแล้ว ' + r.written + ' แถว (แถวที่ ' + r.first_row + '–' + r.last_row + ' ในชีต)' +
      (r.removed ? ' · ลบแถวส่วนเกิน ' + r.removed + ' แถว' : '') + (r.inserted ? ' · แทรกเพิ่ม ' + r.inserted + ' แถว' : '') +
      (r.kept_formula_cols && r.kept_formula_cols.length ? ' · ช่องที่เป็นสูตรในคอลัมน์ ' + r.kept_formula_cols.join(', ') + ' ระบบไม่ได้เขียนทับ ให้ชีตคำนวณเอง' : '') + '</div>' +
      (r.master_saved ? '<p class="mut">🚚 เก็บข้อมูลรถ/พขร. ' + r.master_saved + ' คันแล้ว (ใช้เติมอัตโนมัติ)</p>' : '') +
      (r.master_note ? '<div class="box bad">' + esc(r.master_note) + '</div>' : '') +
      '<p class="mut">' + esc(r.note || '') + '</p><p class="mut">ปิดหน้าต่างนี้เพื่อดูผลในหน้าแผนงาน (เปลี่ยนไปวันที่ ' + dmy(r.date) + ' ให้แล้ว)</p>' +
      (left > 0 && PL.label ? '<button class="go" id="impNext">จัดกลุ่มอื่นต่อ (เหลือ ' + left + ' แถวในตาราง)</button>' : ''));
    const nx = document.getElementById('impNext');
    if(nx) nx.onclick = () => {                                       // เอากลุ่มที่เขียนแล้วออกจากตาราง แล้วจัดกลุ่มที่เหลือต่อ
      const keep = IMP.rows.map((_, i) => i).filter(i => PL.idx.indexOf(i) < 0), ed = {};
      keep.forEach((oi, ni) => Object.keys(IMP.edited).forEach(k => { const p = k.split(','); if(Number(p[0]) === oi) ed[ni + ',' + p[1]] = 1; }));
      IMP.rows = keep.map(i => IMP.rows[i]); IMP.edited = ed; IMP.origin = ''; IMP.autoD = {}; IMP.autoXZ = {}; IMP.userXZ = {}; IMP.hist = [];
      IMPDAY = {date: '', rows: []}; IMP.near = true;
      fetch('/api/plan?date=' + r.date + '&fresh=1').then(x => x.json()).then(pj => { IMPDAY = {date: r.date, rows: (pj.rows || []).map(x => x.cells)}; }).catch(() => {}).finally(impRecheck);
    };
    document.getElementById('date').value = r.date; load(true);
    if(!document.getElementById('addBox').hidden) addReset();      // มาจาก ➕ เพิ่มงาน: ล้างฟอร์ม กันกดเพิ่มงานเดิมซ้ำ
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
// เวลาเดินทาง (นาที) จากพื้นที่ประจำรถ → คลังต้นทาง · ไม่รู้พื้นที่/คลัง = 30 นาทีเหมือนเดิม
const AREA_MIN = {'บางปะกง': {'SC BPK': 30, 'PTT TANK': 180, 'BSRC': 90, 'IRPC': 180},
                  'ศรีราชา': {'SC BPK': 90, 'PTT TANK': 90, 'BSRC': 30, 'IRPC': 90}};
function travelMin(car, origin){
  const a = (CARS && CARS[String(car || '').trim()] || {}).area || '', o = String(origin || '').trim();
  return (AREA_MIN[a] && AREA_MIN[a][o] != null) ? AREA_MIN[a][o] : 30;
}
function xzFrom(row, iso){                // คำนวณ X/Z ของแถวจาก Y + รถ + ต้นทาง → [X, Z] (ข้อความวันที่เวลา) หรือ null
  const y = String(row[24] || '').trim();
  if(!y) return null;
  let dY = parseStamp(y);
  if(!dY){
    const t = tp(y), d = iso || '';
    if(!t || !d) return null;
    dY = new Date(Number(d.slice(0, 4)), Number(d.slice(5, 7)) - 1, Number(d.slice(8, 10)), t[0], t[1], t[2]);
  }
  const dX = new Date(dY.getTime() - travelMin(row[15], row[11]) * 60000), dZ = new Date(dX.getTime() - 60 * 60000);
  return [fmtStamp(dX), fmtStamp(dZ), fmtStamp(dY)];
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
      if(dY && !out[23]) dX = new Date(dY.getTime() - travelMin(out[15], out[11]) * 60000);   // ตามพื้นที่ประจำรถ → คลัง
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
      IMPDAY = {date: iso, rows: []};
      if(pr.ok) ((await pr.json()).rows || []).forEach(x => {
        IMPDAY.rows.push(x.cells);
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
function openImp(paste, add){
  document.getElementById('impBack').hidden = false;
  ['impIntro', 'impFile', 'pasteBox'].forEach(id => { document.getElementById(id).hidden = !!add; });
  document.getElementById('addBox').hidden = !add;
  document.getElementById('impTitle').textContent = add ? '➕ เพิ่มงาน (กรอกเอง)' : '📥 นำเข้า Excel / 📋 วางข้อมูลลูกค้า';
  loadOpts();                            // โหลดรายการตัวเลือกไว้ก่อน ระหว่างที่คนกำลังเลือกไฟล์
  if(add) return;
  fleetDates();                          // รายการแท็บวันที่ของชีตแผนรถ — เปิดจากปุ่มไหนก็โหลด (เดิมโหลดเฉพาะปุ่มวางข้อมูล เลยค้าง "กำลังโหลด...")
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
async function fleetDates(){                                      // รายการแท็บวันที่ในชีตแผนรถ (ค่าเริ่ม = วันนี้)
  const sel = document.getElementById('fleetDate');
  try{
    const r = await fetch('/api/plan/fleet?list=1'), j = await r.json();
    if(!r.ok) throw new Error(j.detail || r.status);
    sel.innerHTML = j.tabs.map(d => '<option value="' + d + '"' + (d === j.default ? ' selected' : '') + '>' + dmy(d) + '</option>').join('');
  }catch(e){ sel.innerHTML = '<option value="">(อ่านรายการแท็บไม่ได้ — ใช้แท็บล่าสุด)</option>'; }
}
// ── เทียบแผนรถกับชีตแผนงานของวันเดียวกัน: เติมเลขที่มาทีหลัง + หางานที่เพิ่มเข้ามาใหม่ ──
function syncKey(origin, dest, time){ return [origin, dest, time].map(v => String(v || '').replace(/ /g, '').toLowerCase()).join('|'); }
function hhmmOf(v){ const t = tp(String(v || '').trim()); return t ? pad2(t[0]) + ':' + pad2(t[1]) : String(v || '').trim(); }
let SYNC = null;
async function fleetSync(){
  const msg = document.getElementById('fleetMsg'), d = document.getElementById('fleetDate').value;
  msg.textContent = 'กำลังเทียบแผนรถกับชีต...';
  try{
    const fr = await fetch('/api/plan/fleet' + (d ? '?date=' + d : '')), fj = await fr.json();
    if(!fr.ok) throw new Error(fj.detail || fr.status);
    const pr = await fetch('/api/plan?date=' + fj.date + '&fresh=1'), pj = await pr.json();      // อ่านชีตสด (ไม่ใช้แคช) จะได้เห็นเลขล่าสุด
    if(!pr.ok) throw new Error(pj.detail || pr.status);
    const pool = {};                                                    // งานในชีต จัดกลุ่มตาม ต้นทาง+ปลายทาง+เวลาส่งมอบ
    pj.rows.forEach(x => { if(x.cancelled) return; const k = syncKey(x.cells[11], x.cells[12], hhmmOf(x.cells[6])); (pool[k] = pool[k] || []).push(x); });
    const fill = [], fresh = [];
    fj.rows.forEach(f => {                                              // f = [เวลา, เลขออเดอร์, เลขโหลด, ปริมาณ, ต้นทาง, ปลายทาง, เงื่อนไข]
      const list = pool[syncKey(f[4], f[5], f[0])];
      const x = list && list.length ? list.shift() : null;
      if(!x){ fresh.push(f); return; }
      const ch = [];
      if(f[1] && !String(x.cells[7] || '').trim()) ch.push([7, f[1]]);
      if(f[2] && !String(x.cells[8] || '').trim()) ch.push([8, f[2]]);
      if(ch.length) fill.push({row: x.row, dest: x.cells[12], time: hhmmOf(x.cells[6]), car: x.cells[15] || '', ch: ch});
    });
    SYNC = {date: fj.date, tab: fj.tab, head: fj.head, fill: fill, fresh: fresh};
    msg.textContent = 'เทียบแท็บ ' + fj.tab + ' กับชีต ' + dmy(fj.date) + ' แล้ว';
    const tbl = fill.length ? '<div class="tbl" style="max-height:260px"><table><thead><tr><th>แถวในชีต</th><th>ปลายทาง</th><th>เวลาส่ง</th><th>เบอร์รถ</th><th>เลขออเดอร์ (H)</th><th>เลขโหลด (I)</th></tr></thead><tbody>' +
      fill.map(u => '<tr><td>' + u.row + '</td><td>' + esc(u.dest) + '</td><td>' + esc(u.time) + '</td><td>' + esc(u.car) + '</td><td>' +
        esc((u.ch.find(c => c[0] === 7) || ['', '–'])[1]) + '</td><td>' + esc((u.ch.find(c => c[0] === 8) || ['', '–'])[1]) + '</td></tr>').join('') + '</tbody></table></div>' : '';
    impBody('<div class="box"><b>🔄 ผลเทียบแผนรถ (แท็บ ' + esc(fj.tab) + ') กับชีตวันที่ ' + dmy(fj.date) + '</b></div>' +
      '<div class="box"><b>🔢 เติมเลขที่มาทีหลัง: ' + fill.length + ' แถว</b>' +
      (fill.length ? '<p class="mut" style="margin:4px 0 8px;font-size:13px">เติมเฉพาะช่องที่ยังว่าง · ไม่แตะรถ/ข้อมูลที่จัดไว้</p>' + tbl +
        '<button class="go" id="syncFill" style="margin-top:8px">เติมเลข ' + fill.length + ' แถวลงชีต</button>' : '<p class="mut" style="margin:4px 0 0">ไม่มีเลขที่ต้องเติม</p>') + '</div>' +
      '<div class="box"><b>➕ งานใหม่ในแผนรถที่ยังไม่มีในชีต: ' + fresh.length + ' งาน</b>' +
      (fresh.length ? '<ul>' + fresh.slice(0, 30).map(f => '<li>' + esc(f[4] + ' → ' + f[5] + ' · ' + (f[0] || 'ไม่มีเวลา') + (f[1] ? ' · ' + f[1] : '')) + '</li>').join('') + '</ul>' +
        '<button class="go" id="syncNew" style="margin-top:8px">นำ ' + fresh.length + ' งานใหม่ไปจัดรถ</button>' : '<p class="mut" style="margin:4px 0 0">ไม่มีงานเพิ่ม</p>') + '</div>');
    const bf = document.getElementById('syncFill'); if(bf) bf.onclick = syncFill;
    const bn = document.getElementById('syncNew'); if(bn) bn.onclick = () => {
      const TAB = String.fromCharCode(9), NL = String.fromCharCode(10);
      document.getElementById('pasteTxt').value = [SYNC.head].concat(SYNC.fresh).map(r => r.join(TAB)).join(NL);
      document.getElementById('pasteDate').value = SYNC.date;
      msg.textContent = 'งานใหม่ ' + SYNC.fresh.length + ' งาน — จัดรถในตารางด้านล่าง แล้วกดเขียนลงชีต (ระบบเพิ่มต่อ ไม่ลบงานเดิม)';
      pasteGo();
    };
  }catch(e){ msg.textContent = 'เทียบไม่สำเร็จ: ' + e.message; }
}
async function syncFill(){                                            // เขียนผ่านคิวบันทึกปกติของตารางหลัก (เหมือนพิมพ์เองทีละช่อง)
  if(!SYNC || !SYNC.fill.length) return;
  if(!EDITING){ setEditing(true); if(!EDITING) return; }
  const btn = document.getElementById('syncFill'); btn.disabled = true; btn.textContent = 'กำลังเติม...';
  if(!DATA || DATA.date !== SYNC.date){ document.getElementById('date').value = SYNC.date; await load(); }
  let n = 0;
  SYNC.fill.forEach(u => {
    const x = DATA.rows.find(r => r.row === u.row);
    if(!x) return;
    u.ch.forEach(c => { if(!String(x.cells[c[0]] || '').trim()){ saveCell(x, c[0], '', c[1], false); n++; } });
  });
  btn.textContent = 'ส่งเติมแล้ว ' + n + ' ช่อง ✓';
  toast('กำลังบันทึกเลข ' + n + ' ช่องลงชีต (ดูสถานะมุมล่าง) — ปิดหน้าต่างนี้เพื่อดูในตาราง', false);
}
document.getElementById('fleetSync').onclick = fleetSync;
document.getElementById('fleetGo').onclick = async () => {        // ดึงจากชีตแผนรถ → ใส่ในกล่องวาง → ตรวจแบบเดียวกับวางเอง
  const msg = document.getElementById('fleetMsg');
  msg.textContent = 'กำลังอ่านชีตแผนรถ...';
  try{
    const d = document.getElementById('fleetDate').value;
    const r = await fetch('/api/plan/fleet' + (d ? '?date=' + d : '')), j = await r.json();
    if(!r.ok) throw new Error(j.detail || r.status);
    if(!j.rows.length){ msg.textContent = 'แท็บ ' + j.tab + ' ไม่มีงานของ PTGLG'; return; }
    const TAB = String.fromCharCode(9), NL = String.fromCharCode(10);
    document.getElementById('pasteTxt').value = [j.head].concat(j.rows).map(r => r.join(TAB)).join(NL);
    document.getElementById('pasteDate').value = j.date;
    msg.textContent = 'ดึงจากแท็บ ' + j.tab + ' ได้ ' + j.rows.length + ' งาน' + (j.skipped ? ' (ข้ามงานขนส่งอื่น ' + j.skipped + ')' : '') + ' — ตรวจ/แก้ด้านล่างได้เลย';
    pasteGo();
  }catch(e){ msg.textContent = 'ดึงไม่สำเร็จ: ' + e.message; }
};
// ── ➕ เพิ่มงาน: กรอกเองทีละแถวบนเว็บ → แปลงเป็นชุด "วางข้อมูล" พร้อมหัวตาราง → ใช้ตัวตรวจเดียวกัน (เติมเที่ยว/รถ/พขร., กันซ้ำ, แทรกติดรถคันเดิม) ──
const ADD_F = [['เวลาส่งมอบ', 'time', 96], ['ต้นทาง', 'o', 110], ['ปลายทาง', 'd', 200], ['Drop', 'drop', 64], ['น้ำหนักบรรทุก', 'num', 96],
               ['เลขออเดอร์', 't', 110], ['เลขโหลด', 't', 110], ['เบอร์รถ', 'car', 96], ['เวลาเข้าโหลด', 'time', 96], ['หมายเหตุ', 't', 170]];
function addCell(f, v){
  const at = ' data-k="' + f[0] + '" style="width:' + f[2] + 'px"';
  if(f[1] === 'time') return '<input type="time"' + at + ' value="' + esc(v) + '">';
  const st = OPTS && OPTS.strict || {};
  const lst = f[1] === 'o' ? st['11'] : f[1] === 'drop' ? (st['13'] || ['1', '2', '3', '4', '5']) : null;
  if(lst && lst.length) return '<select' + at + '>' + (f[1] === 'o' ? '<option value="">—</option>' : '') +
    lst.map(x => '<option' + (String(x) === String(v) ? ' selected' : '') + '>' + esc(x) + '</option>').join('') + '</select>';
  return '<input' + at + (f[1] === 'd' ? ' list="dl12"' : f[1] === 'car' ? ' list="dl15"' : '') + (f[1] === 'num' ? ' inputmode="decimal"' : '') + ' value="' + esc(v) + '">';
}
function addRead(){                      // ค่าในฟอร์ม → [{ชื่อคอลัมน์: ค่า}] (ข้ามแถวที่ว่างทั้งแถว · Drop อย่างเดียวไม่นับ)
  return [...document.querySelectorAll('#addRows tr')].map(tr => {
    const o = {}; tr.querySelectorAll('[data-k]').forEach(el => { o[el.dataset.k] = el.value.trim(); }); return o;
  }).filter(o => ADD_F.some(f => f[0] !== 'Drop' && o[f[0]]));
}
function addRow(v){
  v = v || {};
  document.getElementById('addRows').insertAdjacentHTML('beforeend', '<tr>' + ADD_F.map(f => '<td>' + addCell(f, v[f[0]] || '') + '</td>').join('') +
    '<td><button class="addx" title="ลบแถวนี้">✕</button></td></tr>');
}
function addReset(){
  document.getElementById('addRows').innerHTML = ''; addRow(); document.getElementById('addMsg').textContent = '';
}
async function openAdd(){
  openImp(false, true);
  IMP = null; impBody('');
  const d = document.getElementById('addDate'); d.value = DATA ? DATA.date : (document.getElementById('date').value || '');
  document.getElementById('addHead').innerHTML = ADD_F.map(f => '<th>' + f[0] + (f[1] === 'd' ? ' <i>*</i>' : '') + '</th>').join('') + '<th></th>';
  document.getElementById('addRows').innerHTML = '<tr><td class="mut" colspan="' + (ADD_F.length + 1) + '">กำลังโหลดรายการตัวเลือก...</td></tr>';
  await loadOpts();                      // รายการต้นทาง/Drop/ปลายทาง/เบอร์รถ ให้เลือก
  addReset();
  const f = document.querySelector('#addRows input'); if(f) f.focus();
}
document.getElementById('addOpen').onclick = openAdd;
document.getElementById('addMore').onclick = () => {     // แถวใหม่: ต้นทางตามแถวบน (งานเพิ่มมักออกคลังเดียวกัน)
  const last = [...document.querySelectorAll('#addRows tr')].pop(), v = {};
  if(last) last.querySelectorAll('[data-k="ต้นทาง"]').forEach(el => { v[el.dataset.k] = el.value; });
  addRow(v);
  const inp = [...document.querySelectorAll('#addRows tr')].pop().querySelector('input'); if(inp) inp.focus();
};
document.getElementById('addRows').addEventListener('click', e => {
  const b = e.target.closest('.addx'); if(!b) return;
  b.closest('tr').remove();
  if(!document.querySelector('#addRows tr')) addRow();
});
document.getElementById('addGo').onclick = () => {
  const msg = document.getElementById('addMsg'), iso = document.getElementById('addDate').value, rows = addRead();
  msg.textContent = '';
  if(!iso){ msg.textContent = 'เลือกวันที่ของงานก่อน'; return; }
  if(!rows.length){ msg.textContent = 'ยังไม่ได้กรอกงาน'; return; }
  const miss = rows.findIndex(o => !o['ปลายทาง']);
  if(miss >= 0){ msg.textContent = 'แถวที่ ' + (miss + 1) + ' ยังไม่ได้ใส่ปลายทาง'; return; }
  const TAB = String.fromCharCode(9), NL = String.fromCharCode(10), Q = String.fromCharCode(34);
  const q = v => Q + String(v || '').split(Q).join(Q + Q) + Q;              // ครอบทุกช่องด้วย "..." กันข้อความที่มี Tab/เครื่องหมายคำพูด
  document.getElementById('pasteTxt').value = [ADD_F.map(f => f[0]).join(TAB)].concat(rows.map(o => ADD_F.map(f => q(o[f[0]])).join(TAB))).join(NL);
  document.getElementById('pasteDate').value = iso;
  pasteGo();                             // ผลตรวจแสดงใต้ฟอร์ม · แก้ในฟอร์มแล้วกดตรวจใหม่ได้
};
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
<title>Gasbulk Track PTGLG — ติดตามรถขนส่ง</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Noto+Sans+Thai:wght@400;500;600;700&display=swap" rel="stylesheet" crossorigin="anonymous">
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
  <a class="menu" href="/ready">🚦 รถ/คนพร้อมใช้</a>
  <a class="menu" href="/users">👥 ผู้ใช้</a>
  <a class="menu out" href="/logout" title="ออกจากระบบ">🚪<span>ออกจากระบบ</span></a>
</aside>
<header>
  <div class="bar">
    <h1>🚛 Gasbulk Track PTGLG</h1>
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
