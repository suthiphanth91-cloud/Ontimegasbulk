"""
Gasbulk Track — Python Backend (FastAPI)
อ่านข้อมูลทริปรถจาก Google Sheets แล้วส่งเป็น REST API
"""

from __future__ import annotations

import os
from datetime import date, datetime, timedelta
from typing import List, Optional

import gspread
from fastapi import FastAPI, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware
from google.oauth2.service_account import Credentials
from pydantic import BaseModel

# ─── CONFIG ──────────────────────────────────────────────────────────────────

SHEET_ID    = "1Bl2n1FPPKDIa3FMFpPEyrlzuE296PB0rjPzZtfnJe_U"
SHEET_NAME  = "แผนงาน Gasbulk"
CREDS_FILE  = os.getenv("GOOGLE_CREDS_JSON", "credentials.json")
TZ_OFFSET   = 7   # UTC+7 ไทย

SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets.readonly",
    "https://www.googleapis.com/auth/drive.readonly",
]

# คอลัมน์ใน Sheet (0-based index เหมือน Apps Script เดิม)
COL = {
    "date":     2,   # C  — วันที่
    "source":   11,  # L  — คลังต้นทาง
    "trip":     4,   # E  — เที่ยววิ่ง
    "drop":     13,  # N  — Drop
    "customer": 12,  # M  — ลูกค้าปลายทาง
    "car_no":   15,  # P  — เบอร์รถ
    "plate":    17,  # R  — ทะเบียน
    "volume":   9,   # J  — ปริมาณ
    "sched_time": 6, # G  — เวลากำหนด
    "invoice":  7,   # H  — เลขที่ใบกำกับ
    "gps_status": 33,# AH — สถานะ GPS
}

# ─── APP ─────────────────────────────────────────────────────────────────────

app = FastAPI(
    title="Gasbulk Track API",
    description="API สำหรับติดตามสถานะรถ Gasbulk",
    version="1.0.0",
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],   # เปลี่ยนเป็น domain จริงก่อน deploy
    allow_methods=["GET"],
    allow_headers=["*"],
)

# ─── MODELS ──────────────────────────────────────────────────────────────────

class Trip(BaseModel):
    id:           int
    date:         str          # yyyy-MM-dd
    source:       str          # คลังต้นทาง
    trip_no:      str          # เที่ยววิ่ง
    drop:         str
    customer:     str          # ลูกค้าปลายทาง
    car_no:       str          # เบอร์รถ
    plate:        str          # ทะเบียน
    volume:       str          # ปริมาณ
    sched_time:   str          # เวลากำหนด  "HH:MM"
    invoice_no:   str          # เลขที่ใบกำกับ
    gps_status:   str          # สถานะ GPS จาก Sheet
    status:       str          # early | ontime | late | transit | pending
    actual_time:  Optional[str] = None  # เวลาถึงจริง (ถ้ามี)
    diff_minutes: Optional[int] = None  # บวก=ช้า, ลบ=เร็ว

class TripsResponse(BaseModel):
    date:        str
    fetched_at:  str
    total:       int
    arrived:     int
    in_transit:  int
    late:        int
    pending:     int
    trips:       List[Trip]

# ─── GOOGLE SHEETS ───────────────────────────────────────────────────────────

def _open_sheet() -> gspread.Worksheet:
    creds = Credentials.from_service_account_file(CREDS_FILE, scopes=SCOPES)
    gc    = gspread.authorize(creds)
    return gc.open_by_key(SHEET_ID).worksheet(SHEET_NAME)


def _get(row: list, col_name: str) -> str:
    idx = COL[col_name]
    return str(row[idx]).strip() if idx < len(row) else ""


def _parse_time(val: str) -> Optional[int]:
    """แปลง 'HH:MM' หรือ 'H:MM' เป็นนาทีนับจากเที่ยงคืน"""
    if not val or ":" not in val:
        return None
    try:
        h, m = val.split(":")[:2]
        return int(h) * 60 + int(m)
    except ValueError:
        return None


def _infer_status(gps: str, sched_mins: Optional[int]) -> tuple[str, Optional[int]]:
    """
    คำนวณ status จาก GPS status ที่มีใน Sheet
    กฎง่ายๆ: ปรับตาม keyword ใน gps_status
    (เมื่อเชื่อมข้อมูลจริงให้ปรับ logic ตามรูปแบบข้อความใน AH)
    """
    g = gps.lower()

    if any(k in g for k in ["ถึงแล้ว", "จัดส่งแล้ว", "เสร็จ", "delivered"]):
        # คำนวณเร็ว/ช้าจากเวลากำหนด ถ้ามีข้อมูลเวลาถึงใน GPS string
        return "ontime", None   # TODO: parse actual time จาก GPS string

    if any(k in g for k in ["กำลัง", "เดินทาง", "ออกแล้ว", "moving", "on route"]):
        if sched_mins is None:
            return "transit", None
        now_mins = _now_thai_mins()
        if now_mins > sched_mins:
            return "late", now_mins - sched_mins
        return "transit", None

    # ยังไม่ออก
    return "pending", None


def _now_thai_mins() -> int:
    utc = datetime.utcnow()
    thai = utc + timedelta(hours=TZ_OFFSET)
    return thai.hour * 60 + thai.minute


def _today_thai() -> str:
    utc = datetime.utcnow()
    thai = utc + timedelta(hours=TZ_OFFSET)
    return thai.strftime("%Y-%m-%d")

# ─── ENDPOINTS ───────────────────────────────────────────────────────────────

@app.get("/trips", response_model=TripsResponse, summary="ดึงทริปตามวันที่")
def get_trips(
    date_str: str = Query(
        default=None,
        alias="date",
        description="วันที่ในรูปแบบ yyyy-MM-dd (ค่าเริ่มต้น = วันนี้)",
        example="2025-08-14",
    )
):
    target = date_str or _today_thai()
    try:
        datetime.strptime(target, "%Y-%m-%d")
    except ValueError:
        raise HTTPException(status_code=400, detail="รูปแบบวันที่ต้องเป็น yyyy-MM-dd")

    try:
        ws   = _open_sheet()
        rows = ws.get_all_values()
    except Exception as e:
        raise HTTPException(status_code=502, detail=f"เปิด Google Sheet ไม่ได้: {e}")

    trips: List[Trip] = []
    for i, row in enumerate(rows[1:], start=1):   # ข้าม header
        # ตรวจสอบวันที่คอลัมน์ C
        raw_date = _get(row, "date")
        cell_date = None
        for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%m/%d/%Y"):
            try:
                cell_date = datetime.strptime(raw_date, fmt).strftime("%Y-%m-%d")
                break
            except ValueError:
                continue
        if cell_date != target:
            continue

        sched_str  = _get(row, "sched_time")
        sched_mins = _parse_time(sched_str)
        gps_status = _get(row, "gps_status")
        status, diff_min = _infer_status(gps_status, sched_mins)

        trips.append(Trip(
            id           = i,
            date         = cell_date,
            source       = _get(row, "source"),
            trip_no      = _get(row, "trip"),
            drop         = _get(row, "drop"),
            customer     = _get(row, "customer"),
            car_no       = _get(row, "car_no"),
            plate        = _get(row, "plate"),
            volume       = _get(row, "volume"),
            sched_time   = sched_str,
            invoice_no   = _get(row, "invoice"),
            gps_status   = gps_status,
            status       = status,
            diff_minutes = diff_min,
        ))

    arrived   = sum(1 for t in trips if t.status in ("early", "ontime"))
    in_transit= sum(1 for t in trips if t.status == "transit")
    late      = sum(1 for t in trips if t.status == "late")
    pending   = sum(1 for t in trips if t.status == "pending")

    return TripsResponse(
        date        = target,
        fetched_at  = datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
        total       = len(trips),
        arrived     = arrived,
        in_transit  = in_transit,
        late        = late,
        pending     = pending,
        trips       = trips,
    )


@app.get("/health", summary="Health check")
def health():
    return {"status": "ok", "time": datetime.utcnow().isoformat()}
