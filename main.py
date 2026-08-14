"""
Gasbulk Track API v2
Sources:
  PTGL Sheet         → ตำแหน่งรถ live  (col A=LicenseNO, E=Lat, F=Lng, M=Location)
  แผนงาน Gasbulk     → ทริปประจำวัน   (col C=วันที่, G=เวลากำหนด, M=ปลายทาง, P=เบอร์รถ)
  ข้อมูลปลายทาง      → พิกัดปลายทาง   (col A=ชื่อ ตรงกับแผนงาน M, col G=lat,lng)
  Google Routes API  → ETA จริงพร้อม traffic → รู้ล่วงหน้าว่าจะช้ากี่นาที
"""

from __future__ import annotations

import json
import os
import re
from datetime import datetime, timedelta
from time import time
from typing import Optional

import httpx
import gspread
from fastapi import FastAPI, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware
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

# Sheet 2: แผนงาน Gasbulk — ตารางทริปประจำวัน
PLAN_ID      = "1bwBmxGy1mlnAEIUm5ZNNV71tud3NCyPZlHesIwP4tUs"
PLAN_TAB     = "แผนงาน Gasbulk"
PLAN_DATE    = 2   # C  วันที่
PLAN_SCHED   = 6   # G  เวลากำหนดส่ง (HH:MM)
PLAN_TRIP    = 4   # E  เที่ยววิ่ง
PLAN_INVOICE = 7   # H  เลขที่ใบกำกับ
PLAN_VOLUME  = 9   # J  ปริมาณ
PLAN_SOURCE  = 11  # L  คลังต้นทาง
PLAN_DEST    = 12  # M  ลูกค้าปลายทาง  ← จับคู่กับ ข้อมูลปลายทาง col A
PLAN_DROP    = 13  # N  Drop
PLAN_CARNO   = 15  # P  เบอร์รถ         ← จับคู่กับ PTGL LicenseNO
PLAN_PLATE   = 17  # R  ทะเบียน
PLAN_GPS_ST  = 33  # AH สถานะ GPS

# Sheet 3: ข้อมูลปลายทาง — พิกัดของแต่ละจุดส่ง
DEST_TAB     = "ข้อมูลปลายทาง"
DEST_NAME    = 0   # A  ชื่อปลายทาง (ตรงกับ PLAN_DEST)
DEST_COORD   = 7   # H  พิกัด "lat,lng"  ← col H (แก้จาก G)

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

TZ_OFFSET     = 7    # UTC+7
CACHE_TTL     = 300  # cache Sheet 5 นาที
ETA_CACHE_TTL = 600  # cache Routes API 10 นาที (ลดค่าใช้จ่าย)

SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets.readonly",
    "https://www.googleapis.com/auth/drive.readonly",
]

# ─── APP ─────────────────────────────────────────────────────────────────────

app = FastAPI(
    title="Gasbulk Track API",
    description="ติดตามรถ Gasbulk — รู้ล่วงหน้าว่าจะถึงช้าหรือเร็ว",
    version="2.0.0",
)
app.add_middleware(
    CORSMiddleware, allow_origins=["*"], allow_methods=["GET"], allow_headers=["*"]
)

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
    gps_status:   str           # สถานะจาก Sheet
    # ตำแหน่งปัจจุบัน (จาก PTGL)
    current_lat:  Optional[float] = None
    current_lng:  Optional[float] = None
    current_loc:  Optional[str]   = None
    # ETA (จาก Routes API)
    travel_mins:  Optional[int]   = None   # นาทีจากตำแหน่งปัจจุบัน → ปลายทาง
    eta_time:     Optional[str]   = None   # เวลาถึงโดยประมาณ "HH:MM"
    # สรุป
    status:       str                      # early|ontime|late|transit|pending|arrived
    diff_minutes: Optional[int]   = None   # บวก=ช้า  ลบ=เร็ว
    prediction:   str             = ""     # ข้อความอ่านง่าย

class SummaryResponse(BaseModel):
    date:       str
    fetched_at: str
    total:      int
    arrived:    int
    in_transit: int
    late:       int
    pending:    int
    trips:      list[TripOut]

# ─── CACHE ───────────────────────────────────────────────────────────────────

_sheet_cache: dict[str, tuple[float, list]] = {}
_eta_cache:   dict[str, tuple[float, int]]  = {}

# ─── UTILITIES ───────────────────────────────────────────────────────────────

def _build_creds() -> Credentials:
    env = os.environ.get("GOOGLE_CREDENTIALS")
    if env:
        return Credentials.from_service_account_info(json.loads(env), scopes=SCOPES)
    local = os.path.join(os.path.dirname(__file__), "..", "credentials.json")
    return Credentials.from_service_account_file(local, scopes=SCOPES)


def _fetch_sheet(sheet_id: str, tab: str) -> list[list]:
    """อ่าน Sheet พร้อม cache 5 นาที"""
    key = f"{sheet_id}:{tab}"
    if key in _sheet_cache:
        ts, data = _sheet_cache[key]
        if time() - ts < CACHE_TTL:
            return data
    gc   = gspread.authorize(_build_creds())
    data = gc.open_by_key(sheet_id).worksheet(tab).get_all_values()
    _sheet_cache[key] = (time(), data)
    return data


def _cell(row: list, idx: int) -> str:
    return str(row[idx]).strip() if idx < len(row) else ""


def _extract_car_no(ptgl_license: str) -> str:
    """'No.465(63-3530)' → '465'  ใช้จับคู่กับ เบอร์รถ ในแผนงาน"""
    m = re.search(r"No\.?0*(\d+)", ptgl_license, re.IGNORECASE)
    return m.group(1) if m else re.sub(r"\D", "", ptgl_license)


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
    for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%m/%d/%Y", "%d/%m/%Y %H:%M:%S", "%Y-%m-%d %H:%M:%S"):
        try:
            return datetime.strptime(raw.strip().split(" ")[0], fmt.split(" ")[0]).strftime("%Y-%m-%d")
        except ValueError:
            continue
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

# ─── GOOGLE ROUTES API ───────────────────────────────────────────────────────

def _get_travel_minutes(
    orig_lat: float, orig_lng: float,
    dest_lat: float, dest_lng: float,
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

    api_key = os.environ.get("GOOGLE_ROUTES_KEY")
    if not api_key:
        return None  # ถ้าไม่มี key ข้าม Routes API

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
        return None

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
    rows   = _fetch_sheet(PLAN_ID, DEST_TAB)
    result: dict[str, tuple[float, float]] = {}
    for row in rows[1:]:
        name  = _cell(row, DEST_NAME)
        coord = _parse_coords(_cell(row, DEST_COORD))
        if name and coord:
            result[name] = coord
    return result


def fetch_trips(target_date: str) -> list[dict]:
    """คืนรายการทริปทั้งหมดของวันที่ระบุ"""
    rows  = _fetch_sheet(PLAN_ID, PLAN_TAB)
    trips = []
    for i, row in enumerate(rows[1:], start=1):
        if _parse_date(_cell(row, PLAN_DATE)) != target_date:
            continue
        car_no = _cell(row, PLAN_CARNO)
        car_no = car_no.lstrip("0") or car_no   # ตัด 0 นำหน้า เช่น "0465" → "465"
        trips.append({
            "id":         i,
            "car_no":     car_no,
            "plate":      _cell(row, PLAN_PLATE),
            "trip_no":    _cell(row, PLAN_TRIP),
            "drop":       _cell(row, PLAN_DROP),
            "customer":   _cell(row, PLAN_DEST),
            "source":     _cell(row, PLAN_SOURCE),
            "volume":     _cell(row, PLAN_VOLUME),
            "invoice_no": _cell(row, PLAN_INVOICE),
            "sched_time": _cell(row, PLAN_SCHED),
            "gps_status": _cell(row, PLAN_GPS_ST),
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
        raise HTTPException(502, f"ดึงข้อมูล Google Sheet ไม่ได้: {e}")

    results: list[TripOut] = []
    for t in trips:
        sched_mins  = _to_mins(t["sched_time"])
        pos         = ptgl_map.get(t["car_no"])
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

        if origin and dest_coord:
            # ─ มีตำแหน่ง (GPS หรือคลัง) + พิกัดปลายทาง → เรียก Routes API ─
            travel = _get_travel_minutes(
                origin["lat"], origin["lng"],
                dest_coord[0], dest_coord[1],
            )
            if travel is not None and sched_mins is not None:
                travel_mins  = travel
                eta_total    = _now_mins() + travel
                eta_time_str = _mins_to_hhmm(eta_total)
                diff_min     = eta_total - sched_mins

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
            # ─ ไม่พบทั้ง PTGL และ DEPOTS → ดูจาก GPS status ใน Sheet ─
            g = t["gps_status"].lower()
            if any(k in g for k in ["ถึง", "เสร็จ", "จัดส่งแล้ว", "delivered"]):
                status     = "arrived"
                prediction = "จัดส่งเสร็จแล้ว"
            elif sched_mins and _now_mins() > sched_mins + 20:
                status     = "late"
                prediction = "⚠ เกินเวลากำหนดแล้ว (ไม่พบสัญญาณ GPS)"
            else:
                status     = "pending"
                prediction = "รอออกรถ"

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
            gps_status   = t["gps_status"],
            current_lat  = pos["lat"]      if pos else None,
            current_lng  = pos["lng"]      if pos else None,
            current_loc  = pos["location"] if pos else None,
            travel_mins  = travel_mins,
            eta_time     = eta_time_str,
            status       = status,
            diff_minutes = diff_min,
            prediction   = prediction,
        ))

    arrived    = sum(1 for r in results if r.status == "arrived")
    in_transit = sum(1 for r in results if r.status in ("transit", "early"))
    late       = sum(1 for r in results if r.status == "late")
    pending    = sum(1 for r in results if r.status == "pending")

    return SummaryResponse(
        date       = target,
        fetched_at = _thai_now().strftime("%Y-%m-%dT%H:%M:%S+07:00"),
        total      = len(results),
        arrived    = arrived,
        in_transit = in_transit,
        late       = late,
        pending    = pending,
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


# Vercel entry point
handler = app
