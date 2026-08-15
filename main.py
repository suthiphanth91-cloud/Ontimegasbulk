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
import traceback
from datetime import datetime, timedelta
from math import atan2, cos, radians, sin, sqrt
from time import time
from typing import Optional

import httpx
import gspread
from fastapi import FastAPI, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse
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
PLAN_ID      = "1Bl2n1FPPKDIa3FMFpPEyrlzuE296PB0rjPzZtfnJe_U"
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

# Sheet 3: ข้อมูลปลายทาง — พิกัดของแต่ละจุดส่ง (อยู่ในไฟล์เดียวกับแผนงาน)
DEST_ID      = PLAN_ID
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

# คำในคอลัมน์สถานะ GPS ที่แปลว่า "ส่งเสร็จแล้ว" (เพิ่มคำใหม่ได้ที่นี่)
DONE_KEYWORDS = [
    "สำเร็จ", "เสร็จ", "จัดส่งแล้ว", "ส่งแล้ว",
    "ถึงปลายทาง", "ถึงลูกค้า", "delivered", "complete",
]

TZ_OFFSET     = 7    # UTC+7
CACHE_TTL     = 300  # cache Sheet 5 นาที
ETA_CACHE_TTL = 3600  # cache ETA 1 ชม. (ตรงกับรอบไล่รถ + ประหยัดโควตา ORS)

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
            timeout=10,
        )
        resp.raise_for_status()
        secs = resp.json()["routes"][0]["summary"]["duration"]
        return max(1, int(secs) // 60)
    except Exception:
        return None


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
    rows  = _fetch_sheet(PLAN_ID, PLAN_TAB)
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

    results: list[TripOut] = []
    for t in trips:
        sched_mins  = _to_mins(t["sched_time"])
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

        gps_txt = t["gps_status"].lower()
        done    = any(k in gps_txt for k in DONE_KEYWORDS)

        if done:
            # ─ ส่งเสร็จแล้ว ไม่ต้องเรียก ETA (ประหยัดโควตา API) ─
            status     = "arrived"
            prediction = "จัดส่งเสร็จแล้ว"

        elif not is_today:
            # ─ ทริปวันอื่น: ดูสถานะจากชีตอย่างเดียว ไม่คำนวณ ETA ─
            status     = "pending"
            prediction = t["gps_status"] or "ไม่มีข้อมูลสถานะ"

        elif origin and dest_coord:
            # ─ มีตำแหน่ง (GPS หรือคลัง) + พิกัดปลายทาง → คำนวณ ETA ─
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
            # ─ ไม่พบทั้ง PTGL และ DEPOTS → ดูจากเวลากำหนด ─
            if sched_mins and _now_mins() > sched_mins + 20:  # noqa: SIM102
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


@app.get("/api/debug")
def debug():
    """ตรวจทีละขั้น ว่าติดตรงไหน"""
    out: dict = {}

    # 1. env var
    env = os.environ.get("GOOGLE_CREDENTIALS")
    out["has_GOOGLE_CREDENTIALS"] = bool(env)
    out["has_GOOGLE_ROUTES_KEY"]  = bool(os.environ.get("GOOGLE_ROUTES_KEY"))

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
        ("PLAN",   PLAN_ID, PLAN_TAB),
        ("DEST",   DEST_ID, DEST_TAB),
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


@app.get("/api/peek")
def peek():
    """ดูข้อมูลดิบ 5 แถวแรกของแผนงาน เพื่อเช็คว่าคอลัมน์/วันที่ตรงไหม"""
    rows = _fetch_sheet(PLAN_ID, PLAN_TAB)
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
    return DASHBOARD_HTML


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
  .bar{display:flex;flex-wrap:wrap;gap:10px;align-items:center;max-width:1400px;margin:0 auto}
  h1{font-size:19px;margin:0;font-weight:700;letter-spacing:-.2px}
  .grow{flex:1}
  input,button{font-family:inherit;font-size:14px;padding:8px 12px;border-radius:9px;
               border:1px solid var(--line);background:var(--card);color:var(--ink)}
  input[type=search]{min-width:190px}
  button{cursor:pointer;font-weight:600}
  button.primary{background:#2563eb;border-color:#2563eb;color:#fff}
  button.primary:hover{background:#1d4ed8}
  main{max-width:1400px;margin:0 auto;padding:18px}
  .cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:12px;margin-bottom:18px}
  .c{background:var(--card);border:1px solid var(--line);border-radius:13px;padding:14px 16px}
  .c b{display:block;font-size:27px;font-weight:700;line-height:1.15}
  .c span{color:var(--mut);font-size:13px;font-weight:500}
  .c.late b{color:var(--late)} .c.ok b{color:var(--ok)} .c.tr b{color:var(--tr)}
  .wrap{background:var(--card);border:1px solid var(--line);border-radius:13px;overflow-x:auto}
  table{border-collapse:collapse;width:100%;min-width:1080px}
  th,td{padding:11px 13px;text-align:left;border-bottom:1px solid var(--line);white-space:nowrap}
  th{font-size:12.5px;color:var(--mut);font-weight:600;text-transform:uppercase;
     letter-spacing:.4px;position:sticky;top:0;background:var(--card)}
  tbody tr:hover{background:var(--pd-bg)}
  td.wide{white-space:normal;max-width:270px}
  .badge{display:inline-block;padding:3px 11px;border-radius:999px;font-size:12.5px;font-weight:600}
  .s-late{background:var(--late-bg);color:var(--late)}
  .s-arrived{background:var(--ok-bg);color:var(--ok)}
  .s-transit{background:var(--tr-bg);color:var(--tr)}
  .s-early{background:var(--early-bg);color:#0891b2}
  .s-pending{background:var(--pd-bg);color:var(--pd)}
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
  </div>
</header>

<main>
  <div class="cards" id="cards"></div>
  <div class="chips">
    <button class="chip on" data-f="hour">⏰ ต้องไล่ชั่วโมงนี้</button>
    <button class="chip" data-f="late">🔴 ช้า</button>
    <button class="chip" data-f="active">🚚 ยังไม่ถึง</button>
    <button class="chip" data-f="all">ทั้งหมด</button>
  </div>
  <div class="wrap">
    <table>
      <thead><tr>
        <th>เบอร์รถ</th><th>ทะเบียน</th><th>เที่ยว</th><th>Drop</th>
        <th>ลูกค้าปลายทาง</th><th>คลัง</th><th>ปริมาณ</th>
        <th>กำหนด</th><th>ETA</th><th>ต่าง</th><th>สถานะ</th><th>ตำแหน่งปัจจุบัน</th>
      </tr></thead>
      <tbody id="rows"></tbody>
    </table>
  </div>
  <p class="note" id="foot"></p>
</main>

<script>
const LABEL = {late:'ช้า', arrived:'ส่งแล้ว', transit:'กำลังไป', early:'เร็วกว่ากำหนด', pending:'รอออกรถ'};
let ALL = [], DATA = [], FILTER = 'hour';

function todayISO(){
  const d = new Date(Date.now() + (7*60 + new Date().getTimezoneOffset())*60000);
  return d.toISOString().slice(0,10);
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

function loc(t){
  if(t.current_lat == null || t.current_lng == null) return '—';
  const url  = 'https://www.google.com/maps?q=' + t.current_lat + ',' + t.current_lng;
  const text = t.current_loc || (t.current_lat.toFixed(5) + ', ' + t.current_lng.toFixed(5));
  return '<a href="'+url+'" target="_blank" rel="noopener" style="color:var(--tr)">📍 '+esc(text)+'</a>';
}

function mins(hhmm){                  // "14:30" → 870
  const m = /^(\d{1,2}):(\d{2})/.exec(String(hhmm||''));
  return m ? (+m[1])*60 + (+m[2]) : null;
}

function nowMins(){
  const d = new Date(Date.now() + (7*60 + new Date().getTimezoneOffset())*60000);
  return d.getHours()*60 + d.getMinutes();
}

function keep(t){                     // กรองตามชิปที่เลือก
  if(FILTER === 'all')    return true;
  if(FILTER === 'late')   return t.status === 'late';
  if(FILTER === 'active') return t.status !== 'arrived';
  // 'hour' = ต้องจัดการในชั่วโมงนี้: ช้าอยู่แล้ว หรือ ครบกำหนดภายใน 60 นาที
  if(t.status === 'arrived') return false;
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
      const rank = s => ({late:0, transit:1, early:2, pending:3, arrived:4}[s] ?? 5);
      if (rank(a.status) !== rank(b.status)) return rank(a.status) - rank(b.status);
      if (a.status === 'late') return (b.diff_minutes||0) - (a.diff_minutes||0);
      return String(a.sched_time||'').localeCompare(String(b.sched_time||''));
    });

  document.getElementById('rows').innerHTML = list.length ? list.map(t => {
    const diff = t.diff_minutes == null ? '<span class="mut">—</span>'
      : (t.diff_minutes > 0
          ? '<span style="color:var(--late)">+'+dur(t.diff_minutes)+'</span>'
          : '<span style="color:var(--ok)">-'+dur(-t.diff_minutes)+'</span>');
    return '<tr>'
      + '<td><b>'+esc(t.car_no)+'</b></td>'
      + '<td class="mut">'+esc(t.plate)+'</td>'
      + '<td>'+esc(t.trip_no)+'</td>'
      + '<td>'+esc(t.drop)+'</td>'
      + '<td class="wide">'+esc(t.customer)+'</td>'
      + '<td>'+esc(t.source)+'</td>'
      + '<td class="mono">'+esc(t.volume)+'</td>'
      + '<td class="mono">'+esc(t.sched_time)+'</td>'
      + '<td class="mono">'+(t.eta_time ? esc(t.eta_time) : '<span class="mut">—</span>')+'</td>'
      + '<td class="mono">'+diff+'</td>'
      + '<td><span class="badge s-'+esc(t.status)+'">'+(LABEL[t.status]||esc(t.status))+'</span></td>'
      + '<td class="wide mut">'+loc(t)+'</td>'
      + '</tr>';
  }).join('') : '<tr><td colspan="12" class="empty">ไม่พบข้อมูล</td></tr>';

  document.getElementById('foot').textContent =
    'แสดง ' + list.length + ' ทริป (จากทั้งวัน ' + ALL.length + ' ทริป)';
}

async function load(){
  const d  = document.getElementById('date').value || todayISO();
  const el = document.getElementById('rows');
  el.innerHTML = '<tr><td colspan="12" class="empty">กำลังโหลด…</td></tr>';
  try{
    const r = await fetch('/api/trips?date=' + d);
    if(!r.ok) throw new Error((await r.json()).detail || r.statusText);
    const j = await r.json();
    ALL = j.trips || [];
    document.getElementById('cards').innerHTML =
        card(j.total,'ทริปทั้งหมด','')
      + card(j.arrived,'ส่งเสร็จแล้ว','ok')
      + card(j.in_transit,'กำลังเดินทาง','tr')
      + card(j.late,'คาดว่าจะช้า','late')
      + card(j.pending,'รอออกรถ','');
    document.getElementById('stamp').innerHTML =
      '<span class="dot"></span>อัปเดต ' + String(j.fetched_at).slice(11,16) + ' น.';
    render();
  }catch(e){
    el.innerHTML = '<tr><td colspan="12" class="empty">เกิดข้อผิดพลาด: ' + esc(e.message) + '</td></tr>';
  }
}

document.getElementById('date').value = todayISO();
document.getElementById('go').onclick    = load;
document.getElementById('date').onchange = load;
document.getElementById('q').oninput     = render;

document.querySelectorAll('.chip').forEach(b => {
  b.onclick = () => {
    FILTER = b.dataset.f;
    document.querySelectorAll('.chip').forEach(x => x.classList.toggle('on', x === b));
    render();
  };
});

load();
setInterval(load, 60 * 60 * 1000);   // ดึงข้อมูลใหม่ทุก 1 ชั่วโมง (ตรงกับรอบไล่รถ)
</script>
</body>
</html>
"""

# Vercel entry point
handler = app
