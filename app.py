"""
DealFinder — ETA Business Listing Triage Tool
Scrapes BizBuySell and BizQuest using Playwright, scores deals against
ETA acquisition criteria, and surfaces them in a Streamlit dashboard.

Usage:  streamlit run app.py
"""

import streamlit as st
import pandas as pd
import re
import time
import json
import random
import pathlib
import concurrent.futures
import uuid
import urllib.parse
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from datetime import datetime, timedelta
from streamlit_autorefresh import st_autorefresh
try:
    import gspread
    from google.oauth2.service_account import Credentials as GCredentials
    _GSPREAD_AVAILABLE = True
except ImportError:
    _GSPREAD_AVAILABLE = False


SESSION_DIR = pathlib.Path.home() / ".dealfinder_sessions"
SESSION_DIR.mkdir(exist_ok=True)

# BizBuySell BFF API — confirmed from DevTools (POST, Bearer JWT)
_BBS_BFF_URL       = "https://www.bizbuysell.com/_api/bff/v2/BbsBfsSearchResults"
_BBS_REGIONS_URL   = "https://www.bizbuysell.com/_api/resource/v2/Regions"
_BBS_JWT_FILE      = SESSION_DIR / "bizbuysell_jwt.txt"
_BBS_REGIONS_CACHE = SESSION_DIR / "bizbuysell_regions_cache.json"
_PIPELINE_FILE     = SESSION_DIR / "pipeline.json"
_LAST_AUTO_SCAN    = SESSION_DIR / "last_auto_scan.txt"

PIPELINE_STAGES = [
    "New", "Researching", "Outreach Drafted", "Broker Contacted",
    "Qualification Call", "CIM / Financials Received", "Financials Validated",
    "LOI Submitted", "Due Diligence", "Pass", "Closed",
]

# ─────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────

SELECTORS = {
    "card":        ".listing",
    "title":       ".title",
    "asking":      ".asking-price",
    "cash_flow":   ".cash-flow-on-mobile, .cash-flow",
    "location":    ".location",
    "description": ".description",
    "finance":     ".finance",
    "category":    ".category",          # business type label
}

# State → URL param per source
STATE_PARAMS = {
    "BizBuySell": {
        "South Carolina": "state=South+Carolina",
        "North Carolina":  "state=North+Carolina",
        "Georgia":         "state=Georgia",
        "Virginia":        "state=Virginia",
        "Tennessee":       "state=Tennessee",
        "Florida":         "state=Florida",
    },
    "BizQuest": {
        "South Carolina": "stateId=SC",
        "North Carolina":  "stateId=NC",
        "Georgia":         "stateId=GA",
        "Virginia":        "stateId=VA",
        "Tennessee":       "stateId=TN",
        "Florida":         "stateId=FL",
    },
}

SOURCES = {
    "BizBuySell": {
        "url":        "https://www.bizbuysell.com/businesses-for-sale/",
        "login_url":  "https://www.bizbuysell.com/users/Login.aspx",
        "logged_in_url_fragment": "/mybbs",   # URL contains this after successful login
        "base_url":   "https://www.bizbuysell.com",
        "user_sel":   "#ctl00_ctl00_Content_ContentPlaceHolder1_LoginControl_txtUserName",
        "pass_sel":   "#ctl00_ctl00_Content_ContentPlaceHolder1_LoginControl_txtPassword",
        "submit_sel": "input[type='submit']",
    },
    "BizQuest": {
        "url":        "https://www.bizquest.com/businesses-for-sale/",
        "login_url":  "https://www.bizquest.com/Login/Index/",
        "logged_in_url_fragment": "/myaccount",
        "base_url":   "https://www.bizquest.com",
        "user_sel":   "input[name='email']",
        "pass_sel":   "input[name='password']",
        "submit_sel": "button[type='submit']",
    },
}

RED_FLAG_KEYWORDS = [
    "motivated seller", "priced to sell", "tremendous upside potential",
    "cash only", "turnkey", "turn-key", "no experience needed",
    "absentee", "semi-absentee", "work from home", "e-commerce",
    "online only", "seller will train", "new ownership opportunity",
    "e-2 visa", "visa friendly",
    "amazon fba", "dropship", "passive income", "content creator",
    "currently paused", "listing is paused",
    # Revenue quality red flags
    "project-based", "project based", "bid work", "per-bid", "per bid",
    "government contract", "municipal contract", "dod contract",
    "federal contract", "single customer", "one customer",
    "one major client", "largest customer",
]

QUALITY_KEYWORDS = [
    "recurring", "service contract", "repeat customer", "long-term contract",
    "management team", "manager in place", "b2b", "commercial",
    "essential", "maintenance contract", "annual contract",
    "established clientele", "tenured staff", "niche",
    "preventive maintenance", "inspection contract", "licensed and insured",
    "tenured technician", "certified technician",
]

# HALO tier score adjustments by derived business_type.
# Positive = HALO-aligned, defensible, SBA-friendly exit story.
# Negative = non-HALO, high disruption risk, or poor IS exit story.
_HALO_SCORE: dict[str, int] = {
    # Tier 1 — highest priority
    "HVAC":                       20,
    "Fire Protection":            20,
    # Tier 2 — solid but one key risk each
    "Plumbing":                   12,
    "Electrical":                 12,
    "Environmental / Industrial": 12,
    "Pest Control":               12,
    "Commercial Cleaning":        10,
    # Tier 3 — acceptable; lower multiple / thinner exit
    "Marine Services":             6,
    "Landscaping":                 6,
    "Pool Services":               6,
    "Roofing":                     6,
    "Construction":                4,
    "Security":                    4,
    "Specialty Distribution":      0,
    "Commercial Laundry":          0,
    "Self-Storage":                0,
    # Below-average HALO — not disqualifying but drag the score
    "Auto Services":              -5,
    "Healthcare / Med Spa":       -5,
    "Insurance":                 -10,
    "Technology / IT":           -10,
    "Staffing / Services":       -10,
    # Non-HALO — project-based, high failure, or disruption risk
    "Transportation / Routes":   -25,   # FedEx / UPS routes — contract-dependent
    "Restaurant / Food":         -25,   # high failure rate, not HALO
    "Retail":                    -25,   # price-sensitive, disruptible
    "Event / Hospitality":       -20,   # seasonal, discretionary
    "Fuel / Petroleum":          -15,   # ESG headwinds, lender scrutiny
}

# Ordered: first match wins. Keep specific phrases before generic ones.
_INDUSTRY_MAP: list[tuple[str, list[str]]] = [
    ("HVAC",                ["hvac", "air conditioning", "heating & cooling", "heating and cooling",
                             "refrigeration", "mechanical contractor"]),
    ("Fire Protection",     ["fire protection", "fire sprinkler", "fire suppression",
                             "fire alarm", "fire safety"]),
    ("Plumbing",            ["plumbing", "plumber", "drain cleaning", "sewer", "pipe"]),
    ("Electrical",          ["electrical contractor", "electrician", "electric contractor"]),
    ("Roofing",             ["roofing", "roofer", " roof "]),
    ("Pest Control",        ["pest control", "exterminator", "pest management", "termite"]),
    ("Landscaping",         ["landscaping", "lawn care", "lawn service", "grounds maintenance",
                             "irrigation", "tree service", "arborist"]),
    ("Environmental / Industrial", ["environmental", "industrial cleaning", "industrial service",
                             "remediation", "hazmat", "tank cleaning"]),
    ("Commercial Cleaning", ["commercial cleaning", "janitorial", "cleaning service",
                             "pressure washing", "window cleaning"]),
    ("Self-Storage",        ["self-storage", "self storage", "storage facility", "storage units"]),
    ("Marine Services",     ["marine service", "marina", "boat repair", "yacht", "watercraft",
                             "dock", "maritime"]),
    ("Fuel / Petroleum",    ["fuel distribution", "petroleum", "oil distribution", "propane",
                             "diesel", "fuel delivery"]),
    ("Commercial Laundry",  ["commercial laundry", "linen service", "dry cleaning", "laundromat"]),
    ("Security",            ["security service", "security company", "alarm system",
                             "security design", "security monitoring"]),
    ("Specialty Distribution", ["distribution", "distributor", "wholesale", "supply chain",
                             "industrial supply"]),
    ("Transportation / Routes", ["fedex", "ups", "amazon", "routes", "trucking", "logistics",
                             "freight", "courier", "delivery route"]),
    ("Restaurant / Food",   ["restaurant", "bar and grill", "bar & grill", "cafe", "eatery",
                             "food service", "pizzeria", "diner", "brewery"]),
    ("Retail",              ["retail", "store", "shop", "boutique", "clothing"]),
    ("Healthcare / Med Spa",["medical", "dental", "med spa", "medspa", "healthcare",
                             "clinic", "therapy", "chiropractic", "optometry"]),
    ("Construction",        ["construction", "remodeling", "renovation", "contractor",
                             "home builder", "painting contractor", "flooring",
                             "countertop", "concrete", "gutter", "shutter", "blinds"]),
    ("Pool Services",       ["pool construction", "pool service", "pool & spa", "pool and spa"]),
    ("Auto Services",       ["auto repair", "automotive", "car wash", "auto body", "mechanic"]),
    ("Insurance",           ["insurance agency", "insurance broker"]),
    ("Staffing / Services", ["staffing", "recruiting", "temp agency"]),
    ("Technology / IT",     ["it service", "managed service", "tech support", "software",
                             "digital marketing", "av contractor", "audio visual"]),
    ("Event / Hospitality", ["wedding venue", "event venue", "event center", "hotel", "hospitality"]),
]

PRESET_INDUSTRY_KEYWORDS: list[str] = [
    "HVAC", "Fire Protection", "Plumbing", "Electrical", "Roofing",
    "Pest Control", "Landscaping", "Environmental / Industrial",
    "Commercial Cleaning", "Self-Storage", "Marine Services",
    "Fuel / Petroleum", "Commercial Laundry", "Security",
    "Specialty Distribution", "Transportation / Routes",
    "Construction", "Pool Services", "Auto Services",
]

def _derive_business_type(title: str, description: str = "") -> str:
    """Derive a human-readable industry label from listing text."""
    text = (title + " " + description).lower()
    for label, keywords in _INDUSTRY_MAP:
        if any(kw in text for kw in keywords):
            return label
    return ""

# Cities/markers per state for location confirmation
STATE_LOCATION_MARKERS = {
    "South Carolina": [
        ", SC", "South Carolina", "Charleston", "Columbia", "Greenville",
        "Spartanburg", "Myrtle Beach", "Rock Hill", "Hilton Head", "Florence",
        "Sumter", "Beaufort", "Mount Pleasant", "North Charleston",
        "Goose Creek", "Summerville", "Lexington",
    ],
    "North Carolina": [
        ", NC", "North Carolina", "Charlotte", "Raleigh", "Durham",
        "Greensboro", "Winston-Salem", "Fayetteville", "Asheville",
        "Wilmington", "Cary", "High Point",
    ],
    "Georgia": [
        ", GA", "Georgia", "Atlanta", "Augusta", "Columbus", "Savannah",
        "Athens", "Macon", "Roswell", "Albany",
    ],
    "Virginia": [
        ", VA", "Virginia", "Virginia Beach", "Norfolk", "Chesapeake",
        "Richmond", "Newport News", "Alexandria", "Hampton", "Roanoke",
    ],
    "Tennessee": [
        ", TN", "Tennessee", "Memphis", "Nashville", "Knoxville",
        "Chattanooga", "Clarksville", "Murfreesboro", "Jackson",
    ],
    "Florida": [
        ", FL", "Florida", "Jacksonville", "Miami", "Tampa", "Orlando",
        "St. Petersburg", "Hialeah", "Tallahassee", "Fort Lauderdale",
    ],
}


# ─────────────────────────────────────────────
# UTILITIES
# ─────────────────────────────────────────────

def parse_currency(text: str) -> float | None:
    if not text:
        return None
    text = str(text).strip().upper()
    if "SIGN IN" in text or "N/A" in text or "NOT" in text:
        return None
    mult = 1
    if text.endswith("M"):
        mult, text = 1_000_000, text[:-1]
    elif text.endswith("K"):
        mult, text = 1_000, text[:-1]
    text = re.sub(r"[^\d.]", "", text)
    try:
        return float(text) * mult if text else None
    except ValueError:
        return None


def extract_currency_from_text(label: str, text: str) -> float | None:
    pattern = rf"{label}[:\s]+\$?([\d,\.]+\s*[MKmk]?)"
    m = re.search(pattern, text, re.IGNORECASE)
    return parse_currency(m.group(1)) if m else None


def is_target_location(location: str, selected_states: list[str]) -> bool:
    if not location:
        return False
    loc_lower = location.lower()
    for state in selected_states:
        markers = STATE_LOCATION_MARKERS.get(state, [])
        if any(m.lower() in loc_lower for m in markers):
            return True
    return False


# ─────────────────────────────────────────────
# OUTREACH
# ─────────────────────────────────────────────

def fetch_listing_broker(url: str, listing: dict | None = None) -> dict:
    """Return broker contact info for a listing.

    Uses fields already captured from the BFF search response when available.
    BizBuySell's Kasada protection blocks HTML page requests, so we do not
    attempt a live HTTP fetch of the listing page.
    """
    broker: dict = {}

    if listing:
        if listing.get("broker_name"):    broker["name"]      = listing["broker_name"]
        if listing.get("brokerage_name"): broker["brokerage"] = listing["brokerage_name"]
        if listing.get("broker_phone"):   broker["phone"]     = listing["broker_phone"]
        if listing.get("broker_email"):   broker["email"]     = listing["broker_email"]

    return broker


def draft_outreach(listing: dict, broker: dict) -> str:
    """Return a personalized CIM-request message for a listing."""
    btype    = listing.get("business_type") or "service business"
    title    = listing.get("title") or "your listed business"
    price    = listing.get("asking_price")
    price_s  = f"${price:,.0f}" if price else "the listed price"
    location = listing.get("location") or "the listed area"

    name_parts = (broker.get("name") or "").split()
    first_name = name_parts[0] if name_parts else ""
    greeting   = f"Hi {first_name}," if first_name else "Hi,"

    return f"""{greeting}

My name is [YOUR NAME]. I'm an independent buyer actively searching for \
owner-operated businesses to acquire in the Southeast, with a focus on \
essential-service companies in the {btype.lower()} sector.

I came across your listing for {title} ({price_s}, {location}) and believe \
it could be a strong fit for what I'm looking for — specifically, businesses \
with stable, recurring revenue, a tenured workforce, and a clear path to SBA \
7(a) financing.

To evaluate efficiently, could you share the following?

  1. Confidential Information Memorandum (CIM) or business summary
  2. Last 3 years of business tax returns
  3. Most recent P&L and balance sheet (YTD preferred)
  4. Brief overview of customer/client concentration and any key contracts

Happy to sign your NDA upfront.

Would you have 20 minutes for a call this week?

Thank you,
[YOUR NAME]
[YOUR PHONE]
[YOUR EMAIL]"""


# ─────────────────────────────────────────────
# PIPELINE HELPERS
# ─────────────────────────────────────────────

def _get_gsheet():
    """Return (worksheet, error_str). worksheet is None if connection failed."""
    if not _GSPREAD_AVAILABLE:
        return None, "gspread not installed"
    try:
        creds = GCredentials.from_service_account_info(
            st.secrets["gcp_service_account"],
            scopes=[
                "https://spreadsheets.google.com/feeds",
                "https://www.googleapis.com/auth/drive",
            ],
        )
        client = gspread.authorize(creds)
        sheet = client.open_by_url(st.secrets["sheets"]["pipeline_url"]).sheet1
        return sheet, None
    except Exception as e:
        return None, str(e)

def load_pipeline() -> dict:
    sheet, err = _get_gsheet()
    if err:
        st.session_state["_gsheet_error"] = err
    if sheet is not None:
        st.session_state.pop("_gsheet_error", None)
        try:
            rows = sheet.get_all_records()
            pipeline = {}
            for row in rows:
                key = row.get("key", "")
                if not key:
                    continue
                try:
                    listing = json.loads(row.get("listing_json") or "{}")
                except Exception:
                    listing = {}
                pipeline[key] = {
                    "stage":        row.get("stage", "New"),
                    "notes":        row.get("notes", ""),
                    "date_added":   row.get("date_added", ""),
                    "date_updated": row.get("date_updated", ""),
                    "listing":      listing,
                }
            return pipeline
        except Exception as e:
            st.session_state["_gsheet_error"] = str(e)
    # Fallback: local file (dev / offline)
    if _PIPELINE_FILE.exists():
        try:
            return json.loads(_PIPELINE_FILE.read_text())
        except Exception:
            return {}
    return {}

def save_pipeline(pipeline: dict) -> None:
    sheet, _ = _get_gsheet()
    if sheet is not None:
        try:
            sheet.clear()
            rows = [["key", "stage", "notes", "date_added", "date_updated", "listing_json"]]
            for key, entry in pipeline.items():
                listing_json = json.dumps(entry.get("listing", {}), default=str)
                if len(listing_json) > 45000:
                    listing_json = listing_json[:45000]
                rows.append([
                    key,
                    entry.get("stage", "New"),
                    entry.get("notes", ""),
                    entry.get("date_added", ""),
                    entry.get("date_updated", ""),
                    listing_json,
                ])
            sheet.append_rows(rows, value_input_option="RAW")
            return
        except Exception:
            pass
    # Fallback: local file
    _PIPELINE_FILE.write_text(json.dumps(pipeline, indent=2, default=str))

def pipeline_key(listing: dict) -> str:
    return str(listing.get("listing_id") or listing.get("url") or listing.get("title", ""))

def pipeline_add(listing: dict) -> bool:
    """Add listing to pipeline. Returns True if newly added."""
    pipeline = load_pipeline()
    key = pipeline_key(listing)
    if not key or key in pipeline:
        return False
    pipeline[key] = {
        "stage":        "New",
        "notes":        "",
        "date_added":   datetime.now().strftime("%Y-%m-%d"),
        "date_updated": datetime.now().strftime("%Y-%m-%d"),
        "listing":      listing,
    }
    save_pipeline(pipeline)
    return True

def pipeline_update(key: str, stage: str | None = None, notes: str | None = None) -> None:
    pipeline = load_pipeline()
    if key not in pipeline:
        return
    if stage is not None:
        pipeline[key]["stage"] = stage
    if notes is not None:
        pipeline[key]["notes"] = notes
    pipeline[key]["date_updated"] = datetime.now().strftime("%Y-%m-%d")
    save_pipeline(pipeline)


def _quick_bullets(description: str, n: int = 5) -> list[str]:
    """Extract the n most informative sentences from a listing description."""
    import re
    if not description or len(description) < 40:
        return []
    sents = re.split(r'(?<=[.!?])\s+', description.strip())
    _FILLER = {"don't miss", "opportunity of a lifetime", "priced to sell", "must see",
               "contact us today", "inquire today", "serious buyers only", "asking price is"}
    scored = []
    for s in sents:
        s = s.strip()
        if len(s) < 25:
            continue
        sl = s.lower()
        if any(f in sl for f in _FILLER):
            continue
        pts = 0
        if re.search(r'\$[\d,]+|\d[\d,]*\s*(year|yr|employee|staff|location|truck|vehicle|contract)', sl):
            pts += 3
        if any(w in sl for w in ("established", "founded", "operating since", "in business",
                                  "recurring", "contract", "route", "client", "customer")):
            pts += 2
        if any(w in sl for w in ("licensed", "certified", "insured", "service area", "territory",
                                  "fleet", "equipment", "commercial", "residential", "revenue")):
            pts += 1
        scored.append((pts, s))
    scored.sort(key=lambda x: -x[0])
    return [s for _, s in scored[:n]]


def fmt_k(v) -> str:
    """Format a dollar value as $K / $M for compact metric tiles."""
    if v is None:
        return "—"
    try:
        v = float(v)
    except (TypeError, ValueError):
        return "—"
    if v >= 1_000_000:
        return f"${v / 1_000_000:.1f}M"
    if v >= 1_000:
        return f"${v / 1_000:.0f}K"
    return f"${v:,.0f}"


def _run_ts() -> str:
    """Return a compact timestamp like 'Mar 18 · 10:23' cross-platform."""
    now = datetime.now()
    return f"{now.strftime('%b')} {now.day} · {now.strftime('%H:%M')}"


def send_scan_email(to_addr: str, smtp_user: str, smtp_pass: str, subject: str, body: str) -> str:
    """Send notification via Gmail SMTP. Returns error string or empty string on success."""
    try:
        msg = MIMEMultipart()
        msg["From"]    = smtp_user
        msg["To"]      = to_addr
        msg["Subject"] = subject
        msg.attach(MIMEText(body, "plain"))
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as server:
            server.login(smtp_user, smtp_pass)
            server.send_message(msg)
        return ""
    except Exception as e:
        return str(e)


# ─────────────────────────────────────────────
# SCORING ENGINE
# ─────────────────────────────────────────────

def score_deal(listing: dict, cfg: dict) -> dict:
    asking   = listing.get("asking_price")
    cashflow = listing.get("cash_flow")
    btype    = listing.get("business_type", "")
    combined = ((listing.get("title") or "") + " " + (listing.get("description") or "")).lower()

    score   = 100
    flags   = []
    signals = []

    # ── Layer 1: Math ──────────────────────────
    if asking and cashflow and cashflow > 0:
        multiple = asking / cashflow
        listing["multiple"] = round(multiple, 2)

        if multiple < 1.0:
            flags.append(f"Multiple {multiple:.1f}x — CF exceeds asking, verify data")
            score -= 40
        elif multiple < 1.5:
            flags.append(f"Multiple {multiple:.1f}x — suspiciously low")
            score -= 25
        elif multiple < cfg.get("min_multiple", 0):
            flags.append(f"Multiple {multiple:.1f}x — below {cfg['min_multiple']}x floor")
            score -= 20
        elif multiple > cfg["max_multiple"]:
            flags.append(f"Multiple {multiple:.1f}x — above {cfg['max_multiple']}x ceiling")
            score -= 30
        else:
            signals.append(f"Multiple {multiple:.1f}x ✓")

        # SBA 7(a): 90% LTV, 10-yr term, 7.5% annual interest
        # PMT formula: principal × r / (1 − (1+r)^−n)
        r = 0.075
        n = 10
        annual_ds = asking * 0.90 * (r / (1 - (1 + r) ** -n))
        dscr = cashflow / annual_ds
        listing["est_dscr"] = round(dscr, 2)
        if dscr < 1.25:
            flags.append(f"Est. DSCR {dscr:.2f}x — below SBA 1.25x minimum")
            score -= 25
        elif dscr < 1.40:
            flags.append(f"Est. DSCR {dscr:.2f}x — tight coverage")
            score -= 8
        else:
            signals.append(f"Est. DSCR {dscr:.2f}x ✓")

        # SBA 7(a) loan cap: $5M
        if asking > 5_000_000:
            flags.append(f"Asking ${asking:,.0f} exceeds SBA 7(a) $5M limit")
            score -= 15
    else:
        listing["multiple"]  = None
        listing["est_dscr"]  = None
        if not cashflow:
            flags.append("Cash flow not listed — sign-in required or missing")
            score -= 30          # raised: missing CF is a serious data gap
        if not asking:
            flags.append("No asking price")
            score -= 10

    if cashflow and cashflow < cfg["min_cashflow"]:
        flags.append(f"Cash flow ${cashflow:,.0f} below ${cfg['min_cashflow']:,.0f} floor")
        score -= 20

    if asking and asking > cfg["max_price"]:
        flags.append(f"Asking ${asking:,.0f} above ${cfg['max_price']:,.0f} ceiling")
        score -= 15

    # ── Layer 2: HALO Industry Score ──────────
    halo_adj = _HALO_SCORE.get(btype, 0)
    if halo_adj > 0:
        signals.append(f"HALO tier: {btype} (+{halo_adj})")
        score += halo_adj
    elif halo_adj < 0:
        flags.append(f"HALO tier: {btype} ({halo_adj})")
        score += halo_adj   # halo_adj is negative

    # ── Layer 3a: Red Flags ───────────────────
    for kw in RED_FLAG_KEYWORDS:
        if kw in combined:
            flags.append(f'⚑ "{kw}"')
            score -= 12

    # ── Layer 4: Quality Signals ──────────────
    for kw in QUALITY_KEYWORDS:
        if kw in combined:
            signals.append(f'✓ "{kw}"')
            score += 5

    # Location bonus/penalty vs selected states
    selected_states = cfg.get("selected_states", ["South Carolina"])
    if is_target_location(listing.get("location", ""), selected_states):
        signals.append("✓ Target state confirmed")
        score += 10
    else:
        flags.append(f"Location outside target: {listing.get('location','unknown')}")
        score -= 15

    score = max(0, min(100, score))

    # ── Hard disqualifiers applied LAST (after all bonuses) ──────────────────
    _FRANCHISE_TERMS = [
        "franchise", "franchised", "franchisee",
        "franchise resale", "franchise opportunity", "franchise system",
    ]
    is_franchise = any(t in combined for t in _FRANCHISE_TERMS)
    if is_franchise:
        flags.append("⚑ Franchise — no brand ownership; transfer/royalty risk")
        score = min(score, 43)

    _FEDEX_TERMS = ["fedex route", "fedex ground", "fedex linehaul", "amazon route", "amazon dsp"]
    if any(t in combined for t in _FEDEX_TERMS):
        flags.append("⚑ Delivery route — owner-operator, not a scalable business")
        score = min(score, 43)

    _RESTAURANT_TERMS = ["restaurant", "pizzeria", "diner", "café", "cafe", "bistro", "eatery",
                          "food truck", "fast food", "bar and grill", "bar & grill", "tavern"]
    if any(t in combined for t in _RESTAURANT_TERMS):
        flags.append("⚑ Restaurant — high failure rate, low HALO score")
        score = min(score, 43)

    # Missing cash flow: no-CF listings can't be underwritten — always 🔴
    if not cashflow:
        score = min(score, 43)

    listing["score"]   = score
    listing["flags"]   = " | ".join(flags)   if flags   else "—"
    listing["signals"] = " | ".join(signals) if signals else "—"
    listing["grade"]   = ("🟢 Look Closer" if score >= 75
                          else "🟡 Marginal" if score >= 44
                          else "🔴 Skip")
    return listing


# ─────────────────────────────────────────────
# PLAYWRIGHT SCRAPER
# ─────────────────────────────────────────────

_CHROMIUM_EXE = (
    r"C:\Users\rhode\pw_browsers"
    r"\chromium-1208"
    r"\chrome-win64"
    r"\chrome.exe"
)

# Prefer real Google Chrome over Playwright's bundled Chromium.
# Chrome has genuine browser fingerprints that pass Cloudflare bot detection.
_REAL_CHROME_CANDIDATES = [
    r"C:\Program Files\Google\Chrome\Application\chrome.exe",
    r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
    pathlib.Path.home() / r"AppData\Local\Google\Chrome\Application\chrome.exe",
]
_CHROME_EXE = next(
    (str(p) for p in _REAL_CHROME_CANDIDATES if pathlib.Path(p).exists()),
    None,  # None → fall back to bundled Chromium
)

# Comprehensive stealth patches — covers the main bot-detection fingerprints
_STEALTH_JS = """
() => {
    // webdriver flag
    Object.defineProperty(navigator, 'webdriver', {get: () => undefined});

    // Plugins — headless has 0, real browsers have several
    Object.defineProperty(navigator, 'plugins', {
        get: () => {
            const arr = [1, 2, 3, 4, 5];
            arr.__proto__ = PluginArray.prototype;
            return arr;
        }
    });

    // Languages
    Object.defineProperty(navigator, 'languages', {get: () => ['en-US', 'en']});

    // window.chrome — absent in headless, present in real Chrome
    window.chrome = {
        app: {isInstalled: false},
        runtime: {},
        loadTimes: function() {},
        csi: function() {},
    };

    // Permissions — headless returns 'denied' for notifications; real browsers return 'default'
    const origQuery = window.navigator.permissions.query.bind(navigator.permissions);
    window.navigator.permissions.query = (params) =>
        params.name === 'notifications'
            ? Promise.resolve({state: 'default'})
            : origQuery(params);

    // Screen dimensions — headless uses small defaults
    Object.defineProperty(screen, 'width',       {get: () => 1920});
    Object.defineProperty(screen, 'height',      {get: () => 1080});
    Object.defineProperty(screen, 'availWidth',  {get: () => 1920});
    Object.defineProperty(screen, 'availHeight', {get: () => 1040});
    Object.defineProperty(screen, 'colorDepth',  {get: () => 24});
    Object.defineProperty(screen, 'pixelDepth',  {get: () => 24});

    // Remove Playwright-specific globals
    delete window.__playwright;
    delete window.__pw_manual;
    delete window._playwright;
}
"""


def _extract_chrome_cookies(domain: str) -> list[dict]:
    """
    Pull the current user's Chrome cookies for `domain`.
    Uses browser-cookie3 which reads Chrome's SQLite store (handles DPAPI decryption
    on Windows automatically). Returns [] if the package isn't installed or fails.
    Chrome does NOT need to be closed — browser-cookie3 copies the DB before reading.
    Auto-installs browser-cookie3 on first use if missing.
    """
    try:
        import browser_cookie3
    except ImportError:
        import subprocess, sys
        subprocess.run(
            [sys.executable, "-m", "pip", "install", "browser-cookie3", "--quiet"],
            check=False,
        )
        try:
            import browser_cookie3
        except ImportError:
            return []
    try:
        jar = browser_cookie3.chrome(domain_name=domain)
        cookies = []
        for c in jar:
            entry = {
                "name":   c.name,
                "value":  c.value,
                "domain": c.domain if c.domain else f".{domain}",
                "path":   c.path or "/",
                "secure": bool(c.secure),
            }
            if c.expires:
                entry["expires"] = float(c.expires)
            cookies.append(entry)
        return cookies
    except Exception:
        return []


def _session_path(source_name: str) -> pathlib.Path:
    return SESSION_DIR / f"{source_name.lower().replace(' ', '_')}_cookies.json"


def _save_session(ctx, source_name: str):
    try:
        cookies = ctx.cookies()
        _session_path(source_name).write_text(json.dumps(cookies))
    except Exception:
        pass


def _load_session(ctx, source_name: str) -> bool:
    path = _session_path(source_name)
    if path.exists():
        try:
            cookies = json.loads(path.read_text())
            ctx.add_cookies(cookies)
            return True
        except Exception:
            pass
    return False


def _login(page, ctx, src: dict, username: str, password: str, warnings: list):
    """
    Log in, save cookies on success so future runs skip this step.
    Returns True on success.
    """
    try:
        page.goto(src["login_url"], wait_until="domcontentloaded", timeout=20_000)
        page.wait_for_selector(src["user_sel"], timeout=8_000)

        page.fill(src["user_sel"], username)
        time.sleep(random.uniform(0.4, 0.8))
        page.fill(src["pass_sel"], password)
        time.sleep(random.uniform(0.3, 0.6))
        page.click(src["submit_sel"])
        page.wait_for_load_state("domcontentloaded", timeout=15_000)
        time.sleep(random.uniform(1.5, 2.5))

        success = src.get("logged_in_url_fragment", "") in page.url
        if success:
            _save_session(ctx, src["login_url"].split("/")[2])
        else:
            warnings.append(
                f"{src['login_url'].split('/')[2]}: Login blocked (reCAPTCHA likely). "
                "Scraping without login — cash flow will be limited."
            )
        return success
    except Exception as e:
        warnings.append(
            f"Login error ({src['login_url'].split('/')[2]}): {e}. Continuing without login."
        )
        return False


def _is_blocked(page) -> bool:
    """Return True if the current page is an access-denied / bot-challenge page."""
    title = (page.title() or "").lower()
    url   = (page.url or "").lower()
    return any(kw in title or kw in url for kw in
               ["access denied", "403", "blocked", "captcha", "robot", "are you human",
                "security check", "ddos", "cloudflare", "just a moment"])


def _parse_api_json(data, source_name: str, state: str) -> list[dict]:
    """
    Try to extract listing records from a JSON API response.
    Handles dicts with various 'listings' / 'results' keys, or direct arrays.
    """
    candidates = []
    if isinstance(data, list):
        candidates = data
    elif isinstance(data, dict):
        # Top-level list keys — includes BFF-specific names
        for key in ["listings", "results", "businesses", "data", "items", "records",
                    "Listings", "Results", "Businesses",
                    "bfsSearchResults", "searchResults", "listingResults",
                    "BfsSearchResults", "SearchResults"]:
            val = data.get(key)
            if isinstance(val, list):
                candidates = val
                break
            # BFF often wraps: {"bfsSearchResults": {"listings": [...]}}
            if isinstance(val, dict):
                for inner_key in ["listings", "results", "items", "Listings"]:
                    inner_val = val.get(inner_key)
                    if isinstance(inner_val, list):
                        candidates = inner_val
                        break
                if candidates:
                    break
        if not candidates:
            inner = data.get("data") or data.get("Data") or {}
            if isinstance(inner, dict):
                for key in ["listings", "results", "businesses", "items",
                            "bfsSearchResults", "searchResults"]:
                    if key in inner and isinstance(inner[key], list):
                        candidates = inner[key]
                        break

    results = []
    for item in candidates:
        if not isinstance(item, dict):
            continue

        def get_f(*keys):
            for k in keys:
                v = item.get(k)
                if v is not None:
                    return v
            return None

        title = get_f("title", "businessName", "listingName", "name", "listingTitle",
                      "Title", "BusinessName", "ListingName", "Name")
        if not title:
            continue

        listing = {"source": source_name, "state_searched": state}
        listing["title"]         = str(title)

        # Location: try composing city+state if no single location field
        loc = get_f("location", "city", "address", "Location", "City",
                    "locationDisplayName", "locationDisplay")
        if not loc:
            city  = get_f("city", "City") or ""
            state_val = get_f("state", "State", "stateCode") or ""
            loc = f"{city}, {state_val}".strip(", ") if (city or state_val) else ""
        listing["location"]      = str(loc or "")
        listing["description"]   = str(get_f("description", "businessDescription", "summary",
                                              "about", "Description", "BusinessDescription") or "")[:500]
        listing["business_type"] = str(get_f("businessType", "primaryIndustryName", "category",
                                              "type", "industry", "industryName",
                                              "BusinessType", "PrimaryIndustryName") or "")

        asking_raw = get_f("askingPrice", "asking", "price", "listPrice",
                           "AskingPrice", "Asking", "Price", "listingPrice")
        cf_raw     = get_f("cashFlow", "annualCashFlow", "sde", "netIncome", "cashflow",
                           "earnings", "CashFlow", "AnnualCashFlow", "SDE")
        rev_raw    = get_f("revenue", "grossRevenue", "annualRevenue", "grossSales", "sales",
                           "Revenue", "GrossRevenue", "AnnualRevenue", "GrossSales")

        listing["asking_price"] = parse_currency(str(asking_raw)) if asking_raw else None
        listing["cash_flow"]    = parse_currency(str(cf_raw))     if cf_raw     else None
        listing["revenue"]      = parse_currency(str(rev_raw))    if rev_raw    else None

        lid = get_f("listingId", "id", "businessId", "listingID",
                    "ListingId", "Id", "BusinessId", "ListingID")
        listing["listing_id"] = str(lid) if lid else None
        url_raw = get_f("url", "link", "listingUrl", "detailUrl", "seoUrl",
                        "Url", "Link", "ListingUrl", "DetailUrl")
        base = SOURCES[source_name]["base_url"]
        if url_raw:
            listing["url"] = url_raw if url_raw.startswith("http") else f"{base}{url_raw}"
        else:
            listing["url"] = f"{base}/Business-Opportunity/{lid}/" if lid else ""

        listing["days_listed"] = None
        results.append(listing)

    return results


def _playwright_scrape(source_name: str, cfg: dict, pages: int,
                       states: list[str], credentials: dict):
    """
    Runs in a dedicated thread. Returns (results: list[dict], warnings: list[str]).
    """
    import sys, os, asyncio
    if sys.platform == "win32":
        os.environ["PLAYWRIGHT_BROWSERS_PATH"] = r"C:\Users\rhode\pw_browsers"


    warnings_list = []

    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        return [], ["Playwright not installed. Run: pip install playwright && playwright install chromium"]

    src      = SOURCES[source_name]
    results  = []
    username = credentials.get(source_name, {}).get("username", "")
    password = credentials.get(source_name, {}).get("password", "")
    domain   = src["login_url"].split("/")[2]
    cookie_file = _session_path(domain)

    with sync_playwright() as pw:
        if _CHROME_EXE:
            # Real Chrome, headed but off-screen — passes all Cloudflare fingerprint checks.
            # Headless Chrome (even real Chrome) is detectable via WebGL/canvas signals;
            # headed Chrome off-screen is not.
            browser = pw.chromium.launch(
                executable_path=_CHROME_EXE,
                headless=False,
                args=[
                    "--window-position=-32000,0",   # off-screen, invisible to user
                    "--window-size=1280,900",
                    "--disable-blink-features=AutomationControlled",
                    "--disable-automation",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-infobars",
                    "--no-first-run",
                    "--no-default-browser-check",
                    "--mute-audio",
                ],
            )
        else:
            # Fallback: Playwright's bundled Chromium headless (may be blocked by Cloudflare)
            warnings_list.append(
                "Google Chrome not found — using bundled Chromium. "
                "Install Chrome to fix access-denied errors."
            )
            browser = pw.chromium.launch(
                executable_path=_CHROMIUM_EXE,
                headless=True,
                args=[
                    "--disable-blink-features=AutomationControlled",
                    "--disable-automation",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--no-first-run",
                    "--window-size=1280,900",
                ],
            )
        ctx = browser.new_context(
            user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/131.0.0.0 Safari/537.36"
            ),
            viewport={"width": 1280, "height": 900},
            locale="en-US",
            timezone_id="America/New_York",
            extra_http_headers={
                "Accept-Language": "en-US,en;q=0.9",
                "Accept":          "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            },
        )
        ctx.add_init_script(_STEALTH_JS)

        # Inject real Chrome cookies first — Kasada validates established sessions
        # and skips its JS challenge for browsers it already trusts.
        chrome_cookies = _extract_chrome_cookies(src["url"].split("/")[2])
        if chrome_cookies:
            try:
                ctx.add_cookies(chrome_cookies)
                warnings_list_chrome_ok = True
            except Exception:
                warnings_list_chrome_ok = False
        else:
            warnings_list_chrome_ok = False
            warnings_list.append(
                "Could not extract Chrome cookies (install browser-cookie3 or ensure Chrome is open). "
                "Kasada bot protection may block scraping."
            )

        # Load saved login session; fall back to fresh login
        session_loaded = _load_session(ctx, domain)

        page = ctx.new_page()

        # ── Network interception: capture listing API responses ────────────────
        # Angular fires its data API call before Kasada finishes its JS challenge,
        # so we may be able to extract listing JSON even on bot-blocked pages.
        _captured_json: list[dict] = []
        _api_url_file = SESSION_DIR / f"{source_name.lower()}_api_url.txt"

        def _on_response(response):
            try:
                if response.status != 200:
                    return
                ct  = response.headers.get("content-type", "")
                url = response.url
                if not ("json" in ct or "javascript" in ct):
                    return
                if any(skip in url for skip in
                       ["kasada", "6hLtZv", "analytics", "tracking", "pixel",
                        "telemetry", "gtm", "hotjar", "segment", "clarity"]):
                    return
                try:
                    data     = response.json()
                    data_str = json.dumps(data).lower()
                    if any(k in data_str for k in
                           ["askingprice", "cashflow", "businessname", "listingid",
                            "businesses", "asking_price"]):
                        _captured_json.append({"url": url, "data": data})
                        # Save base URL so _requests_scrape can call it directly later
                        _api_url_file.write_text(url.split("?")[0])
                except Exception:
                    pass
            except Exception:
                pass

        page.on("response", _on_response)
        # ──────────────────────────────────────────────────────────────────────

        if not session_loaded and username and password:
            logged_in = _login(page, ctx, src, username, password, warnings_list)
        elif session_loaded:
            logged_in = True  # assume cookies still valid; will detect otherwise
        else:
            logged_in = False

        # Scrape each state × each page
        state_params_map = STATE_PARAMS.get(source_name, {})
        for state in states:
            state_param = state_params_map.get(state, "")
            price_params = (
                f"priceLow={int(cfg['min_price'])}"
                f"&priceHigh={int(cfg['max_price'])}"
                f"&cfLow={int(cfg['min_cashflow'])}"
            )
            base_params = f"{state_param}&{price_params}" if state_param else price_params

            for pg in range(1, pages + 1):
                page_param = f"&page={pg}" if pg > 1 else ""
                url = f"{src['url']}?{base_params}{page_param}"

                _captured_json.clear()   # reset per-page capture
                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=30_000)
                    # Extra wait — gives Angular time to fire its API call before
                    # Kasada's block page fully replaces the DOM.
                    time.sleep(random.uniform(2.0, 3.5))

                    # ── Try intercepted API data first ─────────────────────────
                    if _captured_json:
                        for captured in _captured_json:
                            parsed = _parse_api_json(
                                captured["data"], source_name, state
                            )
                            results.extend(parsed)
                        if results:
                            continue   # got data — skip HTML scraping

                    # Detect bot-challenge pages before waiting for listing cards
                    if _is_blocked(page):
                        cookie_file = _session_path(domain)
                        if cookie_file.exists():
                            cookie_file.unlink()
                        warnings_list.append(
                            f"{source_name}/{state} page {pg}: access-denied "
                            f"(title: '{page.title()}'). "
                            "Log in to this site in real Chrome to refresh Kasada session cookies."
                        )
                        break

                    page.wait_for_selector(SELECTORS["card"], timeout=20_000)
                    time.sleep(random.uniform(1.2, 2.5))
                except Exception as e:
                    # Even on exception, check if network interception captured data
                    if _captured_json:
                        for captured in _captured_json:
                            parsed = _parse_api_json(
                                captured["data"], source_name, state
                            )
                            results.extend(parsed)
                        if results:
                            continue
                    title = page.title() if page else "?"
                    warnings_list.append(
                        f"{source_name}/{state} page {pg}: selector not found "
                        f"— page title: '{title}'"
                    )
                    continue

                cards = page.query_selector_all(SELECTORS["card"])

                for card in cards:
                    try:
                        listing = {"source": source_name, "state_searched": state}

                        def txt(sel):
                            el = card.query_selector(sel)
                            return el.inner_text().strip() if el else ""

                        listing["title"]       = txt(SELECTORS["title"])
                        listing["location"]    = txt(SELECTORS["location"])
                        listing["description"] = txt(SELECTORS["description"])[:500]
                        listing["business_type"] = txt(SELECTORS["category"]) or ""

                        listing["asking_price"] = parse_currency(txt(SELECTORS["asking"]))

                        cf_text   = txt(SELECTORS["cash_flow"])
                        full_text = card.inner_text()
                        listing["cash_flow"] = (
                            parse_currency(cf_text)
                            or extract_currency_from_text(r"Cash Flow",   full_text)
                            or extract_currency_from_text(r"SDE",         full_text)
                            or extract_currency_from_text(r"Net Income",  full_text)
                        )

                        listing["revenue"] = (
                            extract_currency_from_text(r"Gross Revenue", full_text)
                            or extract_currency_from_text(r"Revenue",     full_text)
                        )

                        img = card.query_selector("img")
                        img_src = img.get_attribute("src") if img else ""
                        id_match = re.search(r"listings/\d+/(\d+)/", img_src or "")
                        lid = id_match.group(1) if id_match else None
                        listing["listing_id"] = lid
                        listing["url"] = (
                            f"{src['base_url']}/Business-Opportunity/{lid}/" if lid else ""
                        )

                        days_m = re.search(r"(\d+)\s*days?\s*(?:listed|on market|ago)", full_text, re.I)
                        listing["days_listed"] = int(days_m.group(1)) if days_m else None

                        if listing["title"]:
                            results.append(listing)

                    except Exception:
                        continue

        ctx.close()
        browser.close()

    return results, warnings_list


def _get_bbs_regions(session, auth_headers: dict) -> dict:
    """
    Fetch BizBuySell region metadata (state → regionId/legacyRegionId).
    Cached locally so we only call once.
    """
    if _BBS_REGIONS_CACHE.exists():
        try:
            return json.loads(_BBS_REGIONS_CACHE.read_text())
        except Exception:
            pass
    try:
        r = session.get(_BBS_REGIONS_URL, headers=auth_headers, timeout=10)
        if r.status_code == 200:
            data  = r.json()
            items = data if isinstance(data, list) else (
                data.get("regions") or data.get("data") or data.get("items") or []
            )
            mapping = {}
            for item in items:
                sc = (item.get("stateCode") or item.get("legacyRegionCode")
                      or item.get("abbreviation") or "")
                if sc and len(sc) == 2:
                    mapping[sc.upper()] = item
            if mapping:
                _BBS_REGIONS_CACHE.write_text(json.dumps(mapping))
                return mapping
    except Exception:
        pass
    return {}


# Fallback region data observed from real DevTools traffic
_BBS_REGION_FALLBACK = {
    "SC": {"regionId": "41", "legacyRegionId": 54,  "regionName": "South Carolina", "regionNameSeo": "south-carolina"},
    "NC": {"regionId": "34", "legacyRegionId": 33,  "regionName": "North Carolina", "regionNameSeo": "north-carolina"},
    "GA": {"regionId": "11", "legacyRegionId": 11,  "regionName": "Georgia",        "regionNameSeo": "georgia"},
    "VA": {"regionId": "46", "legacyRegionId": 48,  "regionName": "Virginia",       "regionNameSeo": "virginia"},
    "TN": {"regionId": "42", "legacyRegionId": 43,  "regionName": "Tennessee",      "regionNameSeo": "tennessee"},
    "FL": {"regionId": "10", "legacyRegionId": 9,   "regionName": "Florida",        "regionNameSeo": "florida"},
}

_STATE_CODE_MAP = {
    "South Carolina": "SC", "North Carolina": "NC", "Georgia": "GA",
    "Virginia": "VA", "Tennessee": "TN", "Florida": "FL",
}


def _bbs_bff_scrape(cfg: dict, pages: int, states: list[str],
                    _session_unused, _headers_unused,
                    progress_cb=None) -> tuple[list[dict], list[str]]:
    """
    POST to the BizBuySell BFF endpoint. Fully self-bootstrapping:
    the API returns a fresh JWT on every response (even unauthenticated ones),
    so no manual token setup is needed. Saved JWT is reused when available;
    on 401/403 or first run we fall back to no-auth to get a fresh one.
    No browser, no CDP, no cookies required.
    """
    # Load any saved JWT (may be empty on first run — that's fine)
    jwt = ""
    if _BBS_JWT_FILE.exists():
        try:
            raw = _BBS_JWT_FILE.read_text().strip()
            jwt = raw.removeprefix("Bearer ").strip()
        except Exception:
            pass

    # Fresh curl_cffi session for TLS impersonation
    try:
        from curl_cffi import requests as _cf
        session = _cf.Session(impersonate="chrome131")
    except ImportError:
        import requests as _rq
        session = _rq.Session()

    def _build_headers(token: str) -> dict:
        h = {
            "User-Agent":      ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                                "AppleWebKit/537.36 (KHTML, like Gecko) "
                                "Chrome/131.0.0.0 Safari/537.36"),
            "Accept":          "application/json, text/plain, */*",
            "Accept-Language": "en-US,en;q=0.9",
            "Accept-Encoding": "gzip, deflate, br",
            "Content-Type":    "application/json",
            "Origin":          "https://www.bizbuysell.com",
            "Referer":         "https://www.bizbuysell.com/businesses-for-sale/",
            "Sec-Fetch-Dest":  "empty",
            "Sec-Fetch-Mode":  "cors",
            "Sec-Fetch-Site":  "same-origin",
            "sec-ch-ua":       '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
            "sec-ch-ua-mobile":    "?0",
            "sec-ch-ua-platform":  '"Windows"',
            "x-lane":          "",
        }
        if token:
            h["Authorization"] = f"Bearer {token}"
        return h

    auth_headers = _build_headers(jwt)

    regions = _get_bbs_regions(session, auth_headers)
    results: list[dict] = []
    warnings: list[str] = []

    for state in states:
        sc  = _STATE_CODE_MAP.get(state, state[:2].upper())
        reg = regions.get(sc) or _BBS_REGION_FALLBACK.get(sc, {})

        region_id   = str(reg.get("regionId",   reg.get("id", "")))
        legacy_id   = int(reg.get("legacyRegionId", reg.get("legacyId", 0)))
        region_name = reg.get("regionName", reg.get("name", state))
        region_seo  = reg.get("regionNameSeo", state.lower().replace(" ", "-"))

        for pg in range(1, pages + 1):
            body = {
                "bfsSearchCriteria": {
                    "siteId":     20,
                    "languageId": 10,
                    "categories": None,
                    "locations": [{
                        "geoType":          20,
                        "regionId":         region_id,
                        "countryCode":      "US",
                        "countryId":        "US",
                        "stateCode":        sc,
                        "legacyRegionId":   legacy_id,
                        "legacyRegionCode": sc,
                        "regionName":       region_name,
                        "regionNameSeo":    region_seo,
                        "displayName":      region_name,
                        "locationDetected": False,
                    }],
                    "excludeLocations":          [],
                    "askingPriceMin":             int(cfg["min_price"]),
                    "askingPriceMax":             int(cfg["max_price"]),
                    "pageNumber":                 pg,
                    "keyword":                    None,
                    "cashFlowMin":                int(cfg["min_cashflow"]),
                    "cashFlowMax":                0,
                    "grossIncomeMin":             0,
                    "grossIncomeMax":             0,
                    "daysListedAgo":              0,
                    "establishedAfterYear":       0,
                    "listingsWithNoAskingPrice":  0,
                    "homeBasedListings":          0,
                    "includeRealEstateForLease":  0,
                    "listingsWithSellerFinancing":0,
                    "realEstateIncluded":         0,
                    "showRelocatableListings":    False,
                    "relatedFranchises":          0,
                    "listingTypeIds":             None,
                    "designationTypeIds":         None,
                    "sortList":                   None,
                    "absenteeOwnerListings":      0,
                    "listingsWithPriceReduced":   0,
                    "daysModifiedAgo":            0,
                    "seoSearchType":              None,
                },
                "industriesHierarchy":      10,
                "industriesFlat":           10,
                "bfsSearchResultsCounts":   0,
                "cmsFilteredData":          0,
                "rightRailBrokers":         0,
                "statesRegions":            10,
                "languageTypeId":           10,
            }
            req_headers = {
                **auth_headers,
                "x-correlation-id": str(uuid.uuid4()),
            }
            try:
                r = session.post(_BBS_BFF_URL, json=body, headers=req_headers, timeout=20)

                # JWT stale/rejected — drop it and retry without auth to get a fresh token.
                # The BFF issues a new JWT even on unauthenticated requests.
                if r.status_code in (401, 403):
                    jwt = ""
                    auth_headers = _build_headers("")
                    req_headers  = {**auth_headers, "x-correlation-id": str(uuid.uuid4())}
                    r = session.post(_BBS_BFF_URL, json=body, headers=req_headers, timeout=20)

                if r.status_code != 200:
                    warnings.append(f"BizBuySell BFF HTTP {r.status_code} ({state} p{pg})")
                    continue

                data = r.json()

                # BizBuySell rotates the JWT on every response — persist the new one
                # so the next request (next page or next session) uses a valid token.
                new_jwt = (data.get("value") or {}).get("jwtToken") or ""
                if new_jwt:
                    try:
                        _BBS_JWT_FILE.write_text(f"Bearer {new_jwt}")
                        jwt = new_jwt
                        auth_headers["Authorization"] = f"Bearer {jwt}"
                    except Exception:
                        pass

                # BFF response: data["value"]["bfsSearchResult"]["value"] = listing list
                # Field names confirmed from DevTools: header, location, price (float),
                # cashFlow (float), urlStub (full URL), specificId, type (int category)
                try:
                    items = data["value"]["bfsSearchResult"]["value"] or []
                except (KeyError, TypeError):
                    items = []
                    warnings.append(
                        f"BizBuySell BFF unexpected response structure ({state} p{pg}). "
                        f"Top keys: {list(data.keys()) if isinstance(data, dict) else type(data)}"
                    )

                page_results = []
                for item in items:
                    if not isinstance(item, dict):
                        continue
                    # Skip ad slots injected into the results list
                    if item.get("isInlineAd") or item.get("isInlineBroker"):
                        continue
                    title = item.get("header") or ""
                    if not title:
                        continue

                    listing = {"source": "BizBuySell", "state_searched": state}
                    listing["title"]         = str(title)
                    _loc  = str(item.get("location") or "")
                    _city = str(item.get("city") or item.get("listingCity") or item.get("locationCity") or "")
                    if _city and _city.lower() not in _loc.lower():
                        _loc = f"{_city}, {_loc}".strip(", ")
                    listing["location"]      = _loc
                    listing["description"]   = str(item.get("description") or "")[:800]
                    # categoryDetails is always None from BFF — derive from title/description
                    listing["business_type"] = _derive_business_type(
                        str(title), listing["description"]
                    )

                    # price and cashFlow are already floats from the API
                    price = item.get("price")
                    cf    = item.get("cashFlow") or item.get("ebitda")
                    listing["asking_price"] = float(price) if price else None
                    listing["cash_flow"]    = float(cf)    if cf    else None
                    listing["revenue"]      = None

                    url_stub = item.get("urlStub") or ""
                    lid      = item.get("specificId") or item.get("listNumber") or item.get("siteSpecificId")
                    listing["listing_id"] = str(lid) if lid else None
                    if url_stub:
                        listing["url"] = (url_stub if url_stub.startswith("http")
                                          else f"https://www.bizbuysell.com{url_stub}")
                    elif lid:
                        listing["url"] = f"https://www.bizbuysell.com/Business-Opportunity/{lid}/"
                    else:
                        listing["url"] = ""

                    listing["days_listed"]    = None

                    # Broker/agent fields — BFF confirmed fields: brokerContactFullName, brokerCompany, contactInfo
                    contact_info = item.get("contactInfo") or {}
                    listing["broker_name"]    = str(item.get("brokerContactFullName") or item.get("brokerName") or item.get("agentName") or contact_info.get("name") or "")
                    listing["broker_phone"]   = str(item.get("brokerPhone") or contact_info.get("phone") or item.get("contactPhone") or "")
                    listing["broker_email"]   = str(item.get("brokerEmail") or contact_info.get("email") or item.get("contactEmail") or "")
                    listing["brokerage_name"] = str(item.get("brokerCompany") or item.get("brokerageName") or "")

                    page_results.append(listing)

                results.extend(page_results)
                if progress_cb:
                    total_so_far = len(results)
                    progress_cb(
                        f"BizBuySell — {state}, page {pg}/{pages} "
                        f"({total_so_far} listings so far)"
                    )
                time.sleep(random.uniform(0.4, 0.9))

            except Exception as e:
                warnings.append(f"BizBuySell BFF error ({state} p{pg}): {e}")
                continue

    return results, warnings


def _requests_scrape(source_name: str, cfg: dict, pages: int,
                     states: list[str], credentials: dict, progress_cb=None):
    """
    HTTP-only scraper — no CDP, no Playwright.
    Uses curl_cffi (Chrome TLS impersonation) when available; falls back to requests.
    Injects real Chrome session cookies so Kasada sees a trusted session.
    Returns (results: list[dict], warnings: list[str]).
    """
    import sys, subprocess

    warnings_list: list[str] = []
    results: list[dict]      = []

    # ── HTTP session ──────────────────────────────────────────────────────────
    session      = None
    session_type = None
    try:
        from curl_cffi import requests as cf_req
        session      = cf_req.Session(impersonate="chrome131")
        session_type = "curl_cffi"
    except ImportError:
        try:
            import requests as _req
            session      = _req.Session()
            session_type = "requests"
        except ImportError:
            return [], ["Neither curl_cffi nor requests is installed."]

    # ── BeautifulSoup ─────────────────────────────────────────────────────────
    try:
        from bs4 import BeautifulSoup
    except ImportError:
        subprocess.run(
            [sys.executable, "-m", "pip", "install", "beautifulsoup4", "--quiet"],
            check=False,
        )
        try:
            from bs4 import BeautifulSoup
        except ImportError:
            return [], ["beautifulsoup4 not installed — cannot parse HTML"]

    src    = SOURCES[source_name]
    domain = src["url"].split("/")[2]

    # ── Merge Chrome cookies + saved session cookies ──────────────────────────
    cookie_jar: dict[str, str] = {}
    for c in _extract_chrome_cookies(domain):
        cookie_jar[c["name"]] = c["value"]
    saved = _session_path(domain)
    if saved.exists():
        try:
            for c in json.loads(saved.read_text()):
                cookie_jar[c["name"]] = c["value"]
        except Exception:
            pass

    if cookie_jar:
        session.cookies.update(cookie_jar)
    elif source_name != "BizBuySell":
        # BizBuySell uses JWT auth via BFF — no Chrome cookies needed.
        # Only warn for other sources where cookies matter.
        warnings_list.append(
            f"{source_name}: No Chrome cookies found — log in to {domain} in Chrome first "
            "so Kasada recognises a trusted session."
        )

    # ── Request headers that match real Chrome ─────────────────────────────────
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/131.0.0.0 Safari/537.36"
        ),
        "Accept": (
            "text/html,application/xhtml+xml,application/xml;q=0.9,"
            "image/avif,image/webp,image/apng,*/*;q=0.8,"
            "application/signed-exchange;v=b3;q=0.7"
        ),
        "Accept-Language":        "en-US,en;q=0.9",
        "Accept-Encoding":        "gzip, deflate, br",
        "Sec-Fetch-Dest":         "document",
        "Sec-Fetch-Mode":         "navigate",
        "Sec-Fetch-Site":         "none",
        "Sec-Fetch-User":         "?1",
        "Upgrade-Insecure-Requests": "1",
        "Cache-Control":          "max-age=0",
        "sec-ch-ua":              '"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"',
        "sec-ch-ua-mobile":       "?0",
        "sec-ch-ua-platform":     '"Windows"',
        "DNT":                    "1",
    }

    _api_url_file = SESSION_DIR / f"{source_name.lower()}_api_url.txt"

    # ── BizBuySell: try confirmed BFF POST endpoint first ─────────────────────
    if source_name == "BizBuySell":
        bff_results, bff_warnings = _bbs_bff_scrape(
            cfg, pages, states, session, headers, progress_cb=progress_cb
        )
        if bff_results:
            return bff_results, bff_warnings
        # BFF failed or no token — log why and continue to probe/HTML fallbacks
        warnings_list.extend(bff_warnings)

    # ── Probe known BizBuySell API candidate endpoints ────────────────────────
    # BizBuySell (CoStar) is an Angular SPA that calls a backend JSON API.
    # Try known / reported endpoint patterns before falling back to HTML scraping.
    _BBS_API_CANDIDATES = [
        # Confirmed from DevTools: BFF search endpoint
        "https://www.bizbuysell.com/_api/bff/v2/BbsBfsSearchResults",
        # Same namespace, resource variants
        "https://www.bizbuysell.com/_api/resource/v2/Listings",
        "https://www.bizbuysell.com/_api/resource/v2/ListingSearch",
        "https://www.bizbuysell.com/_api/resource/v2/BusinessListings",
        "https://www.bizbuysell.com/_api/resource/v2/Search",
    ]
    _BQ_API_CANDIDATES = [
        "https://www.bizquest.com/api/listings/search",
        "https://www.bizquest.com/services/listing/search",
    ]
    _STATE_CODE_MAP = {
        "South Carolina": "SC", "North Carolina": "NC", "Georgia": "GA",
        "Virginia": "VA", "Tennessee": "TN", "Florida": "FL",
    }
    candidates = _BBS_API_CANDIDATES if source_name == "BizBuySell" else _BQ_API_CANDIDATES

    for api_base in candidates:
        probe_results: list[dict] = []
        probe_ok = False
        for state in states:
            sc = _STATE_CODE_MAP.get(state, state[:2].upper())
            for pg in range(1, pages + 1):
                params = {
                    "StateCode":       sc,
                    "ListingType":     "Business",
                    "MinAskingPrice":  int(cfg["min_price"]),
                    "MaxAskingPrice":  int(cfg["max_price"]),
                    "MinCashFlow":     int(cfg["min_cashflow"]),
                    "PageNumber":      pg,
                    "PageSize":        20,
                }
                try:
                    r = session.get(
                        api_base, params=params,
                        headers={**headers, "Accept": "application/json"},
                        timeout=15,
                    )
                    if r.status_code == 200:
                        try:
                            data   = r.json()
                            parsed = _parse_api_json(data, source_name, state)
                            if parsed:
                                probe_results.extend(parsed)
                                probe_ok = True
                                # Save for future direct use
                                _api_url_file.write_text(api_base)
                        except Exception:
                            pass
                    elif r.status_code in (404, 410):
                        break  # this candidate doesn't exist
                except Exception:
                    break  # network/timeout — try next candidate
        if probe_ok and probe_results:
            return probe_results, warnings_list

    # ── Try previously discovered API endpoint directly ──────────────────────
    if _api_url_file.exists():
        saved_api_base = _api_url_file.read_text().strip()
        if saved_api_base:
            api_results  = []
            api_warnings = []
            state_params_map_api = STATE_PARAMS.get(source_name, {})
            for state in states:
                state_param  = state_params_map_api.get(state, "")
                price_params = (
                    f"priceLow={int(cfg['min_price'])}"
                    f"&priceHigh={int(cfg['max_price'])}"
                    f"&cfLow={int(cfg['min_cashflow'])}"
                )
                qp = f"{state_param}&{price_params}" if state_param else price_params
                for pg in range(1, pages + 1):
                    api_url = f"{saved_api_base}?{qp}" + (f"&page={pg}" if pg > 1 else "")
                    try:
                        r = session.get(api_url, headers=headers, timeout=20)
                        if r.status_code == 200:
                            try:
                                data   = r.json()
                                parsed = _parse_api_json(data, source_name, state)
                                if parsed:
                                    api_results.extend(parsed)
                                    continue
                            except Exception:
                                pass
                        if r.status_code in (403, 404, 410):
                            # Saved URL no longer valid — delete it
                            _api_url_file.unlink(missing_ok=True)
                            break
                    except Exception:
                        pass
            if api_results:
                return api_results, api_warnings

    state_params_map = STATE_PARAMS.get(source_name, {})
    blocked          = False

    for state in states:
        if blocked:
            break
        state_param  = state_params_map.get(state, "")
        price_params = (
            f"priceLow={int(cfg['min_price'])}"
            f"&priceHigh={int(cfg['max_price'])}"
            f"&cfLow={int(cfg['min_cashflow'])}"
        )
        base_params = f"{state_param}&{price_params}" if state_param else price_params

        for pg in range(1, pages + 1):
            page_param = f"&page={pg}" if pg > 1 else ""
            url = f"{src['url']}?{base_params}{page_param}"

            try:
                resp = session.get(url, headers=headers, timeout=25, allow_redirects=True)

                if resp.status_code in (403, 429, 503):
                    warnings_list.append(
                        f"{source_name} HTTP {resp.status_code} — "
                        "Kasada blocked plain-HTTP approach; falling back to Playwright"
                    )
                    blocked = True
                    break

                soup       = BeautifulSoup(resp.text, "html.parser")
                title_el   = soup.find("title")
                page_title = (title_el.text if title_el else "").lower()

                if any(kw in page_title for kw in
                       ["access denied", "just a moment", "are you human",
                        "robot", "403", "blocked"]):
                    warnings_list.append(
                        f"{source_name}: bot challenge page via HTTP "
                        f"('{page_title}') — falling back to Playwright"
                    )
                    blocked = True
                    break

                cards = soup.select(SELECTORS["card"])

                if not cards and pg == 1:
                    warnings_list.append(
                        f"{source_name}/{state}: 0 listing cards in raw HTML "
                        f"(page title: '{page_title}') — "
                        "site uses client-side JS rendering; falling back to Playwright"
                    )
                    blocked = True
                    break

                for card in cards:
                    try:
                        listing = {"source": source_name, "state_searched": state}

                        def txt(sel, _card=card):
                            el = _card.select_one(sel)
                            return el.get_text(strip=True) if el else ""

                        listing["title"]         = txt(SELECTORS["title"])
                        listing["location"]      = txt(SELECTORS["location"])
                        listing["description"]   = txt(SELECTORS["description"])[:500]
                        listing["business_type"] = txt(SELECTORS["category"]) or ""
                        listing["asking_price"]  = parse_currency(txt(SELECTORS["asking"]))

                        cf_sels = [s.strip() for s in SELECTORS["cash_flow"].split(",")]
                        cf_text = next((txt(s) for s in cf_sels if txt(s)), "")
                        full    = card.get_text(" ", strip=True)
                        listing["cash_flow"] = (
                            parse_currency(cf_text)
                            or extract_currency_from_text(r"Cash Flow",   full)
                            or extract_currency_from_text(r"SDE",         full)
                            or extract_currency_from_text(r"Net Income",  full)
                        )
                        listing["revenue"] = (
                            extract_currency_from_text(r"Gross Revenue", full)
                            or extract_currency_from_text(r"Revenue",    full)
                        )

                        link = card.select_one("a[href]")
                        if link:
                            href      = link.get("href", "")
                            id_match  = re.search(r"/(\d+)/?$", href)
                            listing["listing_id"] = id_match.group(1) if id_match else None
                            listing["url"] = (
                                f"{src['base_url']}{href}" if href.startswith("/") else href
                            )
                        else:
                            listing["listing_id"] = None
                            listing["url"]        = ""

                        days_m = re.search(r"(\d+)\s*days?\s*(?:listed|on market|ago)", full, re.I)
                        listing["days_listed"] = int(days_m.group(1)) if days_m else None

                        if listing["title"]:
                            results.append(listing)
                    except Exception:
                        continue

                time.sleep(random.uniform(0.5, 1.2))

            except Exception as e:
                warnings_list.append(f"{source_name}/{state} p{pg}: request error — {e}")
                continue

    return results, warnings_list


def scrape_source(source_name: str, cfg: dict, pages: int,
                  states: list[str], credentials: dict,
                  progress_cb=None) -> list[dict]:
    """
    BizBuySell: direct BFF API (JWT auth, no browser needed).
    BizQuest: requires Playwright which is unavailable in this environment — skip fast.
    """
    # BizQuest needs a full browser (Kasada-protected, JS-rendered).
    # Playwright can't run here, so skip immediately rather than spending 60–90s
    # timing out through probe/HTML paths that all return 403.
    if source_name == "BizQuest":
        st.info(
            "ℹ️ BizQuest skipped — it requires browser automation (Playwright) "
            "which is unavailable in the current Python 3.14 environment. "
            "Results are from BizBuySell only."
        )
        return []

    try:
        results, warnings = _requests_scrape(
            source_name, cfg, pages, states, credentials, progress_cb=progress_cb
        )
    except Exception as e:
        results, warnings = [], [f"HTTP scrape error: {e}"]

    if results:
        return results

    # HTTP returned nothing — show why
    for w in warnings:
        st.warning(f"⚠️ {source_name}: {w}")
    return []


# ─────────────────────────────────────────────
# STREAMLIT UI
# ─────────────────────────────────────────────

st.set_page_config(
    page_title="DealFinder — ETA Listings",
    page_icon="🔍",
    layout="wide",
)

# ── Password gate ──────────────────────────────────────────────────────────────
if not st.session_state.get("_authenticated"):
    st.title("🔍 DealFinder")
    pwd = st.text_input("Password", type="password", placeholder="Enter password to continue")
    if pwd:
        if pwd == st.secrets.get("sheets", {}).get("app_password", ""):
            st.session_state["_authenticated"] = True
            st.rerun()
        else:
            st.error("Incorrect password.")
    st.stop()
# ──────────────────────────────────────────────────────────────────────────────

st.title("🔍 DealFinder — ETA Business Acquisition Triage")
st.caption(
    "Pulls listings from BizBuySell & BizQuest · "
    "Scores against your ETA criteria · Surfaces deals worth a second look"
)

# ── Sidebar ───────────────────────────────────
with st.sidebar:
    st.header("Your Criteria")

    # Reset all filters to defaults when button pressed
    if st.session_state.pop("_sidebar_reset", False):
        for _rk in ["sb_min_cf", "sb_min_price", "sb_max_price", "sb_min_mult",
                    "sb_max_mult", "sb_states", "sb_target_only", "sb_use_bbs",
                    "sb_pages", "sb_industries", "sb_custom_kw", "sb_min_score",
                    "sb_show_grades"]:
            st.session_state.pop(_rk, None)

    min_cashflow = st.number_input(
        "Min Cash Flow / SDE", min_value=0, max_value=5_000_000,
        value=100_000, step=50_000, format="%d", key="sb_min_cf",
    )
    st.caption(f"${min_cashflow:,}")
    min_price = st.number_input(
        "Min Asking Price", min_value=0, max_value=20_000_000,
        value=0, step=250_000, format="%d", key="sb_min_price",
    )
    st.caption(f"${min_price:,}")
    max_price = st.number_input(
        "Max Asking Price", min_value=0, max_value=20_000_000,
        value=5_000_000, step=250_000, format="%d", key="sb_max_price",
    )
    st.caption(f"${max_price:,}")

    col_min_m, col_max_m = st.columns(2)
    min_multiple = col_min_m.number_input("Min Multiple", 0.0, 10.0, 2.5, 0.5,
                                          format="%.1f", key="sb_min_mult")
    max_multiple = col_max_m.number_input("Max Multiple", 1.0, 15.0, 6.5, 0.5,
                                          format="%.1f", key="sb_max_mult")

    st.divider()
    st.subheader("Geography")
    selected_states = st.multiselect(
        "States to search",
        list(STATE_PARAMS["BizBuySell"].keys()),
        default=["South Carolina"],
        key="sb_states",
    )
    target_only = st.checkbox("Target states only (hide others)", value=True,
                              key="sb_target_only")

    st.divider()
    st.subheader("Sources")
    use_bbs = st.checkbox("BizBuySell", value=True, key="sb_use_bbs")
    use_bq  = st.checkbox("BizQuest *(unavailable — requires browser)*", value=False,
                          disabled=True)
    pages   = st.slider("Pages per site / per state", 1, 20, 20, key="sb_pages")

    st.divider()
    st.subheader("Industry Filter")
    with st.expander("Select industries (blank = show all)", expanded=False):
        selected_industries = st.multiselect(
            "Industries",
            options=PRESET_INDUSTRY_KEYWORDS,
            default=[],
            label_visibility="collapsed",
            key="sb_industries",
        )
    custom_kw = st.text_input(
        "Custom keywords (comma-separated, added to above)",
        placeholder="e.g. powder coating, crane, septic",
        key="sb_custom_kw",
    )

    st.divider()
    st.subheader("Display Filters")
    min_score   = st.slider("Min score to show", 0, 100, 25, key="sb_min_score")
    show_grades = st.multiselect(
        "Show grades",
        ["🟢 Look Closer", "🟡 Marginal", "🔴 Skip"],
        default=["🟢 Look Closer", "🟡 Marginal"],
        key="sb_show_grades",
    )


    # ── Acquisition Criteria Doc ──────────────────────────────────────────
    st.divider()
    with st.expander("📄 My Acquisition Criteria", expanded=False):
        _ebitda_min = min_cashflow
        _ebitda_max = max_price // 4 if max_price else 2_000_000
        _price_max  = max_price
        _inds = selected_industries if selected_industries else ["HVAC", "Fire Protection", "Environmental / Industrial"]
        _geo  = ", ".join(selected_states) if selected_states else "Southeast US"
        _mult_range = f"{min_multiple:.1f}x – {max_multiple:.1f}x"
        _criteria_text = f"""[YOUR NAME] is an independent buyer actively searching for a single owner-operated business to acquire and lead in the Southeast US.

ACQUISITION CRITERIA
---------------------
Revenue:          $1M – $10M
EBITDA / SDE:     ${_ebitda_min:,.0f} – $2,000,000+
Asking Price:     Up to ${_price_max:,.0f}
EV / EBITDA:      {_mult_range} (entry)
Industries:       {", ".join(_inds)}
Revenue type:     Recurring or highly repeating (service contracts, maintenance agreements)
Customer base:    Diversified — no single customer > 20% of revenue
Geography:        {_geo} (Charleston, SC preferred; will consider broader Southeast)
Seller situation: Retiring owner with desire to exit in 12–24 months
Management:       Capable team or key employees willing to remain post-close
Financing:        SBA 7(a) preferred; open to equity co-investors for the right deal

I move quickly and can reach LOI in 2–3 weeks for a well-qualified opportunity.
Happy to sign NDA on first call.

[YOUR NAME] | [YOUR PHONE] | [YOUR EMAIL]"""
        st.code(_criteria_text, language=None)
        st.caption("Select all text above and copy — use as your broker introduction or cold outreach template.")

    st.divider()
    with st.expander("⚡ Auto-Scan", expanded=False):
        auto_scan_on = st.checkbox("Enable auto-scan", value=False, key="auto_scan_on")
        auto_interval_days = st.selectbox(
            "Interval",
            [1, 2, 3, 4],
            index=1,
            format_func=lambda x: f"Every {x} day{'s' if x > 1 else ''}",
            key="auto_interval_days",
        )
        st.caption("Requires browser tab to be open. Good for 2–3× per week scans.")
        st.divider()
        notify_email = st.text_input(
            "Notify email", key="notify_email", placeholder="you@gmail.com"
        )
        smtp_user = st.text_input(
            "Gmail (sender)", key="smtp_user", placeholder="sender@gmail.com"
        )
        smtp_pass = st.text_input(
            "Gmail App Password", key="smtp_pass", type="password",
            placeholder="xxxx xxxx xxxx xxxx",
        )
        st.caption("Use a [Gmail App Password](https://support.google.com/accounts/answer/185833), not your login password.")

    if st.button("↺ Reset Filters", use_container_width=True):
        st.session_state["_sidebar_reset"] = True
        st.rerun()

    run_btn = st.button(
        "🔄 Fetch & Score Listings", type="primary", use_container_width=True
    )

# ── cfg and filters — computed every render so display always has them ──────
cfg = {
    "min_cashflow":   min_cashflow,
    "min_price":      min_price,
    "max_price":      max_price,
    "min_multiple":   min_multiple,
    "max_multiple":   max_multiple,
    "selected_states": selected_states,
}
industry_kws = [i.lower() for i in selected_industries]
if custom_kw:
    industry_kws += [k.strip().lower() for k in custom_kw.split(",") if k.strip()]

# ── Auto-scan trigger ─────────────────────────────────────────────────────────
_auto_run = False
if st.session_state.get("auto_scan_on"):
    _interval_days = int(st.session_state.get("auto_interval_days", 2))
    _interval_ms   = _interval_days * 86_400_000
    _refresh_ct    = st_autorefresh(interval=_interval_ms, key="auto_scan_refresh")
    if _refresh_ct > 0 and _refresh_ct != st.session_state.get("_prev_refresh_ct", -1):
        st.session_state["_prev_refresh_ct"] = _refresh_ct
        _auto_run = True

# ─────────────────────────────────────────────
# DIRECT OUTREACH — LLR + GOOGLE PLACES
# ─────────────────────────────────────────────

_CORPORATE_INDICATORS = [
    "holdings", "national", " group", "partners", "capital",
    "industries", "inc.", ", inc", "llc", "corp", "franchise",
    "services llc", "management llc",
]
_FRANCHISE_NAMES = [
    "aire serv", "one hour", "service experts", "lennox", "carrier",
    "trane", "comfort systems", "abc fire", "cintas", "convergint",
    "johnson controls", "siemens", "tyco", "simplex", "hochiki",
]

# Yelp industry → categories + HALO mapping
_YELP_INDUSTRY_MAP: dict[str, dict] = {
    "HVAC / Air Conditioning": {
        "categories": "heating_air,airconditioningrepair",
        "halo_industry": "HVAC", "halo_score": 20,
    },
    "Fire Protection": {
        "categories": "fire_protection_services",
        "halo_industry": "Fire Protection", "halo_score": 20,
    },
    "Plumbing": {
        "categories": "plumbing",
        "halo_industry": "Plumbing", "halo_score": 12,
    },
    "Electrical": {
        "categories": "electricians",
        "halo_industry": "Electrical", "halo_score": 12,
    },
    "Environmental / Industrial": {
        "categories": "environmental_services,industrialcleaning",
        "halo_industry": "Environmental / Industrial", "halo_score": 12,
    },
    "Marine Services": {
        "categories": "boatrepairandmaintenance,marineservices",
        "halo_industry": "Marine Services", "halo_score": 6,
    },
    "Pest Control": {
        "categories": "pestcontrol",
        "halo_industry": "Pest Control", "halo_score": 12,
    },
    "Commercial Cleaning / Linen": {
        "categories": "officecleaning,commercialcleaning,laundrycleaningservices",
        "halo_industry": "Commercial Cleaning", "halo_score": 10,
    },
    "Fuel / Propane Distribution": {
        "categories": "propane,fueldealers",
        "halo_industry": "Fuel Distribution", "halo_score": 8,
    },
    "Self-Storage": {
        "categories": "selfstorage",
        "halo_industry": "Self-Storage", "halo_score": 8,
    },
}

# Google Places category → HALO industry mapping
_PLACES_CATEGORY_HALO: dict[str, tuple[str, int]] = {
    "hvac contractor":             ("HVAC", 20),
    "air conditioning contractor": ("HVAC", 20),
    "heating contractor":          ("HVAC", 20),
    "refrigeration contractor":    ("HVAC", 20),
    "fire protection":             ("Fire Protection", 20),
    "fire sprinkler":              ("Fire Protection", 20),
    "plumber":                     ("Plumbing", 12),
    "plumbing contractor":         ("Plumbing", 12),
    "electrician":                 ("Electrical", 12),
    "electrical contractor":       ("Electrical", 12),
    "environmental":               ("Environmental / Industrial", 12),
    "marine":                      ("Marine Services", 6),
    "pest control":                ("Pest Control", 12),
    "commercial cleaning":         ("Commercial Cleaning", 10),
}


def score_outreach_target(target: dict) -> dict:
    """Score a direct outreach target (LLR or Google Places)."""
    score   = 50
    signals = []
    flags   = []

    name_lower = (target.get("company") or "").lower()

    # HALO tier
    halo_adj = target.get("halo_score", 0)
    industry = target.get("industry", "")
    if halo_adj >= 20:
        score += 20; signals.append(f"Tier 1 industry ({industry})")
    elif halo_adj >= 10:
        score += 10; signals.append(f"Tier 2 industry ({industry})")

    # Business age from LLR license date
    lic_year = target.get("license_year")
    if lic_year:
        age = datetime.now().year - lic_year
        if age >= 25:
            score += 18; signals.append(f"In business ~{age} yrs — prime succession gap")
        elif age >= 15:
            score += 12; signals.append(f"In business ~{age} yrs — likely succession gap")
        elif age >= 8:
            score += 5;  signals.append(f"In business ~{age} yrs")
        elif age < 4:
            score -= 15; flags.append(f"Business only ~{age} yrs old — too early")

    # Owner name (individual person = good signal)
    owner = target.get("owner") or ""
    if owner and not any(c.isdigit() for c in owner):
        words = owner.strip().split()
        if len(words) >= 2 and not any(corp in owner.lower() for corp in ["llc", "inc", "corp"]):
            score += 10; signals.append(f"Individual owner on record: {owner}")

    # Tri-county Charleston geography
    city_lower = (target.get("city") or "").lower()
    tri_county = ["charleston", "north charleston", "mount pleasant", "summerville",
                  "goose creek", "hanahan", "ladson", "moncks corner", "isle of palms",
                  "folly beach", "james island", "johns island", "daniel island",
                  "berkeley", "dorchester"]
    if any(c in city_lower for c in tri_county):
        score += 10; signals.append("Charleston tri-county")
    elif "south carolina" in (target.get("state") or "").lower() or ", sc" in city_lower:
        score += 4

    # Google review count — size proxy
    reviews = target.get("review_count") or 0
    if 20 <= reviews <= 150:
        score += 8; signals.append(f"{reviews} reviews — right-sized")
    elif reviews > 150:
        score += 3; signals.append(f"{reviews} reviews — may be larger/institutionalized")
    elif reviews > 0:
        score += 2

    # Rating sweet spot
    rating = target.get("rating") or 0
    if 4.0 <= rating <= 4.7:
        score += 5; signals.append(f"{rating:.1f}★ rating")
    elif rating > 4.7:
        score += 2

    # Franchise / chain flag
    if any(f in name_lower for f in _FRANCHISE_NAMES):
        score -= 30; flags.append("Franchise / national brand — no ownership upside")

    # Corporate / PE indicators
    if any(ind in name_lower for ind in ["holdings", " national", "partners lp", "capital group"]):
        score -= 20; flags.append("Corporate/PE indicator in name")

    # Already in pipeline
    if target.get("in_pipeline"):
        score -= 10; flags.append("Already in pipeline")

    score = max(0, min(100, score))

    if score >= 75:
        grade = "🟢"
    elif score >= 45:
        grade = "🟡"
    else:
        grade = "🔴"

    return {**target, "score": score, "grade": grade,
            "signals": "; ".join(signals), "flags": "; ".join(flags)}


def fetch_foursquare_targets(industries: list[str], api_key: str) -> list[dict]:
    """
    Query Foursquare Places API (v3) for local businesses.
    Free tier: 1,000 calls/day, no credit card.
    Get key: developer.foursquare.com → Create Account → Create App.
    """
    if not api_key:
        return []
    try:
        import requests as _req
    except ImportError:
        return []

    # Charleston, SC center
    LL = "32.7765,-79.9311"
    BASE = "https://api.foursquare.com/v3/places/search"
    headers = {
        "Authorization": api_key,
        "Accept":        "application/json",
    }

    # Industry → Foursquare text queries
    _FSQ_QUERIES: dict[str, list[str]] = {
        "HVAC / Air Conditioning":    ["HVAC", "air conditioning contractor", "heating cooling"],
        "Fire Protection":            ["fire protection", "fire sprinkler", "fire suppression"],
        "Plumbing":                   ["plumbing contractor", "plumber"],
        "Electrical":                 ["electrical contractor", "electrician"],
        "Environmental / Industrial": ["environmental services", "industrial services"],
        "Marine Services":            ["marine contractor", "boat repair", "marine services"],
        "Pest Control":               ["pest control", "exterminator"],
        "Commercial Cleaning / Linen":["commercial cleaning", "linen service", "laundry service"],
        "Fuel / Propane Distribution":["propane", "fuel distribution", "propane delivery"],
        "Self-Storage":               ["self storage", "storage facility"],
    }

    results = []
    seen: set[str] = set()

    for industry in industries:
        cfg     = _YELP_INDUSTRY_MAP.get(industry)
        queries = _FSQ_QUERIES.get(industry, [industry])
        if not cfg:
            continue
        for query in queries:
            try:
                params = {
                    "query":  query,
                    "ll":     LL,
                    "radius": 50000,   # ~31 miles — covers tri-county
                    "limit":  50,
                    "fields": "fsq_id,name,location,tel,website,rating,stats,categories",
                }
                resp = _req.get(BASE, headers=headers, params=params, timeout=12)
                if resp.status_code == 401:
                    return [{"_error": "fsq_auth"}]
                if resp.status_code != 200:
                    continue
                for biz in resp.json().get("results", []):
                    uid = f"fsq_{biz.get('fsq_id','')}"
                    if uid in seen:
                        continue
                    seen.add(uid)
                    loc  = biz.get("location", {})
                    cats = [c.get("name", "") for c in biz.get("categories", [])]
                    stats = biz.get("stats", {})
                    results.append({
                        "source":       "Foursquare",
                        "uid":          uid,
                        "company":      biz.get("name", ""),
                        "owner":        "",
                        "city":         loc.get("locality", ""),
                        "state":        loc.get("region", ""),
                        "county":       "",
                        "address":      loc.get("address", ""),
                        "phone":        biz.get("tel", ""),
                        "website":      biz.get("website", ""),
                        "industry":     cfg["halo_industry"],
                        "halo_score":   cfg["halo_score"],
                        "categories":   cats,
                        "rating":       biz.get("rating", 0),
                        "review_count": stats.get("total_ratings", 0),
                        "license_year": None,
                        "license_num":  "",
                    })
            except Exception:
                continue

    return results



def fetch_google_places_targets(
    industries: list[str], location: str, radius_m: int, api_key: str
) -> list[dict]:
    """
    Query Google Places Text Search API for businesses by industry + location.
    Returns a list of target dicts.
    """
    if not api_key:
        return []

    try:
        import requests as _req
    except ImportError:
        return []

    PLACES_URL = "https://maps.googleapis.com/maps/api/place/textsearch/json"
    DETAILS_URL = "https://maps.googleapis.com/maps/api/place/details/json"

    results = []
    seen = set()

    # Build search queries per industry
    industry_queries = {
        "HVAC":                       ["HVAC contractor", "air conditioning contractor", "heating cooling contractor"],
        "Fire Protection":            ["fire protection contractor", "fire sprinkler company"],
        "Environmental / Industrial": ["environmental services contractor", "industrial cleaning"],
        "Marine Services":            ["marine services", "boat repair marina"],
        "Plumbing":                   ["plumbing contractor"],
        "Electrical":                 ["electrical contractor"],
        "Pest Control":               ["pest control company"],
        "Commercial Cleaning":        ["commercial cleaning service janitorial"],
    }

    for industry in industries:
        queries = industry_queries.get(industry, [industry.lower()])
        halo_adj = _HALO_SCORE.get(industry, 0)

        for query in queries:
            try:
                params = {
                    "query":    f"{query} {location}",
                    "type":     "establishment",
                    "key":      api_key,
                }
                resp = _req.get(PLACES_URL, params=params, timeout=10)
                if resp.status_code != 200:
                    continue
                data = resp.json()
                if data.get("status") not in ("OK", "ZERO_RESULTS"):
                    continue

                for place in data.get("results", []):
                    pid = place.get("place_id", "")
                    if pid in seen:
                        continue
                    seen.add(pid)

                    name    = place.get("name", "")
                    address = place.get("formatted_address", "")
                    rating  = place.get("rating")
                    reviews = place.get("user_ratings_total")
                    types   = place.get("types", [])

                    # Extract city from address
                    addr_parts = address.split(",")
                    city = addr_parts[1].strip() if len(addr_parts) > 1 else ""

                    # Get phone + website from details (one extra call per place)
                    phone, website = "", ""
                    try:
                        det = _req.get(DETAILS_URL, params={
                            "place_id": pid,
                            "fields": "formatted_phone_number,website",
                            "key": api_key,
                        }, timeout=8).json()
                        res = det.get("result", {})
                        phone   = res.get("formatted_phone_number", "")
                        website = res.get("website", "")
                    except Exception:
                        pass

                    results.append({
                        "source":       "Google Places",
                        "uid":          f"gp_{pid}",
                        "company":      name,
                        "owner":        "",
                        "city":         city,
                        "state":        "SC",
                        "county":       "",
                        "phone":        phone,
                        "website":      website,
                        "license_type": "",
                        "license_num":  "",
                        "license_year": None,
                        "industry":     industry,
                        "halo_score":   halo_adj,
                        "rating":       rating,
                        "review_count": reviews,
                    })
            except Exception:
                continue

    return results


tab_search, tab_outreach, tab_pipeline = st.tabs(["🔍 Search", "🎯 Outreach", "📋 Pipeline"])

# ════════════════════════════════════════════════════════════════════════════
# OUTREACH TAB
# ════════════════════════════════════════════════════════════════════════════
with tab_outreach:
    st.subheader("🎯 Direct Outreach Target Finder")
    st.caption(
        "Find owner-operated businesses in the Charleston MSA. Score by HALO tier, reviews, and geography. Add to pipeline."
    )

    pipeline = load_pipeline()
    pipeline_uids = {v.get("listing", {}).get("uid", "") for v in pipeline.values()}

    ot_c1, ot_c2 = st.columns([2, 1])
    with ot_c1:
        ot_source = st.multiselect(
            "Data source",
            ["Foursquare Places", "Google Places"],
            default=["Foursquare Places"],
            key="ot_source",
        )
        ot_industries = st.multiselect(
            "Industries",
            list(_YELP_INDUSTRY_MAP.keys()),
            default=["HVAC / Air Conditioning", "Fire Protection"],
            key="ot_industries",
        )
        ot_counties = st.multiselect(
            "Counties (SC)",
            ["Charleston", "Berkeley", "Dorchester"],
            default=["Charleston", "Berkeley", "Dorchester"],
            key="ot_counties",
        )
    with ot_c2:
        ot_min_score = st.slider("Min score", 0, 100, 45, key="ot_min_score")
        ot_grades = st.multiselect(
            "Show grades",
            ["🟢 High Priority", "🟡 Research", "🔴 Low Priority"],
            default=["🟢 High Priority", "🟡 Research"],
            key="ot_grades",
        )

    # API keys in a collapsible expander — stays out of the way once entered
    _ot_has_fsq = bool(st.session_state.get("ot_yelp_key", ""))
    _ot_has_gp  = bool(st.session_state.get("ot_gplaces_key", ""))
    with st.expander("🔑 API Keys", expanded=not (_ot_has_fsq or _ot_has_gp)):
        yelp_key = st.text_input(
            "Foursquare API Key",
            type="password",
            placeholder="Free at developer.foursquare.com — no credit card",
            key="ot_yelp_key",
        )
        gplaces_key = st.text_input(
            "Google Places API Key",
            type="password",
            placeholder="Required for Google Places source",
            key="ot_gplaces_key",
        )

    # Map text-label grade options back to emoji for filtering
    _OT_GRADE_MAP = {
        "🟢 High Priority": "🟢",
        "🟡 Research":      "🟡",
        "🔴 Low Priority":  "🔴",
    }
    _ot_grade_filter = [_OT_GRADE_MAP[g] for g in ot_grades if g in _OT_GRADE_MAP]

    _needs_fsq    = "Foursquare Places" in ot_source and not yelp_key
    _needs_gplace = "Google Places" in ot_source and not gplaces_key
    _needs_key    = _needs_fsq or _needs_gplace
    if _needs_fsq:
        st.warning("A Foursquare API key is required. Get a free key (no credit card) at developer.foursquare.com → Create App.")
    if _needs_gplace:
        st.warning("A Google Places API key is required. Enter one above or deselect Google Places.")
    ot_run = st.button("🔍 Find Targets", type="primary", key="ot_run_btn", disabled=_needs_key)

    if ot_run:
        _ot_results = []
        with st.spinner("Fetching targets..."):
            if "Foursquare Places" in ot_source and yelp_key:
                fsq_results = fetch_foursquare_targets(ot_industries, yelp_key)
                if fsq_results and fsq_results[0].get("_error") == "fsq_auth":
                    st.error("Foursquare API key rejected (401). Check the key at developer.foursquare.com.")
                    fsq_results = []
                _ot_results.extend(fsq_results)

            if "Google Places" in ot_source and gplaces_key:
                gp_industries = [i for i in ot_industries if i in _HALO_SCORE]
                if gp_industries:
                    gp_results = fetch_google_places_targets(
                        gp_industries, "Charleston SC", 40000, gplaces_key
                    )
                    _ot_results.extend(gp_results)

        # Mark already-in-pipeline
        for t in _ot_results:
            t["in_pipeline"] = t.get("uid", "") in pipeline_uids

        # Score all targets
        _ot_scored = [score_outreach_target(t) for t in _ot_results]
        _ot_scored.sort(key=lambda x: x["score"], reverse=True)

        st.session_state["ot_results"]   = _ot_scored
        st.session_state["ot_last_run"]  = _run_ts()

    _ot_scored = st.session_state.get("ot_results", [])

    if _ot_scored:
        _filtered = [
            t for t in _ot_scored
            if t["score"] >= ot_min_score and t["grade"] in _ot_grade_filter
        ]
        _ot_ts = st.session_state.get("ot_last_run", "")
        _ot_ts_str = f"  ·  Last fetched: {_ot_ts}" if _ot_ts else ""
        st.markdown(f"**{len(_filtered)} targets shown** ({len(_ot_scored)} total){_ot_ts_str}")

        # Summary counts by grade
        g_counts = {"🟢": 0, "🟡": 0, "🔴": 0}
        for t in _ot_scored:
            g_counts[t["grade"]] = g_counts.get(t["grade"], 0) + 1
        st.caption(
            f"🟢 {g_counts['🟢']} high priority  ·  "
            f"🟡 {g_counts['🟡']} research  ·  "
            f"🔴 {g_counts['🔴']} low priority"
        )

        for t in _filtered:
            _in_pipe = t.get("in_pipeline") or (t.get("uid", "") in {
                v.get("listing", {}).get("uid", "") for v in load_pipeline().values()
            })
            _label = (
                f"{t['grade']} [{t['score']}/100]  {t['company']}  —  "
                f"{t.get('city', '')}  |  {t.get('industry', '')}  |  {t.get('source', '')}"
            )
            with st.expander(_label, expanded=False):
                oc1, _ = st.columns([1, 3])
                oc1.metric("Score", f"{t['score']}/100")
                st.markdown(
                    f"**Industry:** {t.get('industry','—')}  ·  "
                    f"**Source:** {t.get('source','—')}  ·  "
                    f"**City:** {t.get('city','—')}"
                )

                if t.get("owner"):
                    st.markdown(f"**Owner / Licensee:** {t['owner']}")
                if t.get("phone"):
                    st.markdown(f"**Phone:** {t['phone']}")
                if t.get("website"):
                    st.markdown(f"**Website:** {t['website']}")
                if t.get("license_num"):
                    st.markdown(f"**License #:** {t['license_num']}  ({t.get('license_type','')})")
                if t.get("rating"):
                    st.markdown(f"**Google Rating:** {t['rating']:.1f}★  ({t.get('review_count',0)} reviews)")
                if t.get("signals") and t["signals"] != "—":
                    st.markdown(f"**Signals:** {t['signals']}")
                if t.get("flags") and t["flags"] != "—":
                    st.markdown(f"**Flags:** {t['flags']}")

                if _in_pipe:
                    st.caption("✅ Already in pipeline")
                else:
                    if st.button("➕ Add to Pipeline", key=f"ot_pipe_{t.get('uid','')}{t['score']}"):
                        # Build a listing-compatible dict for pipeline
                        _ot_listing = {
                            "uid":           t.get("uid", ""),
                            "title":         t["company"],
                            "business_type": t.get("industry", ""),
                            "location":      f"{t.get('city','')}, {t.get('state','SC')}",
                            "source":        t.get("source", "Direct Outreach"),
                            "phone":         t.get("phone", ""),
                            "website":       t.get("website", ""),
                            "owner":         t.get("owner", ""),
                            "license_num":   t.get("license_num", ""),
                            "score":         t["score"],
                            "asking_price":  None,
                            "cash_flow":     None,
                            "url":           t.get("website", ""),
                        }
                        pipeline_add(_ot_listing)
                        t["in_pipeline"] = True
                        st.rerun()

    elif not ot_run:
        st.info(
            "Configure sources and industries above, then click **Find Targets**.\n\n"
            "Foursquare Places provides local business data — free tier, no credit card required. "
            "Google Places requires a free API key from Google Cloud Console."
        )

# ── Scraping (only when Run is clicked) ────────────────────────────────────
with tab_search:
    # ── Scraping (only when Run is clicked) ──────────────────────────────
    if run_btn or _auto_run:
        if not selected_states:
            st.error("Select at least one state.")
            st.stop()

        credentials = {"BizBuySell": {}, "BizQuest": {}}

        scrapers = []
        if use_bbs: scrapers.append("BizBuySell")
        if use_bq:  scrapers.append("BizQuest")

        all_listings = []
        prog         = st.progress(0.0, text="Starting…")
        n_sources    = len(scrapers)
        total_ops    = n_sources * len(selected_states) * pages
        completed_ops = [0]

        def make_progress_cb(source_idx: int):
            def cb(msg: str):
                completed_ops[0] += 1
                frac = min(completed_ops[0] / max(total_ops, 1), 0.97)
                prog.progress(frac, text=msg)
            return cb

        for i, name in enumerate(scrapers):
            prog.progress(i / n_sources, text=f"Fetching {name}…")
            with st.status(f"📡 {name}", expanded=True) as status:
                cb  = make_progress_cb(i)
                raw = scrape_source(name, cfg, pages, selected_states, credentials,
                                    progress_cb=cb)
                scored = [score_deal(l, cfg) for l in raw]
                all_listings.extend(scored)
                status.update(
                    label=f"✅ {name} — {len(raw)} listings fetched",
                    state="complete", expanded=False,
                )
            st.toast(f"✅ {name}: {len(raw)} listings")

        prog.progress(1.0, text="Done.")
        st.session_state["raw_all_listings"] = all_listings
        st.session_state["last_run_time"]    = _run_ts()

        if not all_listings:
            st.error(
                "No listings returned. Try widening your filters "
                "(lower min cash flow, higher max price, or more pages)."
            )
            st.stop()

        # Signal display block to auto-add + email after filtering
        st.session_state["_scan_just_ran"] = True
        st.session_state["_scan_auto"]     = _auto_run

    # ── Display (runs whenever results exist) ────────────────────────────
    if "raw_all_listings" in st.session_state:
        all_listings = st.session_state["raw_all_listings"]
        pipeline     = load_pipeline()

        df = pd.DataFrame(all_listings)
        if "listing_id" in df.columns:
            df = df.drop_duplicates(subset=["listing_id"], keep="first")
        if target_only and "location" in df.columns:
            df = df[df["location"].apply(
                lambda x: is_target_location(str(x), selected_states)
            )]
        if industry_kws and "title" in df.columns:
            def matches_industry(row):
                haystack = (
                    (row.get("business_type") or "") + " " +
                    (row.get("title") or "") + " " +
                    (row.get("description") or "")
                ).lower()
                return any(kw in haystack for kw in industry_kws)
            df = df[df.apply(matches_industry, axis=1)]
        if "grade" in df.columns and show_grades:
            df = df[df["grade"].isin(show_grades)]
        if "score" in df.columns:
            df = df[df["score"] >= min_score]
        df = df.sort_values("score", ascending=False).reset_index(drop=True)

        # ── Metrics row ───────────────────────────────────────────────────
        c1, c2, c3, c4, c5 = st.columns(5)
        c1.metric("Total Fetched",  len(all_listings))
        c2.metric("After Filters",  len(df))
        c3.metric("🟢 Look Closer", sum(1 for l in df.to_dict("records") if "🟢" in l.get("grade", "")))
        c4.metric("🟡 Marginal",    sum(1 for l in df.to_dict("records") if "🟡" in l.get("grade", "")))
        c5.metric("Last Run",       st.session_state.get("last_run_time", "—"))

        # ── Active filter summary ─────────────────────────────────────────
        _active_parts = []
        if target_only:
            _active_parts.append(f"📍 {', '.join(selected_states) or 'All states'}")
        if industry_kws:
            _active_parts.append(f"🏭 {', '.join(i.title() for i in industry_kws[:3])}{'…' if len(industry_kws) > 3 else ''}")
        if show_grades != ["🟢 Look Closer", "🟡 Marginal", "🔴 Skip"]:
            _active_parts.append(f"Grade: {' '.join(show_grades)}")
        if min_score > 0:
            _active_parts.append(f"Score ≥ {min_score}")
        if _active_parts:
            _af_c1, _af_c2 = st.columns([5, 1])
            _af_c1.caption("Filters active: " + "  ·  ".join(_active_parts))
            if _af_c2.button("↺ Reset", key="inline_reset"):
                st.session_state["_sidebar_reset"] = True
                st.rerun()
        st.divider()

        if df.empty:
            st.info(
                "No listings matched your filters. "
                "Try lowering Min Score, unchecking 'Target states only', or broadening criteria."
            )
        else:
            display_cols = [c for c in [
                "grade", "score", "business_type", "title",
                "asking_price", "cash_flow", "multiple", "est_dscr",
                "location", "signals", "flags", "url",
            ] if c in df.columns]

            show_df = df[display_cols].copy()

            def color_row(row):
                g = str(row.get("grade", ""))
                bg = ("#d4edda" if "🟢" in g else
                      "#fff3cd" if "🟡" in g else
                      "#f8d7da" if "🔴" in g else "")
                return [f"background-color:{bg}"] * len(row)

            st.dataframe(
                show_df.style.apply(color_row, axis=1),
                use_container_width=True,
                height=580,
                column_config={
                    "grade":        st.column_config.TextColumn("Grade",     width="small"),
                    "score":        st.column_config.NumberColumn("Score",   format="%d", width="small"),
                    "business_type":st.column_config.TextColumn("Industry",  width="small"),
                    "title":        st.column_config.TextColumn("Business",  width="large"),
                    "asking_price": st.column_config.NumberColumn("Asking",  format="$%.0f", width="small"),
                    "cash_flow":    st.column_config.NumberColumn("CF",      format="$%.0f", width="small"),
                    "multiple":     st.column_config.NumberColumn("Multiple",format="%.1fx", width="small"),
                    "est_dscr":     st.column_config.NumberColumn("DSCR",    format="%.2f",  width="small"),
                    "location":     st.column_config.TextColumn("Location",  width="small"),
                    "signals":      st.column_config.TextColumn("Signals",   width="medium"),
                    "flags":        st.column_config.TextColumn("Flags",     width="medium"),
                    "url":          st.column_config.LinkColumn("Link",      display_text="Open →", width="small"),
                },
            )

            # ── CSV exports ───────────────────────────────────────────────
            _raw = st.session_state.get("raw_all_listings", all_listings)
            _dl1, _dl2 = st.columns(2)
            _dl1.download_button(
                f"⬇️ Filtered Results (CSV) — {len(df)} listings",
                data=df.to_csv(index=False),
                file_name=f"dealfinder_filtered_{datetime.now().strftime('%Y%m%d_%H%M')}.csv",
                mime="text/csv",
            )
            _dl2.download_button(
                f"⬇️ Full Results (CSV) — {len(_raw)} listings",
                data=pd.DataFrame(_raw).to_csv(index=False),
                file_name=f"dealfinder_full_{datetime.now().strftime('%Y%m%d_%H%M')}.csv",
                mime="text/csv",
            )

            # ── Green deal cards ──────────────────────────────────────────
            greens = df[df["grade"].str.startswith("🟢")] if "grade" in df.columns else pd.DataFrame()

            # Auto-add filtered greens to pipeline (runs once right after each scrape)
            if st.session_state.pop("_scan_just_ran", False):
                _new_additions = []
                for _, _row in greens.iterrows():
                    if pipeline_add(dict(_row)):
                        _new_additions.append(_row.get("title", "Untitled"))
                if _new_additions:
                    st.toast(f"➕ {len(_new_additions)} new green deal(s) added to pipeline", icon="🟢")
                    pipeline = load_pipeline()  # refresh so cards show updated in_pipe state

                # Email notification on auto-scan
                if st.session_state.pop("_scan_auto", False):
                    _notify_to = st.session_state.get("notify_email", "").strip()
                    _smtp_user = st.session_state.get("smtp_user",    "").strip()
                    _smtp_pass = st.session_state.get("smtp_pass",    "").strip()
                    if _notify_to and _smtp_user and _smtp_pass:
                        _ts   = datetime.now().strftime("%Y-%m-%d %H:%M")
                        _subj = f"DealFinder Auto-Scan — {len(df)} listings, {len(_new_additions)} new green"
                        _body = [
                            f"DealFinder auto-scan completed at {_ts}.",
                            f"Total listings after filters: {len(df)}",
                            f"New green deals added to pipeline: {len(_new_additions)}",
                        ]
                        if _new_additions:
                            _body.append("\nNew additions:")
                            for _t in _new_additions:
                                _body.append(f"  • {_t}")
                        _err = send_scan_email(_notify_to, _smtp_user, _smtp_pass, _subj, "\n".join(_body))
                        if _err:
                            st.warning(f"Email failed: {_err}")
                        else:
                            st.toast("📧 Scan summary emailed", icon="✉️")
                else:
                    st.session_state.pop("_scan_auto", None)

            if not greens.empty:
                st.divider()
                st.subheader(f"🟢 Deals Worth a Closer Look ({len(greens)})")
                for idx, (_, row) in enumerate(greens.iterrows()):
                    label = f"{row.get('title','Untitled')} — {row.get('location','?')} — Score {row.get('score','?')}/100"
                    if row.get("business_type"):
                        label = f"[{row['business_type']}] {label}"

                    plkey   = pipeline_key(dict(row))
                    in_pipe = plkey in pipeline

                    with st.expander(label, expanded=False):
                        col1, col2, col3, col4 = st.columns(4)
                        col1.metric("Asking",    fmt_k(row.get("asking_price")))
                        col2.metric("Cash Flow", fmt_k(row.get("cash_flow")))
                        col3.metric("Multiple",  f"{row['multiple']:.1f}x"  if row.get("multiple") else "—")
                        col4.metric("Est. DSCR", f"{row['est_dscr']:.2f}x"  if row.get("est_dscr") else "—")
                        st.markdown(
                            f"**Source:** {row.get('source','—')}  |  "
                            f"**Type:** {row.get('business_type','—')}  |  "
                            f"**Location:** {row.get('location','—')}"
                        )
                        # Flags as inline tags
                        _raw_flags = row.get("flags", "")
                        if _raw_flags and _raw_flags != "—":
                            _flag_tags = "  ".join(
                                f"`{f.strip()}`" for f in _raw_flags.split("|") if f.strip()
                            )
                            st.markdown(f"**⚑ Flags:** {_flag_tags}")
                        # Signals as inline tags
                        _raw_sigs = row.get("signals", "")
                        if _raw_sigs and _raw_sigs != "—":
                            _sig_tags = "  ".join(
                                f"`{s.strip()}`" for s in _raw_sigs.split("|") if s.strip()
                            )
                            st.markdown(f"**✓ Signals:** {_sig_tags}")
                        # Quick overview bullets
                        _bullets = _quick_bullets(row.get("description", ""))
                        if _bullets:
                            st.markdown("**Overview:**")
                            for _b in _bullets:
                                st.markdown(f"- {_b}")
                        elif row.get("description"):
                            st.markdown(f"<small>{row['description']}</small>",
                                        unsafe_allow_html=True)

                        # Action buttons
                        btn_c1, btn_c2 = st.columns(2)
                        with btn_c1:
                            if row.get("url"):
                                st.link_button("🔗 Open Listing", row["url"])
                        with btn_c2:
                            if in_pipe:
                                st.caption(f"✅ Pipeline: *{pipeline[plkey]['stage']}*")
                            else:
                                if st.button("➕ Add to Pipeline", key=f"pipe_add_{idx}"):
                                    pipeline_add(dict(row))
                                    pipeline = load_pipeline()
                                    st.toast("➕ Added to pipeline", icon="✅")
                                    st.rerun()

    else:
        # ── Landing page (before first run) ──────────────────────────────
        st.info(
            "Configure your criteria in the sidebar, then click **Fetch & Score Listings**.\n\n"
            "The tool calls the BizBuySell API directly and scores every listing against your "
            "criteria — multiple, DSCR, location, and quality signals. A run typically takes **15–30 seconds**."
        )
        with st.expander("📖 How scoring works"):
            st.markdown("""
| Layer | What it checks | Impact |
|---|---|---|
| **Multiple** | Asking ÷ Cash Flow vs your min/max range | −20 to −30 pts |
| **DSCR** | SBA 7(a): 90% LTV · 10-yr · 7.5% interest; must clear 1.25x | −25 pts if <1.25x |
| **SBA limit** | Asking price exceeds $5M SBA 7(a) cap | −15 pts |
| **HALO tier** | Industry alignment (HVAC/Fire +20 → Routes/Restaurant −25) | −25 to +20 pts |
| **Red flags** | "turnkey", "absentee", "motivated seller", "e-commerce", etc. | −12 pts each |
| **Quality signals** | "recurring", "service contract", "B2B", "management team" | +5 pts each |
| **Location** | Confirmed in a target state | +10 or −15 pts |
| **Missing CF** | Cash flow not shown (gated behind login) | −30 pts |

**Grade thresholds:** 🟢 ≥75 · 🟡 44–74 · 🔴 <44
            """)
        with st.expander("⚠️ Notes"):
            st.markdown("""
- Scores are heuristic triage, not financial analysis. 🟢 means *look closer* — not *buy it*.
- The state filter surfaces national "featured" listings first. Use **Target states only** to filter those out.
- The best deals are off-market and won't appear here at all.
            """)


# ── Pipeline Tab ─────────────────────────────────────────────────────────────
with tab_pipeline:
    pipeline = load_pipeline()

    # Show Google Sheets connection status
    _gsheet_err = st.session_state.get("_gsheet_error")
    if _gsheet_err:
        st.error(f"⚠️ Google Sheets connection failed — showing local data only.\n\n`{_gsheet_err}`")
    else:
        st.caption("✅ Pipeline synced with Google Sheets")

    # ── Per-stage summary counts — one metric per stage ───────────────────
    _sc: dict = {}
    for _pe in pipeline.values():
        _s = _pe.get("stage", "New")
        _sc[_s] = _sc.get(_s, 0) + 1
    _active_count = sum(_sc.get(s, 0) for s in PIPELINE_STAGES if s not in ("Pass", "Closed"))
    # Only show stages with count > 0, never show Pass
    _visible_stages = [s for s in PIPELINE_STAGES if s != "Pass" and _sc.get(s, 0) > 0]
    _stage_cols = st.columns(len(_visible_stages) + 1)
    _stage_cols[0].metric("Total", len(pipeline))
    for _ci, _st_label in enumerate(_visible_stages):
        _stage_cols[_ci + 1].metric(_st_label, _sc[_st_label])

    if not pipeline:
        st.info(
            "No deals in pipeline yet. Run a search in the **Search** tab, "
            "then click **➕ Pipeline** on any 🟢 deal card."
        )
    else:
        # ── Filter + sort controls ─────────────────────────────────────────
        _fc1, _fc2, _fc3 = st.columns([2, 3, 1])
        with _fc1:
            _pipe_search = st.text_input(
                "Search", placeholder="Title, industry, location…",
                key="pipe_search", label_visibility="collapsed",
            )
        with _fc2:
            _pipe_stage_filter = st.multiselect(
                "Stages", PIPELINE_STAGES,
                default=[s for s in PIPELINE_STAGES if s != "Pass"],
                key="pipe_stage_filter",
                placeholder="Filter by stage…",
                label_visibility="collapsed",
            )
        with _fc3:
            sort_by = st.selectbox(
                "Sort", ["Stage order", "Date Added", "Score", "Asking Price"],
                key="pipe_sort", label_visibility="collapsed",
            )

        # ── Build rows ─────────────────────────────────────────────────────
        rows = []
        for key, entry in pipeline.items():
            lst = entry.get("listing", {})
            rows.append({
                "_key":          key,
                "stage":         entry.get("stage", "New"),
                "title":         lst.get("title", "?"),
                "business_type": lst.get("business_type", ""),
                "asking_price":  lst.get("asking_price"),
                "cash_flow":     lst.get("cash_flow"),
                "multiple":      lst.get("multiple"),
                "est_dscr":      lst.get("est_dscr"),
                "score":         lst.get("score"),
                "location":      lst.get("location", ""),
                "url":           lst.get("url", ""),
                "date_added":    entry.get("date_added", ""),
                "notes":         entry.get("notes", ""),
            })

        df_pipe = pd.DataFrame(rows)

        # Apply stage filter — always enforce; empty selection hides Pass by default
        _effective_stage_filter = (
            _pipe_stage_filter if _pipe_stage_filter
            else [s for s in PIPELINE_STAGES if s != "Pass"]
        )
        df_pipe = df_pipe[df_pipe["stage"].isin(_effective_stage_filter)]
        _pass_hidden = _sc.get("Pass", 0) if "Pass" not in _effective_stage_filter else 0
        if _pass_hidden:
            st.caption(f"ℹ️ {_pass_hidden} deal(s) marked Pass are hidden — add **Pass** to the stage filter above to show them.")

        # Apply text search
        if _pipe_search:
            _sq = _pipe_search.lower()
            df_pipe = df_pipe[
                df_pipe["title"].str.lower().str.contains(_sq, na=False)
                | df_pipe["business_type"].str.lower().str.contains(_sq, na=False)
                | df_pipe["location"].str.lower().str.contains(_sq, na=False)
            ]

        # Sort
        if sort_by == "Stage order":
            _so_map = {s: i for i, s in enumerate(PIPELINE_STAGES)}
            df_pipe["_so"] = df_pipe["stage"].map(_so_map).fillna(99)
            df_pipe = df_pipe.sort_values("_so").drop(columns=["_so"])
        elif sort_by == "Date Added":
            df_pipe = df_pipe.sort_values("date_added", ascending=False)
        elif sort_by == "Score":
            df_pipe = df_pipe.sort_values("score", ascending=False)
        elif sort_by == "Asking Price":
            df_pipe = df_pipe.sort_values("asking_price")
        df_pipe = df_pipe.reset_index(drop=True)

        _visible_keys = set(df_pipe["_key"].tolist())

        if df_pipe.empty:
            st.info("No deals match the current filters.")
        else:
            pipe_event = st.dataframe(
                df_pipe.drop(columns=["_key", "notes"]),
                column_config={
                    "stage":         st.column_config.TextColumn("Stage",     width="medium"),
                    "title":         st.column_config.TextColumn("Business",  width="large"),
                    "business_type": st.column_config.TextColumn("Industry",  width="small"),
                    "asking_price":  st.column_config.NumberColumn("Asking",   format="$%.0f", width="small"),
                    "cash_flow":     st.column_config.NumberColumn("Cash Flow",format="$%.0f", width="small"),
                    "multiple":      st.column_config.NumberColumn("Multiple", format="%.1fx", width="small"),
                    "est_dscr":      st.column_config.NumberColumn("DSCR",     format="%.2f",  width="small"),
                    "score":         st.column_config.NumberColumn("Score",    format="%d",   width="small"),
                    "location":      st.column_config.TextColumn("Location",  width="small"),
                    "url":           st.column_config.LinkColumn("Listing",   display_text="Open →", width="small"),
                    "date_added":    st.column_config.TextColumn("Added",     width="small"),
                },
                selection_mode="multi-row",
                on_select="rerun",
                hide_index=True,
                use_container_width=True,
                key="pipeline_table",
            )

            # ── Persist card selection across reruns ───────────────────────
            _sel_rows = pipe_event.selection.rows
            # Guard: indices can be stale if df_pipe shrank after a filter/stage change
            _valid_sel = [i for i in _sel_rows if i < len(df_pipe)]
            if _valid_sel:
                _sel_keys = [df_pipe.iloc[i]["_key"] for i in _valid_sel]
                st.session_state["pipe_card_keys"] = _sel_keys
                st.session_state.pop("_pipe_stage_updated", None)
            elif st.session_state.pop("_pipe_stage_updated", False):
                # Rerun triggered by a stage/notes update — keep stored selection
                _stored = st.session_state.get("pipe_card_keys", [])
                st.session_state["pipe_card_keys"] = [k for k in _stored if k in _visible_keys]
            else:
                # Genuine deselection — clear cards
                st.session_state["pipe_card_keys"] = []

            _card_keys = st.session_state.get("pipe_card_keys", [])

            # ── Bulk quick actions ──────────────────────────────────────────
            if _card_keys:
                st.markdown(f"**{len(_card_keys)} selected — Quick Actions:**")
                _qa1, _qa2, _qa3, _qa4, _qa5 = st.columns(5)
                if _qa1.button("🔬 Researching",      key="qa_research"):
                    for _k in _card_keys:
                        pipeline_update(_k, stage="Researching")
                    st.session_state["_pipe_stage_updated"] = True
                    st.rerun()
                if _qa2.button("📧 Generate Outreach", key="qa_outreach_top"):
                    _drafts = st.session_state.get("pipe_outreach_drafts", {})
                    for _k in _card_keys:
                        _pe = pipeline.get(_k, {})
                        if _pe:
                            _lst = _pe.get("listing", {})
                            _broker = fetch_listing_broker(_lst.get("url", ""), _lst)
                            _drafts[_k] = draft_outreach(_lst, _broker)
                    st.session_state["pipe_outreach_drafts"] = _drafts
                    st.session_state["_pipe_stage_updated"] = True
                    st.rerun()
                if _qa3.button("📞 Broker Contacted", key="qa_broker"):
                    for _k in _card_keys:
                        pipeline_update(_k, stage="Broker Contacted")
                    st.session_state["_pipe_stage_updated"] = True
                    st.rerun()
                if _qa4.button("📑 CIM Received",     key="qa_cim"):
                    for _k in _card_keys:
                        pipeline_update(_k, stage="CIM / Financials Received")
                    st.session_state["_pipe_stage_updated"] = True
                    st.rerun()
                if _qa5.button("❌ Pass",              key="qa_pass"):
                    for _k in _card_keys:
                        pipeline_update(_k, stage="Pass")
                    st.session_state["pipe_card_keys"] = []
                    st.rerun()

            # ── Detail cards ────────────────────────────────────────────────
            pipeline = load_pipeline()   # refresh after any bulk action
            for _card_key in _card_keys:
                _card_entry = pipeline.get(_card_key, {})
                if not _card_entry:
                    continue
                _listing = _card_entry.get("listing", {})
                st.divider()

                # Title: type prefix + name + score — no "Look Closer" text
                _ctitle = _listing.get("title", "?")
                _cbtype = _listing.get("business_type", "")
                _cscore = _listing.get("score")
                _cheader = f"[{_cbtype}] {_ctitle}" if _cbtype else _ctitle
                if _cscore is not None:
                    _cheader += f"  —  Score {int(_cscore)}/100"
                st.subheader(_cheader)

                _dc1, _dc2, _dc3, _dc4 = st.columns(4)
                _dc1.metric("Asking",    fmt_k(_listing.get("asking_price")))
                _dc2.metric("Cash Flow", fmt_k(_listing.get("cash_flow")))
                _dc3.metric("Multiple",  f"{_listing['multiple']:.1f}x" if _listing.get("multiple") else "—")
                _dc4.metric("Est. DSCR", f"{_listing['est_dscr']:.2f}x" if _listing.get("est_dscr") else "—")

                st.markdown(
                    f"**Source:** {_listing.get('source','—')}  ·  "
                    f"**Type:** {_listing.get('business_type','—')}  ·  "
                    f"**Location:** {_listing.get('location','—')}"
                )
                # Flags as inline tags
                _flags = _listing.get("flags", "")
                if _flags and _flags != "—":
                    _ftags = "  ".join(f"`{f.strip()}`" for f in _flags.split("|") if f.strip())
                    st.markdown(f"**⚑ Flags:** {_ftags}")
                # Signals as inline tags
                _signals = _listing.get("signals", "")
                if _signals and _signals != "—":
                    _stags = "  ".join(f"`{s.strip()}`" for s in _signals.split("|") if s.strip())
                    st.markdown(f"**✓ Signals:** {_stags}")

                # Quick overview bullets
                _desc = _listing.get("description", "")
                _bullets = _quick_bullets(_desc)
                if _bullets:
                    st.markdown("**Overview:**")
                    for _b in _bullets:
                        st.markdown(f"- {_b}")
                elif _desc:
                    st.markdown(f"<small>{_desc}</small>", unsafe_allow_html=True)

                st.markdown("")
                _bc1, _bc2 = st.columns([1, 2])
                with _bc1:
                    if _listing.get("url"):
                        st.link_button("🔗 Open Listing", _listing["url"])
                with _bc2:
                    _cur_stage = _card_entry.get("stage", "New")
                    _new_stage = st.selectbox(
                        "Stage",
                        PIPELINE_STAGES,
                        index=PIPELINE_STAGES.index(_cur_stage) if _cur_stage in PIPELINE_STAGES else 0,
                        key=f"card_stage_{_card_key}",
                    )
                    if _new_stage != _cur_stage:
                        pipeline_update(_card_key, stage=_new_stage)
                        if _new_stage == "Pass":
                            # Remove from card keys so card closes
                            _stored = st.session_state.get("pipe_card_keys", [])
                            st.session_state["pipe_card_keys"] = [k for k in _stored if k != _card_key]
                        else:
                            st.session_state["_pipe_stage_updated"] = True
                        st.rerun()

                _new_notes = st.text_area(
                    "Notes",
                    value=_card_entry.get("notes", ""),
                    height=90,
                    key=f"card_notes_{_card_key}",
                )
                if st.button("💾 Save Notes", key=f"save_notes_{_card_key}"):
                    pipeline_update(_card_key, notes=_new_notes)
                    st.session_state["_pipe_stage_updated"] = True
                    st.rerun()

                # ── Outreach draft (per-card) ──────────────────────────────
                _pipe_drafts = st.session_state.get("pipe_outreach_drafts", {})
                if _card_key in _pipe_drafts:
                    st.markdown("**📧 Outreach Draft**")
                    st.text_area(
                        "Draft",
                        value=_pipe_drafts[_card_key],
                        height=300,
                        key=f"pipe_draft_ta_{_card_key}",
                        label_visibility="collapsed",
                    )
                    _od1, _od2 = st.columns([1, 1])
                    if _listing.get("url"):
                        _od1.link_button("🌐 Open Contact Form", _listing["url"])
                    if _od2.button("🗑️ Clear Draft", key=f"clear_pipe_draft_{_card_key}"):
                        _pipe_drafts.pop(_card_key, None)
                        st.session_state["pipe_outreach_drafts"] = _pipe_drafts
                        st.session_state["_pipe_stage_updated"] = True
                        st.rerun()
                else:
                    if st.button("📧 Draft Outreach", key=f"per_card_outreach_{_card_key}"):
                        _broker = fetch_listing_broker(_listing.get("url", ""), _listing)
                        _pipe_drafts[_card_key] = draft_outreach(_listing, _broker)
                        st.session_state["pipe_outreach_drafts"] = _pipe_drafts
                        st.session_state["_pipe_stage_updated"] = True
                        st.rerun()

        # ── Lender Reference Panel ────────────────────────────────────────
        st.divider()
        with st.expander("🏦 Preferred SBA Lenders — ETA / Acquisition Financing", expanded=False):
            st.caption("Source: Chapter 12, Searchfunding Textbook. Verify current rates and appetite before engaging.")
            lender_data = [
                {
                    "Lender":      "Live Oak Bank",
                    "Specialty":   "Largest SBA lender by volume. Deep acquisition experience. Goodwill-heavy deals OK. HVAC, Fire, Services.",
                    "Geography":   "National",
                    "Notes":       "First call for most ETA deals under $5M. Ask for their acquisition lending team.",
                    "Website":     "liveoakbank.com",
                },
                {
                    "Lender":      "Celtic Bank",
                    "Specialty":   "Experienced with intangible-heavy / goodwill acquisitions. Services, distribution, field services.",
                    "Geography":   "National",
                    "Notes":       "Good alternative to Live Oak. Competitive on rate.",
                    "Website":     "celticbank.com",
                },
                {
                    "Lender":      "Huntington National Bank",
                    "Specialty":   "Major regional bank. Strong SBA capability. Good for Southeast.",
                    "Geography":   "Southeast / Midwest",
                    "Notes":       "Larger bank feel — better for deals with hard assets.",
                    "Website":     "huntington.com",
                },
                {
                    "Lender":      "Newtek Business Services",
                    "Specialty":   "Non-bank SBA lender. Flexible on structure. Services and specialty industries.",
                    "Geography":   "National",
                    "Notes":       "Good for deals other banks find complex.",
                    "Website":     "newtekbusiness.com",
                },
                {
                    "Lender":      "ReadyCap Commercial",
                    "Specialty":   "Environmental, industrial services, specialty trades. Comfortable with regulated industries.",
                    "Geography":   "National",
                    "Notes":       "Preferred lender for environmental / industrial services deals.",
                    "Website":     "readycap.com",
                },
            ]
            for l in lender_data:
                st.markdown(f"**{l['Lender']}** — {l['Geography']}")
                st.markdown(f"&nbsp;&nbsp;&nbsp;&nbsp;{l['Specialty']}")
                st.caption(f"    {l['Notes']}  |  {l['Website']}")
