"""STEP 2v3: Prosody fix test with melody analysis.

Key insight: FishAudio HAS prosody, but it's ALWAYS THE SAME melody.
We need to measure whether different tags/temperatures produce DIFFERENT
melodic contours, not just different average F0.

Metrics:
- F0 contour (trajectory over time)
- Pairwise DTW distance between contours (0 = identical melody)
- Contour shape features: rise/fall patterns, turning points
"""
from __future__ import annotations

import json
import logging
import sys
import time
from pathlib import Path

import numpy as np
import requests

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
logger = logging.getLogger(__name__)

FISH_URL = "http://localhost:8197"
OUT_DIR = Path(__file__).resolve().parent / "outputs" / "prosody_fix_test_v3"
OUT_DIR.mkdir(exist_ok=True, parents=True)

NARRATEUR = "narrateur"

# ── TEST PAIRS: exact pipeline output vs proposed fix ──
TEST_PAIRS = [
    {
        "desc": "firmly -> emphasis vs angry",
        "old_text": "[emphasis] BOULE DE SUIF",
        "old_temp": 0.7,
        "new_text": "[angry] BOULE DE SUIF",
        "new_temp": 0.8,
    },
    {
        "desc": "mockingly -> emphasis vs angry",
        "old_text": "[emphasis] Pendant plusieurs jours de suite des lambeaux d'armee en deroute avaient traverse la ville.",
        "old_temp": 0.7,
        "new_text": "[angry] Pendant plusieurs jours de suite des lambeaux d'armee en deroute avaient traverse la ville.",
        "new_temp": 0.8,
    },
    {
        "desc": "cold_tone -> low_voice vs angry",
        "old_text": "[low voice] Les Prussiens allaient entrer dans Rouen, disait-on.",
        "old_temp": 0.7,
        "new_text": "[angry] Les Prussiens allaient entrer dans Rouen, disait-on.",
        "new_temp": 0.7,
    },
    {
        "desc": "sadly_same_tag diff temp",
        "old_text": "[sad] Les derniers soldats francais venaient enfin de traverser la Seine.",
        "old_temp": 0.7,
        "new_text": "[sad] Les derniers soldats francais venaient enfin de traverser la Seine.",
        "new_temp": 0.5,
    },
    {
        "desc": "slowly -> pause vs sad",
        "old_text": "[pause] Puis un calme profond, une attente epouvantee avait plane sur la cite.",
        "old_temp": 0.7,
        "new_text": "[sad] Puis un calme profond, une attente epouvantee avait plane sur la cite.",
        "new_temp": 0.5,
    },
    {
        "desc": "firmly2 -> emphasis vs angry",
        "old_text": "[emphasis] L'angoisse de l'attente faisait desirer la venue de l'ennemi.",
        "old_temp": 0.7,
        "new_text": "[angry] L'angoisse de l'attente faisait desirer la venue de l'ennemi.",
        "new_temp": 0.8,
    },
]


def tts(text: str, reference_id: str = NARRATEUR,
        temperature: float = 0.7) -> bytes | None:
    payload = {
        "text": text,
        "reference_id": reference_id,
        "seed": 42,
        "temperature": temperature,
        "top_p": 0.9,
        "format": "mp3",
    }
    try:
        resp = requests.post(f"{FISH_URL}/v1/tts", json=payload, timeout=300)
        resp.raise_for_status()
        return resp.content
    except requests.RequestException as exc:
        logger.error("TTS error: %s", exc)
        return None


def extract_f0_contour(mp3_bytes: bytes) -> np.ndarray:
    """Extract normalized F0 contour from MP3 bytes."""
    import librosa
    import io
    y, sr = librosa.load(io.BytesIO(mp3_bytes), sr=None)
    f0 = librosa.yin(y, fmin=50, fmax=400, sr=sr)
    # Normalize: resample to 100 points, interpolate unvoiced
    f0_norm = np.interp(
        np.linspace(0, len(f0), 100),
        np.arange(len(f0)),
        f0
    )
    return f0_norm


def contour_distance(c1: np.ndarray, c2: np.ndarray) -> float:
    """Compute DTW-like distance between two F0 contours.

    Uses simple Euclidean on normalized contours (same length).
    Lower = more similar melody.
    """
    # Both already 100 points from extract_f0_contour
    # Z-score normalize each contour to focus on SHAPE not absolute pitch
    c1_z = (c1 - np.mean(c1)) / (np.std(c1) + 1e-6)
    c2_z = (c2 - np.mean(c2)) / (np.std(c2) + 1e-6)
    return float(np.mean((c1_z - c2_z) ** 2) ** 0.5)


def analyze_contour(mp3_bytes: bytes) -> dict:
    """Full contour analysis."""
    import librosa
    import io
    y, sr = librosa.load(io.BytesIO(mp3_bytes), sr=None)
    f0 = librosa.yin(y, fmin=50, fmax=400, sr=sr)
    f0_valid = f0[f0 > 0]
    rms = librosa.feature.rms(y=y)[0]

    # Contour shape features
    f0_norm = np.interp(np.linspace(0, len(f0), 100), np.arange(len(f0)), f0)
    f0_diff = np.diff(f0_norm)

    # Count direction changes (melodic turning points)
    signs = np.sign(f0_diff)
    sign_changes = np.sum(np.diff(signs) != 0)

    return {
        "duration_s": round(len(y) / sr, 2),
        "f0_mean_hz": round(float(np.mean(f0_valid)), 2) if len(f0_valid) > 0 else 0,
        "f0_std_hz": round(float(np.std(f0_valid)), 2) if len(f0_valid) > 0 else 0,
        "f0_range_hz": round(float(np.ptp(f0_valid)), 2) if len(f0_valid) > 0 else 0,
        "turning_points": int(sign_changes),
        "rms_mean": round(float(np.mean(rms)), 6),
        "rms_std": round(float(np.std(rms)), 6),
    }


def main():
    logger.info("Waiting for FishAudio server...")
    for attempt in range(20):
        try:
            r = requests.get(f"{FISH_URL}/", timeout=5)
            if r.status_code in (200, 404):
                logger.info("Server ready.")
                break
        except Exception:
            pass
        time.sleep(5)
    else:
        logger.error("Server not ready.")
        sys.exit(1)

    # Generate all segments
    audio_data = {}  # name -> mp3_bytes
    analyses = {}    # name -> analysis dict
    contours = {}    # name -> f0_contour (100-point ndarray)

    for i, pair in enumerate(TEST_PAIRS):
        desc = pair["desc"]
        safe = desc.replace(" ", "_").replace("->", "to").replace("+", "p").replace(",", "").replace("=", "")

        # OLD
        old_name = f"{i:02d}_{safe}_OLD"
        logger.info("[%d/%d] OLD: %s (temp=%.1f)", i*2+1, len(TEST_PAIRS)*2, desc, pair["old_temp"])
        old_audio = tts(pair["old_text"], temperature=pair["old_temp"])
        if old_audio:
            (OUT_DIR / f"{old_name}.mp3").write_bytes(old_audio)
            audio_data[old_name] = old_audio
            analyses[old_name] = analyze_contour(old_audio)
            contours[old_name] = extract_f0_contour(old_audio)
            analyses[old_name].update({"desc": desc, "mode": "OLD", "temp": pair["old_temp"]})
            a = analyses[old_name]
            logger.info("  F0=%.1f+-%.1fHz, range=%.1fHz, turns=%d, dur=%.1fs",
                       a["f0_mean_hz"], a["f0_std_hz"], a["f0_range_hz"],
                       a["turning_points"], a["duration_s"])
        else:
            logger.error("  FAILED")

        # NEW
        new_name = f"{i:02d}_{safe}_NEW"
        logger.info("[%d/%d] NEW: %s (temp=%.1f)", i*2+2, len(TEST_PAIRS)*2, desc, pair["new_temp"])
        new_audio = tts(pair["new_text"], temperature=pair["new_temp"])
        if new_audio:
            (OUT_DIR / f"{new_name}.mp3").write_bytes(new_audio)
            audio_data[new_name] = new_audio
            analyses[new_name] = analyze_contour(new_audio)
            contours[new_name] = extract_f0_contour(new_audio)
            analyses[new_name].update({"desc": desc, "mode": "NEW", "temp": pair["new_temp"]})
            a = analyses[new_name]
            logger.info("  F0=%.1f+-%.1fHz, range=%.1fHz, turns=%d, dur=%.1fs",
                       a["f0_mean_hz"], a["f0_std_hz"], a["f0_range_hz"],
                       a["turning_points"], a["duration_s"])
        else:
            logger.error("  FAILED")

    # ── MELODY SIMILARITY ANALYSIS ──
    logger.info("\n" + "=" * 80)
    logger.info("MELODY SIMILARITY (z-score DTW distance, lower = more similar)")
    logger.info("=" * 80)

    # 1. Within-pair OLD vs NEW
    for i, pair in enumerate(TEST_PAIRS):
        desc = pair["desc"]
        old_name = f"{i:02d}_{desc}_OLD"
        new_name = f"{i:02d}_{desc}_NEW"
        if old_name in contours and new_name in contours:
            dist = contour_distance(contours[old_name], contours[new_name])
            logger.info("  %s: OLD<->NEW dist = %.3f", desc, dist)
        else:
            logger.info("  %s: MISSING DATA", desc)

    # 2. Cross-pair: all OLD segments vs each other (should be SIMILAR = same melody)
    logger.info("\nCross-pair OLD vs OLD (expecting LOW = same melody):")
    old_names = [f"{i:02d}_{TEST_PAIRS[i]['desc'].replace(' ', '_').replace('->', 'to').replace('+', 'p').replace(',', '').replace('=', '')}_OLD" for i in range(len(TEST_PAIRS))]
    old_dists = []
    for j in range(len(old_names)):
        for k in range(j+1, len(old_names)):
            if old_names[j] in contours and old_names[k] in contours:
                d = contour_distance(contours[old_names[j]], contours[old_names[k]])
                old_dists.append(d)
                logger.info("  %s <-> %s: %.3f",
                           TEST_PAIRS[j]["desc"][:15], TEST_PAIRS[k]["desc"][:15], d)
    if old_dists:
        logger.info("  OLD avg cross-dist: %.3f (std: %.3f)", np.mean(old_dists), np.std(old_dists))

    # 3. Cross-pair: all NEW segments vs each other
    logger.info("\nCross-pair NEW vs NEW (expecting HIGHER = different melodies):")
    new_names = [f"{i:02d}_{TEST_PAIRS[i]['desc'].replace(' ', '_').replace('->', 'to').replace('+', 'p').replace(',', '').replace('=', '')}_NEW" for i in range(len(TEST_PAIRS))]
    new_dists = []
    for j in range(len(new_names)):
        for k in range(j+1, len(new_names)):
            if new_names[j] in contours and new_names[k] in contours:
                d = contour_distance(contours[new_names[j]], contours[new_names[k]])
                new_dists.append(d)
                logger.info("  %s <-> %s: %.3f",
                           TEST_PAIRS[j]["desc"][:15], TEST_PAIRS[k]["desc"][:15], d)
    if new_dists:
        logger.info("  NEW avg cross-dist: %.3f (std: %.3f)", np.mean(new_dists), np.std(new_dists))

    # Summary
    logger.info("\n" + "=" * 80)
    logger.info("SUMMARY")
    if old_dists and new_dists:
        ratio = np.mean(new_dists) / np.mean(old_dists) if np.mean(old_dists) > 0 else 0
        logger.info("OLD melody diversity: %.3f", np.mean(old_dists))
        logger.info("NEW melody diversity: %.3f", np.mean(new_dists))
        logger.info("Diversity ratio (NEW/OLD): %.2fx", ratio)
        if ratio > 1.3:
            logger.info("VERDICT: NEW produces MORE DIVERSE melodies. Fix works.")
        elif ratio > 1.1:
            logger.info("VERDICT: NEW produces SLIGHTLY more diverse melodies. Marginal.")
        else:
            logger.info("VERDICT: No meaningful melody difference. Fix insufficient.")
    logger.info("MP3 files in: %s", OUT_DIR)


if __name__ == "__main__":
    main()
