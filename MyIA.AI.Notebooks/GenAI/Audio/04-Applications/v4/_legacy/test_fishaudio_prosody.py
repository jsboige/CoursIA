"""STEP 1: FishAudio S2-Pro prosody unit tests.

Systematic exploration of ALL levers that could affect pitch/prosody:
- normalize parameter (true vs false)
- temperature variation (0.3 → 1.1)
- top_p variation (0.5 → 0.95)
- Bracket tags [angry] [sad] [excited] [whispering] (S2 syntax)
- Natural language tags [speaking softly with sadness] (S2 NL)
- Parenthesis tags (angry) (sad) (S1 syntax, should NOT work on S2)
- SSML-like tags <break time="1s"/>
- Punctuation effects (ALL CAPS, ellipsis, exclamation)
- Multiple reference voices
- No reference (default voice)

Output: MP3 files + spectral analysis (F0 mean, F0 std, RMS mean, RMS std, duration)
"""
from __future__ import annotations

import json
import logging
import sys
import time
from pathlib import Path

import requests

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
logger = logging.getLogger(__name__)

FISH_URL = "http://localhost:8197"
OUT_DIR = Path(__file__).resolve().parent / "outputs" / "prosody_unit_tests"
OUT_DIR.mkdir(exist_ok=True, parents=True)

TEST_TEXT = "Le premier pas seul coutait. Une fois le Rubicon passe, il fallait aller jusqu au bout."
REFERENCE_ID = "narrateur"  # main narrator reference

# ---------------------------------------------------------------------------
# TTS call
# ---------------------------------------------------------------------------

def tts(text: str, reference_id: str = REFERENCE_ID, **kwargs) -> bytes | None:
    payload = {
        "text": text,
        "reference_id": reference_id,
        "seed": kwargs.pop("seed", 42),
        "temperature": kwargs.pop("temperature", 0.7),
        "top_p": kwargs.pop("top_p", 0.9),
        "format": "mp3",
    }
    if "normalize" in kwargs:
        payload["normalize"] = kwargs["normalize"]
    # Pass any extra kwargs
    payload.update(kwargs)

    try:
        resp = requests.post(f"{FISH_URL}/v1/tts", json=payload, timeout=300)
        resp.raise_for_status()
        return resp.content
    except requests.RequestException as exc:
        logger.error("TTS error: %s", exc)
        return None


def save_and_measure(name: str, audio: bytes | None) -> dict:
    """Save audio and return basic stats."""
    if audio is None:
        return {"name": name, "status": "FAILED", "bytes": 0}

    path = OUT_DIR / f"{name}.mp3"
    path.write_bytes(audio)
    duration = len(audio) * 8 / 192_000  # estimate at 192kbps
    return {"name": name, "status": "OK", "bytes": len(audio), "duration_est": round(duration, 2)}


# ---------------------------------------------------------------------------
# Test definitions
# ---------------------------------------------------------------------------

TESTS = []

# Group 1: normalize parameter
TESTS.append({
    "name": "01_baseline_default",
    "text": TEST_TEXT,
    "reference_id": REFERENCE_ID,
})
TESTS.append({
    "name": "02_normalize_false",
    "text": TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "03_normalize_true",
    "text": TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "normalize": True,
})

# Group 2: temperature variation
for temp in [0.3, 0.5, 0.9, 1.1]:
    TESTS.append({
        "name": f"04_temp_{temp}",
        "text": TEST_TEXT,
        "reference_id": REFERENCE_ID,
        "temperature": temp,
        "normalize": False,
    })

# Group 3: top_p variation
for top_p in [0.5, 0.7, 0.95]:
    TESTS.append({
        "name": f"05_topp_{top_p}",
        "text": TEST_TEXT,
        "reference_id": REFERENCE_ID,
        "top_p": top_p,
        "normalize": False,
    })

# Group 4: S2 bracket tags (single)
for tag in ["[angry]", "[sad]", "[excited]", "[whispering]", "[cold]", "[pause]"]:
    TESTS.append({
        "name": f"06_tag_{tag.strip('[]')}",
        "text": f"{tag} {TEST_TEXT}",
        "reference_id": REFERENCE_ID,
        "normalize": False,
    })

# Group 5: S2 natural language tags
TESTS.append({
    "name": "07_nl_whispering_softly_sad",
    "text": "[whispering softly with deep sadness] " + TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "07_nl_excited_rapid",
    "text": "[excited, speaking rapidly with enthusiasm] " + TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "07_nl_cold_detached",
    "text": "[cold, detached, speaking without any emotion] " + TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "07_nl_shouting_furious",
    "text": "[shouting furiously, voice trembling with rage] " + TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "07_nl_gentle_tender",
    "text": "[speaking gently, with tenderness and warmth] " + TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "normalize": False,
})

# Group 6: S1 parenthesis syntax (should NOT work on S2)
TESTS.append({
    "name": "08_s1_paren_angry",
    "text": f"(angry) {TEST_TEXT}",
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "08_s1_paren_sad",
    "text": f"(sad) {TEST_TEXT}",
    "reference_id": REFERENCE_ID,
    "normalize": False,
})

# Group 7: Paralanguage (S2 docs say parenthesis for effects)
TESTS.append({
    "name": "09_para_break",
    "text": f"Le premier pas (break) seul coutait. (break) Une fois le Rubicon passe, (break) il fallait aller jusqu au bout.",
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "09_para_laughsigh",
    "text": f"(laugh) Le premier pas seul coutait. (sigh) Une fois le Rubicon passe, il fallait aller jusqu au bout.",
    "reference_id": REFERENCE_ID,
    "normalize": False,
})

# Group 8: Punctuation / formatting effects
TESTS.append({
    "name": "10_allcaps",
    "text": "LE PREMIER PAS SEUL COUTAIT. UNE FOIS LE RUBICON PASSE, IL FALLAIT ALLER JUSQU AU BOUT.",
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "10_ellipsis",
    "text": "Le premier pas... seul coutait. Une fois le Rubicon passe... il fallait aller jusqu au bout...",
    "reference_id": REFERENCE_ID,
    "normalize": False,
})
TESTS.append({
    "name": "10_exclamation",
    "text": "Le premier pas seul coutait! Une fois le Rubicon passe, il fallait aller jusqu au bout!",
    "reference_id": REFERENCE_ID,
    "normalize": False,
})

# Group 9: No reference voice (default)
TESTS.append({
    "name": "11_no_reference",
    "text": TEST_TEXT,
    "normalize": False,
})

# Group 10: Combined NL tags + temperature high
TESTS.append({
    "name": "12_nl_angry_temp11",
    "text": "[angry, voice trembling with rage] " + TEST_TEXT,
    "reference_id": REFERENCE_ID,
    "temperature": 1.1,
    "normalize": False,
})


# ---------------------------------------------------------------------------
# Main execution
# ---------------------------------------------------------------------------

def main():
    # Wait for server
    logger.info("Waiting for FishAudio server...")
    for attempt in range(30):
        try:
            r = requests.get(f"{FISH_URL}/v1/references/list", timeout=5)
            if r.status_code == 200:
                refs = r.json()
                logger.info("Server ready. %d references loaded.", len(refs))
                for ref in refs:
                    logger.info("  Ref: %s", ref.get("id", ref.get("name", "?")))
                break
        except Exception:
            pass
        time.sleep(10)
    else:
        logger.error("Server not ready after 5 minutes. Aborting.")
        sys.exit(1)

    results = []
    for i, test in enumerate(TESTS):
        name = test.pop("name")
        logger.info("[%d/%d] %s", i + 1, len(TESTS), name)
        audio = tts(**test)
        result = save_and_measure(name, audio)
        results.append(result)
        logger.info("  -> %s (%d bytes)", result["status"], result.get("bytes", 0))

    # Save results
    results_path = OUT_DIR / "prosody_test_results.json"
    with open(results_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    logger.info("All %d tests complete. Results in %s", len(TESTS), results_path)

    # Summary
    ok = sum(1 for r in results if r["status"] == "OK")
    failed = len(results) - ok
    logger.info("OK: %d, FAILED: %d", ok, failed)

    # Now run spectral analysis
    logger.info("Running spectral analysis...")
    analyze_all()


def analyze_all():
    """Run F0 + RMS analysis on all generated MP3s."""
    try:
        import numpy as np
        import librosa
    except ImportError:
        logger.error("librosa/numpy not installed. pip install librosa")
        return

    results = []
    mp3_files = sorted(OUT_DIR.glob("*.mp3"))

    for mp3_path in mp3_files:
        try:
            y, sr = librosa.load(str(mp3_path), sr=None)
            # F0 via YIN
            f0 = librosa.yin(y, fmin=50, fmax=400, sr=sr)
            f0_valid = f0[f0 > 0]
            # RMS energy
            rms = librosa.feature.rms(y=y)[0]

            result = {
                "file": mp3_path.name,
                "duration_s": round(len(y) / sr, 2),
                "f0_mean_hz": round(float(np.mean(f0_valid)), 2) if len(f0_valid) > 0 else 0,
                "f0_std_hz": round(float(np.std(f0_valid)), 2) if len(f0_valid) > 0 else 0,
                "f0_min_hz": round(float(np.min(f0_valid)), 2) if len(f0_valid) > 0 else 0,
                "f0_max_hz": round(float(np.max(f0_valid)), 2) if len(f0_valid) > 0 else 0,
                "f0_cv": round(float(np.std(f0_valid) / np.mean(f0_valid)), 4) if len(f0_valid) > 0 and np.mean(f0_valid) > 0 else 0,
                "rms_mean": round(float(np.mean(rms)), 6),
                "rms_std": round(float(np.std(rms)), 6),
            }
            results.append(result)
            logger.info(
                "  %s: F0=%.1f±%.1f Hz (CV=%.3f), RMS=%.4f±%.4f, dur=%.1fs",
                mp3_path.name, result["f0_mean_hz"], result["f0_std_hz"],
                result["f0_cv"], result["rms_mean"], result["rms_std"],
                result["duration_s"],
            )
        except Exception as exc:
            logger.error("Error analyzing %s: %s", mp3_path.name, exc)

    # Save spectral results
    spec_path = OUT_DIR / "prosody_spectral_analysis.json"
    with open(spec_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    # Print comparison table
    if results:
        logger.info("\n" + "=" * 100)
        logger.info("%-30s %8s %8s %8s %8s %8s %10s",
                     "Test", "F0_mean", "F0_std", "F0_min", "F0_max", "F0_CV", "RMS_std")
        logger.info("-" * 100)
        for r in results:
            logger.info("%-30s %7.1fHz %7.1fHz %7.1fHz %7.1fHz %7.4f %10.6f",
                         r["file"][:30], r["f0_mean_hz"], r["f0_std_hz"],
                         r["f0_min_hz"], r["f0_max_hz"], r["f0_cv"], r["rms_std"])

        # Quick verdict
        f0_means = [r["f0_mean_hz"] for r in results if r["f0_mean_hz"] > 0]
        f0_range = max(f0_means) - min(f0_means) if f0_means else 0
        logger.info("\nF0 mean range across ALL tests: %.1f Hz", f0_range)
        if f0_range < 10:
            logger.info("VERDICT: FISHAUDIO CANNOT PRODUCE MEANINGFUL F0 VARIATION. Fallback to Qwen required.")
        elif f0_range < 20:
            logger.info("VERDICT: FISHAUDIO PRODUCES MINIMAL F0 VARIATION. May need workaround (multi-voice).")
        else:
            logger.info("VERDICT: FISHAUDIO CAN PRODUCE F0 VARIATION. Identify best parameters and apply to pipeline.")


if __name__ == "__main__":
    main()
