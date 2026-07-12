#!/usr/bin/env python3
"""Long-segment prosody drift test — #1877.

Generates a 30s+ audio clip with the SAME voice (same reference_id) and
measures prosody metrics in sliding windows to detect drift over time.

If prosody is stable: ST/CV/velocity should be roughly constant across windows.
If prosody drifts toward monotone: ST/CV/velocity should decrease in later windows.

Also generates at 3 temperature levels (0.3, 0.7, 1.2) to see if temperature
affects drift behaviour.

Usage:
    cd v4/prosody_lab/
    python long_segment_drift_test.py

Output:
    outputs/prosody_lab/drift_<temp>.mp3
    outputs/prosody_lab/drift_metrics.json
    outputs/prosody_lab/drift_contours.png
    outputs/prosody_lab/drift_window_metrics.json   (per-window breakdown)
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np

from fishaudio_client import fishaudio_tts

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

OUTPUT_DIR = Path(__file__).resolve().parent.parent / "outputs" / "prosody_lab"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)

# Long paragraph from Boule de Suif — should yield 30s+ of audio
# This is the full passage from Act 1, segment 7 (opening of the meal scene)
LONG_TEXT = (
    "Enfin, a trois heures, comme on se trouvait au milieu d'une plaine "
    "interminable, Boule de Suif retira de sous la banquette un large panier "
    "couvert d'une serviette blanche. Elle en tira d'abord un petit plat "
    "de porcelet froid, puis une belle piece de pate de lievre, un beau "
    "fromage de cochon, une forte provision de fruits confits, un pain "
    "de savoie, quatre gouters complets, un saucisson, des petits gateaux "
    "et une bouteille de vin. La Cornudet regardait ce depot de vivres "
    "avec un oeil brillant et satisfait. Quant aux autres, le desappointement "
    "se peignait sur leurs visages. On s'offensait de cette munificence "
    "etouffee. La comtesse surtout semblait contrariee."
)

REFERENCE_ID = "v4_narrator_male_neutral"  # Same voice throughout
SEED = 42
TEMPERATURES = [0.1, 0.5, 1.0]

# Drift analysis: split audio into N windows
N_WINDOWS = 4  # Quarter-window analysis

OUT_METRICS = OUTPUT_DIR / "drift_metrics.json"
OUT_WINDOW_METRICS = OUTPUT_DIR / "drift_window_metrics.json"
OUT_PLOT = OUTPUT_DIR / "drift_contours.png"


# ---------------------------------------------------------------------------
# Audio generation
# ---------------------------------------------------------------------------

def generate_long_clip(temp: float) -> bytes:
    """Generate the long text at given temperature."""
    print(f"  Generating at temperature={temp} ...")
    t0 = time.time()
    audio = fishaudio_tts(
        text=LONG_TEXT,
        reference_id=REFERENCE_ID,
        temperature=temp,
        seed=SEED,
        format="mp3",
        timeout=600,
    )
    dt = time.time() - t0
    if audio is None:
        print(f"  ERROR: Generation failed at temp={temp}")
        sys.exit(1)
    print(f"  -> {len(audio)/1024:.0f} KB in {dt:.1f}s")
    return audio


# ---------------------------------------------------------------------------
# Windowed prosody analysis
# ---------------------------------------------------------------------------

def windowed_metrics(audio_path: str | Path, n_windows: int = N_WINDOWS) -> list[dict]:
    """Compute prosody metrics for each window of the audio file."""
    from prosody_metrics import load_audio, extract_f0, DEFAULT_SR, DEFAULT_FMIN, DEFAULT_FMAX
    import math

    y, sr = load_audio(audio_path, sr=DEFAULT_SR)
    duration = len(y) / sr
    window_len = len(y) // n_windows

    results = []
    for i in range(n_windows):
        start = i * window_len
        end = start + window_len if i < n_windows - 1 else len(y)
        y_win = y[start:end]
        win_duration = len(y_win) / sr

        # Extract F0 for this window
        contour = extract_f0(y_win, sr, fmin=DEFAULT_FMIN, fmax=DEFAULT_FMAX)
        f0v = contour["f0_voiced"]

        if f0v.size < 5:
            results.append({
                "window": i + 1,
                "time_start_s": round(start / sr, 2),
                "time_end_s": round(end / sr, 2),
                "duration_s": round(win_duration, 2),
                "verdict": "NO_VOICED_SIGNAL",
            })
            continue

        p5 = float(np.percentile(f0v, 5))
        p95 = float(np.percentile(f0v, 95))
        semitone_range = 12.0 * math.log2(p95 / p5) if p5 > 0 else 0.0
        f0_mean = float(np.mean(f0v))
        f0_std = float(np.std(f0v))
        cv = f0_std / f0_mean if f0_mean > 0 else 0.0

        # Intonation velocity
        f0_full = contour["f0"]
        voiced = contour["voiced"]
        times = contour["times"]
        median = float(np.median(f0v))
        st_full = 12.0 * np.log2(f0_full / median)
        st_full = np.where(np.isfinite(st_full), st_full, 0.0)
        both_voiced = voiced[:-1] & voiced[1:]
        if both_voiced.any():
            dst = np.abs(np.diff(st_full))[both_voiced]
            dt = np.diff(times)[both_voiced]
            velocity = float(np.sum(dst) / np.sum(dt)) if np.sum(dt) > 0 else 0.0
        else:
            velocity = 0.0

        if semitone_range < 4.0:
            verdict = "FLAT"
        elif semitone_range < 8.0:
            verdict = "MODERATE"
        else:
            verdict = "EXPRESSIVE"

        results.append({
            "window": i + 1,
            "time_start_s": round(start / sr, 2),
            "time_end_s": round(end / sr, 2),
            "duration_s": round(win_duration, 2),
            "f0_median_hz": round(float(np.median(f0v)), 2),
            "f0_semitone_range": round(semitone_range, 2),
            "f0_cv": round(cv, 4),
            "intonation_velocity_st_s": round(velocity, 3),
            "verdict": verdict,
        })

    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 60)
    print("LONG SEGMENT DRIFT TEST — #1877 prosody fix")
    print(f"Reference: {REFERENCE_ID}")
    print(f"Text: {len(LONG_TEXT)} chars (expected 30s+)")
    print(f"Temperatures: {TEMPERATURES}")
    print(f"Windows per clip: {N_WINDOWS}")
    print("=" * 60)

    all_metrics = {}
    all_window_metrics = {}

    for temp in TEMPERATURES:
        label = f"temp_{temp}"
        out_path = OUTPUT_DIR / f"drift_{temp}.mp3"

        print(f"\n--- Temperature {temp} ---")
        audio = generate_long_clip(temp)
        out_path.write_bytes(audio)

        # Full-clip metrics
        from prosody_metrics import compute_metrics
        metrics = compute_metrics(str(out_path))
        all_metrics[label] = metrics
        print(f"  Full clip: ST={metrics['f0_semitone_range']:.2f}, "
              f"CV={metrics['f0_cv']:.4f}, velocity={metrics['intonation_velocity_st_s']:.2f}, "
              f"verdict={metrics['verdict']}")

        # Windowed metrics
        windows = windowed_metrics(str(out_path), N_WINDOWS)
        all_window_metrics[label] = windows
        print(f"  Window breakdown:")
        for w in windows:
            print(f"    W{w['window']} ({w.get('time_start_s',0):.1f}s-"
                  f"{w.get('time_end_s',0):.1f}s): "
                  f"ST={w.get('f0_semitone_range',0):.2f}, "
                  f"CV={w.get('f0_cv',0):.4f}, "
                  f"vel={w.get('intonation_velocity_st_s',0):.2f}, "
                  f"verdict={w.get('verdict','N/A')}")

    # Save results
    OUT_METRICS.parent.mkdir(parents=True, exist_ok=True)
    with open(OUT_METRICS, "w", encoding="utf-8") as f:
        json.dump(all_metrics, f, indent=2, ensure_ascii=False)
    with open(OUT_WINDOW_METRICS, "w", encoding="utf-8") as f:
        json.dump(all_window_metrics, f, indent=2, ensure_ascii=False)

    # Detect drift: check if ST decreases across windows
    print("\n" + "=" * 60)
    print("DRIFT ANALYSIS")
    print("=" * 60)
    for label, windows in all_window_metrics.items():
        sts = [w.get("f0_semitone_range", 0) for w in windows]
        if len(sts) >= 2:
            delta_st = sts[-1] - sts[0]
            drift_pct = (delta_st / sts[0] * 100) if sts[0] > 0 else 0
            direction = "DRIFT DOWN (monotone)" if delta_st < -1.5 else \
                        "DRIFT UP" if delta_st > 1.5 else "STABLE"
            print(f"  {label}: W1→W{len(sts)} ST = {sts[0]:.2f} → {sts[-1]:.2f} "
                  f"(delta={delta_st:+.2f}, {drift_pct:+.1f}%) → {direction}")
        else:
            print(f"  {label}: insufficient windows")

    print(f"\nResults saved to:")
    print(f"  {OUT_METRICS}")
    print(f"  {OUT_WINDOW_METRICS}")

    # Generate contour plot
    from prosody_metrics import plot_contours
    labelled = {f"temp_{t}": str(OUTPUT_DIR / f"drift_{t}.mp3") for t in TEMPERATURES}
    plot_contours(labelled, OUT_PLOT, title="Long segment drift test — same voice, different temperatures")
    print(f"  {OUT_PLOT}")


if __name__ == "__main__":
    main()
