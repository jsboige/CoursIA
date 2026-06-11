#!/usr/bin/env python3
"""A/B test: flat-clone vs expressive-clone for prosodie #1877 fix.

Generates ~25s clips using:
  A (AVANT) = v4_narrator_male_neutral (flat reference, ST~5.8)
  B (APRES) = prosody_expr_voicedesign (expressive reference, ST~9.2)

Then runs prosody_metrics.py on both to produce objective measurements.

Usage:
    cd v4/prosody_lab/
    python ab_clone_test.py

Output:
    outputs/prosody_lab/ab_flat.mp3
    outputs/prosody_lab/ab_expressive.mp3
    outputs/prosody_lab/ab_metrics.json
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

# Add parent dirs to path for imports
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from fishaudio_client import fishaudio_tts

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

TEST_TEXT_FILE = Path(__file__).resolve().parent / "test_segment.txt"
OUTPUT_DIR = Path(__file__).resolve().parent.parent / "outputs" / "prosody_lab"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)

FLAT_REF = "v4_narrator_male_neutral"       # ST~5.8 (MODERATE)
EXPR_REF = "prosody_expr_voicedesign"       # ST~9.2 (EXPRESSIVE)

# Temperature 0.8 matches run_matrix.py Stage 2 conditions
TEMPERATURE = 0.8
SEED = 42

OUT_FLAT = OUTPUT_DIR / "ab_flat.mp3"
OUT_EXPR = OUTPUT_DIR / "ab_expressive.mp3"
OUT_METRICS = OUTPUT_DIR / "ab_metrics.json"

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    # Load test text
    text = TEST_TEXT_FILE.read_text(encoding="utf-8").strip()
    # Remove line number prefix if present
    if text and text[0].isdigit():
        lines = text.split("\n")
        # Take the first substantive line (after line number)
        text = "\n".join(
            line.split("\t", 1)[-1] if line.strip() and line.strip()[0].isdigit() else line
            for line in lines
        ).strip()

    print(f"Test text ({len(text)} chars): {text[:80]}...")
    print(f"Flat ref: {FLAT_REF}")
    print(f"Expressive ref: {EXPR_REF}")
    print(f"Temperature: {TEMPERATURE}, Seed: {SEED}")
    print()

    # Generate A (flat)
    print(f"[1/2] Generating FLAT clip (ref={FLAT_REF})...")
    t0 = time.time()
    audio_flat = fishaudio_tts(
        text=text,
        reference_id=FLAT_REF,
        temperature=TEMPERATURE,
        seed=SEED,
        format="mp3",
        timeout=300,
    )
    dt_flat = time.time() - t0
    if audio_flat is None:
        print("ERROR: Flat TTS failed.")
        sys.exit(1)
    OUT_FLAT.write_bytes(audio_flat)
    print(f"  -> {OUT_FLAT.name}: {len(audio_flat)/1024:.0f} KB in {dt_flat:.1f}s")

    # Generate B (expressive)
    print(f"[2/2] Generating EXPRESSIVE clip (ref={EXPR_REF})...")
    t0 = time.time()
    audio_expr = fishaudio_tts(
        text=text,
        reference_id=EXPR_REF,
        temperature=TEMPERATURE,
        seed=SEED,
        format="mp3",
        timeout=300,
    )
    dt_expr = time.time() - t0
    if audio_expr is None:
        print("ERROR: Expressive TTS failed.")
        sys.exit(1)
    OUT_EXPR.write_bytes(audio_expr)
    print(f"  -> {OUT_EXPR.name}: {len(audio_expr)/1024:.0f} KB in {dt_expr:.1f}s")

    print()
    print(f"Done! Files in {OUTPUT_DIR}/")
    print(f"  {OUT_FLAT.name} (AVANT - flat clone)")
    print(f"  {OUT_EXPR.name} (APRES - expressive clone)")
    print()
    print("Run prosody_metrics.py to measure ST/CV:")
    print(f"  cd {Path(__file__).resolve().parent}")
    print(f"  python prosody_metrics.py {OUT_FLAT} {OUT_EXPR} --json {OUT_METRICS}")

if __name__ == "__main__":
    main()
