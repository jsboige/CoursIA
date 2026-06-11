#!/usr/bin/env python3
"""A/B dialogue test: flat-clone vs expressive-clone for prosodie #1877 fix.

Tests a DIALOGUE voice (not narrator) to validate the expressive reference fix.
Uses Cornudet's lines from Boule de Suif — emotionally charged, good for prosody test.

  A (AVANT) = v4_cornudet_mocking (current flat-clone reference)
  B (APRES) = prosody_expr_voicedesign (expressive reference)

Usage:
    cd v4/prosody_lab/
    python ab_dialogue_test.py

Output:
    outputs/prosody_lab/ab_dialogue_flat.mp3
    outputs/prosody_lab/ab_dialogue_expr.mp3
    outputs/prosody_lab/ab_dialogue_metrics.json
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from fishaudio_client import fishaudio_tts

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

OUTPUT_DIR = Path(__file__).resolve().parent.parent / "outputs" / "prosody_lab"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)

# Cornudet's longest dialogue line — mocking, emotionally charged
DIALOGUE_TEXT = (
    "--La guerre est une barbarie quand on attaque un voisin paisible; "
    "c'est un devoir sacré quand on défend la patrie. "
    "Bravo, citoyenne! dit-il. "
    "Voyons, vous êtes bête, qu'est-ce que ça vous fait?"
)

# Also test Elisabeth Rousset's fiery refusal (most emotional dialogue in the book)
DIALOGUE_TEXT_ROUSSET = (
    "Vous lui direz à cette crapule, à ce saligaud, à cette Charogne de Prussien, "
    "que jamais je ne voudrai; vous entendez bien, jamais, jamais, jamais."
)

FLAT_REF = "v4_cornudet_mocking"              # Current flat-clone
EXPR_REF = "prosody_expr_voicedesign"          # Expressive reference

TEMPERATURE = 0.8
SEED = 42

OUT_FLAT = OUTPUT_DIR / "ab_dialogue_flat.mp3"
OUT_EXPR = OUTPUT_DIR / "ab_dialogue_expr.mp3"
OUT_METRICS = OUTPUT_DIR / "ab_dialogue_metrics.json"


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    text = DIALOGUE_TEXT
    print(f"Dialogue A/B test — Cornudet voice (#1877)")
    print(f"Text ({len(text)} chars): {text[:80]}...")
    print(f"Flat ref: {FLAT_REF}")
    print(f"Expressive ref: {EXPR_REF}")
    print(f"Temperature: {TEMPERATURE}, Seed: {SEED}")
    print()

    # Generate A (flat clone)
    print(f"[1/2] Generating FLAT dialogue (ref={FLAT_REF})...")
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
        print("ERROR: Flat dialogue TTS failed.")
        sys.exit(1)
    OUT_FLAT.write_bytes(audio_flat)
    print(f"  -> {OUT_FLAT.name}: {len(audio_flat)/1024:.0f} KB in {dt_flat:.1f}s")

    # Generate B (expressive reference)
    print(f"[2/2] Generating EXPRESSIVE dialogue (ref={EXPR_REF})...")
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
        print("ERROR: Expressive dialogue TTS failed.")
        sys.exit(1)
    OUT_EXPR.write_bytes(audio_expr)
    print(f"  -> {OUT_EXPR.name}: {len(audio_expr)/1024:.0f} KB in {dt_expr:.1f}s")

    print()
    print(f"Done! Files in {OUTPUT_DIR}/")
    print(f"  {OUT_FLAT.name} (AVANT - flat Cornudet clone)")
    print(f"  {OUT_EXPR.name} (APRES - expressive reference)")
    print()
    print("Run prosody_metrics.py to measure ST/CV:")
    print(f"  cd {Path(__file__).resolve().parent}")
    print(f"  python prosody_metrics.py flat={OUT_FLAT} expr={OUT_EXPR} --json {OUT_METRICS} --plot {OUTPUT_DIR / 'ab_dialogue_contours.png'}")


if __name__ == "__main__":
    main()
