"""Focused prosody iteration test for FishAudio S2-Pro.

Goal: find what actually produces audible prosody variation
WITH the narrator's cloned voice, so we can compare apples to apples.

Usage:
    cd v4 && python test_prosody_iteration.py
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

_parent = str(Path(__file__).resolve().parent)
sys.path.insert(0, _parent)

from fishaudio_client import (
    fishaudio_tts,
    OUTPUT_DIR,
)

# Narrator cloned voice — THE reference for all comparisons
REF = "v4_narrator_male_neutral"

# Short dramatic narration (typical pipeline segment length)
TEXT = (
    "Personne n'osait parler. Le silence etait devenu pesant, "
    "presque insupportable. Boule de Suif, immobile, regardait "
    "fixement par la fenetre de la diligence."
)

OUT = OUTPUT_DIR / "prosody_iter"
OUT.mkdir(exist_ok=True)

SEED = 42  # Fixed seed for reproducibility


def synth(name: str, text: str, **kwargs) -> str:
    """Synthesize with narrator voice. Returns output path."""
    print(f"  {name:40s}", end="", flush=True)
    t0 = time.time()
    audio = fishaudio_tts(
        text=text, reference_id=REF, seed=SEED, timeout=120, **kwargs,
    )
    elapsed = time.time() - t0
    if audio is None:
        print(f"FAILED ({elapsed:.0f}s)")
        return ""
    path = OUT / f"{name}.mp3"
    path.write_bytes(audio)
    dur = len(audio) * 8 / 192_000
    print(f"OK  {dur:.2f}s  {elapsed:.0f}s gen  {len(text)}c")
    return str(path)


def main():
    print(f"Voice: {REF}")
    print(f"Seed: {SEED}")
    print(f"Output: {OUT}")
    print(f"Text ({len(TEXT)}c): {TEXT}")
    print()

    # ── A. Baseline ──
    synth("A0_baseline", TEXT)

    # ── B. Official voice-style tags (prefix) ──
    # These are the ones most likely to change prosody:
    synth("B1_whispering",       f"[whispering] {TEXT}")
    synth("B2_loud_voice",       f"[loud voice] {TEXT}")
    synth("B3_soft_voice",       f"[soft voice] {TEXT}")
    synth("B4_low_voice",        f"[low voice] {TEXT}")
    synth("B5_shouting",         f"[shouting] {TEXT}")
    synth("B6_whispering_voice", f"[whispering voice] {TEXT}")

    # ── C. Official emotion tags (prefix) ──
    synth("C1_sad",     f"[sad] {TEXT}")
    synth("C2_angry",   f"[angry] {TEXT}")
    synth("C3_excited", f"[excited] {TEXT}")

    # ── D. Pacing tags (intra-segment) ──
    synth("D1_pause",
        "Personne n'osait parler. [pause] "
        "Le silence etait devenu pesant, presque insupportable. [pause] "
        "Boule de Suif, immobile, regardait fixement par la fenetre de la diligence.")
    synth("D2_short_pause",
        "Personne n'osait parler. [short pause] "
        "Le silence etait devenu pesant, presque insupportable. [short pause] "
        "Boule de Suif, immobile, regardait fixement par la fenetre de la diligence.")
    synth("D3_long_pause",
        "Personne n'osait parler. [long pause] "
        "Le silence etait devenu pesant, presque insupportable. [long pause] "
        "Boule de Suif, immobile, regardait fixement par la fenetre de la diligence.")

    # ── E. Combinations (emotion + voice style) ──
    synth("E1_sad_whispering",       f"[sad] [whispering] {TEXT}")
    synth("E2_angry_loud_voice",     f"[angry] [loud voice] {TEXT}")
    synth("E3_excited_loud_voice",   f"[excited] [loud voice] {TEXT}")
    synth("E4_sad_soft_voice",       f"[sad] [soft voice] {TEXT}")
    synth("E5_angry_low_voice",      f"[angry] [low voice] {TEXT}")

    # ── F. Vocal sounds (breathing, sighing) ──
    synth("F1_sigh",
        "[sigh] Personne n'osait parler. "
        "Le silence etait devenu pesant, presque insupportable.")
    synth("F2_inhale",
        "[inhale] Personne n'osait parler. "
        "Le silence etait devenu pesant, presque insupportable.")

    # ── G. Emphasis at key moments ──
    synth("G1_emphasis_mid",
        "Personne n'osait parler. Le silence etait devenu [emphasis] pesant, "
        "presque insupportable. Boule de Suif, immobile, regardait fixement "
        "par la fenetre de la diligence.")

    # ── H. Temperature variation (with SAME cloned voice + seed) ──
    synth("H1_temp_03", TEXT, temperature=0.3)
    synth("H2_temp_10", TEXT, temperature=1.0)

    print()
    print("=" * 70)
    print(f"Compare files in: {OUT}")
    print()
    print("Key comparisons to make by ear:")
    print("  A0 vs B1/B2/B4    — voice style tags")
    print("  A0 vs C1/C2/C3    — emotion tags alone")
    print("  C1 vs E1           — sad alone vs sad+whispering")
    print("  A0 vs D1/D2/D3     — pause tags (timing changes)")
    print("  A0 vs H1/H2        — temperature effect")
    print("=" * 70)


if __name__ == "__main__":
    main()
