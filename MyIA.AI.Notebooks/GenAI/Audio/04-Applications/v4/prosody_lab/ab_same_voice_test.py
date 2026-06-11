#!/usr/bin/env python3
"""A/B test: SAME voice identity, different temperature — #1877 prosody fix.

The previous A/B tests were INVALID because they compared different voices
(woman vs man) by changing reference_id. This test keeps the SAME reference_id
and only varies the `temperature` parameter to measure prosody variation.

  A (LOW TEMP)  = reference_id + temperature=0.3  → conservative, flatter prosody
  B (HIGH TEMP) = reference_id + temperature=1.2  → expressive, wider prosody

Both clips use the SAME voice identity (same timbre). If B is significantly
more expressive than A, then temperature IS the prosody control knob.

Tested on BOTH narrator and dialogue voices:
  - Narrator: v4_narrator_male_neutral
  - Dialogue: v4_cornudet_mocking

Usage:
    cd v4/prosody_lab/
    python ab_same_voice_test.py

Output:
    outputs/prosody_lab/ab_sv_narrator_low.mp3
    outputs/prosody_lab/ab_sv_narrator_high.mp3
    outputs/prosody_lab/ab_sv_dialogue_low.mp3
    outputs/prosody_lab/ab_sv_dialogue_high.mp3
    outputs/prosody_lab/ab_same_voice_metrics.json
    outputs/prosody_lab/ab_same_voice_contours.png
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

# Test texts
NARRATOR_TEXT = (
    "Enfin, a trois heures, comme on se trouvait au milieu d'une plaine "
    "interminable, Boule de Suif retira de sous la banquette un large panier "
    "couvert d'une serviette blanche."
)

DIALOGUE_TEXT = (
    "Vous lui direz a cette crapule, a ce saligaud, a cette Charogne de "
    "Prussien, que jamais je ne voudrai; vous entendez bien, jamais, jamais."
)

# Voice identities (same for both A and B within each pair)
NARRATOR_REF = "v4_narrator_male_neutral"
DIALOGUE_REF = "v4_cornudet_mocking"

# Temperature settings
TEMP_LOW = 0.1    # Minimum → expected flatter
TEMP_HIGH = 1.0   # Maximum → expected wider prosody

SEED = 42

# Output files
FILES = {
    "narrator_low":    OUTPUT_DIR / "ab_sv_narrator_low.mp3",
    "narrator_high":   OUTPUT_DIR / "ab_sv_narrator_high.mp3",
    "dialogue_low":    OUTPUT_DIR / "ab_sv_dialogue_low.mp3",
    "dialogue_high":   OUTPUT_DIR / "ab_sv_dialogue_high.mp3",
}
OUT_METRICS = OUTPUT_DIR / "ab_same_voice_metrics.json"
OUT_PLOT = OUTPUT_DIR / "ab_same_voice_contours.png"


# ---------------------------------------------------------------------------
# Generation
# ---------------------------------------------------------------------------

def generate_pair(label: str, text: str, ref_id: str) -> tuple[bytes, bytes]:
    """Generate low-temp and high-temp versions of the same text+voice."""
    print(f"\n[{label}] Generating pair (ref={ref_id})...")

    # Low temperature
    print(f"  [A] temperature={TEMP_LOW} ...")
    t0 = time.time()
    audio_low = fishaudio_tts(
        text=text, reference_id=ref_id,
        temperature=TEMP_LOW, seed=SEED, format="mp3", timeout=300,
    )
    dt_low = time.time() - t0
    if audio_low is None:
        print(f"  ERROR: Low-temp generation failed for {label}")
        sys.exit(1)
    print(f"  -> {len(audio_low)/1024:.0f} KB in {dt_low:.1f}s")

    # High temperature
    print(f"  [B] temperature={TEMP_HIGH} ...")
    t0 = time.time()
    audio_high = fishaudio_tts(
        text=text, reference_id=ref_id,
        temperature=TEMP_HIGH, seed=SEED, format="mp3", timeout=300,
    )
    dt_high = time.time() - t0
    if audio_high is None:
        print(f"  ERROR: High-temp generation failed for {label}")
        sys.exit(1)
    print(f"  -> {len(audio_high)/1024:.0f} KB in {dt_high:.1f}s")

    return audio_low, audio_high


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 60)
    print("A/B SAME VOICE TEST — #1877 prosody fix")
    print(f"Same reference_id, varying temperature: {TEMP_LOW} vs {TEMP_HIGH}")
    print(f"Seed: {SEED}")
    print("=" * 60)

    # Narrator pair
    narr_low, narr_high = generate_pair("Narrator", NARRATOR_TEXT, NARRATOR_REF)
    FILES["narrator_low"].write_bytes(narr_low)
    FILES["narrator_high"].write_bytes(narr_high)

    # Dialogue pair
    dial_low, dial_high = generate_pair("Dialogue", DIALOGUE_TEXT, DIALOGUE_REF)
    FILES["dialogue_low"].write_bytes(dial_low)
    FILES["dialogue_high"].write_bytes(dial_high)

    print("\n" + "=" * 60)
    print("All 4 clips generated!")
    print(f"Output dir: {OUTPUT_DIR}/")
    for name, path in FILES.items():
        print(f"  {path.name} ({name})")
    print()
    print("Run prosody_metrics.py to measure ST/CV:")
    print(f"  python prosody_metrics.py \\")
    for label, path in FILES.items():
        print(f"    {label}={path} \\")
    print(f"    --json {OUT_METRICS} --plot {OUT_PLOT}")


if __name__ == "__main__":
    main()
