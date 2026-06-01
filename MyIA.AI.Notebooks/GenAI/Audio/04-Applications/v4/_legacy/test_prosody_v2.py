"""Prosody test v2 — applying FishAudio official recommendations.

From the FishAudio blog:
1. Tags affect what comes AFTER them
2. Combine emotions with physical reactions: [sigh] [sad]
3. "Different voices respond to tags with variable intensity"
4. Reinforce subtle tags with surrounding text context
5. Free-form natural language IS accepted: [speaking slowly, almost hesitant]

This test tries:
- Repeating tags mid-segment to maintain prosody
- Combining emotion + reaction (sigh+sad, inhale+angry)
- Free-form descriptions per the blog
- Shorter texts (tags have more weight on short segments)

Usage:
    cd v4 && python test_prosody_v2.py
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

_parent = str(Path(__file__).resolve().parent)
sys.path.insert(0, _parent)

from fishaudio_client import fishaudio_tts, OUTPUT_DIR

REF = "v4_narrator_male_neutral"
SEED = 42
OUT = OUTPUT_DIR / "prosody_v2"
OUT.mkdir(exist_ok=True)


def synth(name: str, text: str, **kw) -> str:
    print(f"  {name:45s}", end="", flush=True)
    t0 = time.time()
    audio = fishaudio_tts(text=text, reference_id=REF, seed=SEED, timeout=120, **kw)
    elapsed = time.time() - t0
    if audio is None:
        print(f"FAILED ({elapsed:.0f}s)")
        return ""
    path = OUT / f"{name}.mp3"
    path.write_bytes(audio)
    dur = len(audio) * 8 / 192_000
    print(f"OK  {dur:.2f}s  {elapsed:.0f}s gen")
    return str(path)


def main():
    print(f"Voice: {REF} | Seed: {SEED}")
    print(f"Output: {OUT}\n")

    # Short text — tags have more weight on shorter segments
    SHORT = "Le silence pesant. Personne ne parlait. Boule de Suif restait immobile."
    # Medium text — typical segment
    MEDIUM = (
        "Personne n'osait parler. Le silence etait devenu pesant, "
        "presque insupportable. Boule de Suif, immobile, regardait "
        "fixement par la fenetre de la diligence."
    )

    # ── A. Baseline short + medium ──
    synth("A0_short_baseline", SHORT)
    synth("A1_medium_baseline", MEDIUM)

    # ── B. REPEATED tags mid-segment (FishAudio: "tags affect what comes AFTER") ──
    synth("B1_sad_repeated",
        "[sad] Le silence pesant. [sad] Personne ne parlait. [sad] "
        "Boule de Suif restait immobile.")
    synth("B2_angry_repeated",
        "[angry] Le silence pesant. [angry] Personne ne parlait. [angry] "
        "Boule de Suif restait immobile.")
    synth("B3_shouting_repeated",
        "[shouting] Le silence pesant! [shouting] Personne ne parlait! [shouting] "
        "Boule de Suif restait immobile!")
    synth("B4_whispering_repeated",
        "[whispering] Le silence pesant. [whispering] Personne ne parlait. [whispering] "
        "Boule de Suif restait immobile.")

    # ── C. EMOTION + REACTION combos (FishAudio recommendation) ──
    synth("C1_sigh_sad",
        "[sigh] [sad] Le silence pesant. Personne ne parlait. "
        "Boule de Suif restait immobile.")
    synth("C2_inhale_angry",
        "[inhale] [angry] Le silence pesant. Personne ne parlait. "
        "Boule de Suif restait immobile.")
    synth("C3_exhale_sad",
        "[exhale] [sad] Le silence pesant. Personne ne parlait. "
        "Boule de Suif restait immobile.")
    synth("C4_sigh_sad_repeated",
        "[sigh] [sad] Le silence pesant. [pause] [sad] Personne ne parlait. "
        "[pause] [sad] Boule de Suif restait immobile.")

    # ── D. FREE-FORM descriptions (blog says these ARE accepted) ──
    synth("D1_speaking_slowly",
        "[speaking slowly, in a hushed tone] Le silence pesant. "
        "Personne ne parlait. Boule de Suif restait immobile.")
    synth("D2_voice_trembling",
        "[with a trembling voice, barely audible] Le silence pesant. "
        "Personne ne parlait. Boule de Suif restait immobile.")
    synth("D3_cold_flat",
        "[in a cold, flat monotone] Le silence pesant. "
        "Personne ne parlait. Boule de Suif restait immobile.")
    synth("D4_angry_clenched",
        "[through clenched teeth, furious] Le silence pesant. "
        "Personne ne parlait. Boule de Suif restait immobile.")

    # ── E. Transitions: normal → emotional ──
    synth("E1_normal_to_whisper",
        "Le silence pesant. Personne ne parlait. [whispering] "
        "Boule de Suif restait immobile.")
    synth("E2_normal_to_shout",
        "Le silence pesant. Personne ne parlait. [shouting] "
        "Boule de Suif restait immobile!")
    synth("E3_soft_to_loud",
        "[soft voice] Le silence pesant. Personne ne parlait. [loud voice] "
        "Boule de Suif restait immobile!")

    # ── F. Medium text with REPEATED tags (most realistic for pipeline) ──
    synth("F1_sad_repeat_medium",
        "[sad] Personne n'osait parler. [pause] [sad] Le silence etait devenu "
        "pesant, presque insupportable. [pause] [sad] Boule de Suif, immobile, "
        "regardait fixement par la fenetre de la diligence.")
    synth("F2_angry_repeat_medium",
        "[angry] Personne n'osait parler. [pause] [angry] Le silence etait devenu "
        "pesant, presque insupportable. [pause] [angry] Boule de Suif, immobile, "
        "regardait fixement par la fenetre de la diligence.")
    synth("F3_whisper_repeat_medium",
        "[whispering] Personne n'osait parler. [pause] [whispering] Le silence etait "
        "devenu pesant, presque insupportable. [pause] [whispering] Boule de Suif, "
        "immobile, regardait fixement par la fenetre de la diligence.")

    print()
    print("=" * 70)
    print(f"Files: {OUT}")
    print()
    print("Key comparisons:")
    print("  A0 vs B1/B2/B3/B4  — repeated tags on short text")
    print("  A1 vs F1/F2/F3     — repeated tags on medium text")
    print("  A0 vs C1/C2/C3     — emotion+reaction combos")
    print("  A0 vs D1/D2/D3/D4  — free-form descriptions")
    print("  A0 vs E1/E2/E3     — emotional transitions")
    print("=" * 70)


if __name__ == "__main__":
    main()
