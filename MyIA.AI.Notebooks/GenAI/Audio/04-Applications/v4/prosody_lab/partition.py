#!/usr/bin/env python3
"""partition.py — #11624: print the melody as a readable score of note names.

The user's ask (issue #11624, relayed by ai-01 2026-08-18): "On veut
litteralement des notes de musique — la melodie, ca n'est pas qu'une
metaphore, c'est le meilleur indice de monotonie." This prints, side by
side, the per-syllable note sequence of two or more renders of the SAME
passage, in French solfege names (La2, Sol#2, Do3...), so the lancinant
drone of one and the movement of the other are VISIBLE without listening.

Usage::

    python partition.py --first 64 clip_a.mp3 clip_b.mp3 [--json out.json]

Output: one block per clip, notes grouped by 8 for counting; the clips
should be renders of the same text (the syllable detectors do not align
words, so the comparison is statistical per index, not word-exact).
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

try:
    from syllable_pitch import analyze_syllables
except ImportError:  # direct execution from another cwd
    from syllable_pitch import analyze_syllables  # noqa: F811

# English (C..B) -> French solfege, per MIDI octave m // 12 - 1.
_FR = ["Do", "Do#", "Re", "Re#", "Mi", "Fa", "Fa#", "Sol", "Sol#", "La", "La#", "Si"]
_EN = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]


def to_french(note: str) -> str:
    """'A#2' -> 'La#2' (octave digits pass through)."""
    pitch = note[:-1]
    octave = note[-1]
    if pitch not in _EN:
        return note
    return _FR[_EN.index(pitch)] + octave


def partition_lines(path: str, first: int) -> dict:
    res = analyze_syllables(path)
    sylls = res["syllables"][:first]
    notes = [to_french(s["note"]) for s in sylls]
    return {
        "label": res["label"],
        "n_syllables_total": res["n_syllables"],
        "n_syllables_shown": len(notes),
        "notes": notes,
        "f0_hz_first10": [s["f0_hz"] for s in sylls[:10]],
    }


def _fmt_groups(notes: list[str], group: int = 8) -> str:
    out = []
    for i in range(0, len(notes), group):
        out.append(" ".join(notes[i : i + group]))
    return "\n    ".join(out)


def main() -> None:
    ap = argparse.ArgumentParser(description="Melody partition in note names (#11624)")
    ap.add_argument("clips", nargs="+", help="audio clips of the SAME passage")
    ap.add_argument("--first", type=int, default=64, help="first N syllables per clip")
    ap.add_argument("--json", default=None, help="write full sequences to JSON")
    args = ap.parse_args()

    parts = []
    for clip in args.clips:
        p = partition_lines(clip, args.first)
        parts.append(p)
        print(f"{p['label']}  ({p['n_syllables_shown']}/{p['n_syllables_total']} syllabes):")
        print(f"    {_fmt_groups(p['notes'])}")
        print()

    if args.json:
        Path(args.json).write_text(
            json.dumps(parts, ensure_ascii=False, indent=1), encoding="utf-8"
        )
        print(f"[json] {args.json}")


if __name__ == "__main__":
    main()
