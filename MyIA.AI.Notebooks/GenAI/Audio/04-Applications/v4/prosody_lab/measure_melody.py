"""measure_melody.py — effective-notes / top-3 / motif-repetition metrics (#11624).

The prosody gate (``verify_prosody``) rejects monotone chants (``FLAT``) but
does not quantify HOW narrow a melody is. These three summary metrics do, at
the syllable grain, from :func:`syllable_pitch.analyze_syllables`:

* ``effective_notes`` — exp(Shannon entropy) of the note-name distribution
  (true diversity; a chant parked on three adjacent semitones scores ~3, a
  varied reading 8+).
* ``top3_pct`` — share of syllables sitting on the 3 most frequent notes.
* ``motif_pct`` — share of 3-note positions whose note trigram was already
  heard earlier in the clip (repetition ratio of the melody).

Calibration (issue #11624, measured 2026-08-18): the served v4 extract scores
6.0 effective notes / 72.8 % top-3 / 82.2 % motifs — a drone. Target for a
regenerated review extract: > 7 effective notes, top-3 < 65 %, motifs < 60 %.

CLI::

    python measure_melody.py CLIP.mp3 [CLIP2.mp3 ...] [--json OUT]
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Dict, List

try:
    from syllable_pitch import analyze_syllables
except ImportError:  # pragma: no cover - allow running from another cwd
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from syllable_pitch import analyze_syllables


def _shannon_entropy(counts: Dict[str, int]) -> float:
    total = sum(counts.values())
    if total == 0:
        return 0.0
    return -sum((c / total) * math.log(c / total) for c in counts.values())


def measure_clip(path: str) -> Dict:
    """Run the three melody-narrowness metrics on one audio clip."""
    a = analyze_syllables(path)
    notes = [s["note"] for s in a.get("syllables", [])]
    result: Dict = {
        "label": Path(path).stem,
        "path": path,
        "n_syllables": len(notes),
        "n_distinct_notes": len(set(notes)),
        "verdict": a.get("verdict", "INSUFFICIENT"),
    }
    if len(notes) < 3:
        result.update(
            {
                "effective_notes": 0.0,
                "top3_pct": None,
                "motif_pct": None,
                "note": "INSUFFICIENT_SYLLABLES",
            }
        )
        return result

    counts: Dict[str, int] = {}
    for n in notes:
        counts[n] = counts.get(n, 0) + 1
    eff = math.exp(_shannon_entropy(counts))
    top3 = sorted(counts.items(), key=lambda kv: kv[1], reverse=True)[:3]
    top3_count = sum(c for _, c in top3)

    trigrams: List[str] = []
    for i in range(len(notes) - 2):
        trigrams.append(f"{notes[i]}|{notes[i+1]}|{notes[i+2]}")
    seen: set = set()
    repeats = 0
    for t in trigrams:
        if t in seen:
            repeats += 1
        seen.add(t)

    result.update(
        {
            "effective_notes": round(eff, 2),
            "top3_pct": round(100.0 * top3_count / len(notes), 1),
            "top3_notes": [n for n, _ in top3],
            "motif_pct": round(100.0 * repeats / len(trigrams), 1),
            "note": "OK",
        }
    )
    return result


def main() -> None:
    ap = argparse.ArgumentParser(description="Melody-narrowness metrics (#11624)")
    ap.add_argument("clips", nargs="+", help="audio files (mp3/wav)")
    ap.add_argument("--json", default=None, help="write all measurements to this JSON")
    args = ap.parse_args()

    out = []
    for clip in args.clips:
        m = measure_clip(clip)
        print(
            f"{m['label']}: {m['n_syllables']} syll | "
            f"eff-notes={m['effective_notes']} | top3={m['top3_pct']}% | "
            f"motifs={m['motif_pct']}% | distinct={m['n_distinct_notes']} | {m['verdict']}"
        )
        out.append(m)

    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(
            json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        print(f"\n[json] {args.json}")


if __name__ == "__main__":
    main()
