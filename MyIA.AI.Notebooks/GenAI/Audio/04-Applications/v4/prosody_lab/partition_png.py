#!/usr/bin/env python3
"""partition_png.py — #11624: two-staff same-passage partition as a PNG.

The user-facing A/B card (ai-01 DM 2026-08-18 16:19): the SERVED extract
(A) and the REGENERATED extract (B) are the SAME phrases — plotting both
note sequences one under the other over a shared syllable axis makes the
drone vs the movement visible without listening.

Usage::

    python partition_png.py --a A_servi_depuis_mai.mp3 \
        --b B_regenere_2026-08-18.mp3 --out partition_A_vs_B.png
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from syllable_pitch import analyze_syllables  # noqa: E402
from partition import to_french, _FR, _EN  # noqa: E402


def midi_tick_label(m: int) -> str:
    return f"{_FR[m % 12]}{m // 12 - 1}"


def main() -> None:
    ap = argparse.ArgumentParser(description="Two-staff same-passage partition PNG")
    ap.add_argument("--a", required=True, help="clip A (served)")
    ap.add_argument("--b", required=True, help="clip B (regenerated), same phrases")
    ap.add_argument("--out", required=True, help="output PNG path")
    args = ap.parse_args()

    seqs = {}
    for key, path in (("A", args.a), ("B", args.b)):
        res = analyze_syllables(path)
        seqs[key] = {
            "label": Path(path).stem,
            "midi": [s["midi"] for s in res["syllables"]],
            "n": res["n_syllables"],
        }

    lo = int(min(min(s["midi"]) for s in seqs.values())) - 1
    hi = int(max(max(s["midi"]) for s in seqs.values())) + 1

    meta = {
        "A": ("A — servi depuis mai (DRONE : 6,0 notes eff., top-3 72,8 %)", "#b4443c"),
        "B": ("B — régénéré 2026-08-18, mêmes phrases (EXPRESSIVE : 14,9 notes eff., top-3 32,3 %)", "#2c6e8f"),
    }

    fig, axes = plt.subplots(
        2, 1, figsize=(16, 7.5), sharex=True, sharey=True,
        gridspec_kw={"hspace": 0.3},
    )
    xmax = max(s["n"] for s in seqs.values())
    for ax, key in zip(axes, ("A", "B")):
        s = seqs[key]
        xs = list(range(1, s["n"] + 1))
        title, color = meta[key]
        ax.step(xs, s["midi"], where="mid", color=color, linewidth=1.4, alpha=0.85)
        ax.plot(xs, s["midi"], linestyle="none", marker="o", markersize=2.2, color=color)
        ax.set_title(title, fontsize=11, loc="left", color=color)
        ax.set_ylim(lo, hi)
        ax.set_xlim(1, xmax)
        ax.set_ylabel("note", fontsize=9)
        ax.grid(axis="y", which="major", linewidth=0.4, alpha=0.5)
        ax.grid(axis="x", linewidth=0.15, alpha=0.3)
    axes[0].set_yticks(range(lo, hi + 1))
    axes[0].set_yticklabels([midi_tick_label(m) for m in range(lo, hi + 1)], fontsize=6.5)
    axes[1].set_xlabel("syllabe (index)", fontsize=9)

    fig.suptitle(
        "Partition syllabique — mêmes phrases (Boule de Suif, ouverture) : "
        "A répète ses notes dans une bande étroite, B se déplace",
        fontsize=12,
    )
    out = Path(args.out)
    fig.savefig(out, dpi=150, bbox_inches="tight")
    print(f"OK {out} ({out.stat().st_size // 1024} KB)")
    for key in ("A", "B"):
        s = seqs[key]
        notes = [to_french(midi_to := f"{_EN[int(round(m)) % 12]}{int(round(m)) // 12 - 1}") for m in s["midi"][:8]]
        print(f"  {key}: {s['n']} syllabes, debut: {' '.join(notes)}")


if __name__ == "__main__":
    main()
