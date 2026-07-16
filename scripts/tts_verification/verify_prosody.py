#!/usr/bin/env python3
"""Stage 3: prosody gate — the objective FLOOR before a human ear (#1028).

Stages 1 and 2 of this folder verify *which words* are spoken (WER, ``verify_transcript``)
and *who* speaks them (voice purity, ``verify_diarization``). Neither hears the
*melody*, so a perfectly intelligible yet monotone — or breathless, or voice-swapping —
reading passes them untouched. That is the exact class of defect that has repeatedly
wasted review time on the audiobook EPIC (#1028): "mauvaise prosodie".

This stage composes the three prosody instruments the user mandated
(``MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/``, #1273/#1877):

* ``syllable_pitch.analyze_syllables``  — the MELODY, syllable by syllable
  ("partition de musique"): motion per syllable, flat-transition %, span
  -> FLAT / MODERATE / EXPRESSIVE.
* ``prosody_metrics.compute_metrics``   — the GLOBAL melody: ``f0_semitone_range``
  (< ~4 st = monotone, ~8-12 st = expressive audiobook narration).
* ``spectral_envelope.analyze_spectral`` — the ENERGY envelope: essoufflement
  (breath fading -> WINDED) and voice consistency (chunk re-design / narrator
  bleed -> INCONSISTENT).

What this gate is, and what it is NOT
-------------------------------------
It is a FLOOR, not a naturalness verdict. It reliably rejects three *bad* classes:
monotone chant, true essoufflement, and voice swaps. It does NOT certify a segment
as good — naturalness at the high end still needs the ear. Ground truth for that
caveat: the invalidated Kokoro Boule-de-Suif v1 scores ``EXPRESSIVE`` (span 33.6 st,
motion 3.43 st/syll) — its "bad prosody" is not monotony but *erratic over-modulation*,
which no melody metric can distinguish from healthy expressivity. That failure mode is
surfaced here as ``WARN-ERRATIC`` (span/motion pathologically high), never auto-passed
and never auto-rejected — it is an explicit "send this one to the ear" flag.

Gate outcomes
-------------
* ``REJECT``       — a bad class is detected with confidence; do not surface. Reasons:
                     ``MONOTONE`` (melody FLAT or global span < flat floor),
                     ``WINDED`` (true breath failure), ``VOICE-SWAP`` (INCONSISTENT).
* ``WARN``         — surface *to the ear* with a caveat. Reasons: ``ERRATIC`` (over-
                     modulated, the Kokoro class), ``DRIFTING`` (mild timbre drift),
                     ``FADING`` (energy declination — noisy on short clips, informational).
* ``PASS-TO-EAR``  — objective floor cleared; the ear makes the final call.
* ``INCONCLUSIVE`` — too short / too few voiced syllables for a reliable reading
                     (the instruments abstain rather than cry wolf). Needs the ear.

CLI::

    python verify_prosody.py --audio-dir DIR [--json OUT] [--reject-only]
    python verify_prosody.py --single seg.mp3

Env: needs a Python with librosa/scipy/sklearn/matplotlib (miniconda base has
librosa 0.11). The prosody_lab dir is auto-located from the repo layout; override
with ``--lab-dir`` or ``$PROSODY_LAB_DIR``.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Dict, List, Optional

# --- Gate thresholds (provisional; conservative — WARN before REJECT) --------
GLOBAL_FLAT_ST = 4.0        # global f0_semitone_range below this == monotone
ERRATIC_SPAN_ST = 18.0      # syllable span above this == over-modulated (Kokoro class)
ERRATIC_MOTION_ST = 2.5     # mean |interval| per syllable above this == erratic
MIN_SYLLABLES = 4           # fewer voiced syllables than this -> INCONCLUSIVE


# ---------------------------------------------------------------------------
# Pure gate logic (no audio, no I/O) — this is the CI-testable core.
# ---------------------------------------------------------------------------

def classify_segment(
    melody_verdict: Optional[str],
    global_range_st: Optional[float],
    breath_verdict: Optional[str],
    voice_verdict: Optional[str],
    n_syllables: int,
    melodic_span_st: Optional[float] = None,
    mean_abs_interval_st: Optional[float] = None,
) -> Dict[str, object]:
    """Map instrument verdicts to a gate outcome + reasons. Deterministic.

    Returns ``{"gate": <REJECT|WARN|PASS-TO-EAR|INCONCLUSIVE>, "reasons": [...]}``.
    A single REJECT reason wins over any WARN; a WARN wins over PASS-TO-EAR.
    Kept free of audio so the decision policy is unit-testable without clips.
    """
    reject: List[str] = []
    warn: List[str] = []

    # Not enough voiced material for a reliable reading -> abstain (the ear decides).
    if n_syllables < MIN_SYLLABLES or melody_verdict in (None, "INSUFFICIENT"):
        return {"gate": "INCONCLUSIVE", "reasons": ["TOO-SHORT"]}

    # --- REJECT classes (confident bad) ---
    # Monotone is decided on the SYLLABLE verdict (robust: per-syllable motion +
    # flat-transition %), the signal the syllable_pitch author calibrated on. A low
    # GLOBAL span alone is outlier-driven and noisy on short clips, so when the
    # syllable verdict disagrees (MODERATE/EXPRESSIVE) it only WARNs, never rejects.
    if melody_verdict == "FLAT":
        reject.append("MONOTONE")
    if breath_verdict == "WINDED":
        reject.append("WINDED")
    if voice_verdict == "INCONSISTENT":
        reject.append("VOICE-SWAP")

    # --- WARN classes (surface to the ear with a caveat) ---
    # Over-modulation: the Kokoro-v1 failure mode. High span AND/OR high motion
    # is NOT monotony but instability; a melody metric cannot tell it from good
    # expressivity, so flag it for the ear instead of guessing.
    if (melodic_span_st is not None and melodic_span_st >= ERRATIC_SPAN_ST) or (
        mean_abs_interval_st is not None and mean_abs_interval_st >= ERRATIC_MOTION_ST
    ):
        warn.append("ERRATIC")
    # Global span flat while the (robust) syllable verdict is not FLAT: borderline
    # monotone on a noisy short-clip global — surface to the ear, do not reject.
    if global_range_st is not None and global_range_st < GLOBAL_FLAT_ST and melody_verdict != "FLAT":
        warn.append("GLOBAL-FLAT")
    if voice_verdict == "DRIFTING":
        warn.append("DRIFTING")
    if breath_verdict == "FADING":
        warn.append("FADING")

    if reject:
        return {"gate": "REJECT", "reasons": reject + warn}
    if warn:
        return {"gate": "WARN", "reasons": warn}
    return {"gate": "PASS-TO-EAR", "reasons": []}


# ---------------------------------------------------------------------------
# Instrument loading + per-segment analysis (needs audio + librosa).
# ---------------------------------------------------------------------------

def _default_lab_dir() -> Path:
    """Locate prosody_lab from the repo layout (this file lives in scripts/)."""
    env = os.getenv("PROSODY_LAB_DIR")
    if env:
        return Path(env)
    repo = Path(__file__).resolve().parents[2]
    return repo / "MyIA.AI.Notebooks" / "GenAI" / "Audio" / "04-Applications" / "v4" / "prosody_lab"


def _import_instruments(lab_dir: Path):
    """Import the three prosody_lab instruments; return the callables."""
    lab = str(lab_dir)
    if lab not in sys.path:
        sys.path.insert(0, lab)
    import prosody_metrics
    import spectral_envelope
    import syllable_pitch
    return (
        syllable_pitch.analyze_syllables,
        prosody_metrics.compute_metrics,
        spectral_envelope.analyze_spectral,
    )


def analyze_segment(path: str, instruments) -> Dict[str, object]:
    """Run the three instruments on one clip and apply the gate."""
    analyze_syllables, compute_metrics, analyze_spectral = instruments

    mel = analyze_syllables(path)
    glob = compute_metrics(path)
    spec = analyze_spectral(path)
    spec.pop("_plot", None)  # heavy arrays: never serialize

    decision = classify_segment(
        melody_verdict=mel.get("verdict"),
        global_range_st=glob.get("f0_semitone_range"),
        breath_verdict=spec.get("breath_verdict"),
        voice_verdict=spec.get("voice_verdict"),
        n_syllables=mel.get("n_syllables", 0),
        melodic_span_st=mel.get("melodic_span_st"),
        mean_abs_interval_st=mel.get("mean_abs_interval_st"),
    )

    return {
        "label": Path(path).stem,
        "path": str(path),
        "duration_s": mel.get("duration_s"),
        "gate": decision["gate"],
        "reasons": decision["reasons"],
        "melody_verdict": mel.get("verdict"),
        "n_syllables": mel.get("n_syllables"),
        "melodic_span_st": mel.get("melodic_span_st"),
        "mean_abs_interval_st": mel.get("mean_abs_interval_st"),
        "pct_flat_transitions": mel.get("pct_flat_transitions"),
        "global_range_st": glob.get("f0_semitone_range"),
        "breath_verdict": spec.get("breath_verdict"),
        "decay_db": spec.get("decay_db"),
        "max_voiced_run_s": spec.get("max_voiced_run_s"),
        "voice_verdict": spec.get("voice_verdict"),
        "n_voice_clusters": spec.get("n_voice_clusters"),
    }


def verify_batch(
    audio_dir: str,
    lab_dir: Optional[str] = None,
    output_path: Optional[str] = None,
    reject_only: bool = False,
) -> Dict[str, object]:
    """Run the prosody gate over every mp3/wav in a directory."""
    lab = Path(lab_dir) if lab_dir else _default_lab_dir()
    instruments = _import_instruments(lab)

    clips = sorted(
        p for p in Path(audio_dir).iterdir()
        if p.suffix.lower() in (".mp3", ".wav", ".m4a", ".flac")
    )
    results: List[Dict[str, object]] = []
    counts: Dict[str, int] = {}
    for i, clip in enumerate(clips):
        print(f"  [{i + 1}/{len(clips)}] {clip.name}...", end=" ", flush=True)
        try:
            r = analyze_segment(str(clip), instruments)
        except Exception as e:  # one bad clip must not abort the batch
            print(f"ERR {str(e)[:60]}")
            results.append({"label": clip.stem, "gate": "ERROR", "reasons": [str(e)[:120]]})
            counts["ERROR"] = counts.get("ERROR", 0) + 1
            continue
        counts[r["gate"]] = counts.get(r["gate"], 0) + 1
        reasons = ",".join(r["reasons"]) if r["reasons"] else "-"
        print(f"{r['gate']:12s} [{reasons}]  melody={r['melody_verdict']} "
              f"span={r['melodic_span_st']}st breath={r['breath_verdict']}")
        results.append(r)

    if reject_only:
        results = [r for r in results if r["gate"] in ("REJECT", "ERROR")]

    summary = {
        "audio_dir": str(audio_dir),
        "total": len(clips),
        "counts": counts,
        "results": results,
    }
    if output_path:
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)
        Path(output_path).write_text(
            json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        print(f"\n[json] {output_path}")
    return summary


def print_report(summary: Dict[str, object]) -> None:
    counts = summary["counts"]
    print(f"\n{'=' * 64}")
    print("PROSODY GATE (stage 3) — objective floor, ear judges the survivors")
    print(f"{'=' * 64}")
    print(f"Segments: {summary['total']}")
    for gate in ("REJECT", "WARN", "PASS-TO-EAR", "INCONCLUSIVE", "ERROR"):
        if counts.get(gate):
            print(f"  {gate:12s}: {counts[gate]}")
    rejected = [r for r in summary["results"] if r.get("gate") == "REJECT"]
    if rejected:
        print("\n--- REJECT (do not surface — send to _history with reason) ---")
        for r in rejected:
            print(f"  {r['label']:44s} {','.join(r['reasons'])}")


def main() -> None:
    ap = argparse.ArgumentParser(description="Stage 3: prosody gate (melody + spectral floor)")
    ap.add_argument("--audio-dir", help="directory of mp3/wav segments")
    ap.add_argument("--single", help="single clip to gate")
    ap.add_argument("--lab-dir", default=None, help="override prosody_lab location")
    ap.add_argument("--json", default=None, help="write the gate report to this JSON")
    ap.add_argument("--reject-only", action="store_true", help="report only REJECT/ERROR")
    args = ap.parse_args()

    if args.single:
        instruments = _import_instruments(Path(args.lab_dir) if args.lab_dir else _default_lab_dir())
        r = analyze_segment(args.single, instruments)
        print(json.dumps(r, indent=2, ensure_ascii=False))
        return

    if not args.audio_dir:
        print("Error: --audio-dir or --single required")
        sys.exit(1)

    summary = verify_batch(
        audio_dir=args.audio_dir,
        lab_dir=args.lab_dir,
        output_path=args.json,
        reject_only=args.reject_only,
    )
    print_report(summary)


if __name__ == "__main__":
    main()
