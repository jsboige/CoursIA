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
  ("partition de musique"): motion per syllable, flat-transition %, span, and
  the STRUCTURAL criteria (effective notes, top-3 concentration, repeated
  3-note motifs) that yield the ``DRONE`` verdict. Motion and flat-% are LOCAL:
  a chant alternating two adjacent notes has perfectly normal step size and
  slipped through as ``MODERATE``. Measured 2026-08-18 on the extract served
  for review: 401 syllables, 6.0 effective notes, 73% on three adjacent
  semitones (A2/G#2/A#2), 82% of 3-note positions inside a repeated motif —
  it missed ``FLAT`` by 0.21 st and 1.2 points on the two local axes.
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
                     ``MONOTONE`` (melody FLAT or DRONE, or global span < flat floor),
                     ``WINDED`` (true breath failure), ``VOICE-SWAP`` (INCONSISTENT).
* ``WARN``         — surface *to the ear* with a caveat. Reasons: ``ERRATIC`` (over-
                     modulated, the Kokoro class), ``DRIFTING`` (mild timbre drift),
                     ``FADING`` (energy declination — noisy on short clips, informational).

``ERRATIC`` is an *abstention*, not a finding — read it that way
---------------------------------------------------------------
The docstring above already says no melody metric can separate over-modulation
from healthy expressivity, so the flag defers to the ear. It bears repeating at
the point of consumption, because the bare label reads like a defect and has
been consumed as one: a review note built on it told a reader the instrument had
a reservation about one specific take.

Measured on the seven #1028 review clips (2026-08-18), the flag does not
discriminate on the voice-cloning route — it tracks melodic *richness*:

===========================  =================  =================
clips                        effective notes    flagged ERRATIC
===========================  =================  =================
the 3 flagged                12.4 – 14.9        yes — all EXPRESSIVE
the 4 not flagged            5.4 – 10.2         no  — incl. all 3 DRONE
===========================  =================  =================

All three flagged clips are the *good* material; none of the three DRONE clips
is flagged. The thresholds also sit far below the ground truth that calibrated
them (Kokoro v1: span 33.6 st, motion 3.43 st/syll), which is the correct bias
for a send-to-the-ear flag and the reason it is over-inclusive by design.

``erratic_axes`` therefore reports *which* axis fired, so a consumer can see
whether a clip is near the calibrating pathology or merely melodic. An empty
list means the flag did not fire — it never means "measured clean".
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
DECAY_MIN_DURATION_S = 60.0 # below this, decay_db is masked (noisy on short clips)


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
    breath_trusted: bool = True,
) -> Dict[str, object]:
    """Map instrument verdicts to a gate outcome + reasons. Deterministic.

    Returns ``{"gate": <REJECT|WARN|PASS-TO-EAR|INCONCLUSIVE>, "reasons": [...],
    "erratic_axes": [...]}``. ``reasons`` is a list of strings as before; the
    *severity kind* (``"finding"`` vs ``"informational"``) of each reason is
    exposed separately in ``reason_kinds`` so consumers can render
    abstain-vs-disqualify distinctly. ``erratic_axes`` names which over-modulation
    axis fired (``"span"`` / ``"motion"``); it is ``None`` — never ``[]`` — when
    the segment was too short to evaluate, so "not measured" and "measured,
    nothing fired" never share one value.

    ``breath_trusted`` (default True) is False when the spectral breath instrument
    returned a verdict but the clip is too short for ``decay_db`` to be reliable
    (< ``DECAY_MIN_DURATION_S``). In that case a ``FADING`` verdict is **not**
    surfaced — a single-clip signal on a 20-second extract is noise, not
    information. See c.371-L3 ★★ (FADING distinct from REJECT) and the new
    ``short-clip decay_db masking`` guard.
    A single REJECT reason wins over any WARN; a WARN wins over PASS-TO-EAR.
    Kept free of audio so the decision policy is unit-testable without clips.
    """
    reject: List[str] = []
    reject_kinds: List[str] = []
    warn: List[str] = []
    warn_kinds: List[str] = []

    def _push_reject(name: str) -> None:
        reject.append(name)
        reject_kinds.append("finding")

    def _push_warn(name: str, kind: str = "finding") -> None:
        # WARNs default to "finding" (e.g. ERRATIC, GLOBAL-FLAT). The
        # breath-class FADING / DRIFTING abstentions are explicitly
        # "informational" because they defer to the ear on the cloning route
        # (c.371-L3 ★★). The DRIFTING voice verdict is a mild timbre signal —
        # same category.
        warn.append(name)
        warn_kinds.append(kind)

    # Not enough voiced material for a reliable reading -> abstain (the ear decides).
    if n_syllables < MIN_SYLLABLES or melody_verdict in (None, "INSUFFICIENT"):
        # Nothing was measured here: the axes are unevaluated, not clean.
        return {"gate": "INCONCLUSIVE",
                "reasons": ["TOO-SHORT"],
                "reason_kinds": ["informational"],
                "erratic_axes": None}

    # --- REJECT classes (confident bad) ---
    # Monotone is decided on the SYLLABLE verdict (robust: per-syllable motion +
    # flat-transition %), the signal the syllable_pitch author calibrated on. A low
    # GLOBAL span alone is outlier-driven and noisy on short clips, so when the
    # syllable verdict disagrees (MODERATE/EXPRESSIVE) it only WARNs, never rejects.
    if melody_verdict in ("FLAT", "DRONE"):
        _push_reject("MONOTONE")
    if breath_verdict == "WINDED":
        _push_reject("WINDED")
    if voice_verdict == "INCONSISTENT":
        _push_reject("VOICE-SWAP")

    # --- WARN classes (surface to the ear with a caveat) ---
    # Over-modulation: the Kokoro-v1 failure mode. High span AND/OR high motion
    # is NOT monotony but instability; a melody metric cannot tell it from good
    # expressivity, so flag it for the ear instead of guessing.
    erratic_axes: List[str] = []
    if melodic_span_st is not None and melodic_span_st >= ERRATIC_SPAN_ST:
        erratic_axes.append("span")
    if mean_abs_interval_st is not None and mean_abs_interval_st >= ERRATIC_MOTION_ST:
        erratic_axes.append("motion")
    if erratic_axes:
        _push_warn("ERRATIC", kind="finding")
    # Global span flat while the (robust) syllable verdict is not FLAT: borderline
    # monotone on a noisy short-clip global — surface to the ear, do not reject.
    if (global_range_st is not None and global_range_st < GLOBAL_FLAT_ST
            and melody_verdict not in ("FLAT", "DRONE")):
        _push_warn("GLOBAL-FLAT", kind="informational")
    if voice_verdict == "DRIFTING":
        _push_warn("DRIFTING", kind="informational")
    if breath_verdict == "FADING" and breath_trusted:
        # FADING is informational by default (defer to ear on the cloning route);
        # masked entirely when breath_trusted=False (short clip, decay_db is noise).
        _push_warn("FADING", kind="informational")

    if reject:
        return {"gate": "REJECT", "reasons": reject + warn,
                "reason_kinds": reject_kinds + warn_kinds,
                "erratic_axes": erratic_axes}
    if warn:
        return {"gate": "WARN", "reasons": warn,
                "reason_kinds": warn_kinds,
                "erratic_axes": erratic_axes}
    return {"gate": "PASS-TO-EAR", "reasons": [], "reason_kinds": [],
            "erratic_axes": erratic_axes}


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

    duration_s = mel.get("duration_s")
    # Short-clip guard for the breath instrument. decay_db on a 20-second
    # extract is dominated by the linear-decay fit's noise; the floor
    # (DECAY_MIN_DURATION_S = 60 s) is documented in the spectral envelope
    # module but NOT applied here. We mask the verdict at the gate level so
    # FADING can never be raised on a sub-threshold clip, and we null out
    # the dB reading so a downstream consumer cannot compare 32-s vs 114-s
    # values apples-to-apples. Measured 2026-08-18: B_regenere (113.9 s,
    # decay_db -4.54) was flagged FADING while L2 (32.3 s) was kept
    # PASS-TO-EAR — comparing those decay_db values without normalising on
    # duration is what produced the audit (#1028 c.371).
    breath_trusted = duration_s is None or duration_s >= DECAY_MIN_DURATION_S
    breath_verdict_raw = spec.get("breath_verdict")
    breath_verdict = breath_verdict_raw if breath_trusted else (
        breath_verdict_raw if breath_verdict_raw == "WINDED" else "STEADY"
    )
    # decay_db only carries meaning when the clip is long enough to fit;
    # emit null on short clips so consumers can't accidentally treat it as
    # comparable to a long-clip measurement.
    decay_db = spec.get("decay_db") if breath_trusted else None
    decay_trusted = breath_trusted  # surface the mask so the consumer knows

    decision = classify_segment(
        melody_verdict=mel.get("verdict"),
        global_range_st=glob.get("f0_semitone_range"),
        breath_verdict=breath_verdict,
        voice_verdict=spec.get("voice_verdict"),
        n_syllables=mel.get("n_syllables", 0),
        melodic_span_st=mel.get("melodic_span_st"),
        mean_abs_interval_st=mel.get("mean_abs_interval_st"),
        breath_trusted=breath_trusted,
    )

    return {
        "label": Path(path).stem,
        "path": Path(path).name,  # pas de chemin machine absolu dans le rapport partage (CodeQL clear-text + regle 6)
        "duration_s": duration_s,
        "gate": decision["gate"],
        "reasons": decision["reasons"],
        "reason_kinds": decision["reason_kinds"],
        "erratic_axes": decision["erratic_axes"],
        "melody_verdict": mel.get("verdict"),
        "drone_reasons": mel.get("drone_reasons", []),
        "effective_notes": mel.get("effective_notes"),
        "top3_note_pct": mel.get("top3_note_pct"),
        "motif3_repeat_pct": mel.get("motif3_repeat_pct"),
        "melodic_span_p5p95_st": mel.get("melodic_span_p5p95_st"),
        "n_syllables": mel.get("n_syllables"),
        "melodic_span_st": mel.get("melodic_span_st"),
        "mean_abs_interval_st": mel.get("mean_abs_interval_st"),
        "pct_flat_transitions": mel.get("pct_flat_transitions"),
        "global_range_st": glob.get("f0_semitone_range"),
        "breath_verdict": spec.get("breath_verdict"),
        "breath_verdict_effective": breath_verdict,
        "decay_db": decay_db,
        "decay_trusted": decay_trusted,
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
        # Self-descriptive per-clip line: gate · reasons · melody · span ·
        # breath + duration (so a 30-s and a 110-s clip can't be confused on
        # the same axis) + decay_db (or "n/a" when masked short).
        duration = r.get("duration_s")
        duration_str = f"{duration:.1f}s" if isinstance(duration, (int, float)) else "n/a"
        decay = r.get("decay_db")
        decay_str = f"{decay:+.2f}dB" if isinstance(decay, (int, float)) else "n/a(short)"
        print(f"{r['gate']:12s} [{reasons}]  melody={r['melody_verdict']} "
              f"span={r['melodic_span_st']}st breath={r['breath_verdict']} "
              f"dur={duration_str} decay={decay_str}")
        results.append(r)

    if reject_only:
        results = [r for r in results if r["gate"] in ("REJECT", "ERROR")]

    summary = {
        "audio_dir": Path(audio_dir).name,  # basename : pas de parent machine dans le rapport
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
            duration = r.get("duration_s")
            duration_str = f"{duration:.1f}s" if isinstance(duration, (int, float)) else "n/a"
            print(f"  {r['label']:44s} {','.join(r['reasons'])}  dur={duration_str}")


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
