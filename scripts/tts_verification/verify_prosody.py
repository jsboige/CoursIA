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
    python verify_prosody.py --single seg.mp3 [--window-s 180]

A clip longer than ``LONG_FORM_WINDOW_S`` (180 s) is gated in WINDOWS
(#21485): the structural criteria are functions of the sequence length, so a
verdict taken on a whole chapter measures the aggregation rather than the take.
Each window goes through the unchanged short-segment path; the fold keeps the
worst melody verdict, the widest span, the fastest motion and the narrowest
global range, and reads breath/voice over the whole file.

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

# --- Long-form artefacts (a chapter is not a segment) ----------------------
# A segment is 30-130 s; a delivered audiobook chapter is ~1400 s. The two
# structural criteria are FUNCTIONS OF THE SEQUENCE LENGTH, not only of the
# melody: `motif3_repeat_pct` counts the positions whose 3-note motif occurs
# at least twice *anywhere in the sequence*, so it saturates as the sequence
# grows (#21485, measured on the chapter-1 delivery: 85.2% on the 1365-s file
# against 44.3-49.7% on its 170-s windows -- the same audio, and the 60%
# drone threshold crossed by duration alone). `melodic_span_st` drifts the
# same way. A verdict computed on the whole artefact therefore measures the
# aggregation, not the take.
# So a long artefact is gated in FIXED-LENGTH WINDOWS: each window goes
# through the unchanged short-segment path, and a window's verdict is exactly
# what the same instrument gives on a clip of that length.
LONG_FORM_WINDOW_S = 180.0

# A file above this size that NEITHER backend can probe is treated as a
# possible long-form artefact, not as a short clip: ``analyze_file`` would
# otherwise take the short path silently — the pre-#21485 behaviour, with no
# signal at all (#21521 reserve 1). 1.44 MB is 180 s at 64 kbit/s mono, the
# low end for an audiobook delivery, so the threshold means "could plausibly
# exceed one window". Under it, an unreadable header is an instrument problem
# the short path already reports on its own metrics.
UNKNOWN_DURATION_WARN_BYTES = 1_440_000

# Melody verdicts, worst first. FLAT and DRONE are both reject classes
# (`classify_segment`), so they share the top rank.
MELODY_SEVERITY = {
    None: 0,
    "INSUFFICIENT": 0,
    "EXPRESSIVE": 1,
    "MODERATE": 2,
    "FLAT": 3,
    "DRONE": 3,
}


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

    ``n_syllables`` is a TOTAL, not a density: on the long-form path it is
    the sum over windows (``aggregate_window_measurements``), on the short
    path one clip's count. The name is kept short for the consumers that
    already read it (#21521 reserve 2) — the contract lives here, at the
    point of consumption: compare it to ``MIN_SYLLABLES`` only, never against
    a per-window count, and never as syllables per second.

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


def aggregate_window_measurements(windows: List[Dict[str, object]]) -> Dict[str, object]:
    """Fold per-window measurements into the one set the gate policy reads.

    Pure — no audio, no I/O, unit-testable. The rules are the conservative
    direction (a floor may only get stricter as the material grows):

    * ``melody_verdict`` — the WORST window verdict. A window that is FLAT or
      DRONE rejects the artefact, wherever it sits.
    * ``melodic_span_st`` / ``mean_abs_interval_st`` — the MAXIMUM over the
      windows: an over-modulated window must not be hidden by a calm one.
    * ``global_range_st`` — the MINIMUM over the windows: the narrowest global
      range is the one that can trip the monotone floor, and the whole-file
      value only grows with the material.
    * ``n_syllables`` — the sum, so the "too short to read" abstention cannot
      fire on an artefact that is long in total.

    ``worst_window`` is returned alongside: the window the concentration
    metrics (``effective_notes``, ``motif3_repeat_pct``, ...) are read from.
    Its tie-break is lexicographic ``(severity, motif3, span)``, so at equal
    verdict the *most concentrated* window wins — a very wide but low-motif
    window is never the one reported (the choice is about where concentration
    is read, not about which window is worst on every axis). The widest span
    is therefore not carried by ``worst_window``; ``widest_window`` names the
    window it came from, next to the ``melodic_span_st`` maximum that already
    feeds the gate (#21521 reserve 3).
    """
    if not windows:
        return {
            "melody_verdict": None,
            "melodic_span_st": None,
            "mean_abs_interval_st": None,
            "global_range_st": None,
            "n_syllables": 0,
            "worst_window": None,
            "widest_window": None,
        }

    def _rank(w: Dict[str, object]) -> tuple:
        return (
            MELODY_SEVERITY.get(w.get("melody_verdict"), 0),
            w.get("motif3_repeat_pct") or 0.0,
            w.get("melodic_span_st") or 0.0,
        )

    worst = max(windows, key=_rank)
    widest = max(windows, key=lambda w: w.get("melodic_span_st") or 0.0)

    def _collect(key: str) -> List[float]:
        return [w[key] for w in windows
                if isinstance(w.get(key), (int, float))]

    spans = _collect("melodic_span_st")
    motions = _collect("mean_abs_interval_st")
    ranges = _collect("global_range_st")

    return {
        "melody_verdict": worst.get("melody_verdict"),
        "melodic_span_st": max(spans) if spans else None,
        "mean_abs_interval_st": max(motions) if motions else None,
        "global_range_st": min(ranges) if ranges else None,
        "n_syllables": sum(w.get("n_syllables") or 0 for w in windows),
        "worst_window": worst,
        "widest_window": widest,
    }


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


# ---------------------------------------------------------------------------
# Long-form artefacts — gate a chapter in windows, not in one gulp.
# ---------------------------------------------------------------------------

def _probe_duration_s(path: str) -> Optional[float]:
    """Duration of *path* in seconds, or None when it cannot be probed.

    Cheap first (header only), then the lab's own loader (which has the
    pydub/ffmpeg fallback for mp3 without a libsndfile mp3 build) so an mp3
    delivery is not silently treated as a short segment.
    """
    try:
        import soundfile as sf
        info = sf.info(str(path))
        if info.samplerate and info.frames:
            return float(info.frames) / float(info.samplerate)
    except Exception:
        pass
    try:
        from pydub import AudioSegment
        seg = AudioSegment.from_file(str(path))
        if seg.frame_rate:
            return len(seg) / float(seg.frame_rate)
    except Exception:
        pass
    return None


def _window_audio_files(path: str, window_s: float, tmp_dir: str) -> List[str]:
    """Split *path* into fixed-length windows; return the written file paths.

    The audio is read once through the lab's own loader (resampled to the
    lab's rate, so the windows are exactly what the instruments would have
    read) and each window is written as a wav the short-segment path can
    analyse unchanged.
    """
    import soundfile as sf
    from prosody_metrics import load_audio

    y, sr = load_audio(str(path))
    if not sr:
        return []
    step = max(1, int(window_s * sr))
    out: List[str] = []
    for i, start in enumerate(range(0, len(y), step)):
        chunk = y[start:start + step]
        if chunk.size == 0:
            continue
        p = Path(tmp_dir) / ("w%02d.wav" % i)
        sf.write(str(p), chunk, sr)
        out.append(str(p))
    return out


def analyze_long_form(
    path: str,
    instruments,
    window_s: float = LONG_FORM_WINDOW_S,
) -> Dict[str, object]:
    """Gate a long artefact in fixed-length windows, then fold the windows.

    Each window goes through the unchanged short-segment path, so a window's
    verdict is exactly what the instrument gives on a clip of that length —
    which is what makes the verdict independent of how the caller chose to
    cut the material.

    The breath/voice reading is taken on the WHOLE file, not per window:
    essoufflement and voice identity are measured over the whole signal, and
    windowing them would hide a voice swap between two halves of a chapter
    (and would answer no question about endurance over the duration, which is
    the first question a long listening raises).

    The fold is the conservative one: the worst melody verdict wins, the
    widest span and fastest motion win, the narrowest global range wins.
    """
    import tempfile

    analyze_syllables, compute_metrics, analyze_spectral = instruments

    with tempfile.TemporaryDirectory(prefix="prosody_windows_") as tmp:
        window_paths = _window_audio_files(path, window_s, tmp)
        windows: List[Dict[str, object]] = []
        for i, wp in enumerate(window_paths):
            r = analyze_segment(wp, instruments)
            r["label"] = "w%02d" % i
            windows.append(r)

    if not windows:
        return analyze_segment(path, instruments)

    # Whole-file spectral reading: endurance + voice identity over the duration.
    spec = analyze_spectral(path)
    spec.pop("_plot", None)
    duration_s = spec.get("duration_s")
    breath_verdict = spec.get("breath_verdict")
    voice_verdict = spec.get("voice_verdict")
    decay_db = spec.get("decay_db")

    agg = aggregate_window_measurements(windows)
    worst = agg["worst_window"] or {}

    decision = classify_segment(
        melody_verdict=agg["melody_verdict"],
        global_range_st=agg["global_range_st"],
        breath_verdict=breath_verdict,
        voice_verdict=voice_verdict,
        n_syllables=agg["n_syllables"],
        melodic_span_st=agg["melodic_span_st"],
        mean_abs_interval_st=agg["mean_abs_interval_st"],
        breath_trusted=duration_s is None or duration_s >= DECAY_MIN_DURATION_S,
    )

    counts: Dict[str, int] = {}
    for w in windows:
        counts[str(w.get("gate"))] = counts.get(str(w.get("gate")), 0) + 1

    return {
        "label": Path(path).stem,
        "path": Path(path).name,
        "duration_s": duration_s,
        "gate": decision["gate"],
        "reasons": decision["reasons"],
        "reason_kinds": decision["reason_kinds"],
        "erratic_axes": decision["erratic_axes"],
        "melody_verdict": agg["melody_verdict"],
        "drone_reasons": worst.get("drone_reasons", []),
        "effective_notes": worst.get("effective_notes"),
        "top3_note_pct": worst.get("top3_note_pct"),
        "motif3_repeat_pct": worst.get("motif3_repeat_pct"),
        "melodic_span_p5p95_st": worst.get("melodic_span_p5p95_st"),
        # SUM over the windows, not a per-window density (#21521 reserve 2).
        "n_syllables": agg["n_syllables"],
        "melodic_span_st": agg["melodic_span_st"],
        "mean_abs_interval_st": agg["mean_abs_interval_st"],
        "pct_flat_transitions": worst.get("pct_flat_transitions"),
        "global_range_st": agg["global_range_st"],
        "breath_verdict": spec.get("breath_verdict"),
        "breath_verdict_effective": breath_verdict,
        "decay_db": decay_db,
        "decay_trusted": duration_s is None or duration_s >= DECAY_MIN_DURATION_S,
        "max_voiced_run_s": spec.get("max_voiced_run_s"),
        "voice_verdict": voice_verdict,
        "n_voice_clusters": spec.get("n_voice_clusters"),
        "long_form": True,
        "window_s": window_s,
        "n_windows": len(windows),
        "window_counts": counts,
        "widest_window": {
            "label": (agg["widest_window"] or {}).get("label"),
            "melodic_span_st": (agg["widest_window"] or {}).get("melodic_span_st"),
        },
        "windows": [
            {
                "label": w.get("label"),
                "gate": w.get("gate"),
                "reasons": w.get("reasons"),
                "melody_verdict": w.get("melody_verdict"),
                "motif3_repeat_pct": w.get("motif3_repeat_pct"),
                "melodic_span_st": w.get("melodic_span_st"),
                "mean_abs_interval_st": w.get("mean_abs_interval_st"),
                "n_syllables": w.get("n_syllables"),
            }
            for w in windows
        ],
    }


def analyze_file(
    path: str,
    instruments,
    window_s: float = LONG_FORM_WINDOW_S,
) -> Dict[str, object]:
    """Gate *path*: the short-segment path, or the windowed path if it is long.

    The dispatch is by DURATION, not by a flag: a caller that hands a whole
    chapter to the gate gets the windowed reading whether it meant to or not
    (#21485 — the defect was that the gate measured the aggregation).
    """
    duration = _probe_duration_s(path)
    if duration is not None and duration > window_s:
        return analyze_long_form(path, instruments, window_s=window_s)
    result = analyze_segment(path, instruments)
    if duration is None:
        # Neither backend could probe the header. On a file large enough to be
        # several windows, falling through to the short path is exactly the
        # #21485 defect with no signal (#21521 reserve 1): say so, and never
        # let it read as PASS-TO-EAR. A REJECT still wins; an INCONCLUSIVE
        # (nothing measured) stays INCONCLUSIVE.
        try:
            size_bytes = os.path.getsize(path)
        except OSError:
            size_bytes = 0
        result["duration_unknown"] = True
        result["size_bytes"] = size_bytes
        if size_bytes >= UNKNOWN_DURATION_WARN_BYTES and result.get("gate") == "PASS-TO-EAR":
            result["gate"] = "WARN"
            result["reasons"] = list(result.get("reasons") or []) + ["LONG-FORM-UNVERIFIED"]
            result["reason_kinds"] = list(result.get("reason_kinds") or []) + ["finding"]
    return result


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
    ap.add_argument("--window-s", type=float, default=LONG_FORM_WINDOW_S,
                    help="window length for a long-form artefact (default %(default)s s)")
    args = ap.parse_args()

    if args.single:
        instruments = _import_instruments(Path(args.lab_dir) if args.lab_dir else _default_lab_dir())
        r = analyze_file(args.single, instruments, window_s=args.window_s)
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
