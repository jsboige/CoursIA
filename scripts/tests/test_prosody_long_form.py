"""Tests for the long-form reading of scripts/tts_verification/verify_prosody.py.

Issue #21485: the prosody floor was applied to a whole audiobook chapter and
returned REJECT on material that the same instrument, applied to the windows
a listener actually hears, passes. The cause is in the METRIC, not in the
take: `motif3_repeat_pct` counts the positions whose 3-note motif occurs at
least twice *anywhere in the sequence*, so it saturates as the sequence grows
(#21485: 85.2% on the 1365-s chapter against 44.3-49.7% on its 170-s windows
-- the same audio, and the 60% drone threshold crossed by duration alone).

What is locked here:
* the metric's length-dependence, reproduced DETERMINISTICALLY on a synthetic
  note series (no audio, no librosa) -- the regression that must not come
  back;
* the fold the organ applies to the windows, on the real measured windows of
  the chapter-1 delivery (frozen values) and on synthetic ones;
* the fact that the fold keeps the whole-file breath/voice reading, so a voice
  swap between two halves of a chapter still rejects.

No audio, no librosa: this runs in plain CI, like test_verify_prosody.py.
"""

import random
import sys
from pathlib import Path

# Same sibling convention as test_verify_prosody.py: insert the tool dir and
# import the module directly.
REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts" / "tts_verification"))
# The metric lives in the prosody lab; melody_stats() is pure (no audio).
sys.path.insert(0, str(REPO / "MyIA.AI.Notebooks" / "GenAI" / "Audio"
                       / "04-Applications" / "v4" / "prosody_lab"))

import syllable_pitch as sp  # noqa: E402
from verify_prosody import (  # noqa: E402
    LONG_FORM_WINDOW_S,
    MELODY_SEVERITY,
    _plan_window_bounds,
    aggregate_window_measurements,
    classify_segment,
)

# A bounded 11-note alphabet, like a narration melody: enough variety to be
# EXPRESSIVE, few enough notes for the repertoire to saturate on a long
# sequence -- which is the whole point of the test.
ALPHABET = ["C4", "D4", "E4", "F4", "G4", "A4", "B4", "C5", "D5", "E5", "F5"]
LONG_N = 3700
WINDOW_N = 460


def _series(n: int, seed: int = 42):
    rng = random.Random(seed)
    return [rng.choice(ALPHABET) for _ in range(n)]


# --- the defect, reproduced deterministically ------------------------------

def test_motif3_saturates_with_the_length_of_the_sequence():
    """The same material, read long, trips the drone floor; read short, it does not.

    This is the measurement that opened #21485, on a synthetic series so it is
    reproducible without an audio file.
    """
    notes = _series(LONG_N)
    short = sp.melody_stats(notes[:WINDOW_N])
    long = sp.melody_stats(notes)
    assert short["motif3_repeat_pct"] < sp.MOTIF3_DRONE_MIN
    assert long["motif3_repeat_pct"] >= sp.MOTIF3_DRONE_MIN


def test_every_window_of_the_long_series_stays_below_the_drone_floor():
    notes = _series(LONG_N)
    for start in range(0, LONG_N - WINDOW_N + 1, WINDOW_N):
        st = sp.melody_stats(notes[start:start + WINDOW_N])
        assert st["motif3_repeat_pct"] < sp.MOTIF3_DRONE_MIN


def test_the_windowed_reading_of_the_long_series_is_not_a_drone():
    """The organ's fold over the windows must not reproduce the whole-file verdict."""
    notes = _series(LONG_N)
    windows = []
    for start in range(0, LONG_N - WINDOW_N + 1, WINDOW_N):
        st = sp.melody_stats(notes[start:start + WINDOW_N])
        windows.append({
            "melody_verdict": sp.classify_melody(
                1.5, 30.0, st["effective_notes"], st["top3_note_pct"],
                st["motif3_repeat_pct"])["verdict"],
            "motif3_repeat_pct": st["motif3_repeat_pct"],
            "melodic_span_st": 8.0,
            "mean_abs_interval_st": 1.5,
            "global_range_st": 10.0,
            "n_syllables": WINDOW_N,
        })
    agg = aggregate_window_measurements(windows)
    assert agg["melody_verdict"] != "DRONE"
    assert agg["n_syllables"] == len(windows) * WINDOW_N


# --- the fold, on synthetic windows ---------------------------------------

def _window(**over):
    base = dict(
        label="w00",
        gate="PASS-TO-EAR",
        reasons=[],
        reason_kinds=[],
        erratic_axes=[],
        melody_verdict="EXPRESSIVE",
        drone_reasons=[],
        effective_notes=11.0,
        top3_note_pct=46.0,
        motif3_repeat_pct=45.0,
        melodic_span_st=16.0,
        mean_abs_interval_st=2.4,
        pct_flat_transitions=30.0,
        global_range_st=10.2,
        n_syllables=460,
    )
    base.update(over)
    return base


def test_empty_windows_are_safe():
    agg = aggregate_window_measurements([])
    assert agg["melody_verdict"] is None
    assert agg["n_syllables"] == 0
    assert agg["worst_window"] is None


def test_the_worst_melody_verdict_wins():
    agg = aggregate_window_measurements([
        _window(melody_verdict="EXPRESSIVE"),
        _window(melody_verdict="DRONE"),
        _window(melody_verdict="MODERATE"),
    ])
    assert agg["melody_verdict"] == "DRONE"


def test_a_flat_window_wins_over_an_expressive_one():
    agg = aggregate_window_measurements([
        _window(melody_verdict="FLAT"),
        _window(melody_verdict="EXPRESSIVE"),
    ])
    assert agg["melody_verdict"] == "FLAT"


def test_the_widest_span_wins_so_an_over_modulated_window_is_not_hidden():
    agg = aggregate_window_measurements([
        _window(melodic_span_st=12.0),
        _window(melodic_span_st=19.0),
        _window(melodic_span_st=15.0),
    ])
    assert agg["melodic_span_st"] == 19.0


def test_the_fastest_motion_wins_so_an_erratic_window_is_not_hidden():
    agg = aggregate_window_measurements([
        _window(mean_abs_interval_st=1.2),
        _window(mean_abs_interval_st=2.7),
    ])
    assert agg["mean_abs_interval_st"] == 2.7


def test_the_narrowest_global_range_wins():
    agg = aggregate_window_measurements([
        _window(global_range_st=10.4),
        _window(global_range_st=3.1),
        _window(global_range_st=8.0),
    ])
    assert agg["global_range_st"] == 3.1


def test_the_syllables_are_summed_so_a_long_artefact_never_reads_as_too_short():
    agg = aggregate_window_measurements([_window(n_syllables=460)] * 8)
    assert agg["n_syllables"] == 8 * 460


def test_among_windows_of_equal_verdict_the_more_concentrated_one_is_the_worst():
    agg = aggregate_window_measurements([
        _window(motif3_repeat_pct=30.0),
        _window(motif3_repeat_pct=58.0),
    ])
    assert agg["worst_window"]["motif3_repeat_pct"] == 58.0


# --- the fold, on the MEASURED windows of the chapter-1 delivery ------------
# Frozen values, measured 2026-10-19 by this lane on the delivered chapter
# (voice B, 1364.96 s). PROVENANCE of the cut (#21521 item 4): these values
# were measured on an EQUAL 8-window cut (8 x 170.67 s) -- a measurement
# cut, NOT the one the organ makes. The organ's fixed cut for that duration
# is 7 x 180 s + a 104.96-s queue (the queue is >= window/2, so #21521's
# guard keeps it as its own window: also 8 windows, not the same ones). The
# values are frozen as the data that opened #21485, locking the FOLD against
# the real case; the organ's real cut is locked by the _plan_window_bounds
# tests below, not by this table.

MEASURED_WINDOWS = [
    {"label": "w00", "gate": "PASS-TO-EAR", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 49.7, "melodic_span_st": 15.6, "mean_abs_interval_st": 2.42,
     "global_range_st": 10.2, "n_syllables": 465, "effective_notes": 10.4,
     "pct_flat_transitions": 32.3},
    {"label": "w01", "gate": "PASS-TO-EAR", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 44.3, "melodic_span_st": 16.0, "mean_abs_interval_st": 2.45,
     "global_range_st": 10.3, "n_syllables": 462, "effective_notes": 11.0,
     "pct_flat_transitions": 29.7},
    {"label": "w02", "gate": "PASS-TO-EAR", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 46.6, "melodic_span_st": 17.35, "mean_abs_interval_st": 2.47,
     "global_range_st": 10.16, "n_syllables": 457, "effective_notes": 10.9,
     "pct_flat_transitions": 30.5},
    {"label": "w03", "gate": "WARN", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 46.7, "melodic_span_st": 16.4, "mean_abs_interval_st": 2.5,
     "global_range_st": 10.34, "n_syllables": 462, "effective_notes": 10.7,
     "pct_flat_transitions": 30.8},
    {"label": "w04", "gate": "WARN", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 45.2, "melodic_span_st": 15.27, "mean_abs_interval_st": 2.52,
     "global_range_st": 10.2, "n_syllables": 460, "effective_notes": 10.7,
     "pct_flat_transitions": 31.8},
    {"label": "w05", "gate": "WARN", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 45.0, "melodic_span_st": 16.3, "mean_abs_interval_st": 2.51,
     "global_range_st": 10.45, "n_syllables": 451, "effective_notes": 11.2,
     "pct_flat_transitions": 30.7},
    {"label": "w06", "gate": "WARN", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 44.5, "melodic_span_st": 16.4, "mean_abs_interval_st": 2.51,
     "global_range_st": 10.4, "n_syllables": 483, "effective_notes": 11.2,
     "pct_flat_transitions": 28.8},
    {"label": "w07", "gate": "PASS-TO-EAR", "melody_verdict": "EXPRESSIVE",
     "motif3_repeat_pct": 48.5, "melodic_span_st": 15.0, "mean_abs_interval_st": 2.46,
     "global_range_st": 10.19, "n_syllables": 464, "effective_notes": 11.0,
     "pct_flat_transitions": 30.9},
]

# The same file, read in one gulp: the measurement that the windowing removes.
MEASURED_WHOLE_FILE = {
    "gate": "REJECT",
    "melody_verdict": "DRONE",
    "motif3_repeat_pct": 85.2,
    "melodic_span_st": 18.6,
    "mean_abs_interval_st": 2.48,
    "global_range_st": 10.3,
    "n_syllables": 3700,
    "breath_verdict": "STEADY",
    "voice_verdict": "CONSISTENT",
}


def test_the_measured_windows_fold_to_the_expected_aggregates():
    agg = aggregate_window_measurements(MEASURED_WINDOWS)
    assert agg["melody_verdict"] == "EXPRESSIVE"
    assert agg["melodic_span_st"] == 17.35
    assert agg["mean_abs_interval_st"] == 2.52
    assert agg["global_range_st"] == 10.16
    assert agg["n_syllables"] == 3704


def test_the_measured_chapter_warns_through_the_fold_and_rejects_without_it():
    """The whole point of #21485, on the real data: same audio, two readings."""
    agg = aggregate_window_measurements(MEASURED_WINDOWS)
    folded = classify_segment(
        melody_verdict=agg["melody_verdict"],
        global_range_st=agg["global_range_st"],
        breath_verdict=MEASURED_WHOLE_FILE["breath_verdict"],
        voice_verdict=MEASURED_WHOLE_FILE["voice_verdict"],
        n_syllables=agg["n_syllables"],
        melodic_span_st=agg["melodic_span_st"],
        mean_abs_interval_st=agg["mean_abs_interval_st"],
    )
    assert folded["gate"] == "WARN"
    assert folded["reasons"] == ["ERRATIC"]
    assert folded["erratic_axes"] == ["motion"]

    whole = classify_segment(
        melody_verdict=MEASURED_WHOLE_FILE["melody_verdict"],
        global_range_st=MEASURED_WHOLE_FILE["global_range_st"],
        breath_verdict=MEASURED_WHOLE_FILE["breath_verdict"],
        voice_verdict=MEASURED_WHOLE_FILE["voice_verdict"],
        n_syllables=MEASURED_WHOLE_FILE["n_syllables"],
        melodic_span_st=MEASURED_WHOLE_FILE["melodic_span_st"],
        mean_abs_interval_st=MEASURED_WHOLE_FILE["mean_abs_interval_st"],
    )
    assert whole["gate"] == "REJECT"
    assert "MONOTONE" in whole["reasons"]


def test_a_voice_swap_on_the_whole_file_still_rejects_a_clean_window_set():
    """Windowing must not hide a voice swap between two halves of a chapter."""
    agg = aggregate_window_measurements(MEASURED_WINDOWS)
    decision = classify_segment(
        melody_verdict=agg["melody_verdict"],
        global_range_st=agg["global_range_st"],
        breath_verdict="STEADY",
        voice_verdict="INCONSISTENT",
        n_syllables=agg["n_syllables"],
        melodic_span_st=agg["melodic_span_st"],
        mean_abs_interval_st=agg["mean_abs_interval_st"],
    )
    assert decision["gate"] == "REJECT"
    assert "VOICE-SWAP" in decision["reasons"]


# --- the queue-window guard (#21521 item 3) ----------------------------------
# The cut, not the fold: a closing tail shorter than half a window never
# becomes a window of its own. Sample arithmetic only (sr = 100/s, so a
# second is 100 samples) -- no audio, no librosa, same CI constraint as
# the rest of this file.

_SR = 100  # samples per second, arbitrary: the plan is pure sample math


def test_a_queue_shorter_than_half_a_window_merges_into_the_previous_one():
    """7 x 180 s + a 70-s tail -> 7 windows, the last one 250 s.

    The fold takes the WORST melody verdict and the MINIMUM global range:
    a tail that short is narrow-range by construction, and read alone it
    would reject the whole chapter on the monotone floor by duration alone
    -- the false-REJECT-by-duration class #21486 retired.
    """
    step = int(LONG_FORM_WINDOW_S * _SR)
    n = 7 * step + 70 * _SR
    bounds = _plan_window_bounds(n, step)
    assert len(bounds) == 7
    assert bounds[-1] == (6 * step, n)
    # every window is at least half a window long
    assert all(end - start >= step // 2 for start, end in bounds)


def test_a_queue_at_least_half_a_window_stays_its_own_window():
    """The chapter-1 case: 7 x 180 s + a 104.96-s queue -> 8 windows.

    The queue is >= window/2 (104.96 >= 90), long enough to carry a
    reading of its own: it is NOT merged.
    """
    step = int(LONG_FORM_WINDOW_S * _SR)
    queue = int(104.96 * _SR)
    n = 7 * step + queue
    bounds = _plan_window_bounds(n, step)
    assert len(bounds) == 8
    assert bounds[-1][1] - bounds[-1][0] == queue


def test_a_short_artefact_is_one_window_whatever_its_length():
    """Under one window there is nothing to merge into: single window as-is."""
    step = int(LONG_FORM_WINDOW_S * _SR)
    assert _plan_window_bounds(step // 4, step) == [(0, step // 4)]
    assert _plan_window_bounds(step, step) == [(0, step)]
    assert _plan_window_bounds(0, step) == []


def test_why_the_guard_lives_in_the_cut_and_not_in_the_fold():
    """The defect on window dicts: a short narrow tail read FLAT drags the
    fold to a chapter-wide REJECT.

    Locked here so the next reader sees what the plan guarantees can never
    be produced: with the pre-#21521 cut, a 7-window chapter plus a 10-s
    tail (2.1-st range -- narrow BY CONSTRUCTION, not by performance)
    folds to FLAT + a 2.1-st global range, and the gate rejects the whole
    chapter on MONOTONE. The plan tests above are what prevents this
    window set from ever existing.
    """
    tail = _window(label="w07", melody_verdict="FLAT",
                   global_range_st=2.1, n_syllables=40,
                   motif3_repeat_pct=60.0)
    windows = [_window(label="w0%d" % i) for i in range(7)] + [tail]
    agg = aggregate_window_measurements(windows)
    assert agg["melody_verdict"] == "FLAT"
    assert agg["global_range_st"] == 2.1
    decision = classify_segment(
        melody_verdict=agg["melody_verdict"],
        global_range_st=agg["global_range_st"],
        breath_verdict="STEADY",
        voice_verdict="CONSISTENT",
        n_syllables=agg["n_syllables"],
        melodic_span_st=agg["melodic_span_st"],
        mean_abs_interval_st=agg["mean_abs_interval_st"],
    )
    assert decision["gate"] == "REJECT"
    assert "MONOTONE" in decision["reasons"]


# --- the constants the contract rests on -----------------------------------

def test_the_long_form_window_is_longer_than_the_segment_range():
    """180 s sits above the 30-130 s segments the gate was calibrated on, and
    below a chapter. If it moved into the segment range, the short readings
    would change -- which criterion 3 of #21485 forbids."""
    assert LONG_FORM_WINDOW_S >= 120.0


def test_melody_severity_ranks_flat_and_drone_as_reject_classes():
    assert MELODY_SEVERITY["FLAT"] == MELODY_SEVERITY["DRONE"]
    assert MELODY_SEVERITY["FLAT"] > MELODY_SEVERITY["MODERATE"]
    assert MELODY_SEVERITY["MODERATE"] > MELODY_SEVERITY["EXPRESSIVE"]
