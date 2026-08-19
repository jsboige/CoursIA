"""Tests for scripts/tts_verification/verify_prosody.py — stage-3 prosody gate.

Locks the gate decision policy (``classify_segment``) which is pure logic over the
three prosody instruments' verdicts — no audio, no librosa, so it runs in plain CI.
The audio-facing functions (``analyze_segment``/``verify_batch``) are intentionally
NOT exercised here: they require librosa + real clips, covered by the manual run on
the #1028 review material, not by unit CI.

Policy under test:
* REJECT wins over WARN wins over PASS-TO-EAR; too-short -> INCONCLUSIVE.
* REJECT classes: MONOTONE (melody FLAT or global span < 4 st), WINDED, VOICE-SWAP.
* WARN classes: ERRATIC (over-modulated — the Kokoro-v1 class), DRIFTING, FADING.
"""

import sys
from pathlib import Path

import pytest

# Same sibling convention as test_detect_blank_figures.py: insert the tool dir and
# import the module directly.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tts_verification"))

from verify_prosody import (  # noqa: E402
    DECAY_MIN_DURATION_S,
    ERRATIC_MOTION_ST,
    ERRATIC_SPAN_ST,
    GLOBAL_FLAT_ST,
    MIN_SYLLABLES,
    classify_segment,
)


def _healthy(**over):
    """A segment that clears the floor by default; override one field per test."""
    base = dict(
        melody_verdict="MODERATE",
        global_range_st=7.0,
        breath_verdict="STEADY",
        voice_verdict="CONSISTENT",
        n_syllables=12,
        melodic_span_st=8.0,
        mean_abs_interval_st=1.3,
    )
    base.update(over)
    return base


# --- PASS-TO-EAR -----------------------------------------------------------

def test_healthy_segment_passes_to_ear():
    r = classify_segment(**_healthy())
    assert r["gate"] == "PASS-TO-EAR"
    assert r["reasons"] == []


def test_expressive_within_bounds_passes():
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE", melodic_span_st=11.0,
                                    mean_abs_interval_st=1.9))
    assert r["gate"] == "PASS-TO-EAR"


# --- INCONCLUSIVE (abstain) ------------------------------------------------

def test_too_few_syllables_is_inconclusive():
    r = classify_segment(**_healthy(n_syllables=MIN_SYLLABLES - 1))
    assert r["gate"] == "INCONCLUSIVE"
    assert "TOO-SHORT" in r["reasons"]


def test_insufficient_melody_verdict_is_inconclusive():
    r = classify_segment(**_healthy(melody_verdict="INSUFFICIENT", n_syllables=2))
    assert r["gate"] == "INCONCLUSIVE"


def test_none_melody_verdict_is_inconclusive():
    r = classify_segment(**_healthy(melody_verdict=None, n_syllables=1))
    assert r["gate"] == "INCONCLUSIVE"


# --- REJECT: MONOTONE ------------------------------------------------------

def test_flat_melody_rejects_monotone():
    r = classify_segment(**_healthy(melody_verdict="FLAT"))
    assert r["gate"] == "REJECT"
    assert "MONOTONE" in r["reasons"]


def test_low_global_range_alone_only_warns():
    # global span < floor but syllable verdict not FLAT: robust signal disagrees ->
    # WARN (borderline, send to ear), never REJECT on the noisy short-clip global.
    r = classify_segment(**_healthy(global_range_st=GLOBAL_FLAT_ST - 0.5))
    assert r["gate"] == "WARN"
    assert "GLOBAL-FLAT" in r["reasons"]


def test_low_global_range_with_flat_syllable_rejects():
    # both melody instruments agree flat -> confident MONOTONE reject
    r = classify_segment(**_healthy(melody_verdict="FLAT", global_range_st=GLOBAL_FLAT_ST - 0.5))
    assert r["gate"] == "REJECT"
    assert "MONOTONE" in r["reasons"]


def test_global_range_at_floor_is_not_flat():
    # boundary: exactly the floor is not below it
    r = classify_segment(**_healthy(global_range_st=GLOBAL_FLAT_ST))
    assert r["gate"] == "PASS-TO-EAR"


# --- REJECT: WINDED / VOICE-SWAP -------------------------------------------

def test_winded_breath_rejects():
    r = classify_segment(**_healthy(breath_verdict="WINDED"))
    assert r["gate"] == "REJECT"
    assert "WINDED" in r["reasons"]


def test_inconsistent_voice_rejects_swap():
    r = classify_segment(**_healthy(voice_verdict="INCONSISTENT"))
    assert r["gate"] == "REJECT"
    assert "VOICE-SWAP" in r["reasons"]


def test_multiple_reject_reasons_accumulate():
    r = classify_segment(**_healthy(melody_verdict="FLAT", breath_verdict="WINDED",
                                    voice_verdict="INCONSISTENT"))
    assert r["gate"] == "REJECT"
    assert {"MONOTONE", "WINDED", "VOICE-SWAP"} <= set(r["reasons"])


# --- WARN: ERRATIC (the Kokoro-v1 over-modulation class) -------------------

def test_erratic_span_warns():
    # span >= ERRATIC_SPAN_ST but not flat/winded/swap -> WARN, not REJECT
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    melodic_span_st=ERRATIC_SPAN_ST + 5,
                                    mean_abs_interval_st=1.5))
    assert r["gate"] == "WARN"
    assert "ERRATIC" in r["reasons"]


def test_erratic_motion_warns():
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    melodic_span_st=12.0,
                                    mean_abs_interval_st=ERRATIC_MOTION_ST + 0.5))
    assert r["gate"] == "WARN"
    assert "ERRATIC" in r["reasons"]


def test_kokoro_v1_ground_truth_is_warn_not_pass():
    """The invalidated Kokoro Boule-de-Suif v1: EXPRESSIVE by metric (span 33.6 st,
    motion 3.43 st/syll) yet ear-bad. The gate must NOT pass it silently."""
    r = classify_segment(melody_verdict="EXPRESSIVE", global_range_st=20.0,
                          breath_verdict="STEADY", voice_verdict="CONSISTENT",
                          n_syllables=119, melodic_span_st=33.6,
                          mean_abs_interval_st=3.43)
    assert r["gate"] == "WARN"
    assert "ERRATIC" in r["reasons"]


# --- erratic_axes: which axis fired, and "not measured" != "nothing fired" --

def test_erratic_axes_names_the_span_axis():
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    melodic_span_st=ERRATIC_SPAN_ST + 2,
                                    mean_abs_interval_st=1.5))
    assert r["erratic_axes"] == ["span"]


def test_erratic_axes_names_the_motion_axis():
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    melodic_span_st=12.0,
                                    mean_abs_interval_st=ERRATIC_MOTION_ST + 0.5))
    assert r["erratic_axes"] == ["motion"]


def test_erratic_axes_names_both_when_both_fire():
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    melodic_span_st=ERRATIC_SPAN_ST + 2,
                                    mean_abs_interval_st=ERRATIC_MOTION_ST + 0.5))
    assert r["erratic_axes"] == ["span", "motion"]


def test_erratic_axes_empty_when_measured_and_nothing_fired():
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    melodic_span_st=11.3,
                                    mean_abs_interval_st=1.85))
    assert r["gate"] == "PASS-TO-EAR"
    assert r["erratic_axes"] == []


def test_erratic_axes_is_none_when_the_segment_was_never_evaluated():
    """The invariant: too short -> the axes were not measured, and that must not
    be spelled the same way as "measured, nothing fired" ([]). Same separation
    syllable_pitch.classify_melody already makes for the structural axis."""
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    n_syllables=MIN_SYLLABLES - 1,
                                    melodic_span_st=40.0,
                                    mean_abs_interval_st=5.0))
    assert r["gate"] == "INCONCLUSIVE"
    assert r["erratic_axes"] is None


def test_erratic_does_not_discriminate_on_the_cloning_route():
    """Regression on a *reading*, not on a threshold.

    Measured on the seven #1028 review clips (2026-08-18): every clip carrying
    ERRATIC is one of the good EXPRESSIVE takes, and none of the three DRONE
    takes carries it. A reviewer consumed the bare label as a reservation about
    one take; it is an abstention that tracks melodic richness on this route.
    Pinned here so the reading cannot be re-made silently.
    """
    # (clip, span_st, motion_st, melody verdict) -- firsthand measurements
    good = [("B_regenere", 20.4, 2.30), ("G1_melodique", 15.9, 3.06),
            ("L3_long_melodique", 16.5, 2.94)]
    drone = [("A_servi_depuis_mai", 12.2, 1.21), ("E_plat_grave", 9.8, 1.29),
             ("F1_plat_clair", 8.9, 1.63)]

    for name, span, motion in good:
        r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                        n_syllables=80, melodic_span_st=span,
                                        mean_abs_interval_st=motion))
        # Asserted on `reasons`, which predates this change: the pin is on the
        # BEHAVIOUR (good takes carry the flag), so it holds against the module
        # as it was -- it is a guard on a future silent change, not a proof that
        # the old code was wrong.
        assert "ERRATIC" in r["reasons"], f"{name}: expected the flag on a good take"

    for name, span, motion in drone:
        r = classify_segment(**_healthy(melody_verdict="DRONE",
                                        n_syllables=80, melodic_span_st=span,
                                        mean_abs_interval_st=motion))
        assert "ERRATIC" not in r["reasons"], f"{name}: DRONE must not carry ERRATIC"
        assert r["gate"] == "REJECT"


# --- WARN: DRIFTING / FADING (informational, surface with caveat) ----------

def test_drifting_voice_warns():
    r = classify_segment(**_healthy(voice_verdict="DRIFTING"))
    assert r["gate"] == "WARN"
    assert "DRIFTING" in r["reasons"]


def test_fading_breath_warns_not_rejects():
    # FADING alone is noisy on short clips -> WARN, never REJECT (honest calibration)
    r = classify_segment(**_healthy(breath_verdict="FADING"))
    assert r["gate"] == "WARN"
    assert "FADING" in r["reasons"]


def test_reject_beats_warn():
    # a WARN signal present alongside a REJECT signal -> overall REJECT
    r = classify_segment(**_healthy(melody_verdict="FLAT", breath_verdict="FADING"))
    assert r["gate"] == "REJECT"
    assert "MONOTONE" in r["reasons"]


# --- reason_kinds: informational vs finding (c.378 self-descriptive) ------

def test_reason_kinds_key_present_even_when_empty():
    """The new self-descriptive axis is a list of equal length to reasons, so
    consumers can render each reason with its severity. Always present (even
    when no reason fires) — empty list is the right answer for PASS-TO-EAR."""
    r = classify_segment(**_healthy())
    assert r["gate"] == "PASS-TO-EAR"
    assert r["reasons"] == []
    assert r["reason_kinds"] == []


def test_too_short_has_informational_kind():
    """INCONCLUSIVE abstention is informational, never a finding."""
    r = classify_segment(**_healthy(n_syllables=MIN_SYLLABLES - 1))
    assert r["gate"] == "INCONCLUSIVE"
    assert r["reason_kinds"] == ["informational"]


def test_reject_reasons_are_findings():
    """MONOTONE / WINDED / VOICE-SWAP are disqualifications -> 'finding'."""
    r = classify_segment(**_healthy(melody_verdict="FLAT",
                                    breath_verdict="WINDED",
                                    voice_verdict="INCONSISTENT"))
    assert r["gate"] == "REJECT"
    assert r["reason_kinds"][:3] == ["finding", "finding", "finding"]


def test_fading_kind_is_informational():
    """FADING is an abstention (defer to ear), not a disqualification."""
    r = classify_segment(**_healthy(breath_verdict="FADING"))
    assert r["gate"] == "WARN"
    assert "FADING" in r["reasons"]
    idx = r["reasons"].index("FADING")
    assert r["reason_kinds"][idx] == "informational"


def test_drifting_kind_is_informational():
    """DRIFTING (mild timbre drift) is an abstention, not a disqualification."""
    r = classify_segment(**_healthy(voice_verdict="DRIFTING"))
    assert r["gate"] == "WARN"
    assert "DRIFTING" in r["reasons"]
    idx = r["reasons"].index("DRIFTING")
    assert r["reason_kinds"][idx] == "informational"


def test_global_flat_kind_is_informational():
    """GLOBAL-FLAT hedges the noisy short-clip global span — also informational."""
    r = classify_segment(**_healthy(global_range_st=GLOBAL_FLAT_ST - 0.5))
    assert r["gate"] == "WARN"
    assert "GLOBAL-FLAT" in r["reasons"]
    idx = r["reasons"].index("GLOBAL-FLAT")
    assert r["reason_kinds"][idx] == "informational"


def test_erratic_kind_is_finding():
    """ERRATIC is an over-modulation flag calibrated on a known-bad class
    (Kokoro v1). It is a disqualification-of-suspicion, not an abstention —
    the consumer should treat it as actionable (send to the ear at minimum)."""
    r = classify_segment(**_healthy(melody_verdict="EXPRESSIVE",
                                    melodic_span_st=ERRATIC_SPAN_ST + 5))
    assert r["gate"] == "WARN"
    assert "ERRATIC" in r["reasons"]
    idx = r["reasons"].index("ERRATIC")
    assert r["reason_kinds"][idx] == "finding"


def test_fading_masked_when_breath_not_trusted():
    """Short-clip guard: when breath_trusted=False, FADING is suppressed so a
    20-second clip can never be flagged FADING (the decay_db reading is noise).
    The breath_verdict passed in is preserved by the caller (analyze_segment
    rewrites it to STEADY on a short clip); the gate sees STEADY and stays
    clean. This is the unit-level mirror of the analyze_segment guard."""
    # FADING + breath_trusted=False -> not surfaced at all.
    r = classify_segment(**_healthy(breath_verdict="STEADY", breath_trusted=False))
    assert r["gate"] == "PASS-TO-EAR"
    assert "FADING" not in r["reasons"]
    # Default (breath_trusted=True) still surfaces FADING when present.
    r2 = classify_segment(**_healthy(breath_verdict="FADING", breath_trusted=True))
    assert "FADING" in r2["reasons"]


def test_winded_still_surfaces_even_on_short_clips():
    """WINDED is a confidence-finding (true breath failure) — NOT masked by
    breath_trusted=False. Only the borderline FADING abstention is masked."""
    r = classify_segment(**_healthy(breath_verdict="WINDED", breath_trusted=False))
    assert r["gate"] == "REJECT"
    assert "WINDED" in r["reasons"]


# --- DECAY_MIN_DURATION_S: length guard for the breath instrument ---------

def test_decay_min_duration_threshold_is_exported():
    """The 60-s floor is the documented threshold. Pinned here so a silent
    change to a higher/lower value cannot move without a test red."""
    from verify_prosody import DECAY_MIN_DURATION_S
    assert DECAY_MIN_DURATION_S == 60.0


# --- analyze_segment masking end-to-end (mocked instruments, no audio) ------

def test_analyze_segment_masks_decay_db_on_short_clip():
    """End-to-end mirror of the unit-level breath_trusted guard. Mock the three
    instruments (no librosa needed), feed a 32-s clip with FADING+decay_db=-4.5,
    and assert the output has decay_db=None, breath_verdict_effective='STEADY',
    and gate=PASS-TO-EAR. Same instrument on a 113-s clip preserves both.
    Pinned here so the gate, the duration guard, and the JSON output schema
    cannot drift apart silently."""
    from verify_prosody import analyze_segment, DECAY_MIN_DURATION_S

    def _stub_instruments(*, mel_overrides=None, glob_overrides=None,
                          spec_overrides=None):
        def _analyze_syllables(_path):
            base = {"verdict": "EXPRESSIVE", "n_syllables": 80,
                    "effective_notes": 12.0, "top3_note_pct": 0.32,
                    "motif3_repeat_pct": 0.18,
                    "melodic_span_p5p95_st": 11.0,
                    "melodic_span_st": 11.0, "mean_abs_interval_st": 1.4,
                    "pct_flat_transitions": 0.25, "drone_reasons": []}
            base.update(mel_overrides or {})
            return base

        def _compute_metrics(_path):
            return {"f0_semitone_range": 9.0, **(glob_overrides or {})}

        def _analyze_spectral(_path):
            base = {"breath_verdict": "FADING",
                    "decay_db": -4.5, "max_voiced_run_s": 12.0,
                    "voice_verdict": "CONSISTENT", "n_voice_clusters": 1}
            base.update(spec_overrides or {})
            return base

        return (_analyze_syllables, _compute_metrics, _analyze_spectral)

    # --- case A: short clip (32.3 s, FADING+decay_db=-4.5) ---
    short_overrides = {"duration_s": 32.3}
    inst = _stub_instruments(mel_overrides=short_overrides)
    r_short = analyze_segment("/fake/clip.mp3", inst)
    assert r_short["duration_s"] == 32.3
    assert r_short["decay_db"] is None, (
        f"expected decay_db masked on 32-s clip, got {r_short['decay_db']!r}"
    )
    assert r_short["decay_trusted"] is False
    assert r_short["breath_verdict_effective"] == "STEADY"
    assert r_short["breath_verdict"] == "FADING"  # raw reading preserved for audit
    assert r_short["gate"] == "PASS-TO-EAR", (
        f"FADING must not surface on a short clip; got gate={r_short['gate']}"
    )
    assert "FADING" not in r_short["reasons"]

    # --- case B: long clip (113.9 s, same FADING+decay_db=-4.5) ---
    long_overrides = {"duration_s": 113.9}
    inst = _stub_instruments(mel_overrides=long_overrides)
    r_long = analyze_segment("/fake/clip.mp3", inst)
    assert r_long["duration_s"] == 113.9
    assert r_long["decay_db"] == -4.5
    assert r_long["decay_trusted"] is True
    assert r_long["breath_verdict_effective"] == "FADING"
    assert r_long["gate"] == "WARN"
    assert "FADING" in r_long["reasons"]
    idx = r_long["reasons"].index("FADING")
    assert r_long["reason_kinds"][idx] == "informational"

    # --- case C: boundary, exactly at the threshold ---
    boundary_overrides = {"duration_s": DECAY_MIN_DURATION_S}
    inst = _stub_instruments(mel_overrides=boundary_overrides)
    r_boundary = analyze_segment("/fake/clip.mp3", inst)
    assert r_boundary["decay_trusted"] is True
    assert r_boundary["decay_db"] == -4.5

    # --- case D: just below the threshold ---
    below_overrides = {"duration_s": DECAY_MIN_DURATION_S - 0.1}
    inst = _stub_instruments(mel_overrides=below_overrides)
    r_below = analyze_segment("/fake/clip.mp3", inst)
    assert r_below["decay_trusted"] is False
    assert r_below["decay_db"] is None


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))


# --- DRONE: the repeating-melody class (added 2026-08-18) -------------------
# Local metrics (motion, flat-%) cannot see a melody that *repeats*: a chant
# alternating two adjacent notes has normal step size. syllable_pitch now emits
# DRONE from structural criteria (effective notes / top-3 concentration /
# repeated 3-note motifs). These tests lock it to the same REJECT class as FLAT,
# so the new verdict cannot silently fall through the gate as "not FLAT".

def test_drone_is_rejected_as_monotone():
    out = classify_segment(**_healthy(melody_verdict="DRONE"))
    assert out["gate"] == "REJECT"
    assert "MONOTONE" in out["reasons"]


def test_drone_rejected_even_with_healthy_global_span():
    """The v4 extract's own shape: global span looks fine, melody repeats."""
    out = classify_segment(**_healthy(melody_verdict="DRONE", global_range_st=12.24))
    assert out["gate"] == "REJECT"
    assert "MONOTONE" in out["reasons"]


def test_drone_does_not_also_raise_global_flat_warn():
    """GLOBAL-FLAT is the 'syllable verdict disagrees' hedge; DRONE agrees."""
    out = classify_segment(**_healthy(melody_verdict="DRONE", global_range_st=1.0))
    assert out["gate"] == "REJECT"
    assert "GLOBAL-FLAT" not in out["reasons"]


def test_moderate_still_passes_so_drone_is_not_a_blanket_reject():
    """Guard against over-correction: MODERATE must remain acceptable."""
    assert classify_segment(**_healthy(melody_verdict="MODERATE"))["gate"] == "PASS-TO-EAR"
