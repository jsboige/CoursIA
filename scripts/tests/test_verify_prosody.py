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


# --- #11719: FADING class characterization vs DRONE / PASS-TO-EAR ----------

def test_fading_class_distinct_from_drone():
    """#11719 acceptance (a): the FADING WARN class is a distinct pathology
    from DRONE (a melody that repeats) and from STEADY (a clean voice).

    A DRONE segment has an oscillating/repeating melody — its breath plot
    can be STEADY; the singer holds notes without panting. A FADING segment
    has a real melody that decays in ENERGY (decay_db <= -2.5 dB on the
    last third compared to the first) without a long un-paused run.

    The 3-voix scenario from #11719 (A=DRONE/B=FADING/L2=PASS) must
    classify as 3 distinct gates: REJECT, WARN, PASS-TO-EAR — and the
    FADING gate must NOT be REJECT (an FADING in DRONE is a class
    confusion the detector would surface as 'DRONE inside FADING', which
    is impossible by construction).
    """
    a_drone = _healthy(melody_verdict="DRONE", breath_verdict="STEADY")
    b_fading = _healthy(melody_verdict="MODERATE", breath_verdict="FADING")
    l2_pass = _healthy(melody_verdict="MODERATE", breath_verdict="STEADY")

    r_a = classify_segment(**a_drone)
    r_b = classify_segment(**b_fading)
    r_l2 = classify_segment(**l2_pass)

    assert r_a["gate"] == "REJECT", "DRONE melody must REJECT (MONOTONE)."
    assert "MONOTONE" in r_a["reasons"]
    assert r_b["gate"] == "WARN", (
        "FADING breath alone is WARN (informational, not REJECT)."
    )
    assert "FADING" in r_b["reasons"]
    assert r_l2["gate"] == "PASS-TO-EAR", (
        "STEADY breath + MODERATE melody clears the floor."
    )

    # Class confusion guard: FADING must NEVER ride alongside a DRONE
    # melody — a single segment cannot have a repeating chant AND a
    # steady energy decay (the energy of the chant would be flat).
    # If a downstream regression ever produces this combo, the gate
    # must still REJECT (DRONE > FADING priority).
    combo = _healthy(melody_verdict="DRONE", breath_verdict="FADING")
    r_combo = classify_segment(**combo)
    assert r_combo["gate"] == "REJECT"
    assert "MONOTONE" in r_combo["reasons"]
    assert "FADING" in r_combo["reasons"], (
        "FADING reason must be reported on the combo even when DRONE "
        "wins the gate — the report lists every reason, not only winners."
    )


def test_fading_severity_below_winded_floor_stays_warn():
    """#11719 acceptance (c)-flavored robustness: a segment that crosses
    the WINDED threshold (decay_db <= -4.0) but does NOT qualify for
    WINDED (max_run < 7s) must remain WARN/FADING, not silently
    upgraded to REJECT/WINDED by the gate.

    The detector (spectral_envelope.py:142) is the only place where
    WINDED is decided; this gate only reads the verdict string. So the
    invariant under test is: the gate trusts the detector's three-way
    call (STEADY / FADING / WINDED) and never infers WINDED from the
    decay_db value — that would couple the gate to the floor constants
    and break the moment they change."""
    # FADING breath verdict; the melody is fine. The detector is the
    # source of truth for the WINDED upgrade.
    r = classify_segment(**_healthy(breath_verdict="FADING"))
    assert r["gate"] == "WARN"
    assert "FADING" in r["reasons"]
    assert "WINDED" not in r["reasons"], (
        "Gate must NOT promote FADING to WINDED on its own — the "
        "detector owns that decision."
    )


def test_fading_alone_in_report_no_double_count():
    """#11719 acceptance (d): a single FADING reason is reported exactly
    once; the report doesn't duplicate FADING across reason buckets.

    The gate has only two reason buckets (reject, warn); FADING goes
    in warn. The test asserts that even if the caller passes the same
    breath_verdict via different code paths, the reasons list stays
    clean.
    """
    r = classify_segment(**_healthy(breath_verdict="FADING"))
    fading_count = sum(1 for reason in r["reasons"] if reason == "FADING")
    assert fading_count == 1, f"FADING reported {fading_count} times, expected 1."


def test_reject_beats_warn():
    # a WARN signal present alongside a REJECT signal -> overall REJECT
    r = classify_segment(**_healthy(melody_verdict="FLAT", breath_verdict="FADING"))
    assert r["gate"] == "REJECT"
    assert "MONOTONE" in r["reasons"]


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
