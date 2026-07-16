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


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
