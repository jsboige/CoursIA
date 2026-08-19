"""Tests for prosody_lab/syllable_pitch.py — the melody verdict policy (#1028).

Locks ``classify_melody``, the pure decision layer over the two measurement axes
(no audio, no librosa, so it runs in plain CI — same separation as
``verify_prosody.classify_segment``, tested in ``test_verify_prosody.py``).

The defect these tests close
----------------------------
The structural criteria (effective notes / top-3 concentration / repeated 3-note
motifs) — the ones that actually catch a chant — need ``MIN_SYLL_FOR_STRUCTURE``
syllables before they mean anything. Below that floor they were skipped, and the
result kept the LOCAL reading (``MODERATE``) with ``drone_reasons == []``: the
exact value a clip gets when the three criteria *ran and none fired*.

"Not looked" and "nothing found" shared one return value, so a clip nobody had
assessed was indistinguishable from a clip that passed. Measured 2026-08-18 on
the five v4 character extracts in the #1028 review folder (7 to 24 syllables):
all five read ``MODERATE``, structure never computed.

``melody_stats`` had already refused that conflation one level down ("never
silently zero, which would read as clean"); the verdict layer reintroduced it.
"""

import sys
from pathlib import Path

import pytest

pytest.importorskip("numpy")  # syllable_pitch imports numpy at module level

# Same sibling convention as test_verify_prosody.py: insert the tool dir and
# import the module directly.
sys.path.insert(0, str(
    Path(__file__).resolve().parents[2]
    / "MyIA.AI.Notebooks" / "GenAI" / "Audio" / "04-Applications" / "v4" / "prosody_lab"
))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tts_verification"))

from syllable_pitch import (  # noqa: E402
    EFFNOTES_DRONE_MAX,
    MOTIF3_DRONE_MIN,
    TOP3_DRONE_MIN,
    classify_melody,
)
from verify_prosody import classify_segment  # noqa: E402

# Local-axis inputs that on their own read MODERATE (motion in [1.0, 1.6)).
MODERATE_LOCAL = dict(motion=1.3, flat_pct=30.0)
# ... and that on their own read EXPRESSIVE.
EXPRESSIVE_LOCAL = dict(motion=2.0, flat_pct=20.0)
# ... and FLAT (motion below 1.0 st/syllable).
FLAT_LOCAL = dict(motion=0.5, flat_pct=70.0)

# Structure of a healthy, varied melody: far from all three drone thresholds.
CLEAN_STRUCTURE = dict(effective_notes=11.8, top3_note_pct=44.5, motif3_repeat_pct=14.5)


# ---------------------------------------------------------------------------
# The core distinction: unassessed is not clean
# ---------------------------------------------------------------------------

def test_unassessed_structure_yields_none_not_empty_list():
    """``None`` (not looked) must never be reported as ``[]`` (looked, clean)."""
    short = classify_melody(**MODERATE_LOCAL)
    assert short["structure_assessed"] is False
    assert short["drone_reasons"] is None

    full = classify_melody(**MODERATE_LOCAL, **CLEAN_STRUCTURE)
    assert full["structure_assessed"] is True
    assert full["drone_reasons"] == []

    # The two must be distinguishable by a caller. Before the fix both were [].
    assert short["drone_reasons"] != full["drone_reasons"]


@pytest.mark.parametrize("local", [MODERATE_LOCAL, EXPRESSIVE_LOCAL])
def test_all_clear_does_not_survive_an_unassessed_structure(local):
    """MODERATE/EXPRESSIVE both read as a pass — neither may be handed back
    when the chant detector never ran."""
    r = classify_melody(**local)
    assert r["verdict"] == "INSUFFICIENT"
    # The local reading is preserved, just not promoted to a verdict.
    assert r["local_verdict"] in ("MODERATE", "EXPRESSIVE")


def test_flat_survives_an_unassessed_structure():
    """Deliberate asymmetry: FLAT is a *reject* class measured on the local axis
    alone. Abstaining there would weaken the floor on the clips it should catch."""
    r = classify_melody(**FLAT_LOCAL)
    assert r["verdict"] == "FLAT"
    assert r["structure_assessed"] is False
    assert r["drone_reasons"] is None


# ---------------------------------------------------------------------------
# Consequence at the gate: an unassessed clip must not reach PASS-TO-EAR
# ---------------------------------------------------------------------------

def test_short_clip_reaches_the_gate_as_an_abstention_not_a_pass():
    """End-to-end on the real failure mode: a 21-syllable clip clears the gate's
    own ``MIN_SYLLABLES`` floor of 4, so before the fix its ``MODERATE`` verdict
    walked straight through to PASS-TO-EAR with the chant detector never run."""
    mel = classify_melody(**MODERATE_LOCAL)  # 21 syllables -> structure absent
    gate = classify_segment(
        melody_verdict=mel["verdict"],
        global_range_st=7.0,
        breath_verdict="STEADY",
        voice_verdict="CONSISTENT",
        n_syllables=21,
        melodic_span_st=9.0,
        mean_abs_interval_st=MODERATE_LOCAL["motion"],
    )
    assert gate["gate"] == "INCONCLUSIVE"
    assert gate["reasons"] == ["TOO-SHORT"]


def test_assessed_clean_clip_still_reaches_the_ear():
    """The fix must not turn every clip into an abstention: a long, varied clip
    keeps its verdict and still clears the floor."""
    mel = classify_melody(**EXPRESSIVE_LOCAL, **CLEAN_STRUCTURE)
    assert mel["verdict"] == "EXPRESSIVE"
    gate = classify_segment(
        melody_verdict=mel["verdict"],
        global_range_st=9.0,
        breath_verdict="STEADY",
        voice_verdict="CONSISTENT",
        n_syllables=401,
        melodic_span_st=12.0,
        mean_abs_interval_st=EXPRESSIVE_LOCAL["motion"],
    )
    assert gate["gate"] == "PASS-TO-EAR"


# ---------------------------------------------------------------------------
# Calibration regression lock — the three references in melody_stats' docstring
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "label,local,structure,expected",
    [
        # v4 extrait_ouverture_2min30 — the clip served for review ~20 times.
        # Misses FLAT on both local axes; the structure is what convicts it.
        ("v4", dict(motion=1.21, flat_pct=41.2),
         dict(effective_notes=6.0, top3_note_pct=72.8, motif3_repeat_pct=82.2), "DRONE"),
        # v1 kokoro, no cloning — genuinely varied.
        ("v1_kokoro", dict(motion=3.43, flat_pct=12.0),
         dict(effective_notes=11.8, top3_note_pct=44.5, motif3_repeat_pct=14.5), "EXPRESSIVE"),
        # v2 fishaudio tags-only — flat on the local axis already.
        ("v2_fishaudio", dict(motion=0.8, flat_pct=60.0),
         dict(effective_notes=5.3, top3_note_pct=79.7, motif3_repeat_pct=90.9), "DRONE"),
    ],
)
def test_reference_clips_keep_their_calibrated_verdict(label, local, structure, expected):
    assert classify_melody(**local, **structure)["verdict"] == expected


def test_each_drone_criterion_fires_on_its_own():
    """A criterion nobody can trip is not a criterion. One at a time, the other
    two held clean."""
    for key, bad in (
        ("effective_notes", EFFNOTES_DRONE_MAX - 0.1),
        ("top3_note_pct", TOP3_DRONE_MIN + 0.1),
        ("motif3_repeat_pct", MOTIF3_DRONE_MIN + 0.1),
    ):
        structure = dict(CLEAN_STRUCTURE)
        structure[key] = bad
        r = classify_melody(**EXPRESSIVE_LOCAL, **structure)
        assert r["verdict"] == "DRONE", key
        assert len(r["drone_reasons"]) == 1, (key, r["drone_reasons"])
        assert r["drone_reasons"][0].startswith(key)
