# -*- coding: utf-8 -*-
"""Unit tests for ``scripts/tts_verification/verify_diarization.py``.

The diarization verifier is a Stage-2 TTS QA tool whose network backends
(``_gradio_login`` / ``diarize_gradio`` / ``diarize_whisper_fallback``) call a
live Whisper WebUI / Whisper API and are out of scope for unit tests. The three
**pure** functions that those backends feed -- the SRT parser, the
speaker-label → expected-speaker co-occurrence mapper, and the voice-purity
scorer -- carry the actual decision logic and had **zero direct coverage**.
This file pins their contracts in isolation.

Run from the repo root::

    python -m pytest scripts/tests/test_verify_diarization.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make ``scripts/`` importable so ``tts_verification.verify_diarization`` resolves
# as a PEP-420 namespace package (tts_verification/ has no __init__.py).
_REPO_ROOT = Path(__file__).resolve().parent.parent.parent
_SCRIPTS = Path(__file__).resolve().parent.parent
for p in (_SCRIPTS, _REPO_ROOT):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

from tts_verification.verify_diarization import (  # noqa: E402
    _parse_srt,
    build_speaker_mapping,
    compute_voice_purity,
)


# ---------------------------------------------------------------------------
# _parse_srt
# ---------------------------------------------------------------------------
def test_parse_srt_empty_returns_empty_list():
    """Empty / whitespace-only SRT yields an empty segment list (no crash)."""
    assert _parse_srt("") == []
    assert _parse_srt("   \n\n  ") == []


def test_parse_srt_single_block_extracts_speaker_text_and_times():
    """One well-formed SRT block -> one segment with speaker / text / seconds."""
    srt = "1\n00:00:01,000 --> 00:00:02,500\nSPEAKER_00 | Bonjour le monde"
    segs = _parse_srt(srt)
    assert len(segs) == 1
    seg = segs[0]
    assert seg["start"] == 1.0
    assert seg["end"] == 2.5
    assert seg["text"] == "Bonjour le monde"
    # Speaker label is extracted from the "SPEAKER_XX |" prefix.
    assert "SPEAKER_00" in seg["speaker"]


def test_parse_srt_multiple_blocks_split_on_blank_line():
    """Blocks are separated by a blank line (``\\n\\n``)."""
    srt = (
        "1\n00:00:01,000 --> 00:00:02,000\nSPEAKER_00 | first\n\n"
        "2\n00:00:03,000 --> 00:00:04,000\nSPEAKER_01 | second"
    )
    segs = _parse_srt(srt)
    assert len(segs) == 2
    assert segs[0]["text"] == "first"
    assert segs[1]["text"] == "second"
    assert segs[1]["start"] == 3.0


def test_parse_srt_skips_blocks_with_fewer_than_three_lines():
    """A block needs at least index + timing + text lines; shorter is dropped."""
    srt = "1\n00:00:01,000 --> 00:00:02,000\n\n2\n00:00:03,000 --> 00:00:04,000\nSPEAKER_00 | kept"
    segs = _parse_srt(srt)
    assert len(segs) == 1
    assert segs[0]["text"] == "kept"


def test_parse_srt_unknown_speaker_when_no_prefix():
    """Text without the ``SPEAKER_XX |`` prefix is tagged UNKNOWN."""
    srt = "1\n00:00:01,000 --> 00:00:02,000\njust narration, no speaker tag"
    segs = _parse_srt(srt)
    assert len(segs) == 1
    assert segs[0]["speaker"] == "UNKNOWN"
    assert segs[0]["text"] == "just narration, no speaker tag"


def test_parse_srt_malformed_timing_falls_back_to_zero():
    """A malformed ``-->`` line yields start=end=0.0 (graceful, no exception)."""
    srt = "1\nNOT A TIMESTAMP LINE\nSPEAKER_00 | text"
    segs = _parse_srt(srt)
    assert len(segs) == 1
    assert segs[0]["start"] == 0.0
    assert segs[0]["end"] == 0.0


def test_parse_srt_time_conversion_hours_minutes_seconds():
    """``HH:MM:SS,mmm`` is converted to seconds (1h 1m 1.5s = 3661.5)."""
    srt = "1\n01:01:01,500 --> 01:01:02,500\nSPEAKER_00 | x"
    segs = _parse_srt(srt)
    assert segs[0]["start"] == pytest.approx(3661.5)
    assert segs[0]["end"] == pytest.approx(3662.5)


# ---------------------------------------------------------------------------
# build_speaker_mapping
# ---------------------------------------------------------------------------
def test_build_speaker_mapping_majority_vote():
    """Each detected label maps to its most-co-occurring expected speaker."""
    results = [
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur"},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur"},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "personnage"},
        {"dominant_speaker": "SPEAKER_01", "expected_speaker": "personnage"},
    ]
    mapping = build_speaker_mapping(results, ["narrateur", "personnage"])
    assert mapping == {"SPEAKER_00": "narrateur", "SPEAKER_01": "personnage"}


def test_build_speaker_mapping_ignores_empty_and_errors():
    """Segments with empty speaker / empty expected / error are skipped."""
    results = [
        {"dominant_speaker": "", "expected_speaker": "narrateur"},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": ""},
        {"dominant_speaker": "SPEAKER_01", "expected_speaker": "narrateur", "error": "boom"},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur"},
    ]
    mapping = build_speaker_mapping(results, ["narrateur"])
    assert mapping == {"SPEAKER_00": "narrateur"}


def test_build_speaker_mapping_empty_results():
    """No usable segments -> empty mapping."""
    assert build_speaker_mapping([], ["narrateur"]) == {}
    assert build_speaker_mapping(
        [{"dominant_speaker": "", "expected_speaker": ""}], ["narrateur"]
    ) == {}


def test_build_speaker_mapping_tie_is_deterministic():
    """A tie is broken by ``Counter.most_common`` insertion order (first wins)."""
    # SPEAKER_00 appears once with narrateur, once with personnage.
    # Counter.most_common(1) returns the first-inserted on a tie.
    results = [
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur"},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "personnage"},
    ]
    mapping = build_speaker_mapping(results, ["narrateur", "personnage"])
    assert mapping == {"SPEAKER_00": "narrateur"}


# ---------------------------------------------------------------------------
# compute_voice_purity
# ---------------------------------------------------------------------------
def test_compute_voice_purity_all_pure():
    """Every segment's mapped dominant matches expected -> 100% purity."""
    results = [
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur", "seg_index": 0},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur", "seg_index": 1},
    ]
    mapping = {"SPEAKER_00": "narrateur"}
    metrics = compute_voice_purity(results, mapping)
    assert metrics["total_scored"] == 2
    assert metrics["pure_segments"] == 2
    assert metrics["purity_rate"] == 100.0
    assert metrics["cross_contaminated"] == 0
    assert metrics["contamination_details"] == []


def test_compute_voice_purity_mixed_matches():
    """2/3 pure -> 66.7% purity, 1 contamination detail recorded."""
    results = [
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur", "seg_index": 0},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur", "seg_index": 1},
        {"dominant_speaker": "SPEAKER_01", "expected_speaker": "narrateur", "seg_index": 2},
    ]
    mapping = {"SPEAKER_00": "narrateur", "SPEAKER_01": "personnage"}
    metrics = compute_voice_purity(results, mapping)
    assert metrics["total_scored"] == 3
    assert metrics["pure_segments"] == 2
    assert metrics["purity_rate"] == pytest.approx(66.7, abs=0.05)
    assert len(metrics["contamination_details"]) == 1
    detail = metrics["contamination_details"][0]
    assert detail["seg_index"] == 2
    assert detail["expected"] == "narrateur"
    assert detail["detected_mapped"] == "personnage"


def test_compute_voice_purity_skips_errors_and_missing_speakers():
    """Segments with error / empty dominant / empty expected are not scored."""
    results = [
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur"},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": "narrateur", "error": "x"},
        {"dominant_speaker": "", "expected_speaker": "narrateur"},
        {"dominant_speaker": "SPEAKER_00", "expected_speaker": ""},
    ]
    mapping = {"SPEAKER_00": "narrateur"}
    metrics = compute_voice_purity(results, mapping)
    assert metrics["total_scored"] == 1
    assert metrics["pure_segments"] == 1


def test_compute_voice_purity_zero_scored_returns_zero_rates():
    """No scorable segments -> total=0, rates 0.0 (no ZeroDivisionError)."""
    metrics = compute_voice_purity([], {})
    assert metrics["total_scored"] == 0
    assert metrics["purity_rate"] == 0.0
    assert metrics["contamination_rate"] == 0.0


def test_compute_voice_purity_unmapped_speaker_falls_back_to_label():
    """A dominant speaker absent from the mapping is compared by raw label."""
    results = [
        {"dominant_speaker": "SPEAKER_99", "expected_speaker": "SPEAKER_99"},
    ]
    metrics = compute_voice_purity(results, {})  # empty mapping
    assert metrics["pure_segments"] == 1
    assert metrics["purity_rate"] == 100.0


def test_compute_voice_purity_cross_contamination_detected():
    """Multiple detected speakers in one segment, one foreign -> contaminated."""
    results = [
        {
            "dominant_speaker": "SPEAKER_00",
            "expected_speaker": "narrateur",
            "detected_speakers": ["SPEAKER_00", "SPEAKER_01"],
        },
    ]
    mapping = {"SPEAKER_00": "narrateur", "SPEAKER_01": "personnage"}
    metrics = compute_voice_purity(results, mapping)
    assert metrics["cross_contaminated"] == 1
    assert metrics["contamination_rate"] == 100.0
    assert results[0].get("cross_contamination") is True
    assert "personnage" in results[0].get("foreign_speakers", [])
