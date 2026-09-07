"""F6 narrator routing to Qwen3-TTS VoiceDesign (Issue #15002) — offline tests.

These tests construct AnnotatedSegment instances and verify the routing
decision + bracket-stripping without ever hitting the Qwen3-TTS gateway.
The live gateway is exercised by the run-level smoke in the PR body
(commit hash + byte counts) — these tests guard the dispatch logic.

Run from the v4 directory:
    python -m pytest tests/test_p5_narrator_routing.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def _build_seg(*, speaker: str, text: str = "x"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=1,
        speaker=speaker,
        type="narration" if speaker == "narrateur" else "dialogue",
        text=text,
        annotated_text=text,
    )


def test_routes_narrator_to_qwen_when_flag_on():
    """When NARRATOR_QWEN_ROUTING is ON (default), narrator segments route."""
    from v4.p5_tts import _should_route_narrator_to_qwen

    seg = _build_seg(speaker="narrateur")
    assert _should_route_narrator_to_qwen(seg) is True


def test_does_not_route_non_narrator_speakers():
    """Acceptance #1: routing is limited to narrateur; other speakers stay
    on FishAudio clone even when the flag is ON."""
    from v4.p5_tts import _should_route_narrator_to_qwen

    for speaker in (
        "elisabeth_rousset",
        "loiseau",
        "comte",
        "comtesse",
        "cornudet",
        "officier",
        "figurant",
    ):
        seg = _build_seg(speaker=speaker)
        assert _should_route_narrator_to_qwen(seg) is False, (
            f"non-narrator speaker '{speaker}' must NOT route to Qwen"
        )


def test_routes_off_when_flag_disabled():
    """Env flag NARRATOR_QWEN_ROUTING=0 disables routing (legacy path)."""
    from v4 import p5_tts

    original = p5_tts._NARRATOR_QWEN_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to_qwen(seg) is False
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = original


def test_strip_brackets_for_qwen_removes_inline_tags():
    """VoiceDesign receives the bare text; brackets would be ignored or,
    worse, vocalized (WER regression #1277/#1485 on FishAudio bracket text).
    The narrator branch must strip them BEFORE sending to Qwen."""
    from v4.p5_tts import _strip_brackets_for_qwen

    stripped = _strip_brackets_for_qwen(
        "[emphasis] Les voyageurs se regardaient [whispering] avec une certaine honte."
    )
    assert stripped == "Les voyageurs se regardaient avec une certaine honte."
    assert "[" not in stripped and "]" not in stripped


def test_strip_brackets_handles_empty_input():
    """Empty or whitespace-only input after stripping must raise the
    narrator-unavailable signal — it indicates upstream P4 produced no
    renderable text and we refuse to fabricate audio."""
    from v4.p5_tts import _strip_brackets_for_qwen

    assert _strip_brackets_for_qwen("") == ""
    assert _strip_brackets_for_qwen("[whispering]") == ""
    assert _strip_brackets_for_qwen("   \n  ") == ""


def test_narrator_reference_id_is_qwen_sentinel():
    """The narrator branch must stamp a distinct reference_id so downstream
    consumers (tts_results.json, p7 WER, p8 listener review) can tell which
    engine produced the audio without re-decoding the MP3."""
    from v4.p5_tts import _QWEN_NARRATOR_REFERENCE_ID

    assert _QWEN_NARRATOR_REFERENCE_ID == "qwen-voicedesign-narrator-fr-literary"
    # And it must NOT collide with any FishAudio voice id (prefixed `v4_`).
    assert not _QWEN_NARRATOR_REFERENCE_ID.startswith("v4_")


def test_narrator_instructions_within_server_cap():
    """VoiceDesign server caps `instructions` at 500 chars (qwen_tts_client
    MAX_INSTRUCTIONS_LEN). The narrator instructions must stay under."""
    from v4.p5_tts import _QWEN_NARRATOR_INSTRUCTIONS
    from v4.prosody_lab.qwen_tts_client import MAX_INSTRUCTIONS_LEN

    assert len(_QWEN_NARRATOR_INSTRUCTIONS) <= MAX_INSTRUCTIONS_LEN, (
        f"instructions length {len(_QWEN_NARRATOR_INSTRUCTIONS)} "
        f"exceeds server cap {MAX_INSTRUCTIONS_LEN}"
    )


def test_narrator_unavailable_is_runtime_error():
    """NarratorQwenUnavailable must be a RuntimeError so callers can catch
    a single class for any Qwen-side failure (gateway 4xx/5xx, render fail,
    WAV->MP3 conversion)."""
    from v4.p5_tts import NarratorQwenUnavailable

    assert issubclass(NarratorQwenUnavailable, RuntimeError)
    # Raising preserves the call chain for diagnosis.
    try:
        raise NarratorQwenUnavailable("test")
    except RuntimeError as exc:
        assert str(exc) == "test"


def test_synthesize_narrator_qwen_raises_on_empty_input():
    """If upstream P4 produces no renderable text, _synthesize_narrator_qwen
    must raise NarratorQwenUnavailable rather than write an empty MP3 or
    silently fall back. The pipeline surfaces this as a hard failure."""
    from v4.p5_tts import (
        NarratorQwenUnavailable,
        _synthesize_narrator_qwen,
    )

    seg = _build_seg(speaker="narrateur", text="")
    try:
        _synthesize_narrator_qwen(
            seg=seg,
            fishaudio_text="   \n  ",  # whitespace-only after strip
            mp3_path=Path("/tmp/should_never_be_written.mp3"),
            seed=42,
            text_hash="deadbeef",
        )
    except NarratorQwenUnavailable:
        return  # success: raised as designed
    raise AssertionError("NarratorQwenUnavailable not raised on empty input")
