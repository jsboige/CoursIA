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
    """When NARRATOR_QWEN_ROUTING is ON (default), narrator segments route.
    Default behavior is UNCHANGED by phase 1 (#19692): Qwen VoiceDesign
    stays the narrator engine."""
    from v4.p5_tts import _should_route_narrator_to

    seg = _build_seg(speaker="narrateur")
    assert _should_route_narrator_to("qwen_voicedesign", seg) is True


def test_does_not_route_non_narrator_speakers():
    """Acceptance #1: routing is limited to narrateur; other speakers stay
    on FishAudio clone even when an engine flag is ON."""
    from v4.p5_tts import _should_route_narrator_to

    for engine in ("qwen_voicedesign", "cosyvoice3"):
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
            assert _should_route_narrator_to(engine, seg) is False, (
                f"non-narrator speaker '{speaker}' must NOT route to {engine}"
            )


def test_routes_off_when_flag_disabled():
    """Env flag NARRATOR_QWEN_ROUTING=0 with no other engine selected
    disables routing (legacy FishAudio path)."""
    from v4 import p5_tts

    original = p5_tts._NARRATOR_QWEN_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to("qwen_voicedesign", seg) is False
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = original


def test_cosyvoice3_off_by_default():
    """Phase 1 (#19692): CosyVoice3 routing is OFF by default — the default
    narrator engine does not change until the association's listening picks
    the winner (#17586)."""
    from v4 import p5_tts

    assert p5_tts._NARRATOR_COSYVOICE3_ROUTING is False


def test_cosyvoice3_routes_when_selected():
    """With Qwen off and CosyVoice3 on, the narrator routes to CosyVoice3
    and NOT to Qwen — engine selection is exclusive by construction."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to("cosyvoice3", seg) is True
        assert p5_tts._should_route_narrator_to("qwen_voicedesign", seg) is False
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3


def test_both_engine_flags_active_raises():
    """Two active engine flags are a configuration error, never a silent
    precedence — same no-silent-swap contract as #15002 acceptance 6."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = True
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True
        seg = _build_seg(speaker="narrateur")
        try:
            p5_tts._should_route_narrator_to("cosyvoice3", seg)
        except ValueError:
            pass
        else:
            raise AssertionError("two active engine flags must raise ValueError")
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3


def test_selected_narrator_engine_none_when_all_off():
    """No flag on -> None (legacy FishAudio narrator), not an error."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = False
        assert p5_tts._selected_narrator_engine() is None
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3


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


def test_compose_tts_text_keeps_full_text_for_cosyvoice3_narrator():
    """Phase 1 (#19692): the 500-char cap in _compose_tts_text is an S2-Pro
    input limit. A narrator rerouted to CosyVoice3 is bounded per-chunk by
    _chunk_narration instead — truncating here silently drops the tail of
    every long narration (measured: seg 1, 981 chars -> ~440 rendered,
    17.8 s of audio for a 950-char segment = an omission p7's control
    would attribute to the engine). Default (Qwen) and non-narrator
    speakers keep the cap: their engines really do have it."""
    from v4 import p5_tts

    long_text = (
        "Pendant plusieurs jours de suite des lambeaux d'armee en deroute "
        "avaient traverse la ville. " * 8
    ).strip()
    assert len(long_text) > p5_tts._MAX_TTS_CHARS

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        # CosyVoice3 selected: narrator keeps the full text.
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True
        narrator = _build_seg(speaker="narrateur", text=long_text)
        composed = p5_tts._compose_tts_text(narrator)
        assert len(composed) > p5_tts._MAX_TTS_CHARS
        assert not composed.endswith("...")
        assert long_text[: p5_tts._MAX_TTS_CHARS] in composed

        # Same flags, non-narrator: S2-Pro path keeps its cap.
        speaker = _build_seg(speaker="loiseau", text=long_text)
        capped = p5_tts._compose_tts_text(speaker)
        assert len(capped) <= p5_tts._MAX_TTS_CHARS
        assert capped.endswith("...")
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3

    # Default (Qwen narrator): behavior unchanged — cap still applies.
    narrator = _build_seg(speaker="narrateur", text=long_text)
    composed = p5_tts._compose_tts_text(narrator)
    assert len(composed) <= p5_tts._MAX_TTS_CHARS
    assert composed.endswith("...")
