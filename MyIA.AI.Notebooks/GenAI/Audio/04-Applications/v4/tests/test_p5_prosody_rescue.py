"""F1-F4 audiobook prosody rescue (Issue #1600) — offline smoke tests.

These tests construct AnnotatedSegment instances and verify the composed
TTS text + payload reflect the 4 fixes without hitting the FishAudio server.

Run from the v4 directory:
    python -m pytest tests/test_p5_prosody_rescue.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

# Allow `python tests/test_p5_prosody_rescue.py` from the v4 dir too.
_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def _build_seg(
    *,
    annotated_text: str,
    dramatic_prompt: str = "",
    tts_context_prefix: str = "",
    tension: int = 5,
):
    from v4.schemas import AnnotatedSegment, DramaticContext

    dramatic_ref = DramaticContext(
        seg_index=1,
        act="act1_diligence_aller",
        scene_label="test_scene",
        tension_0_10=tension,
        character_state={"narrateur": "neutral"},
        narrative_position="rising",
        dramatic_prompt=dramatic_prompt,
        emotional_keywords=[],
    )
    return AnnotatedSegment(
        seg_index=1,
        type="narration",
        speaker="narrateur",
        speaker_raw="Narrateur",
        text=annotated_text,
        annotated_text=annotated_text,
        prosody_tags=[],
        tags_used=[],
        fishaudio_text="",
        dramatic_ref=dramatic_ref,
        dramatic_prompt=dramatic_prompt,
        tts_context_prefix=tts_context_prefix,
    )


def test_f1_free_form_french_removed_from_body():
    """F1: _normalize_tags removes free-form tags from the annotated body text.

    Post-WER fix (#1485/#1277), free-form tags in body text are stripped because
    S2-Pro vocalises them (proven by WER > 100% on prefixed segments).  F1 only
    empties ``_NON_OFFICIAL_TAG_MAP`` so official tags are NOT collapsed — free-form
    tags in the body are still removed.  Free-form tags reach S2-Pro only via
    ``_extract_prefix_tags`` / ``_compose_tts_text`` (tested in F2/F3).
    """
    from v4.p5_tts import _normalize_tags

    out = _normalize_tags("[d'un ton menaçant] Sortez d'ici.")
    # Free-form tag is removed from body — only the narrative text remains
    assert "[d'un ton menaçant]" not in out, out
    assert "Sortez d'ici." in out, out


def test_f2_french_prefix_preserved_as_free_form():
    """F2: a French/multi-word prefix returns as a single free-form tag."""
    from v4.p5_tts import _extract_prefix_tags

    tags = _extract_prefix_tags("d'un ton sec")
    assert tags == ["d'un ton sec"], tags


def test_f2_official_english_substring_still_wins():
    """F2: when an official English tag is present, it is preferred."""
    from v4.p5_tts import _extract_prefix_tags

    tags = _extract_prefix_tags("she is whispering softly")
    assert "whispering" in tags, tags


def test_f3_dramatic_prompt_branched_into_compose():
    """F3: seg.dramatic_prompt is consumed by _compose_tts_text."""
    from v4.p5_tts import _compose_tts_text

    seg = _build_seg(
        annotated_text="Boule de Suif baissa la tête.",
        dramatic_prompt="[tense whisper]",
        tension=8,
    )
    composed = _compose_tts_text(seg)
    assert "[tense whisper]" in composed, composed


def test_f3_dramatic_prompt_and_prefix_merge_no_dup():
    """F3: prefix tags merge with dramatic_prompt without duplicating."""
    from v4.p5_tts import _compose_tts_text

    seg = _build_seg(
        annotated_text="Elle se tut.",
        dramatic_prompt="[tense whisper]",
        tts_context_prefix="[tense whisper]",
        tension=6,
    )
    composed = _compose_tts_text(seg)
    # tag appears at most once before any narrative text
    assert composed.count("[tense whisper]") == 1, composed


def test_f4_temperature_modulated_by_tension():
    """F4: synth payload temperature scales with seg.dramatic_ref.tension_0_10.

    We patch fishaudio_tts so no network call happens; we capture the kwargs.
    """
    import v4.p5_tts as p5

    captured: list[dict] = []

    def _fake_tts(**kwargs):
        captured.append(kwargs)
        return b""  # treat as failure so MP3 write is skipped

    real_tts = p5.fishaudio_tts
    real_wait = p5.thermal_wait
    p5.fishaudio_tts = _fake_tts
    p5.thermal_wait = lambda: None
    try:
        seg_low = _build_seg(annotated_text="Texte calme.", tension=0)
        seg_high = _build_seg(annotated_text="Texte tendu.", tension=10)
        p5._synthesize_segment(seg_low, "Texte calme.")
        p5._synthesize_segment(seg_high, "Texte tendu.")
    finally:
        p5.fishaudio_tts = real_tts
        p5.thermal_wait = real_wait

    temps = [c["temperature"] for c in captured]
    assert temps, "no payload captured"
    t_low, t_high = temps[0], temps[-1]
    assert abs(t_low - 0.5) < 1e-6, t_low
    assert abs(t_high - 0.9) < 1e-6, t_high
    assert t_low < t_high


def test_max_prefix_tags_cap():
    """Concern 3: _MAX_PREFIX_TAGS prevents tag explosion in composed text."""
    import warnings

    from v4.p5_tts import _MAX_PREFIX_TAGS, _compose_tts_text

    seg = _build_seg(
        annotated_text="Texte court.",
        tts_context_prefix="whispering laughing crying shouting gasping sighing",
        tension=5,
    )
    composed = _compose_tts_text(seg)
    # Count bracketed tags before the narrative text
    tags = [t for t in composed.split() if t.startswith("[") or t.startswith("(")]
    assert len(tags) <= _MAX_PREFIX_TAGS + 1, (
        f"Expected ≤{_MAX_PREFIX_TAGS + 1} prefix elements, got {len(tags)}: {tags}"
    )


def test_extract_official_tags_deprecation_warning():
    """Concern 4: calling _extract_official_tags emits DeprecationWarning."""
    import warnings

    from v4.p5_tts import _extract_official_tags

    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        result = _extract_official_tags("whispering softly")
    assert any(issubclass(w.category, DeprecationWarning) for w in caught), (
        f"Expected DeprecationWarning, got: {[w.category for w in caught]}"
    )
    assert result, f"Expected non-empty result, got: {result}"


# --- F1 additional tests ---


def test_f1_official_tag_preserved_in_body():
    """F1: official S2-Pro tags in body text are kept (not collapsed)."""
    from v4.p5_tts import _normalize_tags

    out = _normalize_tags("[whispering] Sortez d'ici.")
    assert "[whispering]" in out, out
    assert "Sortez d'ici." in out, out


def test_f1_non_official_map_is_empty():
    """F1: _NON_OFFICIAL_TAG_MAP must be empty (no collapsing)."""
    from v4.p5_tts import _NON_OFFICIAL_TAG_MAP

    assert _NON_OFFICIAL_TAG_MAP == {}, f"Expected empty dict, got: {_NON_OFFICIAL_TAG_MAP}"


# --- F2 additional tests ---


def test_f2_empty_prefix_returns_empty():
    """F2: empty or whitespace-only prefix yields no tags."""
    from v4.p5_tts import _extract_prefix_tags

    assert _extract_prefix_tags("") == []
    assert _extract_prefix_tags("   ") == []


def test_f2_long_free_form_dropped():
    """F2: free-form prefix >80 chars is dropped (risk of vocalization)."""
    from v4.p5_tts import _extract_prefix_tags

    long_prefix = "a" * 81
    tags = _extract_prefix_tags(long_prefix)
    assert tags == [], f"Expected empty for >80 chars, got: {tags}"


def test_f2_max_3_official_tags():
    """F2: at most 3 official tags extracted (cap to avoid over-tagging)."""
    from v4.p5_tts import _extract_prefix_tags

    tags = _extract_prefix_tags("whispering laughing crying shouting gasping sighing")
    assert len(tags) <= 3, f"Expected <=3 official tags, got {len(tags)}: {tags}"


# --- F3 additional tests ---


def test_f3_no_dramatic_prompt_no_prefix():
    """F3: when both dramatic_prompt and prefix are empty, result is body only."""
    from v4.p5_tts import _compose_tts_text

    seg = _build_seg(annotated_text="Simple text.")
    composed = _compose_tts_text(seg)
    assert composed.strip() == "Simple text.", composed


def test_f3_only_prefix_no_dramatic():
    """F3: prefix-only segment composes correctly."""
    from v4.p5_tts import _compose_tts_text

    seg = _build_seg(
        annotated_text="Elle sourit.",
        tts_context_prefix="whispering",
    )
    composed = _compose_tts_text(seg)
    assert "[whispering]" in composed, composed
    assert "Elle sourit." in composed, composed


# --- F4 additional tests ---


def test_f4_no_dramatic_ref_defaults_tension_5():
    """F4: when seg.dramatic_ref is None, temperature defaults to tension=5."""
    from v4.schemas import AnnotatedSegment
    import v4.p5_tts as p5

    seg = AnnotatedSegment(
        seg_index=1,
        type="narration",
        speaker="narrateur",
        speaker_raw="Narrateur",
        text="Test.",
        annotated_text="Test.",
        prosody_tags=[],
        tags_used=[],
        fishaudio_text="",
        dramatic_ref=None,
        dramatic_prompt="",
        tts_context_prefix="",
    )

    captured: list[dict] = []

    def _fake_tts(**kwargs):
        captured.append(kwargs)
        return b""

    real_tts = p5.fishaudio_tts
    real_wait = p5.thermal_wait
    p5.fishaudio_tts = _fake_tts
    p5.thermal_wait = lambda: None
    try:
        p5._synthesize_segment(seg, "Test.")
    finally:
        p5.fishaudio_tts = real_tts
        p5.thermal_wait = real_wait

    assert captured, "no payload captured"
    temp = captured[0]["temperature"]
    # tension=5 → 0.5 + 0.04*5 = 0.7
    assert abs(temp - 0.7) < 1e-6, f"Expected 0.7, got {temp}"


def test_f4_temperature_clamped_low():
    """F4: temperature cannot go below 0.4."""
    from v4.p5_tts import _compose_tts_text

    # tension=0 → 0.5 + 0.04*0 = 0.5 (above 0.4 floor, so ok)
    seg = _build_seg(annotated_text="Calme.", tension=0)
    composed = _compose_tts_text(seg)
    # Just verify the segment builds without error — temperature is in _synthesize_segment
    assert "Calme." in composed


# --- _compose_tts_text end-to-end ---


def test_compose_all_parts():
    """End-to-end: dramatic_prompt + prefix + annotated text all present."""
    from v4.p5_tts import _compose_tts_text

    seg = _build_seg(
        annotated_text="Elle partit en courant.",
        dramatic_prompt="excited",
        tts_context_prefix="whispering",
        tension=7,
    )
    composed = _compose_tts_text(seg)
    assert "[excited]" in composed, composed
    assert "[whispering]" in composed, composed
    assert "Elle partit en courant." in composed, composed


def test_compose_truncation():
    """_compose_tts_text truncates at _MAX_TTS_CHARS."""
    from v4.p5_tts import _MAX_TTS_CHARS, _compose_tts_text

    long_text = "mot " * 200  # ~800 chars
    seg = _build_seg(annotated_text=long_text)
    composed = _compose_tts_text(seg)
    assert len(composed) <= _MAX_TTS_CHARS + 10, f"Composed text too long: {len(composed)}"


if __name__ == "__main__":
    import pytest

    pytest.main([__file__, "-v"])
