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


def test_f1_free_form_french_preserved():
    """F1: free-form natural-language tag stays as [bracket], not collapsed."""
    from v4.p5_tts import _normalize_tags

    out = _normalize_tags("[d'un ton menaçant] Sortez d'ici.")
    assert "[d'un ton menaçant]" in out, out


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


if __name__ == "__main__":
    test_f1_free_form_french_preserved()
    print("F1 ok")
    test_f2_french_prefix_preserved_as_free_form()
    test_f2_official_english_substring_still_wins()
    print("F2 ok")
    test_f3_dramatic_prompt_branched_into_compose()
    test_f3_dramatic_prompt_and_prefix_merge_no_dup()
    print("F3 ok")
    test_f4_temperature_modulated_by_tension()
    print("F4 ok")
    print("All F1-F4 smoke tests passed.")
