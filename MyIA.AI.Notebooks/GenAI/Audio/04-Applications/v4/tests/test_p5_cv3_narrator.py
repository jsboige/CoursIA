"""CosyVoice3 narrator path, phase 1 (#19692) — offline tests.

Covers the sentence chunker (identity, max_chars, clause fallback, no
mid-word cut) and the torch-free failure guards of the CV3 synthesis
branch. The live model is exercised by the measured run in the PR body —
these tests guard the chunking and dispatch logic without torch.

Run from the v4 directory:
    python -m pytest tests/test_p5_cv3_narrator.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


# Extract C of the A0C bench (#17586): real narration long enough to need
# clause fallback and multi-chunk grouping.
_EXTRAIT_C = (
    "Pendant plusieurs jours, des fugitifs discrets arrivaient par tous les "
    "chemins, gens du monde, des femmes, des enfants. Des artilleurs "
    "sombres alignés avec des fantassins divers, sans drapeau, sans "
    "régiment, venaient se ranger sous la croix de guerre. Tous semblaient "
    "accablés, éreintés, incapables de comprendre ou de se décider, prêts à "
    "la fuite puis à la bataille. La maison du notaire était pleine, "
    "jour et nuit."
)


def _build_seg(*, speaker: str, text: str = "x"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=1,
        speaker=speaker,
        type="narration" if speaker == "narrateur" else "dialogue",
        text=text,
        annotated_text=text,
    )


def test_chunker_preserves_every_word():
    """Identity: chunks reassemble to the source — the chunker can never be
    the source of a dropped passage (#19692's omission class lives in the
    model, the chunker must not add its own)."""
    from v4.p5_tts import _chunk_narration

    for text in (_EXTRAIT_C, "Une seule phrase.", "Trois mots. Quatre mots ici. Et voilà."):
        chunks = _chunk_narration(text)
        assert " ".join(chunks).replace("  ", " ").strip() == " ".join(text.split())


def test_chunker_respects_max_chars():
    """Every chunk stays <= max_chars — the bound the A0C bench measured
    (#17586 spec: 280)."""
    from v4.p5_tts import _chunk_narration

    chunks = _chunk_narration(_EXTRAIT_C)
    assert chunks, "chunker returned nothing for a long narration"
    assert all(len(c) <= 280 for c in chunks), [len(c) for c in chunks]


def test_chunker_splits_at_sentence_boundaries():
    """Chunks break after . ! ? — never mid-word, never mid-sentence when
    the sentence fits (small max_chars forces one sentence per chunk)."""
    from v4.p5_tts import _chunk_narration

    chunks = _chunk_narration("Phrase un. Phrase deux ! Phrase trois ?", max_chars=14)
    assert chunks == ["Phrase un.", "Phrase deux !", "Phrase trois ?"]
    # With the default 280 the greedy packer merges short sentences into one
    # chunk — whole units only, identity preserved.
    merged = _chunk_narration("Phrase un. Phrase deux ! Phrase trois ?")
    assert merged == ["Phrase un. Phrase deux ! Phrase trois ?"]


def test_chunker_clause_fallback_for_long_sentence():
    """A sentence over max_chars falls back to clause boundaries (, ; :)
    rather than truncating mid-word."""
    from v4.p5_tts import _chunk_narration

    long_sentence = (
        "Une phrase très longue, avec des propositions, des virgules, des "
        "points-virgules ; et encore des mots, beaucoup de mots, toujours "
        "plus de mots pour dépasser largement la limite de deux cent "
        "quatre-vingts caractères, encore quelques mots supplémentaires "
        "ici, puis d'autres encore, et enfin une fin de phrase."
    )
    assert len(long_sentence) > 280
    chunks = _chunk_narration(long_sentence)
    assert all(len(c) <= 280 for c in chunks)
    # Identity still holds through the fallback.
    rejoined = " ".join(chunks)
    assert rejoined == " ".join(long_sentence.split())


def test_chunker_refuses_undivisible_clause():
    """A clause longer than max_chars with no , ; : boundary is a hard
    error: a mid-word cut would corrupt the narration instead of failing
    loudly."""
    from v4.p5_tts import _chunk_narration

    monolith = "mot " * 100  # 400 chars, no punctuation
    try:
        _chunk_narration(monolith.strip())
    except ValueError:
        pass
    else:
        raise AssertionError("undivisible clause must raise ValueError, not truncate")


def test_chunker_empty_input_returns_empty():
    from v4.p5_tts import _chunk_narration

    assert _chunk_narration("") == []
    assert _chunk_narration("   \n  ") == []


def test_cv3_unavailable_is_runtime_error():
    """NarratorCosyVoice3Unavailable shares the NarratorQwenUnavailable
    contract: a single RuntimeError class for any CV3-side failure, hard
    failure, never a silent FishAudio fallback (#15002 acceptance 6)."""
    from v4.p5_tts import NarratorCosyVoice3Unavailable, NarratorQwenUnavailable

    assert issubclass(NarratorCosyVoice3Unavailable, RuntimeError)
    assert issubclass(NarratorCosyVoice3Unavailable, RuntimeError)
    assert NarratorCosyVoice3Unavailable is not NarratorQwenUnavailable


def test_cv3_reference_id_is_distinct_sentinel():
    """The CV3 branch stamps its own reference_id so tts_results.json and p7
    can tell which engine rendered a segment."""
    from v4.p5_tts import _CV3_NARRATOR_REFERENCE_ID, _QWEN_NARRATOR_REFERENCE_ID

    assert _CV3_NARRATOR_REFERENCE_ID != _QWEN_NARRATOR_REFERENCE_ID
    assert not _CV3_NARRATOR_REFERENCE_ID.startswith("v4_")


def test_synthesize_narrator_cv3_raises_on_empty_input():
    """Empty text after bracket stripping raises BEFORE any torch import —
    hermetic: the guard must not require the CosyVoice runtime."""
    from v4.p5_tts import NarratorCosyVoice3Unavailable, _synthesize_narrator_cosyvoice3

    seg = _build_seg(speaker="narrateur", text="")
    try:
        _synthesize_narrator_cosyvoice3(
            seg=seg,
            fishaudio_text="[whispering]",  # empty after strip
            mp3_path=Path("should_never_be_written.mp3"),
            seed=42,
            text_hash="deadbeef",
        )
    except NarratorCosyVoice3Unavailable:
        return  # success: raised as designed
    raise AssertionError("NarratorCosyVoice3Unavailable not raised on empty input")


def test_narrator_cache_is_engine_aware(tmp_path, monkeypatch):
    """Flipping NARRATOR_COSYVOICE3_ROUTING must not serve the previous
    engine's MP3 from the batch cache: the narrator cache keys on the
    engine sentinel (#19692) — a text hash alone cannot tell which engine
    rendered the file. Dialogue segments stay cached regardless (they never
    change engine)."""
    from v4 import p5_tts
    from v4.schemas import TTSResult

    (tmp_path / "seg_0001_narrateur.mp3").write_bytes(b"fake")
    (tmp_path / "seg_0001_loiseau.mp3").write_bytes(b"fake")
    monkeypatch.setattr(p5_tts, "TTS_DIR", tmp_path)
    monkeypatch.setattr(p5_tts, "audio_duration_mp3", lambda b: 1.0)
    monkeypatch.setattr(p5_tts, "thermal_wait", lambda *a, **k: 0)

    def _stub(seg, text):
        return TTSResult(
            seg_index=seg.seg_index, speaker=seg.speaker, reference_id="stub",
            mp3_path="stub", duration_s=1.0, seed=42, status="generated",
            attempts=1, text_hash="stub",
        )

    monkeypatch.setattr(p5_tts, "_synthesize_segment", _stub)

    narr = _build_seg(speaker="narrateur", text="Il marcha.")
    dlg = _build_seg(speaker="loiseau", text="Bonjour.")
    h_narr = p5_tts._text_hash("Il marcha.")
    h_dlg = p5_tts._text_hash("Bonjour.")

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True

        # Cache says Qwen rendered it; CV3 is selected -> regenerate.
        out = p5_tts._synthesize_batch(
            [(narr, "Il marcha.")],
            {1: h_narr},
            {1: p5_tts._QWEN_NARRATOR_REFERENCE_ID},
        )
        assert out[0].status == "generated"

        # Cache says CV3 rendered it; CV3 is selected -> served cached.
        out = p5_tts._synthesize_batch(
            [(narr, "Il marcha.")],
            {1: h_narr},
            {1: p5_tts._CV3_NARRATOR_REFERENCE_ID},
        )
        assert out[0].status == "cached"

        # Dialogue segments never change engine: hash match is enough.
        out = p5_tts._synthesize_batch(
            [(dlg, "Bonjour.")], {1: h_dlg}, {1: "v4_loiseau_voice"}
        )
        assert out[0].status == "cached"
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3
