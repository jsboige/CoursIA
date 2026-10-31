"""FishAudio multi-chunk path — a partial passage is never shipped.

Issue #1600 / #19739 lineage. ``_synthesize_fishaudio_path`` splits a long
segment into chunks of at most ``_MAX_CHUNK_CHARS`` and renders them
sequentially. Before this guard, a chunk that came back ``None`` (or empty)
was silently filtered out of ``audio_results``: the surviving chunks were
concatenated, the MP3 was written, and the segment was reported
``status="generated"`` — up to ~220 characters of dialogue vanished from the
audiobook with nothing anywhere saying so.

The contract asserted here is the one the other render paths already hold:
the Qwen client returns ``None`` "so a partial passage is never silently
measured", and the single-chunk branch below fails the segment on a falsy
render. A missing segment is visible in the report; a hole is not.

Run from the v4 directory:
    python -m pytest tests/test_p5_fishaudio_partial.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Allow `python tests/test_p5_fishaudio_partial.py` from the v4 dir too.
_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


# A text long enough to be split into more than one chunk (> _MAX_CHUNK_CHARS)
# and written with sentence boundaries so _split_long_text has real split points.
LONG_TEXT = (
    "Le soldat s'approcha lentement de la fenetre. "
    "Il regardait la campagne couverte de neige, sans dire un mot. "
    "Puis il se retourna vers la salle et annonca que le convoi partirait "
    "au lever du jour, ce qui jeta un froid parmi les voyageurs. "
    "Boule de Suif baissa la tete et ne repondit rien. " * 2
)


def _build_seg(seg_index: int = 7, speaker: str = "figurant"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=seg_index,
        type="dialogue",
        speaker=speaker,
        speaker_raw="Soldat",
        text="Texte du segment.",
        annotated_text="Texte du segment.",
        prosody_tags=[],
        tags_used=[],
        fishaudio_text="",
        dramatic_ref=None,
        dramatic_prompt="",
        tts_context_prefix="",
    )


def _patch_common(monkeypatch, p5, render):
    """Patch the network/hardware seams; return the concat recorder."""
    calls = {"concat": []}

    def _fake_concat(parts):
        calls["concat"].append(list(parts))
        return b"CONCAT"

    monkeypatch.setattr(p5, "fishaudio_tts", render)
    monkeypatch.setattr(p5, "thermal_wait", lambda: None)
    monkeypatch.setattr(p5, "thermal_backoff", lambda **kw: None)
    monkeypatch.setattr(p5, "audio_duration_mp3", lambda data: 1.5)
    monkeypatch.setattr(p5, "_concat_audio_parts", _fake_concat)
    return calls


def _call(p5, seg, text, tmp_path, reference_id="v4_figurant_soldier"):
    mp3_path = tmp_path / f"seg_{seg.seg_index:04d}_{seg.speaker}.mp3"
    return p5._synthesize_fishaudio_path(
        seg=seg,
        fishaudio_text=text,
        reference_id=reference_id,
        seed=42 + seg.seg_index,
        mp3_path=mp3_path,
        current_hash=p5._text_hash(text),
    ), mp3_path


def test_long_text_actually_splits_into_several_chunks():
    """Precondition: the fixture text is really multi-chunk, not a single one."""
    from v4.p5_tts import _MAX_CHUNK_CHARS, _split_long_text

    chunks = _split_long_text(LONG_TEXT)
    assert len(chunks) >= 3, f"expected a multi-chunk fixture, got {len(chunks)}"
    # _split_long_text searches for a break point in [max//2, max*1.2], so a
    # chunk may legitimately exceed max_chars by up to 20%.
    hard_cap = int(_MAX_CHUNK_CHARS * 1.2)
    assert all(len(c) <= hard_cap + 2 for c in chunks), [len(c) for c in chunks]


def test_failed_chunk_fails_the_whole_segment(monkeypatch, tmp_path):
    """The defect: chunk 2 dies twice, chunks 1 and 3 render.

    Before the guard, the segment was written with chunks 1 and 3 only and
    reported ``status="generated"``. Now it fails as a whole and no MP3 is
    produced — a hole becomes a visible missing segment.
    """
    import v4.p5_tts as p5

    from v4.p5_tts import _split_long_text

    n_chunks = len(_split_long_text(LONG_TEXT))
    render_calls: list[str] = []

    def _render(**kwargs):
        render_calls.append(kwargs["text"])
        # Chunk 2 fails both times (initial render + thermal retry).
        if len(render_calls) in (2, 3):
            return None
        return b"CHUNK"

    calls = _patch_common(monkeypatch, p5, _render)

    seg = _build_seg()
    result, mp3_path = _call(p5, seg, LONG_TEXT, tmp_path)

    assert result.status == "failed", result
    assert result.mp3_path == "", result.mp3_path
    assert result.duration_s == 0.0
    # 1 render per chunk + 1 extra for the failed chunk's thermal retry.
    assert result.attempts == n_chunks + 1, (result.attempts, n_chunks)
    # The decisive assertion: no partial audio was ever concatenated or written.
    assert calls["concat"] == [], calls["concat"]
    assert not mp3_path.exists(), "a partial passage was written to disk"


def test_empty_bytes_counts_as_failure(monkeypatch, tmp_path):
    """b"" is a failed render, not a delivered chunk.

    The single-chunk branch already treats it that way (``[audio] if audio
    else []``), so the multi-chunk branch must not be more permissive.
    """
    import v4.p5_tts as p5

    render_calls: list[str] = []

    def _render(**kwargs):
        render_calls.append(kwargs["text"])
        if len(render_calls) == 2:
            return b""  # empty body, not None
        return b"CHUNK"

    calls = _patch_common(monkeypatch, p5, _render)

    seg = _build_seg()
    result, mp3_path = _call(p5, seg, LONG_TEXT, tmp_path)

    assert result.status == "failed", result
    assert calls["concat"] == [], calls["concat"]
    assert not mp3_path.exists()


def test_all_chunks_rendered_generates_the_segment(monkeypatch, tmp_path):
    """Control: with every chunk intact, the segment is generated as before.

    A guard that also refused healthy segments would be a different bug.
    """
    import v4.p5_tts as p5

    from v4.p5_tts import _split_long_text

    n_chunks = len(_split_long_text(LONG_TEXT))

    def _render(**kwargs):
        return b"CHUNK"

    calls = _patch_common(monkeypatch, p5, _render)

    seg = _build_seg()
    result, mp3_path = _call(p5, seg, LONG_TEXT, tmp_path)

    assert result.status == "generated", result
    assert result.attempts == n_chunks, (result.attempts, n_chunks)
    assert result.duration_s == 1.5
    assert len(calls["concat"]) == 1, calls["concat"]
    assert len(calls["concat"][0]) == n_chunks, calls["concat"]
    assert mp3_path.exists()
    assert mp3_path.read_bytes() == b"CONCAT"


def test_single_chunk_failure_still_fails(monkeypatch, tmp_path):
    """Regression guard: the single-chunk branch keeps failing the segment."""
    import v4.p5_tts as p5

    def _render(**kwargs):
        return None

    calls = _patch_common(monkeypatch, p5, _render)

    seg = _build_seg()
    result, mp3_path = _call(p5, seg, "Une seule phrase courte.", tmp_path)

    assert result.status == "failed", result
    assert result.attempts == 2, result.attempts  # initial render + retry
    assert calls["concat"] == [], calls["concat"]
    assert not mp3_path.exists()


def test_failed_segment_is_not_cached_as_generated(monkeypatch, tmp_path):
    """The failure path returns before the write, so the cache is untouched.

    ``mp3_path.exists()`` is how the next run decides between "cached" and
    "regenerate": writing a truncated MP3 would also freeze the hole.
    """
    import v4.p5_tts as p5

    def _render(**kwargs):
        return None

    _patch_common(monkeypatch, p5, _render)

    seg = _build_seg(seg_index=11)
    first, mp3_path = _call(p5, seg, LONG_TEXT, tmp_path)
    assert first.status == "failed"
    assert not mp3_path.exists()

    # A second identical call still has to re-render (nothing cached on disk).
    second, _ = _call(p5, seg, LONG_TEXT, tmp_path)
    assert second.status == "failed"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
