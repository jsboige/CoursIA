"""#19694 criterion 4 -- hybrid Fish route: audio.cpp for batch narration.

Decision ai-01 (2026-11-24): the S2-Pro model is served two ways. Batch
narration goes through the local audio.cpp server (GGUF weights,
OpenAI-compatible ``/v1/audio/speech``); the expressive path -- the
theatrical turns (``dialogue``, ``thought``) -- stays on the FishAudio
service. ``_synthesize_fishaudio_path`` picks one engine per segment and
renders EVERY chunk with it.

The contract asserted here:

* the routing rule reads the segment's ``type`` only -- ``dramatic_ref`` and
  ``tags_used`` cannot discriminate (all 385 Boule de Suif segments carry
  both), and a narrator engine flag keeps its segments off this route;
* the flag defaults to off, so the legacy path is byte-identical unless a
  run opts in;
* the batch cache is engine-aware: an MP3 rendered by one engine is never
  served as the other's, in either direction;
* an audio.cpp failure sends the WHOLE segment back to the FishAudio
  service (one segment is never assembled from two engines) and the
  fallback is counted, never silent;
* a segment whose both engines fail still ships nothing -- no partial
  passage.

Every network and audio-codec seam is patched; the suite stays hermetic and
runs without ffmpeg.

Run from the v4 directory:
    python -m pytest tests/test_p5_audiocpp_fish_route.py -v
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import types
from pathlib import Path

import pytest
import requests as requests_lib

# Allow `python tests/test_p5_audiocpp_fish_route.py` from the v4 dir too.
_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


# Long enough to split into several chunks (> _MAX_CHUNK_CHARS).
LONG_TEXT = (
    "Le soldat s'approcha lentement de la fenetre. "
    "Il regardait la campagne couverte de neige, sans dire un mot. "
    "Puis il se retourna vers la salle et annonca que le convoi partirait "
    "au lever du jour, ce qui jeta un froid parmi les voyageurs. "
    "Boule de Suif baissa la tete et ne repondit rien. " * 2
)


def _build_seg(seg_index: int = 19, seg_type: str = "narration",
               speaker: str = "narrateur"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=seg_index,
        type=seg_type,
        speaker=speaker,
        speaker_raw=speaker,
        text="Texte du segment.",
        annotated_text="Texte du segment.",
        prosody_tags=[],
        tags_used=[],
        fishaudio_text="",
        dramatic_ref=None,
        dramatic_prompt="",
        tts_context_prefix="",
    )


@pytest.fixture(autouse=True)
def _clean_fallbacks():
    """Each test starts with an empty fallback ledger."""
    import v4.p5_tts as p5

    p5._AUDIOCPP_FALLBACKS.clear()
    p5._AUDIOCPP_WAV_CACHE.clear()
    yield
    p5._AUDIOCPP_FALLBACKS.clear()
    p5._AUDIOCPP_WAV_CACHE.clear()


def _patch_audio_seams(monkeypatch, p5):
    """Patch thermal + concat + duration seams; return the concat recorder.

    The recorders log the parts they were handed, so a test can prove that
    no part of the wrong engine reached the assembled audio. The engines
    themselves (``audiocpp_fish_audio``, ``fishaudio_tts``) are patched by
    each test.
    """
    calls = {"concat": []}

    def _fake_concat(parts):
        calls["concat"].append(list(parts))
        return b"".join(parts)

    monkeypatch.setattr(p5, "thermal_wait", lambda: None)
    monkeypatch.setattr(p5, "thermal_backoff", lambda **kw: None)
    monkeypatch.setattr(p5, "audio_duration_mp3", lambda data: 1.5)
    monkeypatch.setattr(p5, "_concat_audio_parts", _fake_concat)
    return calls


def _call(p5, seg, text, tmp_path, reference_id="v4_narrator_male_neutral"):
    mp3_path = tmp_path / f"seg_{seg.seg_index:04d}_{seg.speaker}.mp3"
    return p5._synthesize_fishaudio_path(
        seg=seg,
        fishaudio_text=text,
        reference_id=reference_id,
        seed=42 + seg.seg_index,
        mp3_path=mp3_path,
        current_hash=p5._text_hash(text),
    ), mp3_path


# ---------------------------------------------------------------------------
# The routing rule
# ---------------------------------------------------------------------------


def test_route_sends_narration_to_audiocpp_when_enabled(monkeypatch):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    assert p5._fishaudio_route(_build_seg(seg_type="narration")) == p5._ROUTE_AUDIOCPP


def test_route_keeps_dialogue_and_thought_on_the_service(monkeypatch):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    for seg_type in ("dialogue", "thought"):
        assert (
            p5._fishaudio_route(_build_seg(seg_type=seg_type, speaker="figurant"))
            == p5._ROUTE_FISHAUDIO
        ), seg_type


def test_route_is_off_unless_the_run_opts_in():
    """The shipped default keeps the legacy path: no env flag, no audio.cpp.

    Read from a fresh interpreter with the variable removed from the
    environment, so a developer shell that sets the flag cannot mask the
    default. The rule reads ``seg.type`` only, so a stand-in is enough.
    """
    code = (
        "import v4.p5_tts as p5;"
        "seg = type('S', (), {'type': 'narration'})();"
        "print(p5._AUDIOCPP_FISH_ROUTING, p5._fishaudio_route(seg))"
    )
    env = {k: v for k, v in os.environ.items() if k != "AUDIOCPP_FISH_ROUTING"}
    proc = subprocess.run(
        [sys.executable, "-c", code], cwd=_V4.parent, env=env,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        timeout=180,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout.split() == ["False", "fishaudio"]


def test_a_narrator_engine_flag_keeps_narration_off_the_audiocpp_route(monkeypatch):
    """Qwen/CosyVoice3/... own narrator segments before this seam (#19692)."""
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    monkeypatch.setattr(p5, "_NARRATOR_QWEN_ROUTING", True)
    assert p5._fishaudio_route(_build_seg()) == p5._ROUTE_FISHAUDIO


def test_cache_hash_separates_the_two_engines(monkeypatch):
    import v4.p5_tts as p5

    text = "Un texte identique."
    fish = p5._fishaudio_cache_hash(p5._ROUTE_FISHAUDIO, text)
    audiocpp = p5._fishaudio_cache_hash(p5._ROUTE_AUDIOCPP, text)
    assert fish == p5._text_hash(text)  # the legacy key is unchanged
    assert audiocpp != fish


# ---------------------------------------------------------------------------
# The segment-level dispatch
# ---------------------------------------------------------------------------


def test_segment_is_rendered_by_the_audiocpp_adapter(monkeypatch, tmp_path):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    seen: list[dict] = []

    def _adapter(**kwargs):
        seen.append(kwargs)
        return b"AUDIOCPP"

    def _service(**kwargs):  # pragma: no cover - must not run
        raise AssertionError("the FishAudio service was called on the audiocpp route")

    monkeypatch.setattr(p5, "audiocpp_fish_audio", _adapter)
    monkeypatch.setattr(p5, "fishaudio_tts", _service)
    calls = _patch_audio_seams(monkeypatch, p5)

    seg = _build_seg()
    result, mp3_path = _call(p5, seg, "Une phrase courte.", tmp_path)

    assert result.status == "generated", result
    assert len(seen) == 1, seen
    request = seen[0]
    assert request["reference_id"] == "v4_narrator_male_neutral"
    assert request["seed"] == 42 + seg.seg_index
    assert request["format"] == "mp3"
    assert request["temperature"] == pytest.approx(0.7)  # tension 5 -> 0.5+0.2
    assert mp3_path.read_bytes() == b"AUDIOCPP"
    assert p5.audiocpp_fallbacks() == {}


def test_segment_stays_on_the_service_when_the_flag_is_off(monkeypatch, tmp_path):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", False)
    seen: list[dict] = []

    def _service(**kwargs):
        seen.append(kwargs)
        return b"SERVICE"

    def _adapter(**kwargs):  # pragma: no cover - must not run
        raise AssertionError("audio.cpp was called with the flag off")

    monkeypatch.setattr(p5, "fishaudio_tts", _service)
    monkeypatch.setattr(p5, "audiocpp_fish_audio", _adapter)
    calls = _patch_audio_seams(monkeypatch, p5)

    result, mp3_path = _call(p5, _build_seg(), "Une phrase courte.", tmp_path)

    assert result.status == "generated", result
    assert len(seen) == 1, seen
    assert mp3_path.read_bytes() == b"SERVICE"
    assert result.text_hash == p5._text_hash("Une phrase courte.")


# ---------------------------------------------------------------------------
# The engine-aware cache
# ---------------------------------------------------------------------------


def _write_results(p5, base_dir: Path, seg: dict) -> None:
    out = base_dir / "outputs"
    out.mkdir(parents=True, exist_ok=True)
    (out / "tts_results.json").write_text(json.dumps([seg]), encoding="utf-8")


def test_cached_audiocpp_render_is_served_without_rendering(monkeypatch, tmp_path):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    monkeypatch.setattr(p5, "BASE_DIR", tmp_path)
    text = "Une phrase courte."
    mp3_path = tmp_path / "seg_0019_narrateur.mp3"
    mp3_path.write_bytes(b"CACHED")
    _write_results(p5, tmp_path, {
        "seg_index": 19,
        "text_hash": p5._fishaudio_cache_hash(p5._ROUTE_AUDIOCPP, text),
    })

    def _boom(**kwargs):  # pragma: no cover - must not run
        raise AssertionError("a cached audiocpp render was re-rendered")

    monkeypatch.setattr(p5, "audiocpp_fish_audio", _boom)
    monkeypatch.setattr(p5, "fishaudio_tts", _boom)
    _patch_audio_seams(monkeypatch, p5)

    result, _ = _call(p5, _build_seg(), text, tmp_path)

    assert result.status == "cached", result
    assert result.attempts == 0
    assert Path(result.mp3_path).read_bytes() == b"CACHED"


def test_a_service_render_is_not_cached_as_an_audiocpp_render(monkeypatch, tmp_path):
    """Flipping the flag must re-render, not serve the other engine's MP3."""
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    monkeypatch.setattr(p5, "BASE_DIR", tmp_path)
    text = "Une phrase courte."
    mp3_path = tmp_path / "seg_0019_narrateur.mp3"
    mp3_path.write_bytes(b"FROM-THE-SERVICE")
    _write_results(p5, tmp_path, {
        "seg_index": 19,
        "text_hash": p5._text_hash(text),  # the service's key
    })

    monkeypatch.setattr(p5, "audiocpp_fish_audio", lambda **kw: b"AUDIOCPP")
    calls = _patch_audio_seams(monkeypatch, p5)

    result, path = _call(p5, _build_seg(), text, tmp_path)

    assert result.status == "generated", result
    assert path.read_bytes() == b"AUDIOCPP", "the stale service MP3 was served"
    assert result.text_hash == p5._fishaudio_cache_hash(p5._ROUTE_AUDIOCPP, text)
    assert calls["concat"] == [[b"AUDIOCPP"]]  # single chunk, one engine only


# ---------------------------------------------------------------------------
# The fallback
# ---------------------------------------------------------------------------


def test_failed_audiocpp_chunk_falls_back_to_the_service_for_the_whole_segment(
    monkeypatch, tmp_path
):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    n_chunks = len(p5._split_long_text(LONG_TEXT))
    audiocpp_calls: list[str] = []
    service_calls: list[str] = []

    def _adapter(**kwargs):
        audiocpp_calls.append(kwargs["text"])
        # Chunk 2 fails both times (initial render + thermal retry).
        if len(audiocpp_calls) in (2, 3):
            return None
        return b"AUDIOCPP"

    def _service(**kwargs):
        service_calls.append(kwargs["text"])
        return b"CHUNK"

    monkeypatch.setattr(p5, "audiocpp_fish_audio", _adapter)
    monkeypatch.setattr(p5, "fishaudio_tts", _service)
    calls = _patch_audio_seams(monkeypatch, p5)

    seg = _build_seg(seg_index=20)
    result, mp3_path = _call(p5, seg, LONG_TEXT, tmp_path)

    assert result.status == "generated", result
    # The whole segment was re-rendered by the service: every chunk, once.
    assert len(service_calls) == n_chunks, service_calls
    # ...and no audio.cpp part slipped into the assembled audio.
    assert len(calls["concat"]) == 1, calls["concat"]
    assert calls["concat"][0] == [b"CHUNK"] * n_chunks
    assert mp3_path.read_bytes() == b"CHUNK" * n_chunks
    # The fallback is counted with the renders it cost.
    assert p5.audiocpp_fallbacks() == {20: len(audiocpp_calls)}
    # Cached under the service's key: the next audiocpp run retries it.
    assert result.text_hash == p5._text_hash(LONG_TEXT)


def test_failed_fallback_ships_nothing(monkeypatch, tmp_path):
    """Both engines down: a visible missing segment, never a hole."""
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    monkeypatch.setattr(p5, "audiocpp_fish_audio", lambda **kw: None)
    monkeypatch.setattr(p5, "fishaudio_tts", lambda **kw: None)
    calls = _patch_audio_seams(monkeypatch, p5)

    seg = _build_seg(seg_index=21)
    result, mp3_path = _call(p5, seg, LONG_TEXT, tmp_path)

    assert result.status == "failed", result
    assert result.mp3_path == ""
    assert result.duration_s == 0.0
    assert calls["concat"] == []
    assert not mp3_path.exists(), "a partial passage was written to disk"
    # Every chunk was tried twice on audio.cpp before the service took over.
    n_chunks = len(p5._split_long_text(LONG_TEXT))
    assert result.attempts == 2 * n_chunks
    assert p5.audiocpp_fallbacks() == {21: 2 * n_chunks}


def test_single_chunk_failure_falls_back_to_the_service(monkeypatch, tmp_path):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_FISH_ROUTING", True)
    audiocpp_calls: list[str] = []

    def _adapter(**kwargs):
        audiocpp_calls.append(kwargs["text"])
        return None

    monkeypatch.setattr(p5, "audiocpp_fish_audio", _adapter)
    monkeypatch.setattr(p5, "fishaudio_tts", lambda **kw: b"SERVICE")
    calls = _patch_audio_seams(monkeypatch, p5)

    result, mp3_path = _call(p5, _build_seg(seg_index=22), "Une phrase courte.", tmp_path)

    assert result.status == "generated", result
    assert len(audiocpp_calls) == 2  # initial render + thermal retry
    assert mp3_path.read_bytes() == b"SERVICE"
    assert calls["concat"] == [[b"SERVICE"]]  # the service rendered the segment
    assert p5.audiocpp_fallbacks() == {22: 2}


# ---------------------------------------------------------------------------
# The adapter's request
# ---------------------------------------------------------------------------


def _fake_requests(monkeypatch, p5, post):
    """Replace the module's `requests` so no real HTTP leaves the test."""
    monkeypatch.setattr(
        p5,
        "requests",
        types.SimpleNamespace(
            post=post,
            RequestException=requests_lib.RequestException,
            HTTPError=requests_lib.HTTPError,
        ),
    )


def test_adapter_builds_the_openai_speech_payload(monkeypatch):
    import v4.p5_tts as p5

    monkeypatch.setattr(
        p5, "_audiocpp_reference", lambda reference_id: ("QkFTRTY0", "Transcript.")
    )
    monkeypatch.setattr(p5, "_wav_to_mp3", lambda wav: b"MP3")
    seen: dict = {}

    class _Resp:
        content = b"RIFFwav"

        def raise_for_status(self):
            return None

    def _post(url, json=None, timeout=None):
        seen.update(url=url, payload=json, timeout=timeout)
        return _Resp()

    _fake_requests(monkeypatch, p5, _post)

    out = p5.audiocpp_fish_audio(
        "Bonjour.", reference_id="v4_narrator_male_neutral", seed=61,
        temperature=0.7, top_p=0.9,
    )

    assert out == b"MP3"
    assert seen["url"] == f"{p5._AUDIOCPP_FISH_BASE_URL}/v1/audio/speech"
    payload = seen["payload"]
    assert payload["model"] == p5._AUDIOCPP_FISH_MODEL
    assert payload["input"] == "Bonjour."
    assert payload["seed"] == 61
    assert payload["response_format"] == "wav"
    assert payload["voice_ref"] == {"type": "base64", "data": "QkFTRTY0"}
    assert payload["reference_text"] == "Transcript."
    assert payload["options"] == {"temperature": 0.7, "top_p": 0.9}


def test_adapter_returns_none_when_the_reference_is_unusable(monkeypatch):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_audiocpp_reference", lambda reference_id: None)
    _fake_requests(
        monkeypatch, p5,
        lambda *a, **kw: pytest.fail("no request is sent without a reference"),
    )
    assert p5.audiocpp_fish_audio("Bonjour.") is None


def test_adapter_returns_none_on_http_error(monkeypatch):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_audiocpp_reference", lambda reference_id: ("QkFTRTY0", "t"))

    class _Resp:
        status_code = 400
        text = '{"error":"unknown option temperature"}'

    def _post(url, json=None, timeout=None):
        raise requests_lib.HTTPError("400 Client Error", response=_Resp())

    _fake_requests(monkeypatch, p5, _post)
    assert p5.audiocpp_fish_audio("Bonjour.") is None


def test_adapter_returns_none_on_a_connection_error(monkeypatch):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_audiocpp_reference", lambda reference_id: ("QkFTRTY0", "t"))

    def _post(url, json=None, timeout=None):
        raise requests_lib.ConnectionError("refused")

    _fake_requests(monkeypatch, p5, _post)
    assert p5.audiocpp_fish_audio("Bonjour.") is None


def test_adapter_refuses_a_non_mp3_format(monkeypatch):
    import v4.p5_tts as p5

    with pytest.raises(ValueError):
        p5.audiocpp_fish_audio("Bonjour.", format="wav")


# ---------------------------------------------------------------------------
# The reference resolution
# ---------------------------------------------------------------------------


def test_reference_falls_back_to_the_samples_directory(monkeypatch, tmp_path):
    """The P1 manifest records absolute paths that break on another checkout."""
    import v4.p5_tts as p5

    manifest = tmp_path / "manifest.json"
    samples = tmp_path / "samples"
    samples.mkdir()
    (samples / "v4_narrator_male_neutral.mp3").write_bytes(b"ID3fake")
    manifest.write_text(json.dumps([{
        "reference_id": "v4_narrator_male_neutral",
        "sample_mp3_path": str(tmp_path / "elsewhere" / "gone.mp3"),
        "sample_text": "Les voyageurs se regardaient.",
    }]), encoding="utf-8")

    monkeypatch.setattr(p5, "_AUDIOCPP_REFERENCE_MANIFEST", manifest)
    monkeypatch.setattr(p5, "_mp3_to_wav_base64", lambda path: "QkFTRTY0")

    assert p5._audiocpp_reference("v4_narrator_male_neutral") == (
        "QkFTRTY0", "Les voyageurs se regardaient."
    )


def test_reference_is_none_for_an_unknown_id(monkeypatch, tmp_path):
    import v4.p5_tts as p5

    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps([{
        "reference_id": "someone_else",
        "sample_mp3_path": str(tmp_path / "x.mp3"),
        "sample_text": "",
    }]), encoding="utf-8")
    monkeypatch.setattr(p5, "_AUDIOCPP_REFERENCE_MANIFEST", manifest)

    assert p5._audiocpp_reference("v4_narrator_male_neutral") is None


def test_reference_is_none_without_a_manifest(monkeypatch, tmp_path):
    import v4.p5_tts as p5

    monkeypatch.setattr(p5, "_AUDIOCPP_REFERENCE_MANIFEST", tmp_path / "absent.json")
    assert p5._audiocpp_reference("v4_narrator_male_neutral") is None


def test_reference_is_cached_by_file_identity(monkeypatch, tmp_path):
    """The MP3->WAV conversion runs once per sample, not once per chunk."""
    import v4.p5_tts as p5

    mp3 = tmp_path / "narrator.mp3"
    mp3.write_bytes(b"ID3fake")
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps([{
        "reference_id": "v4_narrator_male_neutral",
        "sample_mp3_path": str(mp3),
        "sample_text": "t",
    }]), encoding="utf-8")
    monkeypatch.setattr(p5, "_AUDIOCPP_REFERENCE_MANIFEST", manifest)

    conversions: list[Path] = []

    def _convert(path):
        conversions.append(path)
        return "QkFTRTY0"

    monkeypatch.setattr(p5, "_mp3_to_wav_base64", _convert)

    for _ in range(3):
        assert p5._audiocpp_reference("v4_narrator_male_neutral") is not None
    assert len(conversions) == 1, conversions


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
