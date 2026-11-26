"""_synthesize_narrator_customvoice (v4/p5_tts.py) — offline tests (#21145).

The successor of the wiring skeleton (#20925) ships the real chunked HTTP
call. These tests pin the no-silent-swap contract of #15002 acceptance 6 at
the p5 layer: an undefined endpoint, a gateway failure (client returns
None), and a short-audio render below the char-derived floor must ALL
surface as NarratorCustomVoiceUnavailable — never a silent short MP3, never
a fall back to FishAudio. The success path pins the transport contract the
issue prescribes: the published endpoint (base_url), speaker=serena,
instruct=None, gap-injected chunking.

Hermetic: the gateway client and pydub are faked through sys.modules —
no network, no ffmpeg (same pattern as test_p5_cv3_narrator).

Run from the v4 directory:
    python -m pytest tests/test_p5_customvoice_narrator.py -v
"""
from __future__ import annotations

import sys
import types
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def _build_seg(text="Il marcha longtemps dans la nuit, puis s'arreta."):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=888002,  # distinctive: no cached mp3 can match
        speaker="narrateur",
        type="narration",
        text=text,
        annotated_text=text,
    )


def _install_fake_runtime(monkeypatch, wav_s, mp3_dur, client_wav=b"FAKEWAV"):
    """Fake pydub + gateway client so the CustomVoice branch runs hermetically.

    Returns the recorder dict holding the kwargs p5 passed to the client.
    """
    import v4.prosody_lab.qwen_tts_client as client_mod

    recorder: dict = {}

    def fake_chunked(text, **kwargs):
        recorder["text"] = text
        recorder["kwargs"] = kwargs
        return client_wav

    monkeypatch.setattr(client_mod, "qwen_tts_customvoice_chunked", fake_chunked)

    pydub = types.ModuleType("pydub")

    class _FakeAudio:
        def __len__(self):  # milliseconds — the short-audio guard's input
            return int(wav_s * 1000)

        def export(self, buf, format=None, bitrate=None):
            buf.write(b"MP3")

        @staticmethod
        def from_file(buf, format=None):
            return _FakeAudio()

    pydub.AudioSegment = _FakeAudio
    monkeypatch.setitem(sys.modules, "pydub", pydub)
    monkeypatch.setattr("v4.p5_tts.audio_duration_mp3", lambda b: mp3_dur)
    return recorder


def test_customvoice_success_writes_mp3_and_sentinel(tmp_path, monkeypatch):
    """Success path: chunked WAV in, MP3 out, sentinel reference_id, and the
    transport contract of #21145 (published endpoint, serena, no instruct)."""
    from v4 import p5_tts

    monkeypatch.setenv(
        "NARRATOR_CUSTOMVOICE_GATEWAY_URL", "https://tts-api.myia.io/v1"
    )
    recorder = _install_fake_runtime(
        monkeypatch, wav_s=3.0, mp3_dur=2.9, client_wav=b"WAVBYTES"
    )
    seg = _build_seg()
    out = p5_tts._synthesize_narrator_customvoice(
        seg=seg,
        fishaudio_text=seg.text,
        mp3_path=tmp_path / "seg_0001_narrateur.mp3",
        seed=42,
        text_hash="hash1",
    )
    assert out.status == "generated"
    assert out.reference_id == p5_tts._CUSTOMVOICE_NARRATOR_REFERENCE_ID
    assert out.attempts == 1
    assert out.duration_s == 2.9
    assert out.mp3_path.endswith("seg_0001_narrateur.mp3")
    assert (tmp_path / "seg_0001_narrateur.mp3").read_bytes() == b"MP3"
    # Transport contract: the documented ".../v1" endpoint form is normalized
    # to the gateway base (the client appends /v1/audio/speech itself),
    # neutral render (speaker serena, EMPTY instructions by default),
    # French, gap-injected.
    kw = recorder["kwargs"]
    assert kw["base_url"] == "https://tts-api.myia.io"
    assert kw["model"] == p5_tts._CUSTOMVOICE_SERVED_MODEL
    assert kw["voice"] == "serena"
    assert kw["instructions"] == ""
    assert kw["language"] == "French"
    assert kw["gap_ms"] == 120
    assert kw["max_chars"] == p5_tts._MAX_CHUNK_CHARS


def test_customvoice_no_audio_raises(tmp_path, monkeypatch):
    """A gateway failure (4xx/5xx/unreachable/failed chunk — the client
    returns None) raises NarratorCustomVoiceUnavailable: never a fall back
    to FishAudio (#15002 acceptance 6)."""
    from v4 import p5_tts

    monkeypatch.setenv(
        "NARRATOR_CUSTOMVOICE_GATEWAY_URL", "https://tts-api.myia.io/v1"
    )
    _install_fake_runtime(monkeypatch, wav_s=3.0, mp3_dur=2.9, client_wav=None)
    seg = _build_seg()
    mp3 = tmp_path / "should_never_exist.mp3"
    try:
        p5_tts._synthesize_narrator_customvoice(
            seg=seg, fishaudio_text=seg.text, mp3_path=mp3,
            seed=42, text_hash="hash2",
        )
    except p5_tts.NarratorCustomVoiceUnavailable as exc:
        assert "no audio" in str(exc)
    else:
        raise AssertionError("no-audio response did not raise")
    assert not mp3.exists()


def test_customvoice_short_audio_raises(tmp_path, monkeypatch):
    """A WAV below the char-derived floor is a degenerate render, not fast
    speech: it raises instead of becoming a silent short MP3 (the same gross
    backstop as the CV3 guard, #19692)."""
    from v4 import p5_tts

    monkeypatch.setenv(
        "NARRATOR_CUSTOMVOICE_GATEWAY_URL", "https://tts-api.myia.io/v1"
    )
    # 80 chars -> floor 2.0 s; the fake renders only 0.5 s.
    text = "Il marcha longtemps dans la nuit obscure et froide du vieux chateau."
    assert len(text) / p5_tts._CUSTOMVOICE_MIN_CHARS_PER_SEC > 0.5
    _install_fake_runtime(monkeypatch, wav_s=0.5, mp3_dur=0.5)
    seg = _build_seg(text=text)
    mp3 = tmp_path / "should_never_exist_short.mp3"
    try:
        p5_tts._synthesize_narrator_customvoice(
            seg=seg, fishaudio_text=text, mp3_path=mp3,
            seed=42, text_hash="hash3",
        )
    except p5_tts.NarratorCustomVoiceUnavailable as exc:
        assert "short audio" in str(exc)
    else:
        raise AssertionError("short-audio render did not raise")
    assert not mp3.exists()
