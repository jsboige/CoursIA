"""_split_sentences (prosody_lab/qwen_tts_client.py) — offline tests.

The function saw two consecutive defects: a punctuation-only part forming
its own chunk (commit 0e987cd6 — the gateway answers HTTP 500 "No audio
segments generated" and qwen_tts_voicedesign_chunked treats any failed chunk
as fatal), then the residual case of a text OPENING on such a part (review
of #19453 — the orphan glyph seeded the chunk instead). These tests pin both
sides of the contract so neither regresses.

Run from the v4 directory:
    python -m pytest tests/test_qwen_tts_client.py -v
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def test_closing_punctuation_attaches_to_current_chunk():
    """A punctuation-only part CLOSES the running sentence: it joins the
    current chunk with no space, and never forms its own chunk (the gateway
    renders no audio for it — HTTP 500)."""
    from v4.prosody_lab.qwen_tts_client import _split_sentences

    chunks = _split_sentences('Il dit : "Voila." ». Puis il se tait.')
    assert chunks == ['Il dit : "Voila." ». Puis il se tait.']
    for c in chunks:
        assert re.search(r"[^\W_]", c), f"chunk sans alphanumerique: {c!r}"


def test_leading_orphan_punctuation_does_not_seed_a_chunk():
    """A punctuation-only part with NO running chunk (text opening on an
    orphan closing quote) has nothing to close: seeding the chunk with it
    would send a leading bare glyph to the gateway (review of #19453)."""
    from v4.prosody_lab.qwen_tts_client import _split_sentences

    chunks = _split_sentences("»; Bonjour le monde.")
    assert chunks == ["Bonjour le monde."]


class _FakeResp:
    ok = True
    status_code = 200
    text = ""
    headers = {"content-type": "audio/wav"}
    content = b"WAVBYTES"


def test_post_speech_overrides_url_and_bearer(monkeypatch):
    """Per-call overrides (#21145): base_url/api_key/model route the request
    at the published gateway instead of the local :8196 socket, without
    touching the module constants for other callers."""
    import v4.prosody_lab.qwen_tts_client as client

    seen: dict = {}

    def fake_post(url, json=None, headers=None, timeout=None):
        seen["url"] = url
        seen["payload"] = json
        seen["headers"] = headers
        return _FakeResp()

    monkeypatch.setattr(client.requests, "post", fake_post)
    out = client.qwen_tts_customvoice(
        "Bonjour.",
        voice="serena",
        # base_url is the gateway BASE (no /v1): _post_speech appends the
        # route itself. The p5 layer normalizes the documented ".../v1" form.
        base_url="https://tts-api.myia.io",
        api_key="secret-key",
        model="custom-voice-checkpoint",
    )
    assert out == b"WAVBYTES"
    assert seen["url"] == "https://tts-api.myia.io/v1/audio/speech"
    assert seen["headers"]["Authorization"] == "Bearer secret-key"
    assert seen["payload"]["model"] == "custom-voice-checkpoint"
    assert seen["payload"]["task_type"] == "CustomVoice"
    assert seen["payload"]["voice"] == "serena"


def test_customvoice_chunked_forwards_overrides_and_gaps(monkeypatch):
    """qwen_tts_customvoice_chunked threads the overrides to every chunk and
    concatenates with the silence gap (transport parallel of the VoiceDesign
    chunked path) — None on any chunk failure, never a partial passage."""
    import sys
    import types

    import v4.prosody_lab.qwen_tts_client as client

    calls: list[dict] = []

    def fake_cv(text, **kw):
        calls.append({"text": text, **kw})
        return b"WAVBYTES"

    monkeypatch.setattr(client, "qwen_tts_customvoice", fake_cv)

    pydub = types.ModuleType("pydub")

    class _FakeAudio:
        def __init__(self, tag):
            self.tag = tag

        def __add__(self, other):
            return _FakeAudio(f"{self.tag}+{getattr(other, 'tag', 'gap')}")

        def export(self, buf, format=None):
            buf.write(b"COMBINEDWAV")

        @staticmethod
        def from_file(buf, format=None):
            return _FakeAudio("chunk")

        @staticmethod
        def silent(duration=None):
            return _FakeAudio("gap")

    pydub.AudioSegment = _FakeAudio
    monkeypatch.setitem(sys.modules, "pydub", pydub)

    text = "Premiere phrase assez longue pour exister seule. " * 2
    out = client.qwen_tts_customvoice_chunked(
        text,
        voice="serena",
        base_url="https://tts-api.myia.io",
        api_key="k",
        model="m",
        gap_ms=120,
        max_chars=40,  # force one chunk per sentence (each is ~48 chars)
    )
    assert out == b"COMBINEDWAV"
    assert len(calls) >= 2, "two sentence chunks expected"
    for c in calls:
        assert c["base_url"] == "https://tts-api.myia.io"
        assert c["api_key"] == "k"
        assert c["model"] == "m"
        assert c["voice"] == "serena"

    # A failed chunk returns None — a partial passage is never measured.
    monkeypatch.setattr(
        client, "qwen_tts_customvoice", lambda text, **kw: None
    )
    assert client.qwen_tts_customvoice_chunked(text, voice="serena") is None
