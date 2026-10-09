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
