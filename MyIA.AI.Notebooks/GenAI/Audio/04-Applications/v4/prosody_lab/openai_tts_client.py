"""OpenAI TTS client for the prosody lab (cloud benchmark target).

OpenAI TTS is the reference the local engines are measured against. The
user's standing complaint is that local clones sound monotone *compared to
OpenAI*, so OpenAI defines the expressivity targets (F0 semitone range,
F0 CV) on the same test segment.

Two models are exposed:
- ``tts-1-hd`` — the high-quality benchmark (fixed voices, no style prompt).
- ``gpt-4o-mini-tts`` — accepts an ``instructions`` style prompt, the cloud
  analogue of Qwen VoiceDesign, used for the controllability comparison.

Key is read from ``GenAI/.env`` (``OPENAI_API_KEY``) — never inlined.
"""
from __future__ import annotations

import logging
import os
from pathlib import Path

from dotenv import load_dotenv

def _genai_env() -> Path:
    """Locate GenAI/.env by walking up to the GenAI directory (depth-robust)."""
    here = Path(__file__).resolve()
    for parent in here.parents:
        if parent.name == "GenAI":
            return parent / ".env"
    # fallback: GenAI/Audio/04-Applications/v4/prosody_lab/<file> -> parents[4]
    return here.parents[4] / ".env"


_GENAI_ENV = _genai_env()
load_dotenv(_GENAI_ENV)

OPENAI_API_KEY: str | None = os.getenv("OPENAI_API_KEY")

logger = logging.getLogger(__name__)

# OpenAI native voices (tts-1-hd / gpt-4o-mini-tts).
OPENAI_VOICES = ["alloy", "echo", "fable", "onyx", "nova", "shimmer", "ash", "coral", "sage"]


def _client():
    if not OPENAI_API_KEY:
        raise RuntimeError("OPENAI_API_KEY missing from GenAI/.env")
    from openai import OpenAI

    return OpenAI(api_key=OPENAI_API_KEY)


def openai_tts(
    text: str,
    voice: str = "nova",
    model: str = "tts-1-hd",
    instructions: str | None = None,
    response_format: str = "mp3",
    speed: float = 1.0,
    timeout: int = 120,
) -> bytes | None:
    """Synthesize speech via the OpenAI TTS API.

    ``instructions`` is only honoured by ``gpt-4o-mini-tts`` (ignored by
    ``tts-1-hd``). Returns raw audio bytes on success, ``None`` on failure.
    """
    try:
        client = _client()
        kwargs: dict = {
            "model": model,
            "voice": voice,
            "input": text,
            "response_format": response_format,
            "speed": speed,
        }
        # Only gpt-4o-mini-tts accepts a style instruction prompt.
        if instructions and model == "gpt-4o-mini-tts":
            kwargs["instructions"] = instructions
        resp = client.audio.speech.create(timeout=timeout, **kwargs)
        return resp.content
    except Exception as exc:  # openai raises various subclasses
        logger.error("OpenAI TTS error (model=%s voice=%s): %s", model, voice, exc)
        return None


if __name__ == "__main__":
    import sys

    logging.basicConfig(level=logging.INFO)
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("openai_smoke.mp3")
    audio = openai_tts(
        text="Bonjour, ceci est un test du timbre de reference OpenAI.",
        voice="nova",
        model="tts-1-hd",
    )
    if audio:
        out.write_bytes(audio)
        print(f"OK: {len(audio)} bytes -> {out}")
    else:
        print("FAILED")
        sys.exit(1)
