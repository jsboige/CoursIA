"""Qwen3-TTS client for the prosody lab (port 8196).

Wraps the self-hosted Qwen3-TTS service. Port 8196 (container ``tts-gateway``)
is the vLLM-Omni server itself, serving ``Qwen/Qwen3-TTS-12Hz-1.7B-VoiceDesign``
directly on OpenAI-compatible routes — the audio endpoint is ``/v1/audio/speech``
(verified live: ``GET /v1/models`` returns the VoiceDesign model, no ``/qwen/``
path prefix; an earlier prefix assumption returned 404).

Three task types are supported by the model (verified against the live
container's ``vllm_omni.entrypoints.openai.protocol.audio`` schema):

- **VoiceDesign** — a natural-language ``instructions`` prompt (<=500 chars)
  describes the voice and delivery. This is the "prosody prompt" capability:
  no reference audio, the voice is *designed* from the description.
- **CustomVoice** — a named native speaker (``voice`` field, e.g. "Vivian").
- **Base** — voice cloning from ``ref_audio`` + ``ref_text``.

The endpoint is OpenAI-compatible: ``{model, input, voice, instructions,
task_type, language, response_format, speed}``. Sampling temperature/top_p
are NOT request parameters; they come from the server stage config
(stage-0 temperature 0.9), so VoiceDesign output is mildly stochastic.
"""
from __future__ import annotations

import logging
import os
from pathlib import Path

import requests
from dotenv import load_dotenv

# ---------------------------------------------------------------------------
# Environment & constants
# ---------------------------------------------------------------------------

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

# vLLM-Omni base serving Qwen3-TTS-VoiceDesign directly (route /v1/audio/speech).
QWEN_GATEWAY_URL: str = os.getenv("QWEN_GATEWAY_URL", "http://localhost:8196")
QWEN_MODEL: str = "Qwen/Qwen3-TTS-12Hz-1.7B-VoiceDesign"

# Optional bearer for the gateway auth middleware (absent on localhost).
_TTS_KEY: str | None = os.getenv("TTS_GATEWAY_API_KEY") or os.getenv("KOKORO_API_KEY")

# Max instructions length enforced server-side (stage config tts_args).
MAX_INSTRUCTIONS_LEN: int = 500

logger = logging.getLogger(__name__)


def _headers() -> dict:
    headers = {"Content-Type": "application/json"}
    if _TTS_KEY:
        headers["Authorization"] = f"Bearer {_TTS_KEY}"
    return headers


def qwen_tts_voicedesign(
    text: str,
    instructions: str,
    language: str = "French",
    response_format: str = "wav",
    speed: float = 1.0,
    max_new_tokens: int = 2048,
    timeout: int = 300,
) -> bytes | None:
    """Synthesize speech via the VoiceDesign task.

    ``instructions`` is the natural-language description of the desired voice
    and delivery (required and non-empty for VoiceDesign). Returns raw audio
    bytes on success, ``None`` on failure.
    """
    instructions = (instructions or "").strip()
    if not instructions:
        raise ValueError("VoiceDesign requires a non-empty 'instructions' prompt")
    if len(instructions) > MAX_INSTRUCTIONS_LEN:
        logger.warning(
            "instructions length %d > %d; server will reject. Truncating.",
            len(instructions), MAX_INSTRUCTIONS_LEN,
        )
        instructions = instructions[:MAX_INSTRUCTIONS_LEN]

    payload: dict = {
        "model": QWEN_MODEL,
        "input": text,
        "task_type": "VoiceDesign",
        "instructions": instructions,
        "language": language,
        "response_format": response_format,
        "speed": speed,
        "max_new_tokens": max_new_tokens,
    }
    return _post_speech(payload, timeout)


def _split_sentences(text: str, max_chars: int = 160) -> list[str]:
    """Split text into sentence-level chunks, each <= max_chars where possible.

    Long-text VoiceDesign generation on the WSL engine (pin_memory=False,
    ~0.3-2.8 tok/s) takes minutes and exceeds the gateway's 300s upstream
    timeout, surfacing as a 503. Callers must therefore render long passages
    in shorter chunks. This splits on . ! ? ; keeping the delimiter, then
    merges adjacent short sentences up to ``max_chars``. A single sentence
    longer than ``max_chars`` is kept whole (no sub-sentence split, to
    preserve prosodic context).
    """
    import re

    parts = re.findall(r"[^.!?;]+[.!?;]*", text)
    chunks: list[str] = []
    cur = ""
    for raw in parts:
        p = raw.strip()
        if not p:
            continue
        if cur and len(cur) + 1 + len(p) > max_chars:
            chunks.append(cur)
            cur = p
        else:
            cur = f"{cur} {p}".strip() if cur else p
    if cur:
        chunks.append(cur)
    return chunks


def qwen_tts_voicedesign_chunked(
    text: str,
    instructions: str,
    language: str = "French",
    speed: float = 1.0,
    max_chars: int = 160,
    per_chunk_timeout: int = 290,
    gap_ms: int = 120,
) -> bytes | None:
    """VoiceDesign render of long text, chunked to stay under the gateway timeout.

    Renders each sentence-level chunk as WAV via :func:`qwen_tts_voicedesign`,
    concatenates them with a short silence gap, and returns a single WAV byte
    string. Mirrors how the v4 pipeline renders per-segment. Returns ``None``
    if any chunk fails (so a partial passage is never silently measured).
    """
    from io import BytesIO

    from pydub import AudioSegment

    chunks = _split_sentences(text, max_chars=max_chars)
    if not chunks:
        return None
    logger.info("VoiceDesign chunked render: %d chunk(s)", len(chunks))
    segments: list[AudioSegment] = []
    for i, ch in enumerate(chunks, start=1):
        audio = qwen_tts_voicedesign(
            ch,
            instructions=instructions,
            language=language,
            response_format="wav",
            speed=speed,
            timeout=per_chunk_timeout,
        )
        if not audio:
            logger.error(
                "chunk %d/%d failed (%d chars): %r", i, len(chunks), len(ch), ch[:60]
            )
            return None
        segments.append(AudioSegment.from_file(BytesIO(audio), format="wav"))
    combined = segments[0]
    gap = AudioSegment.silent(duration=gap_ms)
    for seg in segments[1:]:
        combined = combined + gap + seg
    buf = BytesIO()
    combined.export(buf, format="wav")
    return buf.getvalue()


def qwen_tts_customvoice(
    text: str,
    voice: str = "Vivian",
    instructions: str = "",
    language: str = "French",
    response_format: str = "wav",
    speed: float = 1.0,
    timeout: int = 300,
) -> bytes | None:
    """Synthesize via a named native speaker (CustomVoice task).

    ``instructions`` may optionally add a style hint on top of the speaker.
    """
    payload: dict = {
        "model": QWEN_MODEL,
        "input": text,
        "task_type": "CustomVoice",
        "voice": voice,
        "language": language,
        "response_format": response_format,
        "speed": speed,
    }
    if instructions.strip():
        payload["instructions"] = instructions.strip()[:MAX_INSTRUCTIONS_LEN]
    return _post_speech(payload, timeout)


def qwen_tts_clone(
    text: str,
    ref_audio: str,
    ref_text: str,
    language: str = "French",
    response_format: str = "wav",
    x_vector_only_mode: bool = False,
    timeout: int = 300,
) -> bytes | None:
    """Synthesize by cloning a reference voice (Base task).

    ``ref_audio`` is a URL, base64 string, or file path readable by the
    server; ``ref_text`` is its transcript. Used in the cloning-impact stage
    to compare native VoiceDesign against a clone of the same content.
    """
    payload: dict = {
        "model": QWEN_MODEL,
        "input": text,
        "task_type": "Base",
        "ref_audio": ref_audio,
        "ref_text": ref_text,
        "language": language,
        "response_format": response_format,
        "x_vector_only_mode": x_vector_only_mode,
    }
    return _post_speech(payload, timeout)


def _post_speech(payload: dict, timeout: int) -> bytes | None:
    try:
        resp = requests.post(
            f"{QWEN_GATEWAY_URL}/v1/audio/speech",
            json=payload,
            headers=_headers(),
            timeout=timeout,
        )
        if not resp.ok:
            body = resp.text[:500] if resp.text else "<empty>"
            logger.error(
                "Qwen TTS failed: status=%d task=%s body=%s",
                resp.status_code, payload.get("task_type"), body,
            )
            return None
        ctype = resp.headers.get("content-type", "")
        if "audio" not in ctype:
            logger.error("Qwen TTS non-audio response (%s): %s", ctype, resp.text[:300])
            return None
        return resp.content
    except requests.RequestException as exc:
        logger.error("Qwen TTS error: %s", exc)
        return None


if __name__ == "__main__":
    # Minimal CLI smoke test.
    import sys

    logging.basicConfig(level=logging.INFO)
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("qwen_smoke.wav")
    audio = qwen_tts_voicedesign(
        text="Bonjour, ceci est un test de prosodie expressive.",
        instructions=(
            "Une voix feminine francaise, chaleureuse et tres expressive, "
            "qui module fortement son intonation."
        ),
    )
    if audio:
        out.write_bytes(audio)
        print(f"OK: {len(audio)} bytes -> {out}")
    else:
        print("FAILED")
        sys.exit(1)
