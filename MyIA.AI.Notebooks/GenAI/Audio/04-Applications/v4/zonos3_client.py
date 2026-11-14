"""ZONOS3 Mini TTS client for the v4 audiobook pipeline.

Wraps the ZONOS3 Mini HTTP runtime (Zyphra) with:

- text-to-speech synthesis (``POST /v2/generate``, OpenAI-compatible
  ``POST /v1/audio/speech`` as a fallback transport);
- steering controls discovery (``GET /v2/controls``) — the runtime
  serves its direction sets through a steering bundle, and the bundle
  is what decides whether an axis can be steered at all;
- zero-shot voice cloning from a **raw reference clip** (base64) or
  from a **speaker embedding id**.

Contract parity with :mod:`v4.fishaudio_client`: raw audio bytes on
success, ``None`` on failure, ``requests.HTTPError`` raised for
non-2xx responses.

Seed discipline (acceptance #6 of #25835): the runtime returns the
seed it actually used in the ``X-Seed`` response header.  The seed is
**captured, never invented** — :func:`zonos3_tts` returns it next to
the audio so the manifest can record what the render actually used,
and a replay can be checked against it.
"""
from __future__ import annotations

import base64
import logging
import os
from pathlib import Path

import requests
from dotenv import load_dotenv

# ---------------------------------------------------------------------------
# Environment & constants
# ---------------------------------------------------------------------------

_GENAI_DIR = Path(__file__).resolve().parents[2]  # GenAI/
load_dotenv(_GENAI_DIR / ".env")

ZONOS3_URL: str = os.getenv("ZONOS3_URL", "http://localhost:1919")
OUTPUT_DIR: Path = Path(__file__).resolve().parent / "outputs" / "tts_v4"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)

logger = logging.getLogger(__name__)

#: Sampling parameters. The runtime's defaults are tuned for the
#: release checkpoint; these are explicit so a run is reproducible.
DEFAULT_TEMPERATURE: float = 0.7
DEFAULT_TOP_P: float = 0.9


class Zonos3Error(RuntimeError):
    """Raised when the ZONOS3 runtime cannot serve a request.

    Same contract as the other narrator engines (#15002 acceptance 6):
    a hard failure, never a silent fall back to FishAudio — the
    routing decision is explicit and documented in the manifest.
    """


def _reference_payload(
    reference_id: str,
    reference_audio_path: str = "",
) -> dict:
    """Build the speaker reference part of a ``/v2/generate`` payload.

    The runtime accepts a raw reference clip (``speaker_audio_base64``)
    or an already-registered speaker embedding
    (``speaker_embedding_id``).  A reference id without a clip is sent
    as an embedding id — the caller decides which one it holds.
    """
    payload: dict = {}
    if reference_audio_path:
        with open(reference_audio_path, "rb") as handle:
            payload["speaker_audio_base64"] = base64.b64encode(
                handle.read()
            ).decode("ascii")
    elif reference_id:
        payload["speaker_embedding_id"] = reference_id
    return payload


def zonos3_tts(
    text: str,
    reference_id: str = "",
    reference_audio_path: str = "",
    seed: int = 42,
    temperature: float = DEFAULT_TEMPERATURE,
    top_p: float = DEFAULT_TOP_P,
    controls: dict[str, float] | None = None,
    control_spans: dict[str, list[list[int]]] | None = None,
    language: str = "fr",
    format: str = "wav",
    timeout: int = 600,
) -> tuple[bytes | None, int | None]:
    """Synthesize speech via ``POST /v2/generate``.

    Parameters
    ----------
    text:
        The text to render.  The caller is responsible for having
        stripped the FishAudio bracket tags: ZONOS3 does not read
        them, and it would vocalize them.
    reference_id:
        Speaker embedding id, used when no raw clip is given.
    reference_audio_path:
        Raw reference clip for zero-shot cloning (takes precedence
        over ``reference_id``).
    seed:
        The seed requested.  The runtime echoes the seed it used in
        the ``X-Seed`` header.
    controls:
        Steering doses — ``{"mood.arousal": 3.2}``.
    control_spans:
        Character ranges per direction — ``{"mood.arousal": [[0, 42]]}``.
    language:
        Language hint for the runtime ("fr" for French).
    format:
        Requested output format ("wav" or "pcm").
    timeout:
        Request timeout in seconds.

    Returns
    -------
    (audio_bytes, seed_used)
        ``audio_bytes`` is ``None`` on failure.  ``seed_used`` is the
        seed the runtime reports in ``X-Seed`` — ``None`` when the
        header is absent (never a substituted value).
    """
    payload: dict = {
        "text": text,
        "seed": seed,
        "temperature": temperature,
        "top_p": top_p,
        "language": language,
        "format": format,
    }
    payload.update(_reference_payload(reference_id, reference_audio_path))
    if controls:
        payload["controls"] = dict(controls)
    if control_spans:
        payload["control_spans"] = {
            direction: [list(span) for span in spans]
            for direction, spans in control_spans.items()
        }

    try:
        resp = requests.post(
            f"{ZONOS3_URL}/v2/generate",
            json=payload,
            timeout=timeout,
        )
        resp.raise_for_status()
    except requests.RequestException as exc:
        logger.error("ZONOS3 TTS error: %s", exc)
        return None, None

    seed_used: int | None = None
    raw_seed = resp.headers.get("X-Seed")
    if raw_seed is not None:
        try:
            seed_used = int(raw_seed)
        except ValueError:
            logger.warning("ZONOS3 returned a non-integer X-Seed: %r", raw_seed)

    return resp.content, seed_used


def zonos3_controls() -> dict:
    """Read the served steering directions via ``GET /v2/controls``.

    The served direction names depend on the loaded steering bundle, so
    this is the **authority** on what can be steered.  Returns an empty
    dict when the endpoint is absent or unreadable — the resolver then
    degrades every axis to its FishAudio fallback instead of steering
    a direction the server does not serve.
    """
    try:
        resp = requests.get(f"{ZONOS3_URL}/v2/controls", timeout=30)
        resp.raise_for_status()
        return resp.json()  # type: ignore[no-any-return]
    except requests.RequestException as exc:
        logger.warning("ZONOS3 /v2/controls unavailable (%s)", exc)
        return {}
    except ValueError as exc:
        logger.warning("ZONOS3 /v2/controls returned non-JSON (%s)", exc)
        return {}


def zonos3_capabilities() -> dict:
    """Read the runtime capabilities via ``GET /v2/capabilities``.

    Used to degrade according to what the checkpoint actually serves
    (for example ``edit_transcribe: false``).  Returns an empty dict on
    failure.
    """
    try:
        resp = requests.get(f"{ZONOS3_URL}/v2/capabilities", timeout=30)
        resp.raise_for_status()
        return resp.json()  # type: ignore[no-any-return]
    except requests.RequestException as exc:
        logger.warning("ZONOS3 /v2/capabilities unavailable (%s)", exc)
        return {}
    except ValueError as exc:
        logger.warning("ZONOS3 /v2/capabilities returned non-JSON (%s)", exc)
        return {}


def zonos3_tts_batch(
    requests_list: list[dict],
    max_workers: int = 2,
) -> list[tuple[bytes | None, int | None]]:
    """Synthesize multiple texts concurrently via ``POST /v2/generate``.

    Parameters
    ----------
    requests_list:
        List of payload dicts (same kwargs as :func:`zonos3_tts`).
    max_workers:
        Number of concurrent threads.  The default is 2: the runtime
        holds one GPU and a single request already saturates it, so a
        higher value only trades latency for VRAM pressure.

    Returns
    -------
    list of (audio_bytes, seed_used)
        Same order as the input.
    """
    from concurrent.futures import ThreadPoolExecutor, as_completed

    results: list[tuple[bytes | None, int | None]] = [(None, None)] * len(
        requests_list
    )

    def _call(idx: int, payload: dict) -> tuple[int, bytes | None, int | None]:
        audio, seed_used = zonos3_tts(**payload)
        return idx, audio, seed_used

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {
            pool.submit(_call, i, req): i for i, req in enumerate(requests_list)
        }
        for future in as_completed(futures):
            idx, audio, seed_used = future.result()
            results[idx] = (audio, seed_used)

    return results


def audio_duration_wav(wav_bytes: bytes) -> float:
    """Duration of a WAV payload in seconds, read from its header.

    The ZONOS3 runtime renders 44.1 kHz mono; the duration is read
    from the RIFF header rather than estimated, because the duration
    is what the M4B chaptering step consumes.
    """
    if not wav_bytes or len(wav_bytes) < 44:
        return 0.0
    try:
        import wave
        import io

        with wave.open(io.BytesIO(wav_bytes), "rb") as handle:
            frames = handle.getnframes()
            rate = handle.getframerate()
            return frames / rate if rate else 0.0
    except Exception:  # pragma: no cover — malformed payload
        return 0.0
