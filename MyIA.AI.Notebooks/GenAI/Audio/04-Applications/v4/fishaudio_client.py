"""FishAudio S2-Pro TTS client for the v4 audiobook pipeline.

Wraps the FishAudio Docker service (port 8197) with:
- Text-to-speech synthesis (``/v1/tts``)
- Voice reference management (``/v1/references/*``)
- Thermal GPU monitoring (reused from v3)
"""
from __future__ import annotations

import logging
import os
import subprocess
import time
from pathlib import Path

import requests
from dotenv import load_dotenv

# ---------------------------------------------------------------------------
# Environment & constants
# ---------------------------------------------------------------------------

_GENAI_DIR = Path(__file__).resolve().parents[2]  # GenAI/
load_dotenv(_GENAI_DIR / ".env")

FISHAUDIO_URL: str = os.getenv("FISHAUDIO_URL", "http://localhost:8197")
OUTPUT_DIR: Path = Path(__file__).resolve().parent / "outputs" / "tts_v4"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# TTS synthesis
# ---------------------------------------------------------------------------


def fishaudio_tts(
    text: str,
    reference_id: str = "",
    seed: int = 42,
    temperature: float = 0.7,
    top_p: float = 0.9,
    format: str = "mp3",
    timeout: int = 300,
) -> bytes | None:
    """Synthesize speech via ``POST /v1/tts``.

    Returns raw audio bytes on success, ``None`` on failure.
    Raises ``requests.HTTPError`` on non-2xx responses.
    """
    payload: dict = {
        "text": text,
        "seed": seed,
        "temperature": temperature,
        "top_p": top_p,
        "format": format,
    }
    if reference_id:
        payload["reference_id"] = reference_id

    try:
        resp = requests.post(
            f"{FISHAUDIO_URL}/v1/tts",
            json=payload,
            timeout=timeout,
        )
        resp.raise_for_status()
        return resp.content
    except requests.RequestException as exc:
        logger.error("FishAudio TTS error: %s", exc)
        return None


# ---------------------------------------------------------------------------
# Voice reference management
# ---------------------------------------------------------------------------


def upload_reference(reference_id: str, audio_path: str, text: str) -> bool:
    """Upload a voice reference via ``POST /v1/references/add``.

    Parameters
    ----------
    reference_id:
        Unique identifier for the reference voice.
    audio_path:
        Path to the audio sample file.
    text:
        Transcript of the audio sample.

    Returns ``True`` on success.
    """
    try:
        with open(audio_path, "rb") as audio_file:
            resp = requests.post(
                f"{FISHAUDIO_URL}/v1/references/add",
                data={"id": reference_id, "text": text},
                files={"audio": (Path(audio_path).name, audio_file, "audio/wav")},
                timeout=60,
            )
            resp.raise_for_status()
            logger.info("Uploaded reference '%s'", reference_id)
            return True
    except requests.RequestException as exc:
        logger.error("Upload reference error: %s", exc)
        return False


def list_references() -> list[dict]:
    """List all voice references via ``GET /v1/references/list``."""
    try:
        resp = requests.get(
            f"{FISHAUDIO_URL}/v1/references/list",
            timeout=30,
        )
        resp.raise_for_status()
        return resp.json()  # type: ignore[no-any-return]
    except requests.RequestException as exc:
        logger.error("List references error: %s", exc)
        return []


def delete_reference(reference_id: str) -> bool:
    """Delete a voice reference via ``DELETE /v1/references/{id}``."""
    try:
        resp = requests.delete(
            f"{FISHAUDIO_URL}/v1/references/{reference_id}",
            timeout=30,
        )
        resp.raise_for_status()
        logger.info("Deleted reference '%s'", reference_id)
        return True
    except requests.RequestException as exc:
        logger.error("Delete reference error: %s", exc)
        return False


# ---------------------------------------------------------------------------
# Thermal GPU monitoring (reused from v3)
# ---------------------------------------------------------------------------


def get_gpu_temp() -> int:
    """Return GPU1 (index 1) temperature in Celsius via ``nvidia-smi``.

    Falls back to GPU0 if only one GPU is present.  Returns 0 on failure.
    """
    try:
        result = subprocess.run(
            [
                "nvidia-smi",
                "--query-gpu=temperature.gpu",
                "--format=csv,noheader,nounits",
            ],
            capture_output=True,
            text=True,
            timeout=5,
        )
        temps = [
            int(t.strip())
            for t in result.stdout.strip().split("\n")
            if t.strip()
        ]
        return temps[1] if len(temps) > 1 else temps[0] if temps else 0
    except Exception:
        return 0


def thermal_wait(max_temp: int = 82, cool_sleep: int = 20) -> int:
    """Sleep if GPU temperature exceeds *max_temp*.

    Returns the current temperature (after optional cooldown).
    """
    temp = get_gpu_temp()
    if temp > max_temp:
        logger.info(
            "GPU %dC > %dC, cooling %ds...", temp, max_temp, cool_sleep
        )
        time.sleep(cool_sleep)
    return temp


# ---------------------------------------------------------------------------
# Audio duration estimate
# ---------------------------------------------------------------------------


def audio_duration_mp3(mp3_bytes: bytes) -> float:
    """Estimate MP3 duration assuming 192 kbps bitrate.

    Uses a simple heuristic: ``duration = len(bytes) * 8 / 192_000``.
    """
    if not mp3_bytes:
        return 0.0
    return len(mp3_bytes) * 8 / 192_000


# ---------------------------------------------------------------------------
# Batch TTS with ThreadPoolExecutor
# ---------------------------------------------------------------------------


def fishaudio_tts_batch(
    requests: list[dict],
    max_workers: int = 4,
) -> list[bytes | None]:
    """Synthesize multiple texts concurrently via ``POST /v1/tts``.

    Parameters
    ----------
    requests:
        List of payload dicts (same kwargs as :func:`fishaudio_tts`).
    max_workers:
        Number of concurrent threads. The FishAudio server queues
        requests internally, so 3-4 workers saturate a single GPU well.

    Returns list of audio bytes (or ``None`` for failures), same order as input.
    """
    from concurrent.futures import ThreadPoolExecutor, as_completed

    results: list[bytes | None] = [None] * len(requests)

    def _call(idx: int, payload: dict) -> tuple[int, bytes | None]:
        audio = fishaudio_tts(**payload)
        return idx, audio

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {
            pool.submit(_call, i, req): i for i, req in enumerate(requests)
        }
        for future in as_completed(futures):
            idx, audio = future.result()
            results[idx] = audio

    return results
