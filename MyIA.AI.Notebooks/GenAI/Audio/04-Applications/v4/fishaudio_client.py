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
    timeout: int = 600,
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

    Returns ``True`` on success.  HTTP 409 ("already exists") is treated
    as idempotent success so re-running P1 does not regress prior clones.
    On any failure, response status + body are logged for diagnosis.
    """
    try:
        with open(audio_path, "rb") as audio_file:
            resp = requests.post(
                f"{FISHAUDIO_URL}/v1/references/add",
                data={"id": reference_id, "text": text},
                files={
                    "audio": (
                        Path(audio_path).name,
                        audio_file,
                        "audio/mpeg",
                    )
                },
                timeout=60,
            )
        if resp.ok:
            logger.info("Uploaded reference '%s'", reference_id)
            return True
        if resp.status_code == 409:
            logger.info(
                "Reference '%s' already exists on server (idempotent)",
                reference_id,
            )
            return True
        body = resp.text[:500] if resp.text else "<empty>"
        logger.error(
            "Upload reference '%s' failed: status=%d body=%s",
            reference_id, resp.status_code, body,
        )
        return False
    except requests.RequestException as exc:
        body = "<no response>"
        status: int | None = None
        if hasattr(exc, "response") and exc.response is not None:
            body = exc.response.text[:500]
            status = exc.response.status_code
        logger.error(
            "Upload reference '%s' error: status=%s body=%s exc=%s",
            reference_id, status, body, exc,
        )
        return False


def list_references() -> dict:
    """List all voice references via ``GET /v1/references/list``.

    Requests JSON explicitly because the FishAudio server defaults to
    msgpack which silently breaks ``resp.json()``.  Returns the parsed
    dict ``{"success": bool, "reference_ids": [str], "message": str}``
    or an empty dict on failure.
    """
    try:
        resp = requests.get(
            f"{FISHAUDIO_URL}/v1/references/list",
            headers={"Accept": "application/json"},
            timeout=30,
        )
        resp.raise_for_status()
        return resp.json()  # type: ignore[no-any-return]
    except requests.RequestException as exc:
        logger.error("List references error: %s", exc)
        return {}


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


def thermal_backoff(
    target_temp: int = 72,
    max_temp: int = 80,
    base_sleep: float = 3.0,
    max_sleep: float = 30.0,
) -> int:
    """Adaptive thermal pause between TTS generations.

    Strategy (similar to QC training thermal management):
      - Below *target_temp*: minimal pause (base_sleep) to maintain airflow.
      - Between *target_temp* and *max_temp*: progressive backoff,
        scaling from base_sleep to max_sleep linearly with temperature.
      - Above *max_temp*: full max_sleep cooldown and re-check.

    Returns current GPU temperature after the pause.
    """
    temp = get_gpu_temp()
    if temp == 0:
        # nvidia-smi unavailable (unlikely on this machine) — no pause
        return 0

    if temp <= target_temp:
        # Light pause — keeps GPU from heat-soaking between bursts
        time.sleep(base_sleep)
    elif temp <= max_temp:
        # Progressive backoff: scale sleep from base_sleep to max_sleep
        ratio = (temp - target_temp) / (max_temp - target_temp)
        sleep_time = base_sleep + ratio * (max_sleep - base_sleep)
        logger.info(
            "GPU %dC (warm), throttling %.1fs (ratio %.0f%%)...",
            temp, sleep_time, ratio * 100,
        )
        time.sleep(sleep_time)
    else:
        # Over threshold — full cooldown until temperature drops
        while temp > target_temp:
            logger.info(
                "GPU %dC > %dC, cooling %ds...",
                temp, max_temp, int(max_sleep),
            )
            time.sleep(max_sleep)
            temp = get_gpu_temp()

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
