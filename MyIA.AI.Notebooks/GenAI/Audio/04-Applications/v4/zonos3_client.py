"""ZONOS3 Mini TTS client for the v4 audiobook pipeline.

Wraps the ZONOS3 Mini HTTP runtime (Zyphra) served by the ``tts-zonos3``
container (``docker-configurations/services/tts-zonos3``, backend
ggml/CUDA), with:

- text-to-speech synthesis (``POST /v2/generate``);
- on-demand wake of the local container (:func:`zonos3_ensure_up`);
- steering controls discovery (``GET /v2/controls``) — the runtime
  serves its direction sets through a steering bundle, and the bundle
  is what decides whether an axis can be steered at all;
- voice selection by **speaker embedding id** served by the checkpoint,
  or zero-shot cloning from a **raw reference clip** (base64).

The wire contract coded here was **measured** on the delivered service
(2026-11-27; runtime code pinned at ``a50e14117d99`` and weights at
``2921b8821772`` on Hugging Face):

- ``language`` must be one of the codes the server lists.  French is
  ``fr_fr``; ``fr`` is answered ``400 Unsupported language code``.
- ``format: "wav"`` requires ``stream: false``.  The server default is
  ``stream: true``, and a WAV request that omits the field is answered
  ``400 format=wav needs stream=false``.  This client always sends it.
- ``control_spans`` is a **list** of ``{"start", "end", "controls"}``
  objects, offsets counted in **code points of the request text**, end
  exclusive.  The per-direction dict form is answered ``422 unexpected
  instance type``; a span outside ``[0, len(text)]`` (beyond the text,
  reversed or empty) is answered ``400 control span [a, b) is outside
  the text`` and the **whole request** fails.
- ``speaker_embedding_id`` must be an id of ``GET /v2/speakers``.  The
  only French voice of the pinned checkpoint is
  ``default_517319c805b927e9`` ("Gaspard fr M 1").
- with ``ZONOS3_ACCESS_TOKEN`` armed on the server, **every** route
  requires ``Authorization: Bearer <token>`` (``403`` otherwise).
- one request renders at most :data:`MAX_RENDER_SECONDS` of audio —
  1 991 audio frames, 132.733 s.  ``GET /v2/capabilities`` announces
  ``max_tokens: 2000`` and the prompt occupies 9 rows of it (measured:
  ``max_tokens: 1000`` renders 991 frames, ``max_tokens: 50`` renders
  41); ``max_tokens: 4000`` changes nothing (byte-identical audio).
  A longer text is **cut, not refused**, and no header says so: a 200
  response carries ``X-Decoder``, ``X-Seed``, ``X-Audio-Format``,
  ``X-Audio-Channels`` and ``X-Audio-Sample-Rate``, plus
  ``X-Control-Span-Follow`` when the request had spans.  A render that
  ends at the ceiling is therefore a **cut render**, and the caller
  keeps its segments under it.

Steering doses are **calibrated absolutes**, not magnitudes from zero:
``GET /v2/controls`` publishes the neutral dose of each direction
(``sets.<set>.calibration.default`` — 4.0 on the ``mood`` axes, 2.0 on
loudness and clarity), so a dose below the neutral steers the opposite
way.  :mod:`v4.zonos3_steering` centres its doses on that calibration.

Contract parity with :mod:`v4.fishaudio_client`: raw audio bytes on
success, ``None`` on failure, no exception leaking out of the client.

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
import sys
from pathlib import Path
from urllib.parse import urlparse

import requests
from dotenv import load_dotenv

# ---------------------------------------------------------------------------
# Environment & constants
# ---------------------------------------------------------------------------
# The shared env file of the GenAI tree is ``GenAI/.env`` — the one
# ``llm_client.py`` and ``diarization_client.py`` read.  ``v4/`` sits three
# levels below it (GenAI/Audio/04-Applications/v4), so ``parents[2]`` named
# ``Audio/``, where no ``.env`` exists: the load was a silent no-op and every
# key fell back to its hard-coded default.
_GENAI_DIR = Path(__file__).resolve().parents[3]  # GenAI/
load_dotenv(_GENAI_DIR / ".env", override=False)

ZONOS3_URL: str = os.getenv("ZONOS3_URL", "http://localhost:1919")
# Optional access token, the same variable name as on the server's side.
# Armed there, every route answers 403 unless the request bears it.
ZONOS3_ACCESS_TOKEN: str = os.getenv("ZONOS3_ACCESS_TOKEN", "")
OUTPUT_DIR: Path = Path(__file__).resolve().parent / "outputs" / "tts_v4"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)

logger = logging.getLogger(__name__)

#: Sampling parameters. The runtime's defaults are tuned for the
#: release checkpoint; these are explicit so a run is reproducible.
DEFAULT_TEMPERATURE: float = 0.7
DEFAULT_TOP_P: float = 0.9

#: Language code the server lists for French.  ``fr`` is a 400.
FRENCH_LANGUAGE_CODE: str = "fr_fr"

#: Frame budget of one request: ``GET /v2/capabilities`` announces
#: ``max_tokens: 2000``.  The prompt occupies :data:`PROMPT_FRAME_OVERHEAD`
#: rows that the budget does not cover — measured 2026-11-27 on the
#: delivered service: default -> 1 991 audio frames, ``max_tokens: 1000``
#: -> 991 frames, ``max_tokens: 50`` -> 41 frames (a constant 9).
MAX_AUDIO_FRAMES: int = 2000
PROMPT_FRAME_OVERHEAD: int = 9
#: One audio frame is 2 940 samples at 44.1 kHz, i.e. 1/15 s.
FRAME_SECONDS: float = 1.0 / 15.0
#: Longest render one request can produce: (2 000 - 9) x 1/15 s = 132.733 s.
#: Past it the render is **cut without any signal**, so a duration at this
#: value is a cut render, not a long one.
MAX_RENDER_SECONDS: float = (
    (MAX_AUDIO_FRAMES - PROMPT_FRAME_OVERHEAD) * FRAME_SECONDS
)
#: Advisory text length past which a French render reaches the ceiling
#: (measured: 2 682 characters -> 132.73 s, and 4 120 characters -> the
#: same 132.73 s).  A warning only: the ceiling counts audio frames, and
#: the speaking rate decides how much text fits in them.
ADVISORY_TEXT_CHARS: int = 2700

#: Docker container of the service, and the path its compose healthcheck
#: reads.  The runtime cannot put its model to sleep, so the container
#: lives only as long as it is used and must be started on demand.
CONTAINER_NAME: str = "tts-zonos3"
HEALTH_PATH: str = "/v2/health"

#: Hosts whose container this machine is allowed to start.  A ``ZONOS3_URL``
#: on any other host is someone else's service: it is used, never woken.
_LOCAL_HOSTS: frozenset[str] = frozenset({"localhost", "127.0.0.1", "::1"})

#: Where the shared wake organ lives in the repository
#: (``ensure_service_up`` in ``service_wake.py``, #2998).
_SHARED_SERVICES_DIR: Path = (
    Path(__file__).resolve().parents[5]
    / "docker-configurations"
    / "services"
    / "shared"
)


class Zonos3Error(RuntimeError):
    """Raised when the ZONOS3 runtime cannot serve a request.

    Same contract as the other narrator engines (#15002 acceptance 6):
    a hard failure, never a silent fall back to FishAudio — the
    routing decision is explicit and documented in the manifest.
    """


def _auth_headers() -> dict[str, str]:
    """Bearer header for one request; empty when no token is configured."""
    if ZONOS3_ACCESS_TOKEN:
        return {"Authorization": f"Bearer {ZONOS3_ACCESS_TOKEN}"}
    return {}


def _is_local_url(url: str) -> bool:
    """True when ``url`` points at this machine (loopback)."""
    return (urlparse(url).hostname or "").lower() in _LOCAL_HOSTS


# ---------------------------------------------------------------------------
# Wake
# ---------------------------------------------------------------------------
def _import_ensure_service_up():
    """Import the shared wake organ, or ``None`` when it is not reachable.

    ``service_wake.py`` lives in ``docker-configurations/services/shared/``,
    outside the GenAI tree.  It is the one implementation of "probe, then
    ``docker start``, then poll"; this module does not re-implement it.
    """
    if not (_SHARED_SERVICES_DIR / "service_wake.py").exists():
        return None
    if str(_SHARED_SERVICES_DIR) not in sys.path:
        sys.path.insert(0, str(_SHARED_SERVICES_DIR))
    try:
        from service_wake import ensure_service_up  # type: ignore
    except ImportError:
        return None
    return ensure_service_up


def _probe_health(health_url: str, timeout: float = 5.0) -> bool:
    """True when ``health_url`` answers 200 (the token is presented if set)."""
    try:
        resp = requests.get(health_url, headers=_auth_headers(), timeout=timeout)
    except requests.RequestException:
        return False
    return resp.status_code == 200


def zonos3_ensure_up(timeout: int = 180, poll_interval: int = 2) -> bool:
    """Make sure the service answers ``/v2/health`` before a batch starts.

    The ``tts-zonos3`` container is started on demand and never idles
    resident (its runtime cannot sleep its model), so a cold pipeline
    meets a stopped container.  This probes the health route and, when it
    does not answer, starts the container through the shared wake organ
    and polls until it is healthy.

    Only a loopback ``ZONOS3_URL`` is woken: a remote host is not this
    machine's container to start, and the function then returns ``True``
    without probing (the request itself will tell).

    Parameters
    ----------
    timeout:
        Seconds to wait for health after ``docker start``.
    poll_interval:
        Seconds between two health probes.

    Returns
    -------
    bool
        ``True`` when the service is healthy, or when ``ZONOS3_URL`` is
        not loopback.  ``False`` when it could not be brought up — the
        caller decides, no exception is raised for a service failure.
    """
    if not _is_local_url(ZONOS3_URL):
        logger.info(
            "ZONOS3_URL=%s is not loopback: no container to wake", ZONOS3_URL
        )
        return True

    health_url = f"{ZONOS3_URL}{HEALTH_PATH}"
    ensure_service_up = _import_ensure_service_up()
    if ensure_service_up is None:
        # Without the organ only an already-running service can answer.
        logger.warning(
            "service_wake.py not found under %s: ZONOS3 cannot be started "
            "here, probing %s only",
            _SHARED_SERVICES_DIR,
            HEALTH_PATH,
        )
        return _probe_health(health_url)

    return bool(
        ensure_service_up(
            CONTAINER_NAME,
            health_url,
            api_key=ZONOS3_ACCESS_TOKEN or None,
            timeout=timeout,
            poll_interval=poll_interval,
        )
    )


# ---------------------------------------------------------------------------
# Payload helpers
# ---------------------------------------------------------------------------
def _reference_payload(
    reference_id: str,
    reference_audio_path: str = "",
) -> dict:
    """Build the speaker reference part of a ``/v2/generate`` payload.

    The runtime accepts a raw reference clip (``speaker_audio_base64``)
    or a speaker embedding id it serves (``speaker_embedding_id``, listed
    by ``GET /v2/speakers``).  A reference id without a clip is sent as an
    embedding id — the caller decides which one it holds.  Cloning from a
    raw clip needs the ``raw-reference`` weights, outside the minimal set
    the delivered service fetches (its README, section « Poids : jeu
    minimal »), so that path stays an explicit opt-in.
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


def _is_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def sanitize_control_spans(
    text: str,
    control_spans: object,
) -> list[dict]:
    """Keep only the control spans the server will accept for ``text``.

    A span is valid when ``0 <= start < end <= len(text)`` (code points
    of ``text``, end exclusive) and its ``controls`` map at least one
    direction to a number.  The server answers an invalid span with a
    ``400`` **for the whole request**, so one stale sidecar offset would
    otherwise cost the whole segment: invalid spans are dropped here and
    reported in the log, and the whole-segment ``controls`` still apply.

    Parameters
    ----------
    text:
        The request text, exactly as it will be sent.
    control_spans:
        A list of ``{"start", "end", "controls"}`` objects, or ``None``.
        Any other shape (the per-direction dict form the server answers
        ``422``) yields an empty list and an error log.

    Returns
    -------
    list[dict]
        The valid spans, rebuilt with exactly the three keys the server
        reads (``start``, ``end``, ``controls``).
    """
    if not control_spans:
        return []
    if isinstance(control_spans, dict) or not isinstance(control_spans, list):
        logger.error(
            "ZONOS3 control_spans must be a list of {start, end, controls} "
            "objects; got %s — no span sent",
            type(control_spans).__name__,
        )
        return []

    limit = len(text)
    kept: list[dict] = []
    for span in control_spans:
        valid = isinstance(span, dict)
        if valid:
            start, end = span.get("start"), span.get("end")
            controls = span.get("controls")
            valid = (
                isinstance(start, int)
                and not isinstance(start, bool)
                and isinstance(end, int)
                and not isinstance(end, bool)
                and isinstance(controls, dict)
                and bool(controls)
                and all(
                    isinstance(name, str) and _is_number(dose)
                    for name, dose in controls.items()
                )
                and 0 <= start < end <= limit
            )
        if valid:
            kept.append(
                {
                    "start": span["start"],
                    "end": span["end"],
                    "controls": {k: float(v) for k, v in span["controls"].items()},
                }
            )
        else:
            logger.warning(
                "ZONOS3 control span %r dropped: offsets must satisfy "
                "0 <= start < end <= %d (code points of the request text)",
                span,
                limit,
            )
    return kept


# ---------------------------------------------------------------------------
# Synthesis
# ---------------------------------------------------------------------------
def zonos3_tts(
    text: str,
    reference_id: str = "",
    reference_audio_path: str = "",
    seed: int = 42,
    temperature: float = DEFAULT_TEMPERATURE,
    top_p: float = DEFAULT_TOP_P,
    controls: dict[str, float] | None = None,
    control_spans: list[dict] | None = None,
    language: str = FRENCH_LANGUAGE_CODE,
    format: str = "wav",
    max_tokens: int | None = None,
    timeout: int = 600,
) -> tuple[bytes | None, int | None]:
    """Synthesize speech via ``POST /v2/generate``.

    Parameters
    ----------
    text:
        The text to render, read literally — the caller strips the
        FishAudio bracket tags, since ZONOS3 has no tag grammar and
        renders what it is given.  One request holds at most
        :data:`MAX_RENDER_SECONDS` of audio; a longer text is cut
        without any signal, so the caller keeps its segments under it.
    reference_id:
        Speaker embedding id served by ``GET /v2/speakers``, used when no
        raw clip is given.
    reference_audio_path:
        Raw reference clip for zero-shot cloning (takes precedence over
        ``reference_id``).
    seed:
        The seed requested.  The runtime echoes the seed it used in the
        ``X-Seed`` header.
    temperature, top_p:
        Sampling parameters.
    controls:
        Whole-segment steering doses — ``{"mood.arousal": 6.0}``.  Doses
        are calibrated absolutes: see :mod:`v4.zonos3_steering`.
    control_spans:
        Span-scoped steering — ``[{"start": 0, "end": 12, "controls":
        {"mood.arousal": 6.0}}]``, offsets in code points of ``text``,
        end exclusive.  Invalid spans are dropped
        (:func:`sanitize_control_spans`).  The server follows spans at an
        estimated frames-per-character rate and says so in
        ``X-Control-Span-Follow: rate``; a missing header means no span
        was applied, which is logged.
    language:
        Language code the server lists (``fr_fr`` for French).
    format:
        Requested output format (``"wav"`` or ``"pcm"``).  The request is
        always non-streaming: a WAV stream is refused.
    max_tokens:
        Audio frames to render at most.  ``None`` keeps the server
        default; the server caps the value at :data:`MAX_AUDIO_FRAMES`.
    timeout:
        Request timeout in seconds.

    Returns
    -------
    (audio_bytes, seed_used)
        ``audio_bytes`` is ``None`` on failure.  ``seed_used`` is the
        seed the runtime reports in ``X-Seed`` — ``None`` when the
        header is absent (never a substituted value).
    """
    if len(text) > ADVISORY_TEXT_CHARS:
        logger.warning(
            "ZONOS3 text of %d characters: past ~%d characters a French "
            "render reaches the one-request ceiling (%.3f s = %d frames) "
            "and is cut there without any signal; split the text",
            len(text),
            ADVISORY_TEXT_CHARS,
            MAX_RENDER_SECONDS,
            MAX_AUDIO_FRAMES - PROMPT_FRAME_OVERHEAD,
        )

    payload: dict = {
        "text": text,
        "seed": seed,
        "temperature": temperature,
        "top_p": top_p,
        "language": language,
        "format": format,
        "stream": False,
    }
    if max_tokens is not None:
        payload["max_tokens"] = int(max_tokens)
    payload.update(_reference_payload(reference_id, reference_audio_path))
    if controls:
        payload["controls"] = dict(controls)
    spans = sanitize_control_spans(text, control_spans)
    if spans:
        payload["control_spans"] = spans

    try:
        resp = requests.post(
            f"{ZONOS3_URL}/v2/generate",
            json=payload,
            headers=_auth_headers(),
            timeout=timeout,
        )
        resp.raise_for_status()
    except requests.RequestException as exc:
        # The body of a refusal names the clause the request broke
        # ("Unsupported language code", "control span [a, b) is outside
        # the text"): without it a 400 is indistinguishable from a 422.
        detail = getattr(getattr(exc, "response", None), "text", "") or ""
        logger.error(
            "ZONOS3 TTS error: %s%s",
            exc,
            f" — {detail[:400]}" if isinstance(detail, str) and detail else "",
        )
        return None, None

    if spans and "X-Control-Span-Follow" not in resp.headers:
        logger.warning(
            "ZONOS3 reported no X-Control-Span-Follow header: the %d control "
            "span(s) of this request were not applied",
            len(spans),
        )

    seed_used: int | None = None
    raw_seed = resp.headers.get("X-Seed")
    if raw_seed is not None:
        try:
            seed_used = int(raw_seed)
        except ValueError:
            logger.warning("ZONOS3 returned a non-integer X-Seed: %r", raw_seed)

    return resp.content, seed_used


def zonos3_controls() -> dict:
    """Read the served steering bundle via ``GET /v2/controls``.

    The payload is the **authority** on what can be steered: its
    ``directions`` object lists the served directions and its ``sets``
    object the space and calibration of each.  Returns an empty dict
    when the endpoint is absent or unreadable — the resolver then
    degrades every axis rather than steering a direction the server does
    not serve.
    """
    try:
        resp = requests.get(
            f"{ZONOS3_URL}/v2/controls",
            headers=_auth_headers(),
            timeout=30,
        )
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
        resp = requests.get(
            f"{ZONOS3_URL}/v2/capabilities",
            headers=_auth_headers(),
            timeout=30,
        )
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
