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
import tempfile
from pathlib import Path
from typing import Callable

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
# The served model name depends on the container's MODEL_TYPE (VoiceDesign vs
# Base checkpoint — different weights, different /v1/models id). Override via
# env or module attribute when talking to a Base container directly.
QWEN_MODEL: str = os.getenv("QWEN_MODEL", "Qwen/Qwen3-TTS-12Hz-1.7B-VoiceDesign")

# Optional bearer for the gateway auth middleware (absent on localhost).
_TTS_KEY: str | None = os.getenv("TTS_GATEWAY_API_KEY") or os.getenv("KOKORO_API_KEY")

# Max instructions length enforced server-side (stage config tts_args).
MAX_INSTRUCTIONS_LEN: int = 500

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Attack guard (#19739 phase 2) — onset-drop detection, per chunk, online
# ---------------------------------------------------------------------------
# Both chunked renders concatenate sentence-level chunks. A chunk that starts
# **mid-text** loses its attack — the first words of the chunk are never
# pronounced — and the loss is invisible to any duration check: the
# chars/s bands of clean and omitting renders overlap fully (#19739). Only the
# ASR can see it, so the verdict organ is `v4.attack_guard` (delivered by
# #21459), applied here per chunk, exactly as the CV3 narrator path does
# (#23476).
#
# Two differences from the CV3 path, both dictated by this transport:
#
# - the lever is a **re-render**, not a seeded re-roll: the gateway takes no
#   seed and its stage-0 temperature is 0.9 (module docstring), so a
#   re-render is a fresh sample rather than the same audio;
# - the guard is **off by default at this level** and the pipeline turns it on
#   (`attack_guard=True`): a bench render has no ASR server beside it, and a
#   guard that cannot reach its organ must not pretend to have run.
#
# `V4_ATTACK_GUARD=off` still wins over the pipeline's request: the toggle is
# the A/B arm the measured comparison needs.
ATTACK_GUARD_ENV = "V4_ATTACK_GUARD"
# Same endpoint and model as the omission organ p7 (localhost:8190,
# large-v3-turbo): the guard must measure what p7 measures, so an "attack
# dropped" verdict and a p7 omission span cannot diverge.
ATTACK_GUARD_ASR_BASE_URL_ENV = "V4_ASR_BASE_URL"
ATTACK_GUARD_ASR_BASE_URL = "http://localhost:8190"
# Number of renders per chunk before the passage is refused. The CV3 path
# retries 5 times with a spaced seed; here the re-render is the only lever,
# and the server samples at temperature 0.9.
ATTACK_GUARD_ATTEMPTS = 3


def _attack_guard_requested(attack_guard: bool) -> bool:
    """Le pipeline demande la garde ; `V4_ATTACK_GUARD=off` l'emporte."""
    if not attack_guard:
        return False
    return os.getenv(ATTACK_GUARD_ENV, "on").strip().lower() not in {
        "0", "off", "no", "false",
    }


def _attack_guard_asr(attack_asr: Callable[[str], str] | None) -> Callable[[str], str]:
    """Callable de transcription : l'injecte d'abord, l'organe sinon.

    L'organe est le client http de `v4.attack_guard` (`asr_http`), qui lit un
    fichier : la garde ecrit donc le chunk rendu dans un wav temporaire et
    lui passe le chemin. Le client http de la garde est resolu ici, pas
    importe au module, pour que les tests hermetiques n'aient besoin ni du
    serveur Whisper ni de `requests` pour un appel.
    """
    if attack_asr is not None:
        return attack_asr

    from ..attack_guard import asr_http

    base_url = os.getenv(ATTACK_GUARD_ASR_BASE_URL_ENV, ATTACK_GUARD_ASR_BASE_URL)

    def _transcribe(wav_path: str) -> str:
        return asr_http({"audio": str(wav_path)}, base_url=base_url)

    return _transcribe


def _guard_chunk_attack(
    chunk_text: str,
    wav_bytes: bytes,
    chunk_index: int,
    engine: str,
    asr_fn: Callable[[str], str],
) -> dict:
    """Verdict d'attaque manquante pour un chunk rendu (organe v4.attack_guard).

    Le verdict est celui de l'organe : perte de tete contigue depuis le mot 0
    (l'organe d'omission p7 interroge a `min_words=1`), seuil 3 mots. Le
    chunk est ecrit dans un wav temporaire que l'ASR peut lire ; le fichier
    part avec le chunk, jamais dans le depot.
    """
    from ..attack_guard import evaluate_chunk

    with tempfile.NamedTemporaryFile(
        prefix="v4_attack_guard_", suffix=".wav", delete=False
    ) as fh:
        wav_path = fh.name
        fh.write(wav_bytes)
    try:
        transcript = asr_fn(wav_path)
    finally:
        try:
            os.unlink(wav_path)
        except OSError:  # pragma: no cover — fichier deja absent
            pass

    return evaluate_chunk(
        {
            "chunk_index": chunk_index,
            "text": chunk_text,
            "engine": engine,
            "audio": wav_path,
            "seed": None,
        },
        transcript,
    )


def _chunked_render(
    render: Callable[[str], bytes | None],
    chunks: list[str],
    engine: str,
    attack_guard: bool,
    attack_asr: Callable[[str], str] | None,
    attack_attempts: int,
    attack_report: dict | None,
) -> list[bytes] | None:
    """Rend chaque chunk, sous garde d'attaque optionnelle.

    `render(chunk_text)` est le rendu de transport. Renvoie la liste des wav
    de chunk, ou `None` si un chunk a echoue (transport) ou si la garde n'a pas
    obtenu l'attaque d'un chunk apres `attack_attempts` rendus : un chunk dont
    les premiers mots n'ont jamais ete prononces n'est **pas livre** — la
    passage est refusee, comme un rendu degenere l'est sur le chemin CV3.

    Le rapport d'avort (`attack_report`) porte le chunk avorte, la raison du
    verdict et le nombre de rendus tentes : la couche appelante peut alors
    nommer la cause dans son erreur au lieu d'annoncer un vague « rendu
    echoue ».
    """
    guard_on = _attack_guard_requested(attack_guard)
    asr_fn = _attack_guard_asr(attack_asr) if guard_on else None
    attempts = max(1, int(attack_attempts))

    out: list[bytes] = []
    for i, ch in enumerate(chunks, start=1):
        wav: bytes | None = None
        for attempt in range(1, attempts + 1):
            audio = render(ch)
            if not audio:
                logger.error(
                    "%s chunk %d/%d failed (%d chars): %r",
                    engine, i, len(chunks), len(ch), ch[:60],
                )
                return None
            if asr_fn is None:
                wav = audio
                break
            verdict = _guard_chunk_attack(ch, audio, i, engine, asr_fn)
            if verdict["attack_dropped"]:
                logger.warning(
                    "[attack-guard] chunk %d/%d render %d/%d: attack dropped "
                    "(%s, %d leading word(s) lost) - re-rendering",
                    i, len(chunks), attempt, attempts, verdict["reason"],
                    verdict["n_missing_leading"],
                )
                if attack_report is not None:
                    attack_report.update(
                        {
                            "aborted_chunk": i,
                            "reason": verdict["reason"],
                            "n_missing_leading": verdict["n_missing_leading"],
                            "attempts": attempt,
                        }
                    )
                continue
            wav = audio
            break
        if wav is None:
            logger.error(
                "[attack-guard] chunk %d/%d: attack still dropped after %d "
                "render(s) - passage refused",
                i, len(chunks), attempts,
            )
            if attack_report is not None:
                # La raison du dernier verdict (leading_span, ...) est conservee :
                # c'est elle qui nomme le defaut, pas le simple abandon.
                attack_report.update({"aborted": True, "attempts": attempts})
            return None
        out.append(wav)
    return out


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
        # A part with no alphanumeric content (closing quote "»", stray
        # underscore, trailing punctuation the regex split off) must not
        # become its own chunk: the gateway renders no audio for it
        # (Kokoro "No audio segments generated", HTTP 500) and
        # qwen_tts_voicedesign_chunked treats any failed chunk as fatal.
        # Attach it to the running chunk instead -- it belongs to the
        # sentence it closes. When no chunk is running yet (text opening on
        # an orphan "»"), there is no sentence to close: attach nothing, or
        # the next chunk would lead with a bare glyph sent to the gateway
        # (residual nit, review of #19453).
        if not re.search(r"[^\W_]", p):
            if cur:
                cur = f"{cur}{p}"
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
    *,
    attack_guard: bool = False,
    attack_asr: Callable[[str], str] | None = None,
    attack_attempts: int = ATTACK_GUARD_ATTEMPTS,
    attack_report: dict | None = None,
) -> bytes | None:
    """VoiceDesign render of long text, chunked to stay under the gateway timeout.

    Renders each sentence-level chunk as WAV via :func:`qwen_tts_voicedesign`,
    concatenates them with a short silence gap, and returns a single WAV byte
    string. Mirrors how the v4 pipeline renders per-segment. Returns ``None``
    if any chunk fails (so a partial passage is never silently measured).

    ``attack_guard=True`` adds the per-chunk onset-drop guard of #19739: each
    rendered chunk is transcribed and its attack verified before it is
    accepted, and a chunk that lost its attack is re-rendered. The passage is
    refused (``None``) if the attack is still missing after ``attack_attempts``
    renders — a chunk whose first words were never pronounced is never shipped.
    """
    from io import BytesIO

    from pydub import AudioSegment

    chunks = _split_sentences(text, max_chars=max_chars)
    if not chunks:
        return None
    logger.info("VoiceDesign chunked render: %d chunk(s)", len(chunks))

    def _render(ch: str) -> bytes | None:
        return qwen_tts_voicedesign(
            ch,
            instructions=instructions,
            language=language,
            response_format="wav",
            speed=speed,
            timeout=per_chunk_timeout,
        )

    wavs = _chunked_render(
        _render, chunks, "qwen_voicedesign", attack_guard, attack_asr,
        attack_attempts, attack_report,
    )
    if wavs is None:
        return None

    segments = [AudioSegment.from_file(BytesIO(a), format="wav") for a in wavs]
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
    base_url: str | None = None,
    api_key: str | None = None,
    model: str | None = None,
) -> bytes | None:
    """Synthesize via a named native speaker (CustomVoice task).

    ``instructions`` may optionally add a style hint on top of the speaker.
    ``base_url``/``api_key``/``model`` override the module-level gateway
    constants per call (used when the CustomVoice checkpoint is served on a
    different host than the local :8196 VoiceDesign socket — #21145).
    """
    payload: dict = {
        "model": model or QWEN_MODEL,
        "input": text,
        "task_type": "CustomVoice",
        "voice": voice,
        "language": language,
        "response_format": response_format,
        "speed": speed,
    }
    if instructions.strip():
        payload["instructions"] = instructions.strip()[:MAX_INSTRUCTIONS_LEN]
    return _post_speech(payload, timeout, base_url=base_url, api_key=api_key)


def qwen_tts_customvoice_chunked(
    text: str,
    voice: str = "Vivian",
    instructions: str = "",
    language: str = "French",
    speed: float = 1.0,
    max_chars: int = 160,
    per_chunk_timeout: int = 290,
    gap_ms: int = 120,
    base_url: str | None = None,
    api_key: str | None = None,
    model: str | None = None,
    *,
    attack_guard: bool = False,
    attack_asr: Callable[[str], str] | None = None,
    attack_attempts: int = ATTACK_GUARD_ATTEMPTS,
    attack_report: dict | None = None,
) -> bytes | None:
    """CustomVoice render of long text, chunked to stay under the gateway timeout.

    Same orchestration as :func:`qwen_tts_voicedesign_chunked` (sentence-level
    chunks, silence gap, single WAV out, ``None`` if any chunk fails so a
    partial passage is never silently measured), for the CustomVoice task on
    the published gateway (#21145).

    The per-chunk onset-drop guard of #19739 applies identically
    (``attack_guard=True``): a chunk that lost its attack is re-rendered, and
    the passage is refused if the attack is still missing after
    ``attack_attempts`` renders.
    """
    from io import BytesIO

    from pydub import AudioSegment

    chunks = _split_sentences(text, max_chars=max_chars)
    if not chunks:
        return None
    logger.info("CustomVoice chunked render: %d chunk(s)", len(chunks))

    def _render(ch: str) -> bytes | None:
        return qwen_tts_customvoice(
            ch,
            voice=voice,
            instructions=instructions,
            language=language,
            response_format="wav",
            speed=speed,
            timeout=per_chunk_timeout,
            base_url=base_url,
            api_key=api_key,
            model=model,
        )

    wavs = _chunked_render(
        _render, chunks, "qwen_customvoice", attack_guard, attack_asr,
        attack_attempts, attack_report,
    )
    if wavs is None:
        return None

    segments = [AudioSegment.from_file(BytesIO(a), format="wav") for a in wavs]
    combined = segments[0]
    gap = AudioSegment.silent(duration=gap_ms)
    for seg in segments[1:]:
        combined = combined + gap + seg
    buf = BytesIO()
    combined.export(buf, format="wav")
    return buf.getvalue()


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


def _post_speech(
    payload: dict,
    timeout: int,
    base_url: str | None = None,
    api_key: str | None = None,
) -> bytes | None:
    url_base = base_url or QWEN_GATEWAY_URL
    headers = _headers()
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    try:
        resp = requests.post(
            f"{url_base}/v1/audio/speech",
            json=payload,
            headers=headers,
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
