#!/usr/bin/env python3
"""
TADA 3B ML TTS Service - OpenAI-compatible API
HumeAI's voice cloning model (Llama 3.2 fine-tune)

TADA requires reference audio for voice cloning. This service:
1. On first request, generates a bootstrap reference using Kokoro (sibling service)
2. Caches the reference audio for subsequent requests
3. Falls back to a synthetic reference if Kokoro is unavailable
"""

import os
import io
import gc
import logging
import threading
import time
import wave
from contextlib import asynccontextmanager
from pathlib import Path
from typing import Optional, Tuple

import torch
import torchaudio
import numpy as np
from fastapi import FastAPI, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
from tada.modules.encoder import Encoder
from tada.modules.tada import TadaForCausalLM

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Configuration
DEVICE = os.getenv("TTS_DEVICE", "cuda" if torch.cuda.is_available() else "cpu")
SAMPLE_RATE = int(os.getenv("SAMPLE_RATE", "24000"))
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "true").lower() == "true"
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "1200"))
KOKORO_SERVICE_URL = os.getenv("KOKORO_SERVICE_URL", "http://tts-kokoro:8000")
REFERENCE_DIR = Path("/app/models/references")

# Voice mapping for OpenAI compatibility
AVAILABLE_VOICES = {
    "alloy": "default",
    "echo": "default",
    "fable": "default",
    "onyx": "default",
    "nova": "default",
    "shimmer": "default",
}

# Reference text used to generate the bootstrap reference audio
REFERENCE_TEXT = "The quick brown fox jumps over the lazy dog."


def generate_synthetic_reference() -> Tuple[torch.Tensor, int]:
    """Generate a synthetic speech-like reference signal.

    Creates a modulated signal with formant-like structure that the
    TADA encoder can process. This is a fallback when Kokoro is unavailable.
    """
    sr = SAMPLE_RATE
    duration = 2.0  # 2 seconds
    t = np.linspace(0, duration, int(sr * duration), dtype=np.float32)

    # Simulate speech formants (F1~500Hz, F2~1500Hz, F3~2500Hz)
    f1 = np.sin(2 * np.pi * 500 * t) * 0.4
    f2 = np.sin(2 * np.pi * 1500 * t) * 0.25
    f3 = np.sin(2 * np.pi * 2500 * t) * 0.15

    # Amplitude modulation to simulate syllable rhythm (~4Hz)
    envelope = 0.5 + 0.5 * np.sin(2 * np.pi * 4.0 * t)

    # Add slight noise for naturalness
    noise = np.random.randn(len(t)).astype(np.float32) * 0.02

    signal = (f1 + f2 + f3 + noise) * envelope
    signal = signal / (np.max(np.abs(signal)) + 1e-8)  # Normalize
    signal = signal.astype(np.float32)

    audio_tensor = torch.from_numpy(signal).unsqueeze(0)  # [1, samples]
    return audio_tensor, sr


def fetch_kokoro_reference() -> Optional[Tuple[torch.Tensor, int]]:
    """Try to generate reference audio using Kokoro service."""
    import urllib.request
    import json

    try:
        url = f"{KOKORO_SERVICE_URL}/v1/audio/speech"
        data = json.dumps({
            "model": "kokoro",
            "input": REFERENCE_TEXT,
            "voice": "af_sky",
            "response_format": "wav"
        }).encode("utf-8")

        req = urllib.request.Request(
            url, data=data,
            headers={"Content-Type": "application/json"}
        )

        with urllib.request.urlopen(req, timeout=30) as resp:
            wav_data = resp.read()

        # Load the WAV data
        buffer = io.BytesIO(wav_data)
        audio, sr = torchaudio.load(buffer)

        # Resample to TADA's expected rate if needed
        if sr != SAMPLE_RATE:
            resampler = torchaudio.transforms.Resample(sr, SAMPLE_RATE)
            audio = resampler(audio)

        logger.info(f"Generated Kokoro reference audio: {audio.shape}, sr={SAMPLE_RATE}")
        return audio, SAMPLE_RATE

    except Exception as e:
        logger.warning(f"Failed to get Kokoro reference: {e}")
        return None


def get_or_create_reference() -> Tuple[torch.Tensor, int]:
    """Get cached reference audio or create one."""
    REFERENCE_DIR.mkdir(parents=True, exist_ok=True)
    ref_path = REFERENCE_DIR / "default_reference.wav"

    # Try cached file first
    if ref_path.exists():
        try:
            audio, sr = torchaudio.load(str(ref_path))
            logger.info(f"Loaded cached reference: {ref_path}")
            return audio, sr
        except Exception as e:
            logger.warning(f"Failed to load cached reference: {e}")

    # Try Kokoro first (best quality)
    result = fetch_kokoro_reference()
    if result is not None:
        audio, sr = result
        torchaudio.save(str(ref_path), audio, sr)
        logger.info(f"Saved Kokoro reference to {ref_path}")
        return audio, sr

    # Fallback to synthetic
    logger.info("Using synthetic reference audio")
    audio, sr = generate_synthetic_reference()
    torchaudio.save(str(ref_path), audio, sr)
    return audio, sr


class LazyModelManager:
    """Manages lazy loading and unloading of TTS models.

    Le modele charge occupe 10,91 Gio de VRAM sur une carte partagee avec
    ``tts-qwen`` (mesure du 2026-11-27 : 24 293 Mio utilises, 34 Mio libres).
    ``IDLE_TIMEOUT`` bornait nominalement cette occupation, mais aucun code ne
    dechargeait : les champs existaient sans lecteur. ``unload_if_idle`` ferme
    ce trou, et ``use`` interdit qu'un dechargement tombe au milieu d'une
    synthese.
    """

    def __init__(self, idle_timeout: int = IDLE_TIMEOUT):
        self.idle_timeout = idle_timeout
        self.encoder = None
        self.model = None
        self._default_prompt = None
        self.last_load_error = None
        self.last_unload_at = None
        self.unload_count = 0
        self._lock = threading.Lock()
        self._in_flight = 0
        self._last_used = None
        self._reaper_stop = threading.Event()

    def get_model(self):
        """Get or load the model."""
        with self._lock:
            if self.model is None:
                logger.info("Loading TADA model...")
                try:
                    self._load_models()
                except Exception as exc:
                    self.last_load_error = f"{type(exc).__name__}: {exc}"
                    logger.error("TADA model load failed: %s", self.last_load_error, exc_info=True)
                    raise
                logger.info("TADA model loaded successfully")
            self._last_used = time.monotonic()
            return self.encoder, self.model

    def begin_use(self):
        """Marque une synthese en cours : le dechargement l'attend.

        Sans ce compteur, le balayage pourrait retirer le modele entre
        ``get_model`` et ``model.generate`` ; le fil de synthese tiendrait alors
        des references vers des tenseurs dont le cache a ete vide. Les deux
        appels sont explicites plutot qu'un context manager : le corps de la
        route les encadre sans reindenter la generation.
        """
        with self._lock:
            self._in_flight += 1
            self._last_used = time.monotonic()

    def end_use(self):
        with self._lock:
            self._in_flight = max(0, self._in_flight - 1)
            self._last_used = time.monotonic()

    def unload_if_idle(self, now: Optional[float] = None):
        """Decharge le modele et sa reference si le service est inactif.

        Rend ``True`` si un dechargement a eu lieu. Ne fait rien quand aucun
        modele n'est charge, quand une synthese est en cours, ou quand
        ``IDLE_TIMEOUT`` n'est pas encore ecoule. ``idle_timeout <= 0``
        desactive le dechargement.
        """
        if self.idle_timeout <= 0:
            return False
        with self._lock:
            if self.model is None:
                return False
            if self._in_flight > 0:
                return False
            now = time.monotonic() if now is None else now
            last = self._last_used if self._last_used is not None else now
            if now - last < self.idle_timeout:
                return False
            idle_for = now - last
            self.model = None
            self.encoder = None
            self._default_prompt = None
            self.last_unload_at = time.time()
            self.unload_count += 1
        # Hors du verrou : la liberation de l'allocateur CUDA peut prendre du
        # temps et ne doit pas retarder une synthese qui arrive.
        gc.collect()
        if DEVICE == "cuda" and torch.cuda.is_available():
            torch.cuda.empty_cache()
        logger.info(
            "TADA model unloaded after %.1f s idle (unload #%d)",
            idle_for, self.unload_count,
        )
        return True

    def reaper_interval(self):
        """Periode du balayage : bornee, et resserree pour un delai court."""
        return max(1, min(30, self.idle_timeout))

    def start_reaper(self):
        """Demarre le balayage d'inactivite (thread demon)."""
        if self.idle_timeout <= 0:
            logger.info("Idle unload disabled (IDLE_TIMEOUT=%d)", self.idle_timeout)
            return None
        interval = self.reaper_interval()

        def _loop():
            while not self._reaper_stop.wait(interval):
                try:
                    self.unload_if_idle()
                except Exception:
                    logger.warning("Idle unload sweep failed", exc_info=True)

        thread = threading.Thread(target=_loop, name="tada-idle-reaper", daemon=True)
        thread.start()
        logger.info("Idle unload enabled: timeout %d s, sweep every %d s",
                    self.idle_timeout, interval)
        return thread

    def stop_reaper(self):
        self._reaper_stop.set()

    def idle_seconds(self):
        with self._lock:
            if self._last_used is None:
                return None
            return round(time.monotonic() - self._last_used, 1)

    def _load_models(self):
        """Load the encoder, then the 3B model, exactly as the model card does.

        bfloat16 puis ``.to(DEVICE)`` : c'est le chemin publie par la fiche du
        point de controle, et c'est le dtype de ses poids. Deux ecarts mesures
        le 2026-11-27 sur cette image, tous deux fatals :

        - ``device_map="cuda"`` laisse le decodeur sur CPU : ``_decoder`` est
          charge imbrique depuis ``tada-codec`` dans ``__init__``, donc la
          repartition de ``device_map`` ne le couvre pas. La generation echouait
          sur ``Expected all tensors to be on the same device (cpu and cuda:0)``
          dans ``decoder_proj`` ;
        - ``float16`` force une copie de conversion absente en bfloat16 : le
          chargement depassait 8 Gio de RAM hote et le conteneur etait tue,
          alors qu'en bfloat16 le chemin complet (chargement, reference, une
          synthese) culmine a 6 557 Mio.
        """
        self.encoder = Encoder.from_pretrained(
            "HumeAI/tada-codec",
            subfolder="encoder"
        ).to(DEVICE)
        self.model = TadaForCausalLM.from_pretrained(
            "HumeAI/tada-3b-ml",
            torch_dtype=torch.bfloat16 if DEVICE == "cuda" else torch.float32,
        ).to(DEVICE)

    def get_default_prompt(self):
        """Get or create the default reference prompt."""
        if self._default_prompt is None:
            encoder, _ = self.get_model()
            ref_audio, ref_sr = get_or_create_reference()
            ref_audio = ref_audio.to(DEVICE)

            with torch.no_grad():
                self._default_prompt = encoder(
                    ref_audio,
                    text=[REFERENCE_TEXT],
                    sample_rate=ref_sr
                )
            logger.info("Default reference prompt created")
        return self._default_prompt


model_manager = LazyModelManager()


class TTSRequest(BaseModel):
    """OpenAI-compatible TTS request."""
    model: str = "tada"
    input: str
    voice: str = "alloy"
    response_format: str = "wav"
    speed: float = 1.0


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Lifespan context manager."""
    if PRELOAD_MODEL:
        logger.info("Preloading TADA model...")
        model_manager.get_model()
        # Pre-create default prompt (may use Kokoro)
        try:
            model_manager.get_default_prompt()
        except Exception as e:
            logger.warning(f"Failed to pre-create default prompt: {e}")
    model_manager.start_reaper()
    yield
    # Cleanup
    model_manager.stop_reaper()
    if DEVICE == "cuda":
        torch.cuda.empty_cache()


app = FastAPI(
    title="TADA TTS API",
    description="OpenAI-compatible TTS API using HumeAI TADA 3B ML",
    version="1.0.0",
    lifespan=lifespan
)


@app.get("/health")
async def health_check():
    """Health check endpoint.

    Repond toujours 200 : la passerelle declare ce service en
    ``depends_on: condition: service_healthy``, une sonde qui rougirait
    bloquerait son demarrage. L'etat reel du modele est dans le corps ; une
    sonde constante ne distinguait pas un service pret d'un service dont le
    modele n'avait jamais pu se charger.
    """
    return {
        "status": "healthy",
        "model": "tada",
        "device": DEVICE,
        "model_loaded": model_manager.model is not None,
        "encoder_loaded": model_manager.encoder is not None,
        "reference_ready": model_manager._default_prompt is not None,
        "last_load_error": model_manager.last_load_error,
        "idle_timeout_s": model_manager.idle_timeout,
        "idle_seconds": model_manager.idle_seconds(),
        "unload_count": model_manager.unload_count,
    }


@app.get("/v1/models")
async def list_models():
    """List available models (OpenAI-compatible)."""
    return {
        "object": "list",
        "data": [{"id": "tada", "name": "TADA 3B ML", "owned_by": "humeai"}]
    }


@app.get("/v1/voices")
async def list_voices():
    """List available voices (OpenAI-compatible)."""
    voices = [{"id": v, "name": v.capitalize()} for v in AVAILABLE_VOICES.keys()]
    return {"voices": voices}


@app.post("/v1/audio/speech")
async def text_to_speech(request: TTSRequest):
    """Generate speech from text (OpenAI-compatible endpoint)."""
    try:
        # Le dechargement sur inactivite ne doit pas tomber au milieu d'une
        # generation : le modele est retenu du premier acces jusqu'a l'audio
        # converti en numpy (apres cela, plus rien n'est sur le GPU).
        model_manager.begin_use()
        # Get model and default prompt
        _, model = model_manager.get_model()
        prompt = model_manager.get_default_prompt()

        logger.info(f"Generating speech for text: {request.input[:50]}...")

        # Generate speech with reference prompt
        with torch.no_grad():
            output = model.generate(
                prompt=prompt,
                text=request.input,
            )

        # Extract audio from GenerationOutput.
        # The library builds this list with try/except and appends None when the
        # decoder raises (tada/modules/tada.py: ``wavs.append(None)``). np.asarray(None)
        # then yields a single NaN sample, which used to be served as HTTP 200 with a
        # 46-byte WAV (measured 2026-11-27). A failure surfaces as a failure.
        if hasattr(output, 'audio') and output.audio:
            audio_data = output.audio
            audio_tensor = audio_data[0] if isinstance(audio_data, list) else audio_data
        elif isinstance(output, (tuple, list)) and len(output) > 0:
            audio_tensor = output[0]
        else:
            raise ValueError("No audio generated from TADA model")
        if not torch.is_tensor(audio_tensor):
            raise ValueError(
                "TADA decoder produced no waveform "
                f"(audio entry: {type(audio_tensor).__name__})"
            )

        # Move to CPU and convert to numpy
        audio_array = audio_tensor.detach().cpu().float().numpy().squeeze()
        model_manager.end_use()
        if audio_array.size == 0:
            raise ValueError("TADA decoder produced an empty waveform")
        if not np.isfinite(audio_array).all():
            raise ValueError("TADA produced a non-finite waveform (NaN or Inf)")

        # Ensure correct format
        if audio_array.dtype in (np.float32, np.float64):
            audio_array = np.clip(audio_array, -1.0, 1.0)
            audio_array = (audio_array * 32767).astype(np.int16)

        # Write to WAV
        buffer = io.BytesIO()
        with wave.open(buffer, 'wb') as wav_file:
            wav_file.setnchannels(1)
            wav_file.setsampwidth(2)
            wav_file.setframerate(SAMPLE_RATE)
            wav_file.writeframes(audio_array.tobytes())

        buffer.seek(0)

        return StreamingResponse(
            buffer,
            media_type="audio/wav",
            headers={
                "Content-Disposition": 'attachment; filename="speech.wav"',
                "X-Model-Used": "tada"
            }
        )

    except Exception as e:
        model_manager.end_use()
        logger.error(f"TTS generation failed: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail=str(e))


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
