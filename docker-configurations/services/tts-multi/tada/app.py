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
import logging
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
    """Manages lazy loading and unloading of TTS models."""

    def __init__(self, idle_timeout: int = IDLE_TIMEOUT):
        self.idle_timeout = idle_timeout
        self.last_used = None
        self.encoder = None
        self.model = None
        self._default_prompt = None

    def get_model(self):
        """Get or load the model."""
        if self.model is None:
            logger.info("Loading TADA model...")
            self.encoder = Encoder.from_pretrained(
                "HumeAI/tada-codec",
                subfolder="encoder"
            ).to(DEVICE)
            self.model = TadaForCausalLM.from_pretrained(
                "HumeAI/tada-3b-ml",
                torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32,
            ).to(DEVICE)
            logger.info("TADA model loaded successfully")
        self.last_used = torch.cuda.Event(enable_timing=True) if DEVICE == "cuda" else None
        return self.encoder, self.model

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
    yield
    # Cleanup
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
    """Health check endpoint."""
    return {"status": "healthy", "model": "tada"}


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

        # Extract audio from GenerationOutput
        # output.audio is a list of CUDA tensors
        if hasattr(output, 'audio') and output.audio:
            audio_data = output.audio
            if isinstance(audio_data, list):
                audio_tensor = audio_data[0]
            else:
                audio_tensor = audio_data
        elif isinstance(output, (tuple, list)) and len(output) > 0:
            audio_tensor = output[0]
        else:
            raise ValueError("No audio generated from TADA model")

        # Move to CPU and convert to numpy
        if hasattr(audio_tensor, 'detach'):
            audio_array = audio_tensor.detach().cpu().float().numpy().squeeze()
        elif hasattr(audio_tensor, 'cpu'):
            audio_array = audio_tensor.cpu().numpy().squeeze()
        else:
            audio_array = np.asarray(audio_tensor, dtype=np.float32).squeeze()

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
        logger.error(f"TTS generation failed: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail=str(e))


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
