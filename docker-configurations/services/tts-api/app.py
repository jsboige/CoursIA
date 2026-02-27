#!/usr/bin/env python3
"""
TTS API - OpenAI-compatible Text-to-Speech API using Kokoro

Features:
- Lazy loading with auto-unload after inactivity
- GPU memory management
- OpenAI-compatible API
"""

import os
import sys
import time
import io
import logging
import asyncio
from typing import Optional
from pathlib import Path

from fastapi import FastAPI, HTTPException
from fastapi.responses import Response, JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import soundfile as sf
import numpy as np

# Add shared module to path
sys.path.insert(0, "/app/shared")
from lazy_model import LazyModelManager, idle_checker_task, get_all_status

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("tts-api")

# Configuration from environment
DEFAULT_MODEL = os.getenv("DEFAULT_TTS_MODEL", "kokoro")
DEFAULT_VOICE = os.getenv("DEFAULT_TTS_VOICE", "af_sky")
SAMPLE_RATE = int(os.getenv("SAMPLE_RATE", 24000))
DEVICE = os.getenv("TTS_DEVICE", "cuda")
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "300"))  # 5 minutes default
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "true").lower() == "true"

app = FastAPI(
    title="TTS API",
    description="OpenAI-compatible Text-to-Speech API using Kokoro with auto-unload",
    version="2.0.0"
)

# CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Voice mapping
AVAILABLE_VOICES = {
    "alloy": "af_sky",
    "echo": "am_adam",
    "fable": "af_bella",
    "onyx": "am_michael",
    "nova": "af_nova",
    "shimmer": "af_sarah",
    # Direct Kokoro voices
    "af_sky": "af_sky",
    "af_bella": "af_bella",
    "am_adam": "am_adam",
    "am_michael": "am_michael",
}


class TTSModelWrapper:
    """Wrapper to hold both pipeline and voices dict"""
    def __init__(self, pipeline):
        self.pipeline = pipeline
        self.voices = AVAILABLE_VOICES


def _load_tts_model():
    """Load the TTS model."""
    from kokoro import KPipeline
    logger.info(f"Loading Kokoro TTS model on {DEVICE}...")
    pipeline = KPipeline(lang_code='a', device=DEVICE)
    return TTSModelWrapper(pipeline)


def _unload_tts_model(model_wrapper):
    """Unload TTS model and free GPU memory."""
    del model_wrapper.pipeline
    del model_wrapper
    try:
        import torch
        if torch.cuda.is_available():
            torch.cuda.empty_cache()
    except:
        pass


# Model manager with lazy loading and auto-unload
model_manager = LazyModelManager(
    model_name="tts-kokoro",
    load_fn=_load_tts_model,
    unload_fn=_unload_tts_model,
    idle_timeout=IDLE_TIMEOUT,
    device=DEVICE,
    preload=PRELOAD_MODEL
)


# Request/Response models
class TTSRequest(BaseModel):
    model: str = "tts-1"
    input: str
    voice: str = "alloy"
    response_format: str = "mp3"  # mp3, opus, aac, flac, wav, pcm
    speed: float = 1.0


class VoiceInfo(BaseModel):
    voice_id: str
    name: str
    language: str
    gender: str
    preview_url: Optional[str] = None


@app.get("/health")
async def health_check():
    """Health check endpoint"""
    try:
        import torch
        cuda_available = torch.cuda.is_available()
        gpu_name = torch.cuda.get_device_name(0) if cuda_available else None
        gpu_memory = torch.cuda.memory_allocated(0) / (1024**3) if cuda_available else 0
    except:
        cuda_available = False
        gpu_name = None
        gpu_memory = 0

    status = model_manager.status

    return {
        "status": "healthy",
        "model": "kokoro",
        "device": DEVICE,
        "cuda_available": cuda_available,
        "gpu_name": gpu_name,
        "gpu_memory_gb": round(gpu_memory, 2),
        "model_loaded": status["loaded"],
        "idle_seconds": status.get("idle_seconds"),
        "idle_timeout": IDLE_TIMEOUT,
        "sample_rate": SAMPLE_RATE
    }


@app.get("/v1/models")
async def list_models():
    """List available models (OpenAI-compatible)"""
    return {
        "object": "list",
        "data": [
            {"id": "tts-1", "object": "model", "created": 1677610602, "owned_by": "system"},
            {"id": "tts-1-hd", "object": "model", "created": 1677610602, "owned_by": "system"},
            {"id": "kokoro", "object": "model", "created": 1677610602, "owned_by": "myia"}
        ]
    }


@app.get("/v1/voices")
async def list_voices():
    """List available voices"""
    voices = [
        VoiceInfo(voice_id="alloy", name="Alloy", language="en", gender="female"),
        VoiceInfo(voice_id="echo", name="Echo", language="en", gender="male"),
        VoiceInfo(voice_id="fable", name="Fable", language="en", gender="female"),
        VoiceInfo(voice_id="onyx", name="Onyx", language="en", gender="male"),
        VoiceInfo(voice_id="nova", name="Nova", language="en", gender="female"),
        VoiceInfo(voice_id="shimmer", name="Shimmer", language="en", gender="female"),
    ]
    return {"voices": [v.dict() for v in voices]}


@app.post("/v1/audio/speech")
async def create_speech(request: TTSRequest):
    """
    Generate speech from text (OpenAI-compatible endpoint)

    - **model**: tts-1, tts-1-hd, or kokoro
    - **input**: Text to convert to speech (max 4096 characters)
    - **voice**: Voice to use (alloy, echo, fable, onyx, nova, shimmer)
    - **response_format**: mp3, opus, aac, flac, wav, pcm
    - **speed**: Speed of speech (0.25 to 4.0)
    """
    start_time = time.time()

    # Validate input
    if len(request.input) > 4096:
        raise HTTPException(status_code=400, detail="Input text too long (max 4096 characters)")

    if not request.input.strip():
        raise HTTPException(status_code=400, detail="Input text cannot be empty")

    # Load model (lazy with auto-unload)
    model_wrapper = model_manager.get_model()
    tts_pipeline = model_wrapper.pipeline

    # Map voice
    kokoro_voice = AVAILABLE_VOICES.get(request.voice, "af_sky")

    logger.info(f"TTS request: voice={request.voice} ({kokoro_voice}), text_len={len(request.input)}")

    try:
        import torch

        # Generate audio
        audio_chunks = []
        for _, _, audio in tts_pipeline(request.input, voice=kokoro_voice, speed=request.speed):
            if isinstance(audio, torch.Tensor):
                audio = audio.cpu().numpy()
            audio_chunks.append(audio)

        if not audio_chunks:
            raise HTTPException(status_code=500, detail="No audio generated")

        # Concatenate chunks
        full_audio = np.concatenate(audio_chunks)

        # Normalize
        max_val = np.max(np.abs(full_audio))
        if max_val > 0:
            full_audio = full_audio / max_val * 0.95

        elapsed = time.time() - start_time
        duration = len(full_audio) / SAMPLE_RATE
        logger.info(f"Generated {duration:.1f}s audio in {elapsed:.2f}s")

        # Convert to requested format
        return encode_audio(full_audio, request.response_format)

    except Exception as e:
        logger.error(f"TTS error: {str(e)}")
        raise HTTPException(status_code=500, detail=str(e))


@app.post("/admin/unload")
async def force_unload():
    """Force unload the model (admin endpoint)"""
    unloaded = model_manager.force_unload()
    return {"unloaded": unloaded, "status": model_manager.status}


def encode_audio(audio: np.ndarray, format: str) -> Response:
    """Encode audio array to requested format"""
    buffer = io.BytesIO()

    if format == "wav":
        sf.write(buffer, audio, SAMPLE_RATE, format='WAV')
        media_type = "audio/wav"

    elif format == "mp3":
        # Use ffmpeg for mp3 encoding
        import subprocess
        wav_buffer = io.BytesIO()
        sf.write(wav_buffer, audio, SAMPLE_RATE, format='WAV')
        wav_buffer.seek(0)

        process = subprocess.run(
            ['ffmpeg', '-i', 'pipe:0', '-f', 'mp3', '-acodec', 'libmp3lame', '-ab', '128k', 'pipe:1'],
            input=wav_buffer.read(),
            capture_output=True
        )
        buffer = io.BytesIO(process.stdout)
        media_type = "audio/mpeg"

    elif format == "flac":
        sf.write(buffer, audio, SAMPLE_RATE, format='FLAC')
        media_type = "audio/flac"

    elif format == "pcm":
        buffer.write(audio.astype(np.float32).tobytes())
        media_type = "audio/pcm"

    elif format == "opus":
        # Fallback to wav if opus not available
        sf.write(buffer, audio, SAMPLE_RATE, format='WAV')
        media_type = "audio/wav"

    else:
        sf.write(buffer, audio, SAMPLE_RATE, format='WAV')
        media_type = "audio/wav"

    buffer.seek(0)
    return Response(content=buffer.read(), media_type=media_type)


@app.on_event("startup")
async def startup_event():
    """Start background idle checker"""
    asyncio.create_task(idle_checker_task(interval=60))
    logger.info(f"Started idle checker (timeout: {IDLE_TIMEOUT}s)")


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8191)
