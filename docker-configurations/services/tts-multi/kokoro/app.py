#!/usr/bin/env python3
"""
Kokoro TTS Service - OpenAI-compatible API
Lightweight, fast TTS model
"""

import os
import io
import logging
from contextlib import asynccontextmanager
from typing import Optional

import numpy as np
import torch
import torchaudio
from fastapi import FastAPI, HTTPException
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
from kokoro import KPipeline

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Configuration
DEVICE = os.getenv("TTS_DEVICE", "cuda" if torch.cuda.is_available() else "cpu")
SAMPLE_RATE = int(os.getenv("SAMPLE_RATE", "24000"))
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "true").lower() == "true"
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "1200"))

# Voice mapping for OpenAI compatibility
AVAILABLE_VOICES = {
    "alloy": "af_sky",
    "echo": "am_adam",
    "fable": "af_bella",
    "onyx": "am_michael",
    "nova": "af_nova",
    "shimmer": "af_sarah",
}

# Global model instance
_model = None
_pipeline = None


class LazyModelManager:
    """Manages lazy loading and unloading of TTS models."""

    def __init__(self, idle_timeout: int = IDLE_TIMEOUT):
        self.idle_timeout = idle_timeout
        self.last_used = None
        self.model = None
        self.pipeline = None

    def get_model(self):
        """Get or load the model."""
        if self.model is None:
            logger.info("Loading Kokoro TTS model...")
            self.pipeline = KPipeline(
                lang_code='a',  # 'a' for american english
                device=DEVICE
            )
            self.model = self.pipeline  # For compatibility
            logger.info("Kokoro TTS model loaded successfully")
        self.last_used = torch.cuda.Event(enable_timing=True) if DEVICE == "cuda" else None
        return self.model, self.pipeline


model_manager = LazyModelManager()


class TTSRequest(BaseModel):
    """OpenAI-compatible TTS request."""
    model: str = "kokoro"
    input: str
    voice: str = "alloy"
    response_format: str = "mp3"
    speed: float = 1.0


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Lifespan context manager."""
    if PRELOAD_MODEL:
        logger.info("Preloading Kokoro TTS model...")
        model_manager.get_model()
    yield
    # Cleanup
    if DEVICE == "cuda":
        torch.cuda.empty_cache()


app = FastAPI(
    title="Kokoro TTS API",
    description="OpenAI-compatible TTS API using Kokoro",
    version="1.0.0",
    lifespan=lifespan
)


@app.get("/health")
async def health_check():
    """Health check endpoint."""
    return {"status": "healthy", "model": "kokoro"}


@app.get("/v1/models")
async def list_models():
    """List available models (OpenAI-compatible)."""
    return {
        "object": "list",
        "data": [{"id": "kokoro", "name": "Kokoro TTS", "owned_by": "myia"}]
    }


@app.get("/v1/voices")
async def list_voices():
    """List available voices (OpenAI-compatible)."""
    voices = []
    for openai_voice, kokoro_voice in AVAILABLE_VOICES.items():
        voices.append({"id": openai_voice, "name": openai_voice.capitalize()})
    return {"voices": voices}


@app.post("/v1/audio/speech")
async def text_to_speech(request: TTSRequest):
    """Generate speech from text (OpenAI-compatible endpoint)."""
    try:
        # Get or load model
        model, pipeline = model_manager.get_model()

        # Map OpenAI voice to Kokoro voice
        kokoro_voice = AVAILABLE_VOICES.get(request.voice, "af_sky")

        # Generate audio
        logger.info(f"Generating speech for text: {request.input[:50]}...")
        logger.info(f"Voice: {kokoro_voice}, Speed: {request.speed}")

        # Use Kokoro pipeline - yields KPipeline.Result objects
        result = pipeline(request.input, voice=kokoro_voice, speed=request.speed)

        # Collect audio from generator
        audio_segments = []

        for segment in result:
            # KPipeline.Result has .output.audio attribute
            if hasattr(segment, 'output') and hasattr(segment.output, 'audio'):
                audio_tensor = segment.output.audio
                # Convert torch tensor to numpy
                if hasattr(audio_tensor, 'cpu'):
                    audio_segments.append(audio_tensor.cpu().numpy())
                else:
                    audio_segments.append(audio_tensor)
            elif isinstance(segment, np.ndarray):
                audio_segments.append(segment)
            elif isinstance(segment, tuple) and len(segment) > 0:
                if isinstance(segment[0], np.ndarray):
                    audio_segments.append(segment[0])

        if not audio_segments:
            raise ValueError("No audio segments generated from Kokoro pipeline")

        # Concatenate all audio segments
        audio_array = np.concatenate(audio_segments)
        sample_rate = SAMPLE_RATE  # Kokoro uses 24000 Hz by default

        # Convert to bytes using wave library (torchaudio.save doesn't support BytesIO)
        import wave
        buffer = io.BytesIO()

        # Ensure audio is in the right format (float32 -> int16)
        if audio_array.dtype == np.float32 or audio_array.dtype == np.float64:
            # Normalize to [-1, 1] then convert to int16
            audio_array = np.clip(audio_array, -1.0, 1.0)
            audio_array = (audio_array * 32767).astype(np.int16)

        with wave.open(buffer, 'wb') as wav_file:
            wav_file.setnchannels(1)  # Mono
            wav_file.setsampwidth(2)  # 2 bytes for int16
            wav_file.setframerate(sample_rate)
            wav_file.writeframes(audio_array.tobytes())

        buffer.seek(0)

        # Return streaming response
        return StreamingResponse(
            buffer,
            media_type="audio/wav",
            headers={
                "Content-Disposition": f'attachment; filename="speech.wav"',
                "X-Model-Used": "kokoro",
                "X-Voice-Used": kokoro_voice
            }
        )

    except Exception as e:
        logger.error(f"TTS generation failed: {e}")
        raise HTTPException(status_code=500, detail=str(e))


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
