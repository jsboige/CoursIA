#!/usr/bin/env python3
"""
TADA 3B ML TTS Service - OpenAI-compatible API
HumeAI's voice cloning model (Llama 3.2 fine-tune)
"""

import os
import io
import logging
from contextlib import asynccontextmanager
from typing import Optional

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

# Voice mapping for OpenAI compatibility
# TADA uses reference audio for voice cloning
AVAILABLE_VOICES = {
    "alloy": "default",
    "echo": "default",
    "fable": "default",
    "onyx": "default",
    "nova": "default",
    "shimmer": "default",
}

# Global model instances
_encoder = None
_model = None


class LazyModelManager:
    """Manages lazy loading and unloading of TTS models."""

    def __init__(self, idle_timeout: int = IDLE_TIMEOUT):
        self.idle_timeout = idle_timeout
        self.last_used = None
        self.encoder = None
        self.model = None

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


# Default reference audio for TTS without custom voice
# This is a simple generated tone that serves as fallback
def get_default_reference():
    """Generate a simple default reference audio."""
    # Create 1 second of silence as default reference
    # In production, you'd want a real voice sample
    sample_rate = SAMPLE_RATE
    duration = 1.0
    silence = torch.zeros(1, int(sample_rate * duration))
    return silence, sample_rate, ""


@app.post("/v1/audio/speech")
async def text_to_speech(request: TTSRequest):
    """Generate speech from text (OpenAI-compatible endpoint)."""
    try:
        # Get or load model
        encoder, model = model_manager.get_model()

        # Get reference audio (default or custom)
        ref_audio, ref_sr, ref_text = get_default_reference()
        ref_audio = ref_audio.to(DEVICE)

        logger.info(f"Generating speech for text: {request.input[:50]}...")

        # Create prompt from reference
        if ref_text:
            prompt = encoder(ref_audio, text=[ref_text], sample_rate=ref_sr)
        else:
            # For empty reference text, just encode the audio
            prompt = encoder(ref_audio, sample_rate=ref_sr)

        # Generate speech
        with torch.no_grad():
            output = model.generate(
                prompt=prompt,
                text=request.input,
            )

        # Extract audio from output
        if hasattr(output, 'audio'):
            audio_tensor = output.audio
        elif isinstance(output, tuple):
            audio_tensor = output[0] if len(output) > 0 else None
        else:
            audio_tensor = output

        if audio_tensor is None:
            raise ValueError("No audio generated from TADA model")

        # Convert to numpy
        if hasattr(audio_tensor, 'cpu'):
            audio_array = audio_tensor.cpu().numpy().squeeze()
        else:
            audio_array = np.array(audio_tensor).squeeze()

        # Ensure correct format
        if audio_array.dtype == np.float32 or audio_array.dtype == np.float64:
            audio_array = np.clip(audio_array, -1.0, 1.0)
            audio_array = (audio_array * 32767).astype(np.int16)

        # Write to WAV
        import wave
        buffer = io.BytesIO()
        with wave.open(buffer, 'wb') as wav_file:
            wav_file.setnchannels(1)
            wav_file.setsampwidth(2)
            wav_file.setframerate(SAMPLE_RATE)
            wav_file.writeframes(audio_array.tobytes())

        buffer.seek(0)

        # Return streaming response
        return StreamingResponse(
            buffer,
            media_type="audio/wav",
            headers={
                "Content-Disposition": 'attachment; filename="speech.wav"',
                "X-Model-Used": "tada"
            }
        )

    except Exception as e:
        logger.error(f"TTS generation failed: {e}")
        raise HTTPException(status_code=500, detail=str(e))


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
