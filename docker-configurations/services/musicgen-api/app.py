#!/usr/bin/env python3
"""
MusicGen API - HTTP API for music generation using Meta's MusicGen

Features:
- Lazy loading with auto-unload after inactivity
- GPU memory management
- OpenAI-style API
"""

import os
import sys
import time
import io
import logging
import asyncio
from typing import Optional, List
from pathlib import Path

from fastapi import FastAPI, HTTPException, BackgroundTasks
from fastapi.responses import Response, JSONResponse, FileResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import torch
import numpy as np
import scipy.io.wavfile as wavfile

# Add shared module to path
sys.path.insert(0, "/app/shared")
from lazy_model import LazyModelManager, idle_checker_task, get_all_status

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("musicgen-api")

# Configuration from environment
DEFAULT_MODEL = os.getenv("MUSICGEN_MODEL", "facebook/musicgen-medium")
DEVICE = os.getenv("MUSICGEN_DEVICE", "cuda")
MAX_DURATION = int(os.getenv("MAX_DURATION", 30))
DEFAULT_DURATION = int(os.getenv("DEFAULT_DURATION", 10))
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "300"))  # 5 minutes default
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "false").lower() == "true"
OUTPUT_DIR = Path(os.getenv("OUTPUT_DIR", "/app/outputs"))
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

app = FastAPI(
    title="MusicGen API",
    description="HTTP API for music generation using Meta's MusicGen with auto-unload",
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


class MusicGenModelWrapper:
    """Wrapper to hold both model and processor"""
    def __init__(self, model, processor):
        self.model = model
        self.processor = processor


def _load_musicgen_model():
    """Load the MusicGen model using transformers"""
    from transformers import AutoModelForTextToWaveform, AutoProcessor
    logger.info(f"Loading MusicGen model: {DEFAULT_MODEL}")
    start = time.time()

    processor = AutoProcessor.from_pretrained(DEFAULT_MODEL)
    model = AutoModelForTextToWaveform.from_pretrained(DEFAULT_MODEL)

    if DEVICE == "cuda" and torch.cuda.is_available():
        model = model.to("cuda")

    load_time = time.time() - start
    logger.info(f"MusicGen loaded in {load_time:.1f}s")

    return MusicGenModelWrapper(model, processor)


def _unload_musicgen_model(wrapper):
    """Unload MusicGen model and free GPU memory"""
    del wrapper.model
    del wrapper.processor
    del wrapper
    if torch.cuda.is_available():
        torch.cuda.empty_cache()


# Model manager with lazy loading and auto-unload
model_manager = LazyModelManager(
    model_name="musicgen",
    load_fn=_load_musicgen_model,
    unload_fn=_unload_musicgen_model,
    idle_timeout=IDLE_TIMEOUT,
    device=DEVICE,
    preload=PRELOAD_MODEL
)


# Request/Response models
class GenerateRequest(BaseModel):
    prompt: str
    duration: int = DEFAULT_DURATION
    temperature: float = 1.0
    top_k: int = 250
    top_p: float = 0.0
    cfg_coef: float = 3.0
    seed: Optional[int] = None
    format: str = "wav"  # wav, mp3


class GenerationStatus(BaseModel):
    job_id: str
    status: str  # pending, processing, completed, failed
    progress: float
    message: str


# Storage for async jobs
jobs = {}


@app.get("/health")
async def health_check():
    """Health check endpoint"""
    try:
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
        "model": DEFAULT_MODEL,
        "device": DEVICE,
        "cuda_available": cuda_available,
        "gpu_name": gpu_name,
        "gpu_memory_gb": round(gpu_memory, 2),
        "model_loaded": status["loaded"],
        "idle_seconds": status.get("idle_seconds"),
        "idle_timeout": IDLE_TIMEOUT,
        "max_duration": MAX_DURATION
    }


@app.get("/v1/models")
async def list_models():
    """List available models"""
    return {
        "models": [
            {"id": "facebook/musicgen-small", "params": "300M", "vram": "4GB"},
            {"id": "facebook/musicgen-medium", "params": "1.5B", "vram": "10GB"},
            {"id": "facebook/musicgen-large", "params": "3.3B", "vram": "20GB"},
            {"id": "facebook/musicgen-melody", "params": "1.5B", "vram": "10GB"},
        ],
        "current": DEFAULT_MODEL
    }


@app.post("/v1/generate")
async def generate_music(request: GenerateRequest):
    """
    Generate music from text description using transformers

    - **prompt**: Text description of the music to generate
    - **duration**: Duration in seconds (1-30)
    - **temperature**: Sampling temperature (0.5-1.5)
    - **top_k**: Top-k sampling (0-1000)
    - **cfg_coef**: Classifier-free guidance coefficient (1-10)
    - **seed**: Random seed for reproducibility
    - **format**: Output format (wav, mp3)
    """
    start_time = time.time()

    # Validate
    if not request.prompt.strip():
        raise HTTPException(status_code=400, detail="Prompt cannot be empty")

    if request.duration < 1 or request.duration > MAX_DURATION:
        raise HTTPException(status_code=400, detail=f"Duration must be between 1 and {MAX_DURATION} seconds")

    # Load model (lazy with auto-unload)
    wrapper = model_manager.get_model()
    musicgen = wrapper.model
    processor = wrapper.processor

    # Set seed if provided
    if request.seed is not None:
        torch.manual_seed(request.seed)
        generator = torch.Generator(device="cuda" if torch.cuda.is_available() else "cpu")
        generator.manual_seed(request.seed)
    else:
        generator = None

    logger.info(f"Generating {request.duration}s music: {request.prompt[:50]}...")

    try:
        # Generate using transformers
        inputs = processor(
            [request.prompt],
            padding=True,
            return_tensors="pt"
        )

        if torch.cuda.is_available():
            inputs = {k: v.to("cuda") for k, v in inputs.items()}

        with torch.no_grad():
            audio_values = musicgen.generate(
                **inputs,
                max_new_tokens=request.duration * 50,  # approximate tokens
                do_sample=True,
                temperature=request.temperature,
                top_k=request.top_k if request.top_k > 0 else 50,
                generator=generator
            )

        # Get audio data
        audio = audio_values.audios[0].cpu().numpy()
        sample_rate = 32000  # MusicGen default sample rate

        # Normalize
        max_val = np.max(np.abs(audio))
        if max_val > 0:
            audio = audio / max_val * 0.95

        elapsed = time.time() - start_time
        logger.info(f"Generated {request.duration}s audio in {elapsed:.2f}s")

        # Encode response
        buffer = io.BytesIO()

        if request.format == "mp3":
            # Convert to mp3 using ffmpeg
            import subprocess
            wav_buffer = io.BytesIO()
            wavfile.write(wav_buffer, sample_rate, (audio * 32767).astype(np.int16))
            wav_buffer.seek(0)

            process = subprocess.run(
                ['ffmpeg', '-i', 'pipe:0', '-f', 'mp3', '-acodec', 'libmp3lame', '-ab', '192k', 'pipe:1'],
                input=wav_buffer.read(),
                capture_output=True
            )
            buffer = io.BytesIO(process.stdout)
            media_type = "audio/mpeg"
        else:
            wavfile.write(buffer, sample_rate, (audio * 32767).astype(np.int16))
            media_type = "audio/wav"

        buffer.seek(0)

        return Response(
            content=buffer.read(),
            media_type=media_type,
            headers={
                "X-Duration": str(request.duration),
                "X-Generation-Time": f"{elapsed:.2f}",
                "X-Sample-Rate": str(sample_rate)
            }
        )

    except Exception as e:
        logger.error(f"Generation error: {str(e)}")
        raise HTTPException(status_code=500, detail=str(e))


@app.post("/v1/generate/async")
async def generate_music_async(request: GenerateRequest, background_tasks: BackgroundTasks):
    """Start async music generation job"""
    import uuid
    job_id = str(uuid.uuid4())[:8]

    jobs[job_id] = {
        "status": "pending",
        "progress": 0.0,
        "message": "Job queued"
    }

    return {"job_id": job_id, "status": "pending"}


@app.get("/v1/jobs/{job_id}")
async def get_job_status(job_id: str):
    """Get status of async generation job"""
    if job_id not in jobs:
        raise HTTPException(status_code=404, detail="Job not found")

    return jobs[job_id]


@app.post("/admin/unload")
async def force_unload():
    """Force unload the model (admin endpoint)"""
    unloaded = model_manager.force_unload()
    return {"unloaded": unloaded, "status": model_manager.status}


@app.on_event("startup")
async def startup_event():
    """Start background idle checker"""
    asyncio.create_task(idle_checker_task(interval=60))
    logger.info(f"Started idle checker (timeout: {IDLE_TIMEOUT}s)")


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8192)
