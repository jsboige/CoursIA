#!/usr/bin/env python3
"""
Demucs API - HTTP API for music source separation

Features:
- Lazy loading with auto-unload after inactivity
- GPU memory management
- Extract stems: vocals, drums, bass, other
"""

import os
import sys
import time
import io
import logging
import tempfile
import zipfile
import asyncio
from typing import Optional, List
from pathlib import Path

from fastapi import FastAPI, File, UploadFile, HTTPException, BackgroundTasks
from fastapi.responses import Response, JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import torch
import numpy as np
import soundfile as sf

# Add shared module to path
sys.path.insert(0, "/app/shared")
from lazy_model import LazyModelManager, idle_checker_task, get_all_status

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("demucs-api")

# Configuration from environment
DEFAULT_MODEL = os.getenv("DEMUCS_MODEL", "htdemucs_ft")
DEVICE = os.getenv("DEMUCS_DEVICE", "cuda")
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "300"))  # 5 minutes default
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "false").lower() == "true"
OUTPUT_DIR = Path(os.getenv("OUTPUT_DIR", "/app/outputs"))
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# Stem names for htdemucs models
STEM_NAMES = ["drums", "bass", "other", "vocals"]

app = FastAPI(
    title="Demucs API",
    description="HTTP API for music source separation using Demucs v4 with auto-unload",
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


class DemucsModelWrapper:
    """Wrapper to hold model and apply function"""
    def __init__(self, model, apply_fn):
        self.model = model
        self.apply_fn = apply_fn


def _load_demucs_model():
    """Load the Demucs model"""
    from demucs.pretrained import get_model
    from demucs.apply import apply_model

    logger.info(f"Loading Demucs model: {DEFAULT_MODEL}")
    start = time.time()

    model = get_model(DEFAULT_MODEL)
    model.to(DEVICE)
    model.eval()

    load_time = time.time() - start
    logger.info(f"Demucs loaded in {load_time:.1f}s")

    return DemucsModelWrapper(model, apply_model)


def _unload_demucs_model(wrapper):
    """Unload Demucs model and free GPU memory"""
    del wrapper.model
    del wrapper.apply_fn
    del wrapper
    if torch.cuda.is_available():
        torch.cuda.empty_cache()


# Model manager with lazy loading and auto-unload
model_manager = LazyModelManager(
    model_name="demucs",
    load_fn=_load_demucs_model,
    unload_fn=_unload_demucs_model,
    idle_timeout=IDLE_TIMEOUT,
    device=DEVICE,
    preload=PRELOAD_MODEL
)


class SeparationResponse(BaseModel):
    stems: dict
    duration: float
    processing_time: float
    sample_rate: int


class StemInfo(BaseModel):
    name: str
    duration: float
    sample_rate: int
    format: str


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
        "idle_timeout": IDLE_TIMEOUT
    }


@app.get("/v1/models")
async def list_models():
    """List available Demucs models"""
    return {
        "models": [
            {"id": "htdemucs", "name": "Hybrid Transformer Demucs", "quality": "best", "vram": "4GB"},
            {"id": "htdemucs_ft", "name": "Hybrid Transformer Demucs (Fine-tuned)", "quality": "excellent", "vram": "4GB"},
            {"id": "mdx", "name": "MDX", "quality": "good", "vram": "2GB"},
            {"id": "mdx_extra", "name": "MDX Extra", "quality": "better", "vram": "3GB"},
        ],
        "current": DEFAULT_MODEL
    }


@app.get("/v1/stems")
async def list_stems():
    """List available stems"""
    return {
        "stems": [
            {"id": "vocals", "name": "Vocals", "description": "Voice and singing"},
            {"id": "drums", "name": "Drums", "description": "Percussion and drums"},
            {"id": "bass", "name": "Bass", "description": "Bass instruments"},
            {"id": "other", "name": "Other", "description": "All other instruments"},
        ]
    }


@app.post("/v1/separate")
async def separate_sources(
    file: UploadFile = File(...),
    model: str = "htdemucs_ft",
    output_format: str = "wav",
    stems: Optional[str] = None,  # comma-separated stem names
    return_zip: bool = True
):
    """
    Separate audio into stems (vocals, drums, bass, other)

    - **file**: Audio file to separate
    - **model**: Demucs model to use (htdemucs, htdemucs_ft, mdx)
    - **output_format**: Output format (wav, mp3, flac)
    - **stems**: Comma-separated stems to extract (default: all)
    - **return_zip**: Return all stems as a zip file
    """
    start_time = time.time()

    # Load model (lazy with auto-unload)
    wrapper = model_manager.get_model()
    demucs_model = wrapper.model
    apply_fn = wrapper.apply_fn

    # Parse requested stems
    requested_stems = STEM_NAMES
    if stems:
        requested_stems = [s.strip().lower() for s in stems.split(",") if s.strip().lower() in STEM_NAMES]
        if not requested_stems:
            requested_stems = STEM_NAMES

    # Read uploaded file
    content = await file.read()

    # Save to temp file
    suffix = Path(file.filename or "audio.mp3").suffix
    with tempfile.NamedTemporaryFile(delete=False, suffix=suffix) as tmp:
        tmp.write(content)
        tmp_path = tmp.name

    try:
        logger.info(f"Separating: {file.filename} ({len(content)/1024:.1f} KB)")

        # Load audio
        import torchaudio
        wav, sr = torchaudio.load(tmp_path)

        # Convert to stereo if mono
        if wav.shape[0] == 1:
            wav = wav.repeat(2, 1)
        elif wav.shape[0] > 2:
            wav = wav[:2]

        # Resample to model's expected sample rate
        target_sr = demucs_model.samplerate
        if sr != target_sr:
            resampler = torchaudio.transforms.Resample(sr, target_sr)
            wav = resampler(wav)

        # Add batch dimension
        wav = wav.unsqueeze(0).to(DEVICE)

        # Apply model
        with torch.no_grad():
            sources = apply_fn(demucs_model, wav[None], progress=None)[0]

        # sources shape: [batch, sources, channels, time]
        sources = sources.cpu()

        # Duration
        duration = wav.shape[-1] / target_sr
        elapsed = time.time() - start_time
        logger.info(f"Separated {duration:.1f}s audio in {elapsed:.2f}s")

        # Prepare stems
        stem_audios = {}
        for i, stem_name in enumerate(STEM_NAMES):
            if stem_name in requested_stems:
                stem_audio = sources[0, i].numpy()
                # Transpose to (samples, channels)
                stem_audio = stem_audio.T
                stem_audios[stem_name] = stem_audio

        if return_zip and len(stem_audios) > 1:
            # Return as zip
            zip_buffer = io.BytesIO()
            with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
                for stem_name, audio in stem_audios.items():
                    stem_buffer = io.BytesIO()
                    sf.write(stem_buffer, audio, target_sr, format='WAV')
                    stem_buffer.seek(0)
                    zf.writestr(f"{stem_name}.wav", stem_buffer.read())

            zip_buffer.seek(0)
            return Response(
                content=zip_buffer.read(),
                media_type="application/zip",
                headers={
                    "Content-Disposition": f"attachment; filename={Path(file.filename).stem}_stems.zip",
                    "X-Duration": str(duration),
                    "X-Processing-Time": f"{elapsed:.2f}",
                    "X-Stems": ",".join(stem_audios.keys())
                }
            )
        else:
            # Return single stem
            stem_name = list(stem_audios.keys())[0]
            audio = stem_audios[stem_name]

            buffer = io.BytesIO()
            sf.write(buffer, audio, target_sr, format='WAV')
            buffer.seek(0)

            return Response(
                content=buffer.read(),
                media_type="audio/wav",
                headers={
                    "Content-Disposition": f"attachment; filename={stem_name}.wav",
                    "X-Stem": stem_name,
                    "X-Duration": str(duration)
                }
            )

    except Exception as e:
        logger.error(f"Separation error: {str(e)}")
        raise HTTPException(status_code=500, detail=str(e))
    finally:
        try:
            os.unlink(tmp_path)
        except:
            pass


@app.post("/v1/separate/vocals")
async def extract_vocals(file: UploadFile = File(...)):
    """Quick endpoint to extract only vocals"""
    return await separate_sources(
        file=file,
        stems="vocals",
        return_zip=False
    )


@app.post("/v1/separate/instrumental")
async def extract_instrumental(file: UploadFile = File(...)):
    """Quick endpoint to extract instrumental (all except vocals)"""
    return await separate_sources(
        file=file,
        stems="drums,bass,other",
        return_zip=True
    )


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
    uvicorn.run(app, host="0.0.0.0", port=8193)
