#!/usr/bin/env python3
"""
FunASR API - FastAPI wrapper for FunASR (Fun-ASR-Nano-2512)
OpenAI-compatible API for multilingual speech-to-text

Features:
- Lazy loading with auto-unload after inactivity (shared LazyModelManager)
- GPU memory management
- OpenAI-compatible /v1/audio/transcriptions endpoint
- VAD-based segmentation via fsmn-vad
- 31 languages supported (auto-detected)
"""

import os
import sys
import time
import tempfile
import logging
import asyncio
from typing import Optional, List
from pathlib import Path

from fastapi import FastAPI, File, UploadFile, Form, HTTPException
from fastapi.responses import JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

# Add shared module to path
sys.path.insert(0, "/app/shared")
from lazy_model import LazyModelManager, idle_checker_task
from auth_middleware import setup_auth

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("funasr-api")

# Set HuggingFace token for gated model downloads
HF_TOKEN = os.getenv("HF_TOKEN", "")
if HF_TOKEN:
    os.environ["HUGGING_FACE_HUB_TOKEN"] = HF_TOKEN
    os.environ["HF_TOKEN"] = HF_TOKEN
    logger.info("HuggingFace token configured")

# Configuration from environment
FUNASR_MODEL = os.getenv("FUNASR_MODEL", "FunAudioLLM/Fun-ASR-Nano-2512")
VAD_MODEL = os.getenv("VAD_MODEL", "fsmn-vad")
DEVICE = os.getenv("FUNASR_DEVICE", "cuda")
FUNASR_MODEL_CODE = os.getenv("FUNASR_MODEL_CODE", "/app/fun-asr-code/model.py")
MAX_FILE_SIZE = int(os.getenv("MAX_FILE_SIZE", 25 * 1024 * 1024))  # 25MB
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "300"))  # 5 minutes
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "false").lower() == "true"
MAX_SINGLE_SEGMENT_TIME = int(os.getenv("MAX_SINGLE_SEGMENT_TIME", "30000"))  # ms

app = FastAPI(
    title="FunASR API",
    description="OpenAI-compatible ASR API using FunASR with auto-unload and VAD",
    version="1.0.0"
)

# CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Bearer token authentication
setup_auth(app)


def _load_funasr_model():
    """Load the FunASR model with CUDA fallback to CPU."""
    from funasr import AutoModel

    device = DEVICE

    if device == "cuda":
        try:
            import torch
            if not torch.cuda.is_available():
                logger.warning("CUDA not available, falling back to CPU")
                device = "cpu"
        except Exception as e:
            logger.warning(f"CUDA check failed: {e}, falling back to CPU")
            device = "cpu"

    logger.info(f"Loading FunASR model: {FUNASR_MODEL} on {device}")
    try:
        model = AutoModel(
            model=FUNASR_MODEL,
            trust_remote_code=True,
            remote_code=FUNASR_MODEL_CODE,
            vad_model=VAD_MODEL,
            vad_kwargs={"max_single_segment_time": MAX_SINGLE_SEGMENT_TIME},
            device=device,
        )
        return model
    except RuntimeError as e:
        if "cuda" in str(e).lower() or "cublas" in str(e).lower():
            logger.warning(f"CUDA error: {e}, falling back to CPU")
            return AutoModel(
                model=FUNASR_MODEL,
                trust_remote_code=True,
                remote_code=FUNASR_MODEL_CODE,
                vad_model=VAD_MODEL,
                vad_kwargs={"max_single_segment_time": MAX_SINGLE_SEGMENT_TIME},
                device="cpu",
            )
        raise


def _unload_funasr_model(model):
    """Unload FunASR model and free GPU memory."""
    del model
    try:
        import torch
        if torch.cuda.is_available():
            torch.cuda.empty_cache()
    except Exception:
        pass


# Model manager with lazy loading and auto-unload
model_manager = LazyModelManager(
    model_name="funasr",
    load_fn=_load_funasr_model,
    unload_fn=_unload_funasr_model,
    idle_timeout=IDLE_TIMEOUT,
    device=DEVICE,
    preload=PRELOAD_MODEL
)


# Response models (OpenAI-compatible)
class TranscriptionWord(BaseModel):
    word: str
    start: float
    end: float
    probability: float


class TranscriptionSegment(BaseModel):
    id: int
    start: float
    end: float
    text: str


class TranscriptionResponse(BaseModel):
    text: str
    language: Optional[str] = None
    duration: Optional[float] = None
    words: Optional[List[TranscriptionWord]] = None
    segments: Optional[List[TranscriptionSegment]] = None


def _convert_audio_to_wav(input_path: str) -> str:
    """Convert audio to 16kHz mono WAV using ffmpeg (FunASR's expected format)."""
    output_path = input_path.rsplit(".", 1)[0] + "_converted.wav"
    import subprocess
    result = subprocess.run(
        ["ffmpeg", "-y", "-i", input_path, "-ar", "16000", "-ac", "1",
         "-f", "wav", output_path],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        logger.warning(f"ffmpeg conversion warning: {result.stderr}")
        return input_path
    return output_path


@app.get("/health")
async def health_check():
    """Health check endpoint."""
    cuda_available = False
    gpu_name = None
    gpu_memory = 0

    try:
        import torch
        cuda_available = torch.cuda.is_available()
        if cuda_available:
            import subprocess
            result = subprocess.run(
                ["nvidia-smi", "--query-gpu=name,memory.used", "--format=csv,noheader,nounits"],
                capture_output=True, text=True
            )
            if result.returncode == 0:
                parts = result.stdout.strip().split("\n")[0].split(",")
                gpu_name = parts[0].strip()
                gpu_memory = float(parts[1].strip()) / 1024
    except Exception as e:
        logger.debug(f"GPU check failed: {e}")

    status = model_manager.status

    return {
        "status": "healthy",
        "model": FUNASR_MODEL,
        "vad_model": VAD_MODEL,
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
    """List available models (OpenAI-compatible)."""
    return {
        "object": "list",
        "data": [
            {
                "id": "funasr-1",
                "object": "model",
                "created": 1735084800,
                "owned_by": "funasr"
            }
        ]
    }


@app.post("/v1/audio/transcriptions", response_model=TranscriptionResponse)
async def transcribe_audio(
    file: UploadFile = File(...),
    model: str = Form("funasr-1"),
    language: Optional[str] = Form(None),
    prompt: Optional[str] = Form(None),
    response_format: str = Form("json"),
    temperature: float = Form(0.0),
    timestamp_granularities: List[str] = Form(["segment"])
):
    """
    Transcribe audio file (OpenAI-compatible endpoint).

    - **file**: Audio file (mp3, mp4, mpeg, mpga, m4a, wav, webm, ogg, flac)
    - **model**: Model to use (funasr-1)
    - **language**: Language hint (auto-detected if not specified)
    - **response_format**: 'json', 'text', 'verbose_json'
    - **timestamp_granularities**: ['word'] or ['segment']
    """
    start_time = time.time()

    # Validate file size
    content = await file.read()
    if len(content) > MAX_FILE_SIZE:
        raise HTTPException(status_code=413, detail=f"File too large. Max: {MAX_FILE_SIZE / 1024 / 1024}MB")

    # Save to temp file
    suffix = Path(file.filename or "audio.wav").suffix
    with tempfile.NamedTemporaryFile(delete=False, suffix=suffix) as tmp:
        tmp.write(content)
        tmp_path = tmp.name

    converted_path = None
    try:
        # Convert to WAV for FunASR compatibility
        converted_path = _convert_audio_to_wav(tmp_path)
        audio_path = converted_path

        # Get duration using soundfile
        import soundfile as sf
        try:
            info_data, sr = sf.read(audio_path)
            audio_duration = len(info_data) / sr
        except Exception:
            audio_duration = 0.0

        # Load model (lazy with auto-unload)
        funasr_model = model_manager.get_model()

        # Run transcription
        # FunASR generate returns list of results
        # batch_size_s=0 required — FunASRNano does not implement batch decoding
        res = funasr_model.generate(
            input=audio_path,
            cache={},
            batch_size_s=0,
        )

        # Extract text from FunASR result
        full_text = ""
        segments_data = []

        if res and len(res) > 0:
            result = res[0]
            full_text = result.get("text", "").strip()

            # Extract segments if available (timestamp info from FunASR)
            if "sentence_info" in result:
                for i, seg in enumerate(result["sentence_info"]):
                    segments_data.append({
                        "id": i,
                        "start": seg.get("start", 0) / 1000.0,  # ms to seconds
                        "end": seg.get("end", 0) / 1000.0,
                        "text": seg.get("text", "").strip()
                    })

        elapsed = time.time() - start_time
        logger.info(f"Transcribed {audio_duration:.1f}s audio in {elapsed:.2f}s")

        # Format response
        if response_format == "text":
            return JSONResponse(content=full_text, media_type="text/plain")

        response = TranscriptionResponse(
            text=full_text,
            duration=audio_duration
        )

        if response_format == "verbose_json" or "segment" in timestamp_granularities:
            if segments_data:
                response.segments = [TranscriptionSegment(**s) for s in segments_data]

        return response

    finally:
        for path in [tmp_path, converted_path]:
            if path:
                try:
                    os.unlink(path)
                except Exception:
                    pass


@app.post("/admin/unload")
async def force_unload():
    """Force unload the model (admin endpoint)."""
    unloaded = model_manager.force_unload()
    return {"unloaded": unloaded, "status": model_manager.status}


@app.on_event("startup")
async def startup_event():
    """Start background idle checker."""
    asyncio.create_task(idle_checker_task(interval=60))
    logger.info(f"Started idle checker (timeout: {IDLE_TIMEOUT}s)")


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8194)
