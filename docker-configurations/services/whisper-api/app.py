#!/usr/bin/env python3
"""
Whisper API - FastAPI wrapper for faster-whisper
Compatible with OpenAI Whisper API format for easy fallback

Features:
- Lazy loading with auto-unload after inactivity
- GPU memory management
- OpenAI-compatible API
"""

import os
import sys
import time
import tempfile
import logging
import asyncio
from typing import Optional, List
from pathlib import Path

from fastapi import FastAPI, File, UploadFile, Form, HTTPException, Depends
from fastapi.responses import JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

# Add shared module to path
sys.path.insert(0, "/app/shared")
from lazy_model import LazyModelManager, idle_checker_task, get_all_status

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("whisper-api")

# Configuration from environment
MODEL_SIZE = os.getenv("WHISPER_MODEL", "large-v3-turbo")
DEVICE = os.getenv("WHISPER_DEVICE", "cuda")
COMPUTE_TYPE = os.getenv("WHISPER_COMPUTE_TYPE", "float16")
MAX_FILE_SIZE = int(os.getenv("MAX_FILE_SIZE", 25 * 1024 * 1024))  # 25MB
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "300"))  # 5 minutes default
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "true").lower() == "true"

app = FastAPI(
    title="Whisper API",
    description="OpenAI-compatible Whisper API using faster-whisper with auto-unload",
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


def _load_whisper_model():
    """Load the Whisper model with CUDA fallback to CPU."""
    from faster_whisper import WhisperModel

    device = DEVICE
    compute_type = COMPUTE_TYPE

    # Try CUDA first, fallback to CPU if libraries missing
    if device == "cuda":
        try:
            import ctranslate2
            if ctranslate2.get_cuda_device_count() == 0:
                logger.warning("CUDA not available, falling back to CPU")
                device = "cpu"
                compute_type = "int8"
        except Exception as e:
            logger.warning(f"CUDA check failed: {e}, falling back to CPU")
            device = "cpu"
            compute_type = "int8"

    logger.info(f"Loading Whisper model: {MODEL_SIZE} on {device} ({compute_type})")
    try:
        return WhisperModel(MODEL_SIZE, device=device, compute_type=compute_type)
    except RuntimeError as e:
        if "cublas" in str(e).lower() or "cuda" in str(e).lower():
            logger.warning(f"CUDA library error: {e}, falling back to CPU")
            return WhisperModel(MODEL_SIZE, device="cpu", compute_type="int8")
        raise


def _unload_whisper_model(model):
    """Unload Whisper model and free GPU memory."""
    del model
    try:
        import torch
        if torch.cuda.is_available():
            torch.cuda.empty_cache()
    except:
        pass


# Model manager with lazy loading and auto-unload
model_manager = LazyModelManager(
    model_name="whisper",
    load_fn=_load_whisper_model,
    unload_fn=_unload_whisper_model,
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
    seek: int
    start: float
    end: float
    text: str
    tokens: List[int]
    temperature: float
    avg_logprob: float
    compression_ratio: float
    no_speech_prob: float


class TranscriptionResponse(BaseModel):
    text: str
    language: Optional[str] = None
    duration: Optional[float] = None
    words: Optional[List[TranscriptionWord]] = None
    segments: Optional[List[dict]] = None


class ErrorResponse(BaseModel):
    error: dict


@app.get("/health")
async def health_check():
    """Health check endpoint"""
    cuda_available = False
    gpu_name = None
    gpu_memory = 0

    try:
        import ctranslate2
        cuda_available = ctranslate2.get_cuda_device_count() > 0
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
        logger.debug(f"CUDA check failed: {e}")

    status = model_manager.status

    return {
        "status": "healthy",
        "model": MODEL_SIZE,
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
    """List available models (OpenAI-compatible)"""
    return {
        "object": "list",
        "data": [
            {
                "id": "whisper-1",
                "object": "model",
                "created": 1677610602,
                "owned_by": "system"
            }
        ]
    }


@app.post("/v1/audio/transcriptions", response_model=TranscriptionResponse)
async def transcribe_audio(
    file: UploadFile = File(...),
    model: str = Form("whisper-1"),
    language: Optional[str] = Form(None),
    prompt: Optional[str] = Form(None),
    response_format: str = Form("json"),
    temperature: float = Form(0.0),
    timestamp_granularities: List[str] = Form(["segment"])
):
    """
    Transcribe audio file (OpenAI-compatible endpoint)

    - **file**: Audio file to transcribe (mp3, mp4, mpeg, mpga, m4a, wav, webm)
    - **model**: Model to use (whisper-1)
    - **language**: Language code (e.g., 'fr', 'en'). Auto-detected if not specified.
    - **prompt**: Optional context to improve transcription
    - **response_format**: 'json', 'text', 'srt', 'verbose_json', 'vtt'
    - **temperature**: Sampling temperature (0.0-1.0)
    - **timestamp_granularities**: ['word'] or ['segment']
    """
    start_time = time.time()

    # Validate file size
    content = await file.read()
    if len(content) > MAX_FILE_SIZE:
        raise HTTPException(status_code=413, detail=f"File too large. Max size: {MAX_FILE_SIZE / 1024 / 1024}MB")

    # Load model (lazy with auto-unload)
    whisper_model = model_manager.get_model()

    # Save to temp file
    suffix = Path(file.filename or "audio.mp3").suffix
    with tempfile.NamedTemporaryFile(delete=False, suffix=suffix) as tmp:
        tmp.write(content)
        tmp_path = tmp.name

    try:
        # Transcribe
        word_timestamps = "word" in timestamp_granularities
        segments_generator, info = whisper_model.transcribe(
            tmp_path,
            language=language,
            initial_prompt=prompt,
            temperature=temperature,
            word_timestamps=word_timestamps,
            beam_size=5
        )

        # Collect segments
        segments_list = list(segments_generator)

        # Build response
        full_text = " ".join([s.text.strip() for s in segments_list])
        elapsed = time.time() - start_time

        logger.info(f"Transcribed {info.duration:.1f}s audio in {elapsed:.2f}s (lang: {info.language})")

        # Format response based on response_format
        if response_format == "text":
            return JSONResponse(content=full_text, media_type="text/plain")

        elif response_format == "srt":
            srt_content = format_srt(segments_list)
            return JSONResponse(content=srt_content, media_type="text/plain")

        elif response_format == "vtt":
            vtt_content = format_vtt(segments_list)
            return JSONResponse(content=vtt_content, media_type="text/plain")

        else:  # json or verbose_json
            response = TranscriptionResponse(
                text=full_text,
                language=info.language,
                duration=info.duration
            )

            if response_format == "verbose_json" or word_timestamps:
                # Add detailed segments
                response.segments = [
                    {
                        "id": i,
                        "start": s.start,
                        "end": s.end,
                        "text": s.text.strip(),
                        "avg_logprob": s.avg_logprob
                    }
                    for i, s in enumerate(segments_list)
                ]

                if word_timestamps:
                    all_words = []
                    for seg in segments_list:
                        if seg.words:
                            for w in seg.words:
                                all_words.append(TranscriptionWord(
                                    word=w.word,
                                    start=w.start,
                                    end=w.end,
                                    probability=w.probability
                                ))
                    response.words = all_words

            return response

    finally:
        # Cleanup
        try:
            os.unlink(tmp_path)
        except:
            pass


@app.post("/v1/audio/translations")
async def translate_audio(
    file: UploadFile = File(...),
    model: str = Form("whisper-1"),
    prompt: Optional[str] = Form(None),
    response_format: str = Form("json")
):
    """
    Translate audio to English (OpenAI-compatible endpoint)
    """
    result = await transcribe_audio(
        file=file,
        model=model,
        language="en",
        prompt=prompt,
        response_format=response_format
    )

    if isinstance(result, TranscriptionResponse):
        result.text = f"[Translated to English] {result.text}"

    return result


@app.post("/admin/unload")
async def force_unload():
    """Force unload the model (admin endpoint)"""
    unloaded = model_manager.force_unload()
    return {"unloaded": unloaded, "status": model_manager.status}


def format_srt(segments) -> str:
    """Format segments as SRT subtitles"""
    lines = []
    for i, seg in enumerate(segments, 1):
        start = format_timestamp_srt(seg.start)
        end = format_timestamp_srt(seg.end)
        lines.append(f"{i}")
        lines.append(f"{start} --> {end}")
        lines.append(seg.text.strip())
        lines.append("")

    return "\n".join(lines)


def format_vtt(segments) -> str:
    """Format segments as WebVTT subtitles"""
    lines = ["WEBVTT", ""]
    for i, seg in enumerate(segments, 1):
        start = format_timestamp_vtt(seg.start)
        end = format_timestamp_vtt(seg.end)
        lines.append(f"{start} --> {end}")
        lines.append(seg.text.strip())
        lines.append("")

    return "\n".join(lines)


def format_timestamp_srt(seconds: float) -> str:
    """Format timestamp for SRT (00:00:00,000)"""
    hours = int(seconds // 3600)
    minutes = int((seconds % 3600) // 60)
    secs = int(seconds % 60)
    millis = int((seconds % 1) * 1000)
    return f"{hours:02d}:{minutes:02d}:{secs:02d},{millis:03d}"


def format_timestamp_vtt(seconds: float) -> str:
    """Format timestamp for WebVTT (00:00:00.000)"""
    hours = int(seconds // 3600)
    minutes = int((seconds % 3600) // 60)
    secs = int(seconds % 60)
    millis = int((seconds % 1) * 1000)
    return f"{hours:02d}:{minutes:02d}:{secs:02d}.{millis:03d}"


@app.on_event("startup")
async def startup_event():
    """Start background idle checker and optionally preload model"""
    # Start idle checker task
    asyncio.create_task(idle_checker_task(interval=60))
    logger.info(f"Started idle checker (timeout: {IDLE_TIMEOUT}s)")


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8190)
