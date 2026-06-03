#!/usr/bin/env python3
"""
Qwen ASR API - FastAPI wrapper for Qwen3-ASR-1.7B
OpenAI-compatible API for multilingual speech-to-text

Features:
- Lazy loading with auto-unload after inactivity (shared LazyModelManager)
- GPU memory management
- OpenAI-compatible /v1/audio/transcriptions endpoint
- Auto language detection (52 languages)
- Optional word-level timestamps via Qwen3-ForcedAligner-0.6B
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
logger = logging.getLogger("qwen-asr-api")

# Set HuggingFace token for gated model downloads
HF_TOKEN = os.getenv("HF_TOKEN", "")
if HF_TOKEN:
    os.environ["HUGGING_FACE_HUB_TOKEN"] = HF_TOKEN
    os.environ["HF_TOKEN"] = HF_TOKEN
    logger.info("HuggingFace token configured")

# Configuration from environment
QWEN_MODEL = os.getenv("QWEN_ASR_MODEL", "Qwen/Qwen3-ASR-1.7B")
FORCED_ALIGNER = os.getenv("FORCED_ALIGNER", "")  # empty = disabled
DEVICE = os.getenv("QWEN_ASR_DEVICE", "cuda")
MAX_FILE_SIZE = int(os.getenv("MAX_FILE_SIZE", 50 * 1024 * 1024))  # 50MB
IDLE_TIMEOUT = int(os.getenv("IDLE_TIMEOUT", "300"))  # 5 minutes
PRELOAD_MODEL = os.getenv("PRELOAD_MODEL", "false").lower() == "true"
DTYPE = os.getenv("QWEN_ASR_DTYPE", "bfloat16")

app = FastAPI(
    title="Qwen ASR API",
    description="OpenAI-compatible ASR API using Qwen3-ASR-1.7B with auto-unload",
    version="1.1.0"
)

# ISO 639-1 / common codes → qwen-asr full language names
LANG_MAP = {
    "zh": "Chinese", "cn": "Chinese", "chinese": "Chinese",
    "en": "English", "english": "English",
    "yue": "Cantonese", "cantonese": "Cantonese",
    "ar": "Arabic", "arabic": "Arabic",
    "de": "German", "german": "German",
    "fr": "French", "french": "French",
    "es": "Spanish", "spanish": "Spanish",
    "pt": "Portuguese", "portuguese": "Portuguese",
    "id": "Indonesian", "indonesian": "Indonesian",
    "it": "Italian", "italian": "Italian",
    "ko": "Korean", "korean": "Korean",
    "ru": "Russian", "russian": "Russian",
    "th": "Thai", "thai": "Thai",
    "vi": "Vietnamese", "vietnamese": "Vietnamese",
    "ja": "Japanese", "japanese": "Japanese",
    "tr": "Turkish", "turkish": "Turkish",
    "hi": "Hindi", "hindi": "Hindi",
    "ms": "Malay", "malay": "Malay",
    "nl": "Dutch", "dutch": "Dutch",
    "sv": "Swedish", "swedish": "Swedish",
    "da": "Danish", "danish": "Danish",
    "fi": "Finnish", "finnish": "Finnish",
    "pl": "Polish", "polish": "Polish",
    "cs": "Czech", "czech": "Czech",
    "fil": "Filipino", "tl": "Filipino", "filipino": "Filipino",
    "fa": "Persian", "persian": "Persian",
    "el": "Greek", "greek": "Greek",
    "ro": "Romanian", "romanian": "Romanian",
    "hu": "Hungarian", "hungarian": "Hungarian",
    "mk": "Macedonian", "macedonian": "Macedonian",
}


def _normalize_language(lang: str) -> str:
    """Convert ISO 639-1 code or case variant to qwen-asr full name."""
    if not lang:
        return lang
    key = lang.strip().lower()
    return LANG_MAP.get(key, lang)

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


def _get_torch_dtype():
    import torch
    return {"float16": torch.float16, "bfloat16": torch.bfloat16, "float32": torch.float32}.get(
        DTYPE, torch.bfloat16
    )


def _load_qwen_model():
    """Load the Qwen3-ASR model with CUDA fallback to CPU."""
    from qwen_asr import Qwen3ASRModel
    import torch

    device = DEVICE
    dtype = _get_torch_dtype()

    if device == "cuda":
        try:
            if not torch.cuda.is_available():
                logger.warning("CUDA not available, falling back to CPU")
                device = "cpu"
        except Exception as e:
            logger.warning(f"CUDA check failed: {e}, falling back to CPU")
            device = "cpu"

    device_map = f"{device}:0" if device == "cuda" else device

    logger.info(f"Loading Qwen3-ASR model: {QWEN_MODEL} on {device_map} ({DTYPE})")

    kwargs = dict(
        dtype=dtype,
        device_map=device_map,
        max_inference_batch_size=32,
        max_new_tokens=256,
    )

    # Optional forced aligner for word-level timestamps
    if FORCED_ALIGNER:
        logger.info(f"Loading forced aligner: {FORCED_ALIGNER}")
        kwargs["forced_aligner"] = FORCED_ALIGNER
        kwargs["forced_aligner_kwargs"] = dict(dtype=dtype, device_map=device_map)

    try:
        model = Qwen3ASRModel.from_pretrained(QWEN_MODEL, **kwargs)
        return model
    except RuntimeError as e:
        if "cuda" in str(e).lower() or "cublas" in str(e).lower():
            logger.warning(f"CUDA error: {e}, falling back to CPU")
            kwargs["device_map"] = "cpu"
            if FORCED_ALIGNER:
                kwargs["forced_aligner_kwargs"] = dict(dtype=dtype, device_map="cpu")
            return Qwen3ASRModel.from_pretrained(QWEN_MODEL, **kwargs)
        raise


def _unload_qwen_model(model):
    """Unload Qwen model and free GPU memory."""
    del model
    try:
        import torch
        if torch.cuda.is_available():
            torch.cuda.empty_cache()
    except Exception:
        pass


# Model manager with lazy loading and auto-unload
model_manager = LazyModelManager(
    model_name="qwen-asr",
    load_fn=_load_qwen_model,
    unload_fn=_unload_qwen_model,
    idle_timeout=IDLE_TIMEOUT,
    device=DEVICE,
    preload=PRELOAD_MODEL
)


# Response models (OpenAI-compatible)
class TranscriptionWord(BaseModel):
    word: str
    start: float
    end: float


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
    """Convert audio to 16kHz mono WAV using ffmpeg."""
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
        "model": QWEN_MODEL,
        "forced_aligner": FORCED_ALIGNER or None,
        "device": DEVICE,
        "dtype": DTYPE,
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
                "id": "qwen-asr-1",
                "object": "model",
                "created": 1742400000,
                "owned_by": "qwen"
            }
        ]
    }


@app.post("/v1/audio/transcriptions", response_model=TranscriptionResponse)
async def transcribe_audio(
    file: UploadFile = File(...),
    model: str = Form("qwen-asr-1"),
    language: Optional[str] = Form(None),
    prompt: Optional[str] = Form(None),
    response_format: str = Form("json"),
    temperature: float = Form(0.0),
    timestamp_granularities: List[str] = Form(["segment"])
):
    """
    Transcribe audio file (OpenAI-compatible endpoint).

    - **file**: Audio file (mp3, mp4, mpeg, mpga, m4a, wav, webm, ogg, flac)
    - **model**: Model to use (qwen-asr-1)
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
        # Convert to WAV for consistent processing
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
        qwen_model = model_manager.get_model()

        # Run transcription
        transcribe_kwargs = {}
        if language:
            normalized = _normalize_language(language)
            if normalized != language:
                logger.info(f"Language normalized: {language} → {normalized}")
            transcribe_kwargs["language"] = normalized

        # Request timestamps if forced aligner is loaded or verbose output requested
        return_timestamps = (
            response_format == "verbose_json"
            or "word" in timestamp_granularities
            or "segment" in timestamp_granularities
        )
        if return_timestamps and FORCED_ALIGNER:
            transcribe_kwargs["return_time_stamps"] = True

        res = qwen_model.transcribe(audio=audio_path, **transcribe_kwargs)

        # Parse results
        full_text = ""
        detected_language = None
        segments_data = []
        words_data = []

        if res and len(res) > 0:
            result = res[0]
            full_text = result.text.strip() if hasattr(result, "text") else str(result).strip()
            if hasattr(result, "language"):
                detected_language = result.language

            # Extract word-level timestamps if available
            if hasattr(result, "tokens") and "word" in timestamp_granularities:
                for i, token in enumerate(result.tokens):
                    if hasattr(token, "start") and hasattr(token, "end"):
                        words_data.append({
                            "word": token.text if hasattr(token, "text") else str(token),
                            "start": token.start / 1000.0,
                            "end": token.end / 1000.0,
                        })

        elapsed = time.time() - start_time
        logger.info(f"Transcribed {audio_duration:.1f}s audio in {elapsed:.2f}s (lang={detected_language})")

        # Format response
        if response_format == "text":
            return JSONResponse(content=full_text, media_type="text/plain")

        response = TranscriptionResponse(
            text=full_text,
            language=detected_language,
            duration=audio_duration
        )

        if response_format == "verbose_json":
            if words_data:
                response.words = [TranscriptionWord(**w) for w in words_data]

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
    uvicorn.run(app, host="0.0.0.0", port=8195)
