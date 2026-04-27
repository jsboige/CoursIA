# Qwen ASR API - FastAPI wrapper for Qwen3-ASR-1.7B
# Multilingual ASR with auto language detection, OpenAI-compatible API
FROM nvidia/cuda:12.1.0-runtime-ubuntu22.04

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    ffmpeg \
    curl \
    git \
    python3.11 \
    python3.11-venv \
    python3-pip \
    && rm -rf /var/lib/apt/lists/* \
    && ln -sf /usr/bin/python3.11 /usr/bin/python \
    && ln -sf /usr/bin/python3.11 /usr/bin/python3

# Install PyTorch with CUDA 12.1 support first (large, cached layer)
RUN pip install --no-cache-dir \
    torch \
    torchaudio \
    --index-url https://download.pytorch.org/whl/cu121

# Install numpy first (required by sox dependency of qwen-asr)
RUN pip install --no-cache-dir numpy

# Install qwen-asr package and API dependencies
RUN pip install --no-cache-dir \
    qwen-asr \
    fastapi \
    uvicorn \
    python-multipart \
    soundfile \
    librosa \
    transformers \
    sentencepiece

# Copy application files
COPY app.py /app/
COPY start.sh /app/
RUN chmod +x /app/start.sh
# Shared modules (lazy_model, auth_middleware) are mounted at runtime via volume

# Create directories
RUN mkdir -p /app/models /app/uploads

# Expose port
EXPOSE 8195

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=120s --retries=3 \
    CMD curl -f http://localhost:8195/health || exit 1

# Start
CMD ["/app/start.sh"]
