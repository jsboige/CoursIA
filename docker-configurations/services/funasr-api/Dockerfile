# FunASR API - FastAPI wrapper for FunASR (Fun-ASR-Nano-2512)
# Multilingual ASR with VAD, OpenAI-compatible API
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

# Install Fun-ASR from GitHub (PyPI funasr lacks FunASRNano registration)
# Keep repo at /opt/fun-asr — model.py, ctc.py, tools/ are required at runtime
RUN git clone https://github.com/FunAudioLLM/Fun-ASR.git /opt/fun-asr && \
    pip install --no-cache-dir -r /opt/fun-asr/requirements.txt && \
    mkdir -p /app/fun-asr-code && \
    cp /opt/fun-asr/model.py /app/fun-asr-code/ && \
    cp /opt/fun-asr/ctc.py /app/fun-asr-code/ && \
    cp -r /opt/fun-asr/tools /app/fun-asr-code/tools && \
    rm -rf /opt/fun-asr/.git

# Install API dependencies
RUN pip install --no-cache-dir \
    torch \
    torchaudio \
    fastapi \
    uvicorn \
    python-multipart \
    numpy \
    soundfile \
    librosa \
    transformers \
    sentencepiece

# Set PYTHONPATH so funasr can import ctc and tools.utils from fun-asr-code
ENV PYTHONPATH="/app/fun-asr-code:${PYTHONPATH}"

# Copy application
COPY app.py /app/
COPY start.sh /app/
COPY patch-funasr.sh /app/
RUN chmod +x /app/start.sh /app/patch-funasr.sh

# Apply runtime patches for FunASR Nano compatibility
RUN /app/patch-funasr.sh

# Create directories
RUN mkdir -p /app/models /app/uploads

# Expose port
EXPOSE 8194

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=120s --retries=3 \
    CMD curl -f http://localhost:8194/health || exit 1

# Start
CMD ["/app/start.sh"]
