# Whisper API - FastAPI wrapper for faster-whisper
FROM nvidia/cuda:12.1.0-runtime-ubuntu22.04

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    ffmpeg \
    curl \
    python3.11 \
    python3.11-venv \
    python3-pip \
    && rm -rf /var/lib/apt/lists/* \
    && ln -sf /usr/bin/python3.11 /usr/bin/python \
    && ln -sf /usr/bin/python3.11 /usr/bin/python3

# Install Python dependencies
RUN pip install --no-cache-dir \
    fastapi \
    uvicorn \
    python-multipart \
    faster-whisper \
    numpy \
    soundfile

# Copy application
COPY app.py /app/
COPY start.sh /app/
RUN chmod +x /app/start.sh

# Create directories
RUN mkdir -p /app/models /app/uploads /app/outputs

# Expose port
EXPOSE 8190

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=60s --retries=3 \
    CMD curl -f http://localhost:8190/health || exit 1

# Start
CMD ["/app/start.sh"]
