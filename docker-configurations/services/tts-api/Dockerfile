# TTS API - Text-to-Speech with Kokoro and OpenVoice
# OpenAI-compatible TTS API
FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    ffmpeg \
    espeak-ng \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
RUN pip install --no-cache-dir \
    fastapi \
    uvicorn \
    python-multipart \
    torch \
    torchaudio \
    kokoro \
    soundfile \
    numpy \
    scipy

# Copy application
COPY app.py /app/
COPY start.sh /app/
RUN chmod +x /app/start.sh

# Create directories
RUN mkdir -p /app/models /app/outputs

# Expose port
EXPOSE 8191

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=120s --retries=3 \
    CMD curl -f http://localhost:8191/health || exit 1

# Start
CMD ["/app/start.sh"]
