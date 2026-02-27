# Demucs API - Source separation with Demucs v4
# HTTP API for music source separation (stems extraction)
FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    ffmpeg \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
RUN pip install --no-cache-dir \
    fastapi \
    uvicorn \
    python-multipart \
    torch \
    torchaudio \
    demucs \
    soundfile \
    numpy \
    scipy

# Copy application
COPY app.py /app/
COPY start.sh /app/
RUN chmod +x /app/start.sh

# Create directories
RUN mkdir -p /app/models /app/outputs /app/uploads

# Expose port
EXPOSE 8193

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=120s --retries=3 \
    CMD curl -f http://localhost:8193/health || exit 1

# Start
CMD ["/app/start.sh"]
