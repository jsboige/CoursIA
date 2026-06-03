# MusicGen API - Music generation with Meta's MusicGen
# Using transformers + scipy for simpler setup
FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    ffmpeg \
    libsndfile1 \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies - use transformers for MusicGen
RUN pip install --no-cache-dir \
    fastapi \
    uvicorn \
    python-multipart \
    torch \
    scipy \
    transformers \
    accelerate \
    soundfile \
    numpy

# Copy application
COPY app.py /app/
COPY start.sh /app/
RUN chmod +x /app/start.sh

# Create directories
RUN mkdir -p /app/models /app/outputs

# Create non-root user for security
RUN groupadd -g 1000 appuser && \
    useradd -u 1000 -g appuser -m -s /bin/bash appuser && \
    chown -R appuser:appuser /app

USER appuser

# Expose port
EXPOSE 8192

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=180s --retries=3 \
    CMD curl -f http://localhost:8192/health || exit 1

# Start
CMD ["/app/start.sh"]
