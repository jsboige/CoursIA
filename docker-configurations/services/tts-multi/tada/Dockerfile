FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    git \
    curl \
    ffmpeg \
    libsndfile1 \
    && rm -rf /var/lib/apt/lists/*

# Install PyTorch with CUDA support.
# hume-tada pins torch 2.7.x : installer torch+torchaudio PAIRES depuis le
# wheels cu126 AVANT hume-tada, sinon pip resolve torchaudio 2.11 (cu13) et
# l'import crash sur libcudart.so.13 (mesure 2026-08-26, #13110).
RUN pip install --no-cache-dir \
    torch==2.7.1 \
    torchaudio==2.7.1 \
    --index-url https://download.pytorch.org/whl/cu126

# Install TADA package from GitHub (required for HumeAI/tada-3b-ml)
RUN pip install --no-cache-dir git+https://github.com/HumeAI/tada.git

# Install FastAPI and other dependencies
RUN pip install --no-cache-dir \
    'numpy<2' \
    accelerate>=0.26.0 \
    sentencepiece>=0.2.0 \
    fastapi>=0.109.0 \
    uvicorn[standard]>=0.27.0 \
    pydantic>=2.5.0 \
    soundfile

# Copy application
COPY app.py .

# Create non-root user for security
RUN groupadd -g 1000 appuser && \
    useradd -u 1000 -g appuser -m -s /bin/bash appuser && \
    chown -R appuser:appuser /app

USER appuser

# Expose port
EXPOSE 8000

# Run application
CMD ["python", "app.py"]
