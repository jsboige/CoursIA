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

# Install PyTorch with CUDA support
RUN pip install --no-cache-dir \
    torch==2.5.0 \
    torchaudio==2.5.0 \
    --index-url https://download.pytorch.org/whl/cu121

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

# Expose port
EXPOSE 8000

# Run application
CMD ["python", "app.py"]
