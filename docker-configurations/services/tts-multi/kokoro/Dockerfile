FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install PyTorch with CUDA support (use 2.4+ for transformers 5.x compatibility)
RUN pip install --no-cache-dir \
    torch==2.4.0 \
    torchaudio==2.4.0 \
    --index-url https://download.pytorch.org/whl/cu121

# Install Kokoro and dependencies
RUN pip install --no-cache-dir \
    'numpy<2' \
    kokoro \
    fastapi==0.104.1 \
    uvicorn[standard]==0.24.0 \
    pydantic==2.5.0

# Copy application
COPY app.py .

# Expose port
EXPOSE 8000

# Run application
CMD ["python", "app.py"]
