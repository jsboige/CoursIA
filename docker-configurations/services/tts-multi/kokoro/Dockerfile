FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install PyTorch with CUDA support.
# transformers 5.x exige torch >= 2.6 pour son implementation CustomAlbert
# (chemin utilise par KModel de kokoro) : avec torch 2.4, transformers se
# desactive ("PyTorch was not found") et toute synthese renvoie 500
# « CustomAlbert requires PyTorch >= 2.6 ». Mesure 2026-11-12 (po-2024).
RUN pip install --no-cache-dir \
    torch==2.6.0 \
    torchaudio==2.6.0 \
    --index-url https://download.pytorch.org/whl/cu124

# Install Kokoro and dependencies
RUN pip install --no-cache-dir \
    'numpy<2' \
    kokoro \
    fastapi==0.104.1 \
    uvicorn[standard]==0.24.0 \
    pydantic==2.5.0

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
