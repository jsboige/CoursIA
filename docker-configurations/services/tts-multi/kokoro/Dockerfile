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

# KPipeline de kokoro charge spaCy (en_core_web_sm) pour normaliser le texte
# avant synthese. Absent de l'image, il tente un pip install a l'arrivee, sous
# appuser (non-root) : le paquet atterrit dans le site de l'utilisateur, un
# chemin que le process serveur (demarre avant l'install) n'a JAMAIS dans son
# sys.path -> 500 « [E050] Can't find model 'en_core_web_sm' » a chaque synthese.
# Cuire le mode dans le site-packages au build (lisible par le user, deja dans
# sys.path) supprime le pip runtime.
# en_core_web_sm n'est PAS sur PyPI (aucune version publiee) : les modes spaCy
# sont des wheels sur les releases GitHub d'explosion/spacy-models — d'ou
# l'URL directe. Mesure 2026-11-12 (po-2024) : pip install en-core-web-sm rend
# « No matching distribution found ».
RUN pip install --no-cache-dir \
    https://github.com/explosion/spacy-models/releases/download/en_core_web_sm-3.8.0/en_core_web_sm-3.8.0-py3-none-any.whl

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
