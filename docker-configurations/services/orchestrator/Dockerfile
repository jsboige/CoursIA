# =============================================================================
# CoursIA GenAI Orchestrator - Dockerfile
# =============================================================================
# Image Docker pour le service d'orchestration des services GenAI
# =============================================================================

FROM python:3.11-slim

# Métadonnées
LABEL maintainer="CoursIA Team"
LABEL version="1.0.0"
LABEL description="CoursIA GenAI Orchestrator - Service d'orchestration pour les services GenAI"
LABEL com.myia.service="genai-orchestrator"
LABEL com.myia.phase="production"

# Variables d'environnement
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    TZ=Europe/Paris \
    DEBIAN_FRONTEND=noninteractive

# Répertoire de travail
WORKDIR /app

# Installation des dépendances système
RUN apt-get update && apt-get install -y \
    curl \
    jq \
    docker.io \
    && rm -rf /var/lib/apt/lists/*

# Installation des dépendances Python
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copie des fichiers de l'application
COPY orchestrator.py .
COPY config/ ./config/
COPY scripts/ ./scripts/

# Création des répertoires nécessaires
RUN mkdir -p /app/logs /app/secrets

# Permissions
RUN chmod +x orchestrator.py scripts/*.py

# Utilisateur non-root (sécurité)
RUN useradd -m -u 1000 orchestrator && \
    chown -R orchestrator:orchestrator /app
USER orchestrator

# Port d'écoute
EXPOSE 8090

# Commande de démarrage
CMD ["python3", "orchestrator.py"]

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=60s --retries=5 \
    CMD curl -f http://localhost:8090/health || exit 1