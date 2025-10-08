# =============================================================================
# CoursIA GenAI - Orchestrator Docker Image
# =============================================================================
# Image Docker pour l'orchestrateur de services GenAI
# Responsabilités:
#   - Gestion du lifecycle des containers GenAI
#   - Health monitoring des services
#   - Load balancing entre modèles
#   - Métriques et monitoring
# =============================================================================

FROM python:3.11-slim

LABEL maintainer="CoursIA Team"
LABEL description="GenAI Services Orchestrator"
LABEL version="1.0.0"

# ===== ENVIRONMENT SETUP =====
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PIP_NO_CACHE_DIR=1 \
    PIP_DISABLE_PIP_VERSION_CHECK=1

WORKDIR /app

# ===== SYSTEM DEPENDENCIES =====
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# ===== PYTHON DEPENDENCIES =====
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# ===== APPLICATION FILES =====
COPY orchestrator.py .
COPY config/ ./config/

# ===== HEALTH CHECK =====
HEALTHCHECK --interval=30s --timeout=10s --start-period=30s --retries=3 \
    CMD curl -f http://localhost:8193/health || exit 1

# ===== EXPOSE PORT =====
EXPOSE 8193

# ===== USER SETUP (SECURITY) =====
RUN useradd -m -u 1000 orchestrator && \
    chown -R orchestrator:orchestrator /app

USER orchestrator

# ===== ENTRYPOINT =====
CMD ["python", "orchestrator.py"]