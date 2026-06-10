# Fast Downward - Classical AI Planning System
# https://github.com/aibasel/downward
#
# Build: docker compose build
# Run:   docker compose up -d
# Test:  curl http://localhost:8200/health
#
# CPU-only service (no GPU required for classical planning)
# Source: cloned from aibasel/downward release-24.06.1

FROM python:3.11-slim AS builder

RUN apt-get update && apt-get install -y --no-install-recommends \
    cmake \
    make \
    g++ \
    gcc \
    gawk \
    && rm -rf /var/lib/apt/lists/*

# Clone source at build time (reproducible, no local src/ needed)
RUN apt-get update && apt-get install -y --no-install-recommends git \
    && git clone --depth 1 --branch release-24.06.1 https://github.com/aibasel/downward.git /opt/fast-downward-src \
    && apt-get remove -y git && apt-get autoremove -y \
    && rm -rf /var/lib/apt/lists/*
RUN cd /opt/fast-downward-src \
    && python3 build.py

FROM python:3.11-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    gawk \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Copy built artifacts from builder
COPY --from=builder /opt/fast-downward-src /opt/fast-downward

# Install unified-planning with Fast Downward support
RUN pip install --no-cache-dir \
    unified-planning \
    up-fast-downward

# HTTP API for planner invocation
COPY api/ /opt/api/

WORKDIR /opt/fast-downward

EXPOSE 8200

CMD ["python3", "/opt/api/server.py"]
