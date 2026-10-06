# H.7 P3 Notebook Runner — multi-kernel Docker image
# Supports: Python 3.11 (system, bookworm) + kernel global-3.13, .NET 9.0 Interactive (C#), Lean 4 (elan)
# Usage: docker-compose run notebook-runner /scripts/h7_p3_notebook_runner.sh <notebook.ipynb>

# Stage 1: Base image with .NET 9.0 SDK
FROM mcr.microsoft.com/dotnet/sdk:9.0 AS base

# Install system dependencies
# Python = le python3 SYSTEME du tag 9.0 (Debian bookworm, 3.11) :
# - le Dockerfile d'origine demandait python3.12 via apt, qui n'existe dans
#   AUCUN repo Debian (bookworm = 3.11) -- image inconstructible depuis main
#   (mesure 2026-10-06 : "E: Unable to locate package python3.12") ;
# - le socle 3.11 est coherent avec la liste pip du Stage 2 : open_spiel 2.0.x
#   publie des wheels manylinux cp311 a cp314 (requires-python >=3.11).
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 python3-venv python3-pip \
    wget curl git ca-certificates \
    # .NET Interactive prerequisites
    libicu-dev \
    # Lean 4 (elan) prerequisites
    cmake g++ gcc libc6-dev \
    && rm -rf /var/lib/apt/lists/*

# Stage 2: Python environment
FROM base AS python-env

RUN python3 -m pip install --break-system-packages --no-cache-dir \
    jupyter nbconvert nbformat papermill \
    jupyter_client ipykernel \
    numpy pandas scipy scikit-learn matplotlib \
    # QuantConnect research
    quantconnect-stubs \
    # GenAI notebooks
    requests pillow \
    # Game theory -- open_spiel : nom canon PyPI (le repo installe ce nom,
    # cf GameTheory/scripts/setup_wsl_openspiel.sh ; "openspiel" sans
    # separateur est un projet PyPI homonyme disparu, matrice python
    # incompatible -- mesure 2026-10-06 : 404 sur le simple index)
    nashpy open_spiel \
    # SemanticWeb
    rdflib owlready2 pyshacl \
    && python3 -m ipykernel install --name python3 --user

# Stage 2b: kernel Python 3.13 "global-3.13" (notebooks serie Lean, #16262)
# Lean-08-Agentic-Proving-Python.ipynb et ses siblings portent le kernelspec
# `global-3.13` (cf scripts/notebook_tools/check_kernel_suffix_canon.py,
# PYTHON_ENV_NAMES). Env construite via miniforge (conda-forge), meme canal
# que les env des machines de la flotte, puis enregistree en kernelspec.
FROM python-env AS global-313

RUN wget -q https://github.com/conda-forge/miniforge/releases/latest/download/Miniforge3-Linux-x86_64.sh -O /tmp/miniforge.sh \
    && bash /tmp/miniforge.sh -b -p /opt/miniforge \
    && /opt/miniforge/bin/conda create -y -n global-3.13 python=3.13 ipykernel \
    && /opt/miniforge/envs/global-3.13/bin/python -m ipykernel install --name global-3.13 --user \
    && rm /tmp/miniforge.sh

# Stage 3: .NET Interactive
FROM global-313 AS dotnet-interactive

RUN dotnet tool install --global Microsoft.dotnet-interactive \
    && ~/.dotnet/tools/dotnet-interactive jupyter install

# Stage 4: Lean 4 toolchain (elan)
FROM dotnet-interactive AS lean-env

RUN curl -sL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain stable \
    && echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc

# Set environment
ENV PATH="/root/.dotnet/tools:/root/.elan/bin:${PATH}" \
    PYTHONUNBUFFERED=1 \
    DOTNET_INTERACTIVE_DEFAULT_TOOLCHAIN=net9.0 \
    LANG=C.UTF-8

# Copy runner script
COPY h7_p3_notebook_runner.sh /scripts/h7_p3_notebook_runner.sh
RUN chmod +x /scripts/h7_p3_notebook_runner.sh

# Working directory for notebooks
WORKDIR /notebooks

ENTRYPOINT ["/scripts/h7_p3_notebook_runner.sh"]
