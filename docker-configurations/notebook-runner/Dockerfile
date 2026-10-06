# H.7 P3 Notebook Runner — multi-kernel Docker image
# Supports: Python 3.11 (system, bookworm), .NET 9.0 Interactive (C#), Lean 4 (elan)
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
    # SmartContracts SC-11 (LLM-Assisted) : backend EthereumTester local --
    # web3 pour EthereumTesterProvider, eth-tester[py-evm] pour le backend
    web3 "eth-tester[py-evm]" \
    && python3 -m ipykernel install --name python3 --user

# Stage 3: .NET Interactive
FROM python-env AS dotnet-interactive

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
