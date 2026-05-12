# H.7 P3 Notebook Runner — multi-kernel Docker image
# Supports: Python 3.12, .NET 9.0 Interactive (C#), Lean 4 (elan)
# Usage: docker-compose run notebook-runner /scripts/h7_p3_notebook_runner.sh <notebook.ipynb>

# Stage 1: Base image with .NET 9.0 SDK
FROM mcr.microsoft.com/dotnet/sdk:9.0 AS base

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3.12 python3.12-venv python3-pip \
    wget curl git ca-certificates \
    # .NET Interactive prerequisites
    libicu-dev \
    # Lean 4 (elan) prerequisites
    cmake g++ gcc libc6-dev \
    && rm -rf /var/lib/apt/lists/*

# Stage 2: Python environment
FROM base AS python-env

RUN python3.12 -m pip install --break-system-packages --no-cache-dir \
    jupyter nbconvert nbformat papermill \
    jupyter_client ipykernel \
    numpy pandas scipy scikit-learn matplotlib \
    # QuantConnect research
    quantconnect-stubs \
    # GenAI notebooks
    requests pillow \
    # Game theory
    nashpy openspiel \
    # SemanticWeb
    rdflib owlready2 pyshacl \
    && python3.12 -m ipykernel install --name python3 --user

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
