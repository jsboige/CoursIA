#!/usr/bin/env bash
# Setup script for Infer.NET Notebooks — Linux/macOS twin of setup_environment.ps1
# This script installs all required dependencies for running the Infer.NET notebook series
#
# Usage: bash scripts/setup_environment.sh [--skip-dotnet-interactive] [--skip-papermill]

set -euo pipefail

SKIP_DOTNET_INTERACTIVE=0
SKIP_PAPERMILL=0
for arg in "$@"; do
    case "$arg" in
        --skip-dotnet-interactive) SKIP_DOTNET_INTERACTIVE=1 ;;
        --skip-papermill) SKIP_PAPERMILL=1 ;;
        *) echo "Unknown option: $arg" >&2; exit 1 ;;
    esac
done

timestamp() { date '+%H:%M:%S'; }
status()    { echo "[$(timestamp)] $1"; }

status "=== Infer.NET Notebooks Environment Setup ==="

# Check .NET SDK
status "Checking .NET SDK..."
if command -v dotnet >/dev/null 2>&1; then
    DOTNET_VERSION="$(dotnet --version)"
    status "  .NET SDK found: $DOTNET_VERSION"
else
    status "  .NET SDK not found. Please install from https://dotnet.microsoft.com/download" >&2
    exit 1
fi

# Check/Install dotnet-interactive
if [ "$SKIP_DOTNET_INTERACTIVE" -eq 0 ]; then
    status "Checking dotnet-interactive..."
    if dotnet tool list -g 2>/dev/null | grep -q "microsoft.dotnet-interactive"; then
        status "  dotnet-interactive already installed"
    else
        status "  Installing dotnet-interactive..."
        if dotnet tool install -g Microsoft.dotnet-interactive; then
            status "  dotnet-interactive installed successfully"
        else
            status "  Failed to install dotnet-interactive" >&2
            exit 1
        fi
    fi

    # Register Jupyter kernels
    status "Registering .NET Interactive Jupyter kernels..."
    if dotnet interactive jupyter install; then
        status "  Kernels registered successfully"
    else
        status "  Warning: Could not register kernels (may already exist)"
    fi
fi

# Check Python and pip
status "Checking Python..."
if command -v python >/dev/null 2>&1; then
    PYTHON_VERSION="$(python --version)"
    status "  Python found: $PYTHON_VERSION"
else
    status "  Python not found. Please install Python 3.8+" >&2
    exit 1
fi

# Check/Install papermill
if [ "$SKIP_PAPERMILL" -eq 0 ]; then
    status "Checking papermill..."
    if python -c "import papermill" 2>/dev/null; then
        status "  papermill already installed"
    else
        status "  Installing papermill..."
        if pip install papermill jupyter; then
            status "  papermill installed successfully"
        else
            status "  Failed to install papermill" >&2
            exit 1
        fi
    fi
fi

# List available Jupyter kernels
status "Available Jupyter kernels:"
jupyter kernelspec list

status ""
status "=== Setup Complete ==="
status "You can now run the Infer.NET notebooks in:"
status "  MyIA.AI.Notebooks/Probas/Infer/"
status ""
status "To test notebooks with papermill:"
status "  python scripts/infer-notebooks/test_notebooks.py"
