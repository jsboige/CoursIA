#!/bin/bash
# Setup script for Python 3 (WSL) kernel
# Installs all required dependencies for Lean notebooks 7-8

set -e

echo "=== Configuration Python 3 (WSL) pour notebooks Lean ==="

# 1. Verifier que le venv existe
VENV_PATH="$HOME/.python3-wsl-venv"
if [ ! -d "$VENV_PATH" ]; then
    echo "Creation du venv: $VENV_PATH"
    python3 -m venv "$VENV_PATH"
fi

# 2. Activer le venv
source "$VENV_PATH/bin/activate"

# 3. Installer les dependances
echo "Installation des dependances Python..."
pip install --quiet --upgrade pip
pip install --quiet python-dotenv openai anthropic

# 4. Verifier les installations
echo ""
echo "=== Verification ==="
python3 -c "import dotenv; print(f'✓ python-dotenv {dotenv.__version__}')"
python3 -c "import openai; print(f'✓ openai {openai.__version__}')"
python3 -c "import anthropic; print(f'✓ anthropic {anthropic.__version__}')"

echo ""
echo "=== Configuration terminee ==="
echo "Le kernel Python 3 (WSL) est pret pour les notebooks Lean 7-8"
