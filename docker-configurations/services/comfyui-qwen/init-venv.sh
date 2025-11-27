#!/bin/bash
# Script d'initialisation du venv pour ComfyUI dans Docker
# Ce script garantit que le venv est activé avant de démarrer ComfyUI

set -e

echo "=== ComfyUI Venv Initialization ==="
echo "Working directory: $(pwd)"

# Vérifier que le venv existe
if [ ! -d "venv" ]; then
    echo "ERROR: venv not found at $(pwd)/venv"
    echo "Please create venv first using:"
    echo "  wsl -d Ubuntu -e bash -c 'cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI && python3 -m venv venv && source venv/bin/activate && pip install -r requirements.txt'"
    exit 1
fi

# Activer le venv
echo "Activating venv..."
source venv/bin/activate

# Vérifier l'activation
if [ -z "$VIRTUAL_ENV" ]; then
    echo "ERROR: venv activation failed"
    exit 1
fi

echo "✓ Venv activated: $VIRTUAL_ENV"
echo "✓ Python: $(which python)"
echo "✓ Python version: $(python --version)"

# Vérifier que les dépendances sont installées
echo "Checking dependencies..."
python -c "import yaml; import torch; import PIL" || {
    echo "ERROR: Required dependencies not found in venv"
    echo "Please reinstall dependencies:"
    echo "  source venv/bin/activate && pip install -r requirements.txt"
    exit 1
}

echo "✓ Dependencies OK"
echo ""
echo "Starting ComfyUI..."
exec python main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention