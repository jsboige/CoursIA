#!/bin/bash
# Phase 11: Installation des requirements ComfyUI
# Date: 2025-10-13
# Objectif: Installer les dépendances ComfyUI et vérifier GPU

set -e  # Arrêter en cas d'erreur

COMFYUI_DIR="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"

echo "=== Phase 11: Installation requirements ComfyUI ==="
echo "Répertoire: $COMFYUI_DIR"
echo ""

# Vérifier que le répertoire existe
if [ ! -d "$COMFYUI_DIR" ]; then
    echo "❌ Erreur: Répertoire ComfyUI non trouvé: $COMFYUI_DIR"
    exit 1
fi

cd "$COMFYUI_DIR"

# Activer l'environnement virtuel
echo "▶ Activation environnement virtuel..."
source venv/bin/activate

# Installer les requirements
echo ""
echo "▶ Installation requirements.txt..."
pip install -r requirements.txt

# Vérifier PyTorch et CUDA
echo ""
echo "▶ Vérification PyTorch et CUDA..."
python -c "
import torch
print(f'PyTorch version: {torch.__version__}')
print(f'CUDA available: {torch.cuda.is_available()}')
print(f'CUDA version: {torch.version.cuda}')
print(f'GPU count: {torch.cuda.device_count()}')
print('')
print('GPUs détectés:')
for i in range(torch.cuda.device_count()):
    print(f'  GPU {i}: {torch.cuda.get_device_name(i)}')
    mem_total = torch.cuda.get_device_properties(i).total_memory / 1024**3
    print(f'    VRAM: {mem_total:.2f} GB')
"

echo ""
echo "=== ✅ Requirements installés avec succès ==="