#!/bin/bash
# Phase 11: Lancement ComfyUI Standalone avec RTX 3090
# Date: 2025-10-13

set -e

echo "================================================================"
echo "LANCEMENT COMFYUI STANDALONE - RTX 3090 (GPU 0)"
echo "================================================================"
echo ""

# Naviguer vers ComfyUI
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
source venv/bin/activate

echo "=== Configuration GPU ==="
echo "CUDA_VISIBLE_DEVICES=0 (RTX 3090 - 25.8GB)"
echo ""

echo "=== Vérification GPU PyTorch ==="
CUDA_VISIBLE_DEVICES=0 python3 -c "
import torch
print(f'GPU disponible: {torch.cuda.get_device_name(0)}')
print(f'VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB')
"
echo ""

echo "=== Vérification Modèle Qwen ==="
MODEL_PATH="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8"
if [ -d "$MODEL_PATH" ]; then
    echo "✓ Modèle Qwen trouvé: $MODEL_PATH"
    echo "Fichiers:"
    ls -lh "$MODEL_PATH" | head -10
else
    echo "✗ ERREUR: Modèle Qwen non trouvé!"
    exit 1
fi
echo ""

echo "=== Vérification Custom Node Qwen ==="
CUSTOM_NODE_PATH="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge"
if [ -d "$CUSTOM_NODE_PATH" ]; then
    echo "✓ Custom node trouvé: $CUSTOM_NODE_PATH"
else
    echo "✗ ERREUR: Custom node non trouvé!"
    exit 1
fi
echo ""

echo "=== Lancement ComfyUI sur port 8188 ==="
echo "URL: http://localhost:8188"
echo "GPU: RTX 3090 (CUDA_VISIBLE_DEVICES=0)"
echo ""
echo "CTRL+C pour arrêter"
echo "================================================================"
echo ""

# Lancer ComfyUI avec GPU 3090
CUDA_VISIBLE_DEVICES=0 python3 main.py \
    --listen 0.0.0.0 \
    --port 8188 \
    --preview-method auto \
    --use-split-cross-attention \
    --verbose