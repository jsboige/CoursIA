#!/bin/bash
# Phase 11: Vérification Setup ComfyUI avant lancement
# Date: 2025-10-13

set -e

COMFYUI_DIR="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"

echo "=== Vérification Setup ComfyUI + Qwen ==="
echo ""

cd "$COMFYUI_DIR"
source venv/bin/activate

# 1. Vérifier Python et PyTorch
echo "▶ Python & PyTorch:"
python -c "import torch; print(f'  PyTorch: {torch.__version__}'); print(f'  CUDA: {torch.cuda.is_available()}'); print(f'  GPUs: {torch.cuda.device_count()}')"

# 2. Vérifier custom node
echo ""
echo "▶ Custom Node:"
if [ -d "custom_nodes/ComfyUI-QwenImageWanBridge" ]; then
    echo "  ✅ ComfyUI-QwenImageWanBridge installé"
    echo "  Fichiers:"
    ls -1 custom_nodes/ComfyUI-QwenImageWanBridge/*.py | head -5
else
    echo "  ❌ Custom node manquant"
    exit 1
fi

# 3. Vérifier modèle
echo ""
echo "▶ Modèle Qwen-Image-Edit-2509:"
if [ -d "models/checkpoints/Qwen-Image-Edit-2509-FP8" ]; then
    SIZE=$(du -sh models/checkpoints/Qwen-Image-Edit-2509-FP8 | cut -f1)
    echo "  ✅ Modèle présent: $SIZE"
    echo "  Composants:"
    ls -1 models/checkpoints/Qwen-Image-Edit-2509-FP8/
else
    echo "  ❌ Modèle manquant"
    exit 1
fi

# 4. Vérifier GPU
echo ""
echo "▶ GPU Status:"
nvidia-smi --query-gpu=index,name,memory.total,memory.free --format=csv,noheader

# 5. Vérifier port 8188
echo ""
echo "▶ Port 8188:"
if lsof -i :8188 > /dev/null 2>&1; then
    echo "  ⚠️  Port 8188 déjà utilisé:"
    lsof -i :8188
else
    echo "  ✅ Port 8188 disponible"
fi

echo ""
echo "=== ✅ Setup vérifié - Prêt pour lancement ==="
echo ""
echo "Pour lancer ComfyUI:"
echo "  cd $COMFYUI_DIR"
echo "  source venv/bin/activate"
echo "  CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188"