#!/bin/bash
# Phase 11: Test ComfyUI Standalone avec Qwen Image-Edit
# Date: 2025-10-13
# Objectif: Lancer ComfyUI en mode standalone pour validation

set -e  # Arrêter en cas d'erreur

COMFYUI_DIR="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"

echo "=== Phase 11: Test ComfyUI Standalone ==="
echo "Répertoire: $COMFYUI_DIR"
echo ""

# Vérifier que le répertoire existe
if [ ! -d "$COMFYUI_DIR" ]; then
    echo "❌ Erreur: Répertoire ComfyUI non trouvé"
    exit 1
fi

cd "$COMFYUI_DIR"

# Activer environnement virtuel
echo "▶ Activation environnement virtuel..."
source venv/bin/activate

# Vérifier custom node installé
echo ""
echo "▶ Vérification custom node Qwen..."
if [ -d "custom_nodes/ComfyUI-QwenImageWanBridge" ]; then
    echo "✅ Custom node présent"
else
    echo "❌ Custom node non trouvé"
    exit 1
fi

# Vérifier modèle téléchargé
echo ""
echo "▶ Vérification modèle Qwen-Image-Edit-2509..."
if [ -d "models/checkpoints/Qwen-Image-Edit-2509-FP8" ]; then
    echo "✅ Modèle présent ($(du -sh models/checkpoints/Qwen-Image-Edit-2509-FP8 | cut -f1))"
else
    echo "❌ Modèle non trouvé"
    exit 1
fi

# Afficher info GPU
echo ""
echo "▶ Informations GPU:"
nvidia-smi --query-gpu=index,name,memory.total --format=csv,noheader

echo ""
echo "=== Lancement ComfyUI ==="
echo "GPU: 0 (RTX 3090)"
echo "Port: 8188"
echo "URL: http://localhost:8188"
echo ""
echo "Appuyez sur Ctrl+C pour arrêter"
echo ""

# Lancer ComfyUI sur GPU 0 (3090)
CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188