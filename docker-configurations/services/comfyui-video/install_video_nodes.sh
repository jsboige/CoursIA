#!/bin/bash
# Installation des custom nodes video pour ComfyUI
# Executer dans le container ComfyUI-Video apres le premier demarrage
#
# Usage: docker exec comfyui-video bash /install_video_nodes.sh

set -e

CUSTOM_NODES_DIR="/workspace/ComfyUI/custom_nodes"
cd "$CUSTOM_NODES_DIR"

echo "=== Installation des nodes video ComfyUI ==="

# AnimateDiff-Evolved - Animation et generation video
if [ ! -d "ComfyUI-AnimateDiff-Evolved" ]; then
    echo "Installation: ComfyUI-AnimateDiff-Evolved..."
    git clone https://github.com/Kosinkadink/ComfyUI-AnimateDiff-Evolved.git
    cd ComfyUI-AnimateDiff-Evolved && pip install -r requirements.txt && cd ..
else
    echo "Deja installe: ComfyUI-AnimateDiff-Evolved"
fi

# VideoHelperSuite - Utilitaires video (load, save, combine)
if [ ! -d "ComfyUI-VideoHelperSuite" ]; then
    echo "Installation: ComfyUI-VideoHelperSuite..."
    git clone https://github.com/Kosinkadink/ComfyUI-VideoHelperSuite.git
    cd ComfyUI-VideoHelperSuite && pip install -r requirements.txt && cd ..
else
    echo "Deja installe: ComfyUI-VideoHelperSuite"
fi

# HunyuanVideoWrapper - Tencent HunyuanVideo via ComfyUI
if [ ! -d "ComfyUI-HunyuanVideoWrapper" ]; then
    echo "Installation: ComfyUI-HunyuanVideoWrapper..."
    git clone https://github.com/kijai/ComfyUI-HunyuanVideoWrapper.git
    cd ComfyUI-HunyuanVideoWrapper && pip install -r requirements.txt && cd ..
else
    echo "Deja installe: ComfyUI-HunyuanVideoWrapper"
fi

echo ""
echo "=== Installation terminee ==="
echo "Redemarrez le container pour charger les nouveaux nodes."
echo "  docker restart comfyui-video"
