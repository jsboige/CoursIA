#!/bin/bash
# Phase 11: Installation Custom Node ComfyUI-QwenImageWanBridge
# Date: 2025-10-13
# Objectif: Installer le custom node pour Qwen Image-Edit dans ComfyUI

set -e  # Arrêter en cas d'erreur

COMFYUI_DIR="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"
CUSTOM_NODES_DIR="$COMFYUI_DIR/custom_nodes"

echo "=== Phase 11: Installation Custom Node Qwen ==="
echo "Répertoire ComfyUI: $COMFYUI_DIR"
echo "Répertoire custom_nodes: $CUSTOM_NODES_DIR"
echo ""

# Vérifier que le répertoire ComfyUI existe
if [ ! -d "$COMFYUI_DIR" ]; then
    echo "❌ Erreur: Répertoire ComfyUI non trouvé: $COMFYUI_DIR"
    exit 1
fi

cd "$COMFYUI_DIR"

# Activer l'environnement virtuel
echo "▶ Activation environnement virtuel..."
source venv/bin/activate

# Naviguer vers custom_nodes
echo ""
echo "▶ Navigation vers custom_nodes..."
cd custom_nodes

# Clone du custom node Qwen
echo ""
echo "▶ Clone du custom node ComfyUI-QwenImageWanBridge..."
if [ -d "ComfyUI-QwenImageWanBridge" ]; then
    echo "⚠️  Custom node déjà présent, mise à jour..."
    cd ComfyUI-QwenImageWanBridge
    git pull
    cd ..
else
    git clone https://github.com/qwenImage/ComfyUI-QwenImageWanBridge.git
fi

# Installer les requirements du custom node
echo ""
echo "▶ Installation requirements du custom node..."
cd ComfyUI-QwenImageWanBridge

if [ -f "requirements.txt" ]; then
    pip install -r requirements.txt
    echo "✅ Requirements installés"
else
    echo "⚠️  Pas de requirements.txt trouvé"
fi

# Vérifier structure du custom node
echo ""
echo "▶ Vérification structure custom node..."
ls -la

# Retour à la racine ComfyUI
cd "$COMFYUI_DIR"

# Lister tous les custom nodes
echo ""
echo "▶ Custom nodes installés:"
ls -la custom_nodes/

echo ""
echo "=== ✅ Custom Node Qwen installé avec succès ==="