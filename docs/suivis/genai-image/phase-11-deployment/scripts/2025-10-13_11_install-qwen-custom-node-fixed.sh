#!/bin/bash
# Phase 11: Installation Custom Node ComfyUI-QwenImageWanBridge (Version Corrigée)
# Date: 2025-10-13
# Repository: fblissjr/ComfyUI-QwenImageWanBridge

set -e  # Arrêter en cas d'erreur

COMFYUI_DIR="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"
CUSTOM_NODES_DIR="$COMFYUI_DIR/custom_nodes"

echo "=== Phase 11: Installation Custom Node Qwen (Repository Correct) ==="
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

# Clone du custom node Qwen (repository correct)
echo ""
echo "▶ Clone du custom node ComfyUI-QwenImageWanBridge..."
echo "Repository: https://github.com/fblissjr/ComfyUI-QwenImageWanBridge"

if [ -d "ComfyUI-QwenImageWanBridge" ]; then
    echo "⚠️  Custom node déjà présent, mise à jour..."
    cd ComfyUI-QwenImageWanBridge
    git pull
    cd ..
else
    git clone https://github.com/fblissjr/ComfyUI-QwenImageWanBridge.git
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

echo ""
echo "▶ Contenu du README (si disponible)..."
if [ -f "README.md" ]; then
    head -20 README.md
fi

# Retour à la racine ComfyUI
cd "$COMFYUI_DIR"

# Lister tous les custom nodes
echo ""
echo "▶ Custom nodes installés:"
ls -la custom_nodes/

echo ""
echo "=== ✅ Custom Node Qwen installé avec succès ==="
echo ""
echo "Informations:"
echo "- Repository: fblissjr/ComfyUI-QwenImageWanBridge"
echo "- Support: Multi-image editing, qwen2.5-vl, custom prompts"
echo "- Emplacement: $CUSTOM_NODES_DIR/ComfyUI-QwenImageWanBridge"