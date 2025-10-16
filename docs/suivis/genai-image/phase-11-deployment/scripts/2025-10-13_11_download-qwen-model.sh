#!/bin/bash
# Phase 11: Téléchargement Qwen-Image-Edit-2509
# Date: 2025-10-13
# Objectif: Télécharger le modèle Qwen-Image-Edit-2509 FP8 (~12GB)

set -e  # Arrêter en cas d'erreur

COMFYUI_DIR="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"
MODEL_DIR="$COMFYUI_DIR/models/checkpoints"
MODEL_NAME="Qwen-Image-Edit-2509"

echo "=== Phase 11: Téléchargement Qwen-Image-Edit-2509 ==="
echo "Répertoire ComfyUI: $COMFYUI_DIR"
echo "Répertoire modèles: $MODEL_DIR"
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

# Créer répertoire modèles si nécessaire
echo ""
echo "▶ Création répertoire modèles..."
mkdir -p "$MODEL_DIR/$MODEL_NAME-FP8"

# Installer huggingface-hub si nécessaire
echo ""
echo "▶ Installation/Vérification huggingface-hub..."
pip install --upgrade huggingface-hub

# Vérifier si token HF est configuré
echo ""
echo "▶ Vérification token HuggingFace..."
if ! huggingface-cli whoami &>/dev/null; then
    echo "⚠️  Attention: Token HuggingFace non configuré"
    echo "Pour télécharger des modèles privés, configurez votre token:"
    echo "  huggingface-cli login"
    echo ""
    echo "Pour les modèles publics, le téléchargement continuera..."
fi

# Télécharger le modèle Qwen-Image-Edit-2509
echo ""
echo "▶ Téléchargement Qwen-Image-Edit-2509..."
echo "Taille: ~12GB - Cela peut prendre plusieurs minutes"
echo ""

# Option 1: Télécharger avec huggingface-cli (recommandé)
huggingface-cli download Qwen/Qwen-Image-Edit-2509 \
    --local-dir "$MODEL_DIR/$MODEL_NAME-FP8" \
    --local-dir-use-symlinks False \
    --resume-download

# Vérifier téléchargement
echo ""
echo "▶ Vérification téléchargement..."
if [ -d "$MODEL_DIR/$MODEL_NAME-FP8" ]; then
    echo "✅ Répertoire modèle créé"
    
    # Lister fichiers téléchargés
    echo ""
    echo "Fichiers téléchargés:"
    ls -lh "$MODEL_DIR/$MODEL_NAME-FP8/"
    
    # Calculer taille totale
    echo ""
    echo "Taille totale:"
    du -sh "$MODEL_DIR/$MODEL_NAME-FP8/"
else
    echo "❌ Erreur: Répertoire modèle non créé"
    exit 1
fi

echo ""
echo "=== ✅ Qwen-Image-Edit-2509 téléchargé avec succès ==="