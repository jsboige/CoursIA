#!/bin/bash
set -e

echo "=== Installation ComfyUI-Qwen ==="
echo "Installation des dépendances système..."
apt-get update -qq
apt-get install -y -qq --no-install-recommends python3 python3-pip python3-virtualenv git curl wget ca-certificates

echo "Nettoyage..."
apt-get clean
rm -rf /var/lib/apt/lists/*

echo "Clonage ComfyUI..."
cd /workspace

# Gestion robuste du répertoire ComfyUI
if [ -d "ComfyUI" ]; then
    echo "Répertoire ComfyUI détecté, analyse de l'état..."
    
    # Vérifier si c'est un montage de volume partagé
    if mountpoint -q "ComfyUI" 2>/dev/null; then
        echo "ComfyUI est un montage de volume, utilisation directe..."
    else
        # Vérifier si main.py existe
        if [ -f "ComfyUI/main.py" ]; then
            echo "ComfyUI semble correctement installé"
        else
            echo "Répertoire ComfyUI corrompu ou incomplet, nettoyage..."
            # Forcer la suppression avec les bonnes options
            find ComfyUI -type f -name "*.py" -delete 2>/dev/null || true
            find ComfyUI -type d -delete 2>/dev/null || true
            find ComfyUI -type f -name "*.sh" -delete 2>/dev/null || true
            sleep 2
            
            echo "Tentative de clonage..."
            git clone https://github.com/comfyanonymous/ComfyUI.git --depth 1 || {
                echo "Échec du clonage, tentative de nettoyage complet..."
                rm -rf ComfyUI
                sleep 3
                git clone https://github.com/comfyanonymous/ComfyUI.git --depth 1
            }
        fi
    fi
else
    echo "Clonage de ComfyUI depuis GitHub..."
    rm -rf ComfyUI 2>/dev/null || true
    sleep 2
    git clone https://github.com/comfyanonymous/ComfyUI.git --depth 1
fi

cd /workspace/ComfyUI
# Forcer la reconstruction complète du venv pour corriger le problème pyyaml
echo "Suppression du venv existant pour reconstruction complète..."
rm -rf venv
echo "Création du venv et installation des dépendances..."
python3 -m venv venv
venv/bin/pip install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu124
venv/bin/pip install -r requirements.txt
# Installation du module yaml manquant pour ComfyUI
venv/bin/pip install pyyaml
echo "Venv reconstruit avec pyyaml inclus"

echo "Création du répertoire custom_nodes..."
mkdir -p custom_nodes

# =============================================================================
# CUSTOM NODES INSTALLATION
# =============================================================================

echo "=== Installation des Custom Nodes ==="

cd /workspace/ComfyUI/custom_nodes

# -----------------------------------------------------------------------------
# 1. ComfyUI-Login (Authentification)
# -----------------------------------------------------------------------------
echo "1/3 Installation ComfyUI-Login..."
if [ ! -d "ComfyUI-Login" ]; then
    for attempt in 1 2 3; do
        echo "  Tentative $attempt/3 pour cloner ComfyUI-Login..."
        if git clone https://github.com/liusida/ComfyUI-Login.git; then
            echo "  Clonage de ComfyUI-Login réussi"
            break
        else
            if [ "$attempt" -eq 3 ]; then
                echo "  ERREUR: Impossible de cloner ComfyUI-Login après 3 tentatives"
                exit 1
            fi
            sleep 5
        fi
    done
    cd ComfyUI-Login
    /workspace/ComfyUI/venv/bin/pip install -r requirements.txt
    cd ..
else
    echo "  ComfyUI-Login déjà installé"
fi

# -----------------------------------------------------------------------------
# 2. ComfyUI_QwenImageWanBridge (Nodes Qwen - CRITICAL)
# Source: https://github.com/wanfuzhizun/ComfyUI_QwenImageWanBridge
# Ref: Phase 29 - docs/suivis/genai-image/phase-29-corrections-qwen/SYNTHESE-COMPLETE-PHASE-29.md
# -----------------------------------------------------------------------------
echo "2/3 Installation ComfyUI_QwenImageWanBridge..."
if [ ! -d "ComfyUI_QwenImageWanBridge" ]; then
    for attempt in 1 2 3; do
        echo "  Tentative $attempt/3 pour cloner ComfyUI_QwenImageWanBridge..."
        if git clone https://github.com/wanfuzhizun/ComfyUI_QwenImageWanBridge.git; then
            echo "  Clonage de ComfyUI_QwenImageWanBridge réussi"
            break
        else
            if [ "$attempt" -eq 3 ]; then
                echo "  ERREUR: Impossible de cloner ComfyUI_QwenImageWanBridge après 3 tentatives"
                exit 1
            fi
            sleep 5
        fi
    done
    # Installation des dépendances WanBridge
    echo "  Installation des dépendances WanBridge..."
    /workspace/ComfyUI/venv/bin/pip install transformers accelerate safetensors sentencepiece
else
    echo "  ComfyUI_QwenImageWanBridge déjà installé"
fi

# -----------------------------------------------------------------------------
# 3. ComfyUI-GGUF (Support modèles GGUF - optionnel)
# -----------------------------------------------------------------------------
echo "3/3 Installation ComfyUI-GGUF (optionnel)..."
if [ ! -d "ComfyUI-GGUF" ]; then
    git clone https://github.com/city96/ComfyUI-GGUF.git || echo "  Avertissement: ComfyUI-GGUF non installé (optionnel)"
    if [ -d "ComfyUI-GGUF" ]; then
        /workspace/ComfyUI/venv/bin/pip install gguf
    fi
else
    echo "  ComfyUI-GGUF déjà installé"
fi

cd /workspace/ComfyUI

# =============================================================================
# MODELS DIRECTORIES
# =============================================================================
echo "=== Création des répertoires modèles ==="
mkdir -p models/diffusion_models
mkdir -p models/text_encoders
mkdir -p models/vae
mkdir -p models/loras

# =============================================================================
# MODELS DOWNLOAD INSTRUCTIONS
# =============================================================================
echo ""
echo "============================================================"
echo "INSTALLATION TERMINÉE - MODÈLES À TÉLÉCHARGER"
echo "============================================================"
echo ""
echo "Les modèles Qwen FP8 doivent être téléchargés manuellement:"
echo ""
echo "1. Diffusion Model (20GB):"
echo "   URL: https://huggingface.co/Comfy-Org/Qwen-Image-Edit_ComfyUI"
echo "   Fichier: split_files/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors"
echo "   Dest: /workspace/ComfyUI/models/diffusion_models/"
echo ""
echo "2. Text Encoder (8.8GB):"
echo "   URL: https://huggingface.co/Comfy-Org/Qwen-Image_ComfyUI"
echo "   Fichier: split_files/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors"
echo "   Dest: /workspace/ComfyUI/models/text_encoders/"
echo ""
echo "3. VAE (243MB):"
echo "   URL: https://huggingface.co/Comfy-Org/Qwen-Image_ComfyUI"
echo "   Fichier: split_files/vae/qwen_image_vae.safetensors"
echo "   Dest: /workspace/ComfyUI/models/vae/"
echo ""
echo "Script de téléchargement: scripts/genai-stack/download_qwen_models.py"
echo "============================================================"
echo ""
echo "Installation terminée avec succès!"