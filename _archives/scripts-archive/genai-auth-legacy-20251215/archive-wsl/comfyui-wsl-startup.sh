#!/bin/bash

# Script WSL pour démarrer ComfyUI en standalone
# Résout le problème de permissions Docker en utilisant WSL natif

set -e

echo "🚀 Démarrage ComfyUI via WSL standalone..."
echo "📍 Répertoire de travail: $(pwd)"

# Vérifier si nous sommes dans le bon répertoire
if [ ! -d "/mnt/d/Dev/CoursIA/docker-configurations/comfyui-qwen/ComfyUI" ]; then
    echo "❌ Erreur: Répertoire ComfyUI non trouvé dans WSL"
    echo "📂 Création du répertoire de destination..."
    mkdir -p /tmp/comfyui-wsl
    
    echo "📋 Copie des fichiers ComfyUI depuis Windows vers WSL..."
    # Copier depuis le montage Windows vers WSL
    cp -r /mnt/d/Dev/CoursIA/docker-configurations/comfyui-qwen/ComfyUI/* /tmp/comfyui-wsl/
    
    cd /tmp/comfyui-wsl
else
    echo "✅ Répertoire ComfyUI trouvé dans WSL"
    cd /mnt/d/Dev/CoursIA/docker-configurations/comfyui-qwen/ComfyUI
fi

echo "🐍 Vérification de Python..."
python3 --version

echo "📦 Vérification des dépendances..."
if [ -f "requirements.txt" ]; then
    echo "✅ requirements.txt trouvé"
    
    # Créer l'environnement virtuel s'il n'existe pas
    if [ ! -d "venv" ]; then
        echo "🔧 Création de l'environnement virtuel..."
        python3 -m venv venv
        source venv/bin/activate
        
        echo "📥 Installation des dépendances..."
        pip install --no-cache-dir -r requirements.txt
        
        echo "✅ Environnement virtuel créé et dépendances installées"
    else
        echo "✅ Environnement virtuel existant, activation..."
        source venv/bin/activate
    fi
else
    echo "❌ Erreur: requirements.txt non trouvé"
    exit 1
fi

echo "🚀 Démarrage de ComfyUI..."
echo "🌐 Interface web disponible sur: http://localhost:8188"
echo "🔑 Authentification activée avec token Qwen"

# Variables d'environnement pour ComfyUI
export CUDA_VISIBLE_DEVICES=0
export NVIDIA_VISIBLE_DEVICES=0
export COMFYUI_PORT=8188
export COMFYUI_LISTEN=0.0.0.0
export COMFYUI_LOGIN_ENABLED=true
export COMFYUI_AUTH_TOKEN=${QWEN_API_TOKEN}

# Démarrer ComfyUI
exec python main.py \
    --listen 0.0.0.0 \
    --port 8188 \
    --preview-method auto \
    --use-split-cross-attention