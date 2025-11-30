#!/bin/bash
set -e

echo "🚀 Démarrage de l'entrypoint ComfyUI..."

# Clonage si nécessaire
if [ ! -f "main.py" ]; then
    echo "📥 Clonage de ComfyUI..."
    if [ -d ".git" ]; then
        echo "🔄 Dépôt git déjà présent, pull..."
        git pull
    else
        echo "✨ Initialisation du dépôt..."
        git init
        git remote add origin https://github.com/comfyanonymous/ComfyUI.git
        git fetch
        git checkout -t origin/master -f
    fi
fi

# Installation venv si nécessaire
if [ ! -d "venv" ]; then
    echo "📦 Création du venv..."
    python3 -m venv venv
    venv/bin/pip install torch torchvision torchaudio --extra-index-url https://download.pytorch.org/whl/cu121
fi

# Installation des dépendances (toujours vérifier)
echo "📦 Vérification des dépendances..."
venv/bin/pip install -r requirements.txt
venv/bin/pip install einops

# Installation ComfyUI-Login
LOGIN_DIR="custom_nodes/ComfyUI_Login"
if [ ! -d "$LOGIN_DIR" ]; then
    echo "🔑 Installation de ComfyUI-Login..."
    git clone https://github.com/Comfy-Org/ComfyUI_Login.git "$LOGIN_DIR"
    venv/bin/pip install -r "$LOGIN_DIR/requirements.txt"
fi

# Installation explicite des dépendances critiques pour l'auth
echo "🔒 Installation des dépendances d'authentification..."
venv/bin/pip install aiohttp_session aiohttp_security bcrypt

# Démarrage
echo "🔥 Démarrage du serveur..."
exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention