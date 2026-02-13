#!/bin/bash
set -e

echo "Demarrage de l'entrypoint ComfyUI-Video..."

# Clonage si necessaire
if [ ! -f "main.py" ]; then
    echo "Clonage de ComfyUI..."
    if [ -d ".git" ]; then
        echo "Depot git deja present, pull..."
        git pull
    else
        echo "Initialisation du depot..."
        git init
        git remote add origin https://github.com/comfyanonymous/ComfyUI.git
        git fetch
        git checkout -t origin/master -f
    fi
fi

# Installation venv si necessaire
if [ ! -d "venv" ]; then
    echo "Creation du venv..."
    python3 -m venv venv
    venv/bin/pip install torch torchvision torchaudio --extra-index-url https://download.pytorch.org/whl/cu121
fi

# Installation des dependances
echo "Verification des dependances..."
venv/bin/pip install -r requirements.txt
venv/bin/pip install einops

# =============================================================================
# CUSTOM NODES - VIDEO
# =============================================================================
echo "Verification des custom nodes video..."

# 1. ComfyUI-Login (Authentification)
if [ "$COMFYUI_LOGIN_ENABLED" = "true" ]; then
    LOGIN_DIR="custom_nodes/ComfyUI-Login"
    if [ ! -d "$LOGIN_DIR" ]; then
        echo "Installation de ComfyUI-Login..."
        git clone https://github.com/liusida/ComfyUI-Login.git "$LOGIN_DIR"
        venv/bin/pip install -r "$LOGIN_DIR/requirements.txt"
    fi

    venv/bin/pip install aiohttp_session aiohttp_security bcrypt cryptography

    echo "Configuration de l'authentification..."
    venv/bin/python3 -c "
import bcrypt
import os

username = os.environ.get('COMFYUI_USERNAME', 'admin')
password_dir = os.path.join('login')
password_path = os.path.join(password_dir, 'PASSWORD')

if not os.path.exists(password_dir):
    os.makedirs(password_dir)

password = os.environ.get('COMFYUI_PASSWORD', '').encode('utf-8')
if password:
    salt = bcrypt.gensalt()
    hashed = bcrypt.hashpw(password, salt)
    with open(password_path, 'wb') as f:
        f.write(hashed + b'\n' + username.encode('utf-8'))
    print(f'Utilisateur {username} configure')
else:
    print('Aucun mot de passe configure, authentification desactivee')
"
else
    echo "Authentification desactivee (COMFYUI_LOGIN_ENABLED != true)"
fi

# 2. ComfyUI-AnimateDiff-Evolved
ANIMATEDIFF_DIR="custom_nodes/ComfyUI-AnimateDiff-Evolved"
if [ ! -d "$ANIMATEDIFF_DIR" ]; then
    echo "Installation de ComfyUI-AnimateDiff-Evolved..."
    git clone https://github.com/Kosinkadink/ComfyUI-AnimateDiff-Evolved.git "$ANIMATEDIFF_DIR"
    if [ -f "$ANIMATEDIFF_DIR/requirements.txt" ]; then
        venv/bin/pip install -r "$ANIMATEDIFF_DIR/requirements.txt"
    fi
else
    echo "ComfyUI-AnimateDiff-Evolved deja present"
fi

# 3. ComfyUI-VideoHelperSuite
VHS_DIR="custom_nodes/ComfyUI-VideoHelperSuite"
if [ ! -d "$VHS_DIR" ]; then
    echo "Installation de ComfyUI-VideoHelperSuite..."
    git clone https://github.com/Kosinkadink/ComfyUI-VideoHelperSuite.git "$VHS_DIR"
    if [ -f "$VHS_DIR/requirements.txt" ]; then
        venv/bin/pip install -r "$VHS_DIR/requirements.txt"
    fi
else
    echo "ComfyUI-VideoHelperSuite deja present"
fi

# 4. ComfyUI-HunyuanVideoWrapper
HUNYUAN_DIR="custom_nodes/ComfyUI-HunyuanVideoWrapper"
if [ ! -d "$HUNYUAN_DIR" ]; then
    echo "Installation de ComfyUI-HunyuanVideoWrapper..."
    git clone https://github.com/kijai/ComfyUI-HunyuanVideoWrapper.git "$HUNYUAN_DIR"
    if [ -f "$HUNYUAN_DIR/requirements.txt" ]; then
        venv/bin/pip install -r "$HUNYUAN_DIR/requirements.txt"
    fi
else
    echo "ComfyUI-HunyuanVideoWrapper deja present"
fi

# =============================================================================
# DEMARRAGE
# =============================================================================
echo "Demarrage du serveur ComfyUI-Video..."
exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention
