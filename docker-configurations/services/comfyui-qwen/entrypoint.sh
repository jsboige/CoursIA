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
if [ ! -f "venv/bin/pip" ]; then
    echo "📦 Création du venv..."
    rm -rf venv 2>/dev/null || true
    python3 -m venv venv --copies
    # Installer pip manuellement si ensurepip n'est pas disponible
    if [ ! -f "venv/bin/pip" ]; then
        echo "📦 Installation manuelle de pip..."
        curl -sS https://bootstrap.pypa.io/get-pip.py | venv/bin/python3
    fi
    venv/bin/pip install torch torchvision torchaudio --extra-index-url https://download.pytorch.org/whl/cu121
fi

# Installation des dépendances (toujours vérifier)
echo "📦 Vérification des dépendances..."
venv/bin/pip install -r requirements.txt
venv/bin/pip install einops

# =============================================================================
# CUSTOM NODES INSTALLATION
# =============================================================================
echo "Verification des custom nodes..."

# 1. ComfyUI-Login (Authentification)
if [ "$COMFYUI_LOGIN_ENABLED" = "true" ]; then
    LOGIN_DIR="custom_nodes/ComfyUI-Login"
    if [ ! -d "$LOGIN_DIR" ]; then
        echo "Installation de ComfyUI-Login..."
        git clone https://github.com/liusida/ComfyUI-Login.git "$LOGIN_DIR"
        venv/bin/pip install -r "$LOGIN_DIR/requirements.txt"
    fi

    # Installation explicite des dépendances critiques pour l'auth
    echo "🔒 Installation des dépendances d'authentification..."
    venv/bin/pip install aiohttp_session aiohttp_security bcrypt cryptography

    # Configuration de l'authentification (génération du fichier PASSWORD)
    echo "🔐 Configuration de l'authentification..."
    venv/bin/python3 -c "
import bcrypt
import os
import sys

username = os.environ.get('COMFYUI_USERNAME', 'admin')
# Le chemin doit correspondre à celui attendu par ComfyUI-Login (dans le dossier racine de ComfyUI/login)
password_dir = os.path.join('login')
password_path = os.path.join(password_dir, 'PASSWORD')
secret_token_path = os.path.join('.secrets', 'qwen-api-user.token')

if not os.path.exists(password_dir):
    os.makedirs(password_dir)

hashed = None

# Try to load from mounted secret
if os.path.exists(secret_token_path):
    try:
        with open(secret_token_path, 'rb') as f:
            content = f.read().strip()
            if content:
                hashed = content
                print(f'✅ Token chargé depuis {secret_token_path}')
    except Exception as e:
        print(f'⚠️ Erreur lecture token secret: {e}')

# Fallback to generation from password
if not hashed:
    print('⚠️ Pas de token secret trouvé, génération depuis mot de passe...')
    password = os.environ.get('COMFYUI_PASSWORD', '').encode('utf-8')
    if not password:
        # Si pas de mot de passe, on ne fait rien (laisse ComfyUI sans auth ou avec ancienne config)
        # Mais ici on veut forcer une config si possible
        pass
    
    if password:
        salt = bcrypt.gensalt()
        hashed = bcrypt.hashpw(password, salt)

if hashed:
    with open(password_path, 'wb') as f:
        f.write(hashed + b'\n' + username.encode('utf-8'))
    print(f'✅ Utilisateur {username} configuré')
else:
    print('⚠️ Aucune configuration d\'authentification appliquée')
"
else
    echo "Authentification desactivee (COMFYUI_LOGIN_ENABLED != true)"
fi

# 2. ComfyUI_QwenImageWanBridge (Nodes Qwen optionnels)
WANBRIDGE_DIR="custom_nodes/ComfyUI_QwenImageWanBridge"
if [ ! -d "$WANBRIDGE_DIR" ]; then
    echo "Installation de ComfyUI_QwenImageWanBridge..."
    git clone https://github.com/wanfuzhizun/ComfyUI_QwenImageWanBridge.git "$WANBRIDGE_DIR" || echo "WanBridge: echec clone (optionnel)"
    if [ -d "$WANBRIDGE_DIR" ]; then
        venv/bin/pip install transformers accelerate safetensors sentencepiece
    fi
else
    echo "ComfyUI_QwenImageWanBridge deja present"
fi

# 3. ComfyUI-GGUF (Support modeles GGUF - optionnel)
GGUF_DIR="custom_nodes/ComfyUI-GGUF"
if [ ! -d "$GGUF_DIR" ]; then
    echo "Installation de ComfyUI-GGUF (optionnel)..."
    git clone https://github.com/city96/ComfyUI-GGUF.git "$GGUF_DIR" || echo "GGUF: echec clone (optionnel)"
    if [ -d "$GGUF_DIR" ]; then
        venv/bin/pip install gguf
    fi
fi

# 4. ComfyUI-nunchaku (Quantification INT4 SVDQuant - Recommande pour VRAM limitee)
# NOTE: Version 1.1.0 requise pour compatibilite avec nunchaku backend 1.0.1
#       Version 1.2.0+ introduit 'use_additional_t_cond' incompatible avec backend 1.0.1
NUNCHAKU_DIR="custom_nodes/ComfyUI-nunchaku"
NUNCHAKU_PLUGIN_VERSION="v1.1.0"
if [ ! -d "$NUNCHAKU_DIR" ]; then
    echo "Installation de ComfyUI-nunchaku ${NUNCHAKU_PLUGIN_VERSION} (INT4 quantization)..."
    git clone --branch ${NUNCHAKU_PLUGIN_VERSION} --depth 1 https://github.com/nunchaku-ai/ComfyUI-nunchaku.git "$NUNCHAKU_DIR" || echo "Nunchaku: echec clone"
    if [ -d "$NUNCHAKU_DIR" ]; then
        echo "Installation du backend nunchaku..."
        # Detecter version PyTorch pour installer le bon wheel pre-compile
        TORCH_VERSION=$(venv/bin/python -c "import torch; print(torch.__version__.split('+')[0])")
        TORCH_MAJOR=$(echo $TORCH_VERSION | cut -d. -f1)
        TORCH_MINOR=$(echo $TORCH_VERSION | cut -d. -f2)
        NUNCHAKU_WHEEL_URL="https://github.com/nunchaku-ai/nunchaku/releases/download/v1.0.1/nunchaku-1.0.1+torch${TORCH_MAJOR}.${TORCH_MINOR}-cp311-cp311-linux_x86_64.whl"

        echo "Installation nunchaku 1.0.1 pour PyTorch ${TORCH_MAJOR}.${TORCH_MINOR}..."
        wget -q -O /tmp/nunchaku.whl "$NUNCHAKU_WHEEL_URL" && \
        venv/bin/pip install /tmp/nunchaku.whl && \
        rm -f /tmp/nunchaku.whl || \
        echo "ATTENTION: Echec installation nunchaku wheel, fonctionnalites INT4 non disponibles"

        # Installer dependances du plugin
        venv/bin/pip install diffusers>=0.35 peft>=0.17
    fi
else
    echo "ComfyUI-nunchaku deja present"
fi

# =============================================================================
# DEMARRAGE
# =============================================================================
echo "Demarrage du serveur ComfyUI..."
exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention