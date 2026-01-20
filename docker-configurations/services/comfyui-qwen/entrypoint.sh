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

# =============================================================================
# DEMARRAGE
# =============================================================================
echo "Demarrage du serveur ComfyUI..."
exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention