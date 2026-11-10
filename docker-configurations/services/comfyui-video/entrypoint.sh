#!/bin/bash
set -e

echo "Demarrage de l'entrypoint ComfyUI-Video..."

# System packages for OpenCV (cv2) and video processing
apt-get update -qq && apt-get install -y -qq libgl1 libglib2.0-0 2>/dev/null || echo "System packages: already installed or not needed"

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

# Gemma-3 tokenizer deps (LTX-2 GGUF text encoder: gemma-3-12b-it-qat GGUF).
# Without these, loading the gemma tokenizer fails at CLIPLoaderGGUF /
# DualCLIPLoaderGGUF time with "Please install sentencepiece and protobuf".
venv/bin/pip install sentencepiece protobuf

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
# Le hash bcrypt EST le credential lui-meme (le Bearer accepte par
# ComfyUI-Login). S'il est regenere a chaque boot, le Bearer change a chaque
# redemarrage et tout client qui garde l'ancien echoue. Charger un hash
# STABLE depuis un fichier monte supprime cette derive -- meme mecanisme que
# comfyui-qwen (cf .secrets/qwen-api-user.token).
secret_token_path = os.path.join('.secrets', 'video-api-user.token')

if not os.path.exists(password_dir):
    os.makedirs(password_dir)

password = os.environ.get('COMFYUI_PASSWORD', '').encode('utf-8')
hashed = None

# 1) Voie durable : hash stable monte en lecture seule.
if os.path.exists(secret_token_path):
    try:
        with open(secret_token_path, 'rb') as f:
            content = f.read().strip()
        if content:
            hashed = content
            print(f'Token stable charge depuis {secret_token_path}')
    except Exception as exc:
        print(f'Erreur lecture token secret: {exc}')

# 2) Repli : generation depuis le mot de passe (comportement historique,
#    derive par construction -- le Bearer change a chaque redemarrage).
if not hashed and password:
    print('Pas de token stable monte, generation depuis COMFYUI_PASSWORD (Bearer instable)')
    hashed = bcrypt.hashpw(password, bcrypt.gensalt())

if hashed:
    with open(password_path, 'wb') as f:
        f.write(hashed + b'\n' + username.encode('utf-8'))
    # Self-check : le hash ecrit doit verifier le mot de passe configure.
    if password and bcrypt.checkpw(password, hashed):
        print(f'AUTH OK: utilisateur {username} configure, hash verifie contre COMFYUI_PASSWORD')
    else:
        print(f'AUTH OK: utilisateur {username} configure (token stable monte)')
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

# 5. ComfyUI-GGUF (Support modeles GGUF - Qwen/Hunyuan quantizes)
GGUF_DIR="custom_nodes/ComfyUI-GGUF"
if [ ! -d "$GGUF_DIR" ]; then
    echo "Installation de ComfyUI-GGUF (quantization GGUF)..."
    git clone https://github.com/city96/ComfyUI-GGUF.git "$GGUF_DIR" || echo "GGUF: echec clone (optionnel)"
    if [ -d "$GGUF_DIR" ]; then
        venv/bin/pip install gguf
    fi
else
    echo "ComfyUI-GGUF deja present"
fi

# =============================================================================
# QUANTIZATION SUPPORT (INT8/FP8)
# =============================================================================
# NOTE: torchao is NOT installed here because torchao>=0.10 breaks diffusers
# lazy imports (logger undefined in torchao_quantizer.py). If torchao is needed
# later, pin torchao<0.10 or wait for a diffusers fix.

echo "Installation des outils de quantization (sans torchao)..."

# Optimum Quanto pour quantization Hugging Face
venv/bin/pip install optimum-quanto>=0.2.0 || echo "Optimum-Quanto: installation optionnelle echouee"

# bitsandbytes pour INT8 linear layers
venv/bin/pip install bitsandbytes>=0.43.0 || echo "Bitsandbytes: installation optionnelle echouee"

# =============================================================================
# DEMARRAGE
# =============================================================================
echo "Demarrage du serveur ComfyUI-Video..."

# GPU Device ID (defaut: 0)
GPU_ID=${GPU_DEVICE_ID:-0}
echo "Utilisation GPU ${GPU_ID}"

exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention --cuda-device ${GPU_ID}
