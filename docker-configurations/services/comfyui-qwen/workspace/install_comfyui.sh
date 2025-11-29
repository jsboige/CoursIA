#!/bin/bash

echo "=== Installation ComfyUI-Qwen ==="

# Vérifier si ComfyUI est déjà cloné
if [ ! -d "ComfyUI" ]; then
    echo "Création du répertoire ComfyUI..."
    mkdir -p ComfyUI
    echo "Clonage ComfyUI..."
    git clone https://github.com/comfyanonymous/ComfyUI.git
else
    echo "Répertoire ComfyUI détecté, analyse de l'état..."
fi

# Vérifier si ComfyUI est un montage de volume
if [ -f "/workspace/ComfyUI/.volume_mounted" ]; then
    echo "ComfyUI est un montage de volume, utilisation directe..."
    # Nettoyer le venv existant pour reconstruction complète
    if [ -d "venv" ]; then
        echo "Suppression du venv existant pour reconstruction complète..."
        rm -rf venv
    fi
else
    echo "ComfyUI est local, preservation du venv si existant..."
fi

echo "Création du venv et installation des dépendances..."
python3 -m venv venv
source venv/bin/activate

# Installation des dépendances PyTorch avec support CUDA
pip install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu124

# Installation des dépendances additionnelles
pip install -r requirements.txt

# Installation des custom nodes
echo "Installation des custom nodes..."

# ComfyUI-Login (uniquement si activé)
if [ "${COMFYUI_LOGIN_ENABLED:-false}" = "true" ]; then
    if [ ! -d "custom_nodes/ComfyUI-Login" ]; then
        echo "Installation de ComfyUI-Login..."
        cd custom_nodes
        # Gestion d'erreur réseau/DNS avec retry
        for attempt in 1 2 3; do
            echo "Tentative $attempt/3 pour cloner ComfyUI-Login..."
            if git clone https://github.com/liusida/ComfyUI-Login.git; then
                echo "Clonage de ComfyUI-Login réussi"
                break
            else
                echo "Échec du clonage, tentative en cours..."
                if [ "$attempt" -eq 3 ]; then
                    echo "ERREUR: Impossible de cloner ComfyUI-Login après 3 tentatives"
                    exit 1
                fi
                sleep 5
            fi
        done
        cd ComfyUI-Login
        pip install -r requirements.txt
        cd ../..
    else
        echo "ComfyUI-Login déjà installé, vérification des mises à jour..."
        cd custom_nodes/ComfyUI-Login
        git pull origin main || echo "Avertissement: Impossible de mettre à jour ComfyUI-Login"
        cd ../..
    fi
else
    echo "ComfyUI-Login désactivé, installation ignorée..."
fi

# ComfyUI-QwenImageWanBridge
if [ ! -d "custom_nodes/ComfyUI-QwenImageWanBridge" ]; then
    echo "Installation de ComfyUI-QwenImageWanBridge..."
    cd custom_nodes
    # Forcer la réinstallation complète de ComfyUI-QwenImageWanBridge
    echo "Suppression de l'installation existante pour réinstallation propre..."
    rm -rf ComfyUI-QwenImageWanBridge 2>/dev/null || true
    sleep 2
    # Gestion d'erreur réseau/DNS avec retry amélioré
    for attempt in 1 2 3 4 5; do
        echo "Tentative $attempt/5 pour cloner ComfyUI-QwenImageWanBridge..."
        if git clone https://github.com/gokayfem/ComfyUI-QwenImageWanBridge.git; then
            echo "Clonage de ComfyUI-QwenImageWanBridge réussi"
            break
        else
            echo "Échec du clonage, tentative en cours..."
            if [ "$attempt" -eq 5 ]; then
                echo "ERREUR: Impossible de cloner ComfyUI-QwenImageWanBridge après 5 tentatives"
                exit 1
            fi
            sleep 10
        fi
    done
    cd ComfyUI-QwenImageWanBridge
    pip install -r requirements.txt
    cd ../..
else
    echo "ComfyUI-QwenImageWanBridge déjà installé, vérification des mises à jour..."
    cd custom_nodes/ComfyUI-QwenImageWanBridge
    git pull origin main || echo "Avertissement: Impossible de mettre à jour ComfyUI-QwenImageWanBridge"
    cd ../..
fi

# Configuration du token ComfyUI-Login (uniquement si activé)
if [ "${COMFYUI_LOGIN_ENABLED:-false}" = "true" ]; then
    echo "Configuration du token ComfyUI-Login..."
    mkdir -p custom_nodes/ComfyUI-Login
    echo "${COMFYUI_BEARER_TOKEN}" > custom_nodes/ComfyUI-Login/PASSWORD
    chmod 600 custom_nodes/ComfyUI-Login/PASSWORD
fi

echo "Configuration terminée, démarrage de ComfyUI..."
cd ComfyUI
exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention