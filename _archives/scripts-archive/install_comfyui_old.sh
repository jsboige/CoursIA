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
# Vérifier si ComfyUI est déjà installé et fonctionnel
if [ ! -d "ComfyUI" ] || [ ! -f "ComfyUI/main.py" ]; then
    echo "Clonage de ComfyUI depuis GitHub..."
    rm -rf ComfyUI 2>/dev/null || true
    sleep 2
    git clone https://github.com/comfyanonymous/ComfyUI.git --depth 1
else
    echo "ComfyUI déjà présent, vérification de l'installation..."
    # Vérifier si main.py existe
    if [ ! -f "ComfyUI/main.py" ]; then
        echo "main.py manquant, réinstallation..."
        rm -rf ComfyUI
        sleep 2
        git clone https://github.com/comfyanonymous/ComfyUI.git --depth 1
    else
        echo "ComfyUI semble correctement installé"
    fi
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

echo "Installation ComfyUI-Login..."
if [ ! -d custom_nodes/ComfyUI-Login ]; then
    echo "Installation de ComfyUI-Login..."
    cd custom_nodes
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

echo "Installation ComfyUI-QwenImageWanBridge..."
# Temporairement désactivée l'installation de ComfyUI-QwenImageWanBridge pour permettre le démarrage de ComfyUI
# TODO: Réactiver cette section une fois ComfyUI fonctionnel
# if [ ! -d custom_nodes/ComfyUI-QwenImageWanBridge ]; then
#     echo "Installation de ComfyUI-QwenImageWanBridge..."
#     cd custom_nodes
#     echo "Suppression de linstallation existante pour réinstallation propre..."
#     rm -rf ComfyUI-QwenImageWanBridge 2>/dev/null || true
#     sleep 2
#     for attempt in 1 2 3 4 5; do
#         echo "Tentative $attempt/5 pour installer ComfyUI-QwenImageWanBridge..."
#         # Utilisation de wget pour contourner les problèmes d'authentification Git
#         if wget https://github.com/gokayfem/ComfyUI-QwenImageWanBridge/archive/main.zip -O ComfyUI-QwenImageWanBridge.zip; then
#             echo "Téléchargement de ComfyUI-QwenImageWanBridge réussi"
#             unzip -q ComfyUI-QwenImageWanBridge.zip && rm ComfyUI-QwenImageWanBridge.zip
#             mv ComfyUI-QwenImageWanBridge-main ComfyUI-QwenImageWanBridge
#             break
#         else
#             echo "Échec du téléchargement, tentative en cours..."
#             if [ "$attempt" -eq 5 ]; then
#                 echo "ERREUR: Impossible de télécharger ComfyUI-QwenImageWanBridge après 5 tentatives"
#                 exit 1
#             fi
#             sleep 10
#         fi
#     done
#     cd ComfyUI-QwenImageWanBridge
#     pip install -r requirements.txt
#     cd ../..
# else
#     echo "ComfyUI-QwenImageWanBridge déjà installé, vérification des mises à jour..."
#     cd custom_nodes/ComfyUI-QwenImageWanBridge
#     git pull origin main || echo "Avertissement: Impossible de mettre à jour ComfyUI-QwenImageWanBridge"
#     cd ../..
# fi
echo "ComfyUI-QwenImageWanBridge temporairement désactivé pour permettre le démarrage de ComfyUI"

echo "Configuration du token ComfyUI-Login..."
mkdir -p custom_nodes/ComfyUI-Login
echo "${COMFYUI_BEARER_TOKEN}" > custom_nodes/ComfyUI-Login/PASSWORD
chmod 600 custom_nodes/ComfyUI-Login/PASSWORD

echo "Configuration terminée, démarrage de ComfyUI..."
exec venv/bin/python3 main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention