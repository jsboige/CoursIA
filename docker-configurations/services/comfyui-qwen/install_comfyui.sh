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

echo "Installation terminée avec succès!"