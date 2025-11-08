#!/bin/bash
# Script de débogage pour le démarrage de ComfyUI dans le conteneur Docker

set -e

echo "=== Début du script de débogage ComfyUI ==="
echo "Date: $(date)"
echo "Répertoire courant: $(pwd)"

echo "--- Installation des dépendances système ---"
apt-get update -qq && \
apt-get install -y -qq --no-install-recommends python3 python3-pip git curl wget ca-certificates python3.10-venv && \
apt-get clean && \
rm -rf /var/lib/apt/lists/*
echo "✓ Dépendances système installées."

echo "--- Vérification de l'environnement ComfyUI ---"
cd /workspace/ComfyUI
echo "Répertoire de travail: $(pwd)"
echo "Contenu du répertoire:"
ls -la

if [ -d "venv" ]; then
    echo "--- Suppression de l'environnement virtuel (venv) existant ---"
    rm -rf venv
    echo "✓ venv supprimé."
fi

echo "--- Création de l'environnement virtuel (venv) ---"
python3 -m venv venv
echo "✓ venv créé."

echo "--- Activation de venv ---"
source venv/bin/activate
echo "✓ venv activé."

echo "--- Installation des dépendances Python ---"
pip install -r requirements.txt
echo "✓ Dépendances Python installées."

echo "--- Démarrage de ComfyUI ---"
python main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention

echo "=== Fin du script de débogage ComfyUI ==="