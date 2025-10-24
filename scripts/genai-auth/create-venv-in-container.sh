#!/bin/bash
# Script de création du venv Python 3.10 dans le container ComfyUI-Qwen
# Version: 1.0
# Date: 2025-10-24

set -e

echo "=== Installation des dépendances système ==="
apt-get update -qq
apt-get install -y -qq python3 python3-pip python3-venv

echo "=== Création du venv ==="
cd /workspace/ComfyUI
python3 -m venv venv

echo "=== Activation du venv ==="
source venv/bin/activate

echo "=== Mise à jour pip ==="
pip install --upgrade pip

echo "=== Installation des requirements ==="
pip install -r requirements.txt

echo "=== Vérification finale ==="
python --version
echo "VENV_CREATION_SUCCESS"