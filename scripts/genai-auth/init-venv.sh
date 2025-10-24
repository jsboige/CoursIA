#!/bin/bash
# init-venv.sh - Initialisation complète du venv Python 3.10 avec toutes les dépendances

set -e

echo "=== INITIALISATION VENV PYTHON 3.10 ==="
echo "Date: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

echo "Installation des paquets système..."
apt-get update -qq
apt-get install -y python3 python3-pip python3-venv

echo ""
echo "Création du venv..."
cd /workspace/ComfyUI
python3 -m venv venv

echo ""
echo "Activation du venv..."
source venv/bin/activate

echo ""
echo "Mise à jour de pip..."
pip install --upgrade pip

echo ""
echo "Installation des dépendances ComfyUI..."
pip install -r requirements.txt

echo ""
echo "Installation des dépendances ComfyUI-Login..."
pip install cryptography pycryptodome bcrypt aiohttp-session

echo ""
echo "=== VÉRIFICATION DES INSTALLATIONS ==="
python -c 'from Crypto.Cipher import AES; print("✓ pycryptodome OK")'
python -c 'import bcrypt; print("✓ bcrypt OK")'
python -c 'import aiohttp_session; print("✓ aiohttp_session OK")'

echo ""
echo "VENV_INIT_COMPLETE"