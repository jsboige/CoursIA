#!/bin/bash
# install-missing-dependencies.sh - Installation des dépendances ComfyUI-Login dans le venv existant

set -e

COMFYUI_PATH="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"

echo "=== INSTALLATION DÉPENDANCES COMFYUI-LOGIN ==="
echo "Date: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

echo "[1/3] Vérification de l'existence du venv..."
if [ ! -d "$COMFYUI_PATH/venv" ]; then
    echo "✗ ERREUR: venv manquant à $COMFYUI_PATH/venv"
    exit 1
fi
echo "✓ Venv trouvé"

echo ""
echo "[2/3] Activation du venv et installation des dépendances..."
cd "$COMFYUI_PATH"
source venv/bin/activate

echo "=== Installation de pycryptodome, bcrypt, aiohttp-session ==="
pip install --quiet pycryptodome bcrypt aiohttp-session

echo ""
echo "[3/3] Vérification des installations..."
python -c 'from Crypto.Cipher import AES; print("✓ pycryptodome OK")'
python -c 'import bcrypt; print("✓ bcrypt OK")'
python -c 'import aiohttp_session; print("✓ aiohttp_session OK")'

echo ""
echo "=== INSTALLATION COMPLÈTE ==="
echo "Toutes les dépendances sont installées avec succès"