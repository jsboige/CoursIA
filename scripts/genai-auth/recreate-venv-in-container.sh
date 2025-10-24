#!/bin/bash
# recreate-venv-in-container.sh - Recréation complète du venv avec activation automatique au démarrage

set -e

COMFYUI_WORKSPACE="/home/jesse/SD/workspace/comfyui-qwen"
CONTAINER_NAME="comfyui-qwen"

echo "=== RECRÉATION VENV AVEC ACTIVATION AUTOMATIQUE ==="
echo "Date: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

echo "[1/5] Arrêt du container..."
cd "$COMFYUI_WORKSPACE"
docker-compose down

echo ""
echo "[2/5] Suppression de l'ancien venv..."
rm -rf "$COMFYUI_WORKSPACE/ComfyUI/venv"

echo ""
echo "[3/5] Création du nouveau venv Python 3.10 avec TOUTES les dépendances..."
docker-compose run --rm "$CONTAINER_NAME" bash -c "
    set -e &&
    apt-get update -qq &&
    apt-get install -y python3 python3-pip python3-venv &&
    cd /workspace/ComfyUI &&
    python3 -m venv venv &&
    source venv/bin/activate &&
    pip install --upgrade pip &&
    pip install -r requirements.txt &&
    pip install pycryptodome bcrypt aiohttp-session &&
    echo '=== Vérification finale ===' &&
    python -c 'from Crypto.Cipher import AES; print(\"✓ pycryptodome OK\")' &&
    python -c 'import bcrypt; print(\"✓ bcrypt OK\")' &&
    python -c 'import aiohttp_session; print(\"✓ aiohttp_session OK\")' &&
    echo 'VENV_COMPLETE'
"

if [ $? -eq 0 ]; then
    echo "✓ Venv créé avec succès"
else
    echo "✗ ERREUR lors de la création du venv"
    exit 1
fi

echo ""
echo "[4/5] Modification du docker-compose.yml pour activation automatique du venv..."

# Backup du docker-compose.yml
cp "$COMFYUI_WORKSPACE/docker-compose.yml" "$COMFYUI_WORKSPACE/docker-compose.yml.backup-$(date +%Y%m%d-%H%M%S)"

# Vérifier si l'activation du venv est déjà dans le docker-compose.yml
if grep -q "source /workspace/ComfyUI/venv/bin/activate" "$COMFYUI_WORKSPACE/docker-compose.yml"; then
    echo "✓ Activation du venv déjà configurée dans docker-compose.yml"
else
    echo "⚠️ Activation du venv NON configurée - MODIFICATION MANUELLE REQUISE"
    echo ""
    echo "INSTRUCTIONS MANUELLES :"
    echo "1. Ouvrir: $COMFYUI_WORKSPACE/docker-compose.yml"
    echo "2. Modifier le 'command:' pour activer le venv avant le démarrage :"
    echo ""
    echo "   command: >"
    echo "     bash -c \""
    echo "     source /workspace/ComfyUI/venv/bin/activate &&"
    echo "     python main.py --listen 0.0.0.0 --port 8188"
    echo "     \""
    echo ""
    echo "3. Sauvegarder et relancer ce script"
    echo ""
    exit 1
fi

echo ""
echo "[5/5] Démarrage du container avec venv activé..."
cd "$COMFYUI_WORKSPACE"
docker-compose up -d

echo ""
echo "Attente du démarrage complet (45 secondes)..."
sleep 45

echo ""
echo "=== VÉRIFICATION FINALE ==="
docker logs --tail 100 "$CONTAINER_NAME" 2>&1 | grep -i "comfyui-login" || echo "⚠️ Pas de trace de ComfyUI-Login dans les logs"
docker logs --tail 100 "$CONTAINER_NAME" 2>&1 | grep -i "ModuleNotFoundError\|No module named" && echo "✗ Erreurs de dépendances détectées" || echo "✓ Aucune erreur de dépendances"

echo ""
echo "=== FIN DE LA RECRÉATION ==="
echo "Pour voir les logs complets: docker logs $CONTAINER_NAME"