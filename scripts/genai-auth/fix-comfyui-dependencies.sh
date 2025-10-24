#!/bin/bash
# fix-comfyui-dependencies.sh - Installation des dépendances ComfyUI-Login dans le venv Python 3.10
set -e

COMFYUI_WORKSPACE="/home/jesse/SD/workspace/comfyui-qwen"
CONTAINER_NAME="comfyui-qwen"

echo "=== INSTALLATION DÉPENDANCES COMFYUI-LOGIN ==="
echo "Date: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

echo "[1/3] Installation pycryptodome et bcrypt dans le container..."
cd "$COMFYUI_WORKSPACE"
docker-compose exec -T "$CONTAINER_NAME" bash -c "
    set -e &&
    source /workspace/ComfyUI/venv/bin/activate &&
    echo '=== Installation dépendances ===' &&
    pip install --quiet pycryptodome bcrypt &&
    echo '=== Vérification ===' &&
    pip list | grep -E '(pycryptodome|bcrypt)' &&
    python -c 'from Crypto.Cipher import AES; print(\"✓ pycryptodome OK\")' &&
    python -c 'import bcrypt; print(\"✓ bcrypt OK\")' &&
    echo 'DEPENDENCIES_OK'
"

if [ $? -eq 0 ]; then
    echo "✓ Dépendances installées avec succès"
else
    echo "✗ Échec installation dépendances"
    exit 1
fi

echo ""
echo "[2/3] Redémarrage du container pour appliquer les changements..."
cd "$COMFYUI_WORKSPACE"
docker-compose restart "$CONTAINER_NAME"

if [ $? -eq 0 ]; then
    echo "✓ Container redémarré"
else
    echo "✗ Échec redémarrage"
    exit 1
fi

echo ""
echo "[3/3] Vérification du chargement de ComfyUI-Login (attente 30s)..."
sleep 30

echo ""
echo "Vérification logs (recherche ComfyUI-Login):"
docker logs "$CONTAINER_NAME" 2>&1 | tail -100 | grep -E "ComfyUI-Login|Import.*Login|IMPORT.*Login" || echo "⚠ Pas de mention explicite de ComfyUI-Login"

echo ""
echo "Vérification logs (recherche erreurs Crypto/ModuleNotFoundError):"
if docker logs "$CONTAINER_NAME" 2>&1 | tail -100 | grep -E "ModuleNotFoundError.*Crypto|Cannot import.*ComfyUI-Login"; then
    echo "✗ Erreurs détectées - ComfyUI-Login non chargé"
    exit 1
else
    echo "✓ Aucune erreur Crypto détectée"
fi

echo ""
echo "=== SUCCÈS - DÉPENDANCES INSTALLÉES ET CONTAINER OPÉRATIONNEL ==="