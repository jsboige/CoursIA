#!/bin/bash
# Script de setup complet et test ComfyUI-Qwen
# Version: 1.0
# Date: 2025-10-24

set -e

WSL_DISTRO="Ubuntu"
COMFYUI_WORKSPACE="/home/jesse/SD/workspace/comfyui-qwen"
CONTAINER_NAME="comfyui-qwen"

echo "=== SETUP ET TEST COMFYUI-QWEN AVEC AUTHENTIFICATION ==="
echo "Date: $(date '+%Y-%m-%d %H:%M:%S')"

# Étape 1: Arrêt du container
echo ""
echo "[1/5] Arrêt du container actuel..."
cd "$COMFYUI_WORKSPACE"
docker-compose down
echo "✓ Container arrêté"

# Étape 2: Suppression de l'ancien venv
echo ""
echo "[2/5] Suppression de l'ancien venv..."
rm -rf "$COMFYUI_WORKSPACE/ComfyUI/venv"
echo "✓ Ancien venv supprimé"

# Étape 3: Création du venv Python 3.10 DANS le container
echo ""
echo "[3/5] Création du venv Python 3.10 dans le container..."
echo "  ⚠ Cette étape peut prendre 2-5 minutes"

cd "$COMFYUI_WORKSPACE"
docker-compose run --rm "$CONTAINER_NAME" bash -c "
    set -e &&
    echo '=== Installation dépendances système ===' &&
    apt-get update -qq &&
    apt-get install -y python3 python3-pip python3-venv &&
    apt-get clean &&
    rm -rf /var/lib/apt/lists/* &&
    cd /workspace/ComfyUI &&
    echo '=== Création venv ===' &&
    python3 -m venv venv &&
    echo '=== Activation venv ===' &&
    source venv/bin/activate &&
    echo '=== Mise à jour pip ===' &&
    pip install --upgrade pip &&
    echo '=== Installation requirements ===' &&
    pip install -r requirements.txt &&
    echo '=== Vérification ===' &&
    python --version &&
    echo 'VENV_CREATION_SUCCESS'
"

echo "✓ Venv Python 3.10 créé avec succès"

# Étape 4: Redémarrage du container
echo ""
echo "[4/5] Redémarrage du container..."
cd "$COMFYUI_WORKSPACE"
docker-compose up -d
echo "✓ Container redémarré"

# Étape 5: Vérification
echo ""
echo "[5/5] Vérification du démarrage (attente 30s)..."
sleep 30

LOGS=$(docker logs --tail 50 "$CONTAINER_NAME" 2>&1)

echo ""
echo "Résultats de vérification:"

if echo "$LOGS" | grep -q "Python.*3\.10"; then
    echo "✓ Python 3.10"
else
    echo "✗ Python 3.10"
fi

if echo "$LOGS" | grep -q "Venv activated\|venv.*activated"; then
    echo "✓ Venv activé"
else
    echo "✗ Venv activé"
fi

if echo "$LOGS" | grep -q "ComfyUI-Login"; then
    echo "✓ ComfyUI-Login"
else
    echo "✗ ComfyUI-Login"
fi

if ! echo "$LOGS" | grep -qE "ERROR|ModuleNotFoundError"; then
    echo "✓ Pas d'erreurs critiques"
else
    echo "✗ Erreurs détectées"
fi

echo ""
echo "=== SYNTHÈSE ==="
if echo "$LOGS" | grep -q "Python.*3\.10" && \
   echo "$LOGS" | grep -q "Venv activated\|venv.*activated" && \
   ! echo "$LOGS" | grep -qE "ERROR|ModuleNotFoundError"; then
    echo "✓ SETUP RÉUSSI"
    exit 0
else
    echo "⚠ SETUP PARTIEL - Consulter les logs"
    exit 1
fi