#!/bin/bash
# Fichier: run_app.sh
# Description: Lance l'application Flask pour les utilisateurs macOS/Linux.

# --- Configuration ---
set -e

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)
PROJECT_ROOT=$(dirname "$SCRIPT_DIR")

echo "Racine du projet: $PROJECT_ROOT"

# Charger les variables d'environnement
if [ -f "$PROJECT_ROOT/.env" ]; then
    export $(grep -v '^#' "$PROJECT_ROOT/.env" | xargs)
else
    echo "ERREUR: Le fichier .env est introuvable."
    exit 1
fi

VENV_PYTHON=$VENV_PYTHON_PATH
echo "Utilisation de l'environnement Python : $VENV_PYTHON"

# --- Vérification ---
if [ ! -f "$VENV_PYTHON" ]; then
    echo "ERREUR: L'exécutable Python du venv n'a pas été trouvé à l'emplacement spécifié : $VENV_PYTHON"
    exit 1
fi

# --- Préparation de l'environnement ---
export PYTHONPATH="$PROJECT_ROOT:$PYTHONPATH"
echo "PYTHONPATH mis à jour."

# Se positionner à la racine du projet
cd "$PROJECT_ROOT"

# --- Lancement de l'application ---
echo "Lancement du serveur Flask..."
echo "Vous pourrez accéder à l'application sur http://127.0.0.1:5000"
echo "(Utilisez Ctrl+C dans le terminal pour arrêter le serveur)"

$VENV_PYTHON main.py