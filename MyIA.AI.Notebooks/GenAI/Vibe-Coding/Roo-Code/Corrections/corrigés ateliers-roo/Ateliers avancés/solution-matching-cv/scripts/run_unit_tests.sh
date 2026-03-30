#!/bin/bash
# Fichier: run_unit_tests.sh
# Description: Lance les tests unitaires pour les utilisateurs macOS/Linux.

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
echo "Environnement virtuel: $VENV_PYTHON"

# --- Vérification ---
if [ ! -f "$VENV_PYTHON" ]; then
    echo "ERREUR: L'interpréteur Python du venv n'a pas été trouvé : $VENV_PYTHON"
    exit 1
fi

# --- Préparation de l'environnement ---
export PYTHONPATH="$PROJECT_ROOT:$PYTHONPATH"
echo "PYTHONPATH mis à jour."

export ENABLE_PERFORMANCE_LOGS="True"
echo "Logs de performance activés."

cd "$PROJECT_ROOT"

# --- Exécution des tests ---
echo "Lancement des tests unitaires..."
echo "---------------------------------------------------------"

TEST_DIR="$PROJECT_ROOT/tests/unit"
$VENV_PYTHON -m pytest "$TEST_DIR" -v

echo "---------------------------------------------------------"
echo "Exécution des tests unitaires terminée."