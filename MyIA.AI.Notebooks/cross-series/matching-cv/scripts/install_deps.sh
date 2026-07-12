#!/bin/bash
# Fichier: install_deps.sh
# Description: Installe les dépendances Python pour les utilisateurs macOS/Linux.

# --- Configuration ---
set -e # Arrête le script si une commande échoue

# Déterminer le répertoire racine du projet
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)
PROJECT_ROOT=$(dirname "$SCRIPT_DIR")

echo "Racine du projet: $PROJECT_ROOT"

# Charger les variables d'environnement depuis le fichier .env
if [ -f "$PROJECT_ROOT/.env" ]; then
    export $(grep -v '^#' "$PROJECT_ROOT/.env" | xargs)
else
    echo "ERREUR: Le fichier .env est introuvable à la racine du projet."
    exit 1
fi

# Chemin vers l'exécutable Python de l'environnement virtuel (lu depuis .env)
VENV_PYTHON=$VENV_PYTHON_PATH
echo "Environnement virtuel cible: $VENV_PYTHON"

# Chemin vers le fichier requirements.txt
REQUIREMENTS_FILE="$PROJECT_ROOT/requirements.txt"

# --- Vérifications ---
if [ ! -f "$VENV_PYTHON" ]; then
    echo "ERREUR: L'interpréteur Python du venv n'a pas été trouvé à l'emplacement '$VENV_PYTHON'."
    echo "Veuillez vérifier la variable VENV_PYTHON_PATH dans votre fichier .env."
    exit 1
fi

if [ ! -f "$REQUIREMENTS_FILE" ]; then
    echo "ERREUR: Le fichier '$REQUIREMENTS_FILE' est introuvable."
    exit 1
fi

# --- Installation des dépendances ---
echo "Installation des dépendances depuis '$REQUIREMENTS_FILE'..."
echo "---------------------------------------------------------"

$VENV_PYTHON -m pip install -r "$REQUIREMENTS_FILE"

# Installation des navigateurs pour Playwright
echo "Installation des navigateurs pour Playwright..."
$VENV_PYTHON -m playwright install

echo "---------------------------------------------------------"
echo "Installation terminée."