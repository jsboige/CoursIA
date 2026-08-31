#!/usr/bin/env bash
# Script pour mettre a jour l'environnement virtuel Python avec les
# dependances de requirements.txt — jumeau Linux/macOS de update_venv.ps1

set -euo pipefail

# Fonction pour charger les variables d'environnement depuis un fichier .env
load_env_variables() {
    local path="${1:-.env}"
    if [ -f "$path" ]; then
        while IFS= read -r line || [ -n "$line" ]; do
            line="$(echo "$line" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')"
            case "$line" in
                ""|\#*) continue ;;
            esac
            key="${line%%=*}"
            value="${line#*=}"
            if [ "$key" != "$line" ]; then
                key="$(echo "$key" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')"
                value="$(echo "$value" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | sed 's/^"//;s/"$//')"
                export "$key=$value"
            fi
        done < "$path"
    fi
}

# Definir le chemin de base du projet
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(dirname "$script_dir")"
echo "Racine du projet: $project_root"

# Charger les variables du fichier .env
load_env_variables "$project_root/.env"

# Chemin vers l'environnement virtuel Python (lu depuis .env)
venv_path="${VENV_PYTHON_PATH:-}"
requirements_path="$project_root/requirements.txt"

echo "Environnement virtuel: $venv_path"
echo "Fichier de dependances: $requirements_path"

# Verifier si les chemins existent
if [ -z "$venv_path" ] || [ ! -x "$venv_path" ]; then
    echo "ERREUR : l'executable Python de l'environnement virtuel n'a pas ete trouve : $venv_path" >&2
    exit 1
fi
if [ ! -f "$requirements_path" ]; then
    echo "ERREUR : le fichier requirements.txt n'a pas ete trouve : $requirements_path" >&2
    exit 1
fi

# Executer la mise a jour des dependances
echo "Mise a jour des dependances avec pip..."
"$venv_path" -m pip install -r "$requirements_path" --upgrade

echo "Mise a jour terminee."
