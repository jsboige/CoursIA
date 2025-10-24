#!/bin/bash
#
# .SYNOPSIS
#   Installe le custom node ComfyUI-Login dans le workspace persistant de ComfyUI sur l'hôte.
#
# .DESCRIPTION
#   Ce script automatise l'installation du custom node ComfyUI-Login depuis son repository GitHub.
#   CRITIQUE: Ce script installe le node sur le SYSTÈME DE FICHIERS HÔTE et non dans le conteneur
#   pour garantir la PERSISTANCE des données. L'ancienne méthode d'installation via 'docker exec'
#   entraînait une perte du node à chaque redémarrage du conteneur.
#   Le script clone ou met à jour le repository et installe les dépendances Python.
#
# .PARAMETER COMFYUI_WORKSPACE_PATH
#   Chemin d'accès complet au répertoire racine de ComfyUI sur la machine hôte.
#   Ce répertoire doit contenir le sous-répertoire 'custom_nodes'.
#   Ce paramètre est obligatoire.
#
# .EXAMPLE
#   # Installer en spécifiant le chemin du workspace
#   ./install-comfyui-login.sh "/path/to/your/ComfyUI"
#
# .EXAMPLE
#   # Utiliser une variable d'environnement
#   export COMFYUI_WORKSPACE_PATH="/path/to/your/ComfyUI"
#   ./install-comfyui-login.sh
#
# .NOTES
#   - Le script nécessite que Git soit installé sur la machine hôte.
#   - L'utilisateur doit avoir les permissions d'écriture dans le répertoire du workspace.
#   - Le script utilise 'set -e' pour s'arrêter immédiatement en cas d'erreur.
#   - Corrigé le 2025-10-22 pour résoudre un bug critique de persistance.
#

set -euo pipefail

# --- Configuration ---
REPO_URL="https://github.com/liusida/ComfyUI-Login.git"
NODE_DIR_NAME="ComfyUI-Login"
LOG_PREFIX="[INSTALL-LOGIN-HOST]"

# --- Fonctions ---

# Affiche un message de log formaté
log() {
    echo "$(date +'%Y-%m-%d %H:%M:%S') - $LOG_PREFIX $1"
}

# Installe ou met à jour le custom node sur le système de fichiers hôte
install_on_host() {
    local workspace_path="$1"
    
    # Valider que le chemin du workspace est un répertoire valide
    log "Vérification du chemin du workspace: '$workspace_path'..."
    if [ ! -d "$workspace_path" ]; then
        log "❌ ERREUR: Le chemin COMFYUI_WORKSPACE_PATH ('$workspace_path') n'est pas un répertoire valide."
        exit 1
    fi
    log "✅ Le chemin du workspace est valide."

    local custom_nodes_dir="${workspace_path}/custom_nodes"
    # S'assurer que le répertoire custom_nodes existe
    if [ ! -d "$custom_nodes_dir" ]; then
        log "ℹ️ Le répertoire 'custom_nodes' n'existe pas dans le workspace. Création de '$custom_nodes_dir'..."
        mkdir -p "$custom_nodes_dir"
        log "✅ Répertoire 'custom_nodes' créé."
    fi

    local node_path="${custom_nodes_dir}/${NODE_DIR_NAME}"

    log "--- Début de l'installation sur l'hôte ---"

    # Vérifie si le répertoire du node existe déjà pour cloner ou mettre à jour
    if [ -d "$node_path" ]; then
        log "ℹ️ Le répertoire '$node_path' existe déjà. Tentative de mise à jour via 'git pull'..."
        (cd "$node_path" && git pull)
    else
        log "ℹ️ Le répertoire '$node_path' n'existe pas. Clonage du repository..."
        git clone "$REPO_URL" "$node_path"
    fi
    log "✅ Repository cloné/mis à jour avec succès dans '$node_path'."

    # Installe les dépendances Python
    local requirements_path="${node_path}/requirements.txt"
    if [ -f "$requirements_path" ]; then
        log "ℹ️ Fichier 'requirements.txt' trouvé. Installation des dépendances via pip..."
        # Il est attendu que l'environnement Python approprié soit activé
        pip install --no-cache-dir -r "$requirements_path"
        log "✅ Dépendances Python installées."
    else
        log "⚠️ AVERTISSEMENT: Fichier 'requirements.txt' non trouvé. Aucune dépendance installée."
    fi

    log "--- ✅ Installation sur l'hôte terminée avec succès ---"
}

# --- Script Principal ---

# Le chemin du workspace peut être passé en argument ou via une variable d'environnement
COMFYUI_WORKSPACE_PATH="${1:-${COMFYUI_WORKSPACE_PATH:-}}"

# Vérifie que le chemin du workspace a été fourni
if [ -z "$COMFYUI_WORKSPACE_PATH" ]; then
    log "❌ ERREUR: Le chemin du workspace ComfyUI n'a pas été fourni."
    echo "Usage: $0 <COMFYUI_WORKSPACE_PATH>"
    echo "Vous pouvez aussi définir la variable d'environnement COMFYUI_WORKSPACE_PATH."
    exit 1
fi

log "Démarrage du script d'installation ComfyUI-Login pour une installation persistante."
log "Workspace ComfyUI cible: $COMFYUI_WORKSPACE_PATH"

# Installation sur l'hôte
install_on_host "$COMFYUI_WORKSPACE_PATH"

log "🎉 Opération terminée."
log "Veuillez redémarrer les services ComfyUI pour que les changements prennent effet."
echo
echo "Rappel: Cette installation a été effectuée sur la machine hôte pour garantir la persistance."
echo

exit 0