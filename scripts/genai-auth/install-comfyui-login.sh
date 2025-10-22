#!/bin/bash
#
# .SYNOPSIS
#   Installe le custom node ComfyUI-Login dans un ou plusieurs conteneurs Docker ComfyUI.
#
# .DESCRIPTION
#   Ce script automatise l'installation du custom node ComfyUI-Login depuis son repository GitHub.
#   Il clone le repository, installe les dépendances Python nécessaires via pip, et s'assure
#   que le node est correctement placé dans le répertoire 'custom_nodes' du conteneur cible.
#   Le script est conçu pour être idempotent : si le node est déjà installé, il le met à jour.
#
# .PARAMETER ContainerNames
#   Un ou plusieurs noms de conteneurs Docker dans lesquels installer le custom node.
#   Ce paramètre est obligatoire.
#
# .EXAMPLE
#   # Installer dans un seul conteneur
#   ./install-comfyui-login.sh comfyui-qwen
#
# .EXAMPLE
#   # Installer dans plusieurs conteneurs simultanément
#   ./install-comfyui-login.sh comfyui-qwen comfyui-forge
#
# .NOTES
#   - Le script nécessite que Docker soit installé et que l'utilisateur ait les permissions
#     nécessaires pour exécuter des commandes `docker exec`.
#   - Les conteneurs cibles doivent être en cours d'exécution.
#   - Le script utilise 'set -e' pour s'arrêter immédiatement en cas d'erreur.
#   - Créé lors de la reconstruction post-incident (2025-10-22).
#

set -euo pipefail

# --- Configuration ---
REPO_URL="https://github.com/11cafe/ComfyUI-Login.git"
CUSTOM_NODES_DIR="/app/custom_nodes"
NODE_DIR_NAME="ComfyUI-Login"
LOG_PREFIX="[INSTALL-LOGIN]"

# --- Fonctions ---

# Affiche un message de log formaté
log() {
    echo "$(date +'%Y-%m-%d %H:%M:%S') - $LOG_PREFIX $1"
}

# Valide que les conteneurs cibles existent et tournent
validate_containers() {
    for container in "$@"; do
        log "Vérification du conteneur '$container'..."
        if ! docker ps --filter "name=^${container}$" --format "{{.Names}}" | grep -q "^${container}$"; then
            log "❌ ERREUR: Le conteneur '$container' n'est pas en cours d'exécution ou n'existe pas."
            exit 1
        fi
        log "✅ Conteneur '$container' trouvé et en cours d'exécution."
    done
}

# Installe ou met à jour le custom node dans un conteneur donné
install_in_container() {
    local container_name="$1"
    local node_path="${CUSTOM_NODES_DIR}/${NODE_DIR_NAME}"

    log "--- Début de l'installation pour le conteneur '$container_name' ---"

    # Vérifie si le répertoire du node existe déjà
    if docker exec "$container_name" test -d "$node_path"; then
        log "ℹ️ Le répertoire '$node_path' existe déjà. Tentative de mise à jour..."
        docker exec "$container_name" bash -c "cd '$node_path' && git pull"
    else
        log "ℹ️ Le répertoire '$node_path' n'existe pas. Clonage du repository..."
        docker exec "$container_name" git clone "$REPO_URL" "$node_path"
    fi
    log "✅ Repository cloné/mis à jour avec succès."

    # Installe les dépendances Python
    local requirements_path="${node_path}/requirements.txt"
    if docker exec "$container_name" test -f "$requirements_path"; then
        log "ℹ️ Fichier 'requirements.txt' trouvé. Installation des dépendances..."
        docker exec "$container_name" pip install --no-cache-dir -r "$requirements_path"
        log "✅ Dépendances Python installées."
    else
        log "⚠️ AVERTISSEMENT: Fichier 'requirements.txt' non trouvé dans '$node_path'. Aucune dépendance installée."
    fi

    log "--- ✅ Installation terminée avec succès pour '$container_name' ---"
}

# --- Script Principal ---

# Vérifie les arguments
if [ "$#" -eq 0 ]; then
    log "❌ ERREUR: Aucun nom de conteneur fourni."
    echo "Usage: $0 <container_name_1> [container_name_2] ..."
    exit 1
fi

log "Démarrage du script d'installation ComfyUI-Login..."
log "Conteneurs cibles: $@"

# Validation des prérequis
validate_containers "$@"

# Boucle sur chaque conteneur pour l'installation
for container in "$@"; do
    install_in_container "$container"
done

log "🎉 Opération terminée. Tous les conteneurs ont été traités."
log "Veuillez redémarrer les services ComfyUI pour que les changements prennent effet."
echo
echo "Exemple de commande de redémarrage:"
echo "  docker-compose restart $@"
echo

exit 0