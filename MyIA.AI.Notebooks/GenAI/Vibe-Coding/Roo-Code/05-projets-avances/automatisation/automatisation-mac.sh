#!/bin/bash
#
# Script d'automatisation avancé pour la gestion de projets et le traitement de données
# Version pour macOS/Linux
#
# Auteur: Roo
# Version: 1.0.0
# Date de création: 19/05/2025
#
# Description:
# Ce script Bash démontre des techniques avancées d'automatisation avec Roo:
# - Traitement par lots de fichiers (analyse, transformation, validation)
# - Intégration avec des APIs externes
# - Génération de rapports et visualisations
# - Gestion avancée des erreurs et reprise
# - Logging structuré et notifications
# - Parallélisation des tâches
#
# Usage: ./automatisation-mac.sh --project-path /chemin/vers/projet --output-path /chemin/vers/sortie [options]
#
# Options:
#   --project-path PATH    Chemin vers le répertoire du projet à traiter (obligatoire)
#   --output-path PATH     Chemin où les résultats seront générés (obligatoire)
#   --api-key KEY          Clé API pour les services externes (optionnel)
#   --log-level LEVEL      Niveau de détail des logs (verbose, info, warning, error) (défaut: info)
#   --max-threads NUM      Nombre maximum de threads parallèles à utiliser (défaut: 4)
#   --send-notifications   Active l'envoi de notifications par email
#   --help                 Affiche cette aide et quitte

#######################################
# Configuration et initialisation
#######################################

# Couleurs pour les logs
RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
GRAY='\033[0;37m'
NC='\033[0m' # No Color

# Valeurs par défaut
PROJECT_PATH=""
OUTPUT_PATH=""
API_KEY=${API_KEY:-""}
LOG_LEVEL="info"
MAX_THREADS=4
SEND_NOTIFICATIONS=false
TEMP_PATH=""
LOG_PATH=""
REPORT_PATH=""
API_ENDPOINT="https://api.example.com/v1"
MAX_RETRIES=3
RETRY_DELAY=5
START_TIME=$(date +%s)
PROCESSED_FILES=0
ERROR_COUNT=0
WARNING_COUNT=0
LOG_FILE=""

# Fonction d'affichage de l'aide
show_help() {
    echo "Usage: $0 --project-path /chemin/vers/projet --output-path /chemin/vers/sortie [options]"
    echo ""
    echo "Options:"
    echo "  --project-path PATH    Chemin vers le répertoire du projet à traiter (obligatoire)"
    echo "  --output-path PATH     Chemin où les résultats seront générés (obligatoire)"
    echo "  --api-key KEY          Clé API pour les services externes (optionnel)"
    echo "  --log-level LEVEL      Niveau de détail des logs (verbose, info, warning, error) (défaut: info)"
    echo "  --max-threads NUM      Nombre maximum de threads parallèles à utiliser (défaut: 4)"
    echo "  --send-notifications   Active l'envoi de notifications par email"
    echo "  --help                 Affiche cette aide et quitte"
    exit 0
}

# Parsing des arguments
while [[ $# -gt 0 ]]; do
    key="$1"
    case $key in
        --project-path)
            PROJECT_PATH="$2"
            shift 2
            ;;
        --output-path)
            OUTPUT_PATH="$2"
            shift 2
            ;;
        --api-key)
            API_KEY="$2"
            shift 2
            ;;
        --log-level)
            LOG_LEVEL="$2"
            shift 2
            ;;
        --max-threads)
            MAX_THREADS="$2"
            shift 2
            ;;
# Création des répertoires nécessaires
initialize_environment() {
    local paths=("$OUTPUT_PATH" "$TEMP_PATH" "$LOG_PATH" "$REPORT_PATH")
    
    for path in "${paths[@]}"; do
        if [ ! -d "$path" ]; then
            mkdir -p "$path" || { echo "Erreur lors de la création du répertoire $path"; exit 1; }
            write_log "Répertoire créé: $path" "verbose"
        fi
    done
    
    # Initialisation du fichier de log
    local log_filename="AutomationLog_$(date +%Y%m%d_%H%M%S).log"
    LOG_FILE="$LOG_PATH/$log_filename"
    touch "$LOG_FILE" || { echo "Erreur lors de la création du fichier de log"; exit 1; }
    
    write_log "=== Démarrage de l'automatisation ===" "info"
    write_log "Projet: $PROJECT_PATH" "info"
    write_log "Sortie: $OUTPUT_PATH" "info"
    write_log "Threads: $MAX_THREADS" "info"
}

#######################################
# Logging et gestion des erreurs
#######################################

# Fonction de logging avancée
write_log() {
    local message="$1"
    local level="${2:-info}"
    local no_console="${3:-false}"
    
    # Vérification du niveau de log
    local log_levels=("verbose" "info" "warning" "error")
    local current_level_index=0
    local requested_level_index=0
    
    for i in "${!log_levels[@]}"; do
        if [ "${log_levels[$i]}" = "$LOG_LEVEL" ]; then
            current_level_index=$i
        fi
        if [ "${log_levels[$i]}" = "$level" ]; then
            requested_level_index=$i
        fi
    done
    
    if [ $requested_level_index -lt $current_level_index ]; then
        return
    fi
    
    # Formatage du message
    local timestamp=$(date +"%Y-%m-%d %H:%M:%S")
    local log_entry="[$timestamp] [$level] $message"
    
    # Écriture dans le fichier de log
    if [ -n "$LOG_FILE" ]; then
        echo "$log_entry" >> "$LOG_FILE"
    fi
    
    # Affichage dans la console
    if [ "$no_console" != "true" ]; then
        case $level in
            "verbose")
                echo -e "${GRAY}$log_entry${NC}"
                ;;
            "info")
                echo -e "$log_entry"
                ;;
            "warning")
                echo -e "${YELLOW}$log_entry${NC}"
                ((WARNING_COUNT++))
                ;;
            "error")
                echo -e "${RED}$log_entry${NC}"
                ((ERROR_COUNT++))
                ;;
            *)
                echo -e "$log_entry"
                ;;
        esac
    fi
}

# Fonction de gestion des erreurs avec retry
invoke_with_retry() {
    local cmd="$1"
    local operation="${2:-Opération}"
    local max_retries="${3:-$MAX_RETRIES}"
    local retry_delay="${4:-$RETRY_DELAY}"
    
    local attempt=1
    local success=false
    local result=""
    local last_error=""
    
    while [ "$success" = false ] && [ $attempt -le $max_retries ]; do
        if [ $attempt -gt 1 ]; then
            write_log "Tentative $attempt/$max_retries pour: $operation" "warning"
            sleep $retry_delay
        fi
#######################################
# Traitement de fichiers
#######################################

# Fonction pour obtenir tous les fichiers à traiter
get_files_to_process() {
    local path="$1"
    local extensions=(".txt" ".csv" ".json" ".xml" ".md" ".log")
    local files=()
    
    # Construction de la commande find avec les extensions
    local find_cmd="find \"$path\" -type f"
    local extension_pattern=""
    
    for ext in "${extensions[@]}"; do
        if [ -z "$extension_pattern" ]; then
            extension_pattern="-name \"*$ext\""
        else
            extension_pattern="$extension_pattern -o -name \"*$ext\""
        fi
    done
    
    find_cmd="$find_cmd \\( $extension_pattern \\)"
    
    # Exécution de la commande
    local result
    result=$(eval "$find_cmd" 2>&1) || {
        write_log "Erreur lors de la recherche des fichiers: $result" "error"
        return 1
    }
    
    # Comptage des fichiers
    local count=$(echo "$result" | wc -l | tr -d ' ')
    write_log "Trouvé $count fichiers à traiter" "info"
    
    echo "$result"
    return 0
}

# Fonction d'analyse de fichier
analyze_file() {
    local file="$1"
    local filename=$(basename "$file")
    local extension="${filename##*.}"
    local filesize=$(stat -f "%z" "$file" 2>/dev/null || stat -c "%s" "$file" 2>/dev/null)
    local last_modified=$(stat -f "%Sm" "$file" 2>/dev/null || stat -c "%y" "$file" 2>/dev/null)
    
    write_log "Analyse du fichier: $file" "verbose"
    
    # Initialisation du résultat
    local result=$(cat << EOF
{
    "fileName": "$filename",
    "filePath": "$file",
    "fileSize": $filesize,
    "extension": ".$extension",
    "lastModified": "$last_modified",
    "metrics": {},
    "tags": [],
    "status": "Unknown"
}
EOF
)
    
    # Analyse selon le type de fichier
    case ".$extension" in
        .txt)
            local content=$(cat "$file")
            local line_count=$(echo "$content" | wc -l | tr -d ' ')
            local word_count=$(echo "$content" | wc -w | tr -d ' ')
            
            # Mise à jour des métriques
            result=$(echo "$result" | jq --arg content "$content" \
                                        --argjson line_count "$line_count" \
                                        --argjson word_count "$word_count" \
                '.content = $content | .metrics.lineCount = $line_count | .metrics.wordCount = $word_count | .status = "Processed"')
            
            # Détection de mots-clés
            local keywords=("important" "urgent" "critique" "révision" "TODO" "FIXME" "BUG")
            local tags=()
            
            for keyword in "${keywords[@]}"; do
                if echo "$content" | grep -q "$keyword"; then
                    tags+=("$keyword")
                fi
            done
            
            if [ ${#tags[@]} -gt 0 ]; then
                local tags_json=$(printf '%s\n' "${tags[@]}" | jq -R . | jq -s .)
                result=$(echo "$result" | jq --argjson tags "$tags_json" '.tags = $tags')
            fi
            ;;
            
        .csv)
            local header_line=$(head -n 1 "$file")
            local column_count=$(echo "$header_line" | awk -F, '{print NF}')
            local row_count=$(wc -l < "$file" | tr -d ' ')
            
            # Mise à jour des métriques
            result=$(echo "$result" | jq --argjson row_count "$row_count" \
                                        --argjson column_count "$column_count" \
                '.metrics.rowCount = $row_count | .metrics.columnCount = $column_count | .status = "Processed"')
            ;;
            
        .json)
            # Vérification de la validité du JSON
            if jq empty "$file" 2>/dev/null; then
                local is_array=$(jq 'if type=="array" then 1 else 0 end' "$file")
                local object_count=1
                
                if [ "$is_array" -eq 1 ]; then
                    object_count=$(jq 'length' "$file")
                fi
                
                # Mise à jour des métriques
                result=$(echo "$result" | jq --argjson object_count "$object_count" \
                                            '.metrics.objectCount = $object_count | .status = "Processed"')
            else
                result=$(echo "$result" | jq '.status = "Error" | .errorMessage = "Invalid JSON format"')
            fi
            ;;
            
        .xml)
            # Vérification de la validité du XML
            if xmllint --noout "$file" 2>/dev/null; then
                local element_count=$(grep -o "<[^/][^>]*>" "$file" | wc -l | tr -d ' ')
                
                # Mise à jour des métriques
                result=$(echo "$result" | jq --argjson element_count "$element_count" \
                                            '.metrics.elementCount = $element_count | .status = "Processed"')
            else
                result=$(echo "$result" | jq '.status = "Error" | .errorMessage = "Invalid XML format"')
            fi
            ;;
            
        *)
            result=$(echo "$result" | jq '.status = "Skipped"')
            write_log "Type de fichier non pris en charge pour l'analyse détaillée: .$extension" "warning"
            ;;
    esac
    
    echo "$result"
    return 0
}

# Fonction de transformation de fichier
transform_file() {
    local file_analysis="$1"
    local to_upper_case="${2:-false}"
    local add_timestamp="${3:-true}"
    local add_calculated_column="${4:-true}"
    
    # Parsing du JSON d'analyse
    local file_path=$(echo "$file_analysis" | jq -r '.filePath')
    local file_name=$(echo "$file_analysis" | jq -r '.fileName')
    local extension=$(echo "$file_analysis" | jq -r '.extension')
    local status=$(echo "$file_analysis" | jq -r '.status')
    
    if [ "$status" != "Processed" ]; then
        write_log "Impossible de transformer le fichier $file_name: statut $status" "warning"
        echo "$file_analysis"
        return 0
    fi
    
    local output_file="$TEMP_PATH/transformed_$file_name"
    write_log "Transformation du fichier: $file_name" "verbose"
    
    # Transformation selon le type de fichier
    case "$extension" in
        .txt)
            local content=$(echo "$file_analysis" | jq -r '.content')
            
            # Application des transformations
            if [ "$to_upper_case" = true ]; then
                content=$(echo "$content" | tr '[:lower:]' '[:upper:]')
            fi
            
            if [ "$add_timestamp" = true ]; then
                local timestamp=$(date +"%Y-%m-%d %H:%M:%S")
                content="# Processed: $timestamp\n$content"
            fi
            
            # Écriture du fichier transformé
            echo -e "$content" > "$output_file"
            ;;
            
        .csv)
            # Pour CSV, on copie d'abord le fichier
            cp "$file_path" "$output_file"
            
            # Ajout d'une colonne calculée si demandé
            if [ "$add_calculated_column" = true ]; then
                # Cette implémentation est simplifiée
                # Dans un cas réel, vous utiliseriez awk ou un autre outil pour manipuler le CSV
                local temp_file="$TEMP_PATH/temp_$file_name"
                head -n 1 "$output_file" > "$temp_file"
                echo "$(head -n 1 "$output_file"),Total" > "$temp_file"
                tail -n +2 "$output_file" | while IFS=, read -r value1 value2 rest; do
                    if [[ "$value1" =~ ^[0-9]+$ ]] && [[ "$value2" =~ ^[0-9]+$ ]]; then
                        local total=$((value1 + value2))
#######################################
# Intégration API et services externes
#######################################

# Fonction pour appeler une API externe
invoke_api_request() {
    local endpoint="$1"
    local method="${2:-GET}"
    local body="$3"
    local use_api_key="${4:-true}"
    
    local uri="$API_ENDPOINT/$endpoint"
    local headers=(-H "Content-Type: application/json")
    
    # Ajout de la clé API si nécessaire
    if [ "$use_api_key" = true ] && [ -n "$API_KEY" ]; then
        headers+=(-H "Authorization: Bearer $API_KEY")
    fi
    
    write_log "Appel API: $method $uri" "verbose"
    
    local curl_cmd="curl -s -X $method"
    
    # Ajout des headers
    for header in "${headers[@]}"; do
        curl_cmd="$curl_cmd $header"
    done
    
    # Ajout du body pour les méthodes non-GET
    if [ -n "$body" ] && [ "$method" != "GET" ]; then
        curl_cmd="$curl_cmd -d '$body'"
    fi
    
    # Ajout de l'URL
    curl_cmd="$curl_cmd '$uri'"
    
    # Exécution avec retry
    local response
    response=$(invoke_with_retry "$curl_cmd" "Appel API $method $endpoint")
    
    echo "$response"
    return 0
}

# Fonction pour enrichir les données avec des informations externes
enrich_data() {
    local file_analysis="$1"
    
    # Parsing du JSON d'analyse
    local file_name=$(echo "$file_analysis" | jq -r '.fileName')
    local status=$(echo "$file_analysis" | jq -r '.status')
    
    if [[ "$status" != "Processed" && "$status" != "Transformed" ]]; then
        echo "$file_analysis"
        return 0
    fi
    
    write_log "Enrichissement des données pour: $file_name" "verbose"
    
    # Ajout de métadonnées supplémentaires
    local machine_name=$(hostname)
    local user_name=$(whoami)
    local environment=${ENVIRONMENT:-"Development"}
    local processed_at=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    
    local enrichment_data=$(cat << EOF
{
    "processedAt": "$processed_at",
    "machineName": "$machine_name",
    "processedBy": "$user_name",
    "environment": "$environment"
}
EOF
)
    
    # Simulation d'enrichissement avec API externe
    if [ -n "$API_KEY" ]; then
        # Simulation pour l'exemple
        enrichment_data=$(echo "$enrichment_data" | jq '. += {
            "apiClassification": "Document",
            "apiTags": ["automatisation", "exemple"],
            "apiConfidence": 0.85
        }')
    fi
    
    # Mise à jour du résultat
    local result=$(echo "$file_analysis" | jq --argjson enrichment_data "$enrichment_data" \
                                            '.enrichmentData = $enrichment_data | .status = "Enriched"')
    
    echo "$result"
    return 0
}
                        echo "$value1,$value2,$rest,$total" >> "$temp_file"
                    else
                        echo "$value1,$value2,$rest," >> "$temp_file"
                    fi
                done
                mv "$temp_file" "$output_file"
            fi
            ;;
#######################################
# Génération de rapports
#######################################

# Fonction pour générer un rapport HTML
generate_html_report() {
    local processed_files="$1"
    local output_path="$2"
    
    write_log "Génération du rapport HTML" "info"
    
    local report_date=$(date +"%Y-%m-%d %H:%M:%S")
    local end_time=$(date +%s)
    local execution_time=$((end_time - START_TIME))
    local hours=$((execution_time / 3600))
    local minutes=$(( (execution_time % 3600) / 60 ))
    local seconds=$((execution_time % 60))
    local execution_time_formatted=$(printf "%02d:%02d:%02d" $hours $minutes $seconds)
    
    # Calcul des statistiques
    local total_files=$(echo "$processed_files" | jq 'length')
    local success_count=$(echo "$processed_files" | jq '[.[] | select(.status == "Processed" or .status == "Transformed" or .status == "Enriched")] | length')
    local error_count=$(echo "$processed_files" | jq '[.[] | select(.status | contains("Error"))] | length')
    local skipped_count=$(echo "$processed_files" | jq '[.[] | select(.status == "Skipped")] | length')
    
    # Création du contenu HTML
    local html_content=$(cat << EOF
<!DOCTYPE html>
<html lang="fr">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Rapport d'automatisation - $report_date</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; color: #333; }
        h1, h2, h3 { color: #2c3e50; }
        .container { max-width: 1200px; margin: 0 auto; }
        .summary { background-color: #f8f9fa; padding: 15px; border-radius: 5px; margin-bottom: 20px; }
        .success { color: #28a745; }
        .warning { color: #ffc107; }
        .error { color: #dc3545; }
        table { width: 100%; border-collapse: collapse; margin-bottom: 20px; }
        th, td { padding: 8px; text-align: left; border-bottom: 1px solid #ddd; }
        th { background-color: #f2f2f2; }
        tr:hover { background-color: #f5f5f5; }
        .status-Processed, .status-Transformed, .status-Enriched { background-color: #d4edda; }
        .status-Skipped { background-color: #fff3cd; }
        .status-Error, .status-TransformError, .status-EnrichmentError { background-color: #f8d7da; }
        .chart-container { width: 100%; height: 300px; margin-bottom: 20px; }
    </style>
</head>
<body>
    <div class="container">
        <h1>Rapport d'automatisation</h1>
        <p>Généré le: $report_date</p>
        
        <div class="summary">
            <h2>Résumé</h2>
            <p><strong>Projet:</strong> $PROJECT_PATH</p>
            <p><strong>Durée d'exécution:</strong> $execution_time_formatted</p>
            <p><strong>Fichiers traités:</strong> $total_files</p>
            <p><strong class="success">Succès:</strong> $success_count</p>
            <p><strong class="warning">Ignorés:</strong> $skipped_count</p>
            <p><strong class="error">Erreurs:</strong> $error_count</p>
        </div>
        
        <h2>Détails des fichiers</h2>
        <table>
            <thead>
                <tr>
                    <th>Nom du fichier</th>
                    <th>Type</th>
                    <th>Taille</th>
                    <th>Statut</th>
                    <th>Tags</th>
                </tr>
            </thead>
            <tbody>
EOF
)

    # Ajout des lignes pour chaque fichier
    local files_table=""
    for i in $(seq 0 $((total_files - 1))); do
        local file=$(echo "$processed_files" | jq ".[$i]")
        local file_name=$(echo "$file" | jq -r '.fileName')
        local extension=$(echo "$file" | jq -r '.extension')
        local file_size=$(echo "$file" | jq -r '.fileSize')
        local status=$(echo "$file" | jq -r '.status')
        local tags=$(echo "$file" | jq -r '.tags | join(", ")')
        
        # Formatage de la taille
        local size_formatted=""
        if [ "$file_size" -gt 1048576 ]; then
            size_formatted=$(echo "scale=2; $file_size / 1048576" | bc)
            size_formatted="${size_formatted} MB"
        elif [ "$file_size" -gt 1024 ]; then
            size_formatted=$(echo "scale=2; $file_size / 1024" | bc)
            size_formatted="${size_formatted} KB"
        else
            size_formatted="${file_size} B"
        fi
        
        files_table+=$(cat << EOF
                <tr class="status-$status">
                    <td>$file_name</td>
                    <td>$extension</td>
                    <td>$size_formatted</td>
                    <td>$status</td>
                    <td>$tags</td>
                </tr>
EOF
)
    done
    
    # Finalisation du HTML
    html_content+="$files_table"
    html_content+=$(cat << EOF
            </tbody>
        </table>
        
        <h2>Statistiques</h2>
        <div class="chart-container">
            <!-- Ici, vous pourriez intégrer des graphiques avec une bibliothèque JavaScript comme Chart.js -->
            <p>Les graphiques détaillés seraient générés ici dans une implémentation complète.</p>
        </div>
        
        <h2>Logs</h2>
        <p>Fichier de log complet: $LOG_FILE</p>
    </div>
</body>
</html>
EOF
)
    
    # Écriture du fichier HTML
    local report_file_path="$output_path/AutomationReport_$(date +%Y%m%d_%H%M%S).html"
    echo "$html_content" > "$report_file_path"
    
    write_log "Rapport HTML généré: $report_file_path" "info"
    echo "$report_file_path"
    return 0
}

# Fonction pour générer un rapport JSON
generate_json_report() {
    local processed_files="$1"
    local output_path="$2"
    
    write_log "Génération du rapport JSON" "info"
    
    local end_time=$(date +%s)
    local execution_time=$((end_time - START_TIME))
    
    # Création du rapport JSON
    local report=$(cat << EOF
{
    "generatedAt": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
    "executionTimeSeconds": $execution_time,
    "projectPath": "$PROJECT_PATH",
    "summary": {
        "totalFiles": $(echo "$processed_files" | jq 'length'),
        "successCount": $(echo "$processed_files" | jq '[.[] | select(.status == "Processed" or .status == "Transformed" or .status == "Enriched")] | length'),
        "errorCount": $(echo "$processed_files" | jq '[.[] | select(.status | contains("Error"))] | length'),
        "skippedCount": $(echo "$processed_files" | jq '[.[] | select(.status == "Skipped")] | length')
    },
    "files": $(echo "$processed_files" | jq '[.[] | {
        fileName: .fileName,
        filePath: .filePath,
        fileSize: .fileSize,
        extension: .extension,
        lastModified: .lastModified,
        status: .status,
        tags: .tags,
        metrics: .metrics,
        errorMessage: .errorMessage
    }]'),
    "config": {
        "logLevel": "$LOG_LEVEL",
        "maxThreads": $MAX_THREADS,
        "maxRetries": $MAX_RETRIES
    }
}
EOF
)
    
    # Écriture du fichier JSON
    local report_file_path="$output_path/AutomationReport_$(date +%Y%m%d_%H%M%S).json"
    echo "$report" | jq '.' > "$report_file_path"
    
    write_log "Rapport JSON généré: $report_file_path" "info"
    echo "$report_file_path"
    return 0
}
            
        *)
            write_log "Transformation non implémentée pour le type $extension" "warning"
            cp "$file_path" "$output_file"
            ;;
    esac
#######################################
# Traitement parallèle
#######################################

# Fonction pour traiter un fichier (pipeline complet)
process_file_pipeline() {
    local file="$1"
    
    # Pipeline de traitement
    local analysis=$(analyze_file "$file")
    
    local status=$(echo "$analysis" | jq -r '.status')
    if [ "$status" = "Processed" ]; then
        local transformed=$(transform_file "$analysis" "false" "true" "true")
        local enriched=$(enrich_data "$transformed")
        echo "$enriched"
    else
        echo "$analysis"
    fi
}

# Fonction pour exécuter le traitement en parallèle
invoke_parallel_processing() {
    local files=("$@")
    local total_files=${#files[@]}
    
    write_log "Démarrage du traitement parallèle pour $total_files fichiers avec $MAX_THREADS threads" "info"
    
    # Vérification de la disponibilité de GNU Parallel
    if command -v parallel >/dev/null 2>&1; then
        write_log "Utilisation de GNU Parallel pour le traitement parallèle" "info"
        
        # Création d'un fichier temporaire pour stocker les résultats
        local results_file="$TEMP_PATH/results_$(date +%s).json"
        echo "[]" > "$results_file"
        
        # Fonction pour traiter un fichier et ajouter le résultat au fichier
        process_and_save() {
            local file="$1"
            local results_file="$2"
            
            local result=$(process_file_pipeline "$file")
            
            # Ajout du résultat au fichier (avec verrouillage)
            flock "$results_file" bash -c "
                current=\$(cat \"$results_file\")
                echo \"\$current\" | jq --argjson result \"$result\" '. += [\$result]'  > \"$results_file\"
            "
        }
        
        # Export des fonctions et variables nécessaires pour GNU Parallel
        export -f process_file_pipeline analyze_file transform_file enrich_data write_log invoke_with_retry
        export LOG_FILE LOG_LEVEL TEMP_PATH API_KEY API_ENDPOINT MAX_RETRIES RETRY_DELAY
        
        # Exécution parallèle
        printf "%s\n" "${files[@]}" | parallel -j "$MAX_THREADS" "process_and_save {} $results_file"
        
        # Lecture des résultats
        local results=$(cat "$results_file")
        rm "$results_file"
        
        echo "$results"
    else
        write_log "GNU Parallel non disponible, utilisation d'une implémentation basique" "warning"
        
        # Implémentation basique avec des processus en arrière-plan
        local pids=()
        local results=()
        local processed=0
        
        # Traitement par lots
        for file in "${files[@]}"; do
            # Lancement du traitement en arrière-plan
            {
                local result=$(process_file_pipeline "$file")
                echo "$result" > "$TEMP_PATH/result_$(basename "$file").json"
            } &
            pids+=($!)
            
            # Limitation du nombre de processus simultanés
            if [ ${#pids[@]} -ge $MAX_THREADS ]; then
                # Attente de la fin d'un processus
                wait "${pids[0]}"
                pids=("${pids[@]:1}")
            fi
            
            # Affichage de la progression
            ((processed++))
            if [ $((processed % 10)) -eq 0 ] || [ $processed -eq $total_files ]; then
                write_log "Progression: $processed/$total_files fichiers traités" "info"
            fi
        done
        
        # Attente de la fin de tous les processus
        wait
        
        # Collecte des résultats
        local results_json="["
        local first=true
        for file in "${files[@]}"; do
            local result_file="$TEMP_PATH/result_$(basename "$file").json"
            if [ -f "$result_file" ]; then
                if [ "$first" = true ]; then
                    first=false
                else
                    results_json+=","
                fi
                results_json+=$(cat "$result_file")
                rm "$result_file"
            fi
        done
        results_json+="]"
        
        echo "$results_json"
    fi
}

#######################################
# Fonction principale
#######################################

# Fonction principale d'exécution
start_automation() {
    local generate_html_report=true
    local generate_json_report=true
    
    # Initialisation
    initialize_environment
    
    # Notification de démarrage
    if [ "$SEND_NOTIFICATIONS" = true ]; then
        send_notification "Démarrage de l'automatisation" "Traitement démarré pour le projet: $PROJECT_PATH" "Normal"
    fi
    
    # Récupération des fichiers à traiter
    local files_output=$(get_files_to_process "$PROJECT_PATH")
    local files=()
    
    while IFS= read -r line; do
        files+=("$line")
    done <<< "$files_output"
    
    if [ ${#files[@]} -eq 0 ]; then
        write_log "Aucun fichier à traiter trouvé dans $PROJECT_PATH" "warning"
        return 1
    fi
    
    # Traitement des fichiers
    local processed_files=""
    if [ $MAX_THREADS -gt 1 ]; then
        processed_files=$(invoke_parallel_processing "${files[@]}")
    else
        # Traitement séquentiel si un seul thread est demandé
        local results_array="["
        local file_count=${#files[@]}
        local current_file=0
        local first=true
        
        for file in "${files[@]}"; do
            ((current_file++))
            write_log "Traitement du fichier $current_file/$file_count: $(basename "$file")" "info"
            
            local result=$(process_file_pipeline "$file")
            
            if [ "$first" = true ]; then
                first=false
            else
                results_array+=","
            fi
            results_array+="$result"
        done
        
        results_array+="]"
        processed_files="$results_array"
    fi
    
    # Mise à jour des statistiques
    PROCESSED_FILES=$(echo "$processed_files" | jq 'length')
    ERROR_COUNT=$(echo "$processed_files" | jq '[.[] | select(.status | contains("Error"))] | length')
    
    # Génération des rapports
    local report_paths=()
    
    if [ "$generate_html_report" = true ]; then
        local html_report_path=$(generate_html_report "$processed_files" "$REPORT_PATH")
        report_paths+=("$html_report_path")
    fi
    
    if [ "$generate_json_report" = true ]; then
        local json_report_path=$(generate_json_report "$processed_files" "$REPORT_PATH")
        report_paths+=("$json_report_path")
    fi
    
    # Notification de fin
    if [ "$SEND_NOTIFICATIONS" = true ]; then
        local subject=""
        if [ $ERROR_COUNT -gt 0 ]; then
            subject="Automatisation terminée avec $ERROR_COUNT erreurs"
        else
            subject="Automatisation terminée avec succès"
        fi
        
        local body=$(cat << EOF
Traitement terminé pour le projet: $PROJECT_PATH
Fichiers traités: $PROCESSED_FILES
Erreurs: $ERROR_COUNT
Durée: $(( ($(date +%s) - START_TIME) / 60 )) minutes
Rapports générés: ${report_paths[*]}
EOF
)
        
        local priority=""
        if [ $ERROR_COUNT -gt 0 ]; then
            priority="High"
        else
            priority="Normal"
        fi
        
        send_notification "$subject" "$body" "$priority"
    fi
    
    # Résumé final
    write_log "=== Automatisation terminée ===" "info"
    write_log "Fichiers traités: $PROCESSED_FILES" "info"
    write_log "Erreurs: $ERROR_COUNT" "info"
    write_log "Avertissements: $WARNING_COUNT" "info"
    write_log "Durée: $(( ($(date +%s) - START_TIME) / 60 )) minutes" "info"
    write_log "Rapports générés: ${report_paths[*]}" "info"
    
    # Retour du statut
    if [ $ERROR_COUNT -gt 0 ]; then
        return 1
    else
        return 0
    fi
}

# Exécution du script si appelé directement
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    # Exécution de l'automatisation
    start_automation
    exit_code=$?
    
    # Affichage du résumé
    echo -e "\n${BLUE}Résumé de l'exécution:${NC}"
    echo -e "- Fichiers traités: $PROCESSED_FILES"
    
    if [ $ERROR_COUNT -gt 0 ]; then
        echo -e "- ${RED}Erreurs: $ERROR_COUNT${NC}"
    else
        echo -e "- ${GREEN}Erreurs: $ERROR_COUNT${NC}"
    fi
    
    if [ $WARNING_COUNT -gt 0 ]; then
        echo -e "- ${YELLOW}Avertissements: $WARNING_COUNT${NC}"
    else
        echo -e "- ${GREEN}Avertissements: $WARNING_COUNT${NC}"
    fi
    
    echo -e "- Durée: $(( ($(date +%s) - START_TIME) / 60 )) minutes"
    
    exit $exit_code
fi
    
    # Mise à jour du résultat
    local result=$(echo "$file_analysis" | jq --arg transformed_path "$output_file" \
                                            '.transformedPath = $transformed_path | .status = "Transformed"')
    
    echo "$result"
    return 0
}
        
        result=$(eval "$cmd" 2>&1) && success=true || {
            last_error="$result"
            write_log "Échec de $operation (tentative $attempt/$max_retries): $last_error" "warning"
            ((attempt++))
        }
    done
    
    if [ "$success" = false ]; then
        write_log "Échec définitif de $operation après $max_retries tentatives: $last_error" "error"
        return 1
    fi
    
    echo "$result"
    return 0
}

# Fonction d'envoi de notifications
send_notification() {
    local subject="$1"
    local body="$2"
    local priority="${3:-Normal}"
    
    if [ "$SEND_NOTIFICATIONS" != true ]; then
        write_log "Notification non envoyée (désactivé): $subject" "verbose"
        return
    fi
    
    write_log "Envoi de notification: $subject" "info"
    write_log "Contenu: $body" "verbose"
    
    # Exemple avec mail (à adapter selon votre système)
    # echo "$body" | mail -s "$subject" admin@example.com
    
    # Exemple avec osascript pour macOS
    if [ "$(uname)" = "Darwin" ]; then
        osascript -e "display notification \"$body\" with title \"$subject\""
    fi
}
        --send-notifications)
            SEND_NOTIFICATIONS=true
            shift
            ;;
        --help)
            show_help
            ;;
        *)
            echo "Option inconnue: $1"
            show_help
            ;;
    esac
done

# Vérification des arguments obligatoires
if [ -z "$PROJECT_PATH" ] || [ -z "$OUTPUT_PATH" ]; then
    echo "Erreur: --project-path et --output-path sont obligatoires"
    show_help
fi

# Vérification de l'existence du répertoire du projet
if [ ! -d "$PROJECT_PATH" ]; then
    echo "Erreur: Le répertoire du projet n'existe pas: $PROJECT_PATH"
    exit 1
fi

# Initialisation des chemins
TEMP_PATH="$OUTPUT_PATH/temp"
LOG_PATH="$OUTPUT_PATH/logs"
REPORT_PATH="$OUTPUT_PATH/reports"