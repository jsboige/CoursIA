#!/bin/bash
#
# Organisateur de Fichiers - Script Bash pour organiser vos fichiers
#
# Description:
#   Ce script vous aide à organiser vos fichiers (photos, documents, etc.) en les triant
#   selon différents critères (date, type, nom) et en les déplaçant dans des dossiers appropriés.
#   Il peut également générer un rapport des opérations effectuées.
#
# Auteur: Roo Code Assistant
# Date: Mai 2025
# Version: 2.0
#
# Utilisation:
#   ./exemple-script.sh -s "/chemin/source" -d "/chemin/destination" -c "date" -r true -m false
#
# Options:
#   -s, --source         Dossier source contenant les fichiers à organiser
#   -d, --destination    Dossier destination où organiser les fichiers
#   -c, --critere        Critère d'organisation: date, type, nom (défaut: date)
#   -r, --rapport        Générer un rapport: true ou false (défaut: true)
#   -m, --simulation     Mode simulation (ne déplace pas réellement les fichiers): true ou false (défaut: false)
#   -h, --help           Afficher cette aide

# Sortir en cas d'erreur
set -e

# Configuration par défaut
SOURCE_FOLDER=""
DESTINATION_FOLDER=""
ORGANISATION_CRITERE="date"
GENERER_RAPPORT=true
MODE_SIMULATION=false

# Obtenir le répertoire du script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOG_FILE="${SCRIPT_DIR}/OrganisationFichiers_$(date +"%Y%m%d_%H%M%S").log"
RAPPORT_FILE="${SCRIPT_DIR}/Rapport_Organisation_$(date +"%Y%m%d_%H%M%S").html"

# Couleurs pour la console
COLOR_RESET="\033[0m"
COLOR_INFO="\033[36m"    # Cyan
COLOR_SUCCESS="\033[32m" # Vert
COLOR_WARNING="\033[33m" # Jaune
COLOR_ERROR="\033[31m"   # Rouge

# Fonction pour afficher l'aide
show_help() {
    echo "Organisateur de Fichiers - Script Bash pour organiser vos fichiers"
    echo
    echo "Utilisation:"
    echo "  $0 -s \"/chemin/source\" -d \"/chemin/destination\" -c \"date\" -r true -m false"
    echo
    echo "Options:"
    echo "  -s, --source         Dossier source contenant les fichiers à organiser"
    echo "  -d, --destination    Dossier destination où organiser les fichiers"
    echo "  -c, --critere        Critère d'organisation: date, type, nom (défaut: date)"
    echo "  -r, --rapport        Générer un rapport: true ou false (défaut: true)"
    echo "  -m, --simulation     Mode simulation (ne déplace pas réellement les fichiers): true ou false (défaut: false)"
    echo "  -h, --help           Afficher cette aide"
    echo
    exit 0
}

# Fonction pour écrire dans le journal
write_log() {
    local message="$1"
    local level="${2:-INFO}"
    
    timestamp=$(date "+%Y-%m-%d %H:%M:%S")
    log_entry="[$timestamp] [$level] $message"
    
    # Afficher dans la console avec couleur
    case "$level" in
        "INFO")
            echo -e "${COLOR_INFO}${log_entry}${COLOR_RESET}"
            ;;
        "SUCCESS")
            echo -e "${COLOR_SUCCESS}${log_entry}${COLOR_RESET}"
            ;;
        "WARNING")
            echo -e "${COLOR_WARNING}${log_entry}${COLOR_RESET}"
            ;;
        "ERROR")
            echo -e "${COLOR_ERROR}${log_entry}${COLOR_RESET}"
            ;;
        *)
            echo "$log_entry"
            ;;
    esac
    
    # Écrire dans le fichier journal
    echo "$log_entry" >> "$LOG_FILE"
}

# Fonction pour demander un dossier à l'utilisateur (utilise zenity si disponible, sinon demande en ligne de commande)
get_folder_from_user() {
    local message="$1"
    local default_path="${2:-}"
    local selected_path=""
    
    if command -v zenity &> /dev/null; then
        # Interface graphique avec zenity
        selected_path=$(zenity --file-selection --directory --title="$message" --filename="$default_path" 2>/dev/null)
        if [ $? -ne 0 ]; then
            return 1
        fi
    elif command -v dialog &> /dev/null; then
        # Interface semi-graphique avec dialog
        tempfile=$(mktemp)
        dialog --title "$message" --dselect "$default_path" 20 70 2>"$tempfile"
        if [ $? -ne 0 ]; then
            rm -f "$tempfile"
            return 1
        fi
        selected_path=$(cat "$tempfile")
        rm -f "$tempfile"
    else
        # Interface en ligne de commande
        echo "$message"
        if [ -n "$default_path" ]; then
            echo "Appuyez sur Entrée pour utiliser: $default_path"
        fi
        read -e -p "Chemin: " -i "$default_path" selected_path
        if [ -z "$selected_path" ]; then
            return 1
        fi
    fi
    
    echo "$selected_path"
    return 0
}

# Fonction pour vérifier et créer un répertoire
ensure_directory() {
    local dir_path="$1"
    
    if [ ! -d "$dir_path" ]; then
        write_log "Création du répertoire: $dir_path"
        if [ "$MODE_SIMULATION" = false ]; then
            mkdir -p "$dir_path"
        fi
        return 0
    else
        write_log "Le répertoire existe déjà: $dir_path"
        return 1
    fi
}

# Fonction pour obtenir l'extension d'un fichier sans le point
get_file_extension_without_dot() {
    local filename="$1"
    local extension="${filename##*.}"
    
    if [ "$extension" = "$filename" ]; then
        echo ""
    else
        echo "$extension" | tr '[:upper:]' '[:lower:]'
    fi
}

# Fonction pour obtenir le type de fichier à partir de l'extension
get_file_type() {
    local extension="$1"
    
    # Définir les extensions par type
    local image_extensions=("jpg" "jpeg" "png" "gif" "bmp" "tiff" "webp" "heic")
    local document_extensions=("pdf" "doc" "docx" "xls" "xlsx" "ppt" "pptx" "txt" "rtf" "odt")
    local video_extensions=("mp4" "avi" "mov" "wmv" "mkv" "flv" "webm")
    local audio_extensions=("mp3" "wav" "ogg" "flac" "aac" "wma")
    local archive_extensions=("zip" "rar" "7z" "tar" "gz")
    
    # Vérifier le type
    for ext in "${image_extensions[@]}"; do
        if [ "$extension" = "$ext" ]; then
            echo "Images"
            return
        fi
    done
    
    for ext in "${document_extensions[@]}"; do
        if [ "$extension" = "$ext" ]; then
            echo "Documents"
            return
        fi
    done
    
    for ext in "${video_extensions[@]}"; do
        if [ "$extension" = "$ext" ]; then
            echo "Videos"
            return
        fi
    done
    
    for ext in "${audio_extensions[@]}"; do
        if [ "$extension" = "$ext" ]; then
            echo "Audio"
            return
        fi
    done
    
    for ext in "${archive_extensions[@]}"; do
        if [ "$extension" = "$ext" ]; then
            echo "Archives"
            return
        fi
    done
    
    echo "Autres"
}

# Fonction pour organiser les fichiers
organize_files() {
    local source_path="$1"
    local destination_path="$2"
    local critere="$3"
    
    # Vérifier que les chemins existent
    if [ ! -d "$source_path" ]; then
        write_log "Le dossier source n'existe pas: $source_path" "ERROR"
        return 1
    fi
    
    ensure_directory "$destination_path"
    
    # Récupérer tous les fichiers du dossier source (y compris les sous-dossiers)
    local all_files=$(find "$source_path" -type f | sort)
    local total_files=$(echo "$all_files" | wc -l)
    
    if [ "$total_files" -eq 0 ]; then
        write_log "Aucun fichier trouvé dans le dossier source." "WARNING"
        return 1
    fi
    
    write_log "Début de l'organisation de $total_files fichiers selon le critère: $critere"
    
    # Statistiques pour le rapport
    local processed_files=0
    local skipped_files=0
    
    # Tableaux associatifs pour les statistiques
    declare -A stats_by_type
    declare -A stats_by_date_year
    declare -A stats_by_date_month
    declare -A stats_by_name
    
    # Traiter chaque fichier
    while IFS= read -r file; do
        local filename=$(basename "$file")
        local extension=$(get_file_extension_without_dot "$filename")
        local file_type=$(get_file_type "$extension")
        local file_date=$(date -r "$file" "+%Y-%m-%d")
        local year=$(date -r "$file" "+%Y")
        local month=$(date -r "$file" "+%m - %B")
        local first_letter=$(echo "${filename:0:1}" | tr '[:lower:]' '[:upper:]')
        
        # Déterminer le dossier de destination selon le critère
        local destination_subfolder=""
        
        case "$critere" in
            "date")
                destination_subfolder="$destination_path/$year/$month"
                
                # Mettre à jour les statistiques
                if [ -z "${stats_by_date_year[$year]}" ]; then
                    stats_by_date_year[$year]=0
                fi
                stats_by_date_year[$year]=$((stats_by_date_year[$year] + 1))
                
                local year_month="$year-$month"
                if [ -z "${stats_by_date_month[$year_month]}" ]; then
                    stats_by_date_month[$year_month]=0
                fi
                stats_by_date_month[$year_month]=$((stats_by_date_month[$year_month] + 1))
                ;;
            "type")
                destination_subfolder="$destination_path/$file_type"
                
                # Mettre à jour les statistiques
                if [ -z "${stats_by_type[$file_type]}" ]; then
                    stats_by_type[$file_type]=0
                fi
                stats_by_type[$file_type]=$((stats_by_type[$file_type] + 1))
                ;;
            "nom")
                destination_subfolder="$destination_path/$first_letter"
                
                # Mettre à jour les statistiques
                if [ -z "${stats_by_name[$first_letter]}" ]; then
                    stats_by_name[$first_letter]=0
                fi
                stats_by_name[$first_letter]=$((stats_by_name[$first_letter] + 1))
                ;;
        esac
        
        # Créer le dossier de destination s'il n'existe pas
        ensure_directory "$destination_subfolder"
        
        # Chemin complet du fichier de destination
        local destination_filepath="$destination_subfolder/$filename"
        
        # Vérifier si le fichier existe déjà à destination
        if [ -f "$destination_filepath" ]; then
            local filename_only="${filename%.*}"
            local new_filename="${filename_only} ($(date +%Y%m%d_%H%M%S)).$extension"
            destination_filepath="$destination_subfolder/$new_filename"
            write_log "Le fichier existe déjà, renommage en: $new_filename" "WARNING"
        fi
        
        # Copier le fichier
        write_log "Déplacement du fichier: $filename vers $destination_subfolder"
        if [ "$MODE_SIMULATION" = false ]; then
            if cp "$file" "$destination_filepath"; then
                processed_files=$((processed_files + 1))
            else
                write_log "Erreur lors du déplacement du fichier $filename" "ERROR"
                skipped_files=$((skipped_files + 1))
            fi
        else
            processed_files=$((processed_files + 1))
        fi
        
    done <<< "$all_files"
    
    write_log "Organisation terminée. $processed_files fichiers traités, $skipped_files fichiers ignorés." "SUCCESS"
    
    # Créer un fichier temporaire pour stocker les statistiques
    local stats_file=$(mktemp)
    
    # Écrire les statistiques dans le fichier temporaire
    echo "TOTAL_FILES=$total_files" > "$stats_file"
    echo "PROCESSED_FILES=$processed_files" >> "$stats_file"
    echo "SKIPPED_FILES=$skipped_files" >> "$stats_file"
    
    # Écrire les statistiques par type
    for type in "${!stats_by_type[@]}"; do
        echo "TYPE_${type}=${stats_by_type[$type]}" >> "$stats_file"
    done
    
    # Écrire les statistiques par année
    for year in "${!stats_by_date_year[@]}"; do
        echo "YEAR_${year}=${stats_by_date_year[$year]}" >> "$stats_file"
    done
    
    # Écrire les statistiques par mois
    for year_month in "${!stats_by_date_month[@]}"; do
        echo "MONTH_${year_month}=${stats_by_date_month[$year_month]}" >> "$stats_file"
    done
    
    # Écrire les statistiques par nom
    for letter in "${!stats_by_name[@]}"; do
        echo "NAME_${letter}=${stats_by_name[$letter]}" >> "$stats_file"
    done
    
    echo "$stats_file"
    return 0
}

# Fonction pour générer un rapport HTML
generate_report() {
    local stats_file="$1"
    local source_path="$2"
    local destination_path="$3"
    local critere="$4"
    
    local report_date=$(date "+%d/%m/%Y %H:%M:%S")
    
    # Lire les statistiques
    source "$stats_file"
    
    # Créer le contenu HTML
    cat > "$RAPPORT_FILE" << EOF
<!DOCTYPE html>
<html lang="fr">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Rapport d'Organisation de Fichiers</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            line-height: 1.6;
            margin: 0;
            padding: 20px;
            color: #333;
        }
        h1, h2, h3 {
            color: #2c3e50;
        }
        .container {
            max-width: 1000px;
            margin: 0 auto;
            background: #f9f9f9;
            padding: 20px;
            border-radius: 5px;
            box-shadow: 0 0 10px rgba(0,0,0,0.1);
        }
        .summary {
            background: #e8f4fc;
            padding: 15px;
            border-radius: 5px;
            margin-bottom: 20px;
        }
        .success {
            color: #27ae60;
            font-weight: bold;
        }
        .warning {
            color: #f39c12;
            font-weight: bold;
        }
        table {
            width: 100%;
            border-collapse: collapse;
            margin-bottom: 20px;
        }
        th, td {
            padding: 10px;
            border: 1px solid #ddd;
            text-align: left;
        }
        th {
            background-color: #f2f2f2;
        }
        tr:nth-child(even) {
            background-color: #f9f9f9;
        }
        .chart {
            margin-top: 20px;
            margin-bottom: 40px;
        }
        .bar {
            height: 25px;
            background-color: #3498db;
            margin-bottom: 5px;
            border-radius: 3px;
        }
        .bar-label {
            display: flex;
            justify-content: space-between;
            margin-bottom: 15px;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>Rapport d'Organisation de Fichiers</h1>
        <p>Rapport généré le: $report_date</p>
        
        <div class="summary">
            <h2>Résumé</h2>
            <p>Dossier source: <strong>$source_path</strong></p>
            <p>Dossier destination: <strong>$destination_path</strong></p>
            <p>Critère d'organisation: <strong>$critere</strong></p>
            <p>Fichiers traités: <span class="success">$PROCESSED_FILES</span> sur $TOTAL_FILES</p>
            <p>Fichiers ignorés: <span class="warning">$SKIPPED_FILES</span></p>
        </div>
EOF
    
    # Ajouter les détails selon le critère
    case "$critere" in
        "type")
            cat >> "$RAPPORT_FILE" << EOF
        <h2>Organisation par Type de Fichier</h2>
        <table>
            <tr>
                <th>Type de Fichier</th>
                <th>Nombre de Fichiers</th>
            </tr>
EOF
            
            # Récupérer tous les types
            types=$(grep "^TYPE_" "$stats_file" | cut -d'=' -f1 | sed 's/^TYPE_//')
            
            for type in $types; do
                count=$(grep "^TYPE_$type=" "$stats_file" | cut -d'=' -f2)
                percentage=$(echo "scale=1; ($count / $TOTAL_FILES) * 100" | bc)
                bar_width=$(echo "scale=0; ($count / $TOTAL_FILES) * 100" | bc)
                
                cat >> "$RAPPORT_FILE" << EOF
            <tr>
                <td>$type</td>
                <td>$count ($percentage%)</td>
            </tr>
EOF
            done
            
            cat >> "$RAPPORT_FILE" << EOF
        </table>
        
        <div class="chart">
            <h3>Répartition graphique</h3>
EOF
            
            for type in $types; do
                count=$(grep "^TYPE_$type=" "$stats_file" | cut -d'=' -f2)
                percentage=$(echo "scale=1; ($count / $TOTAL_FILES) * 100" | bc)
                bar_width=$(echo "scale=0; ($count / $TOTAL_FILES) * 100" | bc)
                
                cat >> "$RAPPORT_FILE" << EOF
            <div class="bar-label">
                <span>$type</span>
                <span>$count ($percentage%)</span>
            </div>
            <div class="bar" style="width: ${bar_width}%;"></div>
EOF
            done
            
            cat >> "$RAPPORT_FILE" << EOF
        </div>
EOF
            ;;
            
        "date")
            cat >> "$RAPPORT_FILE" << EOF
        <h2>Organisation par Date</h2>
EOF
            
            # Récupérer toutes les années
            years=$(grep "^YEAR_" "$stats_file" | cut -d'=' -f1 | sed 's/^YEAR_//' | sort)
            
            for year in $years; do
                cat >> "$RAPPORT_FILE" << EOF
        <h3>$year</h3>
        <table>
            <tr>
                <th>Mois</th>
                <th>Nombre de Fichiers</th>
            </tr>
EOF
                
                # Récupérer tous les mois pour cette année
                months=$(grep "^MONTH_${year}-" "$stats_file" | cut -d'=' -f1 | sed "s/^MONTH_${year}-//" | sort)
                
                for month_key in $months; do
                    month=$(echo "$month_key" | sed 's/_/ /g')
                    count=$(grep "^MONTH_${year}-${month_key}=" "$stats_file" | cut -d'=' -f2)
                    
                    cat >> "$RAPPORT_FILE" << EOF
            <tr>
                <td>$month</td>
                <td>$count</td>
            </tr>
EOF
                done
                
                cat >> "$RAPPORT_FILE" << EOF
        </table>
EOF
            done
            ;;
            
        "nom")
            cat >> "$RAPPORT_FILE" << EOF
        <h2>Organisation par Nom</h2>
        <table>
            <tr>
                <th>Première Lettre</th>
                <th>Nombre de Fichiers</th>
            </tr>
EOF
            
            # Récupérer toutes les lettres
            letters=$(grep "^NAME_" "$stats_file" | cut -d'=' -f1 | sed 's/^NAME_//' | sort)
            
            for letter in $letters; do
                count=$(grep "^NAME_$letter=" "$stats_file" | cut -d'=' -f2)
                
                cat >> "$RAPPORT_FILE" << EOF
            <tr>
                <td>$letter</td>
                <td>$count</td>
            </tr>
EOF
            done
            
            cat >> "$RAPPORT_FILE" << EOF
        </table>
EOF
            ;;
    esac
    
    # Fermer le HTML
    cat >> "$RAPPORT_FILE" << EOF
    </div>
</body>
</html>
EOF
    
    write_log "Rapport généré: $RAPPORT_FILE" "SUCCESS"
    
    # Supprimer le fichier temporaire de statistiques
    rm -f "$stats_file"
    
    echo "$RAPPORT_FILE"
}

# Fonction pour ouvrir un fichier avec le programme par défaut
open_file() {
    local file_path="$1"
    
    if [ ! -f "$file_path" ]; then
        write_log "Le fichier n'existe pas: $file_path" "ERROR"
        return 1
    fi
    
    # Détecter le système d'exploitation et ouvrir le fichier
    case "$(uname)" in
        "Darwin") # macOS
            open "$file_path"
            ;;
        "Linux")
            if command -v xdg-open &> /dev/null; then
                xdg-open "$file_path"
            elif command -v gnome-open &> /dev/null; then
                gnome-open "$file_path"
            else
                write_log "Impossible d'ouvrir le fichier automatiquement. Chemin: $file_path" "WARNING"
                return 1
            fi
            ;;
        *)
            write_log "Système d'exploitation non pris en charge pour l'ouverture automatique de fichiers" "WARNING"
            return 1
            ;;
    esac
    
    return 0
}

# Fonction principale
main() {
    write_log "Démarrage de l'Organisateur de Fichiers"
    
    # Si les dossiers ne sont pas spécifiés, demander à l'utilisateur
    if [ -z "$SOURCE_FOLDER" ] || [ ! -d "$SOURCE_FOLDER" ]; then
        write_log "Dossier source non spécifié ou invalide, demande à l'utilisateur"
        SOURCE_FOLDER=$(get_folder_from_user "Sélectionnez le dossier contenant les fichiers à organiser")
        
        if [ -z "$SOURCE_FOLDER" ]; then
            write_log "Aucun dossier source sélectionné, arrêt du script" "ERROR"
            return 1
        fi
    fi
    
    if [ -z "$DESTINATION_FOLDER" ]; then
        write_log "Dossier destination non spécifié, demande à l'utilisateur"
        DESTINATION_FOLDER=$(get_folder_from_user "Sélectionnez le dossier où organiser les fichiers" "$SOURCE_FOLDER")
        
        if [ -z "$DESTINATION_FOLDER" ]; then
            write_log "Aucun dossier destination sélectionné, arrêt du script" "ERROR"
            return 1
        fi
    fi
    
    # Afficher les informations de configuration
    write_log "Configuration:"
    write_log "  - Dossier source: $SOURCE_FOLDER"
    write_log "  - Dossier destination: $DESTINATION_FOLDER"
    write_log "  - Critère d'organisation: $ORGANISATION_CRITERE"
    write_log "  - Générer rapport: $GENERER_RAPPORT"
    write_log "  - Mode simulation: $MODE_SIMULATION"
    
    if [ "$MODE_SIMULATION" = true ]; then
        write_log "Mode simulation activé - Aucun fichier ne sera réellement déplacé" "WARNING"
    fi
    
    # Organiser les fichiers
    stats_file=$(organize_files "$SOURCE_FOLDER" "$DESTINATION_FOLDER" "$ORGANISATION_CRITERE")
    
    # Vérifier si l'organisation a réussi
    if [ $? -ne 0 ]; then
        write_log "Échec de l'organisation des fichiers" "ERROR"
        return 1
    fi
    
    # Générer le rapport si demandé
    if [ "$GENERER_RAPPORT" = true ] && [ -f "$stats_file" ]; then
        report_path=$(generate_report "$stats_file" "$SOURCE_FOLDER" "$DESTINATION_FOLDER" "$ORGANISATION_CRITERE")
        
        # Ouvrir le rapport dans le navigateur par défaut
        if [ "$MODE_SIMULATION" = false ] && [ -f "$report_path" ]; then
            write_log "Ouverture du rapport dans le navigateur"
            open_file "$report_path"
        fi
    fi
    
    write_log "Script terminé avec succès" "SUCCESS"
    return 0
}

# Analyser les arguments de la ligne de commande
while [[ $# -gt 0 ]]; do
    case "$1" in
        -s|--source)
            SOURCE_FOLDER="$2"
            shift 2
            ;;
        -d|--destination)
            DESTINATION_FOLDER="$2"
            shift 2
            ;;
        -c|--critere)
            if [[ "$2" =~ ^(date|type|nom)$ ]]; then
                ORGANISATION_CRITERE="$2"
            else
                write_log "Critère invalide: $2. Utilisation de la valeur par défaut: date" "WARNING"
            fi
            shift 2
            ;;
        -r|--rapport)
            if [[ "$2" =~ ^(true|false)$ ]]; then
                GENERER_RAPPORT="$2"
            else
                write_log "Valeur invalide pour --rapport: $2. Utilisation de la valeur par défaut: true" "WARNING"
            fi
            shift 2
            ;;
        -m|--simulation)
            if [[ "$2" =~ ^(true|false)$ ]]; then
                MODE_SIMULATION="$2"
            else
                write_log "Valeur invalide pour --simulation: $2. Utilisation de la valeur par défaut: false" "WARNING"
            fi
            shift 2
            ;;
        -h|--help)
            show_help
            ;;
        *)
            write_log "Option inconnue: $1" "WARNING"
            shift
            ;;
    esac
done

# Gestion des erreurs
trap 'write_log "Erreur à la ligne $LINENO: $BASH_COMMAND" "ERROR"; exit 1' ERR

# Exécution du script
main
exit $?