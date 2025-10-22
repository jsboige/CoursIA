<#
.SYNOPSIS
    Configure l'authentification pour un service ComfyUI via un fichier de configuration .env.

.DESCRIPTION
    Ce script PowerShell gère la configuration de l'authentification pour un service ComfyUI
    en créant ou en mettant à jour un fichier .env spécifique au service. Il permet d'activer
    l'authentification, de définir les arguments de démarrage de ComfyUI et de s'assurer que
    la configuration est prête pour le déploiement.
    Le script est conçu pour être modulaire et s'adapter à différents services (Qwen, Forge, etc.).

.PARAMETER ServiceName
    Le nom du service à configurer (ex: 'comfyui-qwen', 'comfyui-forge').
    Ce paramètre est obligatoire.

.PARAMETER ConfigPath
    Le chemin vers le répertoire de configuration Docker du service, où le fichier .env sera créé.
    La valeur par défaut est "docker-configurations/$ServiceName".

.EXAMPLE
    # Configurer le service 'comfyui-qwen' en utilisant le chemin par défaut
    ./configure-comfyui-auth.ps1 -ServiceName "comfyui-qwen"

.EXAMPLE
    # Configurer le service 'comfyui-forge' avec un chemin de configuration personnalisé
    ./configure-comfyui-auth.ps1 -ServiceName "comfyui-forge" -ConfigPath "./docker-configs/forge"

.NOTES
    - Le script crée le répertoire de configuration s'il n'existe pas.
    - Il préserve les variables existantes dans le fichier .env et ne met à jour que celles
      liées à l'authentification.
    - Créé lors de la reconstruction post-incident (2025-10-22).
#>

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [string]$ServiceName,

    [Parameter(Mandatory=$false)]
    [string]$ConfigPath = "docker-configurations\$ServiceName"
)

# --- Configuration ---
$ErrorActionPreference = "Stop"
$LogPrefix = "[CONFIG-AUTH]"

# --- Fonctions ---

# Affiche un message de log formaté
function Write-Log {
    param ([string]$Message)
    Write-Host "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') - $LogPrefix $Message"
}

# --- Script Principal ---

Write-Log "Démarrage de la configuration d'authentification pour le service '$ServiceName'..."

try {
    # Vérifier et créer le répertoire de configuration si nécessaire
    if (-not (Test-Path -Path $ConfigPath -PathType Container)) {
        Write-Log "ℹ️ Le répertoire de configuration '$ConfigPath' n'existe pas. Création..."
        New-Item -Path $ConfigPath -ItemType Directory -Force | Out-Null
        Write-Log "✅ Répertoire '$ConfigPath' créé."
    } else {
        Write-Log "✅ Le répertoire de configuration '$ConfigPath' existe déjà."
    }

    $envFilePath = Join-Path -Path $ConfigPath -ChildPath ".env"
    $envContent = @{}

    # Lire le contenu existant du fichier .env s'il existe
    if (Test-Path -Path $envFilePath) {
        Write-Log "ℹ️ Fichier .env existant trouvé à '$envFilePath'. Lecture du contenu..."
        Get-Content $envFilePath | ForEach-Object {
            if ($_ -match "^(.*?)=(.*)$") {
                $envContent[$matches[1]] = $matches[2]
            }
        }
    } else {
        Write-Log "ℹ️ Aucun fichier .env existant. Un nouveau fichier sera créé."
    }

    # Définir/Mettre à jour les variables d'authentification
    Write-Log "Mise à jour des variables d'environnement pour l'authentification..."
    $envContent["COMFYUI_LOGIN_ENABLED"] = "true"
    
    # Concaténer les arguments de démarrage. Préserve les arguments existants.
    $existingArgs = if ($envContent.ContainsKey("COMFYUI_ARGS")) { $envContent["COMFYUI_ARGS"] } else { "" }
    if ($existingArgs -notlike "*--enable-auth*") {
        $newArgs = ($existingArgs + " --enable-auth").Trim()
        $envContent["COMFYUI_ARGS"] = $newArgs
        Write-Log "✅ Argument '--enable-auth' ajouté à COMFYUI_ARGS."
    } else {
        Write-Log "✅ Argument '--enable-auth' déjà présent dans COMFYUI_ARGS."
    }

    # Préparer le nouveau contenu du fichier .env
    $newEnvFileContent = $envContent.GetEnumerator() | ForEach-Object { "$($_.Name)=$($_.Value)" }

    # Écrire le contenu mis à jour dans le fichier .env
    Write-Log "Écriture de la configuration dans '$envFilePath'..."
    Set-Content -Path $envFilePath -Value $newEnvFileContent -Encoding UTF8
    
    Write-Log "--- Configuration .env ---"
    Get-Content $envFilePath | ForEach-Object { Write-Host "  $_" }
    Write-Log "--------------------------"

    Write-Log "🎉 Configuration de l'authentification pour '$ServiceName' terminée avec succès."
    Write-Log "Le fichier '$envFilePath' a été créé/mis à jour."

} catch {
    Write-Error "❌ ERREUR: Une erreur est survenue lors de la configuration."
    Write-Error $_.Exception.Message
    exit 1
}

exit 0