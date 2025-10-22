<#
.SYNOPSIS
    Extrait les tokens Bearer depuis les logs d'un conteneur Docker ComfyUI.

.DESCRIPTION
    Ce script PowerShell surveille les logs d'un conteneur Docker ComfyUI spécifié
    pour y détecter la ligne contenant le token d'authentification Bearer généré par
    ComfyUI-Login lors de la première création d'un mot de passe.

    Une fois le token trouvé, il l'extrait et l'ajoute à un fichier .env.production,
    en l'associant à une variable d'environnement spécifiée. Le script gère un timeout
    pour éviter une attente infinie si le token n'apparaît pas.

.PARAMETER ContainerName
    Le nom du conteneur Docker à surveiller. Ce paramètre est obligatoire.

.PARAMETER EnvVarName
    Le nom de la variable d'environnement à utiliser dans le fichier .env.production
    (ex: 'QWEN_API_TOKEN'). Ce paramètre est obligatoire.

.PARAMETER OutputEnvFile
    Le chemin vers le fichier .env de production où le token sera sauvegardé.
    La valeur par défaut est "./.env.production".

.PARAMETER TimeoutSeconds
    Le nombre de secondes à attendre avant d'abandonner la recherche du token.
    La valeur par défaut est 120 secondes.

.EXAMPLE
    # Extraire le token du conteneur 'comfyui-qwen' et le sauvegarder comme QWEN_API_TOKEN
    ./extract-bearer-tokens.ps1 -ContainerName "comfyui-qwen" -EnvVarName "QWEN_API_TOKEN"

.EXAMPLE
    # Extraire le token avec un timeout de 5 minutes et un fichier de sortie personnalisé
    ./extract-bearer-tokens.ps1 -ContainerName "comfyui-forge" -EnvVarName "FORGE_API_TOKEN" -TimeoutSeconds 300 -OutputEnvFile "./.secrets/prod.env"

.NOTES
    - Le script nécessite que Docker soit installé et que l'utilisateur ait les permissions
      nécessaires pour exécuter `docker logs`.
    - Le conteneur cible doit être en cours d'exécution.
    - Le script est conçu pour être utilisé juste après avoir créé un mot de passe pour la
      première fois dans l'interface de ComfyUI.
    - Créé lors de la reconstruction post-incident (2025-10-22).
#>

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [string]$ContainerName,

    [Parameter(Mandatory=$true)]
    [string]$EnvVarName,

    [Parameter(Mandatory=$false)]
    [string]$OutputEnvFile = ".\.env.production",

    [Parameter(Mandatory=$false)]
    [int]$TimeoutSeconds = 120
)

# --- Configuration ---
$ErrorActionPreference = "Stop"
$LogPrefix = "[EXTRACT-TOKEN]"
$LogPattern = "Authentication Token: Bearer "

# --- Fonctions ---

function Write-Log {
    param ([string]$Message)
    Write-Host "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') - $LogPrefix $Message"
}

# --- Script Principal ---

Write-Log "Démarrage de l'extraction du token pour le conteneur '$ContainerName'..."

try {
    # Valider que le conteneur existe et tourne
    Write-Log "Vérification du conteneur '$ContainerName'..."
    $containerCheck = docker ps --filter "name=^${ContainerName}$" --format "{{.Names}}"
    if ([string]::IsNullOrEmpty($containerCheck)) {
        throw "Le conteneur '$ContainerName' n'est pas en cours d'exécution ou n'existe pas."
    }
    Write-Log "✅ Conteneur '$ContainerName' trouvé."

    # Démarrer la surveillance des logs
    Write-Log "Surveillance des logs pour le token... (Timeout: $TimeoutSeconds secondes)"
    $stopwatch = [System.Diagnostics.Stopwatch]::StartNew()
    $token = $null

    while ($stopwatch.Elapsed.TotalSeconds -lt $TimeoutSeconds) {
        $logOutput = docker logs --since "$($stopwatch.Elapsed.Minutes)m$($stopwatch.Elapsed.Seconds)s" $ContainerName 2>&1
        
        if ($logOutput -match "$LogPattern(.*?)$") {
            $token = $matches[1].Trim()
            Write-Log "✅ Token trouvé!"
            break
        }
        
        Start-Sleep -Seconds 2
        Write-Host "." -NoNewline
    }

    $stopwatch.Stop()
    Write-Host "" # Nouvelle ligne après les points

    if ([string]::IsNullOrEmpty($token)) {
        throw "Timeout atteint. Impossible de trouver le token dans les logs de '$ContainerName' après $TimeoutSeconds secondes."
    }

    Write-Log "Token extrait: $token"

    # Valider le format du token (simple vérification de longueur)
    if ($token.Length -lt 32) {
        throw "Le token extrait semble invalide (longueur inférieure à 32 caractères)."
    }
    Write-Log "✅ Format du token validé (longueur: $($token.Length))."

    # Ajouter le token au fichier .env
    Write-Log "Ajout du token au fichier '$OutputEnvFile'..."
    $envLine = "$EnvVarName=$token"
    
    if (Test-Path $OutputEnvFile) {
        $existingContent = Get-Content $OutputEnvFile
        # Supprimer l'ancienne variable si elle existe pour éviter les doublons
        $newContent = $existingContent | Where-Object { $_ -notmatch "^$EnvVarName=" }
        $newContent += $envLine
        Set-Content -Path $OutputEnvFile -Value $newContent -Encoding UTF8
    } else {
        Set-Content -Path $OutputEnvFile -Value $envLine -Encoding UTF8
    }

    Write-Log "🎉 Token sauvegardé avec succès dans '$OutputEnvFile'."
    Write-Log "Contenu du fichier mis à jour:"
    Get-Content $OutputEnvFile | ForEach-Object { Write-Host "  $_" }

} catch {
    Write-Error "❌ ERREUR: Une erreur est survenue lors de l'extraction du token."
    Write-Error $_.Exception.Message
    exit 1
}

exit 0