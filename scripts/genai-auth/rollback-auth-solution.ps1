<#
.SYNOPSIS
    Annule le déploiement de la solution d'authentification ComfyUI et restaure une configuration précédente.

.DESCRIPTION
    Ce script PowerShell est une mesure de sécurité conçue pour annuler rapidement un déploiement
    de la solution d'authentification. Il utilise un répertoire de sauvegarde créé lors du déploiement
    pour restaurer le fichier docker-compose.yml à son état antérieur.

    Le script arrête les services, restaure la configuration, puis redémarre les services
    pour revenir à l'état pré-déploiement. Il effectue également un nettoyage des fichiers
    de configuration (.env) liés à l'authentification.

.PARAMETER BackupPath
    Le chemin vers le répertoire de sauvegarde contenant la configuration à restaurer.
    Ce paramètre est obligatoire.

.PARAMETER DockerComposeFile
    Le chemin vers le fichier docker-compose.yml à restaurer.
    La valeur par défaut est "docker-compose.yml".

.PARAMETER Services
    Une liste des services Docker à redémarrer dans le cadre du rollback.
    La valeur par défaut est @("comfyui-qwen", "comfyui-forge").

.EXAMPLE
    # Annuler un déploiement en utilisant un répertoire de sauvegarde spécifique
    ./rollback-auth-solution.ps1 -BackupPath ".\.backups\deploy_20251022183000"

.NOTES
    - Ce script est potentiellement destructeur et doit être utilisé avec une grande prudence.
    - Il suppose qu'une sauvegarde valide existe au chemin spécifié.
    - Créé lors de la reconstruction post-incident (2025-10-22).
#>

[CmdletBinding(SupportsShouldProcess = $true)]
param(
    [Parameter(Mandatory=$true)]
    [string]$BackupPath,

    [Parameter(Mandatory=$false)]
    [string]$DockerComposeFile = "docker-compose.yml",

    [Parameter(Mandatory=$false)]
    [string[]]$Services = @("comfyui-qwen", "comfyui-forge")
)

# --- Configuration ---
$ErrorActionPreference = "Stop"
$LogPrefix = "[ROLLBACK-AUTH]"

# --- Fonctions ---

function Write-Log {
    param ([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'
    $logEntry = "$timestamp - $LogPrefix [$Level] $Message"
    Write-Host $logEntry
}

function Invoke-Step {
    param(
        [string]$StepName,
        [scriptblock]$Action
    )
    Write-Log "▶️ DÉBUT ÉTAPE: $StepName"
    try {
        if ($PSCmdlet.ShouldProcess("Exécuter l'étape: $StepName")) {
            Invoke-Command -ScriptBlock $Action
        } else {
            Write-Log "Étape '$StepName' ignorée (Dry Run)."
        }
        Write-Log "✅ SUCCÈS ÉTAPE: $StepName"
        return $true
    } catch {
        Write-Log "❌ ÉCHEC ÉTAPE: $StepName" -Level "ERROR"
        Write-Log "   Erreur: $($_.Exception.Message)" -Level "ERROR"
        return $false
    }
}

# --- Script Principal ---

Write-Log "🔥 Démarrage du rollback de la solution d'authentification."
Write-Log "Utilisation du backup: $BackupPath" -Level "WARN"

# Étape 1: Validation du répertoire de backup
$backupValidationSuccess = Invoke-Step -StepName "Validation du répertoire de backup" -Action {
    if (-not (Test-Path -Path $BackupPath -PathType Container)) {
        throw "Le répertoire de backup '$BackupPath' n'existe pas."
    }
    $backupFile = Join-Path $BackupPath $DockerComposeFile
    if (-not (Test-Path -Path $backupFile)) {
        throw "Le fichier de backup '$backupFile' n'a pas été trouvé dans le répertoire de backup."
    }
    Write-Log "Backup validé."
}
if (-not $backupValidationSuccess) { exit 1 }

# Étape 2: Arrêt des services
$stopSuccess = Invoke-Step -StepName "Arrêt des services Docker" -Action {
    docker-compose -f $DockerComposeFile stop $Services
}
if (-not $stopSuccess) { exit 1 }

# Étape 3: Restauration de la configuration
$restoreSuccess = Invoke-Step -StepName "Restauration de la configuration Docker" -Action {
    $backupFile = Join-Path $BackupPath $DockerComposeFile
    Copy-Item -Path $backupFile -Destination . -Force
    Write-Log "Fichier '$DockerComposeFile' restauré depuis le backup."
}
if (-not $restoreSuccess) { exit 1 }

# Étape 4: Nettoyage des fichiers de configuration .env (optionnel mais recommandé)
Invoke-Step -StepName "Nettoyage des fichiers .env de configuration d'authentification" -Action {
    foreach ($service in $Services) {
        $envFile = "docker-configurations\$service\.env"
        if (Test-Path $envFile) {
            # On ne supprime pas le fichier, mais on commente les lignes d'auth
            $content = Get-Content $envFile
            $newContent = $content | ForEach-Object {
                if ($_ -match "^(COMFYUI_LOGIN_ENABLED|COMFYUI_ARGS.*--enable-auth)") {
                    "#" + $_
                } else {
                    $_
                }
            }
            Set-Content -Path $envFile -Value $newContent -Encoding UTF8
            Write-Log "Configuration d'authentification désactivée dans '$envFile'."
        }
    }
}

# Étape 5: Redémarrage des services avec l'ancienne configuration
$restartSuccess = Invoke-Step -StepName "Redémarrage des services avec la configuration restaurée" -Action {
    docker-compose -f $DockerComposeFile up -d $Services
}
if (-not $restartSuccess) {
    Write-Log "Le redémarrage des services a échoué. Intervention manuelle requise." -Level "FATAL"
    exit 1
}

Write-Log "✅ Rollback terminé. Le système a été restauré à l'état du backup '$BackupPath'."
exit 0