<#
.SYNOPSIS
    Orchestre le déploiement complet de la solution d'authentification ComfyUI.

.DESCRIPTION
    Ce script PowerShell est le chef d'orchestre du déploiement. Il exécute une séquence
    d'étapes critiques pour mettre en place la solution d'authentification de manière
    sécurisée et contrôlée. Ses responsabilités incluent :
    - La sauvegarde des configurations existantes.
    - L'arrêt des services ComfyUI concernés.
    - L'application des nouvelles configurations Docker avec authentification.
    - Le redémarrage des services.
    - L'exécution de tests de connectivité post-déploiement.
    - Un mécanisme de rollback automatique en cas d'échec d'une étape critique.

.PARAMETER DockerComposeFile
    Le chemin vers le fichier docker-compose.yml à utiliser pour le déploiement.
    La valeur par défaut est "docker-compose.yml".

.PARAMETER BackupPath
    Le chemin vers le répertoire où les sauvegardes de configuration seront stockées.
    La valeur par défaut est "./.backups/deploy_$(Get-Date -Format 'yyyyMMddHHmmss')".

.PARAMETER Services
    Une liste des services Docker à redémarrer dans le cadre du déploiement.
    La valeur par défaut est @("comfyui-qwen", "comfyui-forge").

.EXAMPLE
    # Déployer la solution en utilisant les paramètres par défaut
    ./deploy-auth-solution.ps1

.EXAMPLE
    # Déployer avec un fichier docker-compose spécifique et un seul service
    ./deploy-auth-solution.ps1 -DockerComposeFile "docker-compose.prod.yml" -Services "comfyui-prod"

.NOTES
    - Ce script est potentiellement destructeur. Exécutez-le avec prudence.
    - Il est fortement recommandé de faire un 'dry run' (non implémenté ici) ou de tester
      dans un environnement de pré-production avant de l'exécuter en production.
    - Créé lors de la reconstruction post-incident (2025-10-22).
#>

[CmdletBinding(SupportsShouldProcess = $true)]
param(
    [Parameter(Mandatory=$false)]
    [string]$DockerComposeFile = "docker-compose.yml",

    [Parameter(Mandatory=$false)]
    [string]$BackupPath = ".\.backups\deploy_$(Get-Date -Format 'yyyyMMddHHmmss')",

    [Parameter(Mandatory=$false)]
    [string[]]$Services = @("comfyui-qwen", "comfyui-forge")
)

# --- Configuration ---
$ErrorActionPreference = "Stop"
$LogPrefix = "[DEPLOY-AUTH]"

# --- Fonctions ---

function Write-Log {
    param ([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'
    $logEntry = "$timestamp - $LogPrefix [$Level] $Message"
    Write-Host $logEntry
    # Potentiellement, ajouter à un fichier de log ici
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

Write-Log "🚀 Démarrage du déploiement de la solution d'authentification."

# Étape 1: Création du répertoire de backup
$backupSuccess = Invoke-Step -StepName "Création du répertoire de backup" -Action {
    if (-not (Test-Path -Path $BackupPath)) {
        New-Item -Path $BackupPath -ItemType Directory -Force | Out-Null
    }
    Write-Log "Répertoire de backup: $BackupPath"
}
if (-not $backupSuccess) { exit 1 }

# Étape 2: Sauvegarde de la configuration Docker
$backupDockerSuccess = Invoke-Step -StepName "Sauvegarde de la configuration Docker" -Action {
    if (Test-Path $DockerComposeFile) {
        Copy-Item -Path $DockerComposeFile -Destination $BackupPath
        Write-Log "Fichier '$DockerComposeFile' sauvegardé."
    } else {
        Write-Log "Fichier '$DockerComposeFile' non trouvé, sauvegarde ignorée." -Level "WARN"
    }
}
if (-not $backupDockerSuccess) { exit 1 }

# Étape 3: Arrêt des services
$stopSuccess = Invoke-Step -StepName "Arrêt des services Docker" -Action {
    docker-compose -f $DockerComposeFile stop $Services
}
if (-not $stopSuccess) { exit 1 }

# Étape 4: Démarrage des services avec la nouvelle configuration
$startSuccess = Invoke-Step -StepName "Démarrage des services avec la nouvelle configuration" -Action {
    docker-compose -f $DockerComposeFile up --build -d $Services
}

# Étape 5: Rollback si le démarrage a échoué
if (-not $startSuccess) {
    Write-Log "Le démarrage a échoué. Tentative de rollback..." -Level "CRITICAL"
    $rollbackSuccess = Invoke-Step -StepName "Rollback de la configuration" -Action {
        Copy-Item -Path (Join-Path $BackupPath $DockerComposeFile) -Destination . -Force
        Write-Log "Configuration restaurée depuis '$BackupPath'."
        docker-compose -f $DockerComposeFile up -d $Services
        Write-Log "Services redémarrés avec l'ancienne configuration."
    }
    if ($rollbackSuccess) {
        Write-Log "Rollback terminé. Le système est revenu à l'état précédent." -Level "WARN"
    } else {
        Write-Log "LE ROLLBACK A ÉCHOUÉ. INTERVENTION MANUELLE REQUISE." -Level "FATAL"
    }
    exit 1
}

# Étape 6: Tests de connectivité post-déploiement (simplifié)
$testSuccess = Invoke-Step -StepName "Tests de connectivité post-déploiement" -Action {
    Write-Log "Attente de 15 secondes pour la stabilisation des services..."
    Start-Sleep -Seconds 15
    foreach ($service in $Services) {
        $containerState = docker inspect --format '{{.State.Status}}' $service
        if ($containerState -ne "running") {
            throw "Le service '$service' n'est pas en état 'running' après le redémarrage."
        }
        Write-Log "✅ Le service '$service' est bien en cours d'exécution."
    }
}
if (-not $testSuccess) {
    Write-Log "Les tests post-déploiement ont échoué. Un rollback manuel peut être nécessaire." -Level "ERROR"
    exit 1
}

Write-Log "🎉 Déploiement de la solution d'authentification terminé avec succès!"
exit 0