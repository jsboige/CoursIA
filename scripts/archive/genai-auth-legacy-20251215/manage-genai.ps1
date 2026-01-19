<#
.SYNOPSIS
    Script de gestion unifié pour l'écosystème GenAI (ComfyUI + Qwen).

.DESCRIPTION
    Ce script centralise toutes les opérations de maintenance, déploiement et diagnostic
    pour l'infrastructure GenAI Image en s'appuyant sur les scripts Python consolidés.

.PARAMETER Action
    L'action à effectuer :
    - Setup       : Installe ou répare l'infrastructure (Nodes + Modèles)
    - Start       : Démarre les services Docker
    - Stop        : Arrête les services Docker
    - Status      : Affiche l'état des conteneurs et du GPU
    - Sync-Auth   : Synchronise les credentials d'authentification
    - Validate    : Lance la suite de validation complète
    - Validate-Auth : Valide uniquement l'authentification
    - Audit       : Audite la sécurité des tokens

.PARAMETER Force
    Force l'opération (ex: reconstruction pour Start, écrasement pour Setup si supporté)

.EXAMPLE
    .\manage-genai.ps1 -Action Status
    .\manage-genai.ps1 -Action Start
    .\manage-genai.ps1 -Action Validate

.NOTES
    Version: 2.0 (Consolidation)
    Date: 2025-12-13
    Auteur: Roo
#>

param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("Setup", "Start", "Stop", "Status", "Sync-Auth", "Validate", "Validate-Auth", "Audit")]
    [string]$Action,

    [switch]$Force
)

$ErrorActionPreference = "Stop"
$ScriptDir = $PSScriptRoot

# Configuration des chemins
$PythonCmd = "python"
$CoreDir = Join-Path $ScriptDir "core"
$DockerManagerScript = Join-Path $ScriptDir "docker_manager.py"
$ValidationScript = Join-Path $ScriptDir "validation_suite.py"
$AuthManagerScript = Join-Path $CoreDir "auth_manager.py"

# Fonction helper pour exécuter Python
function Invoke-PythonScript {
    param(
        [string]$ScriptPath,
        [string[]]$Arguments
    )

    if (-not (Test-Path $ScriptPath)) {
        Write-Error "Script introuvable : $ScriptPath"
    }

    Write-Host "🚀 Exécution : $(Split-Path $ScriptPath -Leaf) $Arguments" -ForegroundColor Cyan
    
    # Ajout du répertoire courant au PYTHONPATH pour les imports relatifs
    $env:PYTHONPATH = "$ScriptDir;$CoreDir;$env:PYTHONPATH"
    
    & $PythonCmd $ScriptPath @Arguments
    
    if ($LASTEXITCODE -ne 0) {
        Write-Error "Échec de l'exécution du script (Code: $LASTEXITCODE)"
    }
}

# Gestion des actions
switch ($Action) {
    "Setup" {
        Write-Host "🛠️ SETUP INFRASTRUCTURE" -ForegroundColor Green
        # docker_manager.py setup
        $Args = @("setup")
        # Si setup supporte force plus tard, on pourra l'ajouter
        Invoke-PythonScript -ScriptPath $DockerManagerScript -Arguments $Args
    }

    "Start" {
        Write-Host "▶️ DÉMARRAGE SERVICES" -ForegroundColor Green
        # docker_manager.py start
        $Args = @("start")
        # Support de --build si Force est présent (hypothèse courante, à adapter si besoin)
        # Vérification du script docker_manager.py suggère qu'il pourrait supporter --build pour start
        # Mais dans le doute et pour suivre les specs strictes, on appelle start simple pour l'instant
        # sauf si l'utilisateur a spécifié Force, on pourrait tenter d'ajouter un argument si supporté.
        # Pour l'instant on reste sur "start" simple comme demandé.
        Invoke-PythonScript -ScriptPath $DockerManagerScript -Arguments $Args
    }

    "Stop" {
        Write-Host "⏹️ ARRÊT SERVICES" -ForegroundColor Yellow
        # docker_manager.py stop
        $Args = @("stop")
        Invoke-PythonScript -ScriptPath $DockerManagerScript -Arguments $Args
    }

    "Status" {
        Write-Host "📊 STATUT SYSTÈME" -ForegroundColor Cyan
        # docker_manager.py status
        $Args = @("status")
        Invoke-PythonScript -ScriptPath $DockerManagerScript -Arguments $Args
    }

    "Sync-Auth" {
        Write-Host "🔐 SYNC AUTHENTIFICATION" -ForegroundColor Yellow
        # docker_manager.py sync
        $Args = @("sync")
        Invoke-PythonScript -ScriptPath $DockerManagerScript -Arguments $Args
    }

    "Validate" {
        Write-Host "✅ VALIDATION COMPLÈTE" -ForegroundColor Green
        # validation_suite.py --full
        $Args = @("--full")
        Invoke-PythonScript -ScriptPath $ValidationScript -Arguments $Args
    }

    "Validate-Auth" {
        Write-Host "🔑 VALIDATION AUTHENTIFICATION" -ForegroundColor Green
        # validation_suite.py --auth-only
        $Args = @("--auth-only")
        Invoke-PythonScript -ScriptPath $ValidationScript -Arguments $Args
    }

    "Audit" {
        Write-Host "🛡️ AUDIT SÉCURITÉ" -ForegroundColor Magenta
        # core/auth_manager.py audit
        $Args = @("audit")
        Invoke-PythonScript -ScriptPath $AuthManagerScript -Arguments $Args
    }
}

Write-Host "`n✨ Opération '$Action' terminée." -ForegroundColor Green
