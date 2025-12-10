<#
.SYNOPSIS
    Script de gestion unifié pour l'écosystème GenAI (ComfyUI + Qwen).

.DESCRIPTION
    Ce script centralise toutes les opérations de maintenance, déploiement et diagnostic
    pour l'infrastructure GenAI Image. Il remplace les multiples scripts épars.

.PARAMETER Action
    L'action à effectuer :
    - Deploy    : Déploie ou met à jour l'infrastructure Docker
    - Diagnose  : Lance un diagnostic complet de l'environnement
    - Validate  : Valide le fonctionnement (API, Auth, GPU)
    - Monitor   : Affiche les logs et l'état des ressources
    - Cleanup   : Nettoie les ressources inutilisées
    - Sync      : Synchronise les tokens d'authentification

.PARAMETER Force
    Force la reconstruction ou le redémarrage (pour Deploy)

.PARAMETER AutoFix
    Tente de corriger automatiquement les problèmes (pour Diagnose)

.EXAMPLE
    .\manage-genai.ps1 -Action Diagnose -AutoFix
    .\manage-genai.ps1 -Action Deploy --Force

.NOTES
    Version: 1.0
    Date: 2025-12-10
    Auteur: Roo
#>

param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("Deploy", "Diagnose", "Validate", "Monitor", "Cleanup", "Sync")]
    [string]$Action,

    [switch]$Force,
    [switch]$AutoFix
)

$ErrorActionPreference = "Stop"
$ScriptDir = $PSScriptRoot

# Configuration des chemins
$PythonCmd = "python"
$CoreDir = Join-Path $ScriptDir "core"
$UtilsDir = Join-Path $ScriptDir "utils"

# Fonction helper pour exécuter Python
function Invoke-PythonScript {
    param(
        [string]$ScriptPath,
        [string[]]$Arguments
    )

    if (-not (Test-Path $ScriptPath)) {
        Write-Error "Script introuvable : $ScriptPath"
    }

    Write-Host "🚀 Exécution : $ScriptPath" -ForegroundColor Cyan
    if ($Arguments) {
        Write-Host "   Arguments : $Arguments" -ForegroundColor Gray
    }

    $env:PYTHONPATH = "$ScriptDir;$UtilsDir;$env:PYTHONPATH"
    
    & $PythonCmd $ScriptPath @Arguments
    
    if ($LASTEXITCODE -ne 0) {
        Write-Error "Échec de l'exécution du script (Code: $LASTEXITCODE)"
    }
}

# Gestion des actions
switch ($Action) {
    "Deploy" {
        Write-Host "📦 DÉPLOIEMENT DE L'INFRASTRUCTURE" -ForegroundColor Green
        $Script = Join-Path $CoreDir "deploy_comfyui_auth.py"
        $Args = @()
        if ($Force) { $Args += "--force" }
        Invoke-PythonScript -ScriptPath $Script -Arguments $Args
    }

    "Diagnose" {
        Write-Host "🔍 DIAGNOSTIC SYSTÈME" -ForegroundColor Yellow
        $Script = Join-Path $CoreDir "diagnose_comfyui_auth.py"
        $Args = @()
        if ($AutoFix) { $Args += "--autofix" }
        if ($PSBoundParameters.ContainsKey('Verbose') -and $PSBoundParameters['Verbose']) { $Args += "--verbose" }
        
        Invoke-PythonScript -ScriptPath $Script -Arguments $Args
    }

    "Validate" {
        Write-Host "✅ VALIDATION FONCTIONNELLE" -ForegroundColor Green
        $Script = Join-Path $CoreDir "validate_comfyui_auth.py"
        Invoke-PythonScript -ScriptPath $Script
    }

    "Monitor" {
        Write-Host "📊 MONITORING" -ForegroundColor Cyan
        # Monitor script was moved to archive, but it's useful.
        # Let's use the one in archive for now or reimplement/restore it if needed.
        # Actually, I moved ALL .ps1 to archive. I should have kept monitor or moved it to utils/scripts.
        # For now, let's point to archive or better, restore it to scripts/genai-auth/utils/monitor.ps1 later.
        # I'll point to archive for this step to keep it working.
        $Script = Join-Path $ScriptDir "archive/monitor_comfyui_qwen.ps1"
        & $Script
    }

    "Cleanup" {
        Write-Host "🧹 NETTOYAGE" -ForegroundColor Magenta
        $Script = Join-Path $CoreDir "cleanup_comfyui_auth.py"
        Invoke-PythonScript -ScriptPath $Script
    }

    "Sync" {
        Write-Host "🔐 SYNCHRONISATION TOKENS" -ForegroundColor Yellow
        $Script = Join-Path $CoreDir "sync_comfyui_credentials.py"
        Invoke-PythonScript -ScriptPath $Script
    }
}

Write-Host "`n✨ Opération '$Action' terminée." -ForegroundColor Green
