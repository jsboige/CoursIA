# Script d'installation de la tâche planifiée Windows pour ComfyUI
# Phase 12A: Production ComfyUI + Qwen Image-Edit
# Date: 2025-10-14

$TaskName = "ComfyUI-Qwen-Startup"
$ScriptPath = Join-Path $PSScriptRoot "2025-10-14_12A_start-comfyui-watchdog.ps1"

Write-Host ""
Write-Host "╔════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║  Installation Tâche Planifiée ComfyUI - Phase 12A     ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Vérifier si exécuté en admin
$isAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
if (-not $isAdmin) {
    Write-Host "❌ ERREUR: Ce script doit être exécuté en tant qu'Administrateur" -ForegroundColor Red
    Write-Host "   Clic droit > Exécuter en tant qu'administrateur" -ForegroundColor Yellow
    exit 1
}

# Vérifier si le script watchdog existe
if (-not (Test-Path $ScriptPath)) {
    Write-Host "❌ ERREUR: Script watchdog introuvable: $ScriptPath" -ForegroundColor Red
    exit 1
}

Write-Host "✅ Script watchdog trouvé: $ScriptPath" -ForegroundColor Green

# Supprimer tâche si existe
$existingTask = Get-ScheduledTask -TaskName $TaskName -ErrorAction SilentlyContinue
if ($existingTask) {
    Write-Host "⚠️ Tâche existante trouvée, suppression..." -ForegroundColor Yellow
    Unregister-ScheduledTask -TaskName $TaskName -Confirm:$false
    Write-Host "✅ Ancienne tâche supprimée" -ForegroundColor Green
}

# Créer nouvelle tâche
Write-Host ""
Write-Host "📝 Création de la tâche planifiée..." -ForegroundColor Cyan

$Action = New-ScheduledTaskAction -Execute "PowerShell.exe" `
    -Argument "-NoProfile -ExecutionPolicy Bypass -WindowStyle Hidden -File `"$ScriptPath`" -monitor"

$Trigger = New-ScheduledTaskTrigger -AtStartup

$Settings = New-ScheduledTaskSettingsSet `
    -AllowStartIfOnBatteries `
    -DontStopIfGoingOnBatteries `
    -StartWhenAvailable `
    -RestartInterval (New-TimeSpan -Minutes 1) `
    -RestartCount 3 `
    -ExecutionTimeLimit (New-TimeSpan -Hours 0)

# Exécuter en tant qu'utilisateur actuel avec privilèges élevés
$Principal = New-ScheduledTaskPrincipal -UserId $env:USERNAME -LogonType Interactive -RunLevel Highest

try {
    Register-ScheduledTask -TaskName $TaskName `
        -Action $Action `
        -Trigger $Trigger `
        -Settings $Settings `
        -Principal $Principal `
        -Description "Démarre et monitore ComfyUI + Qwen Image-Edit sur GPU RTX 3090 (Phase 12A Production)" | Out-Null
    
    Write-Host "✅ Tâche planifiée '$TaskName' créée avec succès!" -ForegroundColor Green
}
catch {
    Write-Host "❌ ERREUR lors de la création de la tâche: $_" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "╔════════════════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║              Configuration Terminée!                    ║" -ForegroundColor Green
Write-Host "╚════════════════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""
Write-Host "📋 Commandes utiles:" -ForegroundColor Cyan
Write-Host ""
Write-Host "  Démarrer maintenant:" -ForegroundColor Yellow
Write-Host "    Start-ScheduledTask -TaskName '$TaskName'" -ForegroundColor White
Write-Host ""
Write-Host "  Arrêter:" -ForegroundColor Yellow
Write-Host "    Stop-ScheduledTask -TaskName '$TaskName'" -ForegroundColor White
Write-Host ""
Write-Host "  Voir statut:" -ForegroundColor Yellow
Write-Host "    Get-ScheduledTask -TaskName '$TaskName' | Format-List" -ForegroundColor White
Write-Host ""
Write-Host "  Désinstaller:" -ForegroundColor Yellow
Write-Host "    Unregister-ScheduledTask -TaskName '$TaskName' -Confirm:`$false" -ForegroundColor White
Write-Host ""
Write-Host "📂 Logs disponibles dans:" -ForegroundColor Cyan
Write-Host "    docs/genai-suivis/logs/comfyui-production/" -ForegroundColor White
Write-Host ""
Write-Host "💡 La tâche démarrera automatiquement au prochain boot Windows" -ForegroundColor Yellow
Write-Host ""