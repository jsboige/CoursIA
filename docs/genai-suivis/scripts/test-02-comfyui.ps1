# =============================================================================
# Test 2: Démarrage ComfyUI Minimal (avec GPU)
# =============================================================================
# Script de test pour ComfyUI - nécessite GPU NVIDIA
# ⚠️ ATTENTION: Télécharge l'image Docker (~5-10GB) au premier lancement
# Date: 2025-10-08
# =============================================================================

param(
    [switch]$Stop,
    [switch]$Force
)

$ErrorActionPreference = "Stop"

function Write-Section {
    param([string]$Title)
    Write-Host ""
    Write-Host "=== $Title ===" -ForegroundColor Cyan
    Write-Host ""
}

try {
    if ($Stop) {
        Write-Section "Arrêt du service ComfyUI"
        docker compose -f ../../../docker-compose.test.yml down comfyui-test
        Write-Host "✅ Service arrêté" -ForegroundColor Green
        exit 0
    }

    Write-Section "TEST 2: Démarrage ComfyUI Minimal (avec GPU)"
    
    # Vérifier si l'image existe
    $imageExists = docker images -q comfyanonymous/comfyui:latest-cu121 2>$null
    if (-not $imageExists -and -not $Force) {
        Write-Host "⚠️ L'image Docker n'existe pas localement" -ForegroundColor Yellow
        Write-Host "   Taille estimée: ~5-10 GB" -ForegroundColor Yellow
        Write-Host "   Temps estimé: 10-30 minutes (selon connexion)" -ForegroundColor Yellow
        Write-Host ""
        Write-Host "Pour continuer, relancer avec -Force:" -ForegroundColor Yellow
        Write-Host "   .\test-02-comfyui.ps1 -Force" -ForegroundColor White
        exit 0
    }
    
    # Vérifier GPU NVIDIA
    Write-Section "Vérification GPU NVIDIA"
    $gpuCheck = docker run --rm --gpus all nvidia/cuda:11.8.0-base-ubuntu22.04 nvidia-smi 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ GPU NVIDIA détecté" -ForegroundColor Green
    } else {
        Write-Host "❌ GPU NVIDIA non détecté ou Docker GPU support non configuré" -ForegroundColor Red
        Write-Host "   Vérifier: Docker Desktop → Settings → Resources → WSL Integration" -ForegroundColor Yellow
        exit 1
    }
    
    Write-Section "Démarrage du service"
    if (-not $imageExists) {
        Write-Host "📥 Téléchargement de l'image en cours..." -ForegroundColor Yellow
        Write-Host "   (Ceci peut prendre 10-30 minutes)" -ForegroundColor Gray
    }
    
    docker compose -f ../../../docker-compose.test.yml up comfyui-test -d
    
    if ($LASTEXITCODE -ne 0) {
        Write-Host "❌ Échec du démarrage" -ForegroundColor Red
        exit 1
    }
    
    Write-Host "Attente 15 secondes pour initialisation..." -ForegroundColor Yellow
    Start-Sleep -Seconds 15
    
    Write-Section "Statut du Container"
    docker compose -f ../../../docker-compose.test.yml ps
    
    Write-Section "Logs (30 dernières lignes)"
    docker compose -f ../../../docker-compose.test.yml logs --tail=30 comfyui-test
    
    Write-Section "Vérification GPU dans le container"
    docker exec coursia-comfyui-test nvidia-smi 2>$null
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ GPU accessible dans le container" -ForegroundColor Green
    } else {
        Write-Host "⚠️ GPU non accessible dans le container" -ForegroundColor Yellow
    }
    
    Write-Section "Test Health Check"
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:8191/system_stats" -UseBasicParsing -TimeoutSec 10
        Write-Host "✅ Health check: OK (Status: $($response.StatusCode))" -ForegroundColor Green
    } catch {
        Write-Host "⚠️ Health check: En attente" -ForegroundColor Yellow
        Write-Host "   (ComfyUI peut prendre 1-2 minutes pour être complètement prêt)" -ForegroundColor Gray
    }
    
    Write-Section "Résumé du Test"
    $containerStatus = docker inspect coursia-comfyui-test --format='{{.State.Status}}' 2>$null
    if ($containerStatus -eq "running") {
        Write-Host "✅ Container: Running" -ForegroundColor Green
        Write-Host ""
        Write-Host "Interface web accessible sur:" -ForegroundColor Yellow
        Write-Host "   http://localhost:8191" -ForegroundColor White
    } else {
        Write-Host "❌ Container: $containerStatus" -ForegroundColor Red
    }
    
    Write-Host ""
    Write-Host "Pour arrêter le service:" -ForegroundColor Yellow
    Write-Host "   .\test-02-comfyui.ps1 -Stop" -ForegroundColor White
    
} catch {
    Write-Host ""
    Write-Host "❌ ERREUR: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}