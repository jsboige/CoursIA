# =============================================================================
# Test 1: Démarrage Orchestrator (sans GPU)
# =============================================================================
# Script de test pour l'orchestrator - service léger sans GPU
# Date: 2025-10-08
# =============================================================================

param(
    [switch]$Stop
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
        Write-Section "Arrêt du service orchestrator"
        docker compose -f docker-compose.test.yml down
        Write-Host "✅ Service arrêté" -ForegroundColor Green
        exit 0
    }

    Write-Section "TEST 1: Démarrage Orchestrator (sans GPU)"
    
    # Créer le réseau si nécessaire
    Write-Host "Création du réseau de test..." -ForegroundColor Yellow
    docker network create --driver bridge --subnet 172.21.0.0/16 genai-test-network 2>$null
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Réseau créé" -ForegroundColor Green
    } else {
        Write-Host "ℹ️ Réseau déjà existant" -ForegroundColor Gray
    }
    
    Write-Section "Démarrage du service"
    docker compose -f docker-compose.test.yml up orchestrator -d
    
    if ($LASTEXITCODE -ne 0) {
        Write-Host "❌ Échec du démarrage" -ForegroundColor Red
        exit 1
    }
    
    Write-Host "Attente 10 secondes pour initialisation..." -ForegroundColor Yellow
    Start-Sleep -Seconds 10
    
    Write-Section "Statut du Container"
    docker compose -f docker-compose.test.yml ps
    
    Write-Section "Logs (20 dernières lignes)"
    docker compose -f docker-compose.test.yml logs --tail=20 orchestrator
    
    Write-Section "Test Health Check"
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:8193/health" -UseBasicParsing -TimeoutSec 5
        Write-Host "✅ Health check: OK (Status: $($response.StatusCode))" -ForegroundColor Green
        Write-Host "Response: $($response.Content)" -ForegroundColor Gray
    } catch {
        Write-Host "❌ Health check: FAILED" -ForegroundColor Red
        Write-Host "Erreur: $($_.Exception.Message)" -ForegroundColor Red
    }
    
    Write-Section "Résumé du Test"
    $containerStatus = docker inspect coursia-orchestrator-test --format='{{.State.Status}}' 2>$null
    if ($containerStatus -eq "running") {
        Write-Host "✅ Container: Running" -ForegroundColor Green
    } else {
        Write-Host "❌ Container: $containerStatus" -ForegroundColor Red
    }
    
    Write-Host ""
    Write-Host "Pour arrêter le service:" -ForegroundColor Yellow
    Write-Host "  .\test-01-orchestrator.ps1 -Stop" -ForegroundColor White
    
} catch {
    Write-Host ""
    Write-Host "❌ ERREUR: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}