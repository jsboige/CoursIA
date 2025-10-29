# Script de diagnostic : Liste des containers Docker actifs
# Date : 2025-10-26
# Mission : Phase 26 - Recovery Workflow Qwen

Write-Host "=== CONTAINERS DOCKER ACTIFS ===" -ForegroundColor Cyan

Write-Host "`n📡 Liste complète des containers..." -ForegroundColor Yellow
docker ps -a --format "table {{.ID}}\t{{.Names}}\t{{.Status}}\t{{.Ports}}"

Write-Host "`n🔍 Recherche containers ComfyUI..." -ForegroundColor Yellow
docker ps -a | Select-String -Pattern "comfy" -CaseSensitive:$false

Write-Host "`n✅ Diagnostic terminé" -ForegroundColor Green