# Test de connexion WebSocket ComfyUI
# Date: 2025-10-16
# Objectif: Valider la connexion WebSocket après correction web.config

Write-Host "`n=== Test WebSocket ComfyUI ===" -ForegroundColor Cyan

# Test 1: Vérifier que le service ComfyUI est actif
Write-Host "`n[1/3] Vérification service ComfyUI..." -ForegroundColor Yellow
try {
    $response = Invoke-WebRequest -Uri "http://localhost:8188/system_stats" -UseBasicParsing
    if ($response.StatusCode -eq 200) {
        Write-Host "✅ Service ComfyUI actif (localhost:8188)" -ForegroundColor Green
    }
} catch {
    Write-Host "❌ Service ComfyUI inaccessible" -ForegroundColor Red
    exit 1
}

# Test 2: Vérifier la configuration IIS WebSocket
Write-Host "`n[2/3] Vérification configuration IIS..." -ForegroundColor Yellow
$webConfigPath = "D:\Production\qwen-image-edit.myia.io\web.config"
$webConfigContent = Get-Content $webConfigPath -Raw

if ($webConfigContent -match '<webSocket\s+enabled="true"\s*/?>') {
    Write-Host "✅ Directive WebSocket activée dans web.config" -ForegroundColor Green
} else {
    Write-Host "❌ Directive WebSocket manquante dans web.config" -ForegroundColor Red
    exit 1
}

# Test 3: Test de connexion HTTPS
Write-Host "`n[3/3] Test connexion HTTPS publique..." -ForegroundColor Yellow
try {
    $response = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io" -UseBasicParsing
    if ($response.StatusCode -eq 200) {
        Write-Host "✅ Site accessible via HTTPS" -ForegroundColor Green
    }
} catch {
    Write-Host "❌ Site inaccessible via HTTPS" -ForegroundColor Red
    exit 1
}

Write-Host "`n=== Tests Terminés ===" -ForegroundColor Cyan
Write-Host "✅ Configuration validée - WebSocket devrait fonctionner" -ForegroundColor Green
Write-Host "`nPour tester la connexion WebSocket complète:" -ForegroundColor Yellow
Write-Host "1. Ouvrir https://qwen-image-edit.myia.io dans un navigateur" -ForegroundColor White
Write-Host "2. Ouvrir la Console Développeur (F12)" -ForegroundColor White
Write-Host "3. Vérifier qu'aucune erreur WebSocket n'apparaît" -ForegroundColor White
Write-Host "4. Charger un workflow et cliquer 'Queue Prompt'" -ForegroundColor White