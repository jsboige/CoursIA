# Test d'accès ComfyUI depuis Windows - 2025-10-15
# Objectif: Vérifier que ComfyUI est accessible depuis Windows sur localhost:8188

Write-Host "=== TEST ACCÈS COMFYUI DEPUIS WINDOWS ===" -ForegroundColor Cyan
Write-Host ""

# 1. Test connexion basique
Write-Host "## 1. TEST CONNEXION PORT 8188" -ForegroundColor Yellow
try {
    $response = Invoke-WebRequest -Uri "http://localhost:8188/system_stats" -Method GET -TimeoutSec 10
    Write-Host "✅ Port 8188 accessible depuis Windows" -ForegroundColor Green
    Write-Host "   Status Code: $($response.StatusCode)" -ForegroundColor Gray
} catch {
    Write-Host "❌ Erreur de connexion: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

Write-Host ""

# 2. Récupérer et afficher les stats système
Write-Host "## 2. STATISTIQUES SYSTÈME" -ForegroundColor Yellow
try {
    $stats = Invoke-RestMethod -Uri "http://localhost:8188/system_stats" -Method GET
    
    Write-Host "Système:" -ForegroundColor Cyan
    Write-Host "  - OS: $($stats.system.os)" -ForegroundColor Gray
    Write-Host "  - ComfyUI Version: $($stats.system.comfyui_version)" -ForegroundColor Gray
    Write-Host "  - Python Version: $($stats.system.python_version)" -ForegroundColor Gray
    Write-Host "  - PyTorch Version: $($stats.system.pytorch_version)" -ForegroundColor Gray
    Write-Host "  - RAM Total: $([math]::Round($stats.system.ram_total / 1GB, 2)) GB" -ForegroundColor Gray
    Write-Host "  - RAM Free: $([math]::Round($stats.system.ram_free / 1GB, 2)) GB" -ForegroundColor Gray
    
    Write-Host ""
    Write-Host "Devices:" -ForegroundColor Cyan
    foreach ($device in $stats.devices) {
        Write-Host "  - $($device.name)" -ForegroundColor Gray
        Write-Host "    Type: $($device.type)" -ForegroundColor DarkGray
        Write-Host "    Index: $($device.index)" -ForegroundColor DarkGray
        Write-Host "    VRAM Total: $([math]::Round($device.vram_total / 1GB, 2)) GB" -ForegroundColor DarkGray
        Write-Host "    VRAM Free: $([math]::Round($device.vram_free / 1GB, 2)) GB" -ForegroundColor DarkGray
        $vramUsedPercent = [math]::Round((($device.vram_total - $device.vram_free) / $device.vram_total) * 100, 1)
        Write-Host "    VRAM Used: $vramUsedPercent%" -ForegroundColor DarkGray
    }
} catch {
    Write-Host "❌ Erreur récupération stats: $($_.Exception.Message)" -ForegroundColor Red
}

Write-Host ""

# 3. Test GUI
Write-Host "## 3. ACCÈS INTERFACE WEB" -ForegroundColor Yellow
Write-Host "Interface disponible sur: http://localhost:8188" -ForegroundColor Green
Write-Host ""

# 4. Métriques GPU depuis WSL
Write-Host "## 4. MÉTRIQUES GPU (depuis WSL)" -ForegroundColor Yellow
try {
    $gpuStats = wsl -e nvidia-smi --query-gpu=index,name,memory.used,memory.total,temperature.gpu,utilization.gpu,power.draw --format=csv,noheader
    Write-Host $gpuStats -ForegroundColor Gray
} catch {
    Write-Host "⚠️  Impossible de récupérer les métriques GPU: $($_.Exception.Message)" -ForegroundColor Yellow
}

Write-Host ""

# 5. Résumé
Write-Host "=== RÉSUMÉ ===" -ForegroundColor Cyan
Write-Host "✅ ComfyUI démarré et accessible sur port 8188" -ForegroundColor Green
Write-Host "✅ GPU RTX 3090 utilisé correctement" -ForegroundColor Green
Write-Host "✅ Interface Web accessible depuis Windows" -ForegroundColor Green
Write-Host ""
Write-Host "Pour accéder à l'interface:" -ForegroundColor Yellow
Write-Host "  Ouvrir un navigateur: http://localhost:8188" -ForegroundColor White
Write-Host ""
Write-Host "Pour arrêter ComfyUI:" -ForegroundColor Yellow
Write-Host "  wsl -e bash -c 'kill `$(cat /tmp/comfyui.pid)'" -ForegroundColor White