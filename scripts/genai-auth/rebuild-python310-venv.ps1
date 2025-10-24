# rebuild-python310-venv.ps1 - Reconstruction complète du venv Python 3.10 avec toutes les dépendances

Write-Host "=== RECONSTRUCTION VENV PYTHON 3.10 AVEC DÉPENDANCES ===" -ForegroundColor Cyan
Write-Host "Date: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Write-Host ""

$WSL_COMFYUI_PATH = "/home/jesse/SD/workspace/comfyui-qwen"
$CONTAINER_NAME = "comfyui-qwen"

# Phase 1: Arrêt du container
Write-Host "[1/5] Arrêt du container..." -ForegroundColor Yellow
wsl -d Ubuntu -e bash -c "cd '$WSL_COMFYUI_PATH' && docker-compose down"
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ Container arrêté" -ForegroundColor Green
} else {
    Write-Host "✗ Erreur lors de l'arrêt" -ForegroundColor Red
    exit 1
}

# Phase 2: Suppression de l'ancien venv
Write-Host ""
Write-Host "[2/5] Suppression de l'ancien venv..." -ForegroundColor Yellow
wsl -d Ubuntu -e bash -c "rm -rf '$WSL_COMFYUI_PATH/ComfyUI/venv'"
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ Ancien venv supprimé" -ForegroundColor Green
} else {
    Write-Host "✗ Erreur lors de la suppression" -ForegroundColor Red
    exit 1
}

# Phase 3: Création du nouveau venv avec TOUTES les dépendances (LONG: 2-5 min)
Write-Host ""
Write-Host "[3/5] Création du venv Python 3.10 avec TOUTES les dépendances (ceci peut prendre 2-5 minutes)..." -ForegroundColor Yellow
$createVenvCommand = @"
cd '$WSL_COMFYUI_PATH' && \
docker-compose run --rm $CONTAINER_NAME bash -c ' \
    set -e && \
    apt-get update -qq && \
    apt-get install -y python3 python3-pip python3-venv && \
    cd /workspace/ComfyUI && \
    python3 -m venv venv && \
    source venv/bin/activate && \
    pip install --upgrade pip && \
    pip install -r requirements.txt && \
    pip install pycryptodome bcrypt aiohttp-session && \
    python -c \"from Crypto.Cipher import AES; print(\\"✓ pycryptodome OK\\")\" && \
    python -c \"import bcrypt; print(\\"✓ bcrypt OK\\")\" && \
    python -c \"import aiohttp_session; print(\\"✓ aiohttp_session OK\\")\" && \
    echo VENV_CREATION_COMPLETE \
'
"@

$output = wsl -d Ubuntu -e bash -c $createVenvCommand

if ($output -match "VENV_CREATION_COMPLETE") {
    Write-Host "✓ Venv créé avec toutes les dépendances" -ForegroundColor Green
} else {
    Write-Host "✗ Erreur lors de la création du venv" -ForegroundColor Red
    Write-Host $output
    exit 1
}

# Phase 4: Redémarrage du container
Write-Host ""
Write-Host "[4/5] Redémarrage du container..." -ForegroundColor Yellow
wsl -d Ubuntu -e bash -c "cd '$WSL_COMFYUI_PATH' && docker-compose up -d"
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ Container redémarré" -ForegroundColor Green
} else {
    Write-Host "✗ Erreur lors du redémarrage" -ForegroundColor Red
    exit 1
}

# Phase 5: Attente et vérification
Write-Host ""
Write-Host "[5/5] Attente du démarrage complet (45 secondes)..." -ForegroundColor Yellow
Start-Sleep -Seconds 45

Write-Host ""
Write-Host "=== VÉRIFICATION DES LOGS ===" -ForegroundColor Cyan
$logs = wsl -d Ubuntu -e docker logs --tail 100 $CONTAINER_NAME 2>&1

# Recherche de ComfyUI-Login
if ($logs -match "ComfyUI-Login") {
    Write-Host "✓ ComfyUI-Login détecté dans les logs" -ForegroundColor Green
} else {
    Write-Host "⚠️ ComfyUI-Login NON détecté dans les logs" -ForegroundColor Yellow
}

# Recherche d'erreurs
$errorPatterns = @("ModuleNotFoundError", "No module named", "Cannot import", "IMPORT FAILED")
$foundErrors = $false
foreach ($pattern in $errorPatterns) {
    if ($logs -match $pattern) {
        Write-Host "✗ Erreur détectée: $pattern" -ForegroundColor Red
        $foundErrors = $true
    }
}

if (-not $foundErrors) {
    Write-Host "✓ Aucune erreur de dépendances détectée" -ForegroundColor Green
}

Write-Host ""
Write-Host "=== RÉSUMÉ ===" -ForegroundColor Cyan
if ($foundErrors) {
    Write-Host "❌ ÉCHEC - Des erreurs subsistent" -ForegroundColor Red
    Write-Host ""
    Write-Host "LOGS COMPLETS (50 dernières lignes):" -ForegroundColor Yellow
    wsl -d Ubuntu -e docker logs --tail 50 $CONTAINER_NAME
} else {
    Write-Host "✅ SUCCÈS - Venv Python 3.10 créé avec toutes les dépendances" -ForegroundColor Green
    Write-Host "Vous pouvez maintenant passer aux tests API (Phase 2)" -ForegroundColor Green
}