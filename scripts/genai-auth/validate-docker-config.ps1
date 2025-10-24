# validate-docker-config.ps1 - Validation complète de la configuration Docker ComfyUI avec authentification

Write-Host "=== VALIDATION CONFIGURATION DOCKER COMFYUI ===" -ForegroundColor Cyan
Write-Host "Date: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Write-Host ""

$WSL_COMFYUI_PATH = "/home/jesse/SD/workspace/comfyui-qwen"
$CONTAINER_NAME = "comfyui-qwen"

# Phase 1: Vérification de l'existence du venv
Write-Host "[1/6] Vérification de l'existence du venv..." -ForegroundColor Yellow
$venvCheck = wsl -d Ubuntu -e bash -c "test -d '$WSL_COMFYUI_PATH/ComfyUI/venv' && echo 'EXISTS' || echo 'MISSING'"
if ($venvCheck -match "EXISTS") {
    Write-Host "✓ Venv existe sur le disque" -ForegroundColor Green
} else {
    Write-Host "✗ Venv manquant - Exécution du script de création..." -ForegroundColor Red
    wsl -d Ubuntu -e bash /mnt/d/Dev/CoursIA/scripts/genai-auth/recreate-venv-in-container.sh
    exit
}

# Phase 2: Installation des dépendances manquantes dans le venv
Write-Host ""
Write-Host "[2/6] Installation des dépendances ComfyUI-Login dans le venv..." -ForegroundColor Yellow
$installResult = wsl -d Ubuntu -e bash -c @"
cd '$WSL_COMFYUI_PATH/ComfyUI' && \
source venv/bin/activate && \
pip install --quiet pycryptodome bcrypt aiohttp-session && \
python -c 'from Crypto.Cipher import AES; print(\"CRYPTO_OK\")' && \
python -c 'import bcrypt; print(\"BCRYPT_OK\")' && \
python -c 'import aiohttp_session; print(\"AIOHTTP_OK\")'
"@

if ($installResult -match "CRYPTO_OK" -and $installResult -match "BCRYPT_OK" -and $installResult -match "AIOHTTP_OK") {
    Write-Host "✓ Toutes les dépendances installées avec succès" -ForegroundColor Green
} else {
    Write-Host "✗ Erreur lors de l'installation des dépendances" -ForegroundColor Red
    Write-Host $installResult
    exit 1
}

# Phase 3: Redémarrage du container
Write-Host ""
Write-Host "[3/6] Redémarrage du container pour appliquer les changements..." -ForegroundColor Yellow
wsl -d Ubuntu -e bash -c "cd '$WSL_COMFYUI_PATH' && docker-compose restart $CONTAINER_NAME"
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ Container redémarré" -ForegroundColor Green
} else {
    Write-Host "✗ Erreur lors du redémarrage" -ForegroundColor Red
    exit 1
}

# Phase 4: Attente du démarrage complet
Write-Host ""
Write-Host "[4/6] Attente du démarrage complet (45 secondes)..." -ForegroundColor Yellow
Start-Sleep -Seconds 45

# Phase 5: Vérification des logs
Write-Host ""
Write-Host "[5/6] Vérification des logs de démarrage..." -ForegroundColor Yellow
$logs = wsl -d Ubuntu -e docker logs --tail 100 $CONTAINER_NAME 2>&1

# Recherche de ComfyUI-Login
if ($logs -match "ComfyUI-Login") {
    Write-Host "✓ ComfyUI-Login détecté dans les logs" -ForegroundColor Green
} else {
    Write-Host "⚠️ ComfyUI-Login NON détecté dans les logs" -ForegroundColor Yellow
}

# Recherche d'erreurs de dépendances
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

# Phase 6: Test de l'endpoint API
Write-Host ""
Write-Host "[6/6] Test de l'endpoint API (sans authentification)..." -ForegroundColor Yellow
try {
    $response = Invoke-WebRequest -Uri "http://localhost:8188/system_stats" -Method GET -ErrorAction SilentlyContinue
    if ($response.StatusCode -eq 401) {
        Write-Host "✓ API répond avec 401 (authentification requise) - COMPORTEMENT ATTENDU" -ForegroundColor Green
    } elseif ($response.StatusCode -eq 200) {
        Write-Host "⚠️ API répond avec 200 (pas d'authentification) - ComfyUI-Login NON ACTIF" -ForegroundColor Yellow
    } else {
        Write-Host "⚠️ API répond avec code $($response.StatusCode)" -ForegroundColor Yellow
    }
} catch {
    $statusCode = $_.Exception.Response.StatusCode.value__
    if ($statusCode -eq 401) {
        Write-Host "✓ API répond avec 401 (authentification requise) - COMPORTEMENT ATTENDU" -ForegroundColor Green
    } else {
        Write-Host "✗ Erreur lors du test API: $_" -ForegroundColor Red
    }
}

Write-Host ""
Write-Host "=== RÉSUMÉ DE LA VALIDATION ===" -ForegroundColor Cyan
if ($foundErrors) {
    Write-Host "❌ ÉCHEC - Des erreurs de dépendances subsistent" -ForegroundColor Red
    Write-Host ""
    Write-Host "LOGS COMPLETS (50 dernières lignes):" -ForegroundColor Yellow
    Write-Host "-----------------------------------"
    wsl -d Ubuntu -e docker logs --tail 50 $CONTAINER_NAME
} else {
    Write-Host "✅ SUCCÈS - Configuration Docker validée" -ForegroundColor Green
}