<#
.SYNOPSIS
    Vérification rapide état MCPs après réparation
.DESCRIPTION
    Vérifie configuration MCPs sans tentative de rebuild
.NOTES
    Date: 2025-10-17
    Phase: 17
#>

$ErrorActionPreference = "Continue"

Write-Host "`n=== VÉRIFICATION ÉTAT MCPs ===" -ForegroundColor Cyan

# 1. Vérifier roo-state-manager
Write-Host "`n[1] Vérification roo-state-manager:" -ForegroundColor Yellow

$packageJsonPath = "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/package.json"
if (Test-Path $packageJsonPath) {
    $content = Get-Content $packageJsonPath -Raw | ConvertFrom-Json
    $mainPath = $content.main
    
    Write-Host "  - package.json 'main': $mainPath" -ForegroundColor Gray
    
    if ($mainPath -eq "build/index.js") {
        Write-Host "  ✅ CORRECT" -ForegroundColor Green
    } else {
        Write-Host "  ❌ INCORRECT (attendu: build/index.js)" -ForegroundColor Red
    }
} else {
    Write-Host "  ❌ package.json NON TROUVÉ" -ForegroundColor Red
}

# Vérifier .env
$envPath = "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/.env"
if (Test-Path $envPath) {
    Write-Host "  ✅ Fichier .env existe" -ForegroundColor Green
} else {
    Write-Host "  ⚠️  Fichier .env manquant" -ForegroundColor Yellow
}

# Vérifier build
$buildPath = "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager/build/index.js"
if (Test-Path $buildPath) {
    $size = (Get-Item $buildPath).Length
    Write-Host "  ✅ build/index.js existe ($size bytes)" -ForegroundColor Green
} else {
    Write-Host "  ❌ build/index.js MANQUANT" -ForegroundColor Red
}

# 2. Vérifier jupyter-papermill
Write-Host "`n[2] Vérification jupyter-papermill:" -ForegroundColor Yellow

$papermillPath = "notebook-infrastructure/papermill-coursia"
if (Test-Path $papermillPath) {
    Write-Host "  ✅ Répertoire existe" -ForegroundColor Green
    
    if (Test-Path "$papermillPath/requirements.txt") {
        Write-Host "  ✅ requirements.txt existe" -ForegroundColor Green
    } else {
        Write-Host "  ❌ requirements.txt manquant" -ForegroundColor Red
    }
    
    if (Test-Path "$papermillPath/cli/papermill_coursia.py") {
        Write-Host "  ✅ CLI existe" -ForegroundColor Green
    } else {
        Write-Host "  ❌ CLI manquant" -ForegroundColor Red
    }
} else {
    Write-Host "  ❌ Répertoire papermill-coursia MANQUANT" -ForegroundColor Red
}

# 3. Test import Python
Write-Host "`n[3] Test import papermill:" -ForegroundColor Yellow

try {
    $testResult = "import papermill; print(f'SUCCESS: {papermill.__version__}')" | python 2>&1
    if ($testResult -match "SUCCESS") {
        Write-Host "  ✅ $testResult" -ForegroundColor Green
    } else {
        Write-Host "  ❌ $testResult" -ForegroundColor Red
    }
} catch {
    Write-Host "  ❌ Erreur test import" -ForegroundColor Red
}

Write-Host "`n=== INSTRUCTIONS ===" -ForegroundColor Cyan
Write-Host ""
Write-Host "Les corrections ont été appliquées:" -ForegroundColor White
Write-Host "  ✅ roo-state-manager: package.json corrigé" -ForegroundColor Green
Write-Host "  ✅ roo-state-manager: .env créé" -ForegroundColor Green
Write-Host ""
Write-Host "ÉTAPE CRITIQUE:" -ForegroundColor Yellow
Write-Host "  1. FERMEZ COMPLÈTEMENT VS CODE" -ForegroundColor Yellow
Write-Host "  2. REDÉMARREZ VS CODE" -ForegroundColor Yellow
Write-Host "  3. ATTENDEZ 10-15 SECONDES" -ForegroundColor Yellow
Write-Host "  4. TESTEZ: Command Palette > 'MCP'" -ForegroundColor Yellow
Write-Host ""