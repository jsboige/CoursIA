<#
.SYNOPSIS
    Validation réparation MCP roo-state-manager
.DESCRIPTION
    Teste le démarrage et la fonctionnalité du MCP roo-state-manager après correction package.json
    Phase 17 - Diagnostic + Réparation MCP
.NOTES
    Date: 2025-10-16
    Phase: 17
    Auteur: SDDD Process
    Usage: pwsh -c "& './2025-10-16_03_valider-roo-state-manager.ps1'"
#>

$ErrorActionPreference = "Continue"
$StartTime = Get-Date

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   PHASE 17: VALIDATION ROO-STATE-MANAGER     ║" -ForegroundColor Cyan
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Configuration
$ServerPath = "D:\Dev\roo-extensions\mcps\internal\servers\roo-state-manager"
$ReportPath = "../rapports/2025-10-16_17_validation-roo-state-manager.md"
$BuildOutputPath = "$ServerPath\build\index.js"

# Initialisation rapport
$Report = @"
# Validation Réparation roo-state-manager - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

**Machine**: $env:COMPUTERNAME
**User**: $env:USERNAME
**Workspace**: $PWD

---

## 1. Vérification Fichier Build

"@

Write-Host "📍 [1/4] Vérification fichier build..." -ForegroundColor Yellow

if (Test-Path $BuildOutputPath) {
    Write-Host "     ✅ Fichier build trouvé: $BuildOutputPath" -ForegroundColor Green
    $Report += "`n- **Fichier build**: ✅ Présent à ``$BuildOutputPath```n"
} else {
    Write-Host "     ❌ Fichier build manquant: $BuildOutputPath" -ForegroundColor Red
    $Report += "`n- **Fichier build**: ❌ Manquant`n"
    Write-Host ""
    Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Red
    Write-Host "║   ❌ VALIDATION ÉCHOUÉE - BUILD MANQUANT     ║" -ForegroundColor Red
    Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "📍 [2/4] Vérification package.json..." -ForegroundColor Yellow

$packageJsonPath = "$ServerPath\package.json"
if (Test-Path $packageJsonPath) {
    $packageJson = Get-Content $packageJsonPath -Raw | ConvertFrom-Json
    $mainEntry = $packageJson.main
    
    if ($mainEntry -eq "build/index.js") {
        Write-Host "     ✅ package.json correctement configuré: main = $mainEntry" -ForegroundColor Green
        $Report += "`n## 2. Configuration package.json`n`n- **main**: ✅ ``$mainEntry```n"
    } else {
        Write-Host "     ❌ package.json incorrectement configuré: main = $mainEntry" -ForegroundColor Red
        $Report += "`n## 2. Configuration package.json`n`n- **main**: ❌ ``$mainEntry`` (attendu: ``build/index.js``)`n"
        Write-Host ""
        Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Red
        Write-Host "║   ❌ VALIDATION ÉCHOUÉE - CONFIG INCORRECTE  ║" -ForegroundColor Red
        Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "     ❌ package.json non trouvé" -ForegroundColor Red
    $Report += "`n## 2. Configuration package.json`n`n- **Status**: ❌ Fichier non trouvé`n"
    exit 1
}

Write-Host ""
Write-Host "📍 [3/4] Test import Node.js..." -ForegroundColor Yellow

try {
    $importTest = @"
const path = require('path');
const serverPath = path.join('$ServerPath', 'build', 'index.js');
console.log('Attempting to load:', serverPath);
try {
    const server = require(serverPath);
    console.log('SUCCESS: Module loaded');
    console.log('Exports:', Object.keys(server || {}));
} catch (err) {
    console.error('ERROR:', err.message);
    process.exit(1);
}
"@
    
    $testResult = $importTest | node 2>&1
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "     ✅ Import Node.js réussi" -ForegroundColor Green
        $Report += "`n## 3. Test Import Node.js`n`n- **Status**: ✅ SUCCESS`n``````text`n$testResult`n```````n"
    } else {
        Write-Host "     ❌ Import Node.js échoué" -ForegroundColor Red
        $Report += "`n## 3. Test Import Node.js`n`n- **Status**: ❌ FAILED`n``````text`n$testResult`n```````n"
        Write-Host ""
        Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Red
        Write-Host "║   ❌ VALIDATION ÉCHOUÉE - IMPORT ÉCHOUÉ      ║" -ForegroundColor Red
        Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Red
        exit 1
    }
} catch {
    Write-Host "     ❌ Erreur test import: $_" -ForegroundColor Red
    $Report += "`n## 3. Test Import Node.js`n`n- **Status**: ❌ ERROR`n``````text`n$_`n```````n"
    exit 1
}

Write-Host ""
Write-Host "📍 [4/4] Synthèse validation..." -ForegroundColor Yellow

$Report += @"

---

## 4. Synthèse Validation

### Status Global

✅ **VALIDATION RÉUSSIE**

### Vérifications Passées

1. ✅ Fichier build présent à ``build/index.js``
2. ✅ ``package.json`` correctement configuré avec ``"main": "build/index.js"``
3. ✅ Module Node.js charge sans erreur

### Prochaine Étape

Le MCP ``roo-state-manager`` est maintenant réparé et prêt à être utilisé.

**Action requise**: Redémarrer VS Code ou recharger la fenêtre pour que le MCP soit détecté.

---

**Durée validation**: $((Get-Date) - $StartTime)
*Rapport généré automatiquement - Phase 17 SDDD*
"@

# Sauvegarde rapport
New-Item -ItemType Directory -Force -Path (Split-Path $ReportPath -Parent) | Out-Null
Set-Content -Path $ReportPath -Value $Report -Encoding UTF8

$EndTime = Get-Date
$Duration = $EndTime - $StartTime

Write-Host ""
Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║   ✅ VALIDATION RÉUSSIE                       ║" -ForegroundColor Green
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""
Write-Host "📊 Rapport: $ReportPath" -ForegroundColor Cyan
Write-Host "⏱️  Durée: $($Duration.TotalSeconds) secondes" -ForegroundColor Cyan
Write-Host ""
Write-Host "⚠️  ACTION REQUISE: Redémarrer VS Code pour appliquer les changements MCP" -ForegroundColor Yellow
Write-Host ""