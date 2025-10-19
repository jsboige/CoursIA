<#
.SYNOPSIS
    Réparation MCP roo-state-manager via rebuild TypeScript
.DESCRIPTION
    Répare le MCP roo-state-manager cassé (MODULE_NOT_FOUND) en rebuildan le serveur TypeScript
    Phase 17 - Diagnostic + Réparation MCP
.NOTES
    Date: 2025-10-16
    Phase: 17
    Auteur: SDDD Process
    Usage: pwsh -c "& './2025-10-16_02_reparer-roo-state-manager.ps1'"
#>

$ErrorActionPreference = "Continue"
$StartTime = Get-Date

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   PHASE 17: RÉPARATION MCP ROO-STATE-MANAGER ║" -ForegroundColor Cyan
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Configuration
$ServerPath = "D:\Dev\roo-extensions\mcps\internal\servers\roo-state-manager"
$BuildOutputPath = "$ServerPath\build\src\index.js"
$ReportPath = "../rapports/2025-10-16_17_reparation-roo-state-manager.md"

# Initialisation rapport
$Report = @"
# Réparation MCP roo-state-manager - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

**Machine**: $env:COMPUTERNAME
**User**: $env:USERNAME
**Serveur**: roo-state-manager

---

## Diagnostic Initial

**Erreur identifiée**:
``````
Error: Cannot find module '$BuildOutputPath'
code: 'MODULE_NOT_FOUND'
``````

**Root Cause**: Build TypeScript non exécuté ou corrompu

---

## Étapes de Réparation

"@

Write-Host "📍 [1/6] Vérification répertoire serveur..." -ForegroundColor Yellow

if (Test-Path $ServerPath) {
    Write-Host "     ✅ Répertoire serveur existe: $ServerPath" -ForegroundColor Green
    $Report += "`n### 1. Vérification Répertoire`n`n- **Status**: ✅ Répertoire existe`n- **Path**: ``$ServerPath```n"
} else {
    Write-Host "     ❌ ERREUR: Répertoire serveur manquant: $ServerPath" -ForegroundColor Red
    $Report += "`n### 1. Vérification Répertoire`n`n- **Status**: ❌ ERREUR - Répertoire manquant`n- **Path**: ``$ServerPath```n"
    $Report += "`n## Conclusion`n`n❌ **ÉCHEC**: Impossible de réparer - répertoire serveur manquant`n"
    
    New-Item -ItemType Directory -Force -Path (Split-Path $ReportPath -Parent) | Out-Null
    Set-Content -Path $ReportPath -Value $Report -Encoding UTF8
    
    Write-Host ""
    Write-Host "❌ ÉCHEC: Répertoire serveur manquant" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "📍 [2/6] Vérification fichiers configuration..." -ForegroundColor Yellow

$hasPackageJson = Test-Path "$ServerPath\package.json"
$hasTsConfig = Test-Path "$ServerPath\tsconfig.json"

if ($hasPackageJson -and $hasTsConfig) {
    Write-Host "     ✅ package.json et tsconfig.json présents" -ForegroundColor Green
    $Report += "`n### 2. Fichiers Configuration`n`n- **package.json**: ✅ Présent`n- **tsconfig.json**: ✅ Présent`n"
} else {
    Write-Host "     ⚠️  Fichiers configuration manquants:" -ForegroundColor Yellow
    if (-not $hasPackageJson) { Write-Host "        - package.json manquant" -ForegroundColor Yellow }
    if (-not $hasTsConfig) { Write-Host "        - tsconfig.json manquant" -ForegroundColor Yellow }
    
    $Report += "`n### 2. Fichiers Configuration`n`n"
    $Report += "- **package.json**: $(if ($hasPackageJson) { '✅ Présent' } else { '❌ Manquant' })`n"
    $Report += "- **tsconfig.json**: $(if ($hasTsConfig) { '✅ Présent' } else { '❌ Manquant' })`n"
}

Write-Host ""
Write-Host "📍 [3/6] Nettoyage builds précédents..." -ForegroundColor Yellow

if (Test-Path "$ServerPath\build") {
    try {
        Remove-Item -Path "$ServerPath\build" -Recurse -Force -ErrorAction Stop
        Write-Host "     ✅ Répertoire build supprimé" -ForegroundColor Green
        $Report += "`n### 3. Nettoyage`n`n- **Status**: ✅ Répertoire build supprimé`n"
    } catch {
        Write-Host "     ⚠️  Impossible de supprimer build: $_" -ForegroundColor Yellow
        $Report += "`n### 3. Nettoyage`n`n- **Status**: ⚠️ Erreur suppression: ``$_```n"
    }
} else {
    Write-Host "     ℹ️  Pas de répertoire build à nettoyer" -ForegroundColor Gray
    $Report += "`n### 3. Nettoyage`n`n- **Status**: ℹ️ Aucun build précédent`n"
}

if (Test-Path "$ServerPath\node_modules") {
    try {
        Remove-Item -Path "$ServerPath\node_modules" -Recurse -Force -ErrorAction Stop
        Write-Host "     ✅ Répertoire node_modules supprimé" -ForegroundColor Green
        $Report += "- **node_modules**: ✅ Supprimé`n"
    } catch {
        Write-Host "     ⚠️  Impossible de supprimer node_modules: $_" -ForegroundColor Yellow
        $Report += "- **node_modules**: ⚠️ Erreur suppression`n"
    }
} else {
    Write-Host "     ℹ️  Pas de node_modules à nettoyer" -ForegroundColor Gray
}

Write-Host ""
Write-Host "📍 [4/6] Installation dépendances npm..." -ForegroundColor Yellow

try {
    Push-Location $ServerPath
    
    $npmInstallOutput = & npm install 2>&1
    $npmInstallExitCode = $LASTEXITCODE
    
    if ($npmInstallExitCode -eq 0) {
        Write-Host "     ✅ npm install réussi" -ForegroundColor Green
        $Report += "`n### 4. Installation Dépendances`n`n- **Status**: ✅ SUCCESS`n- **Commande**: ``npm install```n"
    } else {
        Write-Host "     ❌ npm install échoué (code: $npmInstallExitCode)" -ForegroundColor Red
        Write-Host $npmInstallOutput -ForegroundColor Gray
        $Report += "`n### 4. Installation Dépendances`n`n- **Status**: ❌ FAILED`n- **Exit Code**: $npmInstallExitCode`n``````text`n$npmInstallOutput`n```````n"
    }
} catch {
    Write-Host "     ❌ Erreur npm install: $_" -ForegroundColor Red
    $Report += "`n### 4. Installation Dépendances`n`n- **Status**: ❌ ERROR`n- **Erreur**: ``$_```n"
} finally {
    Pop-Location
}

Write-Host ""
Write-Host "📍 [5/6] Build TypeScript..." -ForegroundColor Yellow

try {
    Push-Location $ServerPath
    
    $npmBuildOutput = & npm run build 2>&1
    $npmBuildExitCode = $LASTEXITCODE
    
    if ($npmBuildExitCode -eq 0) {
        Write-Host "     ✅ npm run build réussi" -ForegroundColor Green
        $Report += "`n### 5. Build TypeScript`n`n- **Status**: ✅ SUCCESS`n- **Commande**: ``npm run build```n"
    } else {
        Write-Host "     ❌ npm run build échoué (code: $npmBuildExitCode)" -ForegroundColor Red
        Write-Host $npmBuildOutput -ForegroundColor Gray
        $Report += "`n### 5. Build TypeScript`n`n- **Status**: ❌ FAILED`n- **Exit Code**: $npmBuildExitCode`n``````text`n$npmBuildOutput`n```````n"
    }
} catch {
    Write-Host "     ❌ Erreur npm run build: $_" -ForegroundColor Red
    $Report += "`n### 5. Build TypeScript`n`n- **Status**: ❌ ERROR`n- **Erreur**: ``$_```n"
} finally {
    Pop-Location
}

Write-Host ""
Write-Host "📍 [6/6] Validation fichier output..." -ForegroundColor Yellow

if (Test-Path $BuildOutputPath) {
    $fileSize = (Get-Item $BuildOutputPath).Length
    Write-Host "     ✅ Fichier index.js généré ($fileSize octets)" -ForegroundColor Green
    $Report += "`n### 6. Validation Output`n`n- **Status**: ✅ Fichier généré`n- **Path**: ``$BuildOutputPath```n- **Taille**: $fileSize octets`n"
    
    $success = $true
} else {
    Write-Host "     ❌ Fichier index.js manquant après build" -ForegroundColor Red
    $Report += "`n### 6. Validation Output`n`n- **Status**: ❌ Fichier manquant`n- **Path attendu**: ``$BuildOutputPath```n"
    
    $success = $false
}

# Synthèse finale
$Report += "`n---`n`n## Synthèse Réparation`n`n"

if ($success) {
    $Report += "### ✅ SUCCÈS`n`n"
    $Report += "Le MCP roo-state-manager a été réparé avec succès:`n`n"
    $Report += "- Build TypeScript complété`n"
    $Report += "- Fichier ``index.js`` généré`n"
    $Report += "- Serveur prêt à démarrer`n`n"
    $Report += "**Action suivante**: Redémarrer le serveur MCP via Roo pour validation`n"
} else {
    $Report += "### ❌ ÉCHEC`n`n"
    $Report += "La réparation a échoué. Vérifier les logs ci-dessus pour diagnostic.`n"
}

$EndTime = Get-Date
$Duration = $EndTime - $StartTime

$Report += "`n---`n`n"
$Report += "**Durée réparation**: $($Duration.TotalSeconds) secondes`n"
$Report += "*Rapport généré automatiquement - Phase 17 SDDD*`n"

# Sauvegarde rapport
New-Item -ItemType Directory -Force -Path (Split-Path $ReportPath -Parent) | Out-Null
Set-Content -Path $ReportPath -Value $Report -Encoding UTF8

Write-Host ""
if ($success) {
    Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Green
    Write-Host "║   ✅ RÉPARATION RÉUSSIE                       ║" -ForegroundColor Green
    Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Green
} else {
    Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Red
    Write-Host "║   ❌ RÉPARATION ÉCHOUÉE                       ║" -ForegroundColor Red
    Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Red
}
Write-Host ""
Write-Host "📊 Rapport: $ReportPath" -ForegroundColor Cyan
Write-Host "⏱️  Durée: $($Duration.TotalSeconds) secondes" -ForegroundColor Cyan
Write-Host ""

if ($success) {
    Write-Host "🔄 Redémarrer le serveur MCP roo-state-manager via Roo pour finaliser la réparation" -ForegroundColor Yellow
    exit 0
} else {
    exit 1
}