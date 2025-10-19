<#
.SYNOPSIS
    Diagnostic complet MCP jupyter-papermill
.DESCRIPTION
    Collecte informations système + état MCP pour identifier root cause panne
    Phase 17 - Diagnostic + Réparation MCP
.NOTES
    Date: 2025-10-16
    Phase: 17
    Auteur: SDDD Process
    Usage: pwsh -c "& './2025-10-16_01_diagnostic-mcp-papermill.ps1'"
#>

$ErrorActionPreference = "Continue"
$StartTime = Get-Date

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   PHASE 17: DIAGNOSTIC MCP JUPYTER-PAPERMILL ║" -ForegroundColor Cyan
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Configuration
$ReportPath = "../rapports/2025-10-16_17_diagnostic-mcp-papermill.md"

# Initialisation rapport
$Report = @"
# Diagnostic MCP jupyter-papermill - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

**Machine**: $env:COMPUTERNAME
**User**: $env:USERNAME
**Workspace**: $PWD

---

## 1. Environnement Système

"@

Write-Host "📍 [1/7] Vérification environnement Python..." -ForegroundColor Yellow

# Python version
try {
    $pythonVersion = & python --version 2>&1
    Write-Host "     ✅ Python: $pythonVersion" -ForegroundColor Green
    $Report += "`n- **Python**: ``$pythonVersion```n"
} catch {
    Write-Host "     ❌ Python non trouvé" -ForegroundColor Red
    $Report += "`n- **Python**: ❌ Non installé`n"
}

# Pip version
try {
    $pipVersion = & pip --version 2>&1
    Write-Host "     ✅ Pip: $pipVersion" -ForegroundColor Green
    $Report += "- **Pip**: ``$pipVersion```n"
} catch {
    Write-Host "     ❌ Pip non trouvé" -ForegroundColor Red
    $Report += "- **Pip**: ❌ Non installé`n"
}

Write-Host ""
Write-Host "📍 [2/7] Vérification MCP papermill-coursia..." -ForegroundColor Yellow

# Vérifier installation papermill-coursia
$papermillPath = "notebook-infrastructure/papermill-coursia"
if (Test-Path $papermillPath) {
    Write-Host "     ✅ Répertoire papermill-coursia existe" -ForegroundColor Green
    $Report += "`n## 2. MCP papermill-coursia`n`n- **Répertoire**: ✅ Existe`n"
    
    # Vérifier requirements.txt
    if (Test-Path "$papermillPath/requirements.txt") {
        Write-Host "     ✅ requirements.txt existe" -ForegroundColor Green
        $requirements = Get-Content "$papermillPath/requirements.txt" -Raw
        $Report += "- **requirements.txt**: ✅ Présent`n``````text`n$requirements`n```````n"
    } else {
        Write-Host "     ❌ requirements.txt manquant" -ForegroundColor Red
        $Report += "- **requirements.txt**: ❌ Manquant`n"
    }
    
    # Vérifier CLI
    if (Test-Path "$papermillPath/cli/papermill_coursia.py") {
        Write-Host "     ✅ CLI papermill_coursia.py existe" -ForegroundColor Green
        $Report += "- **CLI**: ✅ papermill_coursia.py présent`n"
    } else {
        Write-Host "     ❌ CLI manquant" -ForegroundColor Red
        $Report += "- **CLI**: ❌ papermill_coursia.py manquant`n"
    }
} else {
    Write-Host "     ❌ Répertoire papermill-coursia manquant" -ForegroundColor Red
    $Report += "`n## 2. MCP papermill-coursia`n`n- **Répertoire**: ❌ Non trouvé`n"
}

Write-Host ""
Write-Host "📍 [3/7] Vérification packages Python installés..." -ForegroundColor Yellow

# Vérifier papermill installé
try {
    $papermillInstalled = & pip show papermill 2>&1
    if ($papermillInstalled -match "Version") {
        Write-Host "     ✅ Papermill installé" -ForegroundColor Green
        $Report += "`n## 3. Packages Python`n`n- **papermill**: ✅ Installé`n``````text`n$papermillInstalled`n```````n"
    } else {
        Write-Host "     ❌ Papermill non installé" -ForegroundColor Red
        $Report += "`n## 3. Packages Python`n`n- **papermill**: ❌ Non installé`n"
    }
} catch {
    Write-Host "     ❌ Erreur vérification papermill" -ForegroundColor Red
    $Report += "`n## 3. Packages Python`n`n- **papermill**: ❌ Erreur vérification`n"
}

Write-Host ""
Write-Host "📍 [4/7] Test import papermill Python..." -ForegroundColor Yellow

# Test import papermill
$importTest = @"
import sys
try:
    import papermill
    print(f'SUCCESS: papermill {papermill.__version__}')
except Exception as e:
    print(f'ERROR: {e}')
"@

try {
    $importResult = $importTest | & python 2>&1
    if ($importResult -match "SUCCESS") {
        Write-Host "     ✅ Import papermill réussi" -ForegroundColor Green
        $Report += "`n## 4. Test Import`n`n- **papermill**: ✅ $importResult`n"
    } else {
        Write-Host "     ❌ Import papermill échoué: $importResult" -ForegroundColor Red
        $Report += "`n## 4. Test Import`n`n- **papermill**: ❌ $importResult`n"
    }
} catch {
    Write-Host "     ❌ Erreur test import" -ForegroundColor Red
    $Report += "`n## 4. Test Import`n`n- **papermill**: ❌ Erreur`n"
}

Write-Host ""
Write-Host "📍 [5/7] Vérification dotnet-interactive (kernels)..." -ForegroundColor Yellow

# Vérifier dotnet tool list
try {
    $dotnetTools = & dotnet tool list -g 2>&1
    if ($dotnetTools -match "dotnet-interactive") {
        Write-Host "     ✅ dotnet-interactive installé globalement" -ForegroundColor Green
        $Report += "`n## 5. Dotnet Interactive`n`n- **Installation globale**: ✅ Présent`n``````text`n$dotnetTools`n```````n"
    } else {
        Write-Host "     ❌ dotnet-interactive non trouvé" -ForegroundColor Red
        $Report += "`n## 5. Dotnet Interactive`n`n- **Installation globale**: ❌ Non trouvé`n"
    }
} catch {
    Write-Host "     ❌ Erreur vérification dotnet tools" -ForegroundColor Red
    $Report += "`n## 5. Dotnet Interactive`n`n- **Installation globale**: ❌ Erreur`n"
}

# Vérifier kernels Jupyter
try {
    $jupyterKernels = & jupyter kernelspec list 2>&1
    Write-Host "     📋 Kernels Jupyter disponibles:" -ForegroundColor Gray
    Write-Host $jupyterKernels -ForegroundColor Gray
    $Report += "`n- **Kernels Jupyter**:`n``````text`n$jupyterKernels`n```````n"
} catch {
    Write-Host "     ⚠️  Impossible de lister kernels Jupyter" -ForegroundColor Yellow
    $Report += "`n- **Kernels Jupyter**: ⚠️ Liste impossible`n"
}

Write-Host ""
Write-Host "📍 [6/7] Test exécution papermill simple..." -ForegroundColor Yellow

# Créer notebook test minimal
$testNotebookPath = "../test-notebook-minimal.ipynb"
$testNotebook = @"
{
 "cells": [
  {
   "cell_type": "code",
   "execution_count": null,
   "metadata": {},
   "outputs": [],
   "source": [
    "print('Test MCP Papermill Phase 17')"
   ]
  }
 ],
 "metadata": {
  "kernelspec": {
   "display_name": "Python 3",
   "language": "python",
   "name": "python3"
  }
 },
 "nbformat": 4,
 "nbformat_minor": 4
}
"@

Set-Content -Path $testNotebookPath -Value $testNotebook -Encoding UTF8

try {
    $papermillTest = & papermill $testNotebookPath "../test-output.ipynb" 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "     ✅ Test papermill réussi" -ForegroundColor Green
        $Report += "`n## 6. Test Exécution Papermill`n`n- **Status**: ✅ SUCCESS`n"
    } else {
        Write-Host "     ❌ Test papermill échoué" -ForegroundColor Red
        $Report += "`n## 6. Test Exécution Papermill`n`n- **Status**: ❌ FAILED`n``````text`n$papermillTest`n```````n"
    }
} catch {
    Write-Host "     ❌ Erreur exécution papermill: $_" -ForegroundColor Red
    $Report += "`n## 6. Test Exécution Papermill`n`n- **Status**: ❌ ERROR`n``````text`n$_`n```````n"
}

# Cleanup test files
Remove-Item -Path $testNotebookPath -ErrorAction SilentlyContinue
Remove-Item -Path "../test-output.ipynb" -ErrorAction SilentlyContinue

Write-Host ""
Write-Host "📍 [7/7] Synthèse diagnostic..." -ForegroundColor Yellow

$Report += @"

---

## 7. Synthèse Diagnostic

### Status Global

[À compléter après analyse]

### Root Cause Identifiée

[À déterminer]

### Actions Recommandées

1. [Action 1]
2. [Action 2]
3. [Action 3]

---

**Durée diagnostic**: $((Get-Date) - $StartTime)
*Rapport généré automatiquement - Phase 17 SDDD*
"@

# Sauvegarde rapport
New-Item -ItemType Directory -Force -Path (Split-Path $ReportPath -Parent) | Out-Null
Set-Content -Path $ReportPath -Value $Report -Encoding UTF8

$EndTime = Get-Date
$Duration = $EndTime - $StartTime

Write-Host ""
Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║   ✅ DIAGNOSTIC TERMINÉ                       ║" -ForegroundColor Green
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""
Write-Host "📊 Rapport: $ReportPath" -ForegroundColor Cyan
Write-Host "⏱️  Durée: $($Duration.TotalSeconds) secondes" -ForegroundColor Cyan
Write-Host ""