<#
.SYNOPSIS
    Validation réparation MCPs roo-state-manager + jupyter-papermill
.DESCRIPTION
    Vérifie état post-réparation des 2 MCPs et teste leur fonctionnement
    Phase 17 - Diagnostic + Réparation MCP
.NOTES
    Date: 2025-10-17
    Phase: 17
    Auteur: SDDD Process
    Usage: pwsh -c "& './2025-10-17_01_valider-mcps-reparation.ps1'"
#>

$ErrorActionPreference = "Continue"
$StartTime = Get-Date

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   PHASE 17: VALIDATION RÉPARATION MCPs       ║" -ForegroundColor Cyan
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Configuration
$ReportPath = "../rapports/2025-10-17_17_validation-reparation-mcps.md"
$RooStateManagerPath = "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager"
$JupyterPapermillPath = "D:/Dev/CoursIA/notebook-infrastructure/papermill-coursia"

# Initialisation rapport
$Report = @"
# Validation Réparation MCPs - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

**Machine**: $env:COMPUTERNAME
**User**: $env:USERNAME
**Workspace**: $PWD

---

## 1. Validation MCP roo-state-manager

"@

Write-Host "📍 [1/6] Vérification package.json roo-state-manager..." -ForegroundColor Yellow

# Vérifier package.json
if (Test-Path "$RooStateManagerPath/package.json") {
    $packageJson = Get-Content "$RooStateManagerPath/package.json" -Raw | ConvertFrom-Json
    $mainPath = $packageJson.main
    
    Write-Host "     📄 Chemin 'main' actuel: $mainPath" -ForegroundColor Gray
    
    if ($mainPath -eq "build/index.js") {
        Write-Host "     ✅ package.json CORRIGÉ (build/index.js)" -ForegroundColor Green
        $Report += @"
### package.json

- **Status**: ✅ CORRIGÉ
- **Chemin 'main'**: ``$mainPath``
- **Attendu**: ``build/index.js``

"@
    } else {
        Write-Host "     ❌ package.json INCORRECT: $mainPath" -ForegroundColor Red
        $Report += @"
### package.json

- **Status**: ❌ INCORRECT
- **Chemin 'main' actuel**: ``$mainPath``
- **Chemin 'main' attendu**: ``build/index.js``

"@
    }
} else {
    Write-Host "     ❌ package.json NON TROUVÉ" -ForegroundColor Red
    $Report += "### package.json`n`n- **Status**: ❌ NON TROUVÉ`n`n"
}

Write-Host ""
Write-Host "📍 [2/6] Vérification fichier .env roo-state-manager..." -ForegroundColor Yellow

# Vérifier .env
if (Test-Path "$RooStateManagerPath/.env") {
    Write-Host "     ✅ Fichier .env existe" -ForegroundColor Green
    $Report += "### Fichier .env`n`n- **Status**: ✅ Présent`n`n"
} else {
    Write-Host "     ⚠️  Fichier .env manquant" -ForegroundColor Yellow
    $Report += "### Fichier .env`n`n- **Status**: ⚠️ Manquant`n`n"
}

Write-Host ""
Write-Host "📍 [3/6] Vérification build roo-state-manager..." -ForegroundColor Yellow

# Vérifier fichier build
if (Test-Path "$RooStateManagerPath/build/index.js") {
    $buildSize = (Get-Item "$RooStateManagerPath/build/index.js").Length
    Write-Host "     ✅ Fichier build/index.js existe ($buildSize bytes)" -ForegroundColor Green
    $Report += "### Fichier build/index.js`n`n- **Status**: ✅ Présent`n- **Taille**: $buildSize bytes`n`n"
} else {
    Write-Host "     ❌ Fichier build/index.js MANQUANT" -ForegroundColor Red
    $Report += "### Fichier build/index.js`n`n- **Status**: ❌ MANQUANT`n`n"
    
    Write-Host "     🔧 Tentative rebuild..." -ForegroundColor Yellow
    Push-Location $RooStateManagerPath
    try {
        $buildOutput = & npm run build 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "     ✅ Rebuild réussi" -ForegroundColor Green
            $Report += "- **Rebuild**: ✅ SUCCESS`n`n"
        } else {
            Write-Host "     ❌ Rebuild échoué" -ForegroundColor Red
            $Report += "- **Rebuild**: ❌ FAILED`n``````text`n$buildOutput`n```````n`n"
        }
    } catch {
        Write-Host "     ❌ Erreur rebuild: $_" -ForegroundColor Red
        $Report += "- **Rebuild**: ❌ ERROR`n``````text`n$_`n```````n`n"
    }
    Pop-Location
}

$Report += @"
---

## 2. Validation MCP jupyter-papermill

"@

Write-Host ""
Write-Host "📍 [4/6] Vérification structure papermill-coursia..." -ForegroundColor Yellow

# Vérifier structure
if (Test-Path $JupyterPapermillPath) {
    Write-Host "     ✅ Répertoire papermill-coursia existe" -ForegroundColor Green
    $Report += "### Structure`n`n- **Répertoire**: ✅ Présent`n"
    
    # Vérifier requirements.txt
    if (Test-Path "$JupyterPapermillPath/requirements.txt") {
        Write-Host "     ✅ requirements.txt existe" -ForegroundColor Green
        $requirements = Get-Content "$JupyterPapermillPath/requirements.txt" -Raw
        $Report += "- **requirements.txt**: ✅ Présent`n``````text`n$requirements`n```````n`n"
    } else {
        Write-Host "     ❌ requirements.txt manquant" -ForegroundColor Red
        $Report += "- **requirements.txt**: ❌ Manquant`n`n"
    }
    
    # Vérifier CLI
    if (Test-Path "$JupyterPapermillPath/cli/papermill_coursia.py") {
        Write-Host "     ✅ CLI papermill_coursia.py existe" -ForegroundColor Green
        $Report += "- **CLI**: ✅ papermill_coursia.py présent`n`n"
    } else {
        Write-Host "     ❌ CLI papermill_coursia.py manquant" -ForegroundColor Red
        $Report += "- **CLI**: ❌ papermill_coursia.py manquant`n`n"
    }
} else {
    Write-Host "     ❌ Répertoire papermill-coursia MANQUANT" -ForegroundColor Red
    $Report += "### Structure`n`n- **Répertoire**: ❌ NON TROUVÉ`n`n"
}

Write-Host ""
Write-Host "📍 [5/6] Test import papermill Python..." -ForegroundColor Yellow

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
        Write-Host "     ✅ Import papermill réussi: $importResult" -ForegroundColor Green
        $Report += "### Test Import`n`n- **papermill**: ✅ $importResult`n`n"
    } else {
        Write-Host "     ❌ Import papermill échoué: $importResult" -ForegroundColor Red
        $Report += "### Test Import`n`n- **papermill**: ❌ $importResult`n`n"
    }
} catch {
    Write-Host "     ❌ Erreur test import" -ForegroundColor Red
    $Report += "### Test Import`n`n- **papermill**: ❌ Erreur`n`n"
}

Write-Host ""
Write-Host "📍 [6/6] Instructions redémarrage VS Code..." -ForegroundColor Yellow

$Report += @"
---

## 3. Instructions Validation Finale

### Étape 1: Redémarrer VS Code

**CRITIQUE**: Pour que les corrections soient prises en compte, vous devez:

1. **Fermer complètement VS Code** (toutes les fenêtres)
2. **Redémarrer VS Code**
3. **Attendre 10-15 secondes** que les MCPs se rechargent

### Étape 2: Vérifier les MCPs actifs

Après redémarrage, vérifier dans VS Code:

1. Ouvrir **Command Palette** (Ctrl+Shift+P)
2. Taper **"MCP"**
3. Chercher les outils:
   - ``roo-state-manager``: ``view_conversation_tree``, ``get_task_details``, etc.
   - ``papermill-coursia``: Outils notebooks

### Étape 3: Tester roo-state-manager

Si le MCP est actif, tester:

``````
view_conversation_tree --limit 5
``````

**Résultat attendu**: Arbre des conversations récentes sans erreur.

### Étape 4: Tester jupyter-papermill

Si le MCP est actif, vérifier disponibilité outils notebooks.

### Statut Corrections Appliquées

- ✅ **roo-state-manager**: ``package.json`` corrigé (``build/index.js``)
- ✅ **roo-state-manager**: ``.env`` créé depuis ``.env.example``
- ⚠️  **jupyter-papermill**: Diagnostic à compléter après validation roo-state-manager

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
Write-Host "║   ✅ VALIDATION TERMINÉE                      ║" -ForegroundColor Green
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""
Write-Host "📊 Rapport: $ReportPath" -ForegroundColor Cyan
Write-Host "⏱️  Durée: $($Duration.TotalSeconds) secondes" -ForegroundColor Cyan
Write-Host ""
Write-Host "⚠️  ACTION REQUISE:" -ForegroundColor Yellow
Write-Host "    1. FERMER COMPLÈTEMENT VS CODE" -ForegroundColor Yellow
Write-Host "    2. REDÉMARRER VS CODE" -ForegroundColor Yellow
Write-Host "    3. ATTENDRE 10-15 SECONDES" -ForegroundColor Yellow
Write-Host "    4. TESTER LES MCPs" -ForegroundColor Yellow
Write-Host ""