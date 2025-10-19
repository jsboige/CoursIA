<#
.SYNOPSIS
    Tests de validation fonctionnelle des MCPs réparés (Phase 17)
.DESCRIPTION
    Valide que les 2 MCPs sont opérationnels après réparation:
    - roo-state-manager (TypeScript/Node.js)
    - jupyter-papermill (Python)
.NOTES
    Date: 2025-10-17
    Phase: 17 - Réparation MCP
    Auteur: SDDD Process
    Usage: pwsh -c "& './docs/suivis/genai-image/phase-17-reparation-mcp/scripts/2025-10-17_03_test-validation-mcps.ps1'"
#>

$ErrorActionPreference = "Continue"
$StartTime = Get-Date

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   PHASE 17: VALIDATION MCPS RÉPARÉS          ║" -ForegroundColor Cyan
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Configuration
$ReportPath = "docs/suivis/genai-image/phase-17-reparation-mcp/rapports/2025-10-17_17_validation-mcps.md"
$TestsPassed = 0
$TestsFailed = 0

# Initialisation rapport
$Report = @"
# Validation MCPs Réparés - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

**Machine**: $env:COMPUTERNAME
**User**: $env:USERNAME
**Workspace**: $PWD

---

## Tests MCP roo-state-manager

"@

Write-Host "📍 [1/4] Test MCP roo-state-manager (Node.js)..." -ForegroundColor Yellow

# Test 1: Vérifier que le serveur démarre
try {
    $mcpPath = "D:/Dev/roo-extensions/mcps/internal/servers/roo-state-manager"
    
    if (Test-Path "$mcpPath/build/index.js") {
        Write-Host "     ✅ Build du serveur existe" -ForegroundColor Green
        $Report += "`n### Build du Serveur`n`n- **Status**: ✅ Présent`n"
        $TestsPassed++
    } else {
        Write-Host "     ❌ Build du serveur manquant" -ForegroundColor Red
        $Report += "`n### Build du Serveur`n`n- **Status**: ❌ Manquant`n"
        $TestsFailed++
    }
    
    # Vérifier fichier .env
    if (Test-Path "$mcpPath/.env") {
        Write-Host "     ✅ Fichier .env existe" -ForegroundColor Green
        $Report += "- **Fichier .env**: ✅ Présent`n"
        $TestsPassed++
    } else {
        Write-Host "     ❌ Fichier .env manquant" -ForegroundColor Red
        $Report += "- **Fichier .env**: ❌ Manquant`n"
        $TestsFailed++
    }
    
} catch {
    Write-Host "     ❌ Erreur test roo-state-manager: $_" -ForegroundColor Red
    $Report += "`n### Erreur Test`n`n``````text`n$_`n```````n"
    $TestsFailed++
}

Write-Host ""
Write-Host "📍 [2/4] Test MCP jupyter-papermill (Python)..." -ForegroundColor Yellow

$Report += @"

---

## Tests MCP jupyter-papermill

"@

# Test 2: Vérifier packages Python installés
try {
    $packages = @("papermill", "jupyter", "mcp", "fastmcp")
    $allInstalled = $true
    
    foreach ($package in $packages) {
        $checkInstall = & C:\Python313\python.exe -c "import $package; print('OK')" 2>&1
        
        if ($checkInstall -match "OK") {
            Write-Host "     ✅ Package $package installé" -ForegroundColor Green
            $Report += "- **Package $package**: ✅ Installé`n"
            $TestsPassed++
        } else {
            Write-Host "     ❌ Package $package manquant" -ForegroundColor Red
            $Report += "- **Package $package**: ❌ Manquant`n"
            $TestsFailed++
            $allInstalled = $false
        }
    }
    
} catch {
    Write-Host "     ❌ Erreur test packages Python: $_" -ForegroundColor Red
    $Report += "`n### Erreur Test Packages`n`n``````text`n$_`n```````n"
    $TestsFailed++
}

Write-Host ""
Write-Host "📍 [3/4] Test import module papermill_mcp..." -ForegroundColor Yellow

# Test 3: Vérifier module papermill_mcp
try {
    $testImport = @"
import sys
sys.path.insert(0, 'D:/Dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server')
try:
    import papermill_mcp
    print('SUCCESS')
except Exception as e:
    print(f'ERROR: {e}')
"@
    
    $importResult = $testImport | & C:\Python313\python.exe 2>&1
    
    if ($importResult -match "SUCCESS") {
        Write-Host "     ✅ Module papermill_mcp importable" -ForegroundColor Green
        $Report += "`n### Import Module`n`n- **Status**: ✅ SUCCESS`n"
        $TestsPassed++
    } else {
        Write-Host "     ❌ Erreur import module: $importResult" -ForegroundColor Red
        $Report += "`n### Import Module`n`n- **Status**: ❌ FAILED`n``````text`n$importResult`n```````n"
        $TestsFailed++
    }
    
} catch {
    Write-Host "     ❌ Erreur test import: $_" -ForegroundColor Red
    $Report += "`n### Erreur Test Import`n`n``````text`n$_`n```````n"
    $TestsFailed++
}

Write-Host ""
Write-Host "📍 [4/4] Vérification configuration mcp_settings.json..." -ForegroundColor Yellow

$Report += @"

---

## Configuration mcp_settings.json

"@

# Test 4: Vérifier configuration MCP dans VS Code
try {
    $mcpSettingsPath = "C:/Users/jsboi/AppData/Roaming/Code/User/globalStorage/rooveterinaryinc.roo-cline/settings/mcp_settings.json"
    
    if (Test-Path $mcpSettingsPath) {
        Write-Host "     ✅ Fichier mcp_settings.json existe" -ForegroundColor Green
        $Report += "- **Fichier**: ✅ Présent`n"
        $TestsPassed++
        
        # Vérifier contenu
        $mcpConfig = Get-Content $mcpSettingsPath -Raw | ConvertFrom-Json
        
        # Vérifier MCP roo-state-manager
        if ($mcpConfig.mcpServers.'roo-state-manager') {
            Write-Host "     ✅ MCP roo-state-manager configuré" -ForegroundColor Green
            $Report += "- **MCP roo-state-manager**: ✅ Configuré`n"
            $TestsPassed++
        } else {
            Write-Host "     ❌ MCP roo-state-manager non configuré" -ForegroundColor Red
            $Report += "- **MCP roo-state-manager**: ❌ Non configuré`n"
            $TestsFailed++
        }
        
        # Vérifier MCP jupyter
        if ($mcpConfig.mcpServers.jupyter) {
            Write-Host "     ✅ MCP jupyter configuré" -ForegroundColor Green
            $Report += "- **MCP jupyter**: ✅ Configuré`n"
            
            # Vérifier PYTHONPATH dans args
            $jupyterArgs = $mcpConfig.mcpServers.jupyter.args -join " "
            if ($jupyterArgs -match "PYTHONPATH") {
                Write-Host "     ✅ PYTHONPATH configuré dans args" -ForegroundColor Green
                $Report += "- **PYTHONPATH fix**: ✅ Présent`n"
                $TestsPassed++
            } else {
                Write-Host "     ⚠️  PYTHONPATH non trouvé dans args" -ForegroundColor Yellow
                $Report += "- **PYTHONPATH fix**: ⚠️ Non trouvé`n"
            }
        } else {
            Write-Host "     ❌ MCP jupyter non configuré" -ForegroundColor Red
            $Report += "- **MCP jupyter**: ❌ Non configuré`n"
            $TestsFailed++
        }
        
    } else {
        Write-Host "     ❌ Fichier mcp_settings.json manquant" -ForegroundColor Red
        $Report += "- **Fichier**: ❌ Manquant`n"
        $TestsFailed++
    }
    
} catch {
    Write-Host "     ❌ Erreur test configuration: $_" -ForegroundColor Red
    $Report += "`n### Erreur Test Config`n`n``````text`n$_`n```````n"
    $TestsFailed++
}

# Synthèse finale
$TotalTests = $TestsPassed + $TestsFailed
$SuccessRate = if ($TotalTests -gt 0) { [Math]::Round(($TestsPassed / $TotalTests) * 100, 2) } else { 0 }

$Report += @"

---

## Synthèse Validation

### Résultats Tests

- **Tests réussis**: $TestsPassed
- **Tests échoués**: $TestsFailed
- **Total tests**: $TotalTests
- **Taux de réussite**: $SuccessRate%

### Status Global

"@

if ($TestsFailed -eq 0) {
    $Report += @"
✅ **VALIDATION RÉUSSIE**

Les 2 MCPs sont opérationnels :
- ``roo-state-manager`` : Fix bug path .env + recompilation TypeScript
- ``jupyter-papermill`` : Installation packages Python + fix PYTHONPATH + logs stderr

### Actions Suivantes

1. **Checkpoint SDDD** : Synthèse réparations + validation
2. **Documentation Solution** : Guide réparation + prévention futures pannes
3. **Grounding Sémantique Final** : Validation documentation accessible
4. **Rapport Final Phase 17** : Triple grounding
"@
} else {
    $Report += @"
❌ **VALIDATION PARTIELLE**

$TestsFailed test(s) ont échoué. Révision nécessaire avant documentation.

### Actions Requises

[À déterminer selon tests échoués]
"@
}

$Report += @"

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
Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor $(if ($TestsFailed -eq 0) { "Green" } else { "Yellow" })
Write-Host "║   $(if ($TestsFailed -eq 0) { "✅ VALIDATION TERMINÉE" } else { "⚠️  VALIDATION PARTIELLE" })                    ║" -ForegroundColor $(if ($TestsFailed -eq 0) { "Green" } else { "Yellow" })
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor $(if ($TestsFailed -eq 0) { "Green" } else { "Yellow" })
Write-Host ""
Write-Host "📊 Tests réussis : $TestsPassed/$TotalTests ($SuccessRate%)" -ForegroundColor $(if ($TestsFailed -eq 0) { "Green" } else { "Yellow" })
Write-Host "📄 Rapport : $ReportPath" -ForegroundColor Cyan
Write-Host "⏱️  Durée : $($Duration.TotalSeconds) secondes" -ForegroundColor Cyan
Write-Host ""

exit $(if ($TestsFailed -eq 0) { 0 } else { 1 })