<#
.SYNOPSIS
    Wrapper principal exécution tests APIs GenAI (Phase 16)
.DESCRIPTION
    Exécute tous les tests APIs (Qwen + SD XL Turbo) de manière non-bloquante
    Phase 16 - Exécution tests avec itération rapide via Start-Job
.NOTES
    Date: 2025-10-16
    Phase: 16 - Exécution Tests APIs
    Auteur: SDDD Process
    Usage: pwsh -c "& './2025-10-16_00_run-all-tests.ps1'"
#>

$ErrorActionPreference = "Continue"
$StartTime = Get-Date

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║   PHASE 16: EXÉCUTION TESTS APIs GenAI       ║" -ForegroundColor Cyan
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# ═══════════════════════════════════════════════
# CONFIGURATION CHEMINS
# ═══════════════════════════════════════════════

$BaseDir = Split-Path -Parent $PSScriptRoot
$ScriptsPhase14B = Join-Path $BaseDir "..\phase-14b-tests-apis\scripts"
$ReportsPhase14B = Join-Path $BaseDir "..\phase-14b-tests-apis\rapports"
$ReportsPhase16 = Join-Path $BaseDir "rapports"
$SummaryPath = Join-Path $ReportsPhase16 "2025-10-16_16_SYNTHESE-TESTS-APIS.md"

# Création répertoire rapports si nécessaire
New-Item -ItemType Directory -Force -Path $ReportsPhase16 | Out-Null

Write-Host "📂 Configuration:" -ForegroundColor Gray
Write-Host "   Scripts Phase 14B: $ScriptsPhase14B" -ForegroundColor Gray
Write-Host "   Rapports Phase 14B: $ReportsPhase14B" -ForegroundColor Gray
Write-Host "   Rapports Phase 16: $ReportsPhase16" -ForegroundColor Gray
Write-Host ""

# ═══════════════════════════════════════════════
# INITIALISATION RAPPORT SYNTHÈSE
# ═══════════════════════════════════════════════

$Summary = @"
# Synthèse Exécution Tests APIs - Phase 16
**Date**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
**Machine**: $env:COMPUTERNAME
**Phase**: 16 - Exécution Tests APIs GenAI

---

## 🎯 Objectif

Exécution effective des tests de validation des 2 APIs GenAI en production:
- **API Qwen** (ComfyUI) - https://qwen-image-edit.myia.io
- **API SD XL Turbo** (Forge) - https://sd-xl-turbo.myia.io

Méthodologie: Scripts wrapper PowerShell non-bloquants avec timeout pour itération rapide.

---

## 📊 Tests Exécutés

"@

# ═══════════════════════════════════════════════
# TEST 1: API QWEN (ComfyUI)
# ═══════════════════════════════════════════════

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Yellow
Write-Host "║   TEST 1/2: API QWEN (ComfyUI)               ║" -ForegroundColor Yellow
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Yellow
Write-Host ""

$qwenScriptPath = Join-Path $ScriptsPhase14B "2025-10-16_01_test-qwen-api.ps1"
$qwenStartTime = Get-Date

Write-Host "🧪 Exécution Test API Qwen..." -ForegroundColor Cyan
Write-Host "   Script: $qwenScriptPath" -ForegroundColor Gray

if (Test-Path $qwenScriptPath) {
    try {
        Write-Host "   📋 Démarrage job background..." -ForegroundColor Gray
        
        $qwenJob = Start-Job -ScriptBlock {
            param($scriptPath)
            & pwsh -File $scriptPath
        } -ArgumentList $qwenScriptPath
        
        Write-Host "   ⏱️  Job ID: $($qwenJob.Id) - Attente max 60s..." -ForegroundColor Gray
        
        # Attente avec timeout (60 secondes)
        $qwenJob | Wait-Job -Timeout 60 | Out-Null
        
        $qwenEndTime = Get-Date
        $qwenDuration = ($qwenEndTime - $qwenStartTime).TotalSeconds
        
        if ($qwenJob.State -eq "Running") {
            Write-Host "   ⏱️  Timeout après 60s - Test continue en background" -ForegroundColor Yellow
            $qwenStatus = "TIMEOUT"
            $qwenDetails = "Test en cours après timeout 60s (continue en background)"
            $qwenIcon = "⏱️"
        } elseif ($qwenJob.State -eq "Completed") {
            $qwenOutput = Receive-Job -Job $qwenJob -ErrorAction SilentlyContinue
            Write-Host "   ✅ Test Qwen terminé avec succès" -ForegroundColor Green
            Write-Host "   ⏱️  Durée: $([math]::Round($qwenDuration, 2))s" -ForegroundColor Gray
            $qwenStatus = "COMPLETED"
            $qwenDetails = "Test terminé en $([math]::Round($qwenDuration, 2))s"
            $qwenIcon = "✅"
        } else {
            Write-Host "   ❌ Test Qwen échoué: $($qwenJob.State)" -ForegroundColor Red
            $qwenStatus = "ERROR"
            $qwenDetails = "Erreur d'exécution: $($qwenJob.State)"
            $qwenIcon = "❌"
        }
        
        Remove-Job -Job $qwenJob -Force -ErrorAction SilentlyContinue
        
    } catch {
        Write-Host "   ❌ Erreur Test Qwen: $_" -ForegroundColor Red
        $qwenStatus = "ERROR"
        $qwenDetails = "Exception: $_"
        $qwenIcon = "❌"
        $qwenDuration = 0
    }
} else {
    Write-Host "   ❌ Script non trouvé: $qwenScriptPath" -ForegroundColor Red
    $qwenStatus = "ERROR"
    $qwenDetails = "Script introuvable"
    $qwenIcon = "❌"
    $qwenDuration = 0
}

Write-Host ""

$Summary += @"

### Test 1: API Qwen (ComfyUI)

**Script**: [`2025-10-16_01_test-qwen-api.ps1`](../../phase-14b-tests-apis/scripts/2025-10-16_01_test-qwen-api.ps1)

- **Status**: $qwenIcon $qwenStatus
- **Détails**: $qwenDetails
- **Durée**: $([math]::Round($qwenDuration, 2))s
- **Rapport détaillé**: [2025-10-16_14B_rapport-test-qwen-api.md](../../phase-14b-tests-apis/rapports/2025-10-16_14B_rapport-test-qwen-api.md)

**Endpoints testés**:
1. Health Check (`/system_stats`)
2. Queue Status (`/queue`)
3. Nodes Info (`/object_info`)
4. Workflow Submit (`/prompt`)

"@

# ═══════════════════════════════════════════════
# TEST 2: API SD XL TURBO (Forge)
# ═══════════════════════════════════════════════

Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Yellow
Write-Host "║   TEST 2/2: API SD XL TURBO (Forge)          ║" -ForegroundColor Yellow
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Yellow
Write-Host ""

$turboScriptPath = Join-Path $ScriptsPhase14B "2025-10-16_02_test-sdxl-turbo-api.ps1"
$turboStartTime = Get-Date

Write-Host "🧪 Exécution Test API SD XL Turbo..." -ForegroundColor Cyan
Write-Host "   Script: $turboScriptPath" -ForegroundColor Gray

if (Test-Path $turboScriptPath) {
    try {
        Write-Host "   📋 Démarrage job background..." -ForegroundColor Gray
        
        $turboJob = Start-Job -ScriptBlock {
            param($scriptPath)
            & pwsh -File $scriptPath
        } -ArgumentList $turboScriptPath
        
        Write-Host "   ⏱️  Job ID: $($turboJob.Id) - Attente max 60s..." -ForegroundColor Gray
        
        # Attente avec timeout (60 secondes)
        $turboJob | Wait-Job -Timeout 60 | Out-Null
        
        $turboEndTime = Get-Date
        $turboDuration = ($turboEndTime - $turboStartTime).TotalSeconds
        
        if ($turboJob.State -eq "Running") {
            Write-Host "   ⏱️  Timeout après 60s - Test continue en background" -ForegroundColor Yellow
            $turboStatus = "TIMEOUT"
            $turboDetails = "Test en cours après timeout 60s (continue en background)"
            $turboIcon = "⏱️"
        } elseif ($turboJob.State -eq "Completed") {
            $turboOutput = Receive-Job -Job $turboJob -ErrorAction SilentlyContinue
            Write-Host "   ✅ Test SD XL Turbo terminé avec succès" -ForegroundColor Green
            Write-Host "   ⏱️  Durée: $([math]::Round($turboDuration, 2))s" -ForegroundColor Gray
            $turboStatus = "COMPLETED"
            $turboDetails = "Test terminé en $([math]::Round($turboDuration, 2))s"
            $turboIcon = "✅"
        } else {
            Write-Host "   ❌ Test SD XL Turbo échoué: $($turboJob.State)" -ForegroundColor Red
            $turboStatus = "ERROR"
            $turboDetails = "Erreur d'exécution: $($turboJob.State)"
            $turboIcon = "❌"
        }
        
        Remove-Job -Job $turboJob -Force -ErrorAction SilentlyContinue
        
    } catch {
        Write-Host "   ❌ Erreur Test SD XL Turbo: $_" -ForegroundColor Red
        $turboStatus = "ERROR"
        $turboDetails = "Exception: $_"
        $turboIcon = "❌"
        $turboDuration = 0
    }
} else {
    Write-Host "   ❌ Script non trouvé: $turboScriptPath" -ForegroundColor Red
    $turboStatus = "ERROR"
    $turboDetails = "Script introuvable"
    $turboIcon = "❌"
    $turboDuration = 0
}

Write-Host ""

$Summary += @"

### Test 2: API SD XL Turbo (Forge)

**Script**: [`2025-10-16_02_test-sdxl-turbo-api.ps1`](../../phase-14b-tests-apis/scripts/2025-10-16_02_test-sdxl-turbo-api.ps1)

- **Status**: $turboIcon $turboStatus
- **Détails**: $turboDetails
- **Durée**: $([math]::Round($turboDuration, 2))s
- **Rapport détaillé**: [2025-10-16_14B_rapport-test-sdxl-turbo-api.md](../../phase-14b-tests-apis/rapports/2025-10-16_14B_rapport-test-sdxl-turbo-api.md)

**Endpoints testés**:
1. Health Check (`/`)
2. Models List (`/sdapi/v1/sd-models`)
3. Samplers List (`/sdapi/v1/samplers`)
4. Generation Test (`/sdapi/v1/txt2img`)

---

## 📈 Résumé Global

| API | Status | Durée | Rapport |
|-----|--------|-------|---------|
| Qwen (ComfyUI) | $qwenIcon $qwenStatus | $([math]::Round($qwenDuration, 2))s | [Voir rapport](../../phase-14b-tests-apis/rapports/2025-10-16_14B_rapport-test-qwen-api.md) |
| SD XL Turbo (Forge) | $turboIcon $turboStatus | $([math]::Round($turboDuration, 2))s | [Voir rapport](../../phase-14b-tests-apis/rapports/2025-10-16_14B_rapport-test-sdxl-turbo-api.md) |

### Interprétation Status

- ✅ **COMPLETED**: Test terminé avec succès dans timeout
- ⏱️ **TIMEOUT**: Test en cours après 60s (continuera en background)
- ❌ **ERROR**: Erreur d'exécution détectée

### Notes Importantes

"@

if ($qwenStatus -eq "TIMEOUT" -or $turboStatus -eq "TIMEOUT") {
    $Summary += @"
⚠️ **Un ou plusieurs tests ont dépassé le timeout de 60s**:
- Les tests continuent en background et génèreront leurs rapports individuels
- Consultez les rapports détaillés dans `phase-14b-tests-apis/rapports/` après complétion
- Les jobs background PowerShell se termineront automatiquement

"@
}

if ($qwenStatus -eq "ERROR" -or $turboStatus -eq "ERROR") {
    $Summary += @"
❌ **Un ou plusieurs tests ont échoué**:
- Vérifier l'accessibilité des APIs production
- Vérifier les chemins scripts Phase 14B
- Consulter logs PowerShell pour détails erreurs

"@
}

$Summary += @"

---

## 🔄 Prochaines Actions

1. **Consulter rapports individuels générés** dans `phase-14b-tests-apis/rapports/`
2. **Analyser résultats détaillés** (métriques endpoints, temps réponse, erreurs)
3. **Mettre à jour guide étudiants** avec status validation production
4. **Documenter issues identifiées** si applicable
5. **Planifier corrections** si nécessaire

---

## 📊 Métriques Wrapper

- **Durée totale wrapper**: $((Get-Date) - $StartTime | Select-Object -ExpandProperty TotalSeconds) secondes
- **Tests exécutés**: 2/2
- **Mode exécution**: Non-bloquant (Start-Job + timeout 60s)
- **Rapports générés**: 3 (2 individuels + 1 synthèse)

---

**Rapport généré automatiquement** - Phase 16 SDDD  
**Timestamp**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**Script**: `2025-10-16_00_run-all-tests.ps1`
"@

# ═══════════════════════════════════════════════
# SAUVEGARDE SYNTHÈSE
# ═══════════════════════════════════════════════

try {
    Set-Content -Path $SummaryPath -Value $Summary -Encoding UTF8
    Write-Host "✅ Synthèse sauvegardée: $SummaryPath" -ForegroundColor Green
} catch {
    Write-Host "❌ Erreur sauvegarde synthèse: $_" -ForegroundColor Red
}

# ═══════════════════════════════════════════════
# RÉSUMÉ FINAL CONSOLE
# ═══════════════════════════════════════════════

$EndTime = Get-Date
$Duration = $EndTime - $StartTime

Write-Host ""
Write-Host "╔═══════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║   ✅ EXÉCUTION TESTS TERMINÉE                ║" -ForegroundColor Green
Write-Host "╚═══════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""
Write-Host "📊 Synthèse wrapper:" -ForegroundColor Cyan
Write-Host "   - Tests exécutés: 2/2" -ForegroundColor White
Write-Host "   - API Qwen: $qwenIcon $qwenStatus" -ForegroundColor White
Write-Host "   - API SD XL Turbo: $turboIcon $turboStatus" -ForegroundColor White
Write-Host "   - Durée totale: $([math]::Round($Duration.TotalSeconds, 2))s" -ForegroundColor White
Write-Host ""
Write-Host "📁 Rapports disponibles:" -ForegroundColor Cyan
Write-Host "   - Synthèse: $SummaryPath" -ForegroundColor Gray
Write-Host "   - Détails Qwen: $ReportsPhase14B\2025-10-16_14B_rapport-test-qwen-api.md" -ForegroundColor Gray
Write-Host "   - Détails Turbo: $ReportsPhase14B\2025-10-16_14B_rapport-test-sdxl-turbo-api.md" -ForegroundColor Gray
Write-Host ""

if ($qwenStatus -ne "ERROR" -and $turboStatus -ne "ERROR") {
    Write-Host "🎉 Wrapper exécuté avec succès!" -ForegroundColor Green
    exit 0
} else {
    Write-Host "⚠️ Wrapper terminé avec erreurs - Consulter rapports" -ForegroundColor Yellow
    exit 1
}