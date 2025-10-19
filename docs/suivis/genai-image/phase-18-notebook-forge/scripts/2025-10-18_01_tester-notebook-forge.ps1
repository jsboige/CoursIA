<#
.SYNOPSIS
    Tests de validation notebook Forge SD XL Turbo - Phase 18

.DESCRIPTION
    Valide la structure, syntaxe Python et cohérence du notebook pédagogique
    créé via MCP jupyter-papermill. Tests techniques sans exécution API.
    
    Tests réalisés:
    - Existence + taille fichier notebook
    - Validation format JSON nbformat v4
    - Comptage cellules (14 attendues: 7 Markdown + 7 Code)
    - Validation syntaxe Python (cellules code)
    - Présence imports critiques (requests, Pillow, matplotlib)
    - Présence fonction generate_image_turbo()
    - Présence URL API Forge
    - Cohérence paramètres Turbo (steps=4, cfg_scale=2.0)

.NOTES
    Auteur: Phase 18 SDDD Process
    Date: 2025-10-18
    Phase: 18 - Partie 7 (Tests Fonctionnels)
    
.EXAMPLE
    pwsh -c "& './docs/suivis/genai-image/phase-18-notebook-forge/scripts/2025-10-18_01_tester-notebook-forge.ps1'"
    
    Exécute tous les tests de validation du notebook Forge.

.OUTPUTS
    Rapport tests au format Markdown:
    - docs/suivis/genai-image/phase-18-notebook-forge/2025-10-18_18_07_rapport-tests.md
#>

#Requires -Version 7.0

# Configuration
$ErrorActionPreference = "Stop"
$NotebookPath = "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb"
$ReportPath = "docs/suivis/genai-image/phase-18-notebook-forge/2025-10-18_18_07_rapport-tests.md"

# Initialisation rapport
$Report = @"
# Phase 18: Rapport Tests Notebook Forge SD XL Turbo

**Date**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**Notebook testé**: ``$NotebookPath``  
**Phase**: Partie 7 - Tests Fonctionnels  

---

## Résumé Tests

"@

# Compteurs résultats
$TestsPassed = 0
$TestsFailed = 0
$TestsWarning = 0

# Fonction helper test
function Test-NotebookProperty {
    param(
        [string]$TestName,
        [scriptblock]$TestBlock,
        [string]$SuccessMessage,
        [string]$FailureMessage,
        [switch]$Critical
    )
    
    Write-Host "`n🧪 Test: $TestName" -ForegroundColor Cyan
    
    try {
        $result = & $TestBlock
        if ($result) {
            Write-Host "✅ SUCCÈS: $SuccessMessage" -ForegroundColor Green
            $script:TestsPassed++
            $script:Report += "`n### ✅ Test: $TestName`n`n**Résultat**: SUCCÈS`n`n$SuccessMessage`n"
            return $true
        } else {
            if ($Critical) {
                Write-Host "❌ ÉCHEC CRITIQUE: $FailureMessage" -ForegroundColor Red
                $script:TestsFailed++
                $script:Report += "`n### ❌ Test: $TestName`n`n**Résultat**: ÉCHEC CRITIQUE`n`n$FailureMessage`n"
                throw "Test critique échoué: $TestName"
            } else {
                Write-Host "⚠️ AVERTISSEMENT: $FailureMessage" -ForegroundColor Yellow
                $script:TestsWarning++
                $script:Report += "`n### ⚠️ Test: $TestName`n`n**Résultat**: AVERTISSEMENT`n`n$FailureMessage`n"
                return $false
            }
        }
    } catch {
        Write-Host "❌ ERREUR: $_" -ForegroundColor Red
        $script:TestsFailed++
        $script:Report += "`n### ❌ Test: $TestName`n`n**Résultat**: ERREUR`n`n$($_.Exception.Message)`n"
        if ($Critical) {
            throw
        }
        return $false
    }
}

# Début tests
Write-Host "`n═══════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "   TESTS VALIDATION NOTEBOOK FORGE SD XL TURBO" -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════`n" -ForegroundColor Cyan

# Test 1: Existence fichier
Test-NotebookProperty -TestName "Existence Fichier Notebook" -Critical -TestBlock {
    Test-Path $NotebookPath
} -SuccessMessage "Notebook trouvé à ``$NotebookPath``" `
  -FailureMessage "Notebook introuvable à ``$NotebookPath``"

# Test 2: Taille fichier raisonnable
$FileSize = (Get-Item $NotebookPath).Length
Test-NotebookProperty -TestName "Taille Fichier Raisonnable" -TestBlock {
    ($FileSize -gt 10KB) -and ($FileSize -lt 100KB)
} -SuccessMessage "Taille: $([math]::Round($FileSize/1KB, 2)) KB (acceptable)" `
  -FailureMessage "Taille anormale: $([math]::Round($FileSize/1KB, 2)) KB (attendu: 10-100 KB)"

# Test 3: Validation JSON
$NotebookJson = Get-Content $NotebookPath -Raw | ConvertFrom-Json
Test-NotebookProperty -TestName "Format JSON Valide" -Critical -TestBlock {
    $null -ne $NotebookJson
} -SuccessMessage "Format JSON nbformat valide" `
  -FailureMessage "Format JSON corrompu"

# Test 4: Version nbformat
Test-NotebookProperty -TestName "Version nbformat" -TestBlock {
    $NotebookJson.nbformat -eq 4
} -SuccessMessage "nbformat version 4 (standard Jupyter)" `
  -FailureMessage "nbformat version $($NotebookJson.nbformat) (attendu: 4)"

# Test 5: Nombre cellules total
$CellCount = $NotebookJson.cells.Count
Test-NotebookProperty -TestName "Nombre Cellules Total" -Critical -TestBlock {
    $CellCount -eq 15
} -SuccessMessage "15 cellules présentes (conforme design final)" `
  -FailureMessage "$CellCount cellules trouvées (attendu: 15)"

# Test 6: Répartition Markdown/Code
$MarkdownCells = ($NotebookJson.cells | Where-Object { $_.cell_type -eq "markdown" }).Count
$CodeCells = ($NotebookJson.cells | Where-Object { $_.cell_type -eq "code" }).Count

Test-NotebookProperty -TestName "Répartition Markdown/Code" -TestBlock {
    ($MarkdownCells -eq 8) -and ($CodeCells -eq 7)
} -SuccessMessage "8 Markdown + 7 Code (progression pédagogique optimale)" `
  -FailureMessage "$MarkdownCells Markdown + $CodeCells Code (attendu: 8+7)"

# Test 7: Présence imports critiques
$AllCodeSource = ($NotebookJson.cells | Where-Object { $_.cell_type -eq "code" } | ForEach-Object { $_.source -join "`n" }) -join "`n"

$CriticalImports = @("import requests", "from PIL import Image", "import matplotlib.pyplot", "import json", "import base64")
$ImportsMissing = @()

foreach ($import in $CriticalImports) {
    if ($AllCodeSource -notmatch [regex]::Escape($import)) {
        $ImportsMissing += $import
    }
}

Test-NotebookProperty -TestName "Imports Python Critiques" -Critical -TestBlock {
    $ImportsMissing.Count -eq 0
} -SuccessMessage "Tous imports critiques présents: $($CriticalImports -join ', ')" `
  -FailureMessage "Imports manquants: $($ImportsMissing -join ', ')"

# Test 8: Présence fonction generate_image_forge
Test-NotebookProperty -TestName "Fonction generate_image_forge()" -Critical -TestBlock {
    $AllCodeSource -match "def generate_image_forge\("
} -SuccessMessage "Fonction helper principale trouvée" `
  -FailureMessage "Fonction generate_image_forge() absente"

# Test 9: URL API Forge présente
Test-NotebookProperty -TestName "URL API Forge Configurée" -Critical -TestBlock {
    $AllCodeSource -match "turbo\.stable-diffusion-webui-forge\.myia\.io"
} -SuccessMessage "URL API Forge présente: https://turbo.stable-diffusion-webui-forge.myia.io" `
  -FailureMessage "URL API Forge non trouvée dans le code"

# Test 10: Paramètres Turbo optimaux documentés
Test-NotebookProperty -TestName "Paramètres Turbo Optimaux" -TestBlock {
    ($AllCodeSource -match "steps\s*[=:]\s*4") -and ($AllCodeSource -match "cfg_scale\s*[=:]\s*2\.0")
} -SuccessMessage "Paramètres Turbo (steps=4, cfg_scale=2.0) présents" `
  -FailureMessage "Paramètres Turbo absents ou incorrects"

# Test 11: Validation syntaxe Python (cellules code)
Write-Host "`n🧪 Test: Validation Syntaxe Python (7 cellules code)" -ForegroundColor Cyan

$SyntaxErrors = @()
$CodeCellsArray = $NotebookJson.cells | Where-Object { $_.cell_type -eq "code" }

for ($i = 0; $i -lt $CodeCellsArray.Count; $i++) {
    $cellSource = $CodeCellsArray[$i].source -join "`n"
    $tempPyFile = [System.IO.Path]::GetTempFileName() + ".py"
    
    try {
        Set-Content -Path $tempPyFile -Value $cellSource -Encoding UTF8
        
        # Validation syntaxe avec python -m py_compile
        $syntaxCheck = python -m py_compile $tempPyFile 2>&1
        
        if ($LASTEXITCODE -ne 0) {
            $SyntaxErrors += "Cellule Code $($i+1): $syntaxCheck"
        }
    } finally {
        Remove-Item $tempPyFile -ErrorAction SilentlyContinue
    }
}

Test-NotebookProperty -TestName "Syntaxe Python Valide (7 cellules)" -TestBlock {
    $SyntaxErrors.Count -eq 0
} -SuccessMessage "Toutes cellules code syntaxiquement valides" `
  -FailureMessage "Erreurs syntaxe: $($SyntaxErrors -join '; ')"

# Test 12: Présence docstrings
Test-NotebookProperty -TestName "Docstrings Fonction Helper" -TestBlock {
    $AllCodeSource -match '"""[\s\S]*?"""'
} -SuccessMessage "Docstrings présentes (documentation inline)" `
  -FailureMessage "Docstrings absentes ou insuffisantes"

# Test 13: Gestion erreurs (try/except)
Test-NotebookProperty -TestName "Gestion Erreurs (try/except)" -TestBlock {
    ($AllCodeSource -match "\btry\b") -and ($AllCodeSource -match "\bexcept\b")
} -SuccessMessage "Blocs try/except présents (gestion erreurs)" `
  -FailureMessage "Gestion erreurs absente"

# Test 14: Présence exercice pratique
$AllMarkdownSource = ($NotebookJson.cells | Where-Object { $_.cell_type -eq "markdown" } | ForEach-Object { $_.source -join "`n" }) -join "`n"

Test-NotebookProperty -TestName "Exercice Pratique Étudiant" -TestBlock {
    ($AllMarkdownSource -match "Exercice|TODO") -and ($AllCodeSource -match "mon_prompt")
} -SuccessMessage "Exercice pratique avec template code présent" `
  -FailureMessage "Exercice pratique absent ou incomplet"

# Test 15: Liens documentation externes
Test-NotebookProperty -TestName "Ressources Documentation" -TestBlock {
    $AllMarkdownSource -match "GUIDE-APIS-ETUDIANTS|Documentation|Ressources"
} -SuccessMessage "Liens ressources externes documentés" `
  -FailureMessage "Ressources documentation absentes"

# Résumé final
Write-Host "`n═══════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "   RÉSUMÉ TESTS" -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════`n" -ForegroundColor Cyan

Write-Host "✅ Tests réussis    : $TestsPassed" -ForegroundColor Green
Write-Host "⚠️ Avertissements   : $TestsWarning" -ForegroundColor Yellow
Write-Host "❌ Tests échoués    : $TestsFailed" -ForegroundColor Red

$TotalTests = $TestsPassed + $TestsWarning + $TestsFailed
$SuccessRate = [math]::Round(($TestsPassed / $TotalTests) * 100, 1)

Write-Host "`nTaux de réussite: $SuccessRate% ($TestsPassed/$TotalTests)`n" -ForegroundColor $(if ($SuccessRate -ge 90) { "Green" } elseif ($SuccessRate -ge 75) { "Yellow" } else { "Red" })

# Ajout résumé au rapport
$Report += @"

---

## Statistiques Tests

| Métrique | Valeur |
|----------|--------|
| **Tests réussis** | ✅ $TestsPassed |
| **Avertissements** | ⚠️ $TestsWarning |
| **Tests échoués** | ❌ $TestsFailed |
| **Total tests** | $TotalTests |
| **Taux de réussite** | **$SuccessRate%** |

---

## Validation Globale

"@

if ($TestsFailed -eq 0 -and $TestsWarning -eq 0) {
    $Report += "### ✅ NOTEBOOK VALIDÉ (100%)`n`nLe notebook répond à tous les critères de qualité."
    $ExitCode = 0
} elseif ($TestsFailed -eq 0) {
    $Report += "### ⚠️ NOTEBOOK VALIDÉ AVEC AVERTISSEMENTS ($SuccessRate%)`n`nLe notebook est fonctionnel mais nécessite ajustements mineurs."
    $ExitCode = 1
} else {
    $Report += "### ❌ NOTEBOOK NON VALIDÉ ($SuccessRate%)`n`n**$TestsFailed test(s) critique(s) échoué(s)**. Corrections nécessaires avant déploiement."
    $ExitCode = 2
}

$Report += @"


---

## Détails Notebook Analysé

| Propriété | Valeur |
|-----------|--------|
| **Chemin** | ``$NotebookPath`` |
| **Taille fichier** | $([math]::Round($FileSize/1KB, 2)) KB |
| **Cellules totales** | $CellCount |
| **Cellules Markdown** | $MarkdownCells |
| **Cellules Code** | $CodeCells |
| **Version nbformat** | $($NotebookJson.nbformat) |
| **Kernel** | $($NotebookJson.metadata.kernelspec.display_name) |

---

## Recommandations

"@

if ($TestsWarning -gt 0 -or $TestsFailed -gt 0) {
    $Report += "### Actions Correctives`n`n"
    if ($TestsFailed -gt 0) {
        $Report += "1. **Corriger tests critiques échoués** (voir détails ci-dessus)`n"
    }
    if ($TestsWarning -gt 0) {
        $Report += "2. **Examiner avertissements** (améliorations recommandées)`n"
    }
    $Report += "3. **Réexécuter script tests** après corrections`n"
} else {
    $Report += "✅ Aucune action requise. Notebook prêt pour Phase 8 (Checkpoint SDDD).`n"
}

$Report += @"


---

## Prochaines Étapes

### Phase 18 - Partie 8: Checkpoint SDDD Validation

1. [ ] Validation qualité pédagogique (progression logique)
2. [ ] Recherche sémantique validation découvrabilité
3. [ ] Documentation checkpoint SDDD

### Phase 18 - Partie 9: Documentation Notebook

1. [ ] Création README notebook
2. [ ] Guide installation dépendances
3. [ ] Exemples résultats attendus

---

**Date génération rapport**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**Script**: ``2025-10-18_01_tester-notebook-forge.ps1``  
**Phase**: 18 - Partie 7 (Tests Fonctionnels)
"@

# Sauvegarde rapport
Set-Content -Path $ReportPath -Value $Report -Encoding UTF8
Write-Host "📄 Rapport sauvegardé: $ReportPath`n" -ForegroundColor Cyan

# Fin script
exit $ExitCode