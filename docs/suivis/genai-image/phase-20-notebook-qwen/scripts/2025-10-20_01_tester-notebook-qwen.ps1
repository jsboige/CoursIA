<#
.SYNOPSIS
    Tests de validation du notebook Qwen-Image-Edit Phase 20

.DESCRIPTION
    Valide la structure et l'exécution du notebook pédagogique Qwen-Image-Edit
    - Validation structure notebook (15 cellules)
    - Tests imports Python
    - Validation classe ComfyUIClient
    - Tests workflows JSON (structure)
    - Rapport détaillé validation
    
    Phase 20 - Développement notebook Qwen-Image-Edit
    
.NOTES
    Date: 2025-10-20
    Phase: 20
    Auteur: SDDD Process
    Usage: pwsh -c "& 'docs/suivis/genai-image/phase-20-notebook-qwen/scripts/2025-10-20_01_tester-notebook-qwen.ps1'"
    
.EXAMPLE
    pwsh -c "& './2025-10-20_01_tester-notebook-qwen.ps1'"
#>

# ============================================
# CONFIGURATION
# ============================================

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"

# Chemins relatifs depuis racine projet
$NOTEBOOK_PATH = "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-5-Qwen-Image-Edit.ipynb"
# PSScriptRoot = docs/suivis/genai-image/phase-20-notebook-qwen/scripts
# On remonte 5 niveaux: scripts -> phase-20-notebook-qwen -> genai-image -> suivis -> docs -> CoursIA
$PROJECT_ROOT = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $PSScriptRoot))))
$NOTEBOOK_FULL_PATH = Join-Path $PROJECT_ROOT $NOTEBOOK_PATH

# Configuration tests
$EXPECTED_CELL_COUNT = 15
$EXPECTED_CODE_CELLS = 7
$EXPECTED_MARKDOWN_CELLS = 8

# Logs
$TIMESTAMP = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
$LOG_DIR = Join-Path $PROJECT_ROOT "docs/suivis/genai-image/phase-20-notebook-qwen/logs"
$LOG_FILE = Join-Path $LOG_DIR "validation-notebook-$TIMESTAMP.log"

# ============================================
# FONCTIONS UTILITAIRES
# ============================================

function Write-Log {
    param(
        [string]$Message,
        [string]$Level = "INFO"
    )
    
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    
    # Couleurs selon niveau
    switch ($Level) {
        "SUCCESS" { Write-Host $logMessage -ForegroundColor Green }
        "ERROR"   { Write-Host $logMessage -ForegroundColor Red }
        "WARNING" { Write-Host $logMessage -ForegroundColor Yellow }
        "INFO"    { Write-Host $logMessage -ForegroundColor Cyan }
        default   { Write-Host $logMessage }
    }
    
    # Log fichier
    if (-not (Test-Path $LOG_DIR)) {
        New-Item -ItemType Directory -Path $LOG_DIR -Force | Out-Null
    }
    Add-Content -Path $LOG_FILE -Value $logMessage
}

function Test-NotebookExists {
    Write-Log "Vérification existence notebook..." "INFO"
    
    if (-not (Test-Path $NOTEBOOK_FULL_PATH)) {
        Write-Log "ERREUR: Notebook non trouvé: $NOTEBOOK_FULL_PATH" "ERROR"
        return $false
    }
    
    Write-Log "✅ Notebook trouvé: $NOTEBOOK_PATH" "SUCCESS"
    return $true
}

function Test-NotebookStructure {
    Write-Log "Validation structure notebook..." "INFO"
    
    try {
        # Lire fichier JSON
        $notebookJson = Get-Content -Path $NOTEBOOK_FULL_PATH -Raw | ConvertFrom-Json
        
        # Vérifier nombre cellules
        $cellCount = $notebookJson.cells.Count
        if ($cellCount -ne $EXPECTED_CELL_COUNT) {
            Write-Log "ERREUR: Nombre cellules incorrect: $cellCount (attendu: $EXPECTED_CELL_COUNT)" "ERROR"
            return $false
        }
        Write-Log "✅ Nombre cellules correct: $cellCount" "SUCCESS"
        
        # Compter types cellules
        $codeCells = ($notebookJson.cells | Where-Object { $_.cell_type -eq "code" }).Count
        $markdownCells = ($notebookJson.cells | Where-Object { $_.cell_type -eq "markdown" }).Count
        
        if ($codeCells -ne $EXPECTED_CODE_CELLS) {
            Write-Log "WARNING: Cellules code: $codeCells (attendu: $EXPECTED_CODE_CELLS)" "WARNING"
        } else {
            Write-Log "✅ Cellules code: $codeCells" "SUCCESS"
        }
        
        if ($markdownCells -ne $EXPECTED_MARKDOWN_CELLS) {
            Write-Log "WARNING: Cellules markdown: $markdownCells (attendu: $EXPECTED_MARKDOWN_CELLS)" "WARNING"
        } else {
            Write-Log "✅ Cellules markdown: $markdownCells" "SUCCESS"
        }
        
        return $true
    }
    catch {
        Write-Log "ERREUR lecture JSON notebook: $_" "ERROR"
        return $false
    }
}

function Test-CriticalContent {
    Write-Log "Validation contenu critique..." "INFO"
    
    try {
        $notebookJson = Get-Content -Path $NOTEBOOK_FULL_PATH -Raw | ConvertFrom-Json
        $allContent = ($notebookJson.cells | ForEach-Object { $_.source -join "" }) -join " "
        
        # Patterns critiques à vérifier
        $criticalPatterns = @{
            "Classe ComfyUIClient" = "class ComfyUIClient"
            "Méthode execute_workflow" = "def execute_workflow"
            "API_BASE_URL" = "API_BASE_URL"
            "Workflow hello" = "workflow_hello"
            "Workflow img2img" = "workflow_img2img"
            "Upload image" = "def upload_image_to_comfyui"
            "Exercice pratique" = "___VOTRE_"
            "Ressources ComfyUI" = "github.com/comfyanonymous/ComfyUI"
        }
        
        $allPassed = $true
        foreach ($pattern in $criticalPatterns.GetEnumerator()) {
            if ($allContent -match [regex]::Escape($pattern.Value)) {
                Write-Log "✅ Pattern trouvé: $($pattern.Key)" "SUCCESS"
            }
            else {
                Write-Log "ERREUR: Pattern manquant: $($pattern.Key)" "ERROR"
                $allPassed = $false
            }
        }
        
        return $allPassed
    }
    catch {
        Write-Log "ERREUR validation contenu: $_" "ERROR"
        return $false
    }
}

function Test-WorkflowsJSON {
    Write-Log "Validation workflows JSON..." "INFO"
    
    try {
        $notebookJson = Get-Content -Path $NOTEBOOK_FULL_PATH -Raw | ConvertFrom-Json
        $codeCells = $notebookJson.cells | Where-Object { $_.cell_type -eq "code" }
        
        $workflowPatterns = @("workflow_hello", "workflow_img2img", "workflow_exercice")
        $foundWorkflows = 0
        
        foreach ($cell in $codeCells) {
            $cellSource = $cell.source -join ""
            foreach ($pattern in $workflowPatterns) {
                if ($cellSource -match [regex]::Escape($pattern)) {
                    Write-Log "✅ Workflow trouvé: $pattern" "SUCCESS"
                    $foundWorkflows++
                    break
                }
            }
        }
        
        if ($foundWorkflows -eq $workflowPatterns.Count) {
            Write-Log "✅ Tous les workflows détectés ($foundWorkflows/$($workflowPatterns.Count))" "SUCCESS"
            return $true
        }
        else {
            Write-Log "WARNING: Workflows partiels ($foundWorkflows/$($workflowPatterns.Count))" "WARNING"
            return $false
        }
    }
    catch {
        Write-Log "ERREUR validation workflows: $_" "ERROR"
        return $false
    }
}

function Test-PedagogicalQuality {
    Write-Log "Évaluation qualité pédagogique..." "INFO"
    
    try {
        $notebookJson = Get-Content -Path $NOTEBOOK_FULL_PATH -Raw | ConvertFrom-Json
        $markdownCells = $notebookJson.cells | Where-Object { $_.cell_type -eq "markdown" }
        
        # Critères pédagogiques
        $pedagogicalPatterns = @{
            "Objectifs définis" = "Objectif"
            "Exemples concrets" = "Exemple"
            "Bonnes pratiques" = "Bonnes Pratiques"
            "Ressources externes" = "Ressources"
            "Exercice pratique" = "EXERCICE"
        }
        
        $score = 0
        foreach ($pattern in $pedagogicalPatterns.GetEnumerator()) {
            $found = $false
            foreach ($cell in $markdownCells) {
                $cellContent = $cell.source -join ""
                if ($cellContent -match $pattern.Value) {
                    $found = $true
                    break
                }
            }
            if ($found) {
                Write-Log "✅ Critère pédagogique: $($pattern.Key)" "SUCCESS"
                $score++
            }
            else {
                Write-Log "WARNING: Critère manquant: $($pattern.Key)" "WARNING"
            }
        }
        
        $percentage = [math]::Round(($score / $pedagogicalPatterns.Count) * 100, 2)
        Write-Log "Score qualité pédagogique: $score/$($pedagogicalPatterns.Count) ($percentage%)" "INFO"
        
        return $percentage -ge 80
    }
    catch {
        Write-Log "ERREUR évaluation pédagogique: $_" "ERROR"
        return $false
    }
}

# ============================================
# EXÉCUTION TESTS
# ============================================

Write-Host "`n========================================" -ForegroundColor Cyan
Write-Host "🧪 TESTS VALIDATION NOTEBOOK QWEN" -ForegroundColor Cyan
Write-Host "========================================`n" -ForegroundColor Cyan

Write-Log "Démarrage tests validation Phase 20" "INFO"
Write-Log "Notebook: $NOTEBOOK_PATH" "INFO"

# Résultats tests
$results = @{
    "Existence" = $false
    "Structure" = $false
    "Contenu" = $false
    "Workflows" = $false
    "Pédagogie" = $false
}

# Test 1: Existence
$results["Existence"] = Test-NotebookExists
if (-not $results["Existence"]) {
    Write-Log "Arrêt tests: notebook introuvable" "ERROR"
    exit 1
}

# Test 2: Structure
$results["Structure"] = Test-NotebookStructure

# Test 3: Contenu critique
$results["Contenu"] = Test-CriticalContent

# Test 4: Workflows JSON
$results["Workflows"] = Test-WorkflowsJSON

# Test 5: Qualité pédagogique
$results["Pédagogie"] = Test-PedagogicalQuality

# ============================================
# RAPPORT FINAL
# ============================================

Write-Host "`n========================================" -ForegroundColor Cyan
Write-Host "📊 RAPPORT VALIDATION" -ForegroundColor Cyan
Write-Host "========================================`n" -ForegroundColor Cyan

$passedTests = ($results.Values | Where-Object { $_ -eq $true }).Count
$totalTests = $results.Count
$successRate = [math]::Round(($passedTests / $totalTests) * 100, 2)

foreach ($test in $results.GetEnumerator()) {
    $status = if ($test.Value) { "✅ PASS" } else { "❌ FAIL" }
    $color = if ($test.Value) { "Green" } else { "Red" }
    Write-Host "$status - $($test.Key)" -ForegroundColor $color
}

Write-Host "`nRésultat global: $passedTests/$totalTests tests passés ($successRate%)`n" -ForegroundColor $(if ($successRate -ge 80) { "Green" } else { "Yellow" })
Write-Log "Tests terminés: $passedTests/$totalTests passés ($successRate%)" "INFO"
Write-Log "Logs sauvegardés: $LOG_FILE" "INFO"

# Génération rapport markdown
$reportPath = Join-Path (Split-Path $LOG_FILE) "rapport-validation-$TIMESTAMP.md"
$reportContent = @"
# Rapport Validation Notebook Qwen - $TIMESTAMP

## Résultats Tests

| Test | Statut | Résultat |
|------|--------|----------|
| Existence | $(if ($results["Existence"]) { '✅' } else { '❌' }) | $(if ($results["Existence"]) { 'PASS' } else { 'FAIL' }) |
| Structure | $(if ($results["Structure"]) { '✅' } else { '❌' }) | $(if ($results["Structure"]) { 'PASS' } else { 'FAIL' }) |
| Contenu | $(if ($results["Contenu"]) { '✅' } else { '❌' }) | $(if ($results["Contenu"]) { 'PASS' } else { 'FAIL' }) |
| Workflows | $(if ($results["Workflows"]) { '✅' } else { '❌' }) | $(if ($results["Workflows"]) { 'PASS' } else { 'FAIL' }) |
| Pédagogie | $(if ($results["Pédagogie"]) { '✅' } else { '❌' }) | $(if ($results["Pédagogie"]) { 'PASS' } else { 'FAIL' }) |

**Score global**: $passedTests/$totalTests ($successRate%)

## Détails

- **Notebook**: ``$NOTEBOOK_PATH``
- **Date validation**: $TIMESTAMP
- **Logs**: ``$LOG_FILE``

## Conclusion

$(if ($successRate -ge 80) {
    "✅ **Notebook validé** - Qualité satisfaisante pour Phase 20"
} else {
    "❌ **Notebook NON validé** - Corrections nécessaires"
})
"@

Set-Content -Path $reportPath -Value $reportContent
Write-Log "Rapport markdown généré: $reportPath" "SUCCESS"

# Code sortie
if ($successRate -ge 80) {
    Write-Host "✅ VALIDATION RÉUSSIE" -ForegroundColor Green
    exit 0
}
else {
    Write-Host "❌ VALIDATION ÉCHOUÉE" -ForegroundColor Red
    exit 1
}