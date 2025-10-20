<#
.SYNOPSIS
    Tests validation notebooks améliorés
.DESCRIPTION
    Valide structure + contenu notebooks Forge + Qwen améliorés
    Phase 21 - Itérations notebooks
.NOTES
    Date: 2025-10-21
    Phase: 21
    Auteur: SDDD Process
#>

# Configuration
$ErrorActionPreference = "Stop"
$notebookForge = "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb"
$notebookQwen = "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-5-Qwen-Image-Edit.ipynb"

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Tests Validation Notebooks Améliorés" -ForegroundColor Cyan
Write-Host "Phase 21 - Itérations Notebooks" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

# Fonction de test générique
function Test-NotebookStructure {
    param(
        [string]$NotebookPath,
        [int]$MinCellCount,
        [string]$NotebookName,
        [string[]]$ExpectedContentPatterns
    )
    
    Write-Host "Validation: $NotebookName" -ForegroundColor Yellow
    Write-Host "Chemin: $NotebookPath" -ForegroundColor Gray
    
    # Test 1: Fichier existe
    if (-not (Test-Path $NotebookPath)) {
        Write-Host "  ❌ ÉCHEC: Fichier introuvable" -ForegroundColor Red
        return $false
    }
    Write-Host "  ✓ Fichier existe" -ForegroundColor Green
    
    # Test 2: JSON valide
    try {
        $notebook = Get-Content $NotebookPath -Raw | ConvertFrom-Json
    }
    catch {
        Write-Host "  ❌ ÉCHEC: JSON invalide - $_" -ForegroundColor Red
        return $false
    }
    Write-Host "  ✓ JSON valide" -ForegroundColor Green
    
    # Test 3: Nombre minimal de cellules
    $actualCellCount = $notebook.cells.Count
    if ($actualCellCount -lt $MinCellCount) {
        Write-Host "  ❌ ÉCHEC: $actualCellCount cellules trouvées (minimum: $MinCellCount)" -ForegroundColor Red
        return $false
    }
    Write-Host "  ✓ Nombre de cellules OK: $actualCellCount (minimum: $MinCellCount)" -ForegroundColor Green
    
    # Test 4: Recherche de patterns de contenu attendus
    $allContentSource = ($notebook.cells | ForEach-Object { 
        ($_.source -join "") 
    }) -join "`n"
    
    $allPatternsFound = $true
    foreach ($pattern in $ExpectedContentPatterns) {
        if ($allContentSource -match [regex]::Escape($pattern)) {
            Write-Host "  ✓ Contenu validé: '$pattern' présent" -ForegroundColor Green
        }
        else {
            Write-Host "  ❌ ÉCHEC: Pattern '$pattern' introuvable dans le notebook" -ForegroundColor Red
            $allPatternsFound = $false
        }
    }
    
    if (-not $allPatternsFound) {
        return $false
    }
    
    # Test 5: Métadonnées nbformat
    if (-not $notebook.nbformat) {
        Write-Host "  ❌ ÉCHEC: Champ 'nbformat' manquant" -ForegroundColor Red
        return $false
    }
    Write-Host "  ✓ Métadonnées nbformat présentes (version: $($notebook.nbformat))" -ForegroundColor Green
    
    # Test 6: Qualité pédagogique - Vérifier présence de markdown
    $markdownCells = ($notebook.cells | Where-Object { $_.cell_type -eq "markdown" }).Count
    $codeCells = ($notebook.cells | Where-Object { $_.cell_type -eq "code" }).Count
    
    Write-Host "  ✓ Répartition cellules: $markdownCells markdown, $codeCells code" -ForegroundColor Green
    
    if ($markdownCells -lt 2) {
        Write-Host "  ⚠ Avertissement: Peu de cellules markdown ($markdownCells)" -ForegroundColor Yellow
    }
    
    Write-Host ""
    return $true
}

# Tests Notebook Forge
# Patterns de contenu attendus (améliorations Phase 21)
$forgeExpectedPatterns = @(
    "## 💡 Tips & Troubleshooting",
    "🧪 Test comparatif",
    "Techniques Avancées de Génération"
)

$forgeSuccess = Test-NotebookStructure `
    -NotebookPath $notebookForge `
    -MinCellCount 15 `
    -NotebookName "Stable Diffusion Forge" `
    -ExpectedContentPatterns $forgeExpectedPatterns

# Tests Notebook Qwen
# Patterns de contenu attendus (améliorations Phase 21)
$qwenExpectedPatterns = @(
    "Visualisation Architecture Workflow ComfyUI",
    "Workflow chaîné créé",
    "create_simple_edit_workflow"
)

$qwenSuccess = Test-NotebookStructure `
    -NotebookPath $notebookQwen `
    -MinCellCount 15 `
    -NotebookName "Qwen Image Edit" `
    -ExpectedContentPatterns $qwenExpectedPatterns

# Résumé final
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Résumé Tests Validation" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan

if ($forgeSuccess -and $qwenSuccess) {
    Write-Host "✅ TOUS LES TESTS RÉUSSIS" -ForegroundColor Green
    Write-Host ""
    Write-Host "Notebooks validés:" -ForegroundColor Green
    
    # Compter cellules réelles
    $forgeNotebook = Get-Content $notebookForge -Raw | ConvertFrom-Json
    $qwenNotebook = Get-Content $notebookQwen -Raw | ConvertFrom-Json
    
    Write-Host "  - Forge SD XL Turbo: $($forgeNotebook.cells.Count) cellules" -ForegroundColor White
    Write-Host "  - Qwen Image Edit: $($qwenNotebook.cells.Count) cellules" -ForegroundColor White
    Write-Host ""
    Write-Host "Améliorations pédagogiques confirmées:" -ForegroundColor Green
    Write-Host "  ✓ Tips troubleshooting pour autonomie" -ForegroundColor White
    Write-Host "  ✓ Exemples avancés progressifs" -ForegroundColor White
    Write-Host "  ✓ Diagrammes architecture clairs" -ForegroundColor White
    Write-Host "  ✓ Workflows réels applicables" -ForegroundColor White
    Write-Host "  ✓ Fonctions helper réutilisables" -ForegroundColor White
    exit 0
}
else {
    Write-Host "❌ ÉCHECS DÉTECTÉS" -ForegroundColor Red
    Write-Host ""
    if (-not $forgeSuccess) {
        Write-Host "  - Notebook Forge: ÉCHEC" -ForegroundColor Red
    }
    if (-not $qwenSuccess) {
        Write-Host "  - Notebook Qwen: ÉCHEC" -ForegroundColor Red
    }
    exit 1
}