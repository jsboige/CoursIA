# Script de génération automatisée des résumés pour tous les fichiers de trace
# Auteur : Roo Code - Formation IA Pauwels Consulting
# Date : 09/09/2025

[CmdletBinding()]
param(
    [string]$SourceDirectory = "corriges",
    [string]$ScriptPath = ".\Convert-TraceToSummary-Optimized.ps1",
    [switch]$WhatIf,
    [switch]$Force
)

# Configuration UTF-8
$OutputEncoding = [System.Text.Encoding]::UTF8
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$PSDefaultParameterValues['Out-File:Encoding'] = 'utf8'
$PSDefaultParameterValues['Set-Content:Encoding'] = 'utf8'
Write-Host "Configuration UTF-8 chargee automatiquement" -ForegroundColor Green

Write-Host "=== GENERATION AUTOMATISEE DES RESUMES ===" -ForegroundColor Cyan
Write-Host "Source Directory: $SourceDirectory" -ForegroundColor Yellow
Write-Host "Script Path: $ScriptPath" -ForegroundColor Yellow

# Vérification de l'existence du script
if (-not (Test-Path $ScriptPath)) {
    Write-Error "Le script $ScriptPath n'existe pas!"
    exit 1
}

# Recherche récursive de tous les fichiers de trace (ORIGINAUX uniquement)
Write-Host "Recherche des fichiers de trace originaux..." -ForegroundColor Yellow
$traceFiles = Get-ChildItem -Path $SourceDirectory -Filter "roo_task_*.md" -Recurse |
              Where-Object {
                  # Exclure tous les fichiers générés/résumés
                  $_.Name -notmatch "_lecture_" -and
                  $_.Name -notmatch "_Summary\.md$" -and
                  $_.Name -notmatch "_Messages\.md$" -and
                  $_.Name -notmatch "_Full\.md$" -and
                  $_.Name -notmatch "_UserOnly\.md$" -and
                  $_.Name -notmatch "_NoTools\.md$" -and
                  $_.Name -notmatch "_NoResults\.md$" -and
                  # Exclure les anciens formats de résumés avec troncature
                  $_.Name -notmatch "_Summary_T\d+\.md$" -and
                  $_.Name -notmatch "_NoTools_T\d+\.md$" -and
                  $_.Name -notmatch "_NoResults_T\d+\.md$" -and
                  $_.Name -notmatch "_Full_T\d+\.md$" -and
                  $_.Name -notmatch "_UserOnly_T\d+\.md$" -and
                  $_.Name -notmatch "_Messages_T\d+\.md$" -and
                  # Exclure les anciens formats avec suffixes spéciaux
                  $_.Name -notmatch "_summary_Summary_Compact\.md$" -and
                  $_.Name -notmatch "_TEST_summary\.md$"
              }

Write-Host "Fichiers de trace trouves: $($traceFiles.Count)" -ForegroundColor Green

if ($traceFiles.Count -eq 0) {
    Write-Warning "Aucun fichier de trace trouve dans $SourceDirectory"
    exit 0
}

# Affichage de la liste des fichiers
Write-Host "" -ForegroundColor Cyan
Write-Host "Liste des fichiers a traiter:" -ForegroundColor Cyan
$traceFiles | ForEach-Object { 
    $relativePath = $_.FullName.Replace((Get-Location).Path + "\", "")
    Write-Host "  - $relativePath" -ForegroundColor Gray
}

if ($WhatIf) {
    Write-Host "" -ForegroundColor Yellow
    Write-Host "[SIMULATION] Aucune generation effectuee (parametre -WhatIf active)" -ForegroundColor Yellow
    exit 0
}

# Confirmation utilisateur
Write-Host "" -ForegroundColor Yellow
if (-not $Force -and -not $WhatIf) {
    Write-Host "Utilisez -Force pour lancer la generation automatique ou -WhatIf pour simuler." -ForegroundColor Yellow
    Write-Host "Exemple: ./Generate-All-Summaries.ps1 -SourceDirectory '../../corriges' -Force" -ForegroundColor Cyan
    exit 0
}

# Traitement de chaque fichier
$totalFiles = $traceFiles.Count
$successCount = 0
$failureCount = 0
$startTime = Get-Date

Write-Host "" -ForegroundColor Cyan
Write-Host "=== DEBUT DU TRAITEMENT ===" -ForegroundColor Cyan

foreach ($i in 0..($totalFiles-1)) {
    $file = $traceFiles[$i]
    $progress = [math]::Round(($i / $totalFiles) * 100, 1)
    $relativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
    
    Write-Host "" -ForegroundColor White
    Write-Host "[$($i+1)/$totalFiles - $progress%] Traitement: $relativePath" -ForegroundColor White
    
    try {
        # Exécution du script avec GenerateAllVariants
        $scriptResult = & $ScriptPath -TracePath $relativePath -GenerateAllVariants 2>&1
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "  Generation reussie" -ForegroundColor Green
            $successCount++
        } else {
            Write-Host "  Erreur lors de la generation (Exit Code: $LASTEXITCODE)" -ForegroundColor Red
            Write-Host "  Sortie: $scriptResult" -ForegroundColor Gray
            $failureCount++
        }
        
    } catch {
        Write-Host "  Exception: $($_.Exception.Message)" -ForegroundColor Red
        $failureCount++
    }
    
    # Petit délai pour éviter la surcharge
    Start-Sleep -Milliseconds 100
}

$endTime = Get-Date
$duration = $endTime - $startTime

Write-Host "" -ForegroundColor Cyan
Write-Host "=== RESUME DE L'OPERATION ===" -ForegroundColor Cyan
Write-Host "Fichiers traites avec succes: $successCount" -ForegroundColor Green
Write-Host "Fichiers en echec: $failureCount" -ForegroundColor $(if ($failureCount -gt 0) { "Red" } else { "Green" })
Write-Host "Duree totale: $($duration.ToString('mm\:ss'))" -ForegroundColor Yellow

if ($failureCount -eq 0) {
    Write-Host "" -ForegroundColor Green
    Write-Host "TOUS LES FICHIERS ONT ETE TRAITES AVEC SUCCES!" -ForegroundColor Green
} else {
    Write-Host "" -ForegroundColor Yellow
    Write-Host "Certains fichiers n'ont pas pu etre traites." -ForegroundColor Yellow
}

Write-Host "" -ForegroundColor Cyan
Write-Host "Generation terminee." -ForegroundColor Cyan