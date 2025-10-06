#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Script de nettoyage des notebooks temporaires et de diagnostic
    
.DESCRIPTION
    Ce script supprime tous les fichiers notebooks temporaires qui ont ete reveles 
    apres avoir nettoye les patterns "paresseux" du .gitignore.
    
    Types de fichiers supprimes :
    - *_executed*.ipynb : Notebooks executes par Papermill/MCP
    - *-diagnostic*.ipynb : Notebooks de diagnostic temporaires  
    - *-validation-MCP.ipynb : Notebooks de validation MCP temporaires
    - test-*.ipynb : Notebooks de test temporaires
    
.PARAMETER DryRun
    Mode simulation - affiche les fichiers qui seraient supprimes sans les supprimer
    
.PARAMETER Verbose
    Affichage detaille des operations
    
.EXAMPLE
    .\clean-temporary-notebooks.ps1 -DryRun
    Simule le nettoyage et affiche les fichiers qui seraient supprimes
    
.EXAMPLE 
    .\clean-temporary-notebooks.ps1 -Verbose
    Execute le nettoyage avec affichage detaille
    
.NOTES
    Auteur: Roo Debug Agent
    Date: 2025-10-06
    Contexte: Nettoyage post-suppression patterns paresseux .gitignore
    
    IMPORTANT: Ce script est concu pour nettoyer les artefacts temporaires 
    reveles apres avoir supprime les patterns "*_executed.ipynb", "test-*.ipynb" 
    du .gitignore qui etaient utilises pour masquer la flemme de nettoyage.
#>

param(
    [switch]$DryRun = $false,
    [switch]$Verbose = $false
)

# Configuration des couleurs et logging
$ErrorActionPreference = 'Continue'
if ($Verbose) { $VerbosePreference = 'Continue' }

Write-Host "=== SCRIPT DE NETTOYAGE NOTEBOOKS TEMPORAIRES ===" -ForegroundColor Yellow
Write-Host "Repertoire de travail: $(Get-Location)" -ForegroundColor Cyan
if ($DryRun) {
    Write-Host "MODE SIMULATION - Aucun fichier ne sera supprime" -ForegroundColor Magenta
}
Write-Host ""

# Patterns de fichiers temporaires a nettoyer
$patterns = @{
    "Notebooks executes Papermill/MCP" = "*_executed*.ipynb"
    "Notebooks diagnostic temporaires" = "*-diagnostic*.ipynb" 
    "Notebooks validation MCP temporaires" = "*-validation-MCP.ipynb"
    "Notebooks test temporaires" = "test-*.ipynb"
}

$totalFiles = 0
$totalSize = 0

# Parcours de chaque pattern
foreach ($category in $patterns.Keys) {
    $pattern = $patterns[$category]
    Write-Host "Recherche: $category ($pattern)" -ForegroundColor Green
    
    $files = Get-ChildItem -Path . -Recurse -Filter $pattern -File
    
    if ($files.Count -eq 0) {
        Write-Host "   Aucun fichier trouve" -ForegroundColor Gray
        continue
    }
    
    Write-Host "   Trouve $($files.Count) fichier(s)" -ForegroundColor Yellow
    
    foreach ($file in $files) {
        $relativePath = Resolve-Path -Relative $file.FullName
        $sizeKB = [Math]::Round($file.Length / 1KB, 2)
        $totalSize += $file.Length
        
        if ($DryRun) {
            Write-Host "   [SIMULATION] SUPPRIME: $relativePath ($sizeKB KB)" -ForegroundColor Magenta
        } else {
            try {
                Remove-Item -Path $file.FullName -Force
                Write-Host "   SUPPRIME: $relativePath ($sizeKB KB)" -ForegroundColor Red
                $totalFiles++
            }
            catch {
                Write-Host "   ERREUR: $relativePath - $($_.Exception.Message)" -ForegroundColor Red
            }
        }
    }
    Write-Host ""
}

# Resume final
$totalSizeMB = [Math]::Round($totalSize / 1MB, 2)
Write-Host "=== RESUME NETTOYAGE ===" -ForegroundColor Yellow

if ($DryRun) {
    $totalFound = (Get-ChildItem -Path . -Recurse | Where-Object { 
        $_.Name -like "*_executed*.ipynb" -or 
        $_.Name -like "*-diagnostic*.ipynb" -or 
        $_.Name -like "*-validation-MCP.ipynb" -or 
        $_.Name -like "test-*.ipynb" 
    }).Count
    Write-Host "Total fichiers a supprimer: $totalFound" -ForegroundColor Cyan
    Write-Host "Taille totale a liberer: $totalSizeMB MB" -ForegroundColor Cyan
    Write-Host "Executez sans -DryRun pour effectuer le nettoyage" -ForegroundColor Green
} else {
    Write-Host "Fichiers supprimes: $totalFiles" -ForegroundColor Green
    Write-Host "Espace libere: $totalSizeMB MB" -ForegroundColor Green
    Write-Host "Nettoyage termine avec succes!" -ForegroundColor Green
}

Write-Host ""
Write-Host "Conseil: Verifiez avec 'git status' que seuls les fichiers legitimes restent" -ForegroundColor Cyan