o#!/usr/bin/env pwsh

<#
.SYNOPSIS
Backup sécurisé structure GenAI existante avant Phase 2

.DESCRIPTION  
Script de sauvegarde complète du répertoire MyIA.AI.Notebooks/GenAI
avant implémentation de l'architecture modulaire Phase 2.
Préserve tous les assets critiques : notebooks, configurations, data.

.PARAMETER Force
Force la création du backup même si un existe déjà

.EXAMPLE
.\33-backup-genai-before-phase2-20251008.ps1
.\33-backup-genai-before-phase2-20251008.ps1 -Force
#>

[CmdletBinding()]
param(
    [switch]$Force
)

$ErrorActionPreference = "Stop"

Write-Host "🔄 BACKUP GENAI AVANT PHASE 2" -ForegroundColor Cyan
Write-Host "===============================" -ForegroundColor Cyan

$BackupTimestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
$SourcePath = "MyIA.AI.Notebooks/GenAI"
$BackupPath = "MyIA.AI.Notebooks/GenAI_BACKUP_PHASE2_$BackupTimestamp"

# Vérification existence source
if (-not (Test-Path $SourcePath)) {
    Write-Host "❌ Source non trouvée: $SourcePath" -ForegroundColor Red
    exit 1
}

# Vérification backup existant
if ((Test-Path $BackupPath) -and -not $Force) {
    Write-Host "⚠️ Backup existe déjà: $BackupPath" -ForegroundColor Yellow
    Write-Host "💡 Utilisez -Force pour écraser" -ForegroundColor Yellow
    exit 0
}

try {
    Write-Host "📁 Source: $SourcePath" -ForegroundColor Green
    Write-Host "💾 Backup: $BackupPath" -ForegroundColor Green
    
    # Création backup complet
    Copy-Item -Path $SourcePath -Destination $BackupPath -Recurse -Force
    
    # Inventaire
    $Items = Get-ChildItem -Path $BackupPath -Recurse | Measure-Object
    Write-Host "📊 Éléments sauvegardés: $($Items.Count)" -ForegroundColor Yellow
    
    # Vérification assets critiques
    $CriticalAssets = @(
        "DMC_colors.json",
        "img2img_cross_stitch_pattern_maker.ipynb",
        ".env.example",
        "SemanticKernel",
        "EPF"
    )
    
    Write-Host "🔍 Assets critiques:" -ForegroundColor Yellow
    foreach ($asset in $CriticalAssets) {
        $assetPath = Join-Path $BackupPath $asset
        if (Test-Path $assetPath) {
            Write-Host "  ✅ $asset" -ForegroundColor Green
        } else {
            Write-Host "  ⚠️ $asset (optionnel)" -ForegroundColor Yellow
        }
    }
    
    # Création fichier manifest
    $Manifest = @{
        backup_timestamp = $BackupTimestamp
        source_path = $SourcePath
        backup_path = $BackupPath
        total_items = $Items.Count
        critical_assets = $CriticalAssets
        created_by = "Phase 2.1 Implementation"
    }
    
    $ManifestPath = Join-Path $BackupPath "BACKUP_MANIFEST.json"
    $Manifest | ConvertTo-Json -Depth 3 | Set-Content -Path $ManifestPath -Encoding UTF8
    
    Write-Host "✅ BACKUP COMPLÉTÉ AVEC SUCCÈS" -ForegroundColor Green
    Write-Host "📄 Manifest: $ManifestPath" -ForegroundColor Cyan
    
} catch {
    Write-Host "❌ ERREUR BACKUP: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}