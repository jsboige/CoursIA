#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Script intelligent de nettoyage des notebooks temporaires et fichiers de développement
    
.DESCRIPTION
    Ce script supprime intelligemment tous les fichiers temporaires générés pendant 
    le développement et les tests de l'architecture ExecutionManager, tout en préservant
    les fichiers importants.
    
    Types de fichiers supprimés :
    - *_executed*.ipynb : Notebooks exécutés par Papermill/MCP
    - *_test*.ipynb, *_fixed*.ipynb : Notebooks de test et corrections temporaires
    - debug-*.ipynb : Notebooks de debug temporaires
    - diagnostic-*.ipynb : Notebooks de diagnostic temporaires
    - *-validation-MCP.ipynb : Notebooks de validation MCP temporaires
    - *.log, *.tmp, *.cache : Fichiers temporaires système
    - .ipynb_checkpoints/ : Checkpoints Jupyter
    - *.backup, *~ : Fichiers de sauvegarde temporaires
    
.PARAMETER DryRun
    Mode simulation - affiche les fichiers qui seraient supprimés sans les supprimer
    
.PARAMETER Execute
    Mode exécution - effectue le nettoyage après confirmation utilisateur
    
.PARAMETER Restore  
    Mode restauration - restaure les fichiers depuis le backup
    
.PARAMETER Backup
    Crée un backup avant suppression (activé par défaut avec -Execute)
    
.PARAMETER Verbose
    Affichage détaillé des opérations
    
.EXAMPLE
    .\clean-temporary-notebooks.ps1 -DryRun
    Simule le nettoyage et affiche les fichiers qui seraient supprimés
    
.EXAMPLE 
    .\clean-temporary-notebooks.ps1 -Execute -Backup
    Exécute le nettoyage avec backup préalable et demande confirmation
    
.EXAMPLE 
    .\clean-temporary-notebooks.ps1 -Restore
    Restaure les fichiers depuis le dernier backup
    
.NOTES
    Auteur: Roo Code Agent 
    Date: 2025-10-07
    Version: 2.0 - Version améliorée pour nettoyage final ExecutionManager
    
    IMPORTANT: Script intelligent avec backup automatique et classification des fichiers
#>

param(
    [switch]$DryRun = $false,
    [switch]$Execute = $false,
    [switch]$Restore = $false,
    [switch]$Backup = $true,
    [switch]$Force = $false,
    [switch]$Verbose = $false
)

# Configuration des couleurs et logging
$ErrorActionPreference = 'Continue'
if ($Verbose) { $VerbosePreference = 'Continue' }

# Configuration des chemins
$BackupDir = "./backup-temp-files-$(Get-Date -Format 'yyyyMMdd-HHmmss')"
$LogFile = "./clean-notebooks-$(Get-Date -Format 'yyyyMMdd-HHmmss').log"

function Write-Log {
    param([string]$Message, [string]$Color = "White")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] $Message"
    Write-Host $logMessage -ForegroundColor $Color
    Add-Content -Path $LogFile -Value $logMessage
}

function Show-Header {
    Write-Log "=== SCRIPT INTELLIGENT DE NETTOYAGE NOTEBOOKS TEMPORAIRES ===" "Yellow"
    Write-Log "Répertoire de travail: $(Get-Location)" "Cyan"
    Write-Log "Fichier de log: $LogFile" "Cyan"
    
    if ($DryRun) {
        Write-Log "MODE SIMULATION - Aucun fichier ne sera supprimé" "Magenta"
    } elseif ($Execute) {
        Write-Log "MODE EXECUTION - Nettoyage avec confirmation utilisateur" "Green"
        if ($Backup) {
            Write-Log "BACKUP ACTIVÉ - Sauvegarde dans: $BackupDir" "Cyan"
        }
    } elseif ($Restore) {
        Write-Log "MODE RESTAURATION - Restauration depuis backup" "Yellow"
    }
    Write-Log ""
}

# Patterns de fichiers temporaires à nettoyer (avec chemins spécifiques)
$patterns = @{
    "Notebooks test/fixed MyIA.AI.Notebooks" = @{
        "Path" = "MyIA.AI.Notebooks"
        "Patterns" = @("*_test*.ipynb", "*_fixed*.ipynb")
        "Description" = "Notebooks de test et corrections temporaires"
    }
    "Notebooks debug mcp-maintenance" = @{
        "Path" = "notebook-infrastructure/mcp-maintenance/debug-notebooks"
        "Patterns" = @("debug-*.ipynb", "diagnostic-*.ipynb")
        "Description" = "Notebooks de debug et diagnostic MCP"
    }
    "Notebooks executed généraux" = @{
        "Path" = "."
        "Patterns" = @("*_executed*.ipynb")
        "Description" = "Notebooks exécutés par Papermill/MCP"
    }
    "Notebooks validation MCP" = @{
        "Path" = "."
        "Patterns" = @("*-validation-MCP.ipynb")
        "Description" = "Notebooks de validation MCP temporaires"
    }
    "Fichiers système temporaires" = @{
        "Path" = "."
        "Patterns" = @("*.log", "*.tmp", "*.cache", "*.backup", "*~")
        "Description" = "Fichiers temporaires système"
    }
}

# Liste d'exclusion - fichiers à TOUJOURS préserver
$exclusions = @(
    "**/MyIA.AI.Notebooks/GenAI/**/*.ipynb",
    "**/MyIA.AI.Notebooks/ML/ML-1-Introduction.ipynb",
    "**/MyIA.AI.Notebooks/SymbolicAI/**/*.ipynb",
    "**/README*.md",
    "**/docs/**/*",
    "**/*.cs",
    "**/*.py",
    "**/libs/**/*"
)

function Test-ShouldPreserve {
    param([string]$FilePath)
    
    foreach ($exclusion in $exclusions) {
        if ($FilePath -like $exclusion) {
            return $true
        }
    }
    return $false
}

function Get-TemporaryFiles {
    $allFiles = @()
    
    foreach ($category in $patterns.Keys) {
        $config = $patterns[$category]
        $searchPath = $config.Path
        
        Write-Log "Recherche: $category dans '$searchPath'" "Green"
        
        if (-not (Test-Path $searchPath)) {
            Write-Log "   Chemin inexistant: $searchPath" "Yellow"
            continue
        }
        
        foreach ($pattern in $config.Patterns) {
            $files = Get-ChildItem -Path $searchPath -Recurse -Filter $pattern -File -ErrorAction SilentlyContinue
            
            foreach ($file in $files) {
                $relativePath = Resolve-Path -Relative $file.FullName
                
                # Vérification exclusions
                if (Test-ShouldPreserve $relativePath) {
                    Write-Log "   PRESERVE (exclusion): $relativePath" "Cyan"
                    continue
                }
                
                $fileInfo = [PSCustomObject]@{
                    FullPath = $file.FullName
                    RelativePath = $relativePath
                    Size = $file.Length
                    Category = $category
                    Pattern = $pattern
                }
                
                $allFiles += $fileInfo
                Write-Log "   TROUVE: $relativePath ($([Math]::Round($file.Length / 1KB, 2)) KB)" "Gray"
            }
        }
    }
    
    # Recherche des répertoires .ipynb_checkpoints
    $checkpoints = Get-ChildItem -Path . -Recurse -Directory -Name ".ipynb_checkpoints" -ErrorAction SilentlyContinue
    foreach ($checkpoint in $checkpoints) {
        $fileInfo = [PSCustomObject]@{
            FullPath = $checkpoint
            RelativePath = $checkpoint
            Size = 0
            Category = "Checkpoints Jupyter"
            Pattern = ".ipynb_checkpoints/"
        }
        $allFiles += $fileInfo
        Write-Log "   TROUVE CHECKPOINT: $checkpoint" "Gray"
    }
    
    return $allFiles
}

function Backup-Files {
    param([array]$Files)
    
    if ($Files.Count -eq 0) {
        Write-Log "Aucun fichier à sauvegarder" "Yellow"
        return $true
    }
    
    try {
        New-Item -ItemType Directory -Path $BackupDir -Force | Out-Null
        Write-Log "Répertoire de backup créé: $BackupDir" "Green"
        
        foreach ($file in $Files) {
            $sourceFile = $file.FullPath
            $backupFile = Join-Path $BackupDir $file.RelativePath
            $backupDir = Split-Path $backupFile -Parent
            
            if (-not (Test-Path $backupDir)) {
                New-Item -ItemType Directory -Path $backupDir -Force | Out-Null
            }
            
            if (Test-Path $sourceFile -PathType Container) {
                # C'est un répertoire (checkpoint)
                Copy-Item -Path $sourceFile -Destination $backupFile -Recurse -Force
            } else {
                # C'est un fichier
                Copy-Item -Path $sourceFile -Destination $backupFile -Force
            }
            
            Write-Log "   SAUVEGARDE: $($file.RelativePath)" "Cyan"
        }
        
        Write-Log "Backup terminé avec succès!" "Green"
        return $true
    }
    catch {
        Write-Log "ERREUR lors du backup: $($_.Exception.Message)" "Red"
        return $false
    }
}

function Remove-TemporaryFiles {
    param([array]$Files)
    
    $removedCount = 0
    $totalSize = 0
    
    foreach ($file in $Files) {
        try {
            if (Test-Path $file.FullPath -PathType Container) {
                # C'est un répertoire (checkpoint)
                Remove-Item -Path $file.FullPath -Recurse -Force
                Write-Log "   SUPPRIME REPERTOIRE: $($file.RelativePath)" "Red"
            } else {
                # C'est un fichier
                Remove-Item -Path $file.FullPath -Force
                Write-Log "   SUPPRIME FICHIER: $($file.RelativePath) ($([Math]::Round($file.Size / 1KB, 2)) KB)" "Red"
                $totalSize += $file.Size
            }
            $removedCount++
        }
        catch {
            Write-Log "   ERREUR: $($file.RelativePath) - $($_.Exception.Message)" "Red"
        }
    }
    
    return @{
        Count = $removedCount
        Size = $totalSize
    }
}

function Restore-FromBackup {
    $backupDirs = Get-ChildItem -Path . -Directory -Filter "backup-temp-files-*" | Sort-Object Name -Descending
    
    if ($backupDirs.Count -eq 0) {
        Write-Log "Aucun backup trouvé pour restauration" "Yellow"
        return
    }
    
    $latestBackup = $backupDirs[0].Name
    Write-Log "Backup le plus récent trouvé: $latestBackup" "Green"
    
    $confirmation = Read-Host "Confirmer la restauration depuis '$latestBackup' ? (O/N)"
    if ($confirmation -notmatch '^[OoYy]') {
        Write-Log "Restauration annulée par l'utilisateur" "Yellow"
        return
    }
    
    try {
        Copy-Item -Path "./$latestBackup/*" -Destination "." -Recurse -Force
        Write-Log "Restauration terminée avec succès!" "Green"
    }
    catch {
        Write-Log "ERREUR lors de la restauration: $($_.Exception.Message)" "Red"
    }
}

function Show-Summary {
    param([array]$Files, [hashtable]$Results = $null)
    
    Write-Log "=== RESUME NETTOYAGE ===" "Yellow"
    
    if ($DryRun -or $Results -eq $null) {
        Write-Log "Total fichiers à supprimer: $($Files.Count)" "Cyan"
        $totalSizeMB = [Math]::Round(($Files | Measure-Object -Property Size -Sum).Sum / 1MB, 2)
        Write-Log "Taille totale à libérer: $totalSizeMB MB" "Cyan"
        
        if ($DryRun) {
            Write-Log "Exécutez avec -Execute pour effectuer le nettoyage" "Green"
        }
    } else {
        Write-Log "Fichiers supprimés: $($Results.Count)" "Green"
        $totalSizeMB = [Math]::Round($Results.Size / 1MB, 2)
        Write-Log "Espace libéré: $totalSizeMB MB" "Green"
        Write-Log "Nettoyage terminé avec succès!" "Green"
    }
    
    Write-Log ""
    Write-Log "Conseil: Vérifiez avec 'git status' que seuls les fichiers légitimes restent" "Cyan"
}

# === MAIN EXECUTION ===

Show-Header

if ($Restore) {
    Restore-FromBackup
    exit 0
}

# Recherche des fichiers temporaires
Write-Log "Phase 1: Recherche et analyse des fichiers temporaires..." "Yellow"
$filesToClean = Get-TemporaryFiles

if ($filesToClean.Count -eq 0) {
    Write-Log "Aucun fichier temporaire trouvé - Le workspace est déjà propre!" "Green"
    exit 0
}

Write-Log ""
Write-Log "Fichiers temporaires identifiés par catégorie:" "Yellow"
$groupedFiles = $filesToClean | Group-Object -Property Category
foreach ($group in $groupedFiles) {
    Write-Log "  $($group.Name): $($group.Count) fichier(s)" "Cyan"
}
Write-Log ""

if ($DryRun) {
    Show-Summary $filesToClean
    exit 0
}

if ($Execute) {
    Write-Log "Phase 2: Préparation du nettoyage..." "Yellow"
    Write-Log "ATTENTION: $($filesToClean.Count) fichiers vont être supprimés!" "Red"
    
    # Affichage détaillé des fichiers à supprimer
    Write-Log "Liste détaillée des fichiers à supprimer:" "Yellow"
    foreach ($file in $filesToClean) {
        Write-Log "  - $($file.RelativePath) [$($file.Category)]" "Gray"
    }
    Write-Log ""
    
    if (-not $Force) {
        Write-Log "Utilisez -Force pour procéder sans confirmation" "Yellow"
        exit 0
    }
    
    Write-Log "Mode FORCE activé - Procédure automatique" "Green"
    
    # Backup si demandé
    if ($Backup) {
        Write-Log "Phase 3: Sauvegarde préventive..." "Yellow"
        if (-not (Backup-Files $filesToClean)) {
            Write-Log "ERREUR: Impossible de créer le backup - Arrêt du nettoyage" "Red"
            exit 1
        }
        Write-Log ""
    }
    
    # Suppression effective
    Write-Log "Phase 4: Suppression des fichiers temporaires..." "Yellow"
    $results = Remove-TemporaryFiles $filesToClean
    Write-Log ""
    
    Show-Summary $filesToClean $results
    
    if ($Backup) {
        Write-Log "Backup disponible dans: $BackupDir" "Cyan"
        Write-Log "Pour restaurer: ./clean-temporary-notebooks.ps1 -Restore" "Cyan"
    }
} else {
    Write-Log "Utilisez -DryRun pour simulation ou -Execute pour nettoyage effectif" "Yellow"
    Show-Summary $filesToClean
}

Write-Log ""
Write-Log "Log détaillé sauvegardé dans: $LogFile" "Cyan"