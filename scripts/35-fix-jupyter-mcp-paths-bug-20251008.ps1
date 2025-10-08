# =============================================================================
# SCRIPT DE CORRECTION - BUG MCP JUPYTER PATHS
# =============================================================================
# Date: 2025-10-08
# Objectif: Corriger les chemins incorrects créés par le MCP Jupyter
# Problème: Notebooks créés dans SemanticKernel/MyIA.AI.Notebooks/GenAI/ 
#           au lieu de MyIA.AI.Notebooks/GenAI/
# =============================================================================

param(
    [string]$RootPath = "MyIA.AI.Notebooks/GenAI"
)

Write-Host "CORRECTION BUG MCP JUPYTER - CHEMINS INCORRECTS" -ForegroundColor Green
Write-Host "Date: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')" -ForegroundColor Gray
Write-Host "============================================================"

# Définir les chemins problématiques
$ProblematicBasePath = "$RootPath/SemanticKernel/MyIA.AI.Notebooks/GenAI"
$CorrectBasePath = $RootPath

# Modules à corriger
$ModulesToFix = @(
    "00-GenAI-Environment",
    "01-Images-Foundation", 
    "02-Images-Advanced",
    "03-Images-Orchestration",
    "04-Images-Applications"
)

# Statistiques
$TotalMoved = 0
$TotalErrors = 0

foreach ($module in $ModulesToFix) {
    $SourcePath = "$ProblematicBasePath/$module"
    $DestPath = "$CorrectBasePath/$module"
    
    Write-Host ""
    Write-Host "Traitement module: $module" -ForegroundColor Cyan
    
    if (Test-Path $SourcePath) {
        Write-Host "  Source trouvee: $SourcePath" -ForegroundColor Green
        
        # Créer le répertoire de destination si nécessaire
        if (-not (Test-Path $DestPath)) {
            New-Item -Path $DestPath -ItemType Directory -Force | Out-Null
            Write-Host "  Repertoire destination cree: $DestPath" -ForegroundColor Yellow
        }
        
        # Déplacer tous les fichiers .ipynb
        $NotebookFiles = Get-ChildItem -Path $SourcePath -Filter "*.ipynb" -ErrorAction SilentlyContinue
        
        foreach ($file in $NotebookFiles) {
            $DestFile = Join-Path $DestPath $file.Name
            
            try {
                if (-not (Test-Path $DestFile)) {
                    Move-Item -Path $file.FullName -Destination $DestFile -Force
                    Write-Host "    Deplace: $($file.Name)" -ForegroundColor Green
                    $TotalMoved++
                } else {
                    Write-Host "    Deja existant: $($file.Name)" -ForegroundColor Yellow
                    # Sauvegarder avec suffixe
                    $BackupName = $file.BaseName + "_backup_$(Get-Date -Format 'yyyyMMdd_HHmmss')" + $file.Extension
                    $BackupPath = Join-Path $DestPath $BackupName
                    Move-Item -Path $file.FullName -Destination $BackupPath -Force
                    Write-Host "    Sauvegarde comme: $BackupName" -ForegroundColor Magenta
                    $TotalMoved++
                }
            }
            catch {
                Write-Host "    Erreur deplacement $($file.Name): $($_.Exception.Message)" -ForegroundColor Red
                $TotalErrors++
            }
        }
        
        # Nettoyer le répertoire source s'il est vide
        try {
            $RemainingFiles = Get-ChildItem $SourcePath -Recurse -ErrorAction SilentlyContinue
            if ($RemainingFiles.Count -eq 0) {
                Remove-Item -Path $SourcePath -Recurse -Force
                Write-Host "  Repertoire source vide supprime" -ForegroundColor Gray
            } else {
                Write-Host "  Repertoire source non vide ($($RemainingFiles.Count) elements restants)" -ForegroundColor Yellow
            }
        }
        catch {
            Write-Host "  Erreur nettoyage: $($_.Exception.Message)" -ForegroundColor Red
        }
        
    } else {
        Write-Host "  Pas de source problematique pour $module" -ForegroundColor Gray
    }
}

# Nettoyage des répertoires parents vides
Write-Host ""
Write-Host "NETTOYAGE REPERTOIRES PARENTS VIDES" -ForegroundColor Cyan

$ParentPaths = @(
    "$ProblematicBasePath",
    "$RootPath/SemanticKernel/MyIA.AI.Notebooks"
)

foreach ($parentPath in $ParentPaths) {
    if (Test-Path $parentPath) {
        try {
            $ChildItems = Get-ChildItem $parentPath -Recurse -ErrorAction SilentlyContinue
            if ($ChildItems.Count -eq 0) {
                Remove-Item -Path $parentPath -Recurse -Force
                Write-Host "  Repertoire parent vide supprime: $parentPath" -ForegroundColor Gray
            } else {
                Write-Host "  Repertoire parent non vide: $parentPath ($($ChildItems.Count) elements)" -ForegroundColor Yellow
            }
        }
        catch {
            Write-Host "  Erreur nettoyage parent $parentPath : $($_.Exception.Message)" -ForegroundColor Red
        }
    }
}

# Vérification finale
Write-Host ""
Write-Host "VERIFICATION FINALE" -ForegroundColor Cyan

foreach ($module in $ModulesToFix) {
    $ModulePath = "$CorrectBasePath/$module"
    if (Test-Path $ModulePath) {
        $NotebooksCount = (Get-ChildItem -Path $ModulePath -Filter "*.ipynb" | Measure-Object).Count
        Write-Host "  $module : $NotebooksCount notebooks" -ForegroundColor Green
    } else {
        Write-Host "  $module : Repertoire manquant" -ForegroundColor Red
    }
}

# Rapport final
Write-Host ""
Write-Host "============================================================"
Write-Host "RAPPORT FINAL - CORRECTION MCP JUPYTER BUG" -ForegroundColor Green
Write-Host "============================================================"
Write-Host "Fichiers deplaces: $TotalMoved" -ForegroundColor $(if($TotalMoved -gt 0) { "Green" } else { "Gray" })
Write-Host "Erreurs rencontrees: $TotalErrors" -ForegroundColor $(if($TotalErrors -gt 0) { "Red" } else { "Green" })
Write-Host "Correction terminee: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')" -ForegroundColor Gray

if ($TotalErrors -eq 0) {
    Write-Host ""
    Write-Host "SUCCES: Bug MCP Jupyter corrige avec succes !" -ForegroundColor Green
} else {
    Write-Host ""
    Write-Host "ATTENTION: Correction partielle - $TotalErrors erreurs a verifier" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "PROCHAINES ETAPES:" -ForegroundColor Cyan
Write-Host "  1. Verifier le bon fonctionnement des notebooks deplaces"
Write-Host "  2. Signaler le bug au developpeur du MCP Jupyter"
Write-Host "  3. Continuer la generation des templates manquants"

Write-Host ""
Write-Host "INFO: Le MCP Jupyter utilise un chemin de travail incorrect" -ForegroundColor Yellow
Write-Host "qui duplique la structure de repertoires au lieu d'utiliser le chemin absolu correct."

return @{
    FilesMovedCount = $TotalMoved
    ErrorsCount = $TotalErrors
    Success = ($TotalErrors -eq 0)
    Timestamp = $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
}