# ======================================================
# Script d'installation ultra-simplifié pour la démo Roo
# ======================================================
#
# Description: Ce script automatise l'installation et la configuration
# de la démo d'initiation à Roo.
#
# Auteur: Roo Assistant
# Date: 21/05/2025
# Version: 1.2
# ======================================================

param (
    [switch]$SkipPrerequisites = $false,
    [switch]$SkipExtensionInstall = $false,
    [switch]$SkipWorkspacePreparation = $false
)

# Affichage du titre
Write-Host "=========================================" -ForegroundColor Cyan
Write-Host "  INSTALLATION DE LA DÉMO ROO" -ForegroundColor Cyan
Write-Host "=========================================" -ForegroundColor Cyan
Write-Host ""

# Déterminer le chemin du script
$scriptPath = $PSScriptRoot
if (-not $scriptPath) {
    $scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Path
}

# Définir le chemin vers le répertoire demo-roo-code (maintenant c'est le répertoire courant)
$demoRootPath = $scriptPath

Write-Host "Chemin de la démo: $demoRootPath" -ForegroundColor Yellow
Write-Host ""

# Vérification des prérequis
if (-not $SkipPrerequisites) {
    Write-Host "Vérification des prérequis..." -ForegroundColor Yellow
    
    # Vérifier VS Code
    $vsCodePath = Get-Command "code" -ErrorAction SilentlyContinue
    
    if ($vsCodePath) {
        Write-Host "✓ Visual Studio Code est installé" -ForegroundColor Green
    } else {
        Write-Host "✗ Visual Studio Code n'est pas installé ou n'est pas dans le PATH" -ForegroundColor Red
        Write-Host "  Veuillez installer VS Code depuis https://code.visualstudio.com/" -ForegroundColor Red
        Write-Host "  Ou utilisez -SkipPrerequisites pour ignorer cette vérification" -ForegroundColor Red
    }
    
    # Vérifier Python
    $pythonPath = Get-Command "python" -ErrorAction SilentlyContinue
    $python3Path = Get-Command "python3" -ErrorAction SilentlyContinue
    
    if ($pythonPath -or $python3Path) {
        Write-Host "✓ Python est installé" -ForegroundColor Green
    } else {
        Write-Host "✗ Python n'est pas installé ou n'est pas dans le PATH" -ForegroundColor Red
        Write-Host "  Veuillez installer Python depuis https://www.python.org/downloads/" -ForegroundColor Red
        Write-Host "  Ou utilisez -SkipPrerequisites pour ignorer cette vérification" -ForegroundColor Red
    }
    
    # Vérifier Node.js
    $nodePath = Get-Command "node" -ErrorAction SilentlyContinue
    
    if ($nodePath) {
        Write-Host "✓ Node.js est installé" -ForegroundColor Green
    } else {
        Write-Host "✗ Node.js n'est pas installé ou n'est pas dans le PATH" -ForegroundColor Red
        Write-Host "  Veuillez installer Node.js depuis https://nodejs.org/" -ForegroundColor Red
        Write-Host "  Ou utilisez -SkipPrerequisites pour ignorer cette vérification" -ForegroundColor Red
    }
    
    Write-Host ""
}

# Installation de l'extension Roo
if (-not $SkipExtensionInstall) {
    Write-Host "Vérification de l'extension Roo..." -ForegroundColor Yellow
    
    $rooExtensionId = "roo.roo"  # ID de l'extension Roo
    
    $extensions = Invoke-Expression "code --list-extensions" -ErrorAction SilentlyContinue
    $rooExtensionInstalled = $extensions -contains $rooExtensionId
    
    if ($rooExtensionInstalled) {
        Write-Host "✓ L'extension Roo est déjà installée" -ForegroundColor Green
    } else {
        Write-Host "L'extension Roo n'est pas installée. Installation en cours..." -ForegroundColor Yellow
        
        $result = Invoke-Expression "code --install-extension $rooExtensionId --force" -ErrorAction SilentlyContinue
        
        if ($?) {
            Write-Host "✓ L'extension Roo a été installée avec succès" -ForegroundColor Green
        } else {
            Write-Host "✗ Échec de l'installation de l'extension Roo" -ForegroundColor Red
            Write-Host "  Veuillez l'installer manuellement depuis VS Code Marketplace" -ForegroundColor Red
        }
    }
    
    Write-Host ""
}

# Préparation des espaces de travail
if (-not $SkipWorkspacePreparation) {
    Write-Host "Préparation des espaces de travail..." -ForegroundColor Yellow
    
    $prepareScriptPath = Join-Path -Path $demoRootPath -ChildPath "prepare-workspaces.ps1"
    
    if (-not (Test-Path $prepareScriptPath)) {
        Write-Host "✗ Le script de préparation n'existe pas: $prepareScriptPath" -ForegroundColor Red
    } else {
        & $prepareScriptPath -ErrorAction SilentlyContinue
        
        if ($?) {
            Write-Host "✓ Les espaces de travail ont été préparés avec succès" -ForegroundColor Green
        } else {
            Write-Host "✗ Erreur lors de la préparation des espaces de travail" -ForegroundColor Red
        }
    }
    
    Write-Host ""
}

# Affichage du résumé
Write-Host "=========================================" -ForegroundColor Cyan
Write-Host "  INSTALLATION TERMINÉE" -ForegroundColor Cyan
Write-Host "=========================================" -ForegroundColor Cyan
Write-Host "La démo Roo a été installée et configurée avec succès!" -ForegroundColor Green
Write-Host "Pour commencer à utiliser la démo:" -ForegroundColor Yellow
Write-Host "1. Ouvrez VS Code dans le répertoire d'une démo spécifique" -ForegroundColor Yellow
Write-Host "2. Suivez les instructions du fichier README.md dans le workspace" -ForegroundColor Yellow
Write-Host "3. Utilisez le panneau Roo en cliquant sur l'icône Roo dans la barre latérale" -ForegroundColor Yellow
Write-Host ""
Write-Host "Pour plus d'informations, consultez la documentation dans le dossier docs/" -ForegroundColor Yellow
Write-Host ""

$versionPath = Join-Path -Path $demoRootPath -ChildPath "VERSION.md"
if (Test-Path $versionPath) {
    $version = Get-Content -Path $versionPath -TotalCount 1 -ErrorAction SilentlyContinue
    Write-Host "Version actuelle de la démo: $version" -ForegroundColor Cyan
}

Write-Host "=========================================" -ForegroundColor Cyan