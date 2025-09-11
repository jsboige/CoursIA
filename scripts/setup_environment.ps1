#!/usr/bin/env powershell
# =============================================================================
# SETUP ENVIRONNEMENT NOTEBOOKS - CoursIA
# =============================================================================
# Description: Script de configuration et réparation automatique de l'environnement
# Usage: .\scripts\setup_environment.ps1 [-AutoFix] [-InstallOptional]
# =============================================================================

param(
    [switch]$AutoFix = $false,
    [switch]$InstallOptional = $false,
    [switch]$Force = $false,
    [switch]$Resume = $false
)

# Configuration
$LogFile = "setup_$(Get-Date -Format 'yyyyMMdd_HHmmss').log"
$CheckpointFile = "setup_checkpoint.json"
$RequiredPackages = @("numpy", "pandas", "matplotlib", "scikit-learn", "scipy", "z3-solver", "ortools", "jupyter", "ipykernel")
$OptionalPackages = @("seaborn", "torch", "stable-baselines3", "pyro-ppl", "pygad", "deap", "networkx", "plotly", "tensorflow")

# Système de checkpoints
$Checkpoints = @{
    "preliminaries" = $false;
    "python_packages_basic" = $false;
    "python_packages_ml" = $false;
    "python_packages_advanced" = $false;
    "python_packages_optional" = $false;
    "dotnet_nuget_config" = $false;
    "dotnet_interactive_install" = $false;
    "jupyter_directory_setup" = $false;
    "python_kernel_install" = $false;
    "dotnet_kernel_install" = $false;
    "environment_test" = $false;
    "cleanup" = $false
}

# Fonctions utilitaires
function Write-Section { 
    param($Title) 
    Write-Host "`n=== $Title ===" -ForegroundColor Green 
}

function Write-Action { 
    param($Action, $Status = "INFO") 
    $Color = switch($Status) { "SUCCESS" {"Green"} "WARNING" {"Yellow"} "ERROR" {"Red"} default {"Cyan"} }
    Write-Host "[$Status] $Action" -ForegroundColor $Color
}

function Test-Administrator {
    $currentUser = [Security.Principal.WindowsIdentity]::GetCurrent()
    $principal = New-Object Security.Principal.WindowsPrincipal($currentUser)
    return $principal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

function Save-Checkpoint {
    param($CheckpointName)
    $Checkpoints[$CheckpointName] = $true
    $Checkpoints | ConvertTo-Json | Out-File -FilePath $CheckpointFile -Encoding UTF8
    Write-Action "Checkpoint: $CheckpointName" "SUCCESS"
}

function Load-Checkpoints {
    if (Test-Path $CheckpointFile) {
        try {
            $saved = Get-Content $CheckpointFile -Raw | ConvertFrom-Json
            foreach ($key in $saved.PSObject.Properties.Name) {
                $Checkpoints[$key] = $saved.$key
            }
            Write-Action "Checkpoints chargés depuis $CheckpointFile" "INFO"
            return $true
        } catch {
            Write-Action "Erreur lors du chargement des checkpoints" "WARNING"
            return $false
        }
    }
    return $false
}

function Skip-If-Done {
    param($CheckpointName, $Description)
    if ($Checkpoints[$CheckpointName] -and -not $Force) {
        Write-Action "Étape déjà terminée: $Description" "INFO"
        return $true
    }
    return $false
}

function Setup-DotNetNuGet {
    if (Skip-If-Done "dotnet_nuget_config" "Configuration NuGet") { return $true }
    
    try {
        Write-Action "Configuration des sources NuGet..." "INFO"
        $nugetSources = dotnet nuget list source 2>$null
        if (-not ($nugetSources -match "nuget.org")) {
            dotnet nuget add source https://api.nuget.org/v3/index.json -n nuget.org 2>&1 | Out-Null
            if ($LASTEXITCODE -eq 0) {
                Write-Action "Source NuGet ajoutée avec succès" "SUCCESS"
                Save-Checkpoint "dotnet_nuget_config"
                return $true
            } else {
                Write-Action "Échec de la configuration NuGet" "ERROR"
                return $false
            }
        } else {
            Write-Action "Source NuGet déjà configurée" "SUCCESS"
            Save-Checkpoint "dotnet_nuget_config"
            return $true
        }
    } catch {
        Write-Action "Erreur lors de la configuration NuGet: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

function Setup-JupyterDirectory {
    if (Skip-If-Done "jupyter_directory_setup" "Répertoire Jupyter") { return $true }
    
    try {
        $jupyterKernelsPath = "$env:APPDATA\jupyter\kernels"
        Write-Action "Création du répertoire kernels Jupyter..." "INFO"
        
        if (-not (Test-Path $jupyterKernelsPath)) {
            New-Item -ItemType Directory -Force -Path $jupyterKernelsPath | Out-Null
            Write-Action "Répertoire créé: $jupyterKernelsPath" "SUCCESS"
        } else {
            Write-Action "Répertoire déjà existant: $jupyterKernelsPath" "SUCCESS"
        }
        
        Save-Checkpoint "jupyter_directory_setup"
        return $true
    } catch {
        Write-Action "Erreur lors de la création du répertoire Jupyter: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

function Install-PythonKernel {
    if (Skip-If-Done "python_kernel_install" "Kernel Python") { return $true }
    
    try {
        Write-Action "Installation du kernel Python..." "INFO"
        python -m ipykernel install --user 2>&1 | Out-Null
        if ($LASTEXITCODE -eq 0) {
            Write-Action "Kernel Python installé avec succès" "SUCCESS"
            Save-Checkpoint "python_kernel_install"
            return $true
        } else {
            Write-Action "Échec de l'installation du kernel Python" "ERROR"
            return $false
        }
    } catch {
        Write-Action "Erreur lors de l'installation du kernel Python: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

function Install-DotNetKernels {
    if (Skip-If-Done "dotnet_kernel_install" "Kernels .NET") { return $true }
    
    try {
        $interactiveAvailable = Get-Command "dotnet-interactive" -ErrorAction SilentlyContinue
        if (-not $interactiveAvailable) {
            Write-Action "dotnet-interactive non disponible, passage de l'installation des kernels" "WARNING"
            return $false
        }
        
        Write-Action "Installation des kernels .NET Interactive..." "INFO"
        dotnet interactive jupyter install 2>&1 | Out-Null
        if ($LASTEXITCODE -eq 0) {
            Write-Action "Kernels .NET installés avec succès" "SUCCESS"
            Save-Checkpoint "dotnet_kernel_install"
            return $true
        } else {
            Write-Action "Échec de l'installation des kernels .NET" "ERROR"
            return $false
        }
    } catch {
        Write-Action "Erreur lors de l'installation des kernels .NET: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

function Install-PipPackage {
    param($PackageName, $Optional = $false)
    
    try {
        Write-Action "Installation de $PackageName via python -m pip..." "INFO"
        $result = python -m pip install $PackageName 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Action "$PackageName installé avec succès" "SUCCESS"
            return $true
        } else {
            Write-Action "Échec de l'installation de $PackageName" $(if($Optional){"WARNING"}else{"ERROR"})
            return $false
        }
    } catch {
        Write-Action "Erreur lors de l'installation de $PackageName : $($_.Exception.Message)" $(if($Optional){"WARNING"}else{"ERROR"})
        return $false
    }
}

# =============================================================================
# INITIALISATION ET CHECKPOINTS
# =============================================================================
Write-Section "INITIALISATION"

# Chargement des checkpoints si demandé
if ($Resume) {
    $loaded = Load-Checkpoints
    if ($loaded) {
        Write-Action "Mode reprise activé" "INFO"
    } else {
        Write-Action "Aucun checkpoint trouvé, démarrage complet" "INFO"
    }
}

# =============================================================================
# VÉRIFICATIONS PRÉLIMINAIRES
# =============================================================================
Write-Section "VÉRIFICATIONS PRÉLIMINAIRES"

if (Skip-If-Done "preliminaries" "Vérifications préliminaires") {
    # Reload variables from previous run
    $condaAvailable = $true
    $pythonAvailable = $true
} else {
    # Test des permissions
    if (-not (Test-Administrator)) {
        Write-Action "Script non exécuté en tant qu'administrateur" "WARNING"
        Write-Action "Certaines opérations pourraient échouer" "WARNING"
    } else {
        Write-Action "Permissions administrateur détectées" "SUCCESS"
    }

    # Test de Python
    try {
        $pythonVersion = python --version 2>$null
        Write-Action "Python détecté : $pythonVersion" "SUCCESS"
        $pythonAvailable = $true
    } catch {
        Write-Action "Python non disponible" "ERROR"
        $pythonAvailable = $false
    }

    if (-not $pythonAvailable) {
        Write-Action "Python est requis. Installation impossible." "ERROR"
        exit 1
    }
    
    Save-Checkpoint "preliminaries"
}

# =============================================================================
# INSTALLATION PACKAGES REQUIS
# =============================================================================
Write-Section "INSTALLATION PACKAGES REQUIS"

$FailedRequired = @()
$SuccessCount = 0

# Installation progressive par lot
$BasicPackages = @("numpy", "pandas", "matplotlib", "scipy")
$MLPackages = @("scikit-learn", "jupyter", "ipykernel")
$AdvancedPackages = @("z3-solver", "ortools")

# Phase 1: Packages de base
if (-not (Skip-If-Done "python_packages_basic" "Packages Python de base")) {
    Write-Action "Phase 1/3: Packages de base - numpy, pandas, matplotlib, scipy" "INFO"
    $phaseSuccess = 0
    foreach ($package in $BasicPackages) {
        if ($package -in $RequiredPackages) {
            $installed = python -m pip show $package 2>$null
            if ($installed -and -not $Force) {
                Write-Action "$package déjà installé" "SUCCESS"
                $phaseSuccess++
            } else {
                $success = Install-PipPackage $package $false
                if ($success) { $phaseSuccess++ } else { $FailedRequired += $package }
            }
        }
    }
    if ($phaseSuccess -eq $BasicPackages.Count) {
        Save-Checkpoint "python_packages_basic"
    }
    $SuccessCount += $phaseSuccess
} else {
    $SuccessCount += $BasicPackages.Count
}

# Phase 2: Packages ML et Jupyter
if (-not (Skip-If-Done "python_packages_ml" "Packages ML et Jupyter")) {
    Write-Action "Phase 2/3: Packages ML et Jupyter - scikit-learn, jupyter, ipykernel" "INFO"
    $phaseSuccess = 0
    foreach ($package in $MLPackages) {
        if ($package -in $RequiredPackages) {
            $installed = python -m pip show $package 2>$null
            if ($installed -and -not $Force) {
                Write-Action "$package déjà installé" "SUCCESS"
                $phaseSuccess++
            } else {
                $success = Install-PipPackage $package $false
                if ($success) { $phaseSuccess++ } else { $FailedRequired += $package }
            }
        }
    }
    if ($phaseSuccess -eq $MLPackages.Count) {
        Save-Checkpoint "python_packages_ml"
    }
    $SuccessCount += $phaseSuccess
} else {
    $SuccessCount += $MLPackages.Count
}

# Phase 3: Packages avancés
if (-not (Skip-If-Done "python_packages_advanced" "Packages Python avancés")) {
    Write-Action "Phase 3/3: Packages avancés - z3-solver, ortools" "INFO"
    $phaseSuccess = 0
    foreach ($package in $AdvancedPackages) {
        if ($package -in $RequiredPackages) {
            $installed = python -m pip show $package 2>$null
            if ($installed -and -not $Force) {
                Write-Action "$package déjà installé" "SUCCESS"
                $phaseSuccess++
            } else {
                $success = Install-PipPackage $package $false
                if ($success) { $phaseSuccess++ } else { $FailedRequired += $package }
            }
        }
    }
    if ($phaseSuccess -eq $AdvancedPackages.Count) {
        Save-Checkpoint "python_packages_advanced"
    }
    $SuccessCount += $phaseSuccess
} else {
    $SuccessCount += $AdvancedPackages.Count
}

Write-Action "Packages requis installés : $SuccessCount/$($RequiredPackages.Count)" "INFO"

# =============================================================================
# INSTALLATION PACKAGES OPTIONNELS
# =============================================================================
if ($InstallOptional) {
    if (-not (Skip-If-Done "python_packages_optional" "Packages Python optionnels")) {
        Write-Section "INSTALLATION PACKAGES OPTIONNELS"
        
        $OptionalSuccess = 0
        foreach ($package in $OptionalPackages) {
            $installed = python -m pip show $package 2>$null
            if ($installed -and -not $Force) {
                Write-Action "$package déjà installé" "SUCCESS"
                $OptionalSuccess++
                continue
            }
            
            $success = Install-PipPackage $package $true
            if ($success) { $OptionalSuccess++ }
        }
        
        Save-Checkpoint "python_packages_optional"
        Write-Action "Packages optionnels installés : $OptionalSuccess/$($OptionalPackages.Count)" "INFO"
    }
}

# =============================================================================
# CONFIGURATION .NET ET NUGET
# =============================================================================
Write-Section "CONFIGURATION .NET ET NUGET"

# Configuration NuGet
if ($AutoFix) {
    Setup-DotNetNuGet
}

# =============================================================================
# CONFIGURATION .NET INTERACTIVE
# =============================================================================
Write-Section "CONFIGURATION .NET INTERACTIVE"

# Installation .NET Interactive avec checkpoint
if ($AutoFix) {
    if (-not (Skip-If-Done "dotnet_interactive_install" ".NET Interactive")) {
        try {
            $dotnetVersion = dotnet --version 2>$null
            Write-Action ".NET SDK détecté : $dotnetVersion" "SUCCESS"
            
            # Vérifier .NET Interactive
            $interactiveInstalled = dotnet tool list -g | Select-String "microsoft.dotnet-interactive"
            if ($interactiveInstalled) {
                Write-Action ".NET Interactive déjà installé" "SUCCESS"
                Save-Checkpoint "dotnet_interactive_install"
            } else {
                Write-Action "Installation de .NET Interactive..." "INFO"
                dotnet tool install -g Microsoft.dotnet-interactive 2>&1 | Out-Null
                if ($LASTEXITCODE -eq 0) {
                    Write-Action ".NET Interactive installé avec succès" "SUCCESS"
                    Save-Checkpoint "dotnet_interactive_install"
                } else {
                    Write-Action "Échec de l'installation .NET Interactive" "ERROR"
                }
            }
        } catch {
            Write-Action ".NET SDK non disponible" "WARNING"
            Write-Action "Téléchargez .NET SDK depuis https://dotnet.microsoft.com/download" "INFO"
        }
    }
}

# =============================================================================
# CONFIGURATION JUPYTER ET KERNELS
# =============================================================================
Write-Section "CONFIGURATION JUPYTER ET KERNELS"

try {
    # Vérifier Jupyter
    $jupyterVersion = jupyter --version 2>$null
    Write-Action "Jupyter détecté" "SUCCESS"
    
    if ($AutoFix) {
        # Configuration des répertoires Jupyter
        Setup-JupyterDirectory
        
        # Installation du kernel Python
        Install-PythonKernel
        
        # Installation des kernels .NET
        Install-DotNetKernels
        
        # Lister les kernels disponibles
        Write-Action "Kernels Jupyter disponibles :" "INFO"
        jupyter kernelspec list | ForEach-Object { Write-Host "    $_" -ForegroundColor Gray }
    }
    
} catch {
    Write-Action "Jupyter non disponible" "ERROR"
}

# =============================================================================
# TESTS DE L'ENVIRONNEMENT
# =============================================================================
Write-Section "TESTS DE L'ENVIRONNEMENT"

# Test d'import des packages critiques
$TestPackages = @("numpy", "pandas", "matplotlib", "sklearn", "scipy", "z3", "ortools")
$TestResults = @()

Write-Action "Tests d'import des packages installés..." "INFO"
foreach ($package in $TestPackages) {
    try {
        # Gestion des noms spéciaux
        $importName = $package
        if ($package -eq "sklearn") { $importName = "sklearn" }
        if ($package -eq "z3-solver") { $importName = "z3" }
        
        $testResult = python -c "import $importName; print('$package OK')" 2>$null
        if ($testResult -like "*OK*") {
            Write-Action "Test import $package" "SUCCESS"
            $TestResults += @{Package = $package; Status = "OK"}
        } else {
            Write-Action "Test import $package" "WARNING"
            $TestResults += @{Package = $package; Status = "FAILED"}
        }
    } catch {
        Write-Action "Test import $package" "WARNING"
        $TestResults += @{Package = $package; Status = "ERROR"}
    }
}

# =============================================================================
# RAPPORT FINAL
# =============================================================================
Write-Section "RAPPORT FINAL"

$TotalRequired = $RequiredPackages.Count
$InstalledRequired = $TotalRequired - $FailedRequired.Count
$SuccessRate = [Math]::Round(($InstalledRequired / $TotalRequired) * 100, 1)

Write-Host "`nRÉSULTATS DE L'INSTALLATION:" -ForegroundColor Yellow
Write-Host "- Packages requis : $InstalledRequired/$TotalRequired ($SuccessRate%)" -ForegroundColor $(if($SuccessRate -ge 90){"Green"}else{"Red"})

if ($InstallOptional) {
    Write-Host "- Packages optionnels : $OptionalSuccess/$($OptionalPackages.Count)" -ForegroundColor $(if($OptionalSuccess -ge 5){"Green"}else{"Yellow"})
}

$PassedTests = ($TestResults | Where-Object {$_.Status -eq "OK"}).Count
Write-Host "- Tests d'import : $PassedTests/$($TestPackages.Count)" -ForegroundColor $(if($PassedTests -eq $TestPackages.Count){"Green"}else{"Yellow"})

if ($FailedRequired.Count -gt 0) {
    Write-Host "`nPACKAGES REQUIS ÉCHOUÉS:" -ForegroundColor Red
    foreach ($pkg in $FailedRequired) {
        Write-Host "  - $pkg" -ForegroundColor Red
    }
    
    Write-Host "`nCOMMANDE DE RÉCUPÉRATION:" -ForegroundColor Yellow
    Write-Host "  python -m pip install " + ($FailedRequired -join " ") -ForegroundColor Gray
}

# Recommandations finales
Write-Host "`nRECOMMANDATIONS:" -ForegroundColor Cyan
if ($SuccessRate -lt 90) {
    Write-Host "  1. Réexécuter: .\scripts\setup_environment.ps1 -AutoFix -Force" -ForegroundColor Gray
}
Write-Host "  2. Tester l'environnement: .\scripts\audit_environment.ps1" -ForegroundColor Gray
Write-Host "  3. Pour les packages optionnels: .\scripts\setup_environment.ps1 -InstallOptional" -ForegroundColor Gray

# Log final
$LogContent = @"
SETUP ENVIRONNEMENT - $(Get-Date)
================================
Packages requis installés: $InstalledRequired/$TotalRequired ($SuccessRate%)
Packages échoués: $($FailedRequired -join ', ')
Tests d'import réussis: $PassedTests/$($TestPackages.Count)
"@

$LogContent | Out-File -FilePath $LogFile -Encoding UTF8
Write-Host "`nLog sauvegardé: $LogFile" -ForegroundColor Gray

# Code de sortie
if ($FailedRequired.Count -eq 0 -and $PassedTests -eq $TestPackages.Count) {
    Write-Host "`n✅ SETUP TERMINÉ AVEC SUCCÈS" -ForegroundColor Green
    exit 0
} elseif ($FailedRequired.Count -le 2) {
    Write-Host "`n⚠️  SETUP TERMINÉ AVEC AVERTISSEMENTS" -ForegroundColor Yellow
    exit 1
} else {
    Write-Host "`n❌ SETUP ÉCHOUÉ" -ForegroundColor Red
    exit 2
}