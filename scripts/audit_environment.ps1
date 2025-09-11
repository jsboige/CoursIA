#!/usr/bin/env powershell
# =============================================================================
# AUDIT TECHNIQUE ENVIRONNEMENT NOTEBOOKS - CoursIA
# =============================================================================
# Description: Script d'audit complet de l'environnement avant formation
# Usage: .\scripts\audit_environment.ps1
# =============================================================================

param(
    [switch]$Detailed = $false,
    [switch]$ExportJson = $false
)

# Configuration
$LogFile = "audit_$(Get-Date -Format 'yyyyMMdd_HHmmss').log"
$ResultsFile = "audit_results.json"

# Couleurs et formatage
function Write-Section { param($Title) Write-Host "`n=== $Title ===" -ForegroundColor Green }
function Write-Check { param($Item, $Status, $Details = "") 
    $Color = if ($Status -eq "OK") { "Green" } elseif ($Status -eq "WARNING") { "Yellow" } else { "Red" }
    Write-Host "[$Status] $Item" -ForegroundColor $Color
    if ($Details) { Write-Host "    $Details" -ForegroundColor Gray }
}

# Structure des résultats
$Results = @{
    Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    Environment = @{}
    Python = @{}
    Conda = @{}
    Jupyter = @{}
    DotNet = @{}
    Packages = @{}
    System = @{}
    Issues = @()
    Recommendations = @()
}

# =============================================================================
# 1. AUDIT ENVIRONNEMENTS PYTHON/CONDA
# =============================================================================
Write-Section "ENVIRONNEMENTS PYTHON/CONDA"

# Vérification Conda
try {
    $condaVersion = conda --version 2>$null
    $condaEnvs = conda env list 2>$null
    $activeEnv = $condaEnvs | Select-String '\*' | ForEach-Object { $_.Line }
    
    $Results.Conda = @{
        Installed = $true
        Version = $condaVersion
        Environments = ($condaEnvs | Measure-Object).Count - 1  # -1 pour l'en-tête
        ActiveEnvironment = $activeEnv
    }
    
    Write-Check "Conda installé" "OK" $condaVersion
    Write-Check "Environnements conda" "OK" "$($Results.Conda.Environments) environnements trouvés"
    if ($activeEnv) {
        Write-Check "Environnement actif" "OK" $activeEnv.Split('*')[0].Trim()
    }
    
} catch {
    $Results.Conda = @{ Installed = $false; Error = $_.Exception.Message }
    $Results.Issues += "Conda non disponible dans le PATH"
    Write-Check "Conda" "ERROR" "Non trouvé dans le PATH"
}

# Vérification Python
try {
    $pythonVersion = python --version 2>$null
    $pythonPath = (Get-Command python -ErrorAction SilentlyContinue).Source
    
    $Results.Python = @{
        Installed = $true
        Version = $pythonVersion
        Path = $pythonPath
    }
    
    Write-Check "Python" "OK" "$pythonVersion - $pythonPath"
    
} catch {
    $Results.Python = @{ Installed = $false; Error = $_.Exception.Message }
    $Results.Issues += "Python non disponible"
    Write-Check "Python" "ERROR" "Non trouvé"
}

# =============================================================================
# 2. AUDIT KERNELS JUPYTER
# =============================================================================
Write-Section "KERNELS JUPYTER"

try {
    $jupyterVersion = jupyter --version 2>$null
    $kernels = jupyter kernelspec list 2>$null
    
    $Results.Jupyter = @{
        Installed = $true
        Version = $jupyterVersion
        Kernels = $kernels
    }
    
    Write-Check "Jupyter installé" "OK" "Version détectée"
    
    # Test de lancement Jupyter
    $jupyterTest = Start-Job -ScriptBlock { 
        timeout /t 5 /nobreak > $null
        jupyter lab --version 2>$null 
    }
    Wait-Job $jupyterTest -Timeout 10 | Out-Null
    $labVersion = Receive-Job $jupyterTest
    Remove-Job $jupyterTest -Force
    
    if ($labVersion) {
        Write-Check "Jupyter Lab" "OK" $labVersion
    } else {
        Write-Check "Jupyter Lab" "WARNING" "Version non détectée"
    }
    
} catch {
    $Results.Jupyter = @{ Installed = $false; Error = $_.Exception.Message }
    $Results.Issues += "Jupyter non disponible"
    Write-Check "Jupyter" "ERROR" "Non installé"
}

# =============================================================================
# 3. AUDIT .NET INTERACTIVE
# =============================================================================
Write-Section ".NET INTERACTIVE"

# Vérification SDK .NET
try {
    $dotnetVersions = dotnet --list-sdks 2>$null
    $dotnetInfo = dotnet --info 2>$null | Select-String "Version:"
    
    $Results.DotNet = @{
        Installed = $true
        SDKs = $dotnetVersions
        RuntimeInfo = $dotnetInfo.Line
    }
    
    Write-Check ".NET SDK" "OK" "$($dotnetVersions.Count) SDK(s) installé(s)"
    
    # Test dotnet interactive
    try {
        $interactiveCheck = dotnet tool list -g | Select-String "microsoft.dotnet-interactive"
        if ($interactiveCheck) {
            Write-Check ".NET Interactive" "OK" "Installé globalement"
            $Results.DotNet.Interactive = $true
        } else {
            Write-Check ".NET Interactive" "WARNING" "Non installé globalement"
            $Results.DotNet.Interactive = $false
            $Results.Recommendations += "Installer .NET Interactive: dotnet tool install -g Microsoft.dotnet-interactive"
        }
    } catch {
        Write-Check ".NET Interactive" "WARNING" "Statut indéterminé"
    }
    
} catch {
    $Results.DotNet = @{ Installed = $false; Error = $_.Exception.Message }
    $Results.Issues += ".NET SDK non disponible"
    Write-Check ".NET SDK" "ERROR" "Non installé"
}

# =============================================================================
# 4. AUDIT PACKAGES PYTHON CRITIQUES
# =============================================================================
Write-Section "PACKAGES PYTHON CRITIQUES"

$CriticalPackages = @(
    @{Name="numpy"; Category="ML Base"; Required=$true},
    @{Name="pandas"; Category="ML Base"; Required=$true},
    @{Name="matplotlib"; Category="ML Base"; Required=$true},
    @{Name="seaborn"; Category="ML Base"; Required=$false},
    @{Name="scikit-learn"; Category="ML Avancé"; Required=$true},
    @{Name="torch"; Category="ML Avancé"; Required=$false},
    @{Name="tensorflow"; Category="ML Avancé"; Required=$false},
    @{Name="stable-baselines3"; Category="RL"; Required=$false},
    @{Name="pyro-ppl"; Category="Probabilités"; Required=$false},
    @{Name="scipy"; Category="Probabilités"; Required=$true},
    @{Name="z3-solver"; Category="SymbolicAI"; Required=$true},
    @{Name="ortools"; Category="SymbolicAI"; Required=$true},
    @{Name="pygad"; Category="Algorithms génétiques"; Required=$false},
    @{Name="deap"; Category="Algorithms génétiques"; Required=$false},
    @{Name="networkx"; Category="Visualisation"; Required=$false},
    @{Name="plotly"; Category="Visualisation"; Required=$false},
    @{Name="jupyter"; Category="Environment"; Required=$true},
    @{Name="ipykernel"; Category="Environment"; Required=$true}
)

$PackageResults = @{}
$MissingRequired = @()
$MissingOptional = @()

foreach ($pkg in $CriticalPackages) {
    try {
        $version = pip show $pkg.Name 2>$null | Select-String "Version:" | ForEach-Object { $_.Line.Split(':')[1].Trim() }
        if ($version) {
            $PackageResults[$pkg.Name] = @{ Installed = $true; Version = $version; Category = $pkg.Category }
            Write-Check "$($pkg.Name)" "OK" "v$version ($($pkg.Category))"
        } else {
            $PackageResults[$pkg.Name] = @{ Installed = $false; Category = $pkg.Category; Required = $pkg.Required }
            if ($pkg.Required) {
                $MissingRequired += $pkg.Name
                Write-Check "$($pkg.Name)" "ERROR" "REQUIS MANQUANT ($($pkg.Category))"
            } else {
                $MissingOptional += $pkg.Name
                Write-Check "$($pkg.Name)" "WARNING" "Optionnel manquant ($($pkg.Category))"
            }
        }
    } catch {
        $PackageResults[$pkg.Name] = @{ Installed = $false; Error = $_.Exception.Message }
        Write-Check "$($pkg.Name)" "ERROR" "Erreur de vérification"
    }
}

$Results.Packages = $PackageResults

# =============================================================================
# 5. PERFORMANCES SYSTÈME
# =============================================================================
Write-Section "PERFORMANCES SYSTÈME"

# Espace disque
$DiskSpace = Get-WmiObject -Class Win32_LogicalDisk | Where-Object {$_.DeviceID -eq "D:"}
$FreeSpaceGB = [Math]::Round($DiskSpace.FreeSpace / 1GB, 2)
$TotalSpaceGB = [Math]::Round($DiskSpace.Size / 1GB, 2)
$UsedPercentage = [Math]::Round(($TotalSpaceGB - $FreeSpaceGB) / $TotalSpaceGB * 100, 1)

$Results.System = @{
    DiskSpace = @{
        Drive = "D:"
        FreeSpaceGB = $FreeSpaceGB
        TotalSpaceGB = $TotalSpaceGB
        UsedPercentage = $UsedPercentage
    }
    Memory = @{
        TotalGB = [Math]::Round((Get-WmiObject -Class Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2)
        Available = $true
    }
}

if ($FreeSpaceGB -lt 5) {
    Write-Check "Espace disque D:" "ERROR" "$FreeSpaceGB GB libre ($UsedPercentage% utilisé)"
    $Results.Issues += "Espace disque faible sur D: ($FreeSpaceGB GB)"
} elseif ($FreeSpaceGB -lt 20) {
    Write-Check "Espace disque D:" "WARNING" "$FreeSpaceGB GB libre ($UsedPercentage% utilisé)"
} else {
    Write-Check "Espace disque D:" "OK" "$FreeSpaceGB GB libre ($UsedPercentage% utilisé)"
}

# Processus pouvant interférer
$InterferingProcesses = @("jupyter", "dotnet", "python", "node")
$RunningProcesses = @()
foreach ($proc in $InterferingProcesses) {
    $running = Get-Process -Name $proc -ErrorAction SilentlyContinue
    if ($running) {
        $RunningProcesses += @{Name = $proc; Count = $running.Count}
        Write-Check "Processus $proc" "WARNING" "$($running.Count) instance(s) en cours"
    }
}
$Results.System.RunningProcesses = $RunningProcesses

# =============================================================================
# RÉSUMÉ ET RECOMMANDATIONS
# =============================================================================
Write-Section "RÉSUMÉ DE L'AUDIT"

$TotalIssues = $Results.Issues.Count + $MissingRequired.Count
$TotalWarnings = $MissingOptional.Count + $RunningProcesses.Count

Write-Host "`nSTATUT GLOBAL:" -ForegroundColor Yellow
if ($TotalIssues -eq 0) {
    Write-Host "✅ ENVIRONNEMENT PRÊT POUR LA FORMATION" -ForegroundColor Green
} elseif ($TotalIssues -le 3) {
    Write-Host "⚠️  PROBLÈMES MINEURS À CORRIGER" -ForegroundColor Yellow
} else {
    Write-Host "❌ PROBLÈMES CRITIQUES À RÉSOUDRE" -ForegroundColor Red
}

Write-Host "`nDÉTAILS:"
Write-Host "- Erreurs critiques: $TotalIssues" -ForegroundColor $(if ($TotalIssues -eq 0) {"Green"} else {"Red"})
Write-Host "- Avertissements: $TotalWarnings" -ForegroundColor $(if ($TotalWarnings -eq 0) {"Green"} else {"Yellow"})

if ($MissingRequired.Count -gt 0) {
    Write-Host "`nPACKAGES REQUIS MANQUANTS:" -ForegroundColor Red
    foreach ($pkg in $MissingRequired) {
        Write-Host "  - $pkg" -ForegroundColor Red
    }
    $Results.Recommendations += "Installer les packages requis: pip install " + ($MissingRequired -join " ")
}

if ($MissingOptional.Count -gt 0) {
    Write-Host "`nPACKAGES OPTIONNELS MANQUANTS:" -ForegroundColor Yellow
    foreach ($pkg in $MissingOptional) {
        Write-Host "  - $pkg" -ForegroundColor Yellow
    }
}

# Estimation temps de réparation
$RepairTimeMinutes = 0
$RepairTimeMinutes += $MissingRequired.Count * 3  # 3 min par package requis
$RepairTimeMinutes += $MissingOptional.Count * 2  # 2 min par package optionnel
$RepairTimeMinutes += $Results.Issues.Count * 5   # 5 min par problème système

Write-Host "`nESTIMATION TEMPS DE RÉPARATION: $RepairTimeMinutes minutes" -ForegroundColor Cyan

# Export des résultats
if ($ExportJson) {
    $Results | ConvertTo-Json -Depth 10 | Out-File -FilePath $ResultsFile -Encoding UTF8
    Write-Host "`nRésultats exportés vers: $ResultsFile" -ForegroundColor Green
}

# Log des résultats
$LogContent = @"
AUDIT ENVIRONNEMENT NOTEBOOKS - $(Get-Date)
==============================================
Issues: $($Results.Issues -join '; ')
Missing Required Packages: $($MissingRequired -join ', ')
Missing Optional Packages: $($MissingOptional -join ', ')
Repair Time Estimate: $RepairTimeMinutes minutes
"@

$LogContent | Out-File -FilePath $LogFile -Encoding UTF8
Write-Host "Log sauvegardé: $LogFile" -ForegroundColor Gray

return @{
    Status = if ($TotalIssues -eq 0) {"Ready"} elseif ($TotalIssues -le 3) {"MinorIssues"} else {"CriticalIssues"}
    Issues = $TotalIssues
    Warnings = $TotalWarnings
    RepairTime = $RepairTimeMinutes
    Results = $Results
}