<#
.SYNOPSIS
    Exécution des commits structurés thématiques - Phase 19

.DESCRIPTION
    Script autonome pour effectuer 4 commits thématiques selon la stratégie validée:
    1. Mise à jour .gitignore (chore)
    2. Documentation Phases 14-17 (docs)
    3. Documentation Phases 18-19 (docs)
    4. Notebooks et guides pédagogiques (feat)
    
    Phase 19 - Nettoyage Git CoursIA
    
.NOTES
    Auteur: SDDD Process Autonome
    Date: 2025-10-19
    Phase: 19
    Étape: 8/11
    
    Prérequis:
    - Checkpoint SDDD validé (étape 6)
    - .gitignore à jour
    - Aucun fichier temporaire à commiter
    
    Sécurité:
    - Vérification git status avant chaque commit
    - Log SHA de chaque commit
    - Validation messages conventionnels
    
    Usage:
    pwsh -c "& 'docs/suivis/genai-image/phase-19-nettoyage-git/scripts/2025-10-19_05_commits-structures.ps1'"

.EXAMPLE
    # Exécution standard
    pwsh -c "& './2025-10-19_05_commits-structures.ps1'"
    
.OUTPUTS
    - Fichier log: 2025-10-19_19_08_commits-structures.log
    - 4 commits Git avec messages conventionnels
    - Rapport JSON avec SHA de chaque commit
#>

#Requires -Version 7.0

# ===========================
# CONFIGURATION
# ===========================

$ErrorActionPreference = "Stop"
$ProgressPreference = "Continue"

# Chemins
$ScriptDir = $PSScriptRoot
$PhaseDir = Split-Path $ScriptDir -Parent
$LogFile = Join-Path $PhaseDir "2025-10-19_19_08_commits-structures.log"
$ReportFile = Join-Path $PhaseDir "2025-10-19_19_08_commits-structures.json"

# Initialisation rapport
$Report = @{
    Date = Get-Date -Format "o"
    Script = $MyInvocation.MyCommand.Name
    Commits = @()
    Errors = @()
    Status = "RUNNING"
}

# ===========================
# FONCTIONS UTILITAIRES
# ===========================

function Write-Log {
    param(
        [string]$Message,
        [ValidateSet("INFO", "SUCCESS", "WARNING", "ERROR")]
        [string]$Level = "INFO"
    )
    
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    
    # Couleur console
    $color = switch ($Level) {
        "INFO"    { "White" }
        "SUCCESS" { "Green" }
        "WARNING" { "Yellow" }
        "ERROR"   { "Red" }
    }
    
    Write-Host $logMessage -ForegroundColor $color
    Add-Content -Path $LogFile -Value $logMessage -Encoding UTF8
}

function Test-GitStatus {
    <#
    .SYNOPSIS
        Vérifie le statut Git avant commit
    #>
    
    Write-Log "Vérification git status..." -Level INFO
    
    $status = git status --porcelain
    
    if ([string]::IsNullOrWhiteSpace($status)) {
        Write-Log "Aucun changement à commiter" -Level WARNING
        return $false
    }
    
    Write-Log "Changements détectés:" -Level INFO
    $status -split "`n" | ForEach-Object {
        Write-Log "  $_" -Level INFO
    }
    
    return $true
}

function Invoke-GitCommit {
    <#
    .SYNOPSIS
        Exécute un commit Git avec validation
    #>
    param(
        [Parameter(Mandatory)]
        [string[]]$FilePaths,
        
        [Parameter(Mandatory)]
        [string]$Message,
        
        [Parameter(Mandatory)]
        [string]$CommitNumber
    )
    
    Write-Log "=== COMMIT $CommitNumber ===" -Level INFO
    Write-Log "Message: $Message" -Level INFO
    
    $commitResult = @{
        Number = $CommitNumber
        Message = $Message
        Files = $FilePaths
        SHA = $null
        Success = $false
        Error = $null
    }
    
    try {
        # Vérifier existence fichiers
        foreach ($file in $FilePaths) {
            if (-not (Test-Path $file)) {
                throw "Fichier introuvable: $file"
            }
        }
        
        # Git add
        Write-Log "Staging fichiers..." -Level INFO
        foreach ($file in $FilePaths) {
            git add $file
            if ($LASTEXITCODE -ne 0) {
                throw "Échec git add pour: $file"
            }
            Write-Log "  Stagé: $file" -Level INFO
        }
        
        # Vérifier status après staging
        if (-not (Test-GitStatus)) {
            Write-Log "Aucun fichier stagé pour commit $CommitNumber" -Level WARNING
            $commitResult.Error = "No changes staged"
            return $commitResult
        }
        
        # Git commit
        Write-Log "Exécution commit..." -Level INFO
        git commit -m $Message
        
        if ($LASTEXITCODE -ne 0) {
            throw "Échec git commit"
        }
        
        # Récupérer SHA
        $sha = git rev-parse HEAD
        $commitResult.SHA = $sha
        $commitResult.Success = $true
        
        Write-Log "Commit réussi: $sha" -Level SUCCESS
        Write-Log "  Fichiers: $($FilePaths.Count)" -Level SUCCESS
        
    } catch {
        $commitResult.Error = $_.Exception.Message
        Write-Log "Erreur commit $CommitNumber : $($_.Exception.Message)" -Level ERROR
        $Report.Errors += $commitResult
    }
    
    return $commitResult
}

# ===========================
# SCRIPT PRINCIPAL
# ===========================

Write-Log "========================================" -Level INFO
Write-Log "COMMITS STRUCTURÉS - PHASE 19" -Level INFO
Write-Log "========================================" -Level INFO
Write-Log ""

try {
    # Vérifier état initial Git
    Write-Log "Vérification état Git initial..." -Level INFO
    $initialStatus = git status --short
    Write-Log "État initial:" -Level INFO
    Write-Log $initialStatus -Level INFO
    Write-Log ""
    
    # ===========================
    # COMMIT 1: .gitignore
    # ===========================
    
    $commit1 = Invoke-GitCommit `
        -FilePaths @(".gitignore") `
        -Message "chore: Mise à jour .gitignore (docker cache, logs, notebooks tmp) - Phase 19" `
        -CommitNumber "1"
    
    $Report.Commits += $commit1
    Write-Log ""
    
    # ===========================
    # COMMIT 2: Docs Phases 14-17
    # ===========================
    
    $commit2 = Invoke-GitCommit `
        -FilePaths @(
            "docs/suivis/genai-image/phase-14-audit-infrastructure",
            "docs/suivis/genai-image/phase-14b-tests-apis",
            "docs/suivis/genai-image/phase-15-docker-local",
            "docs/suivis/genai-image/phase-16-execution-tests",
            "docs/suivis/genai-image/phase-17-reparation-mcp"
        ) `
        -Message "docs: Ajout documentation Phases 14-17 suivis GenAI Image" `
        -CommitNumber "2"
    
    $Report.Commits += $commit2
    Write-Log ""
    
    # ===========================
    # COMMIT 3: Docs Phases 18-19
    # ===========================
    
    $commit3 = Invoke-GitCommit `
        -FilePaths @(
            "docs/suivis/genai-image/phase-18-notebook-forge",
            "docs/suivis/genai-image/phase-19-nettoyage-git"
        ) `
        -Message "docs: Ajout documentation Phases 18-19 suivis GenAI Image" `
        -CommitNumber "3"
    
    $Report.Commits += $commit3
    Write-Log ""
    
    # ===========================
    # COMMIT 4: Notebooks + Guides
    # ===========================
    
    $commit4 = Invoke-GitCommit `
        -FilePaths @(
            "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb",
            "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo_README.md",
            "docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md"
        ) `
        -Message "feat: Ajout notebook pédagogique Stable Diffusion Forge + Guide APIs - Phase 18" `
        -CommitNumber "4"
    
    $Report.Commits += $commit4
    Write-Log ""
    
    # ===========================
    # RÉSUMÉ FINAL
    # ===========================
    
    Write-Log "========================================" -Level INFO
    Write-Log "RÉSUMÉ COMMITS" -Level INFO
    Write-Log "========================================" -Level INFO
    
    $successCount = ($Report.Commits | Where-Object { $_.Success }).Count
    $totalCount = $Report.Commits.Count
    
    Write-Log "Total commits: $totalCount" -Level INFO
    Write-Log "Succès: $successCount" -Level SUCCESS
    Write-Log "Échecs: $($totalCount - $successCount)" -Level $(if ($successCount -eq $totalCount) { "SUCCESS" } else { "WARNING" })
    Write-Log ""
    
    foreach ($commit in $Report.Commits) {
        if ($commit.Success) {
            Write-Log "✓ Commit $($commit.Number): $($commit.SHA)" -Level SUCCESS
            Write-Log "  Message: $($commit.Message)" -Level INFO
        } else {
            Write-Log "✗ Commit $($commit.Number): ÉCHEC" -Level ERROR
            Write-Log "  Erreur: $($commit.Error)" -Level ERROR
        }
    }
    
    # Statut final
    if ($successCount -eq $totalCount) {
        $Report.Status = "SUCCESS"
        Write-Log ""
        Write-Log "Tous les commits ont réussi ✓" -Level SUCCESS
    } else {
        $Report.Status = "PARTIAL_SUCCESS"
        Write-Log ""
        Write-Log "Certains commits ont échoué" -Level WARNING
    }
    
} catch {
    $Report.Status = "ERROR"
    $Report.Errors += @{
        Message = $_.Exception.Message
        StackTrace = $_.ScriptStackTrace
    }
    Write-Log "Erreur critique: $($_.Exception.Message)" -Level ERROR
} finally {
    # Export rapport JSON
    $Report.EndDate = Get-Date -Format "o"
    $Report | ConvertTo-Json -Depth 5 | Out-File -FilePath $ReportFile -Encoding UTF8
    
    Write-Log ""
    Write-Log "Rapport exporté: $ReportFile" -Level INFO
    Write-Log "Log complet: $LogFile" -Level INFO
}

# Retour code exit
if ($Report.Status -eq "SUCCESS") {
    exit 0
} elseif ($Report.Status -eq "PARTIAL_SUCCESS") {
    exit 1
} else {
    exit 2
}