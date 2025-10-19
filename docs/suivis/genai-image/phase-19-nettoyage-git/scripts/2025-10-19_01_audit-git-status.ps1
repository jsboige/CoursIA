<#
.SYNOPSIS
    Audit complet Git status avec catégorisation fichiers
    
.DESCRIPTION
    Inventorie 55 fichiers untracked et catégorise par type
    Phase 19 - Nettoyage Git
    
    Catégories:
    - TEMPORAIRE: *.log, *.tmp, *.cache
    - NOTEBOOK: *.ipynb
    - DOCUMENTATION: *.md
    - SCRIPT: *.ps1
    - CONFIG: *.json
    - DOCKER_CACHE: docker-configurations/cache|models
    - SUIVI_GENAI: docs/suivis/genai-image
    - AUTRE: Fichiers non catégorisés
    
.NOTES
    Date: 2025-10-19
    Phase: 19
    Auteur: SDDD Process
    
.EXAMPLE
    pwsh -c "& './docs/suivis/genai-image/phase-19-nettoyage-git/scripts/2025-10-19_01_audit-git-status.ps1'"
#>

#Requires -Version 7.0

# ===========================
# CONFIGURATION
# ===========================

$ErrorActionPreference = "Stop"
$OutputDir = "docs/suivis/genai-image/phase-19-nettoyage-git"
$OutputFile = "$OutputDir/2025-10-19_19_02_audit-git-status.json"
$OutputMd = "$OutputDir/2025-10-19_19_02_audit-git-status.md"

# ===========================
# FONCTIONS
# ===========================

function Get-FileCategory {
    <#
    .SYNOPSIS
        Catégorise un fichier selon son extension et répertoire
    #>
    param(
        [Parameter(Mandatory=$true)]
        [string]$Path
    )
    
    $ext = [System.IO.Path]::GetExtension($Path).ToLower()
    $dir = Split-Path $Path -Parent
    
    # Catégories par extension
    if ($ext -match '\.(log|tmp|temp|cache)$') { 
        return "TEMPORAIRE" 
    }
    
    if ($ext -match '\.ipynb$') { 
        # Sous-catégorisation notebooks
        $filename = [System.IO.Path]::GetFileNameWithoutExtension($Path)
        if ($filename -match '(executed|test|fixed|debug|diagnostic|validation)') {
            return "NOTEBOOK_TEMPORAIRE"
        }
        return "NOTEBOOK" 
    }
    
    if ($ext -match '\.md$') { 
        return "DOCUMENTATION" 
    }
    
    if ($ext -match '\.ps1$') { 
        return "SCRIPT" 
    }
    
    if ($ext -match '\.(json|yml|yaml)$') { 
        return "CONFIG" 
    }
    
    # Catégories par répertoire
    if ($dir -match 'docker-configurations[\\/](cache|models)') { 
        return "DOCKER_CACHE" 
    }
    
    if ($dir -match 'docs[\\/]suivis[\\/]genai-image') { 
        return "SUIVI_GENAI" 
    }
    
    if ($dir -match 'MyIA\.AI\.Notebooks[\\/]GenAI') {
        return "NOTEBOOK_GENAI"
    }
    
    return "AUTRE"
}

function Get-FileRisk {
    <#
    .SYNOPSIS
        Évalue le risque de commit d'un fichier
    #>
    param(
        [Parameter(Mandatory=$true)]
        [string]$Category,
        
        [Parameter(Mandatory=$true)]
        [long]$Size
    )
    
    # Risque par catégorie
    $highRiskCategories = @("TEMPORAIRE", "NOTEBOOK_TEMPORAIRE", "DOCKER_CACHE")
    $lowRiskCategories = @("DOCUMENTATION", "SCRIPT", "CONFIG", "SUIVI_GENAI")
    $mediumRiskCategories = @("NOTEBOOK", "NOTEBOOK_GENAI")
    
    if ($highRiskCategories -contains $Category) {
        return "HIGH"  # Ne devrait PAS être commité
    }
    
    if ($lowRiskCategories -contains $Category) {
        return "LOW"   # Devrait être commité
    }
    
    if ($mediumRiskCategories -contains $Category) {
        # Notebooks: vérifier taille (outputs?)
        if ($Size -gt 1MB) {
            return "MEDIUM"  # Possiblement avec outputs
        }
        return "LOW"
    }
    
    return "MEDIUM"  # Autre: nécessite examen
}

function Get-RecommendedAction {
    <#
    .SYNOPSIS
        Recommande action pour fichier selon catégorie/risque
    #>
    param(
        [Parameter(Mandatory=$true)]
        [string]$Category,
        
        [Parameter(Mandatory=$true)]
        [string]$Risk
    )
    
    switch ($Risk) {
        "HIGH" {
            switch ($Category) {
                "TEMPORAIRE" { return "SUPPRIMER" }
                "NOTEBOOK_TEMPORAIRE" { return "SUPPRIMER" }
                "DOCKER_CACHE" { return "GITIGNORE" }
                default { return "EXAMINER" }
            }
        }
        "MEDIUM" {
            return "EXAMINER"
        }
        "LOW" {
            switch ($Category) {
                "DOCUMENTATION" { return "COMMIT" }
                "SCRIPT" { return "COMMIT" }
                "CONFIG" { return "EXAMINER" }
                "SUIVI_GENAI" { return "COMMIT" }
                "NOTEBOOK" { return "COMMIT" }
                "NOTEBOOK_GENAI" { return "COMMIT" }
                default { return "EXAMINER" }
            }
        }
    }
    
    return "EXAMINER"
}

function Format-FileSize {
    <#
    .SYNOPSIS
        Formate taille fichier en unités lisibles
    #>
    param([long]$Size)
    
    if ($Size -gt 1MB) {
        return "{0:N2} MB" -f ($Size / 1MB)
    }
    elseif ($Size -gt 1KB) {
        return "{0:N2} KB" -f ($Size / 1KB)
    }
    else {
        return "$Size B"
    }
}

# ===========================
# EXÉCUTION AUDIT
# ===========================

Write-Host ""
Write-Host "=======================================" -ForegroundColor Cyan
Write-Host "  AUDIT GIT STATUS - PHASE 19" -ForegroundColor Cyan
Write-Host "=======================================" -ForegroundColor Cyan
Write-Host ""

# Vérifier Git repository
if (-not (Test-Path ".git")) {
    Write-Error "Erreur: Ce script doit être exécuté à la racine du dépôt Git"
    exit 1
}

Write-Host "Récupération fichiers untracked..." -ForegroundColor Yellow

# Récupérer fichiers untracked
$untrackedFiles = git ls-files --others --exclude-standard

if (-not $untrackedFiles) {
    Write-Host "Aucun fichier untracked trouvé!" -ForegroundColor Green
    exit 0
}

Write-Host "Fichiers untracked: $($untrackedFiles.Count)" -ForegroundColor White
Write-Host ""

# Initialiser structure audit
$audit = @{
    Date = Get-Date -Format "o"
    TotalFiles = $untrackedFiles.Count
    TotalSize = 0
    Categories = @{}
    Risks = @{}
    Actions = @{}
    Files = @()
}

# Analyser chaque fichier
Write-Host "Analyse et catégorisation..." -ForegroundColor Yellow

foreach ($file in $untrackedFiles) {
    # Obtenir infos fichier
    $size = 0
    $exists = Test-Path $file
    
    if ($exists) {
        $fileInfo = Get-Item $file
        $size = $fileInfo.Length
        $audit.TotalSize += $size
    }
    
    # Catégoriser
    $category = Get-FileCategory -Path $file
    $risk = Get-FileRisk -Category $category -Size $size
    $action = Get-RecommendedAction -Category $category -Risk $risk
    
    # Ajouter aux compteurs
    if (-not $audit.Categories.ContainsKey($category)) {
        $audit.Categories[$category] = 0
    }
    $audit.Categories[$category]++
    
    if (-not $audit.Risks.ContainsKey($risk)) {
        $audit.Risks[$risk] = 0
    }
    $audit.Risks[$risk]++
    
    if (-not $audit.Actions.ContainsKey($action)) {
        $audit.Actions[$action] = 0
    }
    $audit.Actions[$action]++
    
    # Créer entrée fichier
    $fileEntry = @{
        Path = $file
        Category = $category
        Risk = $risk
        Action = $action
        Extension = [System.IO.Path]::GetExtension($file)
        Size = $size
        SizeFormatted = Format-FileSize -Size $size
        Directory = Split-Path $file -Parent
        Exists = $exists
    }
    
    $audit.Files += $fileEntry
}

# ===========================
# AFFICHAGE RÉSUMÉ
# ===========================

Write-Host ""
Write-Host "=======================================" -ForegroundColor Cyan
Write-Host "  RÉSUMÉ AUDIT" -ForegroundColor Cyan
Write-Host "=======================================" -ForegroundColor Cyan
Write-Host ""

Write-Host "Total fichiers: " -NoNewline -ForegroundColor White
Write-Host $audit.TotalFiles -ForegroundColor Yellow

Write-Host "Taille totale:  " -NoNewline -ForegroundColor White
Write-Host (Format-FileSize -Size $audit.TotalSize) -ForegroundColor Yellow

Write-Host ""
Write-Host "--- CATÉGORIES ---" -ForegroundColor Cyan

$sortedCategories = $audit.Categories.GetEnumerator() | Sort-Object Value -Descending
foreach ($cat in $sortedCategories) {
    $percentage = [math]::Round(($cat.Value / $audit.TotalFiles) * 100, 1)
    Write-Host ("  {0,-25} : {1,3} fichiers ({2,5}%)" -f $cat.Key, $cat.Value, $percentage) -ForegroundColor White
}

Write-Host ""
Write-Host "--- NIVEAUX RISQUE ---" -ForegroundColor Cyan

$riskColors = @{
    "HIGH" = "Red"
    "MEDIUM" = "Yellow"
    "LOW" = "Green"
}

$sortedRisks = $audit.Risks.GetEnumerator() | Sort-Object Key -Descending
foreach ($risk in $sortedRisks) {
    $percentage = [math]::Round(($risk.Value / $audit.TotalFiles) * 100, 1)
    $color = $riskColors[$risk.Key]
    Write-Host ("  {0,-10} : {1,3} fichiers ({2,5}%)" -f $risk.Key, $risk.Value, $percentage) -ForegroundColor $color
}

Write-Host ""
Write-Host "--- ACTIONS RECOMMANDÉES ---" -ForegroundColor Cyan

$sortedActions = $audit.Actions.GetEnumerator() | Sort-Object Value -Descending
foreach ($action in $sortedActions) {
    $percentage = [math]::Round(($action.Value / $audit.TotalFiles) * 100, 1)
    Write-Host ("  {0,-15} : {1,3} fichiers ({2,5}%)" -f $action.Key, $action.Value, $percentage) -ForegroundColor White
}

# ===========================
# FICHIERS HAUTE PRIORITÉ
# ===========================

Write-Host ""
Write-Host "=======================================" -ForegroundColor Red
Write-Host "  FICHIERS RISQUE ÉLEVÉ (HIGH)" -ForegroundColor Red
Write-Host "=======================================" -ForegroundColor Red
Write-Host ""

$highRiskFiles = $audit.Files | Where-Object { $_.Risk -eq "HIGH" }

if ($highRiskFiles) {
    foreach ($file in $highRiskFiles) {
        Write-Host "  ❌ $($file.Path)" -ForegroundColor Red
        Write-Host "     Catégorie: $($file.Category) | Taille: $($file.SizeFormatted) | Action: $($file.Action)" -ForegroundColor DarkGray
    }
} else {
    Write-Host "  ✅ Aucun fichier à risque élevé" -ForegroundColor Green
}

# ===========================
# EXPORT JSON
# ===========================

Write-Host ""
Write-Host "Export résultats JSON..." -ForegroundColor Yellow

# Créer répertoire si nécessaire
$outputDirPath = Split-Path $OutputFile -Parent
if (-not (Test-Path $outputDirPath)) {
    New-Item -ItemType Directory -Path $outputDirPath -Force | Out-Null
}

# Exporter JSON
$audit | ConvertTo-Json -Depth 5 | Out-File -FilePath $OutputFile -Encoding UTF8

Write-Host "✅ JSON exporté: $OutputFile" -ForegroundColor Green

# ===========================
# EXPORT MARKDOWN
# ===========================

Write-Host "Export résumé Markdown..." -ForegroundColor Yellow

$mdContent = @"
# Audit Git Status - Phase 19

**Date**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**Fichiers untracked**: $($audit.TotalFiles)  
**Taille totale**: $(Format-FileSize -Size $audit.TotalSize)

---

## Résumé par Catégorie

| Catégorie | Nombre | % Total |
|-----------|--------|---------|
"@

foreach ($cat in $sortedCategories) {
    $percentage = [math]::Round(($cat.Value / $audit.TotalFiles) * 100, 1)
    $mdContent += "`n| $($cat.Key) | $($cat.Value) | $percentage% |"
}

$mdContent += @"


---

## Résumé par Risque

| Risque | Nombre | % Total |
|--------|--------|---------|
"@

foreach ($risk in $sortedRisks) {
    $percentage = [math]::Round(($risk.Value / $audit.TotalFiles) * 100, 1)
    $mdContent += "`n| $($risk.Key) | $($risk.Value) | $percentage% |"
}

$mdContent += @"


---

## Actions Recommandées

| Action | Nombre | % Total |
|--------|--------|---------|
"@

foreach ($action in $sortedActions) {
    $percentage = [math]::Round(($action.Value / $audit.TotalFiles) * 100, 1)
    $mdContent += "`n| $($action.Key) | $($action.Value) | $percentage% |"
}

$mdContent += @"


---

## Fichiers Risque Élevé (HIGH)

"@

if ($highRiskFiles) {
    foreach ($file in $highRiskFiles) {
        $mdContent += "`n- ❌ ``$($file.Path)``"
        $mdContent += "`n  - **Catégorie**: $($file.Category)"
        $mdContent += "`n  - **Taille**: $($file.SizeFormatted)"
        $mdContent += "`n  - **Action**: $($file.Action)"
        $mdContent += "`n"
    }
} else {
    $mdContent += "`n✅ Aucun fichier à risque élevé`n"
}

$mdContent += @"

---

## Liste Complète Fichiers

"@

# Grouper par catégorie
$groupedFiles = $audit.Files | Group-Object Category | Sort-Object Name

foreach ($group in $groupedFiles) {
    $mdContent += "`n### $($group.Name) ($($group.Count) fichiers)`n`n"
    
    foreach ($file in $group.Group | Sort-Object Path) {
        $riskIcon = switch ($file.Risk) {
            "HIGH" { "🔴" }
            "MEDIUM" { "🟡" }
            "LOW" { "🟢" }
        }
        
        $mdContent += "- $riskIcon ``$($file.Path)`` - $($file.SizeFormatted) - **$($file.Action)**`n"
    }
}

$mdContent += @"

---

## Fichier JSON Complet

Voir [`2025-10-19_19_02_audit-git-status.json`](2025-10-19_19_02_audit-git-status.json) pour données détaillées.

---

**Généré automatiquement** par [`scripts/2025-10-19_01_audit-git-status.ps1`](scripts/2025-10-19_01_audit-git-status.ps1)
"@

# Exporter Markdown
$mdContent | Out-File -FilePath $OutputMd -Encoding UTF8

Write-Host "✅ Markdown exporté: $OutputMd" -ForegroundColor Green

# ===========================
# CONCLUSION
# ===========================

Write-Host ""
Write-Host "=======================================" -ForegroundColor Cyan
Write-Host "  AUDIT TERMINÉ" -ForegroundColor Cyan
Write-Host "=======================================" -ForegroundColor Cyan
Write-Host ""

Write-Host "📊 Fichiers analysés: $($audit.TotalFiles)" -ForegroundColor White
Write-Host "📁 Catégories: $($audit.Categories.Count)" -ForegroundColor White
Write-Host "⚠️  Risque HIGH: $($audit.Risks['HIGH'])" -ForegroundColor Red
Write-Host ""
Write-Host "Prochaine étape: Catégorisation fichiers (étape 3)" -ForegroundColor Yellow
Write-Host ""