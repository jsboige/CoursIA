param (
    [Parameter(Mandatory=$true)]
    [string]$UserName,

    [Parameter(Mandatory=$true)]
    [string]$Workshop,

    [string]$CorrectionName
)

# Construit le chemin source basé sur les conventions
$baseWorkspacesPath = Join-Path $PSScriptRoot -ChildPath "workspaces"
$sourceWorkspacePath = Join-Path $baseWorkspacesPath -ChildPath (Join-Path $UserName $Workshop)

# Détermine la racine du projet pour trouver le dossier "corriges" global
$projectRoot = (Get-Item $PSScriptRoot).Parent.Parent.FullName
# Le dossier "corriges" doit contenir un sous-dossier "demo-roo-code"
$baseCorrigesPath = Join-Path $projectRoot -ChildPath (Join-Path "corriges" "demo-roo-code")

# Décompose le chemin $Workshop pour la destination
# e.g., "4-creation-contenu/demo-1-web" -> "4-creation-contenu" et "demo-1-web"
$workshopParts = $Workshop -split '[/\\]'
$workshopDirectory = $workshopParts[0]
# Le reste n'est pas utilisé pour le chemin de destination, seul CorrectionName compte.

# Formate le nom du répertoire de l'atelier si nécessaire (e.g., 4-... -> 04-...)
$formattedWorkshopDirectory = $workshopDirectory
if ($workshopDirectory -match '^\d-') {
    $formattedWorkshopDirectory = "0" + $workshopDirectory
}

# Construit le chemin de destination final
# e.g., corriges/demo-roo-code/04-creation-contenu/demo-1-web-orchestration-optimisee
if (-not [string]::IsNullOrWhiteSpace($CorrectionName)) {
     $destinationPath = Join-Path $baseCorrigesPath -ChildPath (Join-Path $formattedWorkshopDirectory $CorrectionName)
}
else {
    # Fallback si pas de CorrectionName, bien que le scénario d'usage le requiert
    $destinationPath = Join-Path $baseCorrigesPath -ChildPath $formattedWorkshopDirectory
}

# --- Validation des chemins ---
if (-not (Test-Path $sourceWorkspacePath)) {
    Write-Error "Le workspace source n'existe pas : $sourceWorkspacePath"
    exit 1
}

# --- Exécution de la copie ---
Write-Host "Nettoyage de la destination : $destinationPath"
if (Test-Path $destinationPath) {
    Remove-Item -Path $destinationPath -Recurse -Force
}
New-Item -ItemType Directory -Path $destinationPath -Force | Out-Null
Write-Host "Destination préparee."


Write-Host "Copie de '$sourceWorkspacePath' vers '$destinationPath'..."

# Méthode de copie robuste inspirée de prepare-workspaces.ps1
Get-ChildItem -Path $sourceWorkspacePath -Force | ForEach-Object {
    Copy-Item -Path $_.FullName -Destination $destinationPath -Recurse -Force
}

Write-Host "Sauvegarde du workspace terminee avec succes."

# --- Génération automatique des variantes de lecture ---
Write-Host ""
Write-Host "=== GENERATION DES VARIANTES DE LECTURE ===" -ForegroundColor Green

# Recherche des fichiers de trace Roo dans la destination
$traceFiles = Get-ChildItem -Path $destinationPath -Filter "roo_task_*.md" -Recurse | Where-Object { $_.Name -notmatch "_lecture_" }

if ($traceFiles.Count -gt 0) {
    Write-Host "Traces detectees : $($traceFiles.Count)" -ForegroundColor Yellow
    
    # Chemin vers le script de conversion
    $convertScript = Join-Path $PSScriptRoot -ChildPath "Convert-TraceToSummary-Optimized.ps1"
    
    if (Test-Path $convertScript) {
        foreach ($traceFile in $traceFiles) {
            Write-Host "Generation des variantes pour : $($traceFile.Name)" -ForegroundColor Cyan
            try {
                & $convertScript -TracePath $traceFile.FullName -GenerateAllVariants
                Write-Host "✓ Variantes generees avec succes" -ForegroundColor Green
            }
            catch {
                Write-Warning "Erreur lors de la generation des variantes pour $($traceFile.Name): $($_.Exception.Message)"
            }
        }
        Write-Host ""
        Write-Host "=== GENERATION DES VARIANTES TERMINEE ===" -ForegroundColor Green
    }
    else {
        Write-Warning "Script de conversion non trouve : $convertScript"
    }
}
else {
    Write-Host "Aucune trace Roo detectee dans le workspace sauvegarde." -ForegroundColor Yellow
}