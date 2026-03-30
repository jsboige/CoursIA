<#
.SYNOPSIS
    Prepare les workspaces pour les ateliers Claude Code.

.DESCRIPTION
    Ce script cree un workspace isole pour un utilisateur avec tous les fichiers
    necessaires pour suivre les ateliers Claude Code.

.PARAMETER UserName
    Nom de l'utilisateur pour qui creer le workspace.

.PARAMETER Workshop
    (Optionnel) Nom de l'atelier specifique a preparer. Si non specifie, prepare tous les ateliers.

.PARAMETER Force
    (Optionnel) Ecrase le workspace existant sans confirmation.

.EXAMPLE
    .\prepare-workspaces.ps1 -UserName "Jean"
    Prepare tous les ateliers pour l'utilisateur Jean.

.EXAMPLE
    .\prepare-workspaces.ps1 -UserName "Marie" -Workshop "01-decouverte"
    Prepare uniquement l'atelier 01 pour Marie.

.EXAMPLE
    .\prepare-workspaces.ps1 -UserName "Pierre" -Force
    Prepare tous les ateliers pour Pierre en ecrasant tout workspace existant.
#>

param(
    [Parameter(Mandatory=$true)]
    [string]$UserName,

    [Parameter(Mandatory=$false)]
    [string]$Workshop,

    [Parameter(Mandatory=$false)]
    [switch]$Force
)

# Configuration
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$AteliersRoot = Split-Path -Parent $ScriptDir
$WorkspacesDir = Join-Path $AteliersRoot "workspaces"

# Liste des ateliers disponibles
$Workshops = @(
    "01-decouverte",
    "02-orchestration-taches",
    "03-assistant-developpeur",
    "04-creation-code",
    "05-automatisation-avancee"
)

# Fonction pour afficher les messages avec couleur
function Write-ColorMessage {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

# Fonction pour copier les ressources d'un atelier
function Copy-WorkshopResources {
    param(
        [string]$WorkshopName,
        [string]$DestinationPath
    )

    $WorkshopPath = Join-Path $AteliersRoot $WorkshopName

    if (-not (Test-Path $WorkshopPath)) {
        Write-ColorMessage "Atelier non trouve: $WorkshopName" "Yellow"
        return $false
    }

    # Creer le dossier destination
    $WorkshopDest = Join-Path $DestinationPath $WorkshopName
    if (-not (Test-Path $WorkshopDest)) {
        New-Item -ItemType Directory -Path $WorkshopDest -Force | Out-Null
    }

    # Copier le README principal de l'atelier
    $ReadmePath = Join-Path $WorkshopPath "README.md"
    if (Test-Path $ReadmePath) {
        Copy-Item $ReadmePath -Destination $WorkshopDest -Force
    }

    # Copier le fichier de taches
    $TachesPath = Join-Path $WorkshopPath "taches-demo.md"
    if (Test-Path $TachesPath) {
        Copy-Item $TachesPath -Destination $WorkshopDest -Force
    }

    # Parcourir les demos
    Get-ChildItem -Path $WorkshopPath -Directory | Where-Object { $_.Name -like "demo-*" } | ForEach-Object {
        $DemoName = $_.Name
        $DemoPath = $_.FullName
        $DemoDest = Join-Path $WorkshopDest $DemoName

        # Creer le dossier demo
        if (-not (Test-Path $DemoDest)) {
            New-Item -ItemType Directory -Path $DemoDest -Force | Out-Null
        }

        # Copier le README de la demo
        $DemoReadme = Join-Path $DemoPath "README.md"
        if (Test-Path $DemoReadme) {
            Copy-Item $DemoReadme -Destination $DemoDest -Force
        }

        # Copier les ressources
        $RessourcesPath = Join-Path $DemoPath "ressources"
        if (Test-Path $RessourcesPath) {
            $RessourcesDest = Join-Path $DemoDest "ressources"
            Copy-Item $RessourcesPath -Destination $DemoDest -Recurse -Force
        }

        # Creer un dossier de travail pour l'utilisateur
        $WorkDir = Join-Path $DemoDest "travail"
        if (-not (Test-Path $WorkDir)) {
            New-Item -ItemType Directory -Path $WorkDir -Force | Out-Null
        }

        Write-ColorMessage "  - $DemoName" "Gray"
    }

    return $true
}

# Verifier que le nom d'utilisateur est valide
if ($UserName -match '[\\/:*?"<>|]') {
    Write-ColorMessage "Erreur: Le nom d'utilisateur contient des caracteres invalides." "Red"
    exit 1
}

# Creer le dossier workspaces si necessaire
if (-not (Test-Path $WorkspacesDir)) {
    New-Item -ItemType Directory -Path $WorkspacesDir -Force | Out-Null
}

# Chemin du workspace utilisateur
$UserWorkspace = Join-Path $WorkspacesDir $UserName

# Verifier si le workspace existe deja
if (Test-Path $UserWorkspace) {
    if (-not $Force) {
        $Response = Read-Host "Le workspace pour '$UserName' existe deja. Voulez-vous l'ecraser? (O/N)"
        if ($Response -notmatch '^[OoYy]') {
            Write-ColorMessage "Operation annulee." "Yellow"
            exit 0
        }
    }
    Remove-Item $UserWorkspace -Recurse -Force
}

# Creer le workspace
New-Item -ItemType Directory -Path $UserWorkspace -Force | Out-Null

Write-ColorMessage "`n=== Preparation du workspace Claude Code ===" "Cyan"
Write-ColorMessage "Utilisateur: $UserName" "White"
Write-ColorMessage "Destination: $UserWorkspace`n" "White"

# Determiner quels ateliers preparer
$WorkshopsToPrepare = if ($Workshop) { @($Workshop) } else { $Workshops }

# Preparer chaque atelier
$SuccessCount = 0
foreach ($ws in $WorkshopsToPrepare) {
    Write-ColorMessage "Preparation de l'atelier: $ws" "Green"
    if (Copy-WorkshopResources -WorkshopName $ws -DestinationPath $UserWorkspace) {
        $SuccessCount++
    }
}

# Creer un fichier CLAUDE.md de base dans le workspace
$ClaudeMdContent = @"
# Workspace Claude Code - $UserName

## Informations

- Utilisateur: $UserName
- Date de creation: $(Get-Date -Format "yyyy-MM-dd HH:mm")

## Structure

Ce workspace contient les ateliers Claude Code suivants:

$(foreach ($ws in $WorkshopsToPrepare) { "- $ws`n" })

## Instructions

1. Ouvrez ce dossier dans VS Code
2. Suivez les instructions de chaque atelier dans l'ordre
3. Utilisez le dossier 'travail' de chaque demo pour vos exercices

## Notes personnelles

[Ajoutez vos notes ici pendant la formation]
"@

$ClaudeMdPath = Join-Path $UserWorkspace "CLAUDE.md"
Set-Content -Path $ClaudeMdPath -Value $ClaudeMdContent -Encoding UTF8

# Creer un fichier .gitignore pour le workspace
$GitignoreContent = @"
# Fichiers temporaires
*.tmp
*.temp
*.log

# Environnements Python
venv/
.venv/
__pycache__/
*.pyc

# IDE
.vscode/
.idea/

# Secrets
.env
.env.local
.claude/settings.local.json
"@

$GitignorePath = Join-Path $UserWorkspace ".gitignore"
Set-Content -Path $GitignorePath -Value $GitignoreContent -Encoding UTF8

# Resume
Write-ColorMessage "`n=== Preparation terminee ===" "Cyan"
Write-ColorMessage "Ateliers prepares: $SuccessCount / $($WorkshopsToPrepare.Count)" "White"
Write-ColorMessage "Workspace: $UserWorkspace" "Green"
Write-ColorMessage "`nPour commencer, ouvrez ce dossier dans VS Code:" "White"
Write-ColorMessage "  code `"$UserWorkspace`"" "Yellow"
