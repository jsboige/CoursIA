<#
.SYNOPSIS
    Nettoie les workspaces des ateliers Claude Code.

.DESCRIPTION
    Ce script supprime les workspaces utilisateur. Peut supprimer un workspace
    specifique ou tous les workspaces avec confirmation.

.PARAMETER UserName
    (Optionnel) Nom de l'utilisateur dont le workspace doit etre supprime.
    Si non specifie, supprime tous les workspaces.

.PARAMETER Force
    (Optionnel) Supprime sans demander de confirmation.

.PARAMETER List
    (Optionnel) Liste les workspaces existants sans les supprimer.

.EXAMPLE
    .\clean-workspaces.ps1 -UserName "Jean"
    Supprime le workspace de Jean.

.EXAMPLE
    .\clean-workspaces.ps1 -Force
    Supprime tous les workspaces sans confirmation.

.EXAMPLE
    .\clean-workspaces.ps1 -List
    Liste tous les workspaces existants.
#>

param(
    [Parameter(Mandatory=$false)]
    [string]$UserName,

    [Parameter(Mandatory=$false)]
    [switch]$Force,

    [Parameter(Mandatory=$false)]
    [switch]$List
)

# Configuration
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$AteliersRoot = Split-Path -Parent $ScriptDir
$WorkspacesDir = Join-Path $AteliersRoot "workspaces"

# Fonction pour afficher les messages avec couleur
function Write-ColorMessage {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

# Fonction pour obtenir la taille d'un dossier
function Get-FolderSize {
    param([string]$Path)

    $Size = (Get-ChildItem -Path $Path -Recurse -File -ErrorAction SilentlyContinue |
             Measure-Object -Property Length -Sum).Sum

    if ($Size -gt 1GB) {
        return "{0:N2} GB" -f ($Size / 1GB)
    } elseif ($Size -gt 1MB) {
        return "{0:N2} MB" -f ($Size / 1MB)
    } elseif ($Size -gt 1KB) {
        return "{0:N2} KB" -f ($Size / 1KB)
    } else {
        return "$Size bytes"
    }
}

# Verifier que le dossier workspaces existe
if (-not (Test-Path $WorkspacesDir)) {
    Write-ColorMessage "Aucun workspace trouve. Le dossier n'existe pas." "Yellow"
    exit 0
}

# Obtenir la liste des workspaces
$Workspaces = Get-ChildItem -Path $WorkspacesDir -Directory -ErrorAction SilentlyContinue

if ($Workspaces.Count -eq 0) {
    Write-ColorMessage "Aucun workspace a nettoyer." "Yellow"
    exit 0
}

# Mode liste
if ($List) {
    Write-ColorMessage "`n=== Workspaces existants ===" "Cyan"
    Write-ColorMessage "Emplacement: $WorkspacesDir`n" "White"

    foreach ($ws in $Workspaces) {
        $Size = Get-FolderSize -Path $ws.FullName
        $Created = $ws.CreationTime.ToString("yyyy-MM-dd HH:mm")
        Write-ColorMessage "$($ws.Name)" "Green"
        Write-ColorMessage "  Cree le: $Created" "Gray"
        Write-ColorMessage "  Taille: $Size" "Gray"
    }

    Write-ColorMessage "`nTotal: $($Workspaces.Count) workspace(s)" "White"
    exit 0
}

# Nettoyage d'un workspace specifique
if ($UserName) {
    $UserWorkspace = Join-Path $WorkspacesDir $UserName

    if (-not (Test-Path $UserWorkspace)) {
        Write-ColorMessage "Workspace non trouve pour l'utilisateur: $UserName" "Red"
        exit 1
    }

    $Size = Get-FolderSize -Path $UserWorkspace

    if (-not $Force) {
        Write-ColorMessage "`nWorkspace a supprimer: $UserName ($Size)" "Yellow"
        $Response = Read-Host "Confirmer la suppression? (O/N)"
        if ($Response -notmatch '^[OoYy]') {
            Write-ColorMessage "Operation annulee." "Yellow"
            exit 0
        }
    }

    Write-ColorMessage "Suppression du workspace: $UserName..." "White"
    Remove-Item $UserWorkspace -Recurse -Force
    Write-ColorMessage "Workspace supprime avec succes." "Green"
    exit 0
}

# Nettoyage de tous les workspaces
Write-ColorMessage "`n=== Nettoyage des workspaces ===" "Cyan"
Write-ColorMessage "Workspaces trouves: $($Workspaces.Count)" "White"

foreach ($ws in $Workspaces) {
    $Size = Get-FolderSize -Path $ws.FullName
    Write-ColorMessage "  - $($ws.Name) ($Size)" "Gray"
}

if (-not $Force) {
    Write-ColorMessage "`nATTENTION: Cette operation va supprimer TOUS les workspaces!" "Red"
    $Response = Read-Host "Etes-vous sur de vouloir continuer? (O/N)"
    if ($Response -notmatch '^[OoYy]') {
        Write-ColorMessage "Operation annulee." "Yellow"
        exit 0
    }

    # Double confirmation pour suppression totale
    $Response2 = Read-Host "Tapez 'SUPPRIMER' pour confirmer"
    if ($Response2 -ne "SUPPRIMER") {
        Write-ColorMessage "Operation annulee." "Yellow"
        exit 0
    }
}

# Suppression
$DeletedCount = 0
foreach ($ws in $Workspaces) {
    Write-ColorMessage "Suppression: $($ws.Name)..." "White"
    try {
        Remove-Item $ws.FullName -Recurse -Force
        $DeletedCount++
    } catch {
        Write-ColorMessage "Erreur lors de la suppression de $($ws.Name): $_" "Red"
    }
}

Write-ColorMessage "`n=== Nettoyage termine ===" "Cyan"
Write-ColorMessage "Workspaces supprimes: $DeletedCount / $($Workspaces.Count)" "Green"
