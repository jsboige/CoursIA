param (
    [Parameter(Mandatory=$true)]
    [string]$UserName,
    [string]$Workshop
)

$baseDemosPath = Join-Path $PSScriptRoot -ChildPath "." # ateliers/demo-roo-code
$userWorkspacesBase = Join-Path $baseDemosPath -ChildPath "workspaces"
$userWorkspacePath = Join-Path $userWorkspacesBase -ChildPath $UserName

Write-Host "Préparation de l'environnement de travail pour l'utilisateur: $UserName"

# Crée le répertoire principal de l'utilisateur si inexistant
if (-not (Test-Path $userWorkspacePath)) {
    New-Item -ItemType Directory -Path $userWorkspacePath | Out-Null
    Write-Host "Répertoire utilisateur créé : $userWorkspacePath"
} else {
    if ($Workshop) {
        Write-Warning "Le répertoire utilisateur $userWorkspacePath existe déjà. L'atelier '$Workshop' existant sera écrasé."
        # Supprimer uniquement l'atelier spécifié
        Get-ChildItem -Path $userWorkspacePath -Directory | ForEach-Object {
            if ($_.FullName -like "*$Workshop*") {
                Remove-Item -Path $_.FullName -Recurse -Force | Out-Null
                Write-Host "Contenu existant de l'atelier $($_.Name) supprimé dans $userWorkspacePath."
            }
        }
    } else {
        Write-Warning "Le répertoire utilisateur $userWorkspacePath existe déjà. Les workspaces des démos existants seront écrasés."
        # Supprimer tous les contenus des démos à l'intérieur du workspace utilisateur s'il existe
        Get-ChildItem -Path $userWorkspacePath -Directory | ForEach-Object {
            if ($_.Name -like "0*-*" -or $_.Name -like "demo-*") { # Cible les dossiers de démos
                Remove-Item -Path $_.FullName -Recurse -Force | Out-Null
                Write-Host "Contenu existant de la démo $($_.Name) supprimé dans $userWorkspacePath."
            }
        }
    }
}

# Recherche tous les dossiers de démo (0X-*, demo-*) et leurs ressources
if ($Workshop) {
    # Si un atelier spécifique est demandé, chercher uniquement cet atelier
    $demoRootPaths = Get-ChildItem -Path $baseDemosPath -Directory -Recurse -ErrorAction SilentlyContinue | Where-Object {
        ($_.Name -match "^\d{2}-" -or $_.Name -like "demo-*") -and
        ($_.FullName -notmatch "workspaces") -and
        ($_.FullName -like "*$Workshop*")
    }
    Write-Host "Recherche de l'atelier spécifique : $Workshop"
} else {
    # Recherche de tous les ateliers (comportement original)
    $demoRootPaths = Get-ChildItem -Path $baseDemosPath -Directory -Recurse -ErrorAction SilentlyContinue | Where-Object {
        ($_.Name -match "^\d{2}-" -or $_.Name -like "demo-*") -and ($_.FullName -notmatch "workspaces")
    }
    Write-Host "Recherche de tous les ateliers"
}

foreach ($demoRoot in $demoRootPaths) {
    # Ignorer les répertoires qui sont eux-mêmes des ressources
    if ($demoRoot.Name -eq "ressources" -or $demoRoot.Name -like "ressourcesX") {
        continue
    }

    # Copier tous les éléments nécessaires de l'atelier (README.md, docs/, ressources/)
    $sourceItems = Get-ChildItem -Path $demoRoot.FullName -ErrorAction SilentlyContinue | Where-Object {
        ($_.Name -eq "README.md") -or
        ($_.Name -eq "docs") -or
        ($_.Name -eq "ressources") -or
        ($_.Name -like "ressources*")
    }

    if ($sourceItems.Count -gt 0) {
        # Détermine le chemin relatif de la démo par rapport à $baseDemosPath
        $relativePath = $demoRoot.FullName.Substring($baseDemosPath.Length).TrimStart('/')

        # Construit le chemin de destination pour cette démo dans le workspace de l'utilisateur
        $destinationDemoPath = Join-Path $userWorkspacePath -ChildPath $relativePath
        
        if (-not (Test-Path $destinationDemoPath)) {
            New-Item -ItemType Directory -Path $destinationDemoPath | Out-Null
        }

        foreach ($sourceItem in $sourceItems) {
            $destinationItemPath = Join-Path $destinationDemoPath -ChildPath $sourceItem.Name
            
            Write-Host "Copie de $($sourceItem.Name) vers $($destinationItemPath)"
            
            if ($sourceItem.PSIsContainer) {
                # C'est un répertoire
                if (-not (Test-Path $destinationItemPath)) {
                    New-Item -ItemType Directory -Path $destinationItemPath -Force | Out-Null
                }
                
                # Copier le contenu du répertoire
                Get-ChildItem -Path $sourceItem.FullName -Force | ForEach-Object {
                    Copy-Item -Path $_.FullName -Destination $destinationItemPath -Recurse -Force | Out-Null
                }
            } else {
                # C'est un fichier
                Copy-Item -Path $sourceItem.FullName -Destination $destinationItemPath -Force | Out-Null
            }
        }
    }
}

if ($Workshop) {
    Write-Host "Préparation de l'atelier '$Workshop' terminée pour $UserName."
} else {
    Write-Host "Préparation de tous les workspaces terminée pour $UserName."
}