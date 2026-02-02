param (
    [string]$UserName,
    [string]$Workshop
)

$baseDemosPath = Join-Path $PSScriptRoot -ChildPath "."
$userWorkspacesBase = Join-Path $baseDemosPath -ChildPath "workspaces"

if ($UserName) {
    if ($Workshop) {
        # Nettoyage d'un atelier spécifique
        $userPath = Join-Path $userWorkspacesBase -ChildPath $UserName
        $workshopPath = Join-Path $userPath -ChildPath $Workshop
        
        Write-Host "DEBUG: workshopPath = $workshopPath"
        Write-Host "DEBUG: Test-Path = $(Test-Path $workshopPath)"
        
        if (Test-Path $workshopPath) {
            Write-Host "Nettoyage de l'atelier '$Workshop' pour l'utilisateur '$UserName'"
            Write-Host "Contenu avant nettoyage :"
            Get-ChildItem -Path $workshopPath -Recurse | ForEach-Object {
                Write-Host "  - $($_.FullName)"
            }
            
            # Supprimer les fichiers générés
            $filesToDelete = Get-ChildItem -Path $workshopPath -File | Where-Object { 
                $_.Extension -in @('.html', '.css', '.js') -or
                $_.Name -like '*.json' -or
                $_.Name -like '*.txt' -or
                $_.Name -like '*.log'
            }
            
            foreach ($file in $filesToDelete) {
                Write-Host "Suppression de : $($file.Name)"
                try {
                    Remove-Item -Path $file.FullName -Force -ErrorAction Stop
                    Write-Host "  -> Supprimé avec succès"
                } catch {
                    Write-Host "  -> Erreur : $($_.Exception.Message)"
                }
            }
            
            # Supprimer les dossiers générés (sauf docs/ et ressources/)
            $foldersToDelete = Get-ChildItem -Path $workshopPath -Directory | Where-Object { 
                $_.Name -notin @('docs', 'ressources')
            }
            
            foreach ($folder in $foldersToDelete) {
                Write-Host "Suppression du dossier : $($folder.Name)"
                try {
                    Remove-Item -Path $folder.FullName -Recurse -Force -ErrorAction Stop
                    Write-Host "  -> Dossier supprimé avec succès"
                } catch {
                    Write-Host "  -> Erreur : $($_.Exception.Message)"
                }
            }
            
            # Nettoyer les fichiers desktop.ini dans docs/ et ressources/
            $subDirs = @('docs', 'ressources')
            foreach ($subDirName in $subDirs) {
                $subDir = Join-Path $workshopPath -ChildPath $subDirName
                if (Test-Path $subDir) {
                    $desktopIni = Join-Path $subDir -ChildPath 'desktop.ini'
                    if (Test-Path $desktopIni) {
                        Write-Host "Suppression de desktop.ini dans $subDirName"
                        try {
                            Remove-Item -Path $desktopIni -Force -ErrorAction Stop
                            Write-Host "  -> desktop.ini supprimé"
                        } catch {
                            Write-Host "  -> Erreur : $($_.Exception.Message)"
                        }
                    }
                }
            }
            
            Write-Host "Contenu après nettoyage :"
            Get-ChildItem -Path $workshopPath -Recurse | ForEach-Object {
                Write-Host "  - $($_.FullName)"
            }
            
            Write-Host "Nettoyage de l'atelier '$Workshop' terminé."
        } else {
            Write-Warning "L'atelier '$Workshop' n'existe pas : $workshopPath"
        }
    } else {
        # Nettoyage complet du workspace utilisateur
        $targetPath = Join-Path $userWorkspacesBase -ChildPath $UserName
        if (Test-Path $targetPath) {
            Write-Host "Suppression du workspace utilisateur : $UserName"
            Remove-Item -Path $targetPath -Recurse -Force
            Write-Host "Workspace supprimé."
        } else {
            Write-Warning "Le workspace n'existe pas : $targetPath"
        }
    }
} else {
    Write-Host "ATTENTION: Suppression de TOUS les workspaces sous $userWorkspacesBase."
    $confirm = Read-Host "Confirmez-vous ? (oui/non)"
    if ($confirm -eq "oui") {
        Write-Host "Suppression de tous les workspaces..."
        Get-ChildItem -Path $userWorkspacesBase -Directory | ForEach-Object {
            Write-Host "Suppression du répertoire $($_.Name)"
            Remove-Item -Path $_.FullName -Recurse -Force
        }
        Write-Host "Tous les workspaces supprimés."
    } else {
        Write-Host "Opération annulée."
    }
}