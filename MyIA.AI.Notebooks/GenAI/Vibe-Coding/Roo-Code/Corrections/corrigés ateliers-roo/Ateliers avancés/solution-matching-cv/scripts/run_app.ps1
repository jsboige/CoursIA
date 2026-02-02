# Script pour lancer l'application Flask de matching de CV.
# Ce script utilise l'environnement virtuel configuré dans le fichier .env

# Fonction pour charger les variables d'environnement depuis un fichier .env
function Load-EnvVariables {
    param (
        [string]$Path = ".env"
    )
    if (Test-Path $Path) {
        Get-Content $Path | ForEach-Object {
            $line = $_.Trim()
            if ($line -and !$line.StartsWith("#")) {
                $parts = $line.Split("=", 2)
                if ($parts.Length -eq 2) {
                    $key = $parts[0].Trim()
                    $value = $parts[1].Trim().Trim('"')
                    [System.Environment]::SetEnvironmentVariable($key, $value, "Process")
                }
            }
        }
    }
}

# Définir la racine du projet en remontant d'un niveau par rapport à l'emplacement du script
$ProjectRoot = Split-Path -Parent -Path $PSScriptRoot
Set-Location $ProjectRoot
Write-Host "Racine du projet: $ProjectRoot"

# Charger les variables du fichier .env
Load-EnvVariables -Path (Join-Path -Path $ProjectRoot -ChildPath ".env")

# Chemin vers l'exécutable Python de l'environnement virtuel (lu depuis .env)
$PythonExe = $env:VENV_PYTHON_PATH
Write-Host "Utilisation de l'environnement Python : $PythonExe"

# Vérifier si l'exécutable Python de l'environnement virtuel existe
if (-not (Test-Path $PythonExe)) {
    Write-Error "L'exécutable Python de l'environnement virtuel n'a pas été trouvé à l'emplacement spécifié : $PythonExe"
    Write-Error "Veuillez vérifier la variable VENV_PYTHON_PATH dans votre fichier .env et vous assurer que l'environnement est correctement installé."
    exit 1
}

# Mettre à jour le PYTHONPATH pour que les modules de l'application soient trouvables
$env:PYTHONPATH = "$ProjectRoot;$env:PYTHONPATH"
Write-Host "PYTHONPATH mis à jour."

# Lancer l'application Flask
Write-Host "Lancement du serveur Flask..."
Write-Host "Vous pourrez accéder à l'application sur http://127.0.0.1:5000"
Write-Host "(Utilisez Ctrl+C dans le terminal pour arrêter le serveur)"

& $PythonExe main.py