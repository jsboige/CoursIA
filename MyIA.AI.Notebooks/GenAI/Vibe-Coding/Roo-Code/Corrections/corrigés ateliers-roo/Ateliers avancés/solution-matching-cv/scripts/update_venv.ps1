# Script pour mettre à jour l'environnement virtuel Python avec les dépendances de requirements.txt

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

# Définir le chemin de base du projet
$projectRoot = Split-Path -Parent -Path (Split-Path -Parent -Path $MyInvocation.MyCommand.Definition)
Write-Output "Racine du projet: $projectRoot"

# Charger les variables du fichier .env
Load-EnvVariables -Path (Join-Path -Path $projectRoot -ChildPath ".env")

# Chemin vers l'environnement virtuel Python (lu depuis .env)
$venvPath = $env:VENV_PYTHON_PATH
$requirementsPath = Join-Path -Path $projectRoot -ChildPath "requirements.txt"

Write-Output "Environnement virtuel: $venvPath"
Write-Output "Fichier de dépendances: $requirementsPath"

# Vérifier si les chemins existent
if (-not (Test-Path $venvPath)) {
    Write-Error "L'exécutable Python de l'environnement virtuel n'a pas été trouvé : $venvPath"
    exit 1
}
if (-not (Test-Path $requirementsPath)) {
    Write-Error "Le fichier requirements.txt n'a pas été trouvé : $requirementsPath"
    exit 1
}

# Exécuter la mise à jour des dépendances
Write-Output "Mise à jour des dépendances avec pip..."
& $venvPath -m pip install -r $requirementsPath --upgrade

Write-Output "Mise à jour terminée."