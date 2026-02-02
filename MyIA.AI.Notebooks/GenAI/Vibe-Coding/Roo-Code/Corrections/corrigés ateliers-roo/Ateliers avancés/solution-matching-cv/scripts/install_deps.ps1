# Fichier: install_deps.ps1
# Description: Installe les dépendances Python requises pour le projet en utilisant
# le fichier requirements.txt. Cible l'environnement virtuel externe.

# --- Fonctions ---

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

# --- Configuration ---

# Déterminer le répertoire racine du projet
$ProjectRoot = Split-Path -Parent $PSScriptRoot
Write-Output "Racine du projet: $ProjectRoot"

# Charger les variables du fichier .env
Load-EnvVariables -Path (Join-Path -Path $ProjectRoot -ChildPath ".env")

# Chemin vers l'exécutable Python de l'environnement virtuel (lu depuis .env)
$VenvPython = $env:VENV_PYTHON_PATH
Write-Output "Environnement virtuel cible: $VenvPython"

# Chemin vers le fichier requirements.txt
$RequirementsFile = Join-Path $ProjectRoot "requirements.txt"

# --- Vérifications ---
if (-not (Test-Path $VenvPython)) {
    Write-Error "ERREUR: L'interpréteur Python du venv n'a pas été trouvé à l'emplacement '$VenvPython'."
    Write-Error "Veuillez vérifier la variable VENV_PYTHON_PATH dans votre fichier .env."
    exit 1
}

if (-not (Test-Path $RequirementsFile)) {
    Write-Error "ERREUR: Le fichier '$RequirementsFile' est introuvable."
    exit 1
}

# --- Installation des dépendances ---
Write-Host "Installation des dépendances depuis '$RequirementsFile' dans l'environnement virtuel..."
Write-Host "Interpréteur cible : $VenvPython"
Write-Host "---------------------------------------------------------"

# Commande d'installation avec pip
& $VenvPython -m pip install -r $RequirementsFile

# Playwright nécessite une étape d'installation supplémentaire pour les navigateurs
Write-Host "Installation des navigateurs pour Playwright..."
& $VenvPython -m playwright install

Write-Host "---------------------------------------------------------"
Write-Host "Installation terminée."