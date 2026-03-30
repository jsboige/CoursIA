# Fichier: run_e2e_tests.ps1
# Description: Lance les tests End-to-End pour l'application de matching de CV.
# Ce script configure l'environnement nécessaire et exécute pytest.

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

# Déterminer le répertoire racine du projet (solution-matching-cv) de manière dynamique
# $PSScriptRoot est le répertoire où se trouve le script (scripts/)
# On remonte donc d'un niveau pour avoir la racine du projet.
$ProjectRoot = Split-Path -Parent $PSScriptRoot
Write-Output "Racine du projet: $ProjectRoot"

# Charger les variables du fichier .env situé à la racine
Load-EnvVariables -Path (Join-Path -Path $ProjectRoot -ChildPath ".env")

# Chemin vers l'exécutable Python de l'environnement virtuel (lu depuis .env)
$VenvPython = $env:VENV_PYTHON_PATH
Write-Output "Environnement virtuel: $VenvPython"


# --- Vérification ---

# Vérifier si l'interpréteur Python du venv existe
if (-not (Test-Path $VenvPython)) {
    Write-Error "L'environnement virtuel n'a pas été trouvé à l'emplacement spécifié : $VenvPython"
    Write-Error "Veuillez vérifier le chemin dans votre fichier .env (VENV_PYTHON_PATH)."
    exit 1
}

# --- Préparation de l'environnement ---

# Ajoute la racine du projet au PYTHONPATH de la session courante
Write-Host "Ajout de '$ProjectRoot' au PYTHONPATH."
$env:PYTHONPATH = "$ProjectRoot;" + $env:PYTHONPATH

# Activer les logs de performance
$env:ENABLE_PERFORMANCE_LOGS = "True"
Write-Output "Logs de performance activés."

# Se positionner à la racine du projet pour l'exécution des tests
Set-Location $ProjectRoot

# --- Exécution des tests ---
Write-Host "Lancement des tests E2E avec l'interpréteur : $VenvPython"
Write-Host "---------------------------------------------------------"

# Commande pour lancer pytest
$testDir = Join-Path -Path $ProjectRoot -ChildPath "tests\e2e"
& $VenvPython -m pytest $testDir -v --html=test_report.html

# --- Nettoyage ---
Write-Host "---------------------------------------------------------"
Write-Host "Exécution des tests terminée."

# Déplacer le rapport de test dans le dossier de documentation
$ReportPath = Join-Path $ProjectRoot "test_report.html"
$DestinationPath = Join-Path $ProjectRoot "docs"
if (Test-Path $ReportPath) {
    Write-Host "Déplacement du rapport de test vers $DestinationPath..."
    Move-Item -Path $ReportPath -Destination $DestinationPath -Force
}