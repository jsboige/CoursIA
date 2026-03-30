# Fichier: run_unit_tests.ps1
# Description: Lance les tests unitaires pour l'application de matching de CV.

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

# Chemin vers l'environnement virtuel Python (lu depuis .env)
$VenvPython = $env:VENV_PYTHON_PATH
Write-Output "Environnement virtuel: $VenvPython"

# --- Vérification ---

if (-not (Test-Path $VenvPython)) {
    Write-Error "L'environnement virtuel n'a pas été trouvé à l'emplacement spécifié : $VenvPython"
    Write-Error "Veuillez vérifier le chemin dans votre fichier .env (VENV_PYTHON_PATH)."
    exit 1
}

# --- Préparation de l'environnement ---

$env:PYTHONPATH = "$ProjectRoot;" + $env:PYTHONPATH
Write-Host "Ajout de '$ProjectRoot' au PYTHONPATH."

# Activer les logs de performance
$env:ENABLE_PERFORMANCE_LOGS = "True"
Write-Output "Logs de performance activés."

Set-Location $ProjectRoot

# --- Exécution des tests ---
Write-Host "Lancement des tests unitaires avec l'interpréteur : $VenvPython"
Write-Host "---------------------------------------------------------"

$testDir = Join-Path -Path $ProjectRoot -ChildPath "tests\unit"
& $VenvPython -m pytest $testDir -v

Write-Host "---------------------------------------------------------"
Write-Host "Exécution des tests unitaires terminée."