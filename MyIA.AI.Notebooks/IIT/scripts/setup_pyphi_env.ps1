# Setup script for PyPhi conda environment (Python 3.9)
# PyPhi 1.2.0 requires Python <=3.9 (collections.Iterable removed in 3.10)
#
# Usage: .\setup_pyphi_env.ps1
#
# Creates:
#   - conda env 'pyphi' with Python 3.9
#   - Jupyter kernel 'pyphi' (Python 3 - PyPhi/IIT)
#
# Prerequisites: conda (miniconda3 or anaconda)

param(
    [string]$EnvName = "pyphi",
    [string]$PythonVersion = "3.9"
)

$ErrorActionPreference = "Stop"

Write-Host "=== Setup PyPhi Environment ===" -ForegroundColor Green
Write-Host "Env name: $EnvName"
Write-Host "Python version: $PythonVersion"
Write-Host ""

# 1. Check conda is available
$condaExe = Get-Command conda -ErrorAction SilentlyContinue
if (-not $condaExe) {
    # Try common miniconda3 paths
    $condaPaths = @(
        "C:\ProgramData\miniconda3\Scripts\conda.exe",
        "$env:USERPROFILE\miniconda3\Scripts\conda.exe",
        "$env:USERPROFILE\anaconda3\Scripts\conda.exe"
    )
    foreach ($p in $condaPaths) {
        if (Test-Path $p) {
            $condaExe = $p
            break
        }
    }
}

if (-not $condaExe) {
    Write-Host "ERROR: conda not found. Install miniconda3 first." -ForegroundColor Red
    Write-Host "  https://docs.conda.io/en/latest/miniconda.html"
    exit 1
}

Write-Host "[1/4] Using conda: $condaExe" -ForegroundColor Cyan

# 2. Create conda env
$envList = & $condaExe env list 2>$null
if ($envList -match "$EnvName\s") {
    Write-Host "[2/4] Conda env '$EnvName' already exists, updating..." -ForegroundColor Yellow
} else {
    Write-Host "[2/4] Creating conda env '$EnvName' with Python $PythonVersion..." -ForegroundColor Cyan
    & $condaExe create -n $EnvName python=$PythonVersion -y 2>&1 | Out-Null
}

# 3. Install packages
Write-Host "[3/4] Installing packages..." -ForegroundColor Cyan

# Get the python path for the env
$envPython = & $condaExe run -n $EnvName python -c "import sys; print(sys.executable)" 2>$null
if (-not $envPython) {
    Write-Host "ERROR: Could not find Python in conda env '$EnvName'" -ForegroundColor Red
    exit 1
}

& $condaExe run -n $EnvName pip install --quiet pyphi==1.2.0 numpy scipy ipykernel

# 4. Register Jupyter kernel
Write-Host "[4/4] Registering Jupyter kernel..." -ForegroundColor Cyan
& $condaExe run -n $EnvName python -m ipykernel install --user --name pyphi --display-name "Python 3 (PyPhi/IIT)"

# 5. Verify
Write-Host ""
Write-Host "=== Verification ===" -ForegroundColor Green

$pyphiVer = & $condaExe run -n $EnvName python -c "import pyphi; print(pyphi.__version__)" 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "  PyPhi version: $pyphiVer" -ForegroundColor Green
} else {
    Write-Host "  PyPhi: IMPORT FAILED" -ForegroundColor Red
    Write-Host "  Error: $pyphiVer"
}

$kernelList = jupyter kernelspec list 2>$null
if ($kernelList -match "pyphi") {
    Write-Host "  Kernel 'pyphi': registered" -ForegroundColor Green
} else {
    Write-Host "  Kernel 'pyphi': NOT FOUND" -ForegroundColor Red
}

Write-Host ""
Write-Host "Setup complete. Activate with: conda activate $EnvName" -ForegroundColor Green
Write-Host "Use kernel 'Python 3 (PyPhi/IIT)' in Jupyter notebooks." -ForegroundColor Green
