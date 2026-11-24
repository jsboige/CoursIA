# Setup script for the DEDICATED ICT execution environment (Python 3.9)
#
# L'env `ict-py39` est l'environnement d'execution dedie de la serie IIT/ICT
# (MyIA.AI.Notebooks/IIT/ICT-Series). Il unifie, dans UN SEUL env, les trois
# exigences qui ne tiennent pas ensemble dans l'env py3.13 partage de la flotte :
#   - numpy < 2.0          (pyemd / pyphi exigent numpy 1.x)
#   - torch (CPU)          (strates LLM/SAE : ICT-21/22/24, ICT-SAE-JLens, ICT-40a)
#   - le package local `ict` (simulations, F/Lens, bridges -- `from ict import ...`)
#
# Usage: .\setup_ict_env.ps1
#         (Linux/macOS : bash scripts/setup_ict_env.sh)
#
# Creates:
#   - conda env 'ict-py39' (cloné de l'env 'pyphi' de base)
#   - le package local `ict` installe en editable (pip install -e ICT-Series)
#   - torch (build CPU) + transformers (strates LLM/SAE)
#   - Jupyter kernel 'ict-py39' (Python 3 (ICT 3.9 dedicated))
#
# Prerequisites:
#   - l'env de base 'pyphi' DOIT exister (creé par setup_pyphi_env.ps1) :
#     ce script le CLONE pour heriter de pyemd 0.5.1 binaire prebuilt.
#   - conda (miniconda3 ou anaconda)
#
# NOTE pourquoi on CLONE pyphi plutot qu'on cree l'env a zero :
# PyPI ne publie AUCUN wheel cp39 de pyemd 0.5.1, et conda-forge ne fournit
# pas de gcc utilisable sur cette machine Windows (c-compiler / m2w64-gcc ne
# livrent pas de compilateur fonctionnel, mesure firsthand 2026-11-08). Compiler
# la sdist de pyemd est donc un impasse ; l'env 'pyphi' de base porte deja
# pyemd 0.5.1 binaire (lie numpy 1.x) + pyphi 1.2.0 + numpy<2 + scipy. Le
# cloner herite de tout ca pour free, puis on n'ajoute que le package local
# `ict` + torch/transformers.

param(
    [string]$EnvName = "ict-py39",
    [string]$BaseEnv = "pyphi"
)

$ErrorActionPreference = "Stop"

Write-Host "=== Setup ICT (IIT/ICT-Series) Environment ===" -ForegroundColor Green
Write-Host "Env name: $EnvName"
Write-Host "Base env (cloned): $BaseEnv"
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

Write-Host "[1/5] Using conda: $condaExe" -ForegroundColor Cyan

# 2. Clone the base 'pyphi' env (inherits prebuilt pyemd 0.5.1 + pyphi + numpy<2)
#    cf. NOTE en tete : c'est le chemin sans compilateur.
$envList = & $condaExe env list 2>$null
if ($envList -notmatch "$BaseEnv\s") {
    Write-Host "ERROR: base conda env '$BaseEnv' absent. Creer d'abord l'env de base" -ForegroundColor Red
    Write-Host "  via : .\setup_pyphi_env.ps1   (puis relancer ce script)" -ForegroundColor Red
    exit 1
}
if ($envList -match "$EnvName\s") {
    Write-Host "[2/5] Conda env '$EnvName' already exists, reusing..." -ForegroundColor Yellow
} else {
    Write-Host "[2/5] Cloning conda env '$BaseEnv' -> '$EnvName' (heritage pyemd prebuilt)..." -ForegroundColor Cyan
    & $condaExe create -n $EnvName --clone $BaseEnv -y 2>&1 | Out-Null
}

# 3. Install the local `ict` package (editable) + its declared core deps.
#    Les pins durs (pyphi==1.2.0, numpy<2) sont deja satisfaits par le clone,
#    le resolver ne les touche pas ; pip complete seulement ce qui manque
#    (antropy, pandas, cryptography -- tous en wheel, sans compilation).
Write-Host "[3/5] Installing local package `ict` (editable)..." -ForegroundColor Cyan
$ictSeriesDir = Join-Path $PSScriptRoot "..\ICT-Series"
if (-not (Test-Path $ictSeriesDir)) {
    Write-Host "ERROR: ICT-Series dir not found at $ictSeriesDir" -ForegroundColor Red
    exit 1
}
& $condaExe run -n $EnvName pip install --quiet -e $ictSeriesDir

# 4. torch (build CPU) + transformers pour les strates LLM/SAE
Write-Host "[4/5] Installing torch (CPU) + transformers..." -ForegroundColor Cyan
& $condaExe run -n $EnvName pip install --quiet torch --index-url https://download.pytorch.org/whl/cpu
& $condaExe run -n $EnvName pip install --quiet transformers

# 5. Register Jupyter kernel
Write-Host "[5/5] Registering Jupyter kernel..." -ForegroundColor Cyan
& $condaExe run -n $EnvName python -m ipykernel install --user --name $EnvName --display-name "Python 3 (ICT 3.9 dedicated)"

# Verify
Write-Host ""
Write-Host "=== Verification ===" -ForegroundColor Green

$stack = & $condaExe run -n $EnvName python -c "import numpy, pyphi, ict, torch, transformers; print('numpy', numpy.__version__); print('pyphi', pyphi.__version__); print('torch', torch.__version__); print('transformers', transformers.__version__); print('ict', ict.__file__)" 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "  Stack:" -ForegroundColor Green
    $stack | ForEach-Object { Write-Host "    $_" -ForegroundColor Green }
} else {
    Write-Host "  ICT stack: IMPORT FAILED" -ForegroundColor Red
    Write-Host "  Error: $stack"
}

$kernelList = jupyter kernelspec list 2>$null
if ($kernelList -match $EnvName) {
    Write-Host "  Kernel '$EnvName': registered" -ForegroundColor Green
} else {
    Write-Host "  Kernel '$EnvName': NOT FOUND" -ForegroundColor Red
}

Write-Host ""
Write-Host "Setup complete. Activate with: conda activate $EnvName" -ForegroundColor Green
Write-Host "Use kernel 'Python 3 (ICT 3.9 dedicated)' for the IIT/ICT notebooks." -ForegroundColor Green
