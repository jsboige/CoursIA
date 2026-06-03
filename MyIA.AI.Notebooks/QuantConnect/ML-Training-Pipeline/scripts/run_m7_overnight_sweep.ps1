$ErrorActionPreference = "Continue"
$env:CUDA_VISIBLE_DEVICES = "2"
$env:PYTHONUNBUFFERED = "1"

$ScriptDir = $PSScriptRoot
$OutDir = Join-Path $ScriptDir "..\results\m7_robustness_sweep"
$LogDir = $OutDir
$Python = "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe"
$Train = Join-Path $ScriptDir "train_multiscale_gnn.py"

function Run-Sweep {
    param([string]$Name, [string[]]$Args)
    $stamp = Get-Date -Format "yyyyMMdd_HHmmss"
    $log = Join-Path $LogDir "$Name.log"
    $json = Join-Path $OutDir "$Name.json"
    "[$(Get-Date -Format o)] START $Name" | Out-File -Append -Encoding utf8 (Join-Path $LogDir "_overall.log")
    & $Python $Train @Args --out-json $json *>&1 | Tee-Object -FilePath $log
    $exit = $LASTEXITCODE
    "[$(Get-Date -Format o)] END   $Name exit=$exit" | Out-File -Append -Encoding utf8 (Join-Path $LogDir "_overall.log")
}

# Run 1 — extended horizons (10 instead of 6), 8 seeds, 5 splits, 1000 epochs
Run-Sweep "run1_ext_horizons" @(
    "--horizons", "1", "2", "3", "4", "5", "7", "10", "14", "21", "28",
    "--seeds", "0", "1", "7", "42", "99", "777", "1024", "2048",
    "--n-splits", "5",
    "--epochs", "1000",
    "--coins", "BTC-USD", "ETH-USD",
    "--skip-remote"
)

# Run 2 — finer walk-forward (7 splits)
Run-Sweep "run2_more_splits" @(
    "--horizons", "1", "3", "5", "10", "20", "30",
    "--seeds", "0", "1", "7", "42", "99", "777", "1024", "2048",
    "--n-splits", "7",
    "--epochs", "1000",
    "--coins", "BTC-USD", "ETH-USD",
    "--skip-remote"
)

# Run 3 — extended seed bench (12 seeds)
Run-Sweep "run3_more_seeds" @(
    "--horizons", "1", "3", "5", "10", "20", "30",
    "--seeds", "0", "1", "7", "11", "13", "17", "19", "42", "99", "777", "1024", "2048",
    "--n-splits", "5",
    "--epochs", "1000",
    "--coins", "BTC-USD", "ETH-USD",
    "--skip-remote"
)

# Run 4 — longer training (2000 epochs) — undertrain check
Run-Sweep "run4_longer_training" @(
    "--horizons", "1", "3", "5", "10", "20", "30",
    "--seeds", "0", "1", "7", "42", "99", "777", "1024", "2048",
    "--n-splits", "5",
    "--epochs", "2000",
    "--coins", "BTC-USD", "ETH-USD",
    "--skip-remote"
)

"[$(Get-Date -Format o)] ALL DONE" | Out-File -Append -Encoding utf8 (Join-Path $LogDir "_overall.log")
