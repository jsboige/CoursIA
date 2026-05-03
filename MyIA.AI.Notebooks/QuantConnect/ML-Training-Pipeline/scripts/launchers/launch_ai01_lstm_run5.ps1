# launch_ai01_lstm_run5.ps1
# ai-01 RTX 4090 GPU 2 - LSTM SPY 2015-2024 training run 5
# Start-Process detached with log redirection + PID tracking
# ETA: ~30-50 min on RTX 4090
#
# Usage:
#   .\launch_ai01_lstm_run5.ps1            # Full training
#   .\launch_ai01_lstm_run5.ps1 -DryRun    # Quick validation

param(
    [switch]$DryRun
)

$ErrorActionPreference = "Stop"

# --- Environment ---
$env:CUDA_VISIBLE_DEVICES = "2"
$env:PYTHONUNBUFFERED     = "1"

# --- Config ---
$CondaEnv   = "coursia-ml-training"
$PythonExe  = "C:\Users\MYIA\miniconda3\envs\$CondaEnv\python.exe"
$ScriptsDir = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$RootDir    = Split-Path -Parent $ScriptsDir
$SharedDir  = Join-Path (Split-Path -Parent $RootDir) "shared"
$DataDir    = Join-Path (Split-Path -Parent $RootDir) "datasets\yfinance"
$TrainScript= Join-Path $ScriptsDir "train_lstm.py"

# Training hyperparameters
$HiddenSize  = 384
$NumLayers   = 4
$Epochs      = 100
$BatchSize   = 64
$SeqLen      = 30
$Lookback    = 20
$Symbol      = "SPY"
$StartDate   = "2015-01-01"
$EndDate     = "2024-12-31"

# Output dirs
$Ts         = Get-Date -Format "yyyyMMdd_HHmmss"
$OutDir     = Join-Path $RootDir "outputs\ai01_lstm_run5_$Ts"
$CkptDir    = Join-Path $RootDir "checkpoints\lstm"

# --- Pre-checks ---
Write-Host "[PRE-CHECK] Validating environment..."

if (-not (Test-Path $PythonExe)) {
    Write-Error "Python not found: $PythonExe`nActivate conda env '$CondaEnv' first."
    exit 1
}

$verCheck = & $PythonExe -c "import sys; print(sys.version)" 2>&1
Write-Host "[PRE-CHECK] Python: $verCheck"

# Verify FeatureEngineer import (post-#673 sys.path.append fix)
$importCheck = & $PythonExe -c @"
import sys
sys.path.append(r'$SharedDir')
from features import FeatureEngineer
print('OK')
"@ 2>&1
if ($importCheck -notmatch "OK") {
    Write-Error "FeatureEngineer import failed:`n$importCheck`nCheck shared/features.py"
    exit 1
}
Write-Host "[PRE-CHECK] FeatureEngineer import: OK"

# Verify torch + CUDA
$torchCheck = & $PythonExe -c @"
import torch
print(f'torch={torch.__version__} cuda={torch.cuda.is_available()} devices={torch.cuda.device_count()}')
"@ 2>&1
Write-Host "[PRE-CHECK] PyTorch: $torchCheck"

# Verify data directory
if (-not (Test-Path $DataDir)) {
    Write-Error "Data directory not found: $DataDir`nDownload yfinance data first."
    exit 1
}
$dataFiles = Get-ChildItem (Join-Path $DataDir "${Symbol}_*.csv") -ErrorAction SilentlyContinue
if ($dataFiles.Count -eq 0) {
    Write-Error "No CSV files for $Symbol in $DataDir"
    exit 1
}
Write-Host "[PRE-CHECK] Data files: $($dataFiles.Count) CSV for $Symbol"

# Verify GPU 2 available
$gpuCheck = & nvidia-smi -i 2 --query-gpu=name,memory.free,temperature.gpu --format=csv,noheader 2>&1
if ($LASTEXITCODE -ne 0) {
    Write-Warning "nvidia-smi GPU 2 query failed. GPU may not be available."
} else {
    Write-Host "[PRE-CHECK] GPU 2: $gpuCheck"
}

# --- Create output dir ---
New-Item -ItemType Directory -Path $OutDir -Force | Out-Null
Write-Host "[SETUP] Output dir: $OutDir"

# --- Dry-run mode ---
if ($DryRun) {
    Write-Host "[DRY-RUN] Running quick validation..."
    & $PythonExe $TrainScript --dry-run
    Write-Host "[DRY-RUN] Complete."
    exit $LASTEXITCODE
}

# --- Build args ---
$LogPath  = Join-Path $OutDir "train.log"
$ErrPath  = Join-Path $OutDir "train.err"
$PidPath  = Join-Path $OutDir "PID.txt"
$MetaPath = Join-Path $OutDir "run_metadata.json"

$trainArgs = @(
    $TrainScript,
    "--data-dir",       $DataDir,
    "--symbol",         $Symbol,
    "--start",          $StartDate,
    "--end",            $EndDate,
    "--hidden-size",    $HiddenSize,
    "--num-layers",     $NumLayers,
    "--epochs",         $Epochs,
    "--batch-size",     $BatchSize,
    "--seq-len",        $SeqLen,
    "--lookback",       $Lookback,
    "--checkpoint-dir", $CkptDir,
    "--advanced"
)

# --- Write metadata ---
$gitBranch = & git rev-parse --abbrev-ref HEAD 2>$null
$gitCommit = & git rev-parse --short HEAD 2>$null
$metadata = @{
    run_id      = "ai01_lstm_run5_$Ts"
    model       = "lstm"
    machine     = "myia-ai-01"
    gpu         = "RTX 4090 GPU 2"
    symbol      = $Symbol
    period      = "$StartDate to $EndDate"
    hyperparams = @{
        hidden_size = $HiddenSize
        num_layers  = $NumLayers
        epochs      = $Epochs
        batch_size  = $BatchSize
        seq_len     = $SeqLen
        lookback    = $Lookback
        features    = "advanced (19)"
    }
    branch      = if ($gitBranch) { $gitBranch } else { "unknown" }
    commit      = if ($gitCommit) { $gitCommit } else { "unknown" }
    launched_at = (Get-Date -Format "yyyy-MM-ddTHH:mm:ssZ")
    log_file    = "train.log"
    pid_file    = "PID.txt"
}
$metadata | ConvertTo-Json -Depth 3 | Out-File -FilePath $MetaPath -Encoding utf8

# --- Launch detached process ---
Write-Host "[LAUNCH] Starting LSTM training..."
Write-Host "[LAUNCH] Hidden=$HiddenSize Layers=$NumLayers Epochs=$Epochs Batch=$BatchSize Advanced=19"
Write-Host "[LAUNCH] Log: $LogPath"

$proc = Start-Process -FilePath $PythonExe `
    -ArgumentList $trainArgs `
    -RedirectStandardOutput $LogPath `
    -RedirectStandardError $ErrPath `
    -NoNewWindow `
    -PassThru

# Save PID
$proc.Id | Out-File -FilePath $PidPath -Encoding utf8

Write-Host "[LAUNCH] PID: $($proc.Id) -> $PidPath"
Write-Host ""
Write-Host "Monitor log:   Get-Content $LogPath -Wait"
Write-Host "GPU monitor:   nvidia-smi -i 2 -l 5"
Write-Host "Check status:  Get-Process -Id $($proc.Id)"
Write-Host "Stop:          Stop-Process -Id $($proc.Id)"
