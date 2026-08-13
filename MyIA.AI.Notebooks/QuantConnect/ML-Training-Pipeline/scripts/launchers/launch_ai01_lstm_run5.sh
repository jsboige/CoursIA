#!/usr/bin/env bash
# launch_ai01_lstm_run5.sh
# ai-01 RTX 4090 GPU 2 - LSTM SPY 2015-2024 training run 5
# Detached launch with log redirection + PID tracking (bash idiomatique)
# ETA: ~30-50 min on RTX 4090
#
# Usage:
#   ./launch_ai01_lstm_run5.sh            # Full training
#   ./launch_ai01_lstm_run5.sh --dry-run  # Quick validation
#
# See launch_ai01_lstm_run5.ps1 for the Windows companion.

set -euo pipefail

DRY_RUN=0
for arg in "$@"; do
    case "$arg" in
        --dry-run) DRY_RUN=1 ;;
        -h|--help)
            sed -n '2,11p' "$0"
            exit 0
            ;;
        *) echo "Unknown argument: $arg" >&2; exit 2 ;;
    esac
done

# --- Environment ---
export CUDA_VISIBLE_DEVICES=2
export PYTHONUNBUFFERED=1

# --- Config ---
CONDA_ENV="coursia-ml-training"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# Layout: scripts/launchers/<this>.sh -> ../../  is ML-Training-Pipeline root
ROOT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shared dir is sibling of ML-Training-Pipeline
SHARED_DIR="$(cd "${ROOT_DIR}/../shared" && pwd)"
DATA_DIR="${ROOT_DIR}/datasets/yfinance"
TRAIN_SCRIPT="${ROOT_DIR}/scripts/train_lstm.py"

# Training hyperparameters
HIDDEN_SIZE=384
NUM_LAYERS=4
EPOCHS=100
BATCH_SIZE=64
SEQ_LEN=30
LOOKBACK=20
SYMBOL="SPY"
START_DATE="2015-01-01"
END_DATE="2024-12-31"

TS="$(date -u +%Y%m%d_%H%M%S)"
OUT_DIR="${ROOT_DIR}/outputs/ai01_lstm_run5_${TS}"
CKPT_DIR="${ROOT_DIR}/checkpoints/lstm"

# --- Pre-checks ---
echo "[PRE-CHECK] Validating environment..."

# Locate Python in the conda env. On Mac/Linux, conda envs live under
# $HOME/miniconda3 (or $CONDA_PREFIX if already activated). We honour the env
# override if the user has activated one.
if [[ -n "${CONDA_PREFIX:-}" ]]; then
    PYTHON_EXE="${CONDA_PREFIX}/bin/python"
elif command -v conda >/dev/null 2>&1; then
    PYTHON_EXE="$(conda env list 2>/dev/null | awk -v env="${CONDA_ENV}" '$1==env {print $NF}')/bin/python"
else
    echo "ERROR: conda not found and CONDA_PREFIX unset." >&2
    echo "Activate the '${CONDA_ENV}' env first or install Miniconda." >&2
    exit 1
fi

if [[ ! -x "${PYTHON_EXE}" ]]; then
    echo "ERROR: Python not found: ${PYTHON_EXE}" >&2
    echo "Activate conda env '${CONDA_ENV}' first." >&2
    exit 1
fi

echo "[PRE-CHECK] Python: $("${PYTHON_EXE}" -c 'import sys; print(sys.version)')"

# Verify FeatureEngineer import (FeatureEngineer lives in
# ML-Training-Pipeline/scripts/features.py, not shared/features.py).
IMPORT_CHECK="$("${PYTHON_EXE}" - <<'PY' 2>&1
import sys
sys.path.insert(0, "${ROOT_DIR}/scripts")
sys.path.append("${SHARED_DIR}")
from features import FeatureEngineer
print("OK")
PY
)"
if [[ "${IMPORT_CHECK}" != "OK" ]]; then
    echo "ERROR: FeatureEngineer import failed:" >&2
    echo "${IMPORT_CHECK}" >&2
    echo "Check shared/features.py" >&2
    exit 1
fi
echo "[PRE-CHECK] FeatureEngineer import: OK"

# Verify torch + CUDA
TORCH_CHECK="$("${PYTHON_EXE}" - <<'PY' 2>&1
import torch
print(f"torch={torch.__version__} cuda={torch.cuda.is_available()} devices={torch.cuda.device_count()}")
PY
)"
echo "[PRE-CHECK] PyTorch: ${TORCH_CHECK}"

# Verify data directory
if [[ ! -d "${DATA_DIR}" ]]; then
    echo "ERROR: Data directory not found: ${DATA_DIR}" >&2
    echo "Download yfinance data first." >&2
    exit 1
fi
DATA_FILES=$(ls "${DATA_DIR}/${SYMBOL}_"*.csv 2>/dev/null | wc -l)
if [[ "${DATA_FILES}" -eq 0 ]]; then
    echo "ERROR: No CSV files for ${SYMBOL} in ${DATA_DIR}" >&2
    exit 1
fi
echo "[PRE-CHECK] Data files: ${DATA_FILES} CSV for ${SYMBOL}"

# Verify GPU 2 available (use $CUDA_VISIBLE_DEVICES=2 means device index 0 inside the process).
GPU_CHECK=""
if command -v nvidia-smi >/dev/null 2>&1; then
    GPU_CHECK="$(nvidia-smi -i "${CUDA_VISIBLE_DEVICES}" --query-gpu=name,memory.free,temperature.gpu --format=csv,noheader 2>&1 || true)"
fi
if [[ -z "${GPU_CHECK}" ]]; then
    echo "[PRE-CHECK] WARN: nvidia-smi GPU ${CUDA_VISIBLE_DEVICES} query failed. GPU may not be available."
else
    echo "[PRE-CHECK] GPU ${CUDA_VISIBLE_DEVICES}: ${GPU_CHECK}"
fi

# --- Create output dir ---
mkdir -p "${OUT_DIR}"
echo "[SETUP] Output dir: ${OUT_DIR}"

# --- Dry-run mode ---
if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[DRY-RUN] Running quick validation..."
    "${PYTHON_EXE}" "${TRAIN_SCRIPT}" --dry-run
    echo "[DRY-RUN] Complete."
    exit $?
fi

# --- Build args ---
LOG_PATH="${OUT_DIR}/train.log"
ERR_PATH="${OUT_DIR}/train.err"
PID_PATH="${OUT_DIR}/PID.txt"
META_PATH="${OUT_DIR}/run_metadata.json"

# --- Write metadata (Python is more portable than jq for JSON output) ---
GIT_BRANCH="$(git -C "${ROOT_DIR}" rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
GIT_COMMIT="$(git -C "${ROOT_DIR}" rev-parse --short HEAD 2>/dev/null || echo unknown)"
LAUNCHED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

"${PYTHON_EXE}" - <<PY > "${META_PATH}"
import json
print(json.dumps({
    "run_id": "ai01_lstm_run5_${TS}",
    "model": "lstm",
    "machine": "myia-ai-01",
    "gpu": "RTX 4090 GPU 2",
    "symbol": "${SYMBOL}",
    "period": "${START_DATE} to ${END_DATE}",
    "hyperparams": {
        "hidden_size": ${HIDDEN_SIZE},
        "num_layers": ${NUM_LAYERS},
        "epochs": ${EPOCHS},
        "batch_size": ${BATCH_SIZE},
        "seq_len": ${SEQ_LEN},
        "lookback": ${LOOKBACK},
        "features": "advanced (19)",
    },
    "branch": "${GIT_BRANCH}",
    "commit": "${GIT_COMMIT}",
    "launched_at": "${LAUNCHED_AT}",
    "log_file": "train.log",
    "pid_file": "PID.txt",
}, indent=3))
PY

# --- Launch detached process ---
echo "[LAUNCH] Starting LSTM training..."
echo "[LAUNCH] Hidden=${HIDDEN_SIZE} Layers=${NUM_LAYERS} Epochs=${EPOCHS} Batch=${BATCH_SIZE} Advanced=19"
echo "[LAUNCH] Log: ${LOG_PATH}"

# nohup + disown so the process survives the parent shell exiting.
nohup "${PYTHON_EXE}" "${TRAIN_SCRIPT}" \
    --data-dir       "${DATA_DIR}" \
    --symbol         "${SYMBOL}" \
    --start          "${START_DATE}" \
    --end            "${END_DATE}" \
    --hidden-size    "${HIDDEN_SIZE}" \
    --num-layers     "${NUM_LAYERS}" \
    --epochs         "${EPOCHS}" \
    --batch-size     "${BATCH_SIZE}" \
    --seq-len        "${SEQ_LEN}" \
    --lookback       "${LOOKBACK}" \
    --checkpoint-dir "${CKPT_DIR}" \
    --advanced \
    > "${LOG_PATH}" 2> "${ERR_PATH}" &

PID=$!
echo "${PID}" > "${PID_PATH}"

echo "[LAUNCH] PID: ${PID} -> ${PID_PATH}"
echo ""
echo "Monitor log:    tail -f ${LOG_PATH}"
echo "GPU monitor:    nvidia-smi -i ${CUDA_VISIBLE_DEVICES} -l 5"
echo "Check status:   ps -p \$(cat ${PID_PATH})"
echo "Stop:           kill \$(cat ${PID_PATH})"