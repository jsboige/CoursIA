#!/usr/bin/env bash
# run_m7_overnight_sweep.sh
# Multiscale GNN M7 robustness sweep (bash idiomatique, Mac/Linux companion).
# Runs 4 sweeps sequentially, mirroring run_m7_overnight_sweep.ps1.
#
# Usage:
#   ./run_m7_overnight_sweep.sh            # Full sweep
#
# Notes:
# - This is a long-running overnight batch; each run can take hours.
# - Stop with Ctrl+C; partial results persist under results/m7_robustness_sweep/.
# - The Python side reads --skip-remote to avoid network calls during the sweep.

set -uo pipefail  # NOTE: -e removed because we want to continue after a sub-run fails (matches PowerShell $ErrorActionPreference="Continue").

# --- Environment ---
export CUDA_VISIBLE_DEVICES=2
export PYTHONUNBUFFERED=1

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# scripts/run_m7_overnight_sweep.sh -> ../../  is ML-Training-Pipeline root
ROOT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OUT_DIR="${ROOT_DIR}/results/m7_robustness_sweep"
LOG_DIR="${OUT_DIR}"

CONDA_ENV="coursia-ml-training"
if [[ -n "${CONDA_PREFIX:-}" ]]; then
    PYTHON_EXE="${CONDA_PREFIX}/bin/python"
elif command -v conda >/dev/null 2>&1; then
    PYTHON_EXE="$(conda env list 2>/dev/null | awk -v env="${CONDA_ENV}" '$1==env {print $NF}')/bin/python"
else
    echo "ERROR: conda not found and CONDA_PREFIX unset." >&2
    exit 1
fi

if [[ ! -x "${PYTHON_EXE}" ]]; then
    echo "ERROR: Python not found: ${PYTHON_EXE}" >&2
    exit 1
fi

TRAIN_SCRIPT="${ROOT_DIR}/scripts/train_multiscale_gnn.py"
if [[ ! -f "${TRAIN_SCRIPT}" ]]; then
    echo "ERROR: Train script not found: ${TRAIN_SCRIPT}" >&2
    exit 1
fi

mkdir -p "${OUT_DIR}"

stamp() { date -u +%Y%m%d_%H%M%S; }
log_stamp() { date -u +%Y-%m-%dT%H:%M:%SZ; }

# Run-Sweep <name> <args...>
# Mirrors the PowerShell Run-Sweep function. Each sweep is best-effort:
# the overall batch continues even if a single sweep fails (matches the
# original $ErrorActionPreference="Continue" semantics).
run_sweep() {
    local name="$1"; shift
    local s; s="$(stamp)"
    local log="${LOG_DIR}/${name}.log"
    local json="${OUT_DIR}/${name}.json"
    local overall="${LOG_DIR}/_overall.log"
    echo "[$(log_stamp)] START ${name}" >> "${overall}"

    # Tee output to log + stdout; capture exit code separately.
    set +e
    "${PYTHON_EXE}" "${TRAIN_SCRIPT}" "$@" --out-json "${json}" 2>&1 | tee "${log}"
    local exit_code=${PIPESTATUS[0]}
    set -uo pipefail

    echo "[$(log_stamp)] END   ${name} exit=${exit_code}" >> "${overall}"
}

# Run 1 — extended horizons (10 instead of 6), 8 seeds, 5 splits, 1000 epochs
run_sweep "run1_ext_horizons" \
    --horizons 1 2 3 4 5 7 10 14 21 28 \
    --seeds 0 1 7 42 99 777 1024 2048 \
    --n-splits 5 \
    --epochs 1000 \
    --coins BTC-USD ETH-USD \
    --skip-remote

# Run 2 — finer walk-forward (7 splits)
run_sweep "run2_more_splits" \
    --horizons 1 3 5 10 20 30 \
    --seeds 0 1 7 42 99 777 1024 2048 \
    --n-splits 7 \
    --epochs 1000 \
    --coins BTC-USD ETH-USD \
    --skip-remote

# Run 3 — extended seed bench (12 seeds)
run_sweep "run3_more_seeds" \
    --horizons 1 3 5 10 20 30 \
    --seeds 0 1 7 11 13 17 19 42 99 777 1024 2048 \
    --n-splits 5 \
    --epochs 1000 \
    --coins BTC-USD ETH-USD \
    --skip-remote

# Run 4 — longer training (2000 epochs) — undertrain check
run_sweep "run4_longer_training" \
    --horizons 1 3 5 10 20 30 \
    --seeds 0 1 7 42 99 777 1024 2048 \
    --n-splits 5 \
    --epochs 2000 \
    --coins BTC-USD ETH-USD \
    --skip-remote

echo "[$(log_stamp)] ALL DONE" >> "${LOG_DIR}/_overall.log"
echo "All sweeps complete. See ${LOG_DIR}/_overall.log for status."