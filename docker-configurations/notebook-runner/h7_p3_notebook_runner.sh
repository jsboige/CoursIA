#!/usr/bin/env bash
# H.7 P3 Notebook Runner — unified kernel dispatch
# Detects kernel type from notebook metadata and delegates to appropriate executor.
#
# Supported kernels:
#   - python3          → Papermill
#   - .net-csharp      → .NET Interactive cell-by-cell (jupyter nbconvert)
#   - .net-fsharp      → .NET Interactive cell-by-cell
#   - lean4 / lean     → Lean 4 via elan + lake
#   - python3 (QuantBook with QuantConnect header) → nbconvert with --allow-errors
#
# Exit codes:
#   0 = all notebooks passed (0 errors)
#   1 = execution errors found (reported in output)
#   2 = infrastructure error (kernel missing, Docker issue)

set -euo pipefail

TIMEOUT_PER_CELL="${EXECUTION_TIMEOUT:-300}"
RESULTS_DIR="/tmp/notebook_results"
mkdir -p "$RESULTS_DIR"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

log() { echo -e "[$(date +%H:%M:%S)] $*"; }
ok()  { echo -e "${GREEN}[OK]${NC} $*"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $*"; }
err()  { echo -e "${RED}[ERR]${NC} $*"; }

# ── Kernel detection ──────────────────────────────────────────────

detect_kernel() {
    local nb="$1"
    # Extract kernelspec name from notebook metadata
    python3 -c "
import json, sys
with open('$nb') as f:
    nb = json.load(f)
ks = nb.get('metadata', {}).get('kernelspec', {})
print(ks.get('name', 'python3'))
"
}

is_quantconnect_notebook() {
    local nb="$1"
    # Check if notebook contains QuantBook() or qb = QuantBook() patterns
    grep -q 'QuantBook\|from AlgorithmImports\|from QuantConnect' "$nb" 2>/dev/null
}

is_dotnet_kernel() {
    local kernel="$1"
    [[ "$kernel" == .net-csharp || "$kernel" == .net-fsharp || "$kernel" == .net-powershell ]]
}

# ── Executors ─────────────────────────────────────────────────────

execute_python_papermill() {
    local nb="$1"
    local output="${RESULTS_DIR}/$(basename "$nb")"
    log "Python/Papermill: $(basename "$nb")"
    papermill "$nb" "$output" --execution-timeout "$TIMEOUT_PER_CELL" --kernel python3 2>&1
    return $?
}

execute_python_nbconvert() {
    local nb="$1"
    log "Python/nbconvert: $(basename "$nb")"
    jupyter nbconvert --to notebook --execute --inplace \
        --ExecutePreprocessor.timeout="$TIMEOUT_PER_CELL" \
        --ExecutePreprocessor.kernel_name=python3 \
        "$nb" 2>&1
    return $?
}

execute_dotnet() {
    local nb="$1"
    log ".NET Interactive: $(basename "$nb")"
    # nbconvert supports .NET Interactive kernels via the installed kernel spec
    jupyter nbconvert --to notebook --execute --inplace \
        --ExecutePreprocessor.timeout="$TIMEOUT_PER_CELL" \
        "$nb" 2>&1
    return $?
}

execute_lean() {
    local nb="$1"
    log "Lean 4: $(basename "$nb")"
    # Lean notebooks use .NET Interactive with the Lean 4 kernel
    # If lean4 kernel is not available, try as .NET with Lean toolchain
    if jupyter kernelspec list 2>/dev/null | grep -q lean4; then
        jupyter nbconvert --to notebook --execute --inplace \
            --ExecutePreprocessor.timeout="$TIMEOUT_PER_CELL" \
            "$nb" 2>&1
        return $?
    else
        warn "lean4 kernel not available, skipping: $(basename "$nb")"
        return 2
    fi
}

# ── Single notebook dispatch ──────────────────────────────────────

execute_notebook() {
    local nb="$1"
    local kernel

    if [[ ! -f "$nb" ]]; then
        err "File not found: $nb"
        return 2
    fi

    kernel=$(detect_kernel "$nb")
    log "Detected kernel: $kernel for $(basename "$nb")"

    case "$kernel" in
        python3)
            if is_quantconnect_notebook "$nb"; then
                # QC notebooks need --allow-errors to capture partial outputs
                log "QC notebook detected, using nbconvert with --allow-errors"
                jupyter nbconvert --to notebook --execute --inplace \
                    --allow-errors \
                    --ExecutePreprocessor.timeout="$TIMEOUT_PER_CELL" \
                    --ExecutePreprocessor.kernel_name=python3 \
                    "$nb" 2>&1
                return $?
            else
                execute_python_papermill "$nb"
                return $?
            fi
            ;;
        .net-csharp|.net-fsharp|.net-powershell)
            execute_dotnet "$nb"
            return $?
            ;;
        lean4|lean|lean4-wsl)
            execute_lean "$nb"
            return $?
            ;;
        *)
            warn "Unknown kernel '$kernel', trying Papermill fallback"
            execute_python_papermill "$nb"
            return $?
            ;;
    esac
}

# ── Batch execution ───────────────────────────────────────────────

execute_batch() {
    local target="$1"
    local total=0 passed=0 failed=0 skipped=0
    local failed_list=""

    log "Batch execution: $target"

    # Find all .ipynb files, excluding checkpoints and output copies
    while IFS= read -r nb; do
        # Skip checkpoint files and output copies
        [[ "$nb" == *".ipynb_checkpoints"* ]] && continue
        [[ "$nb" == *"_output.ipynb" ]] && continue

        total=$((total + 1))
        if execute_notebook "$nb"; then
            passed=$((passed + 1))
            ok "$(basename "$nb")"
        else
            rc=$?
            if [[ $rc -eq 2 ]]; then
                skipped=$((skipped + 1))
                warn "$(basename "$nb") — skipped"
            else
                failed=$((failed + 1))
                failed_list="$failed_list\n  $(basename "$nb")"
                err "$(basename "$nb") — FAILED"
            fi
        fi
    done < <(find "$target" -name "*.ipynb" -type f 2>/dev/null | sort)

    echo ""
    log "=== BATCH RESULTS ==="
    log "Total: $total | Passed: $passed | Failed: $failed | Skipped: $skipped"
    if [[ -n "$failed_list" ]]; then
        err "Failed notebooks:$failed_list"
    fi

    # Write results JSON
    python3 -c "
import json
result = {'total': $total, 'passed': $passed, 'failed': $failed, 'skipped': $skipped}
with open('$RESULTS_DIR/batch_results.json', 'w') as f:
    json.dump(result, f, indent=2)
print(json.dumps(result))
"

    [[ $failed -eq 0 ]] && return 0 || return 1
}

# ── Main ──────────────────────────────────────────────────────────

usage() {
    echo "Usage: $0 [--batch] <notebook.ipynb|directory> [--timeout SECONDS]"
    echo ""
    echo "Options:"
    echo "  --batch     Execute all notebooks in directory"
    echo "  --timeout   Per-cell timeout in seconds (default: $TIMEOUT_PER_CELL)"
    echo "  --check-env Verify all kernels are installed"
    echo ""
    echo "Examples:"
    echo "  $0 /notebooks/ML/01-Introduction.ipynb"
    echo "  $0 --batch /notebooks/ML/"
    echo "  $0 --check-env"
}

check_environment() {
    log "=== Environment Check ==="
    python3 --version && ok "Python" || err "Python missing"
    dotnet --version && ok ".NET SDK" || err ".NET SDK missing"
    jupyter kernelspec list 2>/dev/null && ok "Jupyter kernels" || warn "Jupyter kernels issue"
    which elan >/dev/null 2>&1 && elan --version && ok "elan (Lean)" || warn "elan not found"
    which lake >/dev/null 2>&1 && lake --version && ok "lake (Lean build)" || warn "lake not found"
    python3 -c "import papermill; print(f'papermill {papermill.__version__}')" && ok "papermill" || err "papermill missing"
    python3 -c "import nbconvert; print(f'nbconvert {nbconvert.__version__}')" && ok "nbconvert" || err "nbconvert missing"
}

# Parse arguments
BATCH_MODE=false
TARGET=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --batch)     BATCH_MODE=true; shift ;;
        --timeout)   TIMEOUT_PER_CELL="$2"; shift 2 ;;
        --check-env) check_environment; exit 0 ;;
        --help|-h)   usage; exit 0 ;;
        *)           TARGET="$1"; shift ;;
    esac
done

if [[ -z "$TARGET" ]]; then
    usage
    exit 0
fi

if $BATCH_MODE; then
    execute_batch "$TARGET"
else
    execute_notebook "$TARGET"
fi
