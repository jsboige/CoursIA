#!/bin/bash
# Setup script for Lean 4 on macOS / Linux (native, no WSL)
# Installs elan, Lean 4 stable, lean4_jupyter, and REPL
#
# Usage:
#   bash setup_lean4_native.sh          # Full install
#   bash setup_lean4_native.sh --check  # Verify only
#
# For WSL (Windows): use setup_wsl_lean4.sh instead.

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() { echo -e "${GREEN}[INFO]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }
log_step() { echo -e "\n${BLUE}[STEP]${NC} $1"; }

# Detect OS
OS_NAME="$(uname -s)"
case "$OS_NAME" in
    Darwin) log_info "macOS detected (native setup)";;
    Linux)
        # Check if running in WSL
        if grep -qi microsoft /proc/version 2>/dev/null; then
            log_warn "Running inside WSL. Consider using setup_wsl_lean4.sh for Windows integration."
        else
            log_info "Linux detected (native setup)"
        fi
        ;;
    *) log_error "Unsupported OS: $OS_NAME"; exit 1;;
esac

# Configurable paths
VENV_PATH="${LEAN4_VENV:-$HOME/.lean4-venv}"
REPL_DIR="$HOME/repl"
KERNEL_NAME="lean4"

# --check mode: verify only
if [ "$1" = "--check" ]; then
    echo "=============================================="
    echo "   LEAN 4 ENVIRONMENT CHECK"
    echo "=============================================="
    ERRORS=0

    # Check elan
    if command -v elan &>/dev/null; then
        log_info "elan: $(elan --version 2>&1 | head -1)"
    else
        log_error "elan: NOT FOUND"
        ERRORS=$((ERRORS + 1))
    fi

    # Check lean
    if command -v lean &>/dev/null; then
        log_info "lean: $(lean --version 2>&1 | head -1)"
    else
        log_error "lean: NOT FOUND"
        ERRORS=$((ERRORS + 1))
    fi

    # Check REPL
    if [ -f "$HOME/.elan/bin/repl" ]; then
        log_info "REPL: $HOME/.elan/bin/repl"
    else
        log_error "REPL: NOT FOUND"
        ERRORS=$((ERRORS + 1))
    fi

    # Check venv + lean4_jupyter
    if [ -d "$VENV_PATH" ]; then
        if "$VENV_PATH/bin/python3" -c "import lean4_jupyter" 2>/dev/null; then
            log_info "lean4_jupyter: OK ($VENV_PATH)"
        else
            log_error "lean4_jupyter: NOT INSTALLED in $VENV_PATH"
            ERRORS=$((ERRORS + 1))
        fi
    else
        log_error "venv: NOT FOUND at $VENV_PATH"
        ERRORS=$((ERRORS + 1))
    fi

    # Check Jupyter kernel
    if jupyter kernelspec list 2>/dev/null | grep -q "$KERNEL_NAME"; then
        log_info "Jupyter kernel '$KERNEL_NAME': registered"
    else
        log_warn "Jupyter kernel '$KERNEL_NAME': NOT registered (optional for papermill)"
    fi

    echo ""
    if [ "$ERRORS" -eq 0 ]; then
        log_info "All checks passed!"
        exit 0
    else
        log_error "$ERRORS issue(s) found. Run without --check to install."
        exit 1
    fi
fi

# Full installation
echo "=============================================="
echo "   LEAN 4 NATIVE INSTALLATION"
echo "   OS: $OS_NAME"
echo "=============================================="

# 1. Check prerequisites
log_step "Checking prerequisites..."

if ! command -v python3 &>/dev/null; then
    log_error "Python3 is not installed."
    if [ "$OS_NAME" = "Darwin" ]; then
        echo "  Install with: brew install python3"
    else
        echo "  Install with: sudo apt install -y python3 python3-pip python3-venv"
    fi
    exit 1
fi
log_info "Python3: $(python3 --version)"

if ! command -v git &>/dev/null; then
    log_info "Installing git..."
    if [ "$OS_NAME" = "Darwin" ]; then
        brew install git
    else
        sudo apt update && sudo apt install -y git
    fi
fi

# 2. Install elan (Lean version manager)
log_step "Installing elan (Lean version manager)..."

if [ -d "$HOME/.elan" ] && command -v elan &>/dev/null; then
    log_warn "elan already installed. Updating..."
    source "$HOME/.elan/env" 2>/dev/null || true
    elan self update || true
else
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
    source "$HOME/.elan/env"
fi

# Add to shell profile if not already there
for rcfile in "$HOME/.bashrc" "$HOME/.zshrc" "$HOME/.profile"; do
    if [ -f "$rcfile" ] && ! grep -q "elan/env" "$rcfile" 2>/dev/null; then
        echo 'source "$HOME/.elan/env" 2>/dev/null || true' >> "$rcfile"
        log_info "elan added to $(basename "$rcfile")"
    fi
done

# Make sure elan is in PATH for the rest of this script
export PATH="$HOME/.elan/bin:$PATH"

# 3. Install Lean 4 stable
log_step "Installing Lean 4 (stable)..."

elan default leanprover/lean4:stable
LEAN_VERSION="$(lean --version 2>&1 | head -1)"
log_info "Lean installed: $LEAN_VERSION"

# 4. Create Python virtual environment for lean4_jupyter
log_step "Creating Python venv: $VENV_PATH"

if [ -d "$VENV_PATH" ]; then
    log_warn "venv already exists at $VENV_PATH. Reusing."
else
    python3 -m venv "$VENV_PATH"
fi

# shellcheck disable=SC1090
source "$VENV_PATH/bin/activate"

# 5. Install lean4_jupyter and dependencies
log_step "Installing lean4_jupyter and dependencies..."

pip install --upgrade pip -q
pip install lean4_jupyter ipykernel pyyaml -q

# 6. Install REPL (required by lean4_jupyter)
log_step "Installing Lean REPL..."

if [ -d "$REPL_DIR" ]; then
    log_warn "REPL directory exists. Updating..."
    cd "$REPL_DIR"
    git pull || true
else
    cd "$HOME"
    git clone https://github.com/leanprover-community/repl.git
    cd "$REPL_DIR"
fi

log_info "Building REPL (may take a few minutes)..."
lake build

# Copy REPL to PATH
REPL_BIN="$REPL_DIR/.lake/build/bin/repl"
if [ -f "$REPL_BIN" ]; then
    mkdir -p "$HOME/.elan/bin"
    cp "$REPL_BIN" "$HOME/.elan/bin/"
    log_info "REPL copied to ~/.elan/bin/"
else
    log_error "REPL binary not found after build"
    exit 1
fi

# 7. Register Jupyter kernel (optional, for VSCode/Jupyter)
log_step "Registering Jupyter kernel..."

python3 -m ipykernel install --user --name "$KERNEL_NAME" --display-name "Lean 4 (Native)" 2>/dev/null && \
    log_info "Kernel 'Lean 4 (Native)' registered" || \
    log_warn "Kernel registration skipped (ipykernel may not be available)"

# 8. Verify installation
log_step "Verifying installation..."

echo ""
echo "--- Test REPL ---"
echo '{"cmd": "#eval 2 + 2"}' | "$HOME/.elan/bin/repl" 2>&1 | head -5

echo ""
echo "--- Test lean4_jupyter ---"
python3 -c "import lean4_jupyter; print('lean4_jupyter OK')"

echo ""
echo "=============================================="
echo -e "${GREEN}   INSTALLATION COMPLETE!${NC}"
echo "=============================================="
echo ""
echo "Installed:"
echo "  - elan (Lean version manager)"
echo "  - Lean 4: $LEAN_VERSION"
echo "  - REPL: $HOME/.elan/bin/repl"
echo "  - lean4_jupyter in $VENV_PATH"
echo ""
echo "Next steps:"
echo "  1. Restart VSCode / Jupyter"
echo "  2. Select kernel 'Lean 4 (Native)'"
echo "  3. Open GameTheory-1-Setup.ipynb"
echo ""
echo "Verify anytime: bash setup_lean4_native.sh --check"
