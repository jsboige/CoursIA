#!/bin/bash
# Setup script for Lean 4 in WSL Ubuntu
# This script installs Lean 4 and lean4_jupyter for the GameTheory notebooks
#
# Usage: bash setup_wsl_lean4.sh

set -e

echo "=============================================="
echo "   INSTALLATION DE LEAN 4 DANS WSL"
echo "=============================================="
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() { echo -e "${GREEN}[INFO]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

# 1. Check prerequisites
log_info "Verification des prerequis..."

if ! command -v python3 &> /dev/null; then
    log_error "Python3 n'est pas installe. Installez-le d'abord:"
    echo "  sudo apt update && sudo apt install -y python3 python3-pip python3-venv"
    exit 1
fi

if ! command -v git &> /dev/null; then
    log_info "Installation de git..."
    sudo apt update && sudo apt install -y git
fi

# 2. Install elan (Lean version manager)
log_info "Installation de elan (gestionnaire de versions Lean)..."

if [ -d "$HOME/.elan" ]; then
    log_warn "elan est deja installe. Mise a jour..."
    source "$HOME/.elan/env"
    elan self update || true
else
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
    source "$HOME/.elan/env"
fi

# Add to .bashrc if not already there
if ! grep -q "elan/env" ~/.bashrc 2>/dev/null; then
    echo 'source ~/.elan/env' >> ~/.bashrc
    log_info "elan ajoute au .bashrc"
fi

# 3. Install Lean 4 stable
log_info "Installation de Lean 4 (version stable)..."
elan default leanprover/lean4:stable

# Verify installation
LEAN_VERSION=$(lean --version)
log_info "Lean installe: $LEAN_VERSION"

# 4. Create Python virtual environment for lean4_jupyter
VENV_PATH="$HOME/.lean4-venv"
log_info "Creation de l'environnement Python: $VENV_PATH"

if [ -d "$VENV_PATH" ]; then
    log_warn "L'environnement existe deja. Mise a jour..."
else
    python3 -m venv "$VENV_PATH"
fi

source "$VENV_PATH/bin/activate"

# 5. Install lean4_jupyter and dependencies
log_info "Installation de lean4_jupyter et dependances..."
pip install --upgrade pip
pip install lean4_jupyter ipykernel pyyaml

# 6. Install REPL (required by lean4_jupyter)
log_info "Installation du REPL Lean..."

REPL_DIR="$HOME/repl"
if [ -d "$REPL_DIR" ]; then
    log_warn "REPL existe deja. Mise a jour..."
    cd "$REPL_DIR"
    git pull || true
else
    cd "$HOME"
    git clone https://github.com/leanprover-community/repl.git
    cd "$REPL_DIR"
fi

# Build REPL
log_info "Compilation du REPL (peut prendre quelques minutes)..."
lake build

# Copy to PATH
REPL_BIN="$REPL_DIR/.lake/build/bin/repl"
if [ -f "$REPL_BIN" ]; then
    mkdir -p "$HOME/.elan/bin"
    cp "$REPL_BIN" "$HOME/.elan/bin/"
    log_info "REPL copie vers ~/.elan/bin/"
else
    log_error "REPL non trouve apres compilation"
    exit 1
fi

# 7. Install the kernel wrapper from the canonical repository source
# The versioned wrapper at SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py is
# the only source of truth. Reinstalling from this script must not regenerate
# a stale embedded template (#16567).
log_info "Installation du wrapper depuis la source canonique du depot..."

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
CANONICAL_WRAPPER="$SCRIPT_DIR/../../SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py"
if [ ! -f "$CANONICAL_WRAPPER" ]; then
    log_error "Source canonique du wrapper absente: $CANONICAL_WRAPPER"
    exit 1
fi

cp "$CANONICAL_WRAPPER" "$HOME/.lean4-kernel-wrapper.py"
chmod +x "$HOME/.lean4-kernel-wrapper.py"
log_info "Wrapper canonique copie depuis le depot: ~/.lean4-kernel-wrapper.py"

# 8. Verify installation
log_info "Verification de l'installation..."

echo ""
echo "--- Test REPL ---"
echo '{"cmd": "#eval 2 + 2"}' | repl

echo ""
echo "--- Test lean4_jupyter ---"
python3 -c "import lean4_jupyter; print(f'lean4_jupyter OK')"

echo ""
echo "=============================================="
echo -e "${GREEN}   INSTALLATION TERMINEE !${NC}"
echo "=============================================="
echo ""
echo "Etape suivante: Executez le script PowerShell Windows:"
echo "  cd C:\\dev\\CoursIA\\MyIA.AI.Notebooks\\GameTheory\\scripts"
echo "  .\\setup_lean4_kernel.ps1"
echo ""
echo "Puis redemarrez VSCode et selectionnez le kernel 'Lean 4 (WSL)'"
echo ""
