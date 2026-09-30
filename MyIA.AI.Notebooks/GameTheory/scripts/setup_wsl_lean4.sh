#!/bin/bash
# Setup script for Lean 4 in WSL Ubuntu, or natively on Linux / macOS
# This script installs Lean 4 and lean4_jupyter for the GameTheory notebooks
#
# Usage: bash setup_wsl_lean4.sh
#
# Sous WSL, le kernel Jupyter `lean4-wsl` est enregistre cote Windows par
# setup_lean4_kernel.ps1. Hors WSL (Linux ou macOS natif), ce script
# l'enregistre lui-meme a l'etape 8 : les notebooks Lean declarent ce nom de
# kernel, qui doit donc exister sous ce nom sur toutes les plateformes.

set -e

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

# Version de Lean des lakes du depot, lue dans game_theory_lean/lean-toolchain
# (la version epinglee par la grande majorite des lakes). Le REPL doit etre
# compile avec cette version : un REPL d'une autre version ne charge pas les
# .olean des lakes, et la branche master du REPL suit la derniere toolchain.
LEAN_TOOLCHAIN="$(tr -d '[:space:]' < "$SCRIPT_DIR/../game_theory_lean/lean-toolchain")"
LEAN_TAG="${LEAN_TOOLCHAIN##*:}"

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

# 3. Install Lean 4 (version des lakes du depot)
log_info "Installation de Lean 4 ($LEAN_TOOLCHAIN, version des lakes du depot)..."
elan default "$LEAN_TOOLCHAIN"

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
# Fork du depot plutot que la version PyPI : le lean4_jupyter publie (0.0.2)
# echoue des la premiere cellule (sortie REPL vide, JSONDecodeError), et le
# fork lance le REPL directement avec le LEAN_PATH du lake, ce qui permet
# d'importer ses modules. Source de verite de l'URL et du tag :
# FORK_URL / FORK_TAG dans scripts/lean/setup_native_lean4_import.py.
LEAN4_JUPYTER_SPEC="lean4_jupyter @ git+https://github.com/jsboige/lean4_jupyter.git@v0.0.1-native-import"
log_info "Installation de lean4_jupyter (fork du depot) et dependances..."
pip install --upgrade pip
pip install ipykernel pyyaml "$LEAN4_JUPYTER_SPEC"

# 6. Install REPL (required by lean4_jupyter)
log_info "Installation du REPL Lean..."

REPL_DIR="$HOME/repl"
if [ -d "$REPL_DIR" ]; then
    log_warn "REPL existe deja. Mise a jour..."
    cd "$REPL_DIR"
else
    cd "$HOME"
    git clone https://github.com/leanprover-community/repl.git
    cd "$REPL_DIR"
fi
# Tag du REPL aligne sur la version des lakes (voir LEAN_TOOLCHAIN plus haut)
git fetch --tags --quiet || true
if ! git checkout --quiet "$LEAN_TAG"; then
    log_error "Tag $LEAN_TAG introuvable dans le depot du REPL"
    exit 1
fi
log_info "REPL au tag $LEAN_TAG"

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

# 7. Create the kernel wrapper script
log_info "Creation du wrapper pour le kernel..."

CANONICAL_WRAPPER="$SCRIPT_DIR/../../SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py"
if [ ! -f "$CANONICAL_WRAPPER" ]; then
    log_error "Source canonique du wrapper absente: $CANONICAL_WRAPPER"
    exit 1
fi

# Le wrapper est canonique : copie directe depuis le depot. Aucun heredoc
# mort ne doit reintroduire de logique obsolete ; le source est versionne
# et revu dans MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py.
cp "$CANONICAL_WRAPPER" "$HOME/.lean4-kernel-wrapper.py"
log_info "Wrapper canonique copie depuis le depot"

chmod +x "$HOME/.lean4-kernel-wrapper.py"
log_info "Wrapper cree: ~/.lean4-kernel-wrapper.py"

# 8. Hors WSL : enregistrer le kernel Jupyter `lean4-wsl` pointant vers le venv
#    et le wrapper (sous WSL, c'est setup_lean4_kernel.ps1 qui l'enregistre cote Windows)
IS_WSL=0
if grep -qiE 'microsoft|wsl' /proc/version 2>/dev/null; then
    IS_WSL=1
fi
if [ "$IS_WSL" -eq 0 ]; then
    log_info "Plateforme native (hors WSL) : enregistrement du kernel lean4-wsl..."
    KERNEL_SRC="$(mktemp -d)"
    cat > "$KERNEL_SRC/kernel.json" <<KERNEL_EOF
{
  "argv": [
    "$VENV_PATH/bin/python3",
    "$HOME/.lean4-kernel-wrapper.py",
    "-f", "{connection_file}"
  ],
  "display_name": "Lean 4",
  "language": "lean4"
}
KERNEL_EOF
    jupyter kernelspec install --user --name lean4-wsl "$KERNEL_SRC"
    rm -rf "$KERNEL_SRC"
    log_info "Kernel lean4-wsl enregistre pour l'utilisateur courant"
fi

# 9. Verify installation
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
if [ "$IS_WSL" -eq 1 ]; then
    echo "Etape suivante: Executez le script PowerShell Windows:"
    echo "  cd C:\\dev\\CoursIA\\MyIA.AI.Notebooks\\GameTheory\\scripts"
    echo "  .\\setup_lean4_kernel.ps1"
    echo ""
    echo "Puis redemarrez VSCode et selectionnez le kernel 'Lean 4 (WSL)'"
else
    echo "Kernel 'Lean 4' (nom lean4-wsl) enregistre : ouvrez un notebook Lean"
    echo "depuis son lake (repertoire contenant lakefile.lean ou lakefile.toml)."
    echo "Pour un lake qui depend de Mathlib : 'lake exe cache get' dans ce lake."
fi
echo ""
