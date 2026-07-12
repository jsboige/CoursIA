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

# 7. Create the kernel wrapper script
log_info "Creation du wrapper pour le kernel..."

cat > "$HOME/.lean4-kernel-wrapper.py" << 'WRAPPER_EOF'
#!/usr/bin/env python3
# Lean 4 Jupyter Kernel Wrapper for WSL
# Converts Windows paths to WSL paths and launches lean4_jupyter kernel.
import sys
import subprocess
import os
import re


def convert_windows_path(path):
    """Convert Windows path to WSL path, handling various formats."""
    if not path:
        return path

    # Already a Unix path
    if path.startswith("/"):
        return path

    # Handle ~ shorthand (tilde followed by backslash or forward slash)
    if len(path) >= 2 and path[0] == "~" and path[1] in ["/", "\\"]:
        rest = path[2:].replace("\\", "/")
        # Try to find WSL username
        wsl_user = os.environ.get("USER", "jsboi")
        return "/mnt/c/Users/{}/{}".format(wsl_user, rest)

    # Check for mangled path (backslashes eaten by WSL shell)
    # Pattern: c:UsersjsboiAppDataRoamingjupyterruntimekernel-xxx.json
    if len(path) >= 2 and path[1] == ":":
        if "Users" in path and "\\" not in path and "/" not in path[2:]:
            match = re.match(r"([a-zA-Z]):Users([a-z0-9_]+)AppDataRoaming(.+)", path, re.IGNORECASE)
            if match:
                drive = match.group(1).lower()
                user = match.group(2)
                rest = match.group(3)
                rest = rest.replace("jupyter", "/jupyter").replace("runtime", "/runtime")
                rest = rest.replace("kernel-", "/kernel-")
                rest = rest.lstrip("/")
                return "/mnt/{}/Users/{}/AppData/Roaming/{}".format(drive, user, rest)

        # Standard Windows path - use wslpath
        try:
            result = subprocess.run(["wslpath", "-a", path], capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                return result.stdout.strip()
        except:
            pass
        # Fallback
        drive = path[0].lower()
        rest = path[2:].replace("\\", "/").lstrip("/")
        return "/mnt/{}/{}".format(drive, rest)

    return path


def main():
    log_file = os.path.expanduser("~/.lean4-wrapper.log")

    def log(msg):
        try:
            with open(log_file, "a") as f:
                f.write(msg + "\n")
        except:
            pass

    log("=== Lean4 Wrapper started ===")
    log("sys.argv: " + str(sys.argv))

    # Process arguments
    args = sys.argv[1:]
    for i, arg in enumerate(args):
        if arg == "-f" and i + 1 < len(args):
            original = args[i + 1]
            converted = convert_windows_path(args[i + 1])
            args[i + 1] = converted
            log("Original: " + str(original))
            log("Converted: " + str(converted))

            if os.path.exists(converted):
                log("Connection file EXISTS")
            else:
                log("Connection file MISSING - waiting...")
                import time
                for _ in range(20):
                    time.sleep(0.1)
                    if os.path.exists(converted):
                        log("Connection file appeared")
                        break
            break

    # Set up clean environment
    home = os.path.expanduser("~")
    os.environ["PATH"] = "{}/.elan/bin:{}/.lean4-venv/bin:/usr/local/bin:/usr/bin:/bin".format(home, home)
    os.chdir(home)
    log("PATH: " + os.environ["PATH"])
    log("Launching kernel with args: " + str(args))

    try:
        sys.argv = ["lean4_jupyter"] + args
        log("sys.argv set to: " + str(sys.argv))

        from ipykernel.kernelapp import IPKernelApp
        from lean4_jupyter.kernel import Lean4Kernel

        log("Starting kernel...")
        IPKernelApp.launch_instance(kernel_class=Lean4Kernel)
        log("Kernel exited normally")
    except SystemExit as e:
        log("SystemExit: " + str(e))
        sys.exit(e.code if e.code is not None else 0)
    except Exception as e:
        log("Exception: " + str(e))
        import traceback
        log(traceback.format_exc())
        sys.exit(1)


if __name__ == "__main__":
    main()
WRAPPER_EOF

chmod +x "$HOME/.lean4-kernel-wrapper.py"
log_info "Wrapper cree: ~/.lean4-kernel-wrapper.py"

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
