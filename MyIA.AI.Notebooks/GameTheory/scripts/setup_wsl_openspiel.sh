#!/bin/bash
# Setup script for GameTheory WSL environment
# Covers the entire GameTheory notebook series:
#   - OpenSpiel (game theory library)
#   - PySAT (SAT solving for social choice theorems)
#   - Standard scientific Python stack
#
# Run this script inside WSL Ubuntu:
#   bash setup_wsl_openspiel.sh
#
# After this script, run setup_wsl_kernel.ps1 on Windows
# to register the Jupyter kernel.

set -e

VENV_PATH="$HOME/.gametheory-venv"
WRAPPER_PATH="$HOME/.gametheory-kernel-wrapper.sh"

echo "=== GameTheory WSL Environment Setup ==="
echo "  Covers: OpenSpiel, PySAT, NashPy, scientific stack"
echo ""

# Check if running in WSL
if [ ! -f /proc/sys/fs/binfmt_misc/WSLInterop ]; then
    echo "ERROR: This script must be run inside WSL"
    exit 1
fi

# Step 1: Install system dependencies
echo "[1/5] Installing system dependencies..."
sudo apt update
sudo apt install -y python3-pip python3-venv python3-full

# Step 2: Create virtual environment
echo "[2/5] Creating virtual environment at $VENV_PATH..."
if [ -d "$VENV_PATH" ]; then
    echo "  Virtual environment already exists, reusing..."
else
    python3 -m venv "$VENV_PATH"
fi

# Step 3: Install packages (full GameTheory series)
echo "[3/5] Installing GameTheory dependencies..."
source "$VENV_PATH/bin/activate"
pip install --upgrade pip

# Core game theory
pip install open_spiel nashpy

# SAT solving (social choice theorems)
pip install python-sat

# Scientific stack
pip install numpy scipy matplotlib networkx seaborn pandas tqdm

# Jupyter kernel support
pip install ipykernel

# Verify key imports
echo "  Verifying installations..."
python3 -c "import pyspiel; print(f'  OpenSpiel OK: {len(pyspiel.registered_names())} games available')"
python3 -c "from pysat.solvers import Glucose3; print('  PySAT OK')"
python3 -c "import nashpy; print('  NashPy OK')"
python3 -c "import matplotlib; print(f'  matplotlib OK ({matplotlib.__version__})')"

# Step 4: Register ipykernel
echo "[4/5] Registering Jupyter kernel..."
python3 -m ipykernel install --user --name python3 \
    --display-name "Python 3 (WSL)" \
    --env PATH "$VENV_PATH/bin:/usr/local/bin:/usr/bin:/bin"
echo "  Kernel 'Python 3 (WSL)' registered"

# Step 5: Create wrapper script (for Windows Jupyter to connect)
echo "[5/5] Creating kernel wrapper script..."
cat > "$WRAPPER_PATH" << 'WRAPPER_SCRIPT'
#!/bin/bash
# Kernel wrapper for WSL - handles Windows path conversion
# Handles multiple path formats:
#   1. Tilde notation: ~\AppData\Roaming\jupyter\runtime\kernel-xxx.json
#   2. Stripped backslashes: c:UsersjsboiAppDataRoamingjupyterruntimekernel-xxx.json
#   3. Normal Windows paths: C:\Users\...\kernel-xxx.json

LOGFILE="/tmp/kernel-wrapper.log"
echo "=== Kernel wrapper started ===" > "$LOGFILE"
echo "Args: $@" >> "$LOGFILE"

ARGS=()
NEXT_IS_CONN=false

for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        echo "Original path: $arg" >> "$LOGFILE"

        # Case 1: Tilde notation (~\AppData\... or ~/AppData/...)
        if [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
            echo "After tilde expansion: $arg" >> "$LOGFILE"
        fi

        # Case 2: Backslashes were stripped by shell (c:UsersjsboiAppDataRoaming...)
        if [[ "$arg" =~ ^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$ ]]; then
            USERNAME="${BASH_REMATCH[1]}"
            FILENAME="${BASH_REMATCH[2]}"
            arg="C:\\Users\\${USERNAME}\\AppData\\Roaming\\jupyter\\runtime\\${FILENAME}"
            echo "Reconstructed path: $arg" >> "$LOGFILE"
        fi

        # Convert Windows path to Linux path
        if [[ "$arg" == *":"* ]] || [[ "$arg" == *"\\"* ]]; then
            LINUX_PATH=$(wslpath -u "$arg" 2>/dev/null)
            if [ -n "$LINUX_PATH" ]; then
                arg="$LINUX_PATH"
            fi
        fi

        echo "Final path: $arg" >> "$LOGFILE"
        ARGS+=("$arg")
        NEXT_IS_CONN=false
    elif [ "$arg" = "-f" ]; then
        ARGS+=("$arg")
        NEXT_IS_CONN=true
    else
        ARGS+=("$arg")
    fi
done

echo "Final args: ${ARGS[@]}" >> "$LOGFILE"
echo "Launching ipykernel..." >> "$LOGFILE"

# Run ipykernel
WRAPPER_SCRIPT

# Add the exec line with actual path (not variable)
echo "export PATH=\"$VENV_PATH/bin:\$PATH\"" >> "$WRAPPER_PATH"
echo "cd ~" >> "$WRAPPER_PATH"
echo "exec $VENV_PATH/bin/python3 -m ipykernel_launcher \"\${ARGS[@]}\"" >> "$WRAPPER_PATH"

chmod +x "$WRAPPER_PATH"

# Verify wrapper syntax
bash -n "$WRAPPER_PATH" && echo "  Wrapper script OK"

# Done
echo ""
echo "=== Setup complete! ==="
echo ""
echo "Installed packages:"
echo "  - open_spiel  (game theory library)"
echo "  - pysat       (SAT solving)"
echo "  - nashpy      (Nash equilibrium)"
echo "  - numpy, scipy, matplotlib, networkx, seaborn, pandas, tqdm"
echo "  - ipykernel   (Jupyter kernel support)"
echo ""
echo "Jupyter kernel: 'Python 3 (WSL)' (python3)"
echo ""
echo "=== Next Steps (run in PowerShell on Windows) ==="
echo ""
echo "  cd $(wslpath -w "$(dirname "$0")")"
echo "  .\\setup_wsl_kernel.ps1"
echo ""
