#!/bin/bash
# Setup script for SmartContracts WSL environment
# Run inside WSL Ubuntu: bash setup_wsl_smartcontracts.sh
#
# Installs:
# - Foundry (forge, cast, anvil) for Solidity compilation and testing
# - Python venv with all SC dependencies (including Linux-only packages)
# - Jupyter kernel wrapper for Windows <-> WSL path conversion

set -e

VENV_PATH="$HOME/.smartcontracts-venv"
WRAPPER_PATH="$HOME/.smartcontracts-kernel-wrapper.sh"
FOUNDRY_BIN="$HOME/.foundry/bin"

echo "============================================================"
echo "SmartContracts WSL Setup"
echo "============================================================"
echo ""

# Check if running in WSL
if [ ! -f /proc/sys/fs/binfmt_misc/WSLInterop ]; then
    echo "ERROR: This script must be run inside WSL"
    exit 1
fi

# ================================================================
# Step 1: System dependencies
# ================================================================
echo "[1/6] Installing system dependencies..."
sudo apt update -qq
sudo apt install -y -qq python3-pip python3-venv curl git build-essential

# ================================================================
# Step 2: Install Foundry
# ================================================================
echo "[2/6] Installing Foundry (forge, cast, anvil)..."
if command -v forge &> /dev/null; then
    echo "  Foundry already installed"
    forge --version
else
    echo "  Downloading foundryup..."
    curl -L https://foundry.paradigm.xyz | bash
    # Source the new PATH
    export PATH="$FOUNDRY_BIN:$PATH"
    echo "  Running foundryup..."
    "$FOUNDRY_BIN/foundryup"
fi

# Verify Foundry
echo "  Verifying Foundry tools..."
for tool in forge cast anvil; do
    if command -v "$tool" &> /dev/null || [ -f "$FOUNDRY_BIN/$tool" ]; then
        VERSION=$("$FOUNDRY_BIN/$tool" --version 2>/dev/null || $tool --version 2>/dev/null)
        echo "  [OK] $tool: $VERSION"
    else
        echo "  [FAIL] $tool not found"
    fi
done

# ================================================================
# Step 3: Create Python virtual environment
# ================================================================
echo "[3/6] Creating Python virtual environment at $VENV_PATH..."
if [ -d "$VENV_PATH" ]; then
    echo "  Virtual environment already exists, updating..."
else
    python3 -m venv "$VENV_PATH"
fi

source "$VENV_PATH/bin/activate"
pip install --upgrade pip --quiet

# ================================================================
# Step 4: Install Python packages
# ================================================================
echo "[4/6] Installing Python packages..."

# Core packages (same as requirements.txt)
pip install --quiet \
    "web3>=7.0" \
    "py-solc-x>=1.1" \
    "python-dotenv>=1.0" \
    "pycryptodome>=3.20" \
    "py_ecc>=7.0" \
    "phe>=1.5" \
    "tenseal>=0.3" \
    "mpyc>=0.10" \
    "xrpl-py>=3.0" \
    "python-bitcoinlib>=0.12" \
    "vyper>=0.4" \
    "matplotlib>=3.5" \
    "tabulate>=0.9" \
    ipykernel

# Linux-only packages
echo "  Installing Linux-only packages..."
pip install --quiet "concrete-python>=2.0" 2>/dev/null && echo "  [OK] concrete-python" || echo "  [SKIP] concrete-python (may need specific Python version)"

# electionguard has pydantic<2 conflict - install separately and check
echo "  Attempting electionguard (may conflict with pydantic)..."
pip install --quiet "electionguard>=1.4" 2>/dev/null && echo "  [OK] electionguard" || echo "  [SKIP] electionguard (pydantic conflict)"

# Install solc compiler
echo "  Installing Solidity compiler (solc 0.8.28)..."
python3 -c "
import solcx
try:
    installed = [str(v) for v in solcx.get_installed_solc_versions()]
    if '0.8.28' not in installed:
        solcx.install_solc('0.8.28')
        print('  [OK] solc 0.8.28 installed')
    else:
        print('  [OK] solc 0.8.28 already installed')
except Exception as e:
    print(f'  [FAIL] solc: {e}')
"

# Verify key imports
echo ""
echo "  Verifying packages..."
python3 -c "
packages = [
    ('web3', 'web3'), ('solcx', 'py-solc-x'), ('Crypto', 'pycryptodome'),
    ('py_ecc', 'py_ecc'), ('phe', 'phe'), ('tenseal', 'tenseal'),
    ('mpyc', 'mpyc'), ('xrpl', 'xrpl-py'), ('bitcoin', 'python-bitcoinlib'),
    ('vyper', 'vyper'),
]
for imp, name in packages:
    try:
        __import__(imp)
        print(f'  [OK] {name}')
    except ImportError:
        print(f'  [MISSING] {name}')

# Optional
for imp, name in [('concrete', 'concrete-python'), ('electionguard', 'electionguard')]:
    try:
        __import__(imp)
        print(f'  [OK] {name} (optional)')
    except ImportError:
        print(f'  [N/A] {name} (optional, not critical)')
"

# ================================================================
# Step 5: Create kernel wrapper script
# ================================================================
echo ""
echo "[5/6] Creating kernel wrapper script..."
cat > "$WRAPPER_PATH" << 'WRAPPER_SCRIPT'
#!/bin/bash
# Kernel wrapper for SmartContracts WSL
# Handles Windows path conversion for Jupyter connection files
#
# Path formats received from Windows:
#   1. Tilde: ~\AppData\Roaming\jupyter\runtime\kernel-xxx.json
#   2. Mangled (backslashes eaten): c:Users<user>AppDataRoamingjupyterruntimekernel-xxx.json
#   3. Standard: C:\Users\...\kernel-xxx.json

LOGFILE="/tmp/smartcontracts-kernel-wrapper.log"
echo "=== SmartContracts kernel wrapper started ===" > "$LOGFILE"
echo "Args: $@" >> "$LOGFILE"

ARGS=()
NEXT_IS_CONN=false

for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        echo "Original path: $arg" >> "$LOGFILE"

        # Case 1: Tilde notation
        if [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
            echo "After tilde expansion: $arg" >> "$LOGFILE"
        fi

        # Case 2: Backslashes stripped by shell
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

WRAPPER_SCRIPT

# Add the exec line with actual venv path
echo "export PATH=\"$FOUNDRY_BIN:$VENV_PATH/bin:\$PATH\"" >> "$WRAPPER_PATH"
echo "cd ~" >> "$WRAPPER_PATH"
echo "exec $VENV_PATH/bin/python3 -m ipykernel_launcher \"\${ARGS[@]}\"" >> "$WRAPPER_PATH"

chmod +x "$WRAPPER_PATH"
bash -n "$WRAPPER_PATH" && echo "  [OK] Wrapper script created at $WRAPPER_PATH"

# ================================================================
# Step 6: Summary
# ================================================================
echo ""
echo "[6/6] Setup complete!"
echo ""
echo "============================================================"
echo "Summary"
echo "============================================================"
echo ""
echo "  Foundry : $FOUNDRY_BIN"
echo "  Venv    : $VENV_PATH"
echo "  Wrapper : $WRAPPER_PATH"
echo ""
echo "=== Next Steps (run in PowerShell on Windows) ==="
echo ""
SCRIPT_WIN_PATH=$(wslpath -w "$(dirname "$0")" 2>/dev/null || echo "(run from SmartContracts/scripts/)")
echo "  cd $SCRIPT_WIN_PATH"
echo "  .\\setup_wsl_kernel.ps1"
echo ""
echo "Or test anvil directly:"
echo "  wsl -d Ubuntu -- bash -c 'source ~/.smartcontracts-venv/bin/activate && anvil'"
echo ""
