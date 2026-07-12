#!/bin/bash
# Cross-platform setup for SmartContracts series
# Works on: Mac (native), Linux (native), Windows (run inside WSL)
#
# Usage:
#   Mac/Linux:  bash scripts/setup.sh
#   Windows:    wsl -d Ubuntu -- bash /mnt/d/.../SmartContracts/scripts/setup.sh
#
# Installs: Foundry, Python venv, all dependencies, Jupyter kernel

set -e

VENV_PATH="$HOME/.smartcontracts-venv"
FOUNDRY_BIN="$HOME/.foundry/bin"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SC_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
KERNEL_NAME="smartcontracts"

# Detect OS
IS_WSL=false
IS_MAC=false
IS_LINUX=false

if [ -f /proc/sys/fs/binfmt_misc/WSLInterop ] 2>/dev/null; then
    IS_WSL=true
elif [ "$(uname)" = "Darwin" ]; then
    IS_MAC=true
else
    IS_LINUX=true
fi

echo "============================================================"
echo "SmartContracts Setup"
if $IS_WSL; then echo "  Platform: Windows (WSL)"
elif $IS_MAC; then echo "  Platform: macOS"
else echo "  Platform: Linux"; fi
echo "============================================================"
echo ""

# ================================================================
# Step 1: System dependencies
# ================================================================
echo "[1/6] System dependencies..."
if $IS_MAC; then
    # macOS: use Homebrew
    if ! command -v brew &>/dev/null; then
        echo "  Installing Homebrew..."
        /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    fi
    brew install python3 curl git 2>/dev/null || true
elif $IS_WSL || $IS_LINUX; then
    sudo apt update -qq
    sudo apt install -y -qq python3-pip python3-venv curl git build-essential
fi
echo "  [OK]"

# ================================================================
# Step 2: Install Foundry
# ================================================================
echo "[2/6] Installing Foundry (forge, cast, anvil)..."
export PATH="$FOUNDRY_BIN:$PATH"

if command -v forge &>/dev/null; then
    echo "  Foundry already installed: $(forge --version 2>/dev/null | head -1)"
else
    echo "  Downloading foundryup..."
    curl -L https://foundry.paradigm.xyz | bash
    echo "  Running foundryup..."
    "$FOUNDRY_BIN/foundryup"
fi

# Verify
for tool in forge cast anvil; do
    if [ -f "$FOUNDRY_BIN/$tool" ] || command -v "$tool" &>/dev/null; then
        echo "  [OK] $tool"
    else
        echo "  [FAIL] $tool not found"
        exit 1
    fi
done

# ================================================================
# Step 3: Python virtual environment
# ================================================================
echo "[3/6] Python venv at $VENV_PATH..."
if [ -d "$VENV_PATH" ]; then
    echo "  Existing venv found, updating..."
else
    python3 -m venv "$VENV_PATH"
    echo "  Created."
fi

source "$VENV_PATH/bin/activate"
pip install --upgrade pip --quiet

# ================================================================
# Step 4: Python packages
# ================================================================
echo "[4/6] Installing Python packages..."

# Read requirements.txt (skip comments and empty lines)
REQ_FILE="$SC_DIR/requirements.txt"
if [ -f "$REQ_FILE" ]; then
    pip install --quiet -r "$REQ_FILE"
    echo "  [OK] requirements.txt installed"
else
    echo "  [WARN] requirements.txt not found, installing manually..."
    pip install --quiet \
        "web3>=7.0" "py-solc-x>=1.1" "python-dotenv>=1.0" "requests>=2.28" \
        "pycryptodome>=3.20" "py_ecc>=7.0" "phe>=1.5" "tenseal>=0.3" \
        "mpyc>=0.10" "xrpl-py>=3.0" "python-bitcoinlib>=0.12" "vyper>=0.4" \
        "matplotlib>=3.5" "tabulate>=0.9" "openai>=1.0"
fi

pip install --quiet ipykernel

# Optional Linux-only packages
echo "  Optional packages..."
pip install --quiet "concrete-python>=2.0" 2>/dev/null \
    && echo "  [OK] concrete-python" \
    || echo "  [SKIP] concrete-python (Python 3.10-3.12 Linux only)"

# Install solc 0.8.28
echo "  Installing solc compiler..."
python3 -c "
import solcx
installed = [str(v) for v in solcx.get_installed_solc_versions()]
if '0.8.28' not in installed:
    solcx.install_solc('0.8.28')
    print('  [OK] solc 0.8.28 installed')
else:
    print('  [OK] solc 0.8.28 already present')
"

# Install Foundry libraries (OpenZeppelin, account-abstraction)
echo "  Installing Foundry libraries..."
FOUNDRY_LIB="$SC_DIR/foundry-lib"
if [ -d "$FOUNDRY_LIB/lib/openzeppelin-contracts" ]; then
    echo "  [OK] OpenZeppelin already installed"
else
    cd "$FOUNDRY_LIB"
    forge install --no-git openzeppelin/openzeppelin-contracts 2>&1 | tail -1
    echo "  [OK] OpenZeppelin installed"
fi
if [ -d "$FOUNDRY_LIB/lib/account-abstraction" ]; then
    echo "  [OK] account-abstraction already installed"
else
    cd "$FOUNDRY_LIB"
    forge install --no-git eth-infinitism/account-abstraction 2>&1 | tail -1
    echo "  [OK] account-abstraction installed"
fi
cd "$SC_DIR"

# Verify key packages
echo ""
echo "  Package verification:"
python3 -c "
packages = [
    ('web3', 'web3'), ('solcx', 'py-solc-x'), ('Crypto', 'pycryptodome'),
    ('py_ecc', 'py_ecc'), ('phe', 'phe'), ('tenseal', 'tenseal'),
    ('mpyc', 'mpyc'), ('xrpl', 'xrpl-py'), ('bitcoin', 'python-bitcoinlib'),
    ('vyper', 'vyper'), ('openai', 'openai'),
]
ok = 0
for imp, name in packages:
    try:
        __import__(imp)
        print(f'  [OK] {name}')
        ok += 1
    except ImportError:
        print(f'  [MISSING] {name}')
print(f'  {ok}/{len(packages)} packages OK')
"

# ================================================================
# Step 5: Register Jupyter kernel
# ================================================================
echo ""
echo "[5/6] Registering Jupyter kernel '$KERNEL_NAME'..."

if $IS_WSL; then
    # On WSL: create wrapper script + Windows-side kernel registration
    WRAPPER_PATH="$HOME/.smartcontracts-kernel-wrapper.sh"

    cat > "$WRAPPER_PATH" << 'WRAPPER_SCRIPT'
#!/bin/bash
# Kernel wrapper: handles Windows -> WSL path conversion for connection files
ARGS=()
NEXT_IS_CONN=false

for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        # Tilde expansion
        if [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
        fi
        # Backslashes stripped by WSL shell
        if [[ "$arg" =~ ^[a-zA-Z]:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$ ]]; then
            USERNAME="${BASH_REMATCH[1]}"
            FILENAME="${BASH_REMATCH[2]}"
            arg="${arg:0:1}:\\Users\\${USERNAME}\\AppData\\Roaming\\jupyter\\runtime\\${FILENAME}"
        fi
        # Convert Windows path to Linux
        if [[ "$arg" == *":"* ]] || [[ "$arg" == *"\\"* ]]; then
            LINUX_PATH=$(wslpath -u "$arg" 2>/dev/null)
            [ -n "$LINUX_PATH" ] && arg="$LINUX_PATH"
        fi
        ARGS+=("$arg")
        NEXT_IS_CONN=false
    elif [ "$arg" = "-f" ]; then
        ARGS+=("$arg")
        NEXT_IS_CONN=true
    else
        ARGS+=("$arg")
    fi
done
WRAPPER_SCRIPT

    # Append PATH setup and exec (with actual paths)
    cat >> "$WRAPPER_PATH" << EOF
export PATH="$FOUNDRY_BIN:$VENV_PATH/bin:\$PATH"
exec $VENV_PATH/bin/python3 -m ipykernel_launcher "\${ARGS[@]}"
EOF
    chmod +x "$WRAPPER_PATH"

    # Get WSL username for Windows-side kernel registration
    WSL_USER=$(whoami)

    # Create kernel.json for Windows
    KERNEL_DIR_WIN=""
    if command -v cmd.exe &>/dev/null; then
        APPDATA=$(cmd.exe /c "echo %APPDATA%" 2>/dev/null | tr -d "\r\n" | sed 's/\\/\//g')
        if [ -n "$APPDATA" ]; then
            KERNEL_DIR_LINUX=$(wslpath -u "$APPDATA/jupyter/kernels/$KERNEL_NAME" 2>/dev/null)
            mkdir -p "$KERNEL_DIR_LINUX"
            cat > "$KERNEL_DIR_LINUX/kernel.json" << KJSON
{
  "argv": [
    "wsl.exe", "-d", "Ubuntu", "--",
    "bash", "/home/$WSL_USER/.smartcontracts-kernel-wrapper.sh",
    "-f", "{connection_file}"
  ],
  "display_name": "Python (SmartContracts + Foundry)",
  "language": "python",
  "metadata": {"debugger": false}
}
KJSON
            echo "  [OK] Kernel registered (Windows: $KERNEL_DIR_LINUX)"
        fi
    fi

    if [ -z "$KERNEL_DIR_WIN" ] && [ -z "$KERNEL_DIR_LINUX" ]; then
        echo "  [INFO] Auto-registration failed. Run in PowerShell:"
        echo "    powershell -File $SC_DIR/scripts/setup_wsl_kernel.ps1"
    fi

else
    # Mac/Linux: standard kernel registration
    python3 -m ipykernel install \
        --user \
        --name "$KERNEL_NAME" \
        --display-name "Python (SmartContracts + Foundry)" \
        --env PATH "$FOUNDRY_BIN:$VENV_PATH/bin:$PATH"
    echo "  [OK] Kernel registered natively"
fi

# ================================================================
# Step 6: Summary
# ================================================================
echo ""
echo "[6/6] Setup complete!"
echo ""
echo "============================================================"
echo "Summary"
echo "============================================================"
echo "  Foundry  : $FOUNDRY_BIN"
echo "  Venv     : $VENV_PATH"
echo "  Kernel   : $KERNEL_NAME"
if $IS_WSL; then
    echo "  Wrapper  : $HOME/.smartcontracts-kernel-wrapper.sh"
fi
echo ""
echo "Quick start:"
echo "  # Start local blockchain"
if $IS_WSL; then
    echo "  wsl -d Ubuntu -- bash -c 'export PATH=\$HOME/.foundry/bin:\$PATH && anvil --host 0.0.0.0'"
else
    echo "  anvil"
fi
echo ""
echo "  # Open notebooks in VS Code/Jupyter"
echo "  # Select kernel: Python (SmartContracts + Foundry)"
echo ""
