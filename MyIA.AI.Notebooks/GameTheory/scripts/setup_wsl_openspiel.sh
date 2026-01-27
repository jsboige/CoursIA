#!/bin/bash
# Setup script for OpenSpiel WSL kernel
# Run this script inside WSL Ubuntu

set -e

VENV_PATH="$HOME/.gametheory-venv"
WRAPPER_PATH="$HOME/.gametheory-kernel-wrapper.sh"

echo "=== OpenSpiel WSL Kernel Setup ==="
echo ""

# Check if running in WSL
if [ ! -f /proc/sys/fs/binfmt_misc/WSLInterop ]; then
    echo "ERROR: This script must be run inside WSL"
    exit 1
fi

# Step 1: Install system dependencies
echo "[1/5] Installing system dependencies..."
sudo apt update
sudo apt install -y python3-pip python3-venv

# Step 2: Create virtual environment
echo "[2/5] Creating virtual environment at $VENV_PATH..."
if [ -d "$VENV_PATH" ]; then
    echo "  Virtual environment already exists, skipping..."
else
    python3 -m venv "$VENV_PATH"
fi

# Step 3: Install packages
echo "[3/5] Installing OpenSpiel and dependencies..."
source "$VENV_PATH/bin/activate"
pip install --upgrade pip
pip install open_spiel nashpy numpy scipy matplotlib networkx seaborn pandas tqdm ipykernel

# Verify OpenSpiel
echo "  Verifying OpenSpiel installation..."
GAME_COUNT=$(python3 -c "import pyspiel; print(len(pyspiel.registered_names()))")
echo "  OpenSpiel OK: $GAME_COUNT games available"

# Step 4: Create wrapper script
echo "[4/5] Creating kernel wrapper script..."
cat > "$WRAPPER_PATH" << 'WRAPPER_SCRIPT'
#!/bin/bash
# Kernel wrapper for WSL - handles Windows path conversion
# DO NOT use variables like $LOG directly - they get expanded during creation

LOGFILE="/tmp/kernel-wrapper.log"
echo "=== Kernel wrapper started ===" > "$LOGFILE"
echo "Args: $@" >> "$LOGFILE"

ARGS=()
NEXT_IS_CONN=false

for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        echo "Original path: $arg" >> "$LOGFILE"

        # Handle tilde notation (~\AppData\...)
        if [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
            echo "After tilde expansion: $arg" >> "$LOGFILE"
        fi

        # Convert to Linux path
        LINUX_PATH=$(wslpath -u "$arg" 2>/dev/null)
        if [ -n "$LINUX_PATH" ]; then
            arg="$LINUX_PATH"
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

# Step 5: Instructions for Windows
echo "[5/5] Setup complete!"
echo ""
echo "=== Next Steps (run in PowerShell on Windows) ==="
echo ""
echo "Run the following PowerShell script to register the kernel:"
echo ""
echo "  cd $(wslpath -w "$(dirname "$0")")"
echo "  .\\setup_wsl_kernel.ps1"
echo ""
echo "Or manually:"
echo ""
WSL_USER=$(whoami)
echo "  \$kernelPath = \"\$env:APPDATA\\jupyter\\kernels\\gametheory-wsl\""
echo "  New-Item -ItemType Directory -Force -Path \$kernelPath"
echo "  # Then create kernel.json with wrapper path: /home/$WSL_USER/.gametheory-kernel-wrapper.sh"
echo ""
