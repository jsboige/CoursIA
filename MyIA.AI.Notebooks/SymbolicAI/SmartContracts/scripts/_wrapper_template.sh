#!/bin/bash
# Kernel wrapper for SmartContracts WSL
# Handles Windows path conversion for Jupyter connection files
LOGFILE="/tmp/smartcontracts-kernel-wrapper.log"
echo "=== SmartContracts kernel wrapper ===" > "$LOGFILE"
echo "Args: $@" >> "$LOGFILE"
ARGS=()
NEXT_IS_CONN=false
for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        echo "Original path: $arg" >> "$LOGFILE"
        if [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
        fi
        if [[ "$arg" =~ ^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$ ]]; then
            USERNAME="${BASH_REMATCH[1]}"
            FILENAME="${BASH_REMATCH[2]}"
            arg="C:\\Users\\${USERNAME}\\AppData\\Roaming\\jupyter\\runtime\\${FILENAME}"
        fi
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
echo "Launching ipykernel..." >> "$LOGFILE"
export PATH="$HOME/.foundry/bin:$HOME/.smartcontracts-venv/bin:$PATH"
cd ~
exec $HOME/.smartcontracts-venv/bin/python3 -m ipykernel_launcher "${ARGS[@]}"
