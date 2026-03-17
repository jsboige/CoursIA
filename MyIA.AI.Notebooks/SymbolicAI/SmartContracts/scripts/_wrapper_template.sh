#!/bin/bash
# Kernel wrapper for SmartContracts (WSL on Windows)
# Handles Windows path conversion for Jupyter connection files
#
# Problem: WSL consumes backslashes, so a path like:
#   C:\Users\MYIA\AppData\Local\Temp\tmp123.json
# arrives as:
#   C:UsersMYIAAppDataLocalTemptmp123.json
#
# Solution: extract filename, search known temp locations.

LOGFILE="/tmp/smartcontracts-kernel-wrapper.log"
echo "=== SmartContracts kernel wrapper ===" > "$LOGFILE"
echo "Args: $@" >> "$LOGFILE"

ARGS=()
NEXT_IS_CONN=false

for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        echo "Original path: $arg" >> "$LOGFILE"

        # Already a Linux path
        if [[ "$arg" == /* ]]; then
            true  # keep as-is

        # Tilde notation
        elif [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
            LINUX_PATH=$(wslpath -u "$arg" 2>/dev/null)
            [ -n "$LINUX_PATH" ] && arg="$LINUX_PATH"

        # Intact Windows path (has backslashes or proper drive:\ format)
        elif [[ "$arg" == *"\\"* ]]; then
            LINUX_PATH=$(wslpath -u "$arg" 2>/dev/null)
            [ -n "$LINUX_PATH" ] && arg="$LINUX_PATH"

        # Mangled path: backslashes stripped (e.g. C:UsersMYIAAppDataLocalTemptmpXXX.json)
        elif [[ "$arg" =~ ^([a-zA-Z]):(.+)$ ]]; then
            DRIVE="${BASH_REMATCH[1]}"
            REST="${BASH_REMATCH[2]}"
            # Extract filename: tmp*.json or kernel-*.json (pattern after Temp or runtime)
            FILENAME=""
            if [[ "$REST" =~ (tmp[a-zA-Z0-9_]+\.json)$ ]]; then
                FILENAME="${BASH_REMATCH[1]}"
            elif [[ "$REST" =~ (kernel-[a-zA-Z0-9-]+\.json)$ ]]; then
                FILENAME="${BASH_REMATCH[1]}"
            fi
            echo "Mangled: drive=$DRIVE filename=$FILENAME rest=$REST" >> "$LOGFILE"

            if [ -n "$FILENAME" ]; then
                # Search for the file in known temp/runtime locations
                FOUND=""
                for DIR in "/mnt/${DRIVE,,}/Users/"*/AppData/Local/Temp \
                           "/mnt/${DRIVE,,}/Users/"*/AppData/Roaming/jupyter/runtime \
                           "/tmp"; do
                    [ -d "$DIR" ] || continue
                    MATCH="$DIR/$FILENAME"
                    if [ -f "$MATCH" ]; then
                        FOUND="$MATCH"
                        break
                    fi
                done

                if [ -n "$FOUND" ]; then
                    arg="$FOUND"
                    echo "Found: $arg" >> "$LOGFILE"
                else
                    echo "WARN: Could not find $FILENAME" >> "$LOGFILE"
                fi
            else
                echo "WARN: Could not extract filename from mangled path" >> "$LOGFILE"
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

export PATH="$HOME/.foundry/bin:$HOME/.smartcontracts-venv/bin:$PATH"
exec "$HOME/.smartcontracts-venv/bin/python3" -m ipykernel_launcher "${ARGS[@]}" 2>> "$LOGFILE"
