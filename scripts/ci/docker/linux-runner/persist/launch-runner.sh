#!/usr/bin/env bash
# Pont logon -> holder : action de la tache planifiee "CoursIA-LinuxRunners"
# (InteractiveToken, LeastPrivilege). Copie de reference genrique -- sur
# po-2024 l'original vit sous %USERPROFILE%\.coursia-runner\launch-myia-po-2024.sh
# et appelle le holder machine-local hold-myia-po-2024.ps1.
#
#   schtasks action : C:\Program Files\Git\bin\bash.exe -lc "<ce script> 4"
#
# Le pont ne fait RIEN lui-meme : il invoque le holder PowerShell (spawn wsl
# detache) et rend son rc. Toute la logique vit dans hold-runner.ps1.
set -uo pipefail

LOG="$HOME/.coursia-runner/launcher.log"
mkdir -p "$(dirname "$LOG")"
exec >>"$LOG" 2>&1
echo "=== $(date -u +%Y-%m-%dT%H:%M:%SZ) pont logon->holder (args: $*) ==="

# cygpath : powershell.exe -File exige un chemin Windows, $HOME est posix.
WINPS1="$(cygpath -w "$HOME/.coursia-runner/hold-myia-po-2024.ps1")"
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "$WINPS1"
rc=$?
echo "holder spawn -> rc=$rc"
exit $rc
