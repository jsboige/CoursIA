#!/usr/bin/env bash
# Pont logon -> holder : action de la tache planifiee "CoursIA-LinuxRunners"
# (InteractiveToken, LeastPrivilege). Copie de reference genrique -- le pont
# appelle le holder via HOLDER_NAME, derive par defaut de la machine
# (hold-$(hostname).ps1) : la recette §Persistance est copy-paste sur une
# machine tierce, aucune edition de script (cf #14347 item 1, reserve Hermes
# sur #14341).
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
HOLDER_NAME="${HOLDER_NAME:-hold-$(hostname).ps1}"
WINPS1="$(cygpath -w "$HOME/.coursia-runner/$HOLDER_NAME")"
if [ ! -f "$WINPS1" ]; then
  echo "FATAL: holder $WINPS1 introuvable -- deployer le ps1 ou surcharger HOLDER_NAME" >&2
  exit 2
fi
echo "holder=$HOLDER_NAME"
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "$WINPS1"
rc=$?
echo "holder spawn -> rc=$rc"
exit $rc
