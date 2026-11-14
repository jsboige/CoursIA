#!/usr/bin/env bash
# CI-CHECK: --check
#   ^ Verifie l'installation et la nature du kernelspec sans rien installer.
# Façade historique pour macOS/Linux : l'installation canonique est partagée
# avec setup_wsl_lean4.sh afin de garder le pin Lean et le kernel Lean réels.
#
# Usage:
#   bash setup_lean4_native.sh          # Installation native macOS/Linux
#   bash setup_lean4_native.sh --check  # Vérification sans modification

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
LEAN4_VENV="${LEAN4_VENV:-$HOME/.lean4-venv}"
LEAN_TOOLCHAIN="$(tr -d '[:space:]' < "$SCRIPT_DIR/../game_theory_lean/lean-toolchain")"

if [[ "${1:-}" == "--check" ]]; then
    errors=0
    if [[ -x "$ELAN_HOME/bin/elan" ]]; then
        echo "[OK] elan: $ELAN_HOME/bin/elan"
    else
        echo "[ERROR] elan absent: $ELAN_HOME/bin/elan"
        errors=$((errors + 1))
    fi
    if [[ -x "$ELAN_HOME/bin/elan" ]] && \
       lean_version="$("$ELAN_HOME/bin/elan" run "$LEAN_TOOLCHAIN" lean --version 2>&1)"; then
        echo "[OK] lean ($LEAN_TOOLCHAIN): $lean_version"
    else
        echo "[ERROR] toolchain Lean indisponible: $LEAN_TOOLCHAIN (${lean_version:-elan absent})"
        errors=$((errors + 1))
    fi
    if [[ -x "$ELAN_HOME/bin/repl" ]]; then
        echo "[OK] REPL: $ELAN_HOME/bin/repl"
    else
        echo "[ERROR] REPL absent: $ELAN_HOME/bin/repl"
        errors=$((errors + 1))
    fi
    if [[ -x "$LEAN4_VENV/bin/python3" ]] && \
       "$LEAN4_VENV/bin/python3" -c 'import lean4_jupyter' >/dev/null 2>&1; then
        echo "[OK] lean4_jupyter: $LEAN4_VENV"
    else
        echo "[ERROR] lean4_jupyter absent du venv: $LEAN4_VENV"
        errors=$((errors + 1))
    fi

    if ! command -v jupyter >/dev/null 2>&1 || ! command -v python3 >/dev/null 2>&1; then
        echo "[ERROR] jupyter et python3 sont requis pour vérifier le kernelspec"
        errors=$((errors + 1))
    elif python3 -c '
import json
import subprocess
import sys

try:
    inventory = json.loads(subprocess.check_output(
        ["jupyter", "kernelspec", "list", "--json"], text=True
    ))["kernelspecs"]
    spec = inventory["lean4-wsl"]["spec"]
except (KeyError, json.JSONDecodeError, subprocess.CalledProcessError) as exc:
    print(f"[ERROR] kernelspec lean4-wsl absent ou illisible: {exc}")
    sys.exit(1)

argv = spec.get("argv", [])
if spec.get("language", "").lower() != "lean4" or not any(
    "lean4-kernel-wrapper.py" in str(arg) for arg in argv
):
    print("[ERROR] lean4-wsl ne pointe pas vers le wrapper Lean (un noyau IPython ne convient pas)")
    sys.exit(1)
print("[OK] kernelspec lean4-wsl: language=lean4, wrapper Lean")
'; then
        :
    else
        errors=$((errors + 1))
    fi

    if [[ "$errors" -eq 0 ]]; then
        echo "[OK] Installation Lean native prête"
        exit 0
    fi
    echo "[ERROR] $errors vérification(s) en échec; lancer le script sans --check pour installer"
    exit 1
fi

if [[ $# -gt 0 ]]; then
    echo "Usage: bash setup_lean4_native.sh [--check]" >&2
    exit 2
fi

exec bash "$SCRIPT_DIR/setup_wsl_lean4.sh"
