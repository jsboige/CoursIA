#!/usr/bin/env bash
# #21527 predicat de superviseur PER-CHECKOUT pour les scripts de demarrage
# persist/. Remplace les pgrep -f globaux : un superviseur d'un autre worktree
# (orphelin de test, etat sous /tmp) ne doit PAS bloquer le purge de la
# sentinelle de celui-ci. Usage: supervisor_live_for.sh <REPO_DIR> <mode>
# rend rc=0 si un processus vivant porte dans sa cmdline le superviseur de CE
# repo avec la sous-commande <mode>.
set -u
REPO_DIR="$1"; MODE="$2"
case "$REPO_DIR" in */) REPO_DIR="${REPO_DIR%/}" ;; esac
for c in /proc/[0-9]*/cmdline; do
  line="$(tr '\0' ' ' < "$c" 2>/dev/null)" || continue
  case "$line" in
    *"$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh $MODE "*) exit 0 ;;
    *"$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh $MODE")  exit 0 ;;
  esac
done
exit 1

