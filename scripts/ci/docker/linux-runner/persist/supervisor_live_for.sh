#!/usr/bin/env bash
# #21527 predicat de superviseur PER-CHECKOUT pour les scripts de demarrage
# persist/. Remplace les pgrep -f globaux : un superviseur d'un autre worktree
# (orphelin de test, etat sous /tmp) ne doit PAS bloquer le purge de la
# sentinelle de celui-ci. Usage: supervisor_live_for.sh <REPO_DIR> <mode>
# rend rc=0 si un processus vivant porte dans sa cmdline le superviseur de CE
# repo avec la sous-commande <mode>.
#
# LA RACINE DE SCAN EST INJECTABLE (COURSIA_PROC_SCAN_ROOT, defaut /proc) --
# sinon ce predicat n'est pas testable. Le cas « aucun superviseur vivant »
# est, sur une machine de production, impossible a etablir contre le /proc
# reel : les slots y tournent toujours. Le harnais
# persist/test_sentinel_purge.sh injecte donc un arbre /proc FAKE ; sans cette
# injection, la jambe ai-01 du harnais passait VACUEMENT (le predicat ne
# trouvait jamais rien, donc ni refus ni purge n'etaient reels).
set -u
REPO_DIR="$1"; MODE="$2"
case "$REPO_DIR" in */) REPO_DIR="${REPO_DIR%/}" ;; esac
PROC_SCAN_ROOT="${COURSIA_PROC_SCAN_ROOT:-/proc}"
case "$PROC_SCAN_ROOT" in */) PROC_SCAN_ROOT="${PROC_SCAN_ROOT%/}" ;; esac
for c in "$PROC_SCAN_ROOT"/[0-9]*/cmdline; do
  [ -r "$c" ] || continue
  line="$(tr '\0' ' ' < "$c" 2>/dev/null)" || continue
  case "$line" in
    *"$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh $MODE "*) exit 0 ;;
    *"$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh $MODE")  exit 0 ;;
  esac
done
exit 1

