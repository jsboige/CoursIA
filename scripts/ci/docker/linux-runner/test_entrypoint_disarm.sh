#!/usr/bin/env bash
# Tests du desarmement des refs distantes dangling de entrypoint.sh (famille
# slot-poisoning du volume _work persistant #14285/#14288 ; incident PR #15089,
# job 101812399772 : `git checkout --force` mort en `fatal: bad object
# refs/remotes/origin/chore/11840-iit-zero-pad`).
#
# Methode : on extrait le bloc REEL du script sous test (marqueurs de section)
# et on l'execute contre des depots fixture reels -- pas de stub, git est
# l'outil observe. Une ref saine doit survivre, une ref dangling (objet absent,
# fabriquee par ecriture directe du fichier loose, git refusant de la creer via
# update-ref) doit etre supprimee, le cache/working tree conserves.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/entrypoint-disarm-test-$$"
mkdir -p "$TEST_DIR/_work"
LOG="$TEST_DIR/test.log"
: > "$LOG"

RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# Extraction du bloc reel : du header de section au marqueur END.
if ! sed -n '/# --- Desarmement des refs distantes dangling/,/# TEST-ENTRYPOINT-DANGLING-REFS-END/p' \
    "$SCRIPT_DIR/entrypoint.sh" > "$TEST_DIR/block.sh" || \
   ! grep -q "for-each-ref" "$TEST_DIR/block.sh"; then
  echo "FAIL extraction du bloc entrypoint.sh" >&2
  exit 1
fi

# Fixture : un repo client sous la layout _work/<org>/<repo> avec un commit,
# une ref saine (objet present) et une ref dangling (sha fabrique, fichier
# loose ecrit directement).
make_fixture() {  # $1 = chemin du repo
  git init -q "$1"
  git -C "$1" -c user.email=t@t -c user.name=t commit -q --allow-empty -m "c1"
  echo content > "$1/file.txt"
  git -C "$1" add file.txt
  git -C "$1" -c user.email=t@t -c user.name=t commit -q -m "c2"
  local head_sha
  head_sha="$(git -C "$1" rev-parse HEAD)"
  mkdir -p "$1/.git/refs/remotes/origin"
  echo "$head_sha" > "$1/.git/refs/remotes/origin/keepbranch"
}

REPO_POISONED="$TEST_DIR/_work/jsboige/CoursIA"
REPO_CLEAN="$TEST_DIR/_work/jsboige/OtherRepo"
make_fixture "$REPO_POISONED"
make_fixture "$REPO_CLEAN"
echo "1234567890123456789012345678901234567890" > "$REPO_POISONED/.git/refs/remotes/origin/deadbranch"

# --- Test 1 : la ref dangling est supprimee, la saine conservee -------------
(
  out="$(ACTIONS_RUNNER_INPUT_WORK="$TEST_DIR/_work" bash "$TEST_DIR/block.sh" 2>&1)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -ne 0 ]; then ko "T1 le bloc doit sortir 0 (rc=$rc)"; else ok "T1 bloc exit 0"; fi
  if git -C "$REPO_POISONED" rev-parse --verify -q refs/remotes/origin/deadbranch >/dev/null; then
    ko "T1 la ref dangling doit etre supprimee"
  else ok "T1 ref dangling supprimee"; fi
  if git -C "$REPO_POISONED" rev-parse --verify -q refs/remotes/origin/keepbranch >/dev/null; then
    ok "T1 ref saine conservee"
  else ko "T1 la ref saine ne doit PAS etre supprimee"; fi
  if echo "$out" | grep -q "deadbranch"; then ok "T1 suppression journalisee"; else ko "T1 aucune trace de la suppression"; fi
)

# --- Test 2 : repo sain = intouché (controle negatif) ------------------------
(
  out="$(ACTIONS_RUNNER_INPUT_WORK="$TEST_DIR/_work" bash "$TEST_DIR/block.sh" 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ]; then ko "T2 second passage exit 0 (rc=$rc)"; else ok "T2 second passage exit 0"; fi
  if [ -n "$out" ]; then ko "T2 rien a signaler sur un depot sain (sort: $out)"; else ok "T2 silencieux sur depot sain"; fi
  if git -C "$REPO_CLEAN" rev-parse --verify -q refs/remotes/origin/keepbranch >/dev/null; then
    ok "T2 repo temoin intouché"
  else ko "T2 le repo temoin a ete modifie"; fi
)

# --- Test 3 : working tree et cache conserves --------------------------------
(
  if [ "$(cat "$REPO_POISONED/file.txt" 2>/dev/null)" = "content" ]; then
    ok "T3 working tree conserve"
  else ko "T3 working tree altere"; fi
  if git -C "$REPO_POISONED" status --porcelain 2>/dev/null | grep -q .; then
    ko "T3 status sale apres passage"
  else ok "T3 status propre"; fi
  if [ "$(git -C "$REPO_POISONED" log --oneline 2>/dev/null | wc -l)" -ge 2 ]; then
    ok "T3 historique/cache conserves (pas de purge rm -rf)"
  else ko "T3 le clone a ete purge (historique absent)"; fi
)

# --- Verdict agrege -----------------------------------------------------------
n_pass="$(grep -c '^PASS' "$RESULTS" || true)"
n_fail="$(grep -c '^FAIL' "$RESULTS" || true)"
echo "============================================================"
echo "entrypoint dangling-refs disarm : $n_pass PASS, $n_fail FAIL"
echo "============================================================"
if [ "$n_fail" -gt 0 ]; then
  echo "(logs: $LOG)"
  exit 1
fi
rm -rf "$TEST_DIR"
exit 0
