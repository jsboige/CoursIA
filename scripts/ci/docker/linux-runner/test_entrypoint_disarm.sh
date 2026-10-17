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

# --- Test 4 : prune des refs pull/* (#20697 point 2) ------------------------
# Le fetch EXPLICITE de actions/checkout (refspec +<sha>:refs/remotes/pull/N/...)
# depose une ref `refs/remotes/<remote>/pull/N/{head,merge}` par PR vue. Ces
# refs ne sont JAMAIS prunees auto et s'accumulent (~4 600 mesure du jour).
# La borne `update-ref --stdin` doit retirer les pull/*, en preservant les
# autres refs (notamment main, qui passe par refs/remotes/<remote>/main --
# pas par pull/*).
REPO_PULL="$TEST_DIR/_work/jsboige/PullRepo"
make_fixture "$REPO_PULL"
head_sha="$(git -C "$REPO_PULL" rev-parse HEAD)"
mkdir -p "$REPO_PULL/.git/refs/remotes/origin/pull/12345"
echo "$head_sha" > "$REPO_PULL/.git/refs/remotes/origin/pull/12345/head"
echo "$head_sha" > "$REPO_PULL/.git/refs/remotes/origin/pull/12345/merge"
echo "$head_sha" > "$REPO_PULL/.git/refs/remotes/origin/main"

(
  out="$(ACTIONS_RUNNER_INPUT_WORK="$TEST_DIR/_work" bash "$TEST_DIR/block.sh" 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ]; then ko "T4 le bloc doit sortir 0 (rc=$rc)"; else ok "T4 bloc exit 0"; fi
  if git -C "$REPO_PULL" rev-parse --verify -q refs/remotes/origin/pull/12345/head >/dev/null; then
    ko "T4 la ref pull/N/head doit etre supprimee"
  else ok "T4 ref pull/N/head supprimee"; fi
  if git -C "$REPO_PULL" rev-parse --verify -q refs/remotes/origin/pull/12345/merge >/dev/null; then
    ko "T4 la ref pull/N/merge doit etre supprimee"
  else ok "T4 ref pull/N/merge supprimee"; fi
  if git -C "$REPO_PULL" rev-parse --verify -q refs/remotes/origin/main >/dev/null; then
    ok "T4 ref main survit (n'est pas un pull/*)"
  else ko "T4 ref main injustement supprimee"; fi
)

# --- Test 5 : borne sur fetch paresseux en clone partiel (#20699) -----------
# Le bloc entrypoint.sh doit terminer en temps borne meme quand cat-file -e
# declenche un fetch paresseux (clone partiel : promisor=true, partialclonefilter=
# blob:none -- c.327 slot 3 po-2024). On simule en positionnant extensions.
# partialClone + remote.origin.promisor + une URL de fetch invalide : git tente
# alors un fetch paresseux sur l'objet absent. Sans timeout, le fetch pend
# indefiniment ; avec `timeout 10` (et `GIT_NO_LAZY_FETCH=1` no-op sur git 2.43
# mais actif si l'image est bumpee), le bloc sort vite. Le 2>/dev/null
# historique a ete retire -- le de-masquage est aussi verifie ici (T5 attend
# la trace sur stderr, pas en silence).
REPO_PARTIAL="$TEST_DIR/_work/jsboige/PartialRepo"
make_fixture "$REPO_PARTIAL"
git -C "$REPO_PARTIAL" config --local extensions.partialClone origin
git -C "$REPO_PARTIAL" config --local remote.origin.promisor true
git -C "$REPO_PARTIAL" config --local remote.origin.url "file:///nonexistent-at-$(date +%s)"
echo "deadbeef00000000000000000000000000000000" > "$REPO_PARTIAL/.git/refs/remotes/origin/ghost"
(
  start_ns=$(date +%s%N)
  out="$(ACTIONS_RUNNER_INPUT_WORK="$TEST_DIR/_work" bash "$TEST_DIR/block.sh" 2>&1)"; rc=$?
  end_ns=$(date +%s%N)
  duration_s=$(( (end_ns - start_ns) / 1000000000 ))
  echo "$out" >> "$LOG"
  if [ "$rc" -ne 0 ]; then ko "T5 bloc doit sortir 0 (rc=$rc)"; else ok "T5 bloc exit 0"; fi
  # Timeout 10s/SHA + 1 ref. Borne large (15s) pour absorptions CI bruyantes.
  if [ "$duration_s" -le 15 ]; then
    ok "T5 desarmement en ${duration_s}s (<15s, timeout effectif)"
  else
    ko "T5 desarmement en ${duration_s}s (>15s, timeout absent ou trop long)"
  fi
  if ! git -C "$REPO_PARTIAL" rev-parse --verify -q refs/remotes/origin/ghost >/dev/null; then
    ok "T5 ref ghost supprimee (cat-file absent/timeout -> update-ref -d)"
  else
    ko "T5 ref ghost non supprimee"
  fi
  # De-masquage de stderr : un garde de sante reste diagnosticable (#16938).
  # La trace de suppression apparait sur stderr (que l'on capture via 2>&1).
  if echo "$out" | grep -q "ghost"; then
    ok "T5 suppression journalisee (stderr de-masque)"
  else
    ko "T5 aucune trace de la suppression (stderr encore masque ?)"
  fi
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
