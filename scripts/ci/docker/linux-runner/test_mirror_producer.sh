#!/usr/bin/env bash
# Tests de la moitie PRODUCTRICE du magasin d'objets partage (#18225) -- le
# script que supervise.sh fait tourner dans un conteneur jetable du volume
# toolcache : bootstrap, refresh sous throttle, prune, fail-open.
#
# Methode : meme contrat que les autres bancs de ce repertoire -- on extrait le
# script REEL du superviseur (heredoc `MIRROR_SH`) et on l'execute contre un
# depot fixture reel. Aucun stub, aucun reseau : le remote est un chemin local,
# donc ce qui est observe est le comportement de git, pas une imitation.
#
# Les cas couvrent ce qui coute cher quand c'est faux :
#   - bootstrap : un miroir mal initialise (HEAD casse, refs absentes) ferait
#     semer des slots morts ;
#   - throttle : sans lui, un tick de boucle fait un fetch -- et deux boucles
#     en font deux par periode ;
#   - prune : la propriete « prune sur = aucun objet perdu » tient a l'ABSENCE
#     de gc ; ce test la mesure au lieu de la supposer ;
#   - fail-open : sans miroir, la fonction doit rendre la main sans rien creer.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="$(mktemp -d /tmp/mirror-producer-test-XXXXXX)"
LOG="$TEST_DIR/test.log"
: > "$LOG"

RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# Extraction du script embarque (heredoc quote : aucune substitution cote
# superviseur, c'est le texte exact qui part dans le conteneur).
sed -n "/<<'MIRROR_SH'/,/^MIRROR_SH$/p" "$SCRIPT_DIR/supervise.sh" \
  | sed '1d;$d' > "$TEST_DIR/mirror.sh"
if ! grep -q 'git init --quiet --bare' "$TEST_DIR/mirror.sh"; then
  echo "FAIL extraction du script miroir de supervise.sh" >&2
  exit 1
fi

SRC="$TEST_DIR/remote.git"
MIRROR="$TEST_DIR/coursia-mirror.git"

export COURSIA_RUNNER_MIRROR_PATH="$MIRROR"
export COURSIA_RUNNER_MIRROR_REMOTE="$SRC"
export COURSIA_RUNNER_MIRROR_HEAD=main
export COURSIA_RUNNER_MIRROR_REFRESH_EVERY=300
export COURSIA_RUNNER_MIRROR_MIN_FREE_MB=1
export COURSIA_RUNNER_MIRROR_BOOTSTRAP=0

run_mirror() {  # $1 = action
  COURSIA_RUNNER_MIRROR_ACTION="$1" bash "$TEST_DIR/mirror.sh" 2>&1
}

# Remote de fixture : trois commits sur main, une branche `ephemere` en plus
# (elle servira au cas prune).
make_remote() {
  git init -q --bare "$SRC"
  git init -q -b main "$TEST_DIR/work"
  git -C "$TEST_DIR/work" config user.email t@t
  git -C "$TEST_DIR/work" config user.name t
  local i
  for i in 1 2 3; do
    echo "contenu $i" > "$TEST_DIR/work/f$i.txt"
    git -C "$TEST_DIR/work" add .
    git -C "$TEST_DIR/work" commit -qm "c$i"
  done
  git -C "$TEST_DIR/work" push -q "$SRC" main
  git -C "$TEST_DIR/work" push -q "$SRC" main:ephemere
}

make_remote

# --- Test 1 : fail-open sans miroir et sans bootstrap ----------------------
echo "Test 1 : miroir absent + bootstrap desactive -- aucun geste (fail-open)"
(
  out="$(run_mirror refresh)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 0 ]; then ok "T1 rc=0 sans miroir"; else ko "T1 rc=$rc"; fi
  if [ -d "$MIRROR" ]; then
    ko "T1 un miroir a ete cree alors que le bootstrap est desactive"
  else
    ok "T1 aucun miroir cree (le parc reste dans son etat d'avant)"
  fi
  if echo "$out" | grep -q "bootstrap desactive"; then
    ok "T1 le no-op est journalise (pas un silence)"
  else
    ko "T1 no-op silencieux : $out"
  fi
)
echo ""

# --- Test 2 : bootstrap -- miroir bare, refs bornees, HEAD resolu ----------
echo "Test 2 : bootstrap -- init bare + fetch borne, HEAD sur main"
(
  out="$(run_mirror bootstrap)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 0 ]; then ok "T2 rc=0"; else ko "T2 rc=$rc"; fi
  if [ "$(git --git-dir="$MIRROR" rev-parse --is-bare-repository 2>/dev/null)" = "true" ]; then
    ok "T2 depot bare cree"
  else
    ko "T2 depot bare absent"
  fi
  head_ref="$(git --git-dir="$MIRROR" symbolic-ref HEAD 2>/dev/null)"
  if [ "$head_ref" = "refs/heads/main" ]; then
    ok "T2 HEAD pointe refs/heads/main ($head_ref)"
  else
    ko "T2 HEAD = '$head_ref' -- un clone --shared heriterait d'un HEAD casse"
  fi
  n_main="$(git --git-dir="$MIRROR" rev-list --count main 2>/dev/null)"
  if [ "$n_main" = "3" ]; then
    ok "T2 main porte les 3 commits du remote"
  else
    ko "T2 main porte $n_main commit(s) au lieu de 3"
  fi
  # Le refspec est BORNE : aucune ref pull/ ne doit entrer dans le miroir.
  if git --git-dir="$MIRROR" for-each-ref refs/pull 2>/dev/null | grep -q .; then
    ko "T2 des refs refs/pull/* sont entrees dans le miroir (refspec non borne)"
  else
    ok "T2 aucune ref refs/pull/* (refspec borne a heads+tags)"
  fi
)
echo ""

# --- Test 3 : throttle -- deux appels rapproches, un seul fetch ------------
echo "Test 3 : throttle -- un second refresh immediat ne fetch pas"
(
  # Nouveau commit cote remote : c'est l'observable du fetch.
  echo "contenu 4" > "$TEST_DIR/work/f4.txt"
  git -C "$TEST_DIR/work" add .
  git -C "$TEST_DIR/work" commit -qm c4
  git -C "$TEST_DIR/work" push -q "$SRC" main
  # Le stamp vient d'etre pose par le bootstrap : le refresh doit sortir
  # immediatement, sans prendre le commit c4.
  run_mirror refresh >/dev/null 2>&1
  n="$(git --git-dir="$MIRROR" rev-list --count main 2>/dev/null)"
  if [ "$n" = "3" ]; then
    ok "T3 refresh throttled : main reste a 3 commits (aucun fetch)"
  else
    ko "T3 main est passe a $n commits -- le throttle ne tient pas"
  fi
  # Throttle a 0 : le meme appel doit maintenant prendre c4.
  out="$(COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh)"
  echo "$out" >> "$LOG"
  n="$(git --git-dir="$MIRROR" rev-list --count main 2>/dev/null)"
  if [ "$n" = "4" ]; then
    ok "T3 throttle a 0 : refresh effectif (main -> 4 commits)"
  else
    ko "T3 throttle a 0 : main a $n commits, le refresh n'a pas eu lieu"
  fi
  if echo "$out" | grep -q "rafraichi"; then
    ok "T3 le refresh est journalise"
  else
    ko "T3 refresh silencieux : $out"
  fi
)
echo ""

# --- Test 4 : prune d'une branche -- ref retiree, OBJET conserve ------------
# La propriete qui rend `--prune` sur : aucun gc n'est lance, donc l'objet
# entre par la ref supprimee reste dans les packs du miroir. Un slot qui
# l'emprunte -- un `_work` encore sur cette branche -- continue de le resoudre.
echo "Test 4 : prune -- la ref disparait, l'objet reste empruntable (pas de gc)"
(
  sha_eph="$(git --git-dir="$MIRROR" rev-parse refs/heads/ephemere 2>/dev/null)"
  git -C "$TEST_DIR/work" push -q "$SRC" --delete ephemere
  COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh >/dev/null 2>&1
  if git --git-dir="$MIRROR" rev-parse -q --verify refs/heads/ephemere >/dev/null 2>&1; then
    ko "T4 la branche supprimee est encore dans le miroir (--prune inoperant)"
  else
    ok "T4 la ref supprimee a bien ete prune"
  fi
  if [ -n "$sha_eph" ] && git --git-dir="$MIRROR" cat-file -e "$sha_eph^{commit}" 2>/dev/null; then
    ok "T4 l'objet de la ref prunee est TOUJOURS present (aucun gc -- un slot qui l'emprunte resout encore)"
  else
    ko "T4 l'objet a disparu avec la ref -- un slot sur cette branche serait casse"
  fi
)
echo ""

# --- Test 5 : bootstrap refuse faute d'espace -----------------------------
echo "Test 5 : garde d'espace -- bootstrap refuse proprement, rien n'est cree"
(
  M2="$TEST_DIR/mirror-toobig.git"
  out="$(COURSIA_RUNNER_MIRROR_PATH="$M2" COURSIA_RUNNER_MIRROR_MIN_FREE_MB=999999999 run_mirror bootstrap)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 0 ]; then ok "T5 rc=0 (un refus n'est pas une panne)"; else ko "T5 rc=$rc"; fi
  if [ -e "$M2" ]; then
    ko "T5 un miroir partiel a ete laisse derriere un refus"
  else
    ok "T5 aucun repertoire cree par le refus"
  fi
  if echo "$out" | grep -q "bootstrap REFUSE"; then
    ok "T5 le refus est nomme avec sa cause"
  else
    ko "T5 refus silencieux : $out"
  fi
)
echo ""

# --- Test 6 : status -- mesure reelle, jamais un zero fabrique --------------
echo "Test 6 : status -- taille, refs et date de refresh lus sur le miroir"
(
  out="$(run_mirror status)"
  echo "$out" >> "$LOG"
  if echo "$out" | grep -q "refs: "; then ok "T6 refs comptees"; else ko "T6 pas de compte de refs : $out"; fi
  if echo "$out" | grep -q "taille: [0-9]"; then ok "T6 taille mesuree"; else ko "T6 taille absente : $out"; fi
  if echo "$out" | grep -q "dernier refresh: 2"; then
    ok "T6 date du dernier refresh presente"
  else
    ko "T6 date du dernier refresh absente : $out"
  fi
  # Controle negatif : aucun compte d'emprunteurs ne doit etre annonce depuis un
  # conteneur qui ne monte aucun volume _work -- ce serait un zero fabrique.
  if echo "$out" | grep -q "emprunteurs"; then
    ko "T6 un compte d'emprunteurs est annonce depuis un conteneur sans _work (zero fabrique)"
  else
    ok "T6 aucun compte d'emprunteurs fabrique"
  fi
)
echo ""

# --- Verdict agrege --------------------------------------------------------
n_pass="$(grep -c '^PASS' "$RESULTS" || true)"
n_fail="$(grep -c '^FAIL' "$RESULTS" || true)"
echo "============================================================"
echo "miroir d'objets, moitie productrice (#18225) : $n_pass PASS, $n_fail FAIL"
echo "============================================================"
if [ "$n_fail" -gt 0 ]; then
  echo "(logs: $LOG)"
  exit 1
fi
if [ "$n_pass" -eq 0 ]; then
  echo "ERREUR: aucune assertion executee -- le harnais n'a rien mesure." >&2
  exit 2
fi
rm -rf "$TEST_DIR"
exit 0
