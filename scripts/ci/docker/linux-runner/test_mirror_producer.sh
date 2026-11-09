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
  # Le throttle s'applique AVANT la lecture de l'existence du miroir : sans cet
  # ordre, une machine sans miroir relancerait un conteneur a chaque tick pour
  # relire le meme constat. Le second appel doit donc etre MUET (sorti sur le
  # stamp), pas repeter le message.
  out2="$(run_mirror refresh)"; rc2=$?
  if [ "$rc2" -eq 0 ] && [ -z "$out2" ]; then
    ok "T1 second refresh throttled : aucun conteneur relance, aucune trace"
  else
    ko "T1 second refresh non throttled (rc=$rc2, sortie=[$out2])"
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

# --- Tests 7-10 : `probe`, le controle positif pour hotes tiers -------------
# Le dispatch exige « un controle positif (un job fetch-depth: 0 qui finit sous
# son timeout) ». Le probe fait ce que fait un slot -- clone --shared puis
# checkout de la tete -- et rend trois faits : la duree, la presence des
# alternates, le compte d'objets locaux. Il doit ECHOUER distinctement sur un
# miroir absent, sinon « probe OK » serait rendu par un hote non installe.
echo "Test 7 : probe sur miroir absent -- echec distinct, rien de cree"
(
  M2="$TEST_DIR/mirror-absent.git"
  out="$(COURSIA_RUNNER_MIRROR_PATH="$M2" run_mirror probe)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 6 ]; then ok "T7 rc=6 sur miroir absent"; else ko "T7 rc=$rc (attendu 6)"; fi
  if echo "$out" | grep -q 'probe ECHEC.*miroir absent'; then
    ok "T7 le verdict nomme l'absence du miroir"
  else
    ko "T7 verdict muet sur la cause : $out"
  fi
  if [ -d "$M2" ]; then ko "T7 un miroir a ete cree par un probe"; else ok "T7 aucun miroir cree"; fi
)
echo ""

echo "Test 8 : probe sur miroir bootstrappe -- OK, emprunt prouve"
(
  out="$(run_mirror bootstrap)"; echo "$out" >> "$LOG"
  out="$(run_mirror probe)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 0 ]; then ok "T8 rc=0"; else ko "T8 rc=$rc : $out"; fi
  if echo "$out" | grep -q 'probe OK'; then ok "T8 verdict OK rendu"; else ko "T8 pas de verdict OK : $out"; fi
  if echo "$out" | grep -q 'budget 300s'; then
    ok "T8 le budget par defaut (300 s) est nomme dans le verdict"
  else
    ko "T8 budget par defaut non nomme : $out"
  fi
  # L'arbre de la fixture doit avoir ete checkoute : un probe qui n'ouvre rien
  # rendrait « OK » sans avoir rien mesure. Le compte exact n'est pas epingle
  # (les blocs precedents ajoutent des fichiers a la fixture) -- c'est le fait
  # qu'il soit non nul qui porte la preuve.
  if echo "$out" | grep -qE 'probe -- [1-9][0-9]* fichiers,'; then
    ok "T8 le probe a bien checkoute l'arbre (compte non nul)"
  else
    ko "T8 compte de fichiers inattendu : $out"
  fi
  if echo "$out" | grep -qE '\(budget 300s\), 0 objet'; then
    ok "T8 zero objet LOCAL : le checkout vient de l'emprunt, pas d'une copie"
  else
    ko "T8 des objets locaux ont ete crees : $out"
  fi
)
echo ""

echo "Test 9 : probe avec une tete inexistante -- echec au checkout (rc 4)"
(
  out="$(COURSIA_RUNNER_MIRROR_HEAD=pas-une-branche run_mirror probe)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 4 ]; then ok "T9 rc=4 sur checkout impossible"; else ko "T9 rc=$rc (attendu 4) : $out"; fi
  if echo "$out" | grep -q 'probe ECHEC.*checkout'; then
    ok "T9 le verdict nomme le checkout"
  else
    ko "T9 verdict muet : $out"
  fi
)
echo ""

echo "Test 10 : temoin -- la preuve d'emprunt discrimine"
(
  # Meme depot, deux formes : un clone ordinaire n'a PAS d'alternates, le clone
  # --shared du probe en a. Sans ce temoin, le « zero objet local » du test 8
  # pourrait venir de la taille de la fixture et non du montage.
  W="$TEST_DIR/witness"
  mkdir -p "$W"
  git clone -q --no-checkout "$MIRROR" "$W/plain" 2>/dev/null
  if [ -s "$W/plain/.git/objects/info/alternates" ]; then
    ko "T10 temoin : un clone ordinaire porte des alternates -- le test 8 ne prouve rien"
  else
    ok "T10 temoin : clone ordinaire sans alternates (controle negatif)"
  fi
  git clone -q --shared --no-checkout "$MIRROR" "$W/shared" 2>/dev/null
  if [ -s "$W/shared/.git/objects/info/alternates" ]; then
    ok "T10 clone --shared porte bien des alternates (controle positif)"
  else
    ko "T10 clone --shared sans alternates : le probe ne pourrait pas emprunter"
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
