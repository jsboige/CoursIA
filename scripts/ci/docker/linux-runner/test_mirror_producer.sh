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
  # Les DEUX horodatages (#26453) : le throttle (quand on a tente) et le
  # succes (quand le miroir a reellement ete rafraichi).
  if echo "$out" | grep -q "dernier refresh (throttle): 2"; then
    ok "T6 horodatage de throttle presente"
  else
    ko "T6 horodatage de throttle absent : $out"
  fi
  if echo "$out" | grep -q "dernier succes:"; then
    ok "T6 horodatage de succes presente"
  else
    ko "T6 horodatage de succes absent : $out"
  fi
  if echo "$out" | grep -q "echecs consecutifs: [0-9]"; then
    ok "T6 compteur d'echecs consecutifs affiche"
  else
    ko "T6 compteur d'echecs consecutifs absent : $out"
  fi
  # L'ecart au remote est annonce : c'est la mesure qui dit si le miroir
  # traine (la panne du 26/10 se voyait justement par un ecart de 19 jours).
  if echo "$out" | grep -q "origin/main: "; then
    ok "T6 origin/main interroge"
  else
    ko "T6 origin/main absent : $out"
  fi
  if echo "$out" | grep -qE "origin/main: [0-9a-f]{40}|origin/main: injoignable"; then
    ok "T6 la source de la reference est nommee (sha ou etat degrade)"
  else
    ko "T6 source de la reference absente : $out"
  fi
  if echo "$out" | grep -q "etat: "; then
    ok "T6 l'etat du miroir est annonce (mesure, pas supposition)"
  else
    ko "T6 etat absent : $out"
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

# --- Tests 11-14 : ce qui rend la panne MUETTE (#26453) --------------------
# Incident mesure le 2026-11-14 : le miroir d'ai-01 n'etait plus rafraichi
# depuis le 26/10. Huit entrees root-owned (FETCH_HEAD, refs/heads/main, un
# pack...) laissees par un fetch root ; le conteneur de refresh tourne sous
# `runner` (uid 1001). Le fetch echouait donc sur `FETCH_HEAD` -- et
# l'echec ressemblait a une panne reseau. Pire : l'horodatage de throttle
# etait pose AVANT le fetch, donc `mirror status` disait « dernier refresh »
# meme apres 19 jours d'echec : la panne etait muette.
#
# Ces quatre tests couvrent ce qui manquait :
#   11 : une entree hors de portee de l'uid courant fait ECHOUER le refresh
#        avec un code DISTINCT, et le dit comme une cause de droits, pas
#        comme une panne reseau ;
#   12 : un fetch en echec (reseau) ne met PAS a jour l'horodatage de
#        succes -- les deux causes sont donc distinguables ;
#   13 : trois echecs consecutifs produisent une ligne `[WARN][mirror]` ;
#   14 : un refresh reussi pose l'horodatage de succes et remet le compteur
#        d'echecs a zero.
echo "Test 11 : garde de propriete -- une entree hors de portee, refus visible (rc 7)"
(
  out="$(run_mirror bootstrap)"; echo "$out" >> "$LOG"
  OKFILE="$TEST_DIR/.objects-mirror.ok"
  if [ -f "$OKFILE" ]; then
    ok "T11 le bootstrap pose l'horodatage de succes"
  else
    ko "T11 le bootstrap n'a pas pose l'horodatage de succes"
  fi
  ok_before="$(stat -c %Y "$OKFILE" 2>/dev/null || echo 0)"
  # Rendre UNE entree inaccessible a l'uid courant. La branche exercee depend
  # du privilege du processus : root peut changer un proprietaire, un
  # utilisateur ordinaire ne peut que restreindre les droits. Les DEUX cas
  # doivent produire le meme refus visible -- c'est ce qui compte.
  if [ "$(id -u)" = "0" ]; then
    chown 1001 "$MIRROR/FETCH_HEAD" 2>/dev/null || true
    branche="propriete heterogene"
  else
    chmod 000 "$MIRROR/FETCH_HEAD" 2>/dev/null || true
    branche="droits"
  fi
  out="$(COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 7 ]; then
    ok "T11 rc=7 -- code distinct de l'echec reseau"
  else
    ko "T11 rc=$rc (attendu 7) : $out"
  fi
  if echo "$out" | grep -q "garde de propriete REFUSEE"; then
    ok "T11 le refus est nomme dans le journal"
  else
    ko "T11 refus muet : $out"
  fi
  if echo "$out" | grep -qi "PAS le reseau"; then
    ok "T11 la cause est distinguee d'une panne reseau"
  else
    ko "T11 la cause n'est pas distinguee du reseau : $out"
  fi
  if echo "$out" | grep -q "FETCH_HEAD"; then
    ok "T11 l'entree fautive est nommee ($branche)"
  else
    ko "T11 l'entree fautive n'est pas nommee : $out"
  fi
  # L'echec NE doit PAS mettre a jour l'horodatage de succes : c'est
  # precisement ce que le stamp unique ne pouvait pas dire.
  ok_after="$(stat -c %Y "$OKFILE" 2>/dev/null || echo 0)"
  if [ "$ok_after" = "$ok_before" ]; then
    ok "T11 l'horodatage de succes n'a pas bouge"
  else
    ko "T11 l'horodatage de succes a bouge malgre l'echec"
  fi
  # Et le compteur d'echecs consecutifs doit avoir avance.
  fails="$(cat "$TEST_DIR/.objects-mirror.fails" 2>/dev/null || echo 0)"
  if [ "$fails" -ge 1 ]; then
    ok "T11 le compteur d'echecs consecutifs a avance ($fails)"
  else
    ko "T11 le compteur d'echecs n'a pas avance ($fails)"
  fi
  # RESTAURATION : les tests suivants doivent retrouver un miroir sain. Sans
  # cela, ils mesureraient l'echec du test 11 au lieu de leur propre cas.
  if [ "$(id -u)" = "0" ]; then
    chown 0 "$MIRROR/FETCH_HEAD" 2>/dev/null || true
  else
    chmod 644 "$MIRROR/FETCH_HEAD" 2>/dev/null || true
  fi
)
echo ""

echo "Test 12 : fetch en echec -- l'horodatage de succes n'est PAS pose"
(
  rm -f "$TEST_DIR/.objects-mirror.ok" "$TEST_DIR/.objects-mirror.fails"
  out="$(COURSIA_RUNNER_MIRROR_REMOTE="$TEST_DIR/remote-absent.git" \
         COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 0 ]; then
    ok "T12 rc=0 (un echec reseau reste fail-open pour le parc)"
  else
    ko "T12 rc=$rc (attendu 0)"
  fi
  if [ ! -f "$TEST_DIR/.objects-mirror.ok" ]; then
    ok "T12 aucun horodatage de succes pose sur un fetch en echec"
  else
    ko "T12 un horodatage de succes a ete pose malgre l'echec"
  fi
  if echo "$out" | grep -q "refresh echoue"; then
    ok "T12 l'echec reseau est journalise"
  else
    ko "T12 echec reseau muet : $out"
  fi
)
echo ""

echo "Test 13 : trois echecs consecutifs -- une ligne [WARN][mirror]"
(
  rm -f "$TEST_DIR/.objects-mirror.fails"
  o1="$(COURSIA_RUNNER_MIRROR_REMOTE="$TEST_DIR/remote-absent.git" \
        COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh)"
  o2="$(COURSIA_RUNNER_MIRROR_REMOTE="$TEST_DIR/remote-absent.git" \
        COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh)"
  o3="$(COURSIA_RUNNER_MIRROR_REMOTE="$TEST_DIR/remote-absent.git" \
        COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh)"
  echo "$o1$o2$o3" >> "$LOG"
  if echo "$o1" | grep -q "WARN"; then
    ko "T13 une alerte est sortie au premier echec (un incident ponctuel n'alerte pas)"
  else
    ok "T13 pas d'alerte au premier echec"
  fi
  if echo "$o3" | grep -q "\[WARN\]\[mirror\]"; then
    ok "T13 l'alerte [WARN][mirror] sort au troisieme echec consecutif"
  else
    ko "T13 aucune alerte au troisieme echec : $o3"
  fi
  if echo "$o3" | grep -q "3 fois de suite"; then
    ok "T13 l'alerte nomme le nombre d'echecs"
  else
    ko "T13 l'alerte ne nomme pas le nombre d'echecs : $o3"
  fi
  # L'alerte doit aussi etre lisible dans le STATUT : c'est la surface qu'un
  # heartbeat ou un operateur consulte. Une ligne de journal jamais relue ne
  # vaut rien (l'incident du 26/10 a produit 2 700 lignes d'erreur sans
  # qu'aucune ne soit vue).
  sout="$(run_mirror status)"
  echo "$sout" >> "$LOG"
  if echo "$sout" | grep -q "\[WARN\]\[mirror\]"; then
    ok "T13 l'alerte est reprise dans le statut"
  else
    ko "T13 l'alerte n'apparait pas dans le statut : $sout"
  fi
)
echo ""

echo "Test 14 : refresh reussi -- horodatage de succes pose, compteur a zero"
(
  rm -f "$TEST_DIR/.objects-mirror.fails" "$TEST_DIR/.objects-mirror.ok"
  out="$(COURSIA_RUNNER_MIRROR_REFRESH_EVERY=0 run_mirror refresh)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 0 ]; then ok "T14 rc=0"; else ko "T14 rc=$rc"; fi
  if [ -f "$TEST_DIR/.objects-mirror.ok" ]; then
    ok "T14 l'horodatage de succes est pose"
  else
    ko "T14 l'horodatage de succes est absent"
  fi
  fails="$(cat "$TEST_DIR/.objects-mirror.fails" 2>/dev/null || echo 0)"
  if [ "$fails" = "0" ]; then
    ok "T14 le compteur d'echecs est remis a zero"
  else
    ko "T14 le compteur d'echecs est a $fails"
  fi
  if echo "$out" | grep -q "rafraichi"; then
    ok "T14 le refresh est journalise"
  else
    ko "T14 refresh silencieux : $out"
  fi
)
echo ""

# --- Test 15 : la mesure en direct du miroir est BORDEE EN TEMPS ---------
# Un `git ls-remote` qui pend (reseau coupe, DNS qui ne repond pas) ne doit
# pas pendre le tick : le tick qui ne rend pas ne rafraichit rien, et le
# miroir finit par figer SANS que personne ne le voie -- exactement la panne
# muette de #26453 (19 jours de miroir fige, 2 700 lignes de journal lues
# par personne).
#
# Le test est HERMETIQUE : pas de reseau, pas d'attente. Un faux `git` --
# place AVANT le vrai dans le PATH -- pend sur `ls-remote` et delegue tout
# le reste. Le `timeout` doit couper la mesure en quelques secondes.
echo "Test 15 : ls-remote borne -- un reseau qui pend ne pend pas le tick"
(
  REAL_GIT="$(command -v git)"
  mkdir -p "$TEST_DIR/bin"
  cat > "$TEST_DIR/bin/git" <<'FAKEGIT'
#!/usr/bin/env bash
if [ "$1" = "ls-remote" ]; then
  sleep 60
  exit 0
fi
exec "@REAL_GIT@" "$@"
FAKEGIT
  sed -i "s|@REAL_GIT@|$REAL_GIT|" "$TEST_DIR/bin/git"
  chmod +x "$TEST_DIR/bin/git"

  # CONTROLE NEGATIF : sans faux `git`, la mesure ne doit PAS annoncer un
  # delai depasse. Sans ce controle, un test qui annonce toujours
  # « delai depasse » passerait quand meme.
  out_ok="$(run_mirror status)"
  echo "$out_ok" >> "$LOG"
  if echo "$out_ok" | grep -qi "delai depasse"; then
    ko "T15 controle negatif : un delai depasse est annonce alors que le reseau repond"
  else
    ok "T15 controle negatif : aucune mention de delai depasse quand la mesure repond"
  fi
  if echo "$out_ok" | grep -q "mesure distante: ls-remote borne a"; then
    ok "T15 la mesure en direct annonce sa borne"
  else
    ko "T15 la borne de la mesure en direct n'est pas annoncee : $out_ok"
  fi

  if ! command -v timeout >/dev/null 2>&1; then
    ok "T15 environnement sans \`timeout\` : la mesure ne peut pas etre bornee ici (controle non applicable)"
  else
    t0="$(date +%s)"
    out="$(PATH="$TEST_DIR/bin:$PATH" COURSIA_RUNNER_MIRROR_LS_REMOTE_TIMEOUT_S=2 run_mirror status)"; rc=$?
    t1="$(date +%s)"
    echo "$out" >> "$LOG"
    if [ "$rc" -eq 0 ]; then ok "T15 rc=0 -- le statut rend la main"; else ko "T15 rc=$rc"; fi
    dur=$(( t1 - t0 ))
    if [ "$dur" -le 30 ]; then
      ok "T15 le tick n'a pas pendu (${dur}s pour une mesure bornee a 2s)"
    else
      ko "T15 le tick a pendu ${dur}s : la mesure en direct n'est pas bornee"
    fi
    if echo "$out" | grep -qi "delai depasse"; then
      ok "T15 le delai depasse est annonce (cause et non pas un silence)"
    else
      ko "T15 le delai depasse n'est pas annonce : $out"
    fi
    # La note doit SURVIVRE a la reconduction vers la reference hors-ligne :
    # sinon le tick suivant ne sait plus pourquoi la source a change.
    if echo "$out" | grep -q "mesure distante:"; then
      ok "T15 la note de la mesure distante est dans le statut"
    else
      ko "T15 la note de la mesure distante est absente : $out"
    fi
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
