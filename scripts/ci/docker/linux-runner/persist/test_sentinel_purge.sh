#!/usr/bin/env bash
# Harnais de la PURGE DE SENTINELLE PERIMEE (#15163).
#
# CE QUE CE HARNAIS EXISTE POUR EMPECHER
# --------------------------------------
# La sentinelle d'arret gracieux ("$STATE_DIR/stop") est un FICHIER : elle
# survit au reboot. Sans purge au demarrage, un arret gracieux suivi d'un
# redemarrage machine laisse l'unite echouer et le pool a ZERO jusqu'a
# intervention humaine -- quatre fois dans la journee du 2026-09-07, chaque
# fois avec un deplacement physique jusqu'a la machine.
#
# La prose du wrapper decrit ce comportement ; elle ne le tient pas. Ce fichier
# le tient : retirer la purge, ou revenir a un predicat flotte-entiere, fait
# rougir les cas 2 et 4.
#
# LE CAS 4 EST LA RAISON D'ETRE DU CORRECTIF #15163.
# Un predicat `supervise\.sh (start|waiters)` repond « un superviseur
# QUELCONQUE vit-il ? ». Les deux jambes ont pourtant des sentinelles
# DISTINCTES (/var/lib/coursia-runner/stop et /var/lib/coursia-waiters/stop) :
# sous un predicat global, chaque jambe refuse de purger SA PROPRE sentinelle
# perimee tant que L'AUTRE tourne. Les deux formes ne divergent que la -- c'est
# donc le seul cas qui distingue le correctif de ce qu'il corrige, et le seul
# qui rougirait sur une regression silencieuse.
#
# Aucun etat reel n'est touche : STATE_DIR est un repertoire jetable, et les
# faux superviseurs sont des `sleep` dont l'argv porte le motif recherche.
#
# Usage : bash scripts/ci/docker/linux-runner/persist/test_sentinel_purge.sh
# Sortie : "N PASS / M FAIL", rc=0 si M==0.
set -uo pipefail

# ISOLATION DU PREDICAT -- pourquoi un stub `pgrep` et pas de vrais processus.
# Premiere version de ce harnais : de faux superviseurs (`sleep` a l'argv
# maquille) et le vrai `pgrep`. Elle rendait 6 PASS / 4 FAIL sur ai-01, et le
# rouge etait JUSTE : la machine porte de VRAIS superviseurs actifs, que
# `pgrep -f 'supervise\.sh start'` trouve. Le cas « aucun superviseur vivant »
# est donc intestable avec le pgrep du systeme -- sur une machine de
# production, il ne peut pas etre vrai.
#
# Le stub ci-dessous rend le predicat interrogeable : il recoit le MEME motif
# que le code du depot (extrait de lui, jamais reecrit) et repond contre une
# table de processus declaree par chaque cas. On teste ainsi la logique du bloc
# ET le motif reel, sans dependre de ce qui tourne sur la machine hote.

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TMP="$(mktemp -d)"
# Les compteurs vivent dans des FICHIERS, pas des variables : chaque cas tourne
# dans un sous-shell, ou un compteur serait incremente dans une copie que le
# parent ne relit jamais (piege mesure sur test_supervise_guards.sh, #15103).
: >"$TMP/pass"; : >"$TMP/fail"
trap 'rm -rf "$TMP"' EXIT

# Stub `pgrep` : place en tete de PATH, il court-circuite celui du systeme.
# Il lit la table de processus simules dans $FAKE_PROCS (une ligne par
# processus) et applique le motif recu en -f comme une ERE, exactement comme le
# ferait pgrep. Un motif qui ne matche rien -> rc=1, comme pgrep.
mkdir -p "$TMP/bin"
cat >"$TMP/bin/pgrep" <<'STUB'
#!/usr/bin/env bash
pat=""
while [ $# -gt 0 ]; do case "$1" in -f) shift; pat="$1" ;; esac; shift; done
[ -n "${FAKE_PROCS:-}" ] || exit 1
printf '%s
' "$FAKE_PROCS" | grep -Eq -- "$pat"
STUB
chmod +x "$TMP/bin/pgrep"
export PATH="$TMP/bin:$PATH"

# Controle du stub lui-meme : un harnais dont l'instrument ment est vert a
# tort. On verifie qu'il sait dire oui ET non avant de s'en servir.
if FAKE_PROCS='bash ./supervise.sh start 4' pgrep -f 'supervise\.sh start' >/dev/null    && ! FAKE_PROCS='bash ./supervise.sh waiters 4' pgrep -f 'supervise\.sh start' >/dev/null; then
  echo "  PASS: stub pgrep discrimine start vs waiters (controle d'instrument)"
  echo x >>"$TMP/pass"
else
  echo "  FAIL: stub pgrep ne discrimine pas -- resultats non interpretables"
  echo x >>"$TMP/fail"
fi

ok()   { echo "  PASS: $1"; echo x >>"$TMP/pass"; }
bad()  { echo "  FAIL: $1"; echo x >>"$TMP/fail"; }

# Extrait le bloc de purge d'un wrapper et le rend executable isolement : on
# teste LE CODE DU DEPOT, pas une reecriture qui pourrait diverger de lui.
extract_purge() {
  local src="$1" out="$2"
  {
    echo '#!/usr/bin/env bash'
    echo 'set -uo pipefail'
    sed -n '/^# --- PURGE SENTINELLE PERIMEE/,/^# ---------------------------------------------------------------------------$/p' "$src"
    echo 'echo DEMARRAGE'
  } >"$out"
  # Controle : le bloc doit avoir ete trouve. Un sed muet produirait un script
  # qui imprime DEMARRAGE dans tous les cas -- vert en permanence.
  grep -q 'rm -f "$COURSIA_RUNNER_STATE_DIR/stop"' "$out"
}

run_case() {  # $1 = script de purge ; $2 = STATE_DIR ; $3 = table de processus
  COURSIA_RUNNER_STATE_DIR="$2" FAKE_PROCS="${3:-}" PATH="$TMP/bin:$PATH" bash "$1" 2>&1
  return $?
}

for LEG in runner waiters lean; do
  case "$LEG" in
    runner)  SRC="$HERE/ai-01/coursia-runner-start.sh"; OTHER=waiters ;;
    waiters) SRC="$HERE/coursia-waiters-start.sh";      OTHER=start   ;;
    lean)    SRC="$HERE/coursia-lean-start.sh";         OTHER=start   ;;
  esac
  [ -r "$SRC" ] || { bad "$LEG: wrapper illisible ($SRC)"; continue; }

  PURGE="$TMP/purge-$LEG.sh"
  if ! extract_purge "$SRC" "$PURGE"; then
    bad "$LEG: bloc de purge INTROUVABLE dans $(basename "$SRC") -- purge retiree ?"
    continue
  fi
  ok "$LEG: bloc de purge present et extrait"

  SD="$TMP/state-$LEG"; mkdir -p "$SD"

  # --- Cas 1 : pas de sentinelle -> demarrage normal, rien a purger
  rm -f "$SD/stop"
  out="$(run_case "$PURGE" "$SD" "")"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "DEMARRAGE" ]; then
    ok "$LEG/1 sentinelle absente -> demarrage, aucun bruit"
  else
    bad "$LEG/1 sentinelle absente -> rc=$rc out='$out'"
  fi

  # --- Cas 2 : sentinelle perimee, AUCUN superviseur -> purge + demarrage
  touch "$SD/stop"
  out="$(run_case "$PURGE" "$SD" "")"; rc=$?
  if [ "$rc" -eq 0 ] && [ ! -e "$SD/stop" ] && printf '%s' "$out" | grep -q 'perimee'; then
    ok "$LEG/2 sentinelle perimee sans superviseur -> PURGEE, demarrage"
  else
    bad "$LEG/2 attendu purge+rc0, obtenu rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi

  # --- Cas 3 : sentinelle + SON superviseur vivant -> refus, sentinelle INTACTE
  touch "$SD/stop"
  case "$LEG" in
    runner)  MINE='bash ./supervise.sh start 4' ;;
    waiters) MINE='bash ./supervise.sh waiters 4' ;;
    lean)    MINE='bash ./supervise.sh lean 2' ;;
  esac
  out="$(run_case "$PURGE" "$SD" "$MINE")"; rc=$?
  if [ "$rc" -eq 1 ] && [ -e "$SD/stop" ] && ! printf '%s' "$out" | grep -q 'DEMARRAGE'; then
    ok "$LEG/3 arret en cours -> refus rc=1, sentinelle preservee, pas de demarrage"
  else
    bad "$LEG/3 attendu rc=1 + sentinelle intacte, obtenu rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi

  # --- Cas 4 : LE CAS DIVERGENT (#15163) ------------------------------------
  # Sentinelle de CETTE jambe, superviseur de L'AUTRE jambe vivant, la sienne
  # morte. Un predicat flotte-entiere refuserait de purger (« un superviseur
  # vit ») et laisserait le pool a zero ; le predicat par-jambe purge.
  touch "$SD/stop"
  out="$(run_case "$PURGE" "$SD" "bash ./supervise.sh $OTHER 4")"; rc=$?
  if [ "$rc" -eq 0 ] && [ ! -e "$SD/stop" ]; then
    ok "$LEG/4 superviseur de l'AUTRE jambe vivant -> purge quand meme (predicat par-jambe)"
  else
    bad "$LEG/4 REGRESSION #15163 : predicat flotte-entiere -- rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi
done

# `grep -c` imprime son 0 AVANT de sortir 1 : `grep -c || echo 0` SUFFIXE un
# second zero au lieu de le remplacer, et le verdict devient "0\n0" (mesure
# #15103). On compte donc des lignes, sans gestionnaire d'erreur fabricant.
n_pass=$(wc -l <"$TMP/pass"); n_fail=$(wc -l <"$TMP/fail")
echo
echo "$n_pass PASS / $n_fail FAIL"
[ "$n_fail" -eq 0 ]
