#!/usr/bin/env bash
# Harnais de la PURGE DE SENTINELLE PERIMEE (#15163, #21527).
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
# LE CAS 5 EST LA RAISON D'ETRE DU CORRECTIF #21527.
# Un predicat PER-MACHINE (`pgrep -f 'supervise\.sh start'`) reconnait en plus
# les superviseurs d'un AUTRE checkout : un orphelin de test (etat sous /tmp,
# 6-11 h) bloquait le purge de cette sentinelle-la, service en failed, pool a
# zero. Le predicat PER-CHECKOUT ne voit que le superviseur de CE depot. Le
# cas 5 met un leurre de MEME mode, depuis un autre checkout, et exige la
# purge : c'est exactement le defaut que #21527 decrit.
#
# Aucun etat reel n'est touche : STATE_DIR est un repertoire jetable, et les
# processus sont un ARBRE /proc FAKE (COURSIA_PROC_SCAN_ROOT), jamais des
# processus vivants.
#
# Usage : bash scripts/ci/docker/linux-runner/persist/test_sentinel_purge.sh
# Sortie : "N PASS / M FAIL", rc=0 si M==0.
set -uo pipefail

# ISOLATION DU PREDICAT -- pourquoi un /proc FAKE et pas de vrais processus.
# Premiere version de ce harnais : de faux superviseurs (`sleep` a l'argv
# maquille) et le vrai `pgrep`. Elle rendait 6 PASS / 4 FAIL sur ai-01, et le
# rouge etait JUSTE : la machine porte de VRAIS superviseurs actifs, que
# `pgrep -f 'supervise\.sh start'` trouve. Le cas « aucun superviseur vivant »
# est donc intestable avec le pgrep du systeme -- sur une machine de
# production, il ne peut pas etre vrai.
#
# Deuxieme version : un stub `pgrep` sur le PATH, repondant a une table de
# processus simulee. Elle rendait VERT la jambe `runner` -- dont le predicat
# est, depuis #21541, le predicat PAR-CHECKOUT `supervisor_live_for.sh` : le
# stub n'etait plus interroge, et le predicat reel, tourne contre le /proc de
# la machine, ne trouvait jamais rien. Le cas 3 passait donc pour la mauvaise
# raison (refus par defaut) et le cas 4 pour la mauvaise raison (purge par
# defaut) : un harnais VERT A TORT, exactement ce que ce fichier reproche aux
# autres.
#
# Troisieme version (celle-ci) : le predicat PAR-CHECKOUT lit
# `COURSIA_PROC_SCAN_ROOT` (defaut /proc). Le harnais lui injecte un arbre
# /proc FAKE dont chaque `cmdline` porte un chemin de superviseur. On teste
# ainsi la logique du bloc ET le predicat reel du depot, sans dependre de ce
# qui tourne sur la machine hote -- et le cas « aucun superviseur vivant »
# redevient etabliable.

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# Racine du depot : le predicat est appele par le bloc extrait, avec
# "$REPO_DIR/scripts/ci/docker/linux-runner/persist/supervisor_live_for.sh" --
# il doit donc resoudre un vrai fichier.
REPO_ROOT="$(cd "$HERE/../../../../.." && pwd)"
TMP="$(mktemp -d)"
# Les compteurs vivent dans des FICHIERS, pas des variables : chaque cas tourne
# dans un sous-shell, ou un compteur serait incremente dans une copie que le
# parent ne relit jamais (piege mesure sur test_supervise_guards.sh, #15103).
: >"$TMP/pass"; : >"$TMP/fail"
trap 'rm -rf "$TMP"' EXIT

PROC="$TMP/proc"
LEURRE="/tmp/checkout-leurre"

# Fabrique une table de processus FAKE : un repertoire par pid, un `cmdline`
# argv-style (NUL entre les arguments, comme le vrai /proc).
#
# DEUX instruments lisent cette table, et ils doivent TOUS LES DEUX etre
# isoles de la machine hote :
# - le predicat par-checkout, par COURSIA_PROC_SCAN_ROOT (l'arbre /proc) ;
# - le repli `pgrep`, par un STUB place en tete de PATH.
# Sans le stub, le repli verrait les VRAIS superviseurs de la machine hote : le
# cas « organe absent » serait alors intestable sur une machine de production
# (le cas « aucun superviseur vivant » ne peut pas y etre vrai) -- c'est
# exactement le piege que la premiere version du harnais avait et que la
# deuxieme version avait reintroduit par l'autre bout.
PROC_TABLE="$TMP/proc-table"
fake_proc_reset() { rm -rf "$PROC"; mkdir -p "$PROC"; : >"$PROC_TABLE"; }
fake_proc_add() {  # $1 = chemin du script superviseur ; $2 = mode ; $3 = nb
  local pid
  pid=$(( 1000 + $(find "$PROC" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | wc -l) ))
  mkdir -p "$PROC/$pid"
  printf 'bash\0%s\0%s\0%s\0' "$1" "$2" "$3" >"$PROC/$pid/cmdline"
  printf 'bash %s %s %s\n' "$1" "$2" "$3" >>"$PROC_TABLE"
}
sup_path() { printf '%s/scripts/ci/docker/linux-runner/supervise.sh' "$1"; }

# Stub `pgrep` : il repond contre la table FAKE, jamais contre les processus
# reels de la machine. Il recoit le MEME motif que le code du depot.
mkdir -p "$TMP/bin"
cat >"$TMP/bin/pgrep" <<'STUB'
#!/usr/bin/env bash
pat=""
while [ $# -gt 0 ]; do case "$1" in -f) shift; pat="$1" ;; esac; shift; done
[ -f "${COURSIA_FAKE_PROC_TABLE:-}" ] || exit 1
grep -Eq -- "$pat" "$COURSIA_FAKE_PROC_TABLE"
STUB
chmod +x "$TMP/bin/pgrep"
export COURSIA_FAKE_PROC_TABLE="$PROC_TABLE"

# Deux checkouts de degrade :
# - ABSENT   : l'organe n'y est pas (checkout perime) -> repli conservateur ;
# - PERIME   : l'organe y est, mais SANS le bit executable (mode 100644 dans
#              l'index) -- le cas d'un checkout Linux natif.
ABSENT="$TMP/checkout-absent"
PERIME="$TMP/checkout-perime"
mkdir -p "$PERIME/scripts/ci/docker/linux-runner/persist"
cp "$REPO_ROOT/scripts/ci/docker/linux-runner/persist/supervisor_live_for.sh" \
   "$PERIME/scripts/ci/docker/linux-runner/persist/supervisor_live_for.sh"
chmod 644 "$PERIME/scripts/ci/docker/linux-runner/persist/supervisor_live_for.sh"

ok()   { echo "  PASS: $1"; echo x >>"$TMP/pass"; }
bad()  { echo "  FAIL: $1"; echo x >>"$TMP/fail"; }

# Controle du predicat lui-meme : un harnais dont l'instrument ment est vert a
# tort. On verifie que le predicat PAR-CHECKOUT sait dire oui (son mode, son
# checkout) ET non (autre mode) sur l'arbre fake.
fake_proc_reset
fake_proc_add "$(sup_path "$REPO_ROOT")" start 4
HELPER="$REPO_ROOT/scripts/ci/docker/linux-runner/persist/supervisor_live_for.sh"
# Le predicat est appele par `bash`, comme les SEPT wrappers de production
# (coursia-runner-start.sh et les six variantes) : dans l'index git le helper
# est en mode 100644, donc le noyau ne le rend pas executable sur un checkout
# Linux natif -- un exec direct echouerait en "Permission denied" et le
# controle d'instrument passerait A TORT (le predicat ne serait jamais
# consulte). `bash` rend l'instrumentation fidele a la production.

if COURSIA_PROC_SCAN_ROOT="$PROC" bash "$HELPER" "$REPO_ROOT" start >/dev/null \
   && ! COURSIA_PROC_SCAN_ROOT="$PROC" bash "$HELPER" "$REPO_ROOT" waiters >/dev/null; then
  echo "  PASS: le predicat discrimine le mode start du mode waiters (controle d'instrument)"
  echo x >>"$TMP/pass"
else
  echo "  FAIL: le predicat ne discrimine pas -- resultats non interpretables"
  echo x >>"$TMP/fail"
fi

# Controle negatif du meme instrument : un leurre d'un AUTRE checkout, de MEME
# mode, ne doit PAS etre vu. C'est le defaut #21527 ; si ce controle passe,
# le predicat per-checkout tient.
fake_proc_reset
fake_proc_add "$(sup_path "$LEURRE")" start 4
if ! COURSIA_PROC_SCAN_ROOT="$PROC" bash "$HELPER" "$REPO_ROOT" start >/dev/null; then
  echo "  PASS: un superviseur d'un autre checkout n'est pas vu (controle negatif #21527)"
  echo x >>"$TMP/pass"
else
  echo "  FAIL: le predicat voit le superviseur d'un autre checkout -- per-checkout non tenu"
  echo x >>"$TMP/fail"
fi

# Controle STRICT : une cmdline RELATIVE ne doit pas etre vue. Un argv relatif
# (`./scripts/...`) ne porte pas REPO_DIR : il est indiscernable entre deux
# checkouts, donc le predicat par-checkout le refuse -- c'est voulu. Ce refus
# ne serait pas sans danger si la forme relative pouvait exister en production
# (le predicat ne verrait pas le superviseur qu'il a lance) : c'est exactement
# ce que le controle statique ci-dessous interdit.
fake_proc_reset
fake_proc_add "./scripts/ci/docker/linux-runner/supervise.sh" start 4
if ! COURSIA_PROC_SCAN_ROOT="$PROC" bash "$HELPER" "$REPO_ROOT" start >/dev/null; then
  echo "  PASS: une cmdline relative n'est pas vue (forme relative non admise -- controle statique plus bas)"
  echo x >>"$TMP/pass"
else
  echo "  FAIL: le predicat voit un superviseur en argv relatif -- deux checkouts seraient confondus"
  echo x >>"$TMP/fail"
fi

# Controle STATIQUE : les sept wrappers cables lancent le superviseur par un
# CHEMIN ABSOLU. C'est l'invariant de production qui tient le predicat exact :
# le predicat ne matche que "$REPO_DIR/scripts/ci/docker/linux-runner/
# supervise.sh <mode>", donc un argv relatif produirait un faux negatif (le
# superviseur vivant, invisible au predicat) et une purge a tort de la
# sentinelle. Ce controle le rend visible dans le harnais, pas seulement a la
# relecture d'un wrapper.
PERSIST_DIR="$REPO_ROOT/scripts/ci/docker/linux-runner/persist"
rel_wrappers=""
for w in ai-01/coursia-runner-start.sh coursia-lean-start.sh \
         coursia-waiters-start.sh coursia-runner-start.sh \
         po-2025/coursia-runner-start.sh po-2027/coursia-runner-start.sh \
         po-2028/coursia-runner-start.sh; do
  if grep -nE '^[[:space:]]*exec[[:space:]]+(\./)?scripts/ci/docker/linux-runner/supervise\.sh' \
       "$PERSIST_DIR/$w" >/dev/null 2>&1; then
    rel_wrappers="$rel_wrappers $w"
  fi
done
if [ -z "$rel_wrappers" ]; then
  echo "  PASS: les sept wrappers lancent le superviseur par un chemin absolu (invariant de production)"
  echo x >>"$TMP/pass"
else
  echo "  FAIL: argv relatif du superviseur dans :$rel_wrappers"
  echo x >>"$TMP/fail"
fi

# Controle du stub `pgrep` : il doit savoir dire oui ET non, et ne JAMAIS voir
# les processus reels de la machine hote (le stub est en tete de PATH).
fake_proc_reset
fake_proc_add "$(sup_path "$REPO_ROOT")" start 4
if PATH="$TMP/bin:$PATH" pgrep -f 'supervise\.sh start' >/dev/null \
   && ! PATH="$TMP/bin:$PATH" pgrep -f 'supervise\.sh waiters' >/dev/null \
   && ! PATH="$TMP/bin:$PATH" pgrep -f 'jamais-un-mode' >/dev/null; then
  echo "  PASS: le stub pgrep discrimine les modes et ignore la machine hote (controle d'instrument)"
  echo x >>"$TMP/pass"
else
  echo "  FAIL: le stub pgrep ne discrimine pas -- resultats non interpretables"
  echo x >>"$TMP/fail"
fi

# Extrait le bloc de purge d'un wrapper et le rend executable isolement : on
# teste LE CODE DU DEPOT, pas une reecriture qui pourrait diverger de lui.
extract_purge() {
  local src="$1" out="$2"
  {
    echo '#!/usr/bin/env bash'
    echo 'set -uo pipefail'
    sed -n '/^# --- PURGE SENTINELLE PERIMEE/,/^# -\+$/p' "$src"
    echo 'echo DEMARRAGE'
  } >"$out"
  # Controle : le bloc doit avoir ete trouve. Un sed muet produirait un script
  # qui imprime DEMARRAGE dans tous les cas -- vert en permanence.
  grep -q 'rm -f "$COURSIA_RUNNER_STATE_DIR/stop"' "$out"
}

run_case() {  # $1 = script de purge ; $2 = STATE_DIR ; $3 = REPO_DIR (defaut : le depot)
  COURSIA_RUNNER_STATE_DIR="$2" \
  REPO_DIR="${3:-$REPO_ROOT}" \
  COURSIA_PROC_SCAN_ROOT="$PROC" \
  COURSIA_FAKE_PROC_TABLE="$PROC_TABLE" \
  PATH="$TMP/bin:$PATH" \
    bash "$1" 2>&1
  return $?
}

# `runner` = la jambe ai-01 (wrapper sous ai-01/) ; `po2024` = le wrapper de la
# RACINE, qui est celui de po-2024 et que son unite systemd pilote en `start` /
# `stop` (table de correspondance : persist/README.md). Les deux portent le meme
# predicat PER-CHECKOUT (`supervisor_live_for.sh ... start`) ; ils divergent par
# leur arret, et c'est ce qui rend la jambe po2024 non redondante -- sa purge
# est gardee sur la forme `start`, parce que `stop` retombe sur le meme bloc.
# `po2025` / `po2027` / `po2028` = les memes jambes sur leurs machines ; elles
# portaient le predicat PER-MACHINE comme la racine, et relèvent du meme
# defaut (#21527).
for LEG in runner waiters lean po2024 po2025 po2027 po2028; do
  case "$LEG" in
    runner)  SRC="$HERE/ai-01/coursia-runner-start.sh"; OTHER=waiters ;;
    waiters) SRC="$HERE/coursia-waiters-start.sh";      OTHER=start   ;;
    lean)    SRC="$HERE/coursia-lean-start.sh";         OTHER=start   ;;
    po2024)  SRC="$HERE/coursia-runner-start.sh";       OTHER=waiters ;;
    po2025)  SRC="$HERE/po-2025/coursia-runner-start.sh"; OTHER=waiters ;;
    po2027)  SRC="$HERE/po-2027/coursia-runner-start.sh"; OTHER=waiters ;;
    po2028)  SRC="$HERE/po-2028/coursia-runner-start.sh"; OTHER=waiters ;;
  esac
  [ -r "$SRC" ] || { bad "$LEG: wrapper illisible ($SRC)"; continue; }

  PURGE="$TMP/purge-$LEG.sh"
  if ! extract_purge "$SRC" "$PURGE"; then
    bad "$LEG: bloc de purge INTROUVABLE dans $(basename "$SRC") -- purge retiree ?"
    continue
  fi
  ok "$LEG: bloc de purge present et extrait"

  SD="$TMP/state-$LEG"; mkdir -p "$SD"

  case "$LEG" in
    runner)  MODE=start   ;;
    waiters) MODE=waiters ;;
    lean)    MODE=lean    ;;
    po2024)  MODE=start   ;;
    po2025)  MODE=start   ;;
    po2027)  MODE=start   ;;
    po2028)  MODE=start   ;;
  esac

  # --- Cas 1 : pas de sentinelle -> demarrage normal, rien a purger
  rm -f "$SD/stop"
  fake_proc_reset
  out="$(run_case "$PURGE" "$SD")"; rc=$?
  if [ "$rc" -eq 0 ] && [ "$out" = "DEMARRAGE" ]; then
    ok "$LEG/1 sentinelle absente -> demarrage, aucun bruit"
  else
    bad "$LEG/1 sentinelle absente -> rc=$rc out='$out'"
  fi

  # --- Cas 2 : sentinelle perimee, AUCUN superviseur -> purge + demarrage
  touch "$SD/stop"
  fake_proc_reset
  out="$(run_case "$PURGE" "$SD")"; rc=$?
  if [ "$rc" -eq 0 ] && [ ! -e "$SD/stop" ] && printf '%s' "$out" | grep -q 'perimee'; then
    ok "$LEG/2 sentinelle perimee sans superviseur -> PURGEE, demarrage"
  else
    bad "$LEG/2 attendu purge+rc0, obtenu rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi

  # --- Cas 3 : sentinelle + SON superviseur vivant -> refus, sentinelle INTACTE
  touch "$SD/stop"
  fake_proc_reset
  fake_proc_add "$(sup_path "$REPO_ROOT")" "$MODE" 4
  out="$(run_case "$PURGE" "$SD")"; rc=$?
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
  fake_proc_reset
  fake_proc_add "$(sup_path "$REPO_ROOT")" "$OTHER" 4
  out="$(run_case "$PURGE" "$SD")"; rc=$?
  if [ "$rc" -eq 0 ] && [ ! -e "$SD/stop" ]; then
    ok "$LEG/4 superviseur de l'AUTRE jambe vivant -> purge quand meme (predicat par-jambe)"
  else
    bad "$LEG/4 REGRESSION #15163 : predicat flotte-entiere -- rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi

  # --- Cas 5 : LE CAS DE #21527 ---------------------------------------------
  # Sentinelle de CETTE jambe, superviseur de MEME mode mais d'un AUTRE
  # checkout vivant (orphelin de test), la sienne morte. Un predicat
  # per-MACHINE refuserait de purger et laissait le service en failed, pool a
  # zero ; le predicat per-CHECKOUT purge.
  touch "$SD/stop"
  fake_proc_reset
  fake_proc_add "$(sup_path "$LEURRE")" "$MODE" 4
  out="$(run_case "$PURGE" "$SD")"; rc=$?
  if [ "$rc" -eq 0 ] && [ ! -e "$SD/stop" ]; then
    ok "$LEG/5 superviseur d'un AUTRE checkout vivant -> purge quand meme (predicat per-checkout)"
  else
    bad "$LEG/5 REGRESSION #21527 : predicat per-machine -- rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi

  # --- Cas 6 : leurre d'un autre checkout ET SON superviseur vivant -> refus
  # Le predicat ne doit voir QUE son propre superviseur : le leurre ne doit
  # ni bloquer la purge (cas 5) ni faire croire qu'un arret est en cours.
  touch "$SD/stop"
  fake_proc_reset
  fake_proc_add "$(sup_path "$LEURRE")" "$MODE" 4
  fake_proc_add "$(sup_path "$REPO_ROOT")" "$MODE" 4
  out="$(run_case "$PURGE" "$SD")"; rc=$?
  if [ "$rc" -eq 1 ] && [ -e "$SD/stop" ]; then
    ok "$LEG/6 son superviseur + un leurre -> refus rc=1, sentinelle preservee"
  else
    bad "$LEG/6 attendu rc=1 + sentinelle intacte, obtenu rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi

  # --- Cas 7 : ORGANE ABSENT (checkout perime) -> repli, pas de wedge
  # Si l'organe n'est pas lisible sur la machine (wrapper deploye avant la
  # mise a jour du checkout), le predicat retombe sur le predicat
  # per-machine. Le repli peut refuser un purge a tort, jamais purger a tort
  # -- et surtout il ne doit pas faire echouer le demarrage.
  touch "$SD/stop"
  fake_proc_reset
  out="$(run_case "$PURGE" "$SD" "$ABSENT")"; rc=$?
  if [ "$rc" -eq 0 ] && [ ! -e "$SD/stop" ]; then
    ok "$LEG/7 organe absent -> repli conservateur, purge et demarrage"
  else
    bad "$LEG/7 attendu purge+rc0 (repli), obtenu rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi

  # --- Cas 8 : ORGANE PRESENT MAIS NON EXECUTABLE -> il doit ENCORE voir
  # L'organe est 100644 dans l'index : sur un checkout Linux natif, un exec
  # direct echoue (Permission denied) et le predicat repond « aucun
  # superviseur » -- donc purge a tort, avec le superviseur vivant. Le bloc
  # doit le LIRE (`bash`), pas l'executer.
  touch "$SD/stop"
  fake_proc_reset
  fake_proc_add "$(sup_path "$PERIME")" "$MODE" 4
  out="$(run_case "$PURGE" "$SD" "$PERIME")"; rc=$?
  if [ "$rc" -eq 1 ] && [ -e "$SD/stop" ]; then
    ok "$LEG/8 organe non executable -> lu par bash, superviseur vu, refus rc=1"
  else
    bad "$LEG/8 attendu rc=1 + sentinelle intacte, obtenu rc=$rc sentinelle=$([ -e "$SD/stop" ] && echo presente || echo absente)"
  fi
done

# `grep -c` imprime son 0 AVANT de sortir 1 : `grep -c || echo 0` SUFFIXE un
# second zero au lieu de le remplacer, et le verdict devient "0\n0" (mesure
# #15103). On compte donc des lignes, sans gestionnaire d'erreur fabricant.
n_pass=$(wc -l <"$TMP/pass"); n_fail=$(wc -l <"$TMP/fail")
echo
echo "$n_pass PASS / $n_fail FAIL"
[ "$n_fail" -eq 0 ]
