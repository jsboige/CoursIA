#!/usr/bin/env bash
# Dry-run NON MUTANT du controle de dimensionnement ai-01 (#15091, protocole
# #15095 « un slot avant plusieurs »).
#
# CE QUE CE SCRIPT NE FAIT JAMAIS
# -------------------------------
#   - il n'ecrit rien dans /etc ni dans /usr/local/bin ;
#   - il n'appelle systemctl qu'avec `show` / `is-active` ;
#   - il ne redemarre ni docker ni WSL ;
#   - il ne touche a aucun quota de slice.
#
# Il MESURE l'etat vivant, CALCULE l'arithmetique du garde de budget, CAPTURE
# un bundle de rollback a partir des octets vivants, et IMPRIME les commandes
# d'application sans les executer. La derniere ligne d'un dry-run est une
# proposition, jamais un fait accompli.
#
# Pourquoi cette forme : le 2026-09-08, une reecriture de wrapper a 07:47:21Z a
# arme un garde que le processus vivant, demarre 18 min plus tot, n'a pas relu.
# Le refus n'est apparu qu'au redemarrage suivant, 6 h 35 plus tard. Un
# changement de dimensionnement qui ne redemarre pas son consommateur est une
# bombe a retardement a meche arbitraire -- donc tout ce qui suit separe
# explicitement « ce que le fichier declare » de « ce que le processus applique ».

set -uo pipefail

SLOTS=1
CPUS=2
OUT="${COURSIA_DRYRUN_OUT:-/var/tmp/coursia-dryrun-$(date -u +%Y%m%dT%H%M%SZ)}"
ACK_ONE_SLOT=0

usage() {
  cat <<'USAGE'
usage: dryrun-sizing-control.sh [options]

  --slots N        nombre de slots de la famille `start` (defaut : 1)
  --cpus C         cap --cpus par conteneur de la famille (defaut : 2)
  --out DIR        repertoire du bundle de rollback (defaut : /var/tmp/...)
  --ack-one-slot   atteste que le controle a 1 slot a DEJA tourne et conclu ;
                   requis pour proposer --slots > 1 (protocole #15095)
  -h, --help

La memoire par conteneur n'est PAS un parametre : le controle la reconduit a sa
valeur vivante. Une seule variable bouge a la fois, sinon l'avant/apres
n'attribue rien.
USAGE
}

while [ $# -gt 0 ]; do
  case "$1" in
    --slots) SLOTS="${2:?--slots exige une valeur}"; shift 2 ;;
    --cpus)  CPUS="${2:?--cpus exige une valeur}";   shift 2 ;;
    --out)   OUT="${2:?--out exige une valeur}";     shift 2 ;;
    --ack-one-slot) ACK_ONE_SLOT=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "option inconnue : $1" >&2; usage >&2; exit 2 ;;
  esac
done

say()   { printf '%s\n' "$*"; }
head1() { printf '\n=== %s ===\n' "$*"; }
warn()  { printf 'ATTENTION: %s\n' "$*" >&2; }
die()   { printf 'REFUS: %s\n' "$*" >&2; exit 1; }

# --- Protocole #15095 : un slot avant plusieurs -----------------------------
# L'acceptance dit « controle positif sur un slot avant toute restauration a
# N slots ». Elle est portee ici, pas laissee a la memoire de l'operateur.
if [ "$SLOTS" -gt 1 ] && [ "$ACK_ONE_SLOT" -eq 0 ]; then
  die "protocole #15095 : --slots $SLOTS demande --ack-one-slot.
Le controle a 1 slot doit avoir tourne et conclu d'abord. S'il a conclu,
re-invoquer avec --ack-one-slot et citer sa mesure dans le compte rendu."
fi

UNIT_START=/etc/systemd/system/coursia-runner.service
UNIT_WAIT=/etc/systemd/system/coursia-waiters.service
DROPIN_START=/etc/systemd/system/coursia-runner.service.d/10-sizing.conf
DROPIN_WAIT=/etc/systemd/system/coursia-waiters.service.d/10-sizing.conf
WRAPPER_START=/usr/local/bin/coursia-runner-start.sh
SLICE_CG=/sys/fs/cgroup/coursia.slice/coursia-ci.slice

head1 "contexte"
say "date            : $(date -u '+%Y-%m-%dT%H:%M:%SZ')  (tout est horodate en Z)"
say "hote            : $(hostname)"
say "propose         : famille start = $SLOTS slot(s) x $CPUS vCPU"
say "bundle rollback : $OUT"

# --- 1. Ce que les fichiers declarent ---------------------------------------
head1 "1. ce que les fichiers vivants declarent"

read_env_of() {
  [ -r "$1" ] || return 0
  sed -n "s/^[[:space:]]*Environment=$2=\(.*\)$/\1/p" "$1" | tail -1
}
read_execstart_arg() {
  [ -r "$1" ] || return 0
  grep -E '^[[:space:]]*ExecStart=[^[:space:]]' "$1" | tail -1 | awk '{print $NF}'
}

LIVE_START_N="$(read_execstart_arg "$DROPIN_START")"
LIVE_START_MEM="$(read_env_of "$DROPIN_START" COURSIA_RUNNER_MEMORY)"
LIVE_START_CPUS="$(read_env_of "$DROPIN_START" COURSIA_RUNNER_CPUS)"
LIVE_WAIT_N="$(read_execstart_arg "$DROPIN_WAIT")"
LIVE_WAIT_MEM="$(read_env_of "$DROPIN_WAIT" COURSIA_RUNNER_WAITER_MEMORY)"
LIVE_WAIT_CPUS="$(read_env_of "$DROPIN_WAIT" COURSIA_RUNNER_WAITER_CPUS)"

# Defauts de supervise.sh quand le drop-in ne surcharge pas. La source de
# verite est le script, pas ce commentaire -- verifies contre main le
# 2026-09-08 : COURSIA_RUNNER_CPUS:-3 (l.81), COURSIA_RUNNER_WAITER_CPUS:-1
# (l.118). C'est de la que vient `cpus=3` : le drop-in vivant ne porte AUCUN
# CPUS, contrairement a ce qu'une lecture rapide de son commentaire suggere.
DEF_START_CPUS=3
DEF_WAIT_CPUS=1
EFF_START_CPUS="${LIVE_START_CPUS:-$DEF_START_CPUS}"
EFF_WAIT_CPUS="${LIVE_WAIT_CPUS:-$DEF_WAIT_CPUS}"

BUDGET="$(sed -n 's/.*COURSIA_RUNNER_CPU_BUDGET.*:-\([0-9][0-9]*\)}.*/\1/p' "$WRAPPER_START" 2>/dev/null | tail -1)"
BUDGET="${BUDGET:-0}"

printf '  %-36s %s\n' "start : slots declares" "${LIVE_START_N:-<absent>}"
if [ -n "$LIVE_START_CPUS" ]; then
  printf '  %-36s %s\n' "start : cpus par conteneur" "$EFF_START_CPUS"
else
  printf '  %-36s %s (defaut supervise.sh, PAS le drop-in)\n' "start : cpus par conteneur" "$EFF_START_CPUS"
fi
printf '  %-36s %s\n' "start : memoire par conteneur" "${LIVE_START_MEM:-<defaut>}"
printf '  %-36s %s\n' "waiters : slots declares" "${LIVE_WAIT_N:-<absent>}"
if [ -n "$LIVE_WAIT_CPUS" ]; then
  printf '  %-36s %s\n' "waiters : cpus par conteneur" "$EFF_WAIT_CPUS"
else
  printf '  %-36s %s (defaut supervise.sh)\n' "waiters : cpus par conteneur" "$EFF_WAIT_CPUS"
fi
printf '  %-36s %s\n' "waiters : memoire par conteneur" "${LIVE_WAIT_MEM:-<defaut>}"
printf '  %-36s %s\n' "budget CPU inter-familles" "$BUDGET"

# --- 2. Ce que les processus appliquent -------------------------------------
head1 "2. ce que les processus appliquent (fichier != processus)"
for U in coursia-runner.service coursia-waiters.service; do
  ST="$(systemctl is-active "$U" 2>/dev/null)"
  TS="$(systemctl show "$U" -p ExecMainStartTimestamp --value 2>/dev/null)"
  printf '  %-28s etat=%-10s demarre=%s\n' "$U" "${ST:-?}" "${TS:-<jamais>}"
done
MTIME_WRAP="$(stat -c '%y' "$WRAPPER_START" 2>/dev/null | cut -d. -f1)"
printf '  %-28s %s\n' "wrapper mtime" "${MTIME_WRAP:-<absent>}"
say "  -> si un mtime est POSTERIEUR au demarrage de l'unite, le processus"
say "     vivant tourne sous l'ANCIEN code : le garde est arme mais latent."

# --- 3. Le plafond noyau ----------------------------------------------------
head1 "3. le plafond noyau (independant de toute declaration)"
if [ -d "$SLICE_CG" ]; then
  for F in cpu.max memory.max memory.high memory.current; do
    printf '  %-16s %s\n' "$F" "$(cat "$SLICE_CG/$F" 2>/dev/null || echo '<absent>')"
  done
  say "  --- pression memoire : ou vit-elle vraiment ? ---"
  printf '  %-44s %s\n' "memory.events       (cgroup ET descendants)" \
    "$(awk '/^max /{print $2}' "$SLICE_CG/memory.events" 2>/dev/null)"
  printf '  %-44s %s\n' "memory.events.local (ce cgroup SEUL)" \
    "$(awk '/^max /{print $2}' "$SLICE_CG/memory.events.local" 2>/dev/null)"
  say "  -> local=0 avec hierarchique>0 : la pression est AU NIVEAU DES"
  say "     CONTENEURS (cap --memory par conteneur), pas au plafond agrege."
  say "     Rehausser la slice ne la soulagerait donc en rien."
  for D in "$SLICE_CG"/*/; do
    [ -d "$D" ] || continue
    printf '    %-26s cur=%-12s max=%-12s hits=%s\n' \
      "$(basename "$D" | cut -c1-26)" \
      "$(cat "$D/memory.current" 2>/dev/null)" \
      "$(cat "$D/memory.max" 2>/dev/null)" \
      "$(awk '/^max /{print $2}' "$D/memory.events" 2>/dev/null)"
  done
  say "  --- reclaim (memory.stat) ---"
  awk '/^(pgscan_direct|pgscan_kswapd|pgsteal_direct|workingset_refault_file|pgmajfault) /{printf "    %-28s %s\n",$1,$2}' \
    "$SLICE_CG/memory.stat" 2>/dev/null
  say "  -> pgscan_kswapd=0 avec pgscan_direct eleve signifie un reclaim 100 %"
  say "     DIRECT : la tache qui alloue stalle elle-meme pour liberer. C'est"
  say "     le chemin par lequel une contrainte memoire devient de la latence"
  say "     et des relectures disque (cf. la tempete d'I/O de #15095)."
else
  warn "slice absente du cgroupfs : $SLICE_CG"
fi

# --- 4. L'arithmetique du garde ---------------------------------------------
head1 "4. arithmetique du garde de budget (assert_cpu_budget)"
mul() { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.2f", a*b}'; }
add() { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.2f", a+b}'; }
verdict() { awk -v t="$1" -v b="$2" 'BEGIN{print (b>0 && t>b) ? "-> REFUSE" : "-> passe"}'; }

CUR_START="$(mul "${LIVE_START_N:-0}" "$EFF_START_CPUS")"
CUR_WAIT="$(mul "${LIVE_WAIT_N:-0}" "$EFF_WAIT_CPUS")"
CUR_TOT="$(add "$CUR_START" "$CUR_WAIT")"
NEW_START="$(mul "$SLOTS" "$CPUS")"
NEW_TOT="$(add "$NEW_START" "$CUR_WAIT")"

printf '  %-40s %s\n' "actuel  : start ${LIVE_START_N:-0} x $EFF_START_CPUS" "$CUR_START"
printf '  %-40s %s\n' "actuel  : waiters ${LIVE_WAIT_N:-0} x $EFF_WAIT_CPUS" "$CUR_WAIT"
printf '  %-40s %s / %s  %s\n' "actuel  : TOTAL" "$CUR_TOT" "$BUDGET" "$(verdict "$CUR_TOT" "$BUDGET")"
printf '  %-40s %s\n' "propose : start $SLOTS x $CPUS" "$NEW_START"
printf '  %-40s %s / %s  %s\n' "propose : TOTAL" "$NEW_TOT" "$BUDGET" "$(verdict "$NEW_TOT" "$BUDGET")"

if awk -v t="$NEW_TOT" -v b="$BUDGET" 'BEGIN{exit !(b>0 && t>b)}'; then
  die "la configuration proposee serait refusee par le garde ($NEW_TOT > $BUDGET).
Un dry-run qui propose un demarrage impossible n'a aucune valeur : baisser
--slots ou --cpus, ou arbitrer le budget en connaissance de cause."
fi
say "  -> la configuration proposee PASSE le garde. Ce n'est pas une promesse"
say "     de performance : le noyau borne deja la slice par cpu.max ci-dessus,"
say "     et un cap --cpus DECLARE n'est pas du temps CPU CONSOMME."

# --- 5. Bundle de rollback --------------------------------------------------
head1 "5. capture du rollback (octets VIVANTS, pas contenu du depot)"
mkdir -p "$OUT/live" || die "impossible de creer $OUT/live"
for F in "$UNIT_START" "$UNIT_WAIT" "$DROPIN_START" "$DROPIN_WAIT" "$WRAPPER_START"; do
  if [ ! -r "$F" ]; then warn "illisible, absent du bundle : $F"; continue; fi
  D="$OUT/live$(dirname "$F")"
  mkdir -p "$D" && cp -p "$F" "$D/" && printf '  capture %s\n' "$F"
done
{
  printf '# etat au moment de la capture -- %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  for U in coursia-runner.service coursia-waiters.service; do
    printf '%s: is-active=%s ExecMainStartTimestamp=%s\n' "$U" \
      "$(systemctl is-active "$U" 2>/dev/null)" \
      "$(systemctl show "$U" -p ExecMainStartTimestamp --value 2>/dev/null)"
  done
  if [ -d "$SLICE_CG" ]; then
    for F in cpu.max memory.max memory.high memory.current; do
      printf 'slice %s: %s\n' "$F" "$(cat "$SLICE_CG/$F" 2>/dev/null)"
    done
  fi
} > "$OUT/state-before.txt"
say "  etat consigne : $OUT/state-before.txt"

# --- 6. Le drop-in propose --------------------------------------------------
head1 "6. drop-in propose (ecrit dans le bundle, PAS dans /etc)"
mkdir -p "$OUT/proposed"
PROP="$OUT/proposed/10-sizing.conf"
{
  printf '# Controle de dimensionnement borne -- protocole #15095, « un slot\n'
  printf '# avant plusieurs ». Genere par dryrun-sizing-control.sh le %s.\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '#\n'
  printf '# UNE SEULE dimension bouge par rapport au vivant : le nombre de slots\n'
  printf '# et le cap CPU. La MEMOIRE est reconduite telle quelle (%s) --\n' "${LIVE_START_MEM:-defaut}"
  printf '# deplacer deux variables a la fois rend un avant/apres qui n%s attribue rien.\n' "'"
  printf '#\n'
  printf '# Budget : %s x %s (start) + %s x %s (waiters) = %s / %s vCPU.\n' \
    "$SLOTS" "$CPUS" "${LIVE_WAIT_N:-0}" "$EFF_WAIT_CPUS" "$NEW_TOT" "$BUDGET"
  printf '[Service]\n'
  if [ -n "$LIVE_START_MEM" ]; then
    printf 'Environment=COURSIA_RUNNER_MEMORY=%s\n' "$LIVE_START_MEM"
  fi
  printf 'Environment=COURSIA_RUNNER_CPUS=%s\n' "$CPUS"
  printf 'ExecStart=\n'
  printf 'ExecStart=/usr/local/bin/coursia-runner-start.sh %s\n' "$SLOTS"
} > "$PROP"
say "  ecrit : $PROP"
say "  --- diff vivant -> propose (informatif) ---"
diff -u "$DROPIN_START" "$PROP" 2>/dev/null | sed 's/^/  /'

# --- 7. Le script de rollback -----------------------------------------------
head1 "7. script de rollback (restaure les octets captures)"
RB="$OUT/rollback.sh"
{
  printf '#!/usr/bin/env bash\n'
  printf '# Rollback genere le %s a partir des octets VIVANTS de ai-01.\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '# Il restaure exactement ce qui etait en place AVANT toute application.\n'
  printf '# Il ne redemarre RIEN : le redemarrage est une decision separee, prise\n'
  printf '# par la lane qui porte le parc.\n'
  printf 'set -euo pipefail\n'
  printf 'B="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/live"\n'
  printf '[ -d "$B" ] || { echo "bundle absent : $B" >&2; exit 1; }\n'
  for F in "$UNIT_START" "$UNIT_WAIT" "$DROPIN_START" "$DROPIN_WAIT" "$WRAPPER_START"; do
    [ -r "$OUT/live$F" ] || continue
    case "$F" in
      *.sh) M=0755 ;;
      *)    M=0644 ;;
    esac
    printf 'install -D -m %s "$B%s" "%s"\n' "$M" "$F" "$F"
    printf 'echo "  restaure %s"\n' "$F"
  done
  printf 'systemctl daemon-reload\n'
  printf 'echo "rollback applique. AUCUNE unite redemarree -- geste separe et delibere."\n'
} > "$RB"
chmod 0755 "$RB"
say "  ecrit : $RB"

# --- 8. Ce qu'il faudrait executer -- imprime, jamais execute ---------------
head1 "8. commandes d'application -- A RELIRE, PAS A COPIER SANS ARBITRAGE"
say "  # Aucune des lignes ci-dessous n'a ete executee par ce script."
say "  #"
say "  # install -D -m 0644 $PROP \\"
say "  #                    $DROPIN_START"
say "  # systemctl daemon-reload"
say "  # systemctl start coursia-runner.service"
say "  #"
say "  # Puis, et SEULEMENT ensuite, verifier que le garde a laisse passer :"
say "  #   journalctl -u coursia-runner.service --since '-5min' | grep 'budget CPU'"
say "  # La ligne de SUCCES est « budget CPU inter-familles : N / M vCPU »."
say "  # Au 2026-09-08 elle n'avait JAMAIS ete emise sur cette machine (0 sur"
say "  # tout le journal disponible, contre 10 refus) : sa premiere apparition"
say "  # est le vrai critere de reussite du controle."
say "  #"
say "  # Rollback : $RB"

# --- 9. Temoins a relever pendant le controle -------------------------------
head1 "9. temoins a relever pendant le controle"
cat <<'WITNESS'
  Un cycle de conteneur court n'est PAS en soi une pathologie. Le 2026-09-08,
  487 intervalles inter-cycles sous 10 s ont ete mesures pendant que le parc
  fonctionnait. Le chemin rc=0 de slot_loop() est un `sleep 2` FIXE
  (supervise.sh sur main, l.588) : c'est le regime NOMINAL d'un runner
  ephemere, ou un conteneur = un job. Le backoff exponentiel (l.472, 5 s ->
  300 s, jitter 25 %) ne couvre que le chemin rc != 0.

  Le discriminant n'est donc pas la duree du cycle, mais la conjonction
  « cycle court ET aucun job reclame ». Relever, par slot :

    1. duree de vie de chaque conteneur   -- journal du superviseur
    2. le job a-t-il ete reclame ?        -- $STATE_DIR/<nom>.log a-t-il grossi
    3. jobs.runner_name cote GitHub       -- SEULE attribution valable d'un run
       a ce parc. Un compte de runs termines par heure ne rattache rien : le
       depot est servi par plusieurs machines.
    4. rc du conteneur                    -- rc=0 ne prouve PAS un job reussi
       (un runner qui s'enregistre, attend, puis sort proprement rend aussi 0).

  Ces quatre temoins ensemble decident. Aucun d'eux seul ne decide.

  PIEGE D'INSTRUMENT mesure le 2026-09-08, a connaitre avant de relever quoi
  que ce soit depuis Ubuntu :
    - `docker` y repond « docker-desktop », PAS docker-ce -- y compris via
      DOCKER_HOST=unix:///var/run/docker.sock. Un `docker inspect` lance ici
      decrit le MAUVAIS moteur. La seule surface qui donne docker-ce de facon
      sure est le cgroupfs (/sys/fs/cgroup/coursia.slice/...).
    - `/proc/uptime` et `uptime -s` sont inutilisables : 419 evenements
      « Clock change detected » dans le seul boot courant, et un ecart mesure
      de 3 min 12 s entre `uptime -s` (16:25:16) et la premiere ligne kernel du
      journal (16:22:04). Dater un boot se fait par `journalctl --list-boots`,
      jamais par uptime.
WITNESS

head1 "fin"
say "Aucun fichier de /etc ni de /usr/local/bin n'a ete modifie par ce script."
say "Bundle complet : $OUT"
exit 0
