#!/usr/bin/env bash
# Dry-run NON MUTANT du controle de dimensionnement ai-01 (#15091, protocole
# #15095 « un slot avant plusieurs »).
#
# CE QUE CE SCRIPT NE FAIT JAMAIS
# -------------------------------
#   - il n'ecrit rien dans /etc ni dans /usr/local/bin ;
#   - il n'appelle systemctl qu'avec `show` / `cat` / `is-active` ;
#   - il ne redemarre ni docker ni WSL ;
#   - il ne touche a aucun quota de slice.
#
# IL ECHOUE PLUTOT QUE DE RENDRE UN VERDICT QU'IL NE PEUT PAS ETAYER.
# C'est la propriete centrale, et elle a ete ajoutee apres coup : la premiere
# version rendait « passe » quand le budget etait ILLISIBLE (budget non lu -> 0,
# et le predicat `total > budget` est faux quand budget vaut 0). Un dry-run dont
# le mode de defaillance est « approuver » est pire que pas de dry-run du tout.
# Toute source requise absente, illisible ou non interpretable est desormais
# FATALE, et l'absence de garde se dit, elle ne se confond pas avec un succes.
#
# Pourquoi cette forme : le 2026-09-08, une reecriture de wrapper a 07:47:21Z a
# arme un garde que le processus vivant, demarre 18 min plus tot, n'a pas relu.
# Le refus n'est apparu qu'au redemarrage suivant, 6 h 35 plus tard, puis a
# rejoue a l'identique a chaque boot. Un changement de dimensionnement qui ne
# redemarre pas son consommateur est une bombe a retardement a meche arbitraire
# -- donc tout ce qui suit separe « ce que le fichier declare », « ce que
# systemd applique reellement » et « ce que le processus vivant execute ».

set -uo pipefail

SLOTS=1
CPUS=2
OUT="${COURSIA_DRYRUN_OUT:-/var/tmp/coursia-dryrun-$(date -u +%Y%m%dT%H%M%SZ)}"
ACK_ONE_SLOT=0

# Points d'injection pour les tests : ils permettent d'exercer le script sur des
# fixtures, sans machine reelle, sans systemd, sans redemarrage.
ROOT="${COURSIA_DRYRUN_ROOT:-}"
SYSTEMCTL="${COURSIA_DRYRUN_SYSTEMCTL:-systemctl}"

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
valeur vivante, ce qui retire UNE variable du plan -- pas toutes. Si cette
valeur ne peut pas etre lue, le script ECHOUE : emettre un drop-in sans ligne
memoire la ferait retomber sur le defaut de supervise.sh (4g), c'est-a-dire
deplacer en silence la variable que l'on pretend tenir fixe.

Ce controle n'est PAS univarie, et il ne faut pas le lire comme tel : DEUX
facteurs de capacite bougent ensemble, le nombre de slots et le cap CPU par
slot. Un avant/apres a deux cellules dont deux variables ont bouge n'attribue
aucune difference observee a l'une plutot qu'a l'autre.

Ce qu'il peut trancher malgre ca, et qui est tout ce qu'on lui demande, est
BINAIRE : la famille franchit-elle le garde et demarre-t-elle, et un slot unique
reclame-t-il un job. Ces deux reponses ne demandent aucune attribution. Tout
jugement de DEBIT tire de ce controle serait, lui, confondu -- ne pas en tirer un.

Variables d'environnement (tests) :
  COURSIA_DRYRUN_ROOT        prefixe applique aux chemins systeme (fixtures)
  COURSIA_DRYRUN_SYSTEMCTL   commande a utiliser a la place de `systemctl`
  COURSIA_DRYRUN_OUT         repertoire du bundle
USAGE
}

say()   { printf '%s\n' "$*"; }
head1() { printf '\n=== %s ===\n' "$*"; }
warn()  { printf 'ATTENTION: %s\n' "$*" >&2; }
die()   { printf 'REFUS: %s\n' "$*" >&2; exit 1; }

# --- Validation des entrees (fail-closed) -----------------------------------
pos_int() {
  case "${1:-}" in
    ''|*[!0-9]*) return 1 ;;
  esac
  [ "$1" -ge 1 ] 2>/dev/null || return 1
  [ "$1" -le 64 ] 2>/dev/null || return 1
  return 0
}

while [ $# -gt 0 ]; do
  case "$1" in
    --slots)
      [ $# -ge 2 ] || die "--slots exige une valeur"
      pos_int "$2" || die "--slots : entier attendu entre 1 et 64, recu « $2 »"
      SLOTS="$2"; shift 2 ;;
    --cpus)
      [ $# -ge 2 ] || die "--cpus exige une valeur"
      pos_int "$2" || die "--cpus : entier attendu entre 1 et 64, recu « $2 »"
      CPUS="$2"; shift 2 ;;
    --out)
      [ $# -ge 2 ] || die "--out exige une valeur"
      case "$2" in ''|-*) die "--out : chemin invalide « $2 »" ;; esac
      OUT="$2"; shift 2 ;;
    --ack-one-slot) ACK_ONE_SLOT=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'option inconnue : %s\n' "$1" >&2; usage >&2; exit 2 ;;
  esac
done

# --- Protocole #15095 : un slot avant plusieurs -----------------------------
if [ "$SLOTS" -gt 1 ] && [ "$ACK_ONE_SLOT" -eq 0 ]; then
  die "protocole #15095 : --slots $SLOTS demande --ack-one-slot.
Le controle a 1 slot doit avoir tourne et conclu d'abord. S'il a conclu,
re-invoquer avec --ack-one-slot et citer sa mesure dans le compte rendu."
fi

UNIT_START="$ROOT/etc/systemd/system/coursia-runner.service"
UNIT_WAIT="$ROOT/etc/systemd/system/coursia-waiters.service"
DROPIN_START="$ROOT/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
DROPIN_WAIT="$ROOT/etc/systemd/system/coursia-waiters.service.d/10-sizing.conf"
WRAPPER_START="$ROOT/usr/local/bin/coursia-runner-start.sh"
SLICE_CG="$ROOT/sys/fs/cgroup/coursia.slice/coursia-ci.slice"

# Etat d'une source, en TROIS valeurs -- « absent » et « illisible » ne se
# confondent pas : le premier peut etre nominal, le second est toujours une
# panne d'instrument.
state_of() {
  if   [ -e "$1" ] && [ -r "$1" ]; then printf 'PRESENT'
  elif [ -e "$1" ];                then printf 'ILLISIBLE'
  else                                  printf 'ABSENT'
  fi
}
require_readable() {   # $1 = chemin, $2 = role
  case "$(state_of "$1")" in
    PRESENT)   return 0 ;;
    ABSENT)    die "source requise ABSENTE ($2) : $1
Sans elle, aucun verdict de dimensionnement n'est etayable." ;;
    ILLISIBLE) die "source requise ILLISIBLE ($2) : $1
Le fichier existe mais n'est pas lisible par cet utilisateur -- panne
d'instrument, pas etat nominal. Relancer avec les droits de lecture." ;;
  esac
}

head1 "contexte"
say "date            : $(date -u '+%Y-%m-%dT%H:%M:%SZ')  (tout est horodate en Z)"
say "hote            : $(hostname 2>/dev/null || echo '<inconnu>')"
say "propose         : famille start = $SLOTS slot(s) x $CPUS vCPU"
say "bundle rollback : $OUT"
[ -n "$ROOT" ] && say "racine fixture  : $ROOT  (MODE TEST -- pas la machine reelle)"

# --- 1. La configuration EFFECTIVE, telle que systemd la calcule ------------
head1 "1. configuration EFFECTIVE (systemd, tous drop-ins fusionnes)"
say "Lire un seul 10-sizing.conf ne suffit pas : un autre drop-in, ou l'unite"
say "elle-meme, peut surcharger ce qu'il declare. On interroge donc systemd."

sc_show() {  # $1 = unite, $2 = propriete
  "$SYSTEMCTL" show "$1" -p "$2" --value 2>/dev/null
}

for U in coursia-runner.service coursia-waiters.service; do
  if ! "$SYSTEMCTL" show "$U" -p Id >/dev/null 2>&1; then
    die "systemd injoignable ou unite inconnue : $U
La commande 'systemctl show' a echoue. Sans la configuration effective, ce
script ne peut pas distinguer ce que les fichiers declarent de ce qui
s'applique reellement -- la distinction qui a coute 6 h 35 le 2026-09-08."
  fi
done

# Bornage explicite des formes de configuration SUPPORTEES.
# « systemctl show -p Environment » rend les Environment= INLINE. Il ne rend PAS
# le CONTENU des EnvironmentFile=, que systemd lit a l'execution : une valeur
# posee par ce biais serait INVISIBLE a env_value(), on retomberait sur le
# defaut du wrapper, et le budget lu serait faux DANS LE SENS PERMISSIF. Meme
# classe de defaut pour une valeur quotee : le decoupage par espaces la
# couperait en deux. On refuse dans les deux cas -- un verdict que l'instrument
# ne sait pas etayer ne vaut pas mieux que pas de verdict, il vaut moins.
DQ='"'
for U in coursia-runner.service coursia-waiters.service; do
  EF="$(sc_show "$U" EnvironmentFiles)"
  if [ -n "$EF" ]; then
    die "configuration NON SUPPORTEE : $U declare EnvironmentFile.
  $EF
Ce script lit l'Environment par « systemctl show -p Environment », qui ne rend
que les Environment= inline. Le contenu d'un EnvironmentFile lui est invisible :
une valeur qui y serait posee (budget, memoire, cpus) serait lue comme ABSENTE,
et le script retomberait sur le defaut du wrapper. Le verdict porterait alors
sur une valeur que le processus ne verra jamais, et l'erreur irait dans le sens
permissif. Bornage delibere : lire ces fichiers n'est pas de ce ressort."
  fi
  case "$(sc_show "$U" Environment)" in
    *"$DQ"*)
      die "configuration NON SUPPORTEE : l'Environment effectif de $U porte une
valeur quotee. env_value() decoupe sur les espaces : une valeur quotee contenant
un espace serait tronquee en silence, donc mal lue -- sans que rien ne le
signale. Refus, plutot qu'une lecture approximative." ;;
  esac
done

# Dernier argument de l'ExecStart effectif = nombre de slots.
exec_last_arg() {
  sc_show "$1" ExecStart \
    | sed -n 's/.*argv\[\]=\([^;]*\).*/\1/p' \
    | head -1 \
    | awk '{print $NF}'
}
# Valeur d'une cle dans l'Environment effectif.
env_value() {   # $1 = unite, $2 = cle
  sc_show "$1" Environment \
    | tr ' ' '\n' \
    | sed -n "s/^$2=\(.*\)$/\1/p" \
    | tail -1
}

EFF_START_N="$(exec_last_arg coursia-runner.service)"
EFF_WAIT_N="$(exec_last_arg coursia-waiters.service)"
EFF_START_MEM="$(env_value coursia-runner.service COURSIA_RUNNER_MEMORY)"
EFF_START_CPUS="$(env_value coursia-runner.service COURSIA_RUNNER_CPUS)"
EFF_WAIT_CPUS="$(env_value coursia-waiters.service COURSIA_RUNNER_WAITER_CPUS)"

# Defauts de supervise.sh quand rien ne surcharge. Verifies contre main le
# 2026-09-08 : COURSIA_RUNNER_CPUS:-3 (l.81), COURSIA_RUNNER_WAITER_CPUS:-1
# (l.118). C'est de la que vient cpus=3 : aucun drop-in vivant ne porte CPUS.
DEF_START_CPUS=3
DEF_WAIT_CPUS=1
START_CPUS_SRC="drop-in"; [ -n "$EFF_START_CPUS" ] || { EFF_START_CPUS=$DEF_START_CPUS; START_CPUS_SRC="defaut supervise.sh"; }
WAIT_CPUS_SRC="drop-in";  [ -n "$EFF_WAIT_CPUS"  ] || { EFF_WAIT_CPUS=$DEF_WAIT_CPUS;   WAIT_CPUS_SRC="defaut supervise.sh"; }

pos_int "$EFF_START_N" || die "nombre de slots « start » ineligible depuis l'ExecStart effectif (« ${EFF_START_N:-<vide>} »).
Sans lui, la somme du budget est fausse -- et une somme fausse rend « passe »."
pos_int "$EFF_WAIT_N"  || die "nombre de waiters ineligible depuis l'ExecStart effectif (« ${EFF_WAIT_N:-<vide>} »).
Un waiter non compte n'est pas un waiter absent : le total serait SOUS-estime,
donc le verdict serait faussement permissif. C'est exactement le mode de
defaillance que ce script doit refuser."
pos_int "$EFF_START_CPUS" || die "cap CPU « start » ineligible : « $EFF_START_CPUS »"
pos_int "$EFF_WAIT_CPUS"  || die "cap CPU waiter ineligible : « $EFF_WAIT_CPUS »"
[ -n "$EFF_START_MEM" ] || die "memoire par conteneur « start » introuvable dans l'Environment effectif.
Le controle doit la RECONDUIRE a l'identique. L'omettre du drop-in propose la
ferait retomber sur le defaut de supervise.sh (4g) : ce serait deplacer en
silence la variable que l'on pretend tenir fixe, et rendre le plan ininterpretable."

printf '  %-38s %s\n' "start : slots (ExecStart effectif)" "$EFF_START_N"
printf '  %-38s %s (%s)\n' "start : cpus par conteneur" "$EFF_START_CPUS" "$START_CPUS_SRC"
printf '  %-38s %s\n' "start : memoire par conteneur" "$EFF_START_MEM"
printf '  %-38s %s\n' "waiters : slots (ExecStart effectif)" "$EFF_WAIT_N"
printf '  %-38s %s (%s)\n' "waiters : cpus par conteneur" "$EFF_WAIT_CPUS" "$WAIT_CPUS_SRC"

say ""
say "  fichiers sources fusionnes par systemd (systemctl cat) :"
"$SYSTEMCTL" cat coursia-runner.service 2>/dev/null | sed -n 's/^# \(\/.*\)$/    \1/p' || true

# --- 2. Le budget du garde (fail-closed, DEUX sources dans le bon ordre) ----
head1 "2. budget du garde -- lu a la source qui fait foi"
say "Le budget a DEUX sources, et elles ne sont pas equivalentes :"
say "  a. l'Environment EFFECTIF de l'unite -- s'il porte une valeur, c'est"
say "     elle que le processus verra, et le defaut du wrapper ne s'applique"
say "     jamais (le wrapper ecrit VAR:-8, c'est-a-dire « 8 sauf si defini »)."
say "  b. le defaut du wrapper, qui ne vaut qu'en l'absence de (a)."
say "Lire (b) seul est le defaut meme que ce script doit eviter : un drop-in"
say "posant COURSIA_RUNNER_CPU_BUDGET=0 desarmerait le garde sans que le"
say "fichier du wrapper change d'un seul octet."

budget_from_wrapper() {
  # Formes acceptees : VAR:-N dans une accolade, VAR:=N, VAR=N, VAR="N"
  sed -n \
    -e 's/.*COURSIA_RUNNER_CPU_BUDGET[^}]*:[-=]\([0-9][0-9]*\)}.*/\1/p' \
    -e 's/^[^#]*COURSIA_RUNNER_CPU_BUDGET="\{0,1\}\([0-9][0-9]*\)"\{0,1\}[[:space:]]*$/\1/p' \
    "$1" | tail -1
}

BUDGET_ENV="$(env_value coursia-runner.service COURSIA_RUNNER_CPU_BUDGET)"
if [ -n "$BUDGET_ENV" ]; then
  BUDGET_RAW="$BUDGET_ENV"; BUDGET_SRC="Environment effectif (fait foi)"
else
  require_readable "$WRAPPER_START" "wrapper qui porte COURSIA_RUNNER_CPU_BUDGET"
  BUDGET_RAW="$(budget_from_wrapper "$WRAPPER_START")"; BUDGET_SRC="defaut du wrapper"
fi
if [ -z "$BUDGET_RAW" ]; then
  die "COURSIA_RUNNER_CPU_BUDGET introuvable -- ni dans l'Environment effectif,
ni sous une forme reconnue dans $WRAPPER_START.
Le budget est donc INCONNU. Il ne doit surtout pas etre lu comme « 0 » :
0 DESACTIVE le garde (supervise.sh l.206 rend 0 par defaut) et ferait passer
n'importe quelle configuration. C'est le mode de defaillance que ce script
existe pour ne pas commettre."
fi
case "$BUDGET_RAW" in *[!0-9]*) die "budget non numerique : « $BUDGET_RAW »" ;; esac
BUDGET="$BUDGET_RAW"
printf '  %-38s %s   (source : %s)\n' "COURSIA_RUNNER_CPU_BUDGET" "$BUDGET" "$BUDGET_SRC"
if [ "$BUDGET" -eq 0 ]; then
  say "  -> 0 signifie GARDE DESACTIVE (assert_cpu_budget rend 0 immediatement)."
  say "     Aucun verdict « passe » ne sera rendu : il n'y a rien a franchir."
fi

# --- 3. Ce que les processus appliquent (fichier != processus) --------------
head1 "3. fichier != processus -- la meche latente"
for U in coursia-runner.service coursia-waiters.service; do
  printf '  %-28s etat=%-10s demarre=%s\n' "$U" \
    "$("$SYSTEMCTL" is-active "$U" 2>/dev/null || echo '?')" \
    "$(sc_show "$U" ExecMainStartTimestamp)"
done
MTIME_WRAP="$(stat -c '%y' "$WRAPPER_START" 2>/dev/null | cut -d. -f1)"
printf '  %-28s %s\n' "wrapper mtime" "${MTIME_WRAP:-<indisponible>}"
say "  -> si un mtime est POSTERIEUR au demarrage de l'unite, le processus"
say "     vivant tourne sous l'ANCIEN code : le garde est arme mais latent,"
say "     et il ne se manifestera qu'au prochain redemarrage."

# --- 4. Le plafond noyau (informatif, jamais decisif) -----------------------
head1 "4. plafond noyau (informatif)"
if [ -d "$SLICE_CG" ]; then
  for F in cpu.max memory.max memory.high memory.current; do
    printf '  %-16s %s\n' "$F" "$(cat "$SLICE_CG/$F" 2>/dev/null || echo '<illisible>')"
  done
  printf '  %-44s %s\n' "memory.events       (cgroup ET descendants)" \
    "$(awk '/^max /{print $2}' "$SLICE_CG/memory.events" 2>/dev/null)"
  printf '  %-44s %s\n' "memory.events.local (ce cgroup SEUL)" \
    "$(awk '/^max /{print $2}' "$SLICE_CG/memory.events.local" 2>/dev/null)"
  say "  -> local=0 avec hierarchique>0 : la pression est AU NIVEAU DES"
  say "     CONTENEURS (cap --memory par conteneur), pas au plafond agrege."
  say ""
  say "  CE QUE CES COMPTEURS NE DISENT PAS. Ils sont CUMULATIFS depuis la"
  say "  creation du cgroup et rendus ici sans fenetre temporelle. Ils"
  say "  etablissent une STRUCTURE -- ou s'exerce la pression -- et rien de"
  say "  plus : ils n'attribuent aucun hit a un incident et n'en etablissent"
  say "  pas la cause. Dater la pression demande DEUX releves horodates et"
  say "  leur difference ; ce script n'en prend qu'un."
else
  warn "slice absente du cgroupfs ($SLICE_CG) -- section informative sautee."
fi

# --- 5. L'arithmetique du garde ---------------------------------------------
head1 "5. arithmetique du garde (assert_cpu_budget)"
mul() { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.2f", a*b}'; }
sum() { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.2f", a+b}'; }
over() { awk -v t="$1" -v b="$2" 'BEGIN{exit !(t>b)}'; }   # vrai si total > budget

CUR_START="$(mul "$EFF_START_N" "$EFF_START_CPUS")"
CUR_WAIT="$(mul "$EFF_WAIT_N" "$EFF_WAIT_CPUS")"
CUR_TOT="$(sum "$CUR_START" "$CUR_WAIT")"
NEW_START="$(mul "$SLOTS" "$CPUS")"
NEW_TOT="$(sum "$NEW_START" "$CUR_WAIT")"

verdict_of() {
  if [ "$BUDGET" -eq 0 ]; then printf 'garde desactive (budget=0)'
  elif over "$1" "$BUDGET";  then printf '-> REFUSE'
  else                            printf '-> passe'
  fi
}
printf '  %-40s %s\n' "actuel  : start $EFF_START_N x $EFF_START_CPUS" "$CUR_START"
printf '  %-40s %s\n' "actuel  : waiters $EFF_WAIT_N x $EFF_WAIT_CPUS" "$CUR_WAIT"
printf '  %-40s %s / %s  %s\n' "actuel  : TOTAL" "$CUR_TOT" "$BUDGET" "$(verdict_of "$CUR_TOT")"
printf '  %-40s %s\n' "propose : start $SLOTS x $CPUS" "$NEW_START"
printf '  %-40s %s / %s  %s\n' "propose : TOTAL" "$NEW_TOT" "$BUDGET" "$(verdict_of "$NEW_TOT")"

if [ "$BUDGET" -gt 0 ] && over "$NEW_TOT" "$BUDGET"; then
  die "la configuration proposee serait refusee par le garde ($NEW_TOT > $BUDGET).
Un dry-run qui propose un demarrage impossible n'a aucune valeur : baisser
--slots ou --cpus, ou arbitrer le budget en connaissance de cause."
fi
if [ "$BUDGET" -gt 0 ]; then
  say "  -> la configuration proposee FRANCHIT le garde. Ce n'est pas une"
  say "     promesse de performance : un cap --cpus DECLARE n'est pas du temps"
  say "     CPU CONSOMME, et le noyau borne deja la slice par cpu.max."
fi

# --- 6. Bundle de preuve (toute defaillance est FATALE) ---------------------
head1 "6. capture du bundle (octets VIVANTS)"
mkdir -p "$OUT/live" || die "impossible de creer $OUT/live"
MANIFEST="$OUT/manifest.tsv"
: > "$MANIFEST" || die "impossible d'ecrire $MANIFEST"
printf 'role\tchemin\tetat\tmode\n' >> "$MANIFEST"

# La CIBLE : le seul fichier que le controle modifierait.
TARGET="$DROPIN_START"
TARGET_STATE="$(state_of "$TARGET")"
[ "$TARGET_STATE" = "ILLISIBLE" ] && die "la cible du controle est ILLISIBLE : $TARGET
Impossible de garantir un rollback vers un contenu qu'on ne peut pas lire.
Aucun bundle ne sera produit -- un rollback incomplet est pire qu'aucun."

capture() {   # $1 = chemin, $2 = role, $3 = requis(0/1)
  local st mode dst
  st="$(state_of "$1")"
  mode="$(stat -c '%a' "$1" 2>/dev/null || printf '-')"
  if [ "$st" = "PRESENT" ]; then
    dst="$OUT/live${1#"$ROOT"}"
    mkdir -p "$(dirname "$dst")" || die "mkdir echoue pour $dst"
    cp -p "$1" "$dst" || die "COPIE ECHOUEE ($2) : $1
Le bundle serait incomplet. Un bundle incomplet presente comme complet est le
defaut que ce script existe pour ne pas commettre : on s'arrete ici."
    cmp -s "$1" "$dst" || die "COPIE DIVERGENTE ($2) : $1 != $dst"
  elif [ "$3" -eq 1 ]; then
    die "source requise $st ($2) : $1"
  fi
  printf '%s\t%s\t%s\t%s\n' "$2" "${1#"$ROOT"}" "$st" "$mode" >> "$MANIFEST"
  printf '  %-9s %-22s %s\n' "$st" "$2" "${1#"$ROOT"}"
}

capture "$TARGET"        "CIBLE"            0   # peut legitimement etre ABSENT
capture "$WRAPPER_START" "preuve-wrapper"   1
capture "$UNIT_START"    "preuve-unite"     1
capture "$UNIT_WAIT"     "preuve-unite-w"   0
capture "$DROPIN_WAIT"   "preuve-dropin-w"  0

{
  printf '# etat au moment de la capture -- %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  for U in coursia-runner.service coursia-waiters.service; do
    printf '%s: is-active=%s ExecMainStart=%s ExecStart=%s\n' "$U" \
      "$("$SYSTEMCTL" is-active "$U" 2>/dev/null || echo '?')" \
      "$(sc_show "$U" ExecMainStartTimestamp)" "$(sc_show "$U" ExecStart)"
  done
  printf 'budget=%s start=%sx%s mem=%s waiters=%sx%s\n' \
    "$BUDGET" "$EFF_START_N" "$EFF_START_CPUS" "$EFF_START_MEM" \
    "$EFF_WAIT_N" "$EFF_WAIT_CPUS"
} > "$OUT/state-before.txt" || die "ecriture de state-before.txt echouee"
say "  etat consigne : $OUT/state-before.txt"
say ""
say "  NOTE -- seule la ligne « CIBLE » sera restauree par le rollback. Les"
say "  lignes « preuve-* » sont capturees pour la forensique : le controle ne"
say "  les modifie pas, donc les reinstaller serait un geste hors perimetre."

# --- 7. Le drop-in propose ---------------------------------------------------
head1 "7. drop-in propose (dans le bundle, PAS dans /etc)"

# systemd fusionne les drop-ins dans l'ordre LEXICOGRAPHIQUE de leur nom. Un
# drop-in lu apres la cible ecraserait ce qu'elle declare : proposer un fichier
# qu'un autre surcharge, c'est proposer un no-op tout en rendant un verdict
# affirmatif. On enumere les drop-ins EFFECTIFS et on refuse s'il en existe un
# qui soit lu apres la cible.
TARGET_BASE="$(basename "$TARGET")"
LATER=""
for D in $(sc_show coursia-runner.service DropInPaths); do
  DB="$(basename "$D")"
  [ "$DB" = "$TARGET_BASE" ] && continue
  if [ "$(printf '%s\n%s\n' "$TARGET_BASE" "$DB" | LC_ALL=C sort | tail -1)" = "$DB" ]; then
    LATER="$LATER $D"
  fi
done
if [ -n "$LATER" ]; then
  die "drop-in(s) lus APRES la cible, donc susceptibles de l'ecraser :$LATER
systemd fusionne les drop-ins par ordre lexicographique des noms de fichiers.
« $TARGET_BASE » etant lu avant eux, ce que la proposition declare pourrait
etre surcharge -- et le verdict porterait sur une configuration qui ne
s'appliquerait pas. Refus : la resolution (renommer la cible, ou retirer la
surcharge) est une decision de configuration, pas un ajustement de ce script."
fi

# Le drop-in propose porte exactement trois directives. Si la cible vivante en
# porte d'autres, l'ecrire A LA PLACE les perdrait en silence. Les reconduire
# serait un choix de configuration, pas une transformation mecanique que ce
# script puisse s'autoriser.
if [ "$TARGET_STATE" = "PRESENT" ]; then
  EXTRA="$(sed -e 's/#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' "$TARGET" \
    | grep -v '^$' \
    | grep -v '^\[Service\]$' \
    | grep -v '^Environment=COURSIA_RUNNER_MEMORY=' \
    | grep -v '^Environment=COURSIA_RUNNER_CPUS=' \
    | grep -v '^ExecStart=' || true)"
  if [ -n "$EXTRA" ]; then
    die "la cible vivante porte des directives que la proposition ne reconduit pas :
$EXTRA
Le drop-in propose serait ecrit a la place du fichier existant : ces lignes
seraient perdues sans que rien ne l'indique. Refus -- statuer sur leur sort est
une decision deliberee, pas un effet de bord d'un controle de dimensionnement."
  fi
fi

mkdir -p "$OUT/proposed" || die "mkdir $OUT/proposed echoue"
PROP="$OUT/proposed/10-sizing.conf"
{
  printf '# Controle de dimensionnement borne -- protocole #15095, « un slot\n'
  printf '# avant plusieurs ». Genere par dryrun-sizing-control.sh le %s.\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '#\n'
  printf '# DEUX facteurs de capacite bougent ici : le nombre de slots et le cap\n'
  printf '# CPU par slot. La MEMOIRE est reconduite a sa valeur EFFECTIVE lue sur\n'
  printf '# la machine (%s), ce qui retire une troisieme variable -- sans rendre\n' "$EFF_START_MEM"
  printf '# le plan univarie pour autant. Ce controle tranche donc un BINAIRE (la\n'
  printf '# famille demarre-t-elle, un slot reclame-t-il un job) et n%s attribue\n' "'"
  printf '# AUCUNE difference de debit a l%s un ou l%s autre des deux facteurs.\n' "'" "'"
  printf '#\n'
  printf '# Budget : %s x %s (start) + %s x %s (waiters) = %s / %s vCPU.\n' \
    "$SLOTS" "$CPUS" "$EFF_WAIT_N" "$EFF_WAIT_CPUS" "$NEW_TOT" "$BUDGET"
  printf '[Service]\n'
  printf 'Environment=COURSIA_RUNNER_MEMORY=%s\n' "$EFF_START_MEM"
  printf 'Environment=COURSIA_RUNNER_CPUS=%s\n' "$CPUS"
  printf 'ExecStart=\n'
  printf 'ExecStart=/usr/local/bin/coursia-runner-start.sh %s\n' "$SLOTS"
} > "$PROP" || die "ecriture du drop-in propose echouee"
say "  ecrit : $PROP"
if [ "$TARGET_STATE" = "PRESENT" ]; then
  say "  --- diff vivant -> propose ---"
  diff -u "$TARGET" "$PROP" | sed 's/^/  /' || true
else
  say "  (cible ABSENTE : le controle CREERAIT ce fichier)"
fi

# --- 8. Le rollback, borne aux cibles reellement changees -------------------
head1 "8. rollback (borne a la CIBLE, metadonnees conservees)"
RB="$OUT/rollback.sh"
# Deux chemins, et les confondre est un defaut de surete :
#   TARGET_ABS  = chemin CANONIQUE (racine retiree) -- c'est la clef sous
#                 laquelle les octets vivent dans le bundle ;
#   TARGET_DEST = destination REELLE, telle que le controle l'a inspectee.
# En production ROOT est vide, les deux coincident et rien ne change. Sous une
# racine de test, les confondre faisait ecrire le rollback vers le VRAI /etc :
# un rollback qui restaure ailleurs que la ou il a mesure est pire qu'absent.
TARGET_ABS="${TARGET#"$ROOT"}"
TARGET_DEST="$TARGET"
TARGET_DIR_DEST="$(dirname "$TARGET_DEST")"
DIR_STATE="$(state_of "$(dirname "$TARGET")")"
TARGET_MODE="$(stat -c '%a' "$TARGET" 2>/dev/null || printf '0644')"
TARGET_OWN="$(stat -c '%U:%G' "$TARGET" 2>/dev/null || printf 'root:root')"

# Le rollback rend des OCTETS et des METADONNEES. Trois formes sortent de ce
# qu'il sait restituer a l'identique. On les refuse : un rollback qui restaure
# approximativement est pire qu'un refus, parce qu'il a l'air d'avoir marche.
if [ -L "$TARGET" ]; then
  die "la cible est un LIEN SYMBOLIQUE : $TARGET
« install -D » ecrirait a travers le lien, donc dans sa cible ; le rollback
reposerait ensuite un fichier reel la ou il y avait un lien. Non supporte."
fi
if [ -L "$(dirname "$TARGET")" ]; then
  die "le repertoire .d de la cible est un LIEN SYMBOLIQUE : $(dirname "$TARGET")
Meme raison : ni le controle ni le rollback ne raisonnent a travers un lien."
fi
if [ "$TARGET_STATE" = "PRESENT" ]; then
  case "$(ls -ld "$TARGET" 2>/dev/null | cut -c1-11)" in
    *+) die "la cible porte des ACL etendues : $TARGET
Le rollback ne restitue que le mode et le proprietaire. Restaurer une cible
ACL-ee avec le seul mode rendrait un fichier d'apparence correcte et de droits
differents -- un rollback qui ment sur ce qu'il a fait. Non supporte." ;;
  esac
fi
{
  printf '#!/usr/bin/env bash\n'
  printf '# Rollback genere le %s.\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '# Il ne touche QUE la cible que le controle modifie, et il ne redemarre\n'
  printf '# RIEN : le redemarrage est une decision separee, prise par la lane qui\n'
  printf '# porte le parc.\n'
  printf 'set -euo pipefail\n'
  printf 'B="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/live"\n'
  if [ "$TARGET_STATE" = "PRESENT" ]; then
    printf '[ -r "$B%s" ] || { echo "octets captures introuvables" >&2; exit 1; }\n' "$TARGET_ABS"
    printf 'install -D -m %s "$B%s" "%s"\n' "$TARGET_MODE" "$TARGET_ABS" "$TARGET_DEST"
    printf 'chown %s "%s"\n' "$TARGET_OWN" "$TARGET_DEST"
    printf 'echo "  restaure %s (mode %s, %s)"\n' "$TARGET_DEST" "$TARGET_MODE" "$TARGET_OWN"
  else
    printf '# La cible etait ABSENTE avant le controle : la restaurer, c est la SUPPRIMER.\n'
    printf 'rm -f "%s"\n' "$TARGET_DEST"
    printf 'echo "  supprime %s (absent avant le controle)"\n' "$TARGET_DEST"
    if [ "$DIR_STATE" = "ABSENT" ]; then
      printf '# Le repertoire .d n existait pas non plus : le retirer s il est vide.\n'
      printf 'rmdir "%s" 2>/dev/null || true\n' "$TARGET_DIR_DEST"
    fi
  fi
  printf 'systemctl daemon-reload\n'
  printf 'echo "rollback applique. AUCUNE unite redemarree -- geste separe et delibere."\n'
} > "$RB" || die "ecriture du rollback echouee"
chmod 0755 "$RB" || die "chmod du rollback echoue"
say "  ecrit  : $RB"
say "  cible  : $TARGET_DEST  (etat avant controle : $TARGET_STATE)"
say "  action : $([ "$TARGET_STATE" = PRESENT ] && echo "restaurer les octets, mode $TARGET_MODE, $TARGET_OWN" || echo "SUPPRIMER le fichier cree")"

# --- 9. Auto-verification du bundle -----------------------------------------
head1 "9. auto-verification du bundle"
BAD=0
while IFS="$(printf '\t')" read -r role path st mode; do
  [ "$role" = "role" ] && continue
  [ "$st" = "PRESENT" ] || continue
  if [ ! -r "$OUT/live$path" ]; then
    warn "manquant dans le bundle : $path"; BAD=$((BAD+1)); continue
  fi
  cmp -s "$ROOT$path" "$OUT/live$path" || { warn "divergent : $path"; BAD=$((BAD+1)); }
done < "$MANIFEST"
[ -s "$PROP" ] || { warn "drop-in propose vide"; BAD=$((BAD+1)); }
[ -x "$RB" ]   || { warn "rollback non executable"; BAD=$((BAD+1)); }
[ "$BAD" -eq 0 ] || die "bundle INCOMPLET ($BAD anomalie(s)). Ne pas s'en servir."
say "  toutes les entrees PRESENT du manifeste sont capturees et identiques."

# --- 10. Ce qu'il faudrait executer -- imprime, jamais execute --------------
head1 "10. commandes d'application -- A RELIRE, PAS A COPIER SANS ARBITRAGE"
say "  # Aucune des lignes ci-dessous n'a ete executee par ce script."
say "  #"
say "  # install -D -m 0644 $PROP \\"
say "  #                    $TARGET_ABS"
say "  # systemctl daemon-reload"
say "  # systemctl start coursia-runner.service"
say "  #"
say "  # Puis verifier que le garde a laisse passer :"
say "  #   journalctl -u coursia-runner.service --since '-5min' | grep 'budget CPU'"
say "  # La ligne de SUCCES est « budget CPU inter-familles : N / M vCPU »."
say "  # Au 2026-09-08 elle n'avait JAMAIS ete emise sur cette machine : sa"
say "  # premiere apparition est le vrai critere de reussite du controle."
say "  #"
say "  # Rollback : $RB"

# --- 11. Temoins a relever pendant le controle ------------------------------
head1 "11. temoins a relever pendant le controle"
cat <<'WITNESS'
  Un cycle de conteneur court n'est PAS en soi une pathologie. Le 2026-09-08,
  487 intervalles inter-cycles sous 10 s ont ete mesures pendant que le parc
  FONCTIONNAIT. Le chemin rc=0 de slot_loop() est un `sleep 2` FIXE
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

  PIEGES D'INSTRUMENT mesures le 2026-09-08, a connaitre avant tout releve :
    - depuis Ubuntu, `docker` repond « docker-desktop », PAS docker-ce -- y
      compris via DOCKER_HOST=unix:///var/run/docker.sock. Un `docker inspect`
      lance ici decrit le MAUVAIS moteur. Seule surface sure : le cgroupfs.
    - `/proc/uptime` et `uptime -s` sont inutilisables : des centaines
      d'evenements « Clock change detected » par boot, et un ecart mesure de
      3 min 12 s. Un boot se date par `journalctl --list-boots`.
    - un refus deterministe rejoue a CHAQUE boot : compter les refus PAR BOOT,
      jamais en cumul, sinon la bascule latent -> actif reste invisible.
WITNESS

head1 "fin"
say "Aucun fichier de /etc ni de /usr/local/bin n'a ete modifie par ce script."
say "Bundle verifie et complet : $OUT"
exit 0
