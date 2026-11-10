#!/usr/bin/env bash
# Dry-run NON MUTANT du controle de dimensionnement ai-01 (#15091, protocole
# #15095 « un slot avant plusieurs »).
#
# CE QUE CE SCRIPT NE FAIT JAMAIS
# -------------------------------
#   - il n'ecrit rien dans /etc ni dans /usr/local/bin ;
#   - il n'appelle systemctl qu'avec `show` / `cat` / `is-active` ;
#   - il ne redemarre ni docker ni WSL ;
#   - il ne touche a aucun quota de slice ;
#   - il n'ecrit RIEN hors de son bundle, a UNE exception nommee : l'etat du
#     temoin de throttling par delta (section 4bis-ter), qui vit hors du depot
#     et hors de /etc -- COURSIA_DRYRUN_STATE, sinon %LOCALAPPDATA%\Coursia,
#     sinon /var/lib/coursia. Cet etat ne fait que dater une lecture ; il ne
#     configure rien.
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

# Seuil du temoin de throttling : secondes de throttling cumulees tolerees
# sur 24 h de fenetre. 60 s est l'ordre de grandeur arbitre par le
# coordinateur (dispatch `ai01-c2721-23037-budget`) : il ne s'agit pas d'un
# seuil de performance, mais du seuil AU-DELA duquel le noyau a refuse du
# temps CPU -- c'est-a-dire ou la declaration de budget cesse d'etre
# theorique. Surchargeable pour les tests.
THROTTLE_BUDGET_SPD="${COURSIA_DRYRUN_THROTTLE_BUDGET_SPD:-60}"
THROTTLE_ALERT=0
THROTTLE_VERDICT="INDISPONIBLE"
THROTTLE_DELTA_VERDICT="INDISPONIBLE"

# Etat du temoin de throttling PAR DELTA (#23051, point 2). Le compteur cumule
# de la slice a une sensibilite qui DECROIT avec son age : sur une slice de
# plusieurs semaines, une rafale de 60 s survenue aujourd'hui passe sous un
# seuil proportionnel a l'age. Le delta entre deux lectures datees garde une
# fenetre courte, donc une sensibilite constante.
#
# Cette lecture anterieure est le SEUL fichier que ce script ecrit hors de son
# bundle -- et il ne vit pas dans le depot : c'est de l'etat de machine.
#   - COURSIA_DRYRUN_STATE impose le repertoire (tests, machines non standard) ;
#   - sinon %LOCALAPPDATA%\Coursia sous Windows, /var/lib/coursia sous Linux.
# Aucun etat n'est ecrit quand aucune des deux formes n'est disponible : le
# temoin rend alors INDETERMINE, il ne devine pas.
STATE_DIR="${COURSIA_DRYRUN_STATE:-}"
if [ -z "$STATE_DIR" ]; then
  if [ -n "${LOCALAPPDATA:-}" ]; then
    STATE_DIR="$LOCALAPPDATA/Coursia"
  elif [ -d /var/lib ]; then
    STATE_DIR="/var/lib/coursia"
  fi
fi
THROTTLE_STATE=""
[ -n "$STATE_DIR" ] && THROTTLE_STATE="$STATE_DIR/dryrun-sizing-throttle.state"

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
  COURSIA_DRYRUN_UPTIME_S    uptime de l'hote, en secondes (borne SUPERIEURE
                             de l'age de la slice). Sans cette variable, le
                             mode fixture ne dispose d'aucune borne
                             superieure : le temoin peut alors conclure «
                             ALERTE CERTAINE », jamais « passe ».
  COURSIA_DRYRUN_THROTTLE_BUDGET_SPD
                             secondes de throttling tolerees par 24 h
                             (defaut : 60). Sert au temoin de la section 4bis.

Codes de sortie :
  0  le controle est complet et la proposition franchit le garde
  1  REFUS : une source requise manque, ou la proposition serait refusee
  3  ALERTE : le temoin de throttling (4bis) contredit la declaration de
     budget. distinct de 1 : le garde n'a pas refuse la proposition, c'est
     la MESURE du noyau qui parle. L'alerte PRIME sur un refus concomitant :
     si le temoin a alerte, la sortie est 3 meme si une autre source a refuse
     ensuite (le motif du refus reste imprime).
USAGE
}

say()   { printf '%s\n' "$*"; }
head1() { printf '\n=== %s ===\n' "$*"; }
warn()  { printf 'ATTENTION: %s\n' "$*" >&2; }
# `die` respecte la priorite du temoin : si le noyau a refuse du temps CPU
# (section 4bis), c'est la MESURE qui parle, et elle passe devant un refus
# concomitant de configuration. Sans cela, un refus survenu AVANT la fin du
# script porterait la sortie 1 et masquerait l'alerte -- le code de sortie
# dirait « refus de configuration » alors qu'une mesure contredit la
# declaration. Le motif du refus reste imprime : rien n'est cache.
die() {
  printf 'REFUS: %s\n' "$*" >&2
  if [ "${THROTTLE_ALERT:-0}" -eq 1 ]; then
    printf 'TEMOIN THROTTLING : %s -- la MESURE contredit la declaration (section 4bis).\n' \
      "${THROTTLE_VERDICT:-ALERTE}" >&2
    printf 'Sortie 3 : l alerte prime sur le refus.\n' >&2
    exit 3
  fi
  exit 1
}

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

# --- 4bis. Le temoin de throttling (ce que le noyau a REELLEMENT refuse) ---
#
# CE QUE CE TEMOIN MESURE, ET CE QU'IL NE MESURE PAS.
#
# `cpu.stat` de la slice porte deux compteurs CUMULATIFS depuis la creation du
# cgroup : `nr_throttled` (periodes pendant lesquelles la slice a ete
# THROTTLEE) et `throttled_usec` (microsecondes cumulees de throttling).
# Throttler, c'est le noyau qui RETIRE du temps CPU : la slice a demande plus
# que son plafond `cpu.max` ne pouvait servir.
#
# C'est le seul signal qui dise si un budget DECLARE est realiste. Une
# declaration est un cap ; le throttling dit si le cap a morde. Un budget
# declare de 40 vCPU sur une slice de 32 coeurs ne se prouve pas en comparant
# des nombres : il se prouve en montrant que la slice n'a pas ete throttlee.
#
# LA FENETRE, ET POURQUOI ELLE EST BORNEE DE DEUX COTES.
#
# Un taux exige une fenetre, et l'age de la slice n'est pas lisible : cgroup
# v2 n'expose aucune date de creation. Le PIEGE deja note dans ce script vaut
# aussi ici -- `/proc/uptime` et `journalctl --list-boots` ne concordent pas
# sur cette machine (ecart mesure de 22 min le 2026-10-28, a cause des
# « Clock change detected » du WSL). Deux bornes sont donc employees :
#
#   W_LO = nr_periods x periode -- duree pendant laquelle la slice a ete
#           COMPTEE. Une slice ne peut etre comptee que dans des periodes
#           ecoulees, donc W_LO <= age REEL : c'est une borne INFERIEURE.
#   W_HI = uptime de l'hote      -- la slice est nee apres le boot, donc
#           age REEL <= W_HI : c'est une borne SUPERIEURE.
#
# L'age reel est entre les deux. Ce que cela autorise, et ce que cela
# n'autorise pas :
#
#   - « PASSE » exige T <= allocation(W_LO). L'age reel etant >= W_LO, son
#     allocation est >= celle de W_LO : le PASS est donc SOUND.
#   - « ALERTE CERTAINE » : T > allocation(W_HI) -- meme la borne la plus
#     generouse est depassee, l'alerte est etablie.
#   - entre les deux, l'alerte est INCERTAINE : elle est poussee quand meme,
#     parce que l'orientation prudente est d'alerter, mais elle est nommee
#     comme telle -- une alerte qui pretend etre certaine quand elle ne l'est
#     pas reproduirait exactement le defaut que ce script combat.
#
# CE QUE LA MESURE NE DISE PAS : elle ne dit pas QUEL conteneur a consomme le
# temps, ni quand. La ligne « slots » ci-dessous est informative : elle
# rattache le throttling aux slots individuels, la ou il se produit.
head1 "4bis. temoin de throttling (CPU)"
THR_STAT="$SLICE_CG/cpu.stat"
if [ ! -d "$SLICE_CG" ]; then
  warn "slice absente du cgroupfs ($SLICE_CG) -- temoin de throttling INDISPONIBLE."
  say "  TEMOIN THROTTLING : INDISPONIBLE (pas de slice) -- AUCUN verdict rendu."
  say "  TEMOIN THROTTLING (delta) : INDETERMINE (meme cause -- rien a dater)."
elif [ ! -r "$THR_STAT" ]; then
  warn "cpu.stat absent ou illisible ($THR_STAT) -- temoin de throttling INDETERMINE."
  say "  TEMOIN THROTTLING : INDETERMINE (cpu.stat absent ou illisible)."
  say "  TEMOIN THROTTLING (delta) : INDETERMINE (meme cause -- rien a dater)."
  say "  -> une panne d'instrument ne se confond pas avec une absence de"
  say "     throttling : aucun « passe » n'est rendu ici."
else
  THR_NR="$(awk '/^nr_throttled /{print $2; exit}' "$THR_STAT" 2>/dev/null)"
  THR_US="$(awk '/^throttled_usec /{print $2; exit}' "$THR_STAT" 2>/dev/null)"
  THR_PER="$(awk '/^nr_periods /{print $2; exit}' "$THR_STAT" 2>/dev/null)"
  THR_USE="$(awk '/^usage_usec /{print $2; exit}' "$THR_STAT" 2>/dev/null)"
  PERIOD_US="$(awk '{print $2; exit}' "$SLICE_CG/cpu.max" 2>/dev/null)"

  is_uint() { case "${1:-}" in ''|*[!0-9]*) return 1 ;; esac; return 0; }
  if ! is_uint "$THR_US"; then
    warn "throttled_usec illisible ($THR_STAT) -- temoin de throttling INDETERMINE."
    say "  TEMOIN THROTTLING : INDETERMINE (throttled_usec illisible)."
  elif ! is_uint "$PERIOD_US" || [ "$PERIOD_US" -le 0 ]; then
    warn "periode de la slice illisible (cpu.max) -- temoin de throttling INDETERMINE."
    say "  TEMOIN THROTTLING : INDETERMINE (periode de la slice inconnue)."
  else
    if [ -n "${COURSIA_DRYRUN_UPTIME_S:-}" ]; then
      W_HI_S="$COURSIA_DRYRUN_UPTIME_S"
    elif [ -n "$ROOT" ]; then
      W_HI_S=""      # fixture : pas d'horloge hote, pas de borne superieure
    else
      W_HI_S="$(awk '{print int($1)}' /proc/uptime 2>/dev/null)"
    fi
    is_uint "$W_HI_S" || W_HI_S=""

    W_LO_S=""
    ALLOC_LO=""
    # La borne INFERIEURE (fenetre minimale) exige `nr_periods`. S'il est
    # illisible, aucune borne inferieure n'existe : le « passe » devient
    # IMPOSSIBLE a etablir (une borne superieure ne suffirait pas -- elle
    # donnerait un PASS non sound). Le temoin rend alors INDETERMINE plutot
    # que de crier au throttling sur une panne d'instrument.
    if is_uint "$THR_PER"; then
      W_LO_S="$(awk -v p="$THR_PER" -v q="$PERIOD_US" 'BEGIN{printf "%.1f", p*q/1e6}')"
      ALLOC_LO="$(awk -v s="$THROTTLE_BUDGET_SPD" -v w="$W_LO_S" 'BEGIN{printf "%.2f", s*w/86400}')"
    fi
    THR_S="$(awk -v u="$THR_US" 'BEGIN{printf "%.2f", u/1e6}')"
    ALLOC_HI=""
    [ -n "$W_HI_S" ] && ALLOC_HI="$(awk -v s="$THROTTLE_BUDGET_SPD" -v w="$W_HI_S" 'BEGIN{printf "%.2f", s*w/86400}')"

    printf '  %-22s %s\n' "nr_throttled" "${THR_NR:-<absent>}"
    printf '  %-22s %s\n' "throttled_usec" "${THR_US:-<absent>}  (${THR_S} s cumulees)"
    printf '  %-22s %s\n' "nr_periods" "${THR_PER:-<absent>}"
    printf '  %-22s %s\n' "usage_usec" "${THR_USE:-<absent>}"
    printf '  %-22s %s\n' "periode (cpu.max)" "${PERIOD_US} us"
    if [ -n "$W_LO_S" ]; then
      printf '  %-22s %s s  %s\n' "fenetre minimale" "$W_LO_S" "(borne INFERIEURE de l'age de la slice)"
    else
      printf '  %-22s %s\n' "fenetre minimale" "INDETERMINEE (nr_periods illisible)"
    fi
    if [ -n "$W_HI_S" ]; then
      printf '  %-22s %s s  %s\n' "fenetre maximale" "$W_HI_S" "(uptime de l'hote -- borne SUPERIEURE)"
    else
      printf '  %-22s %s\n' "fenetre maximale" "INDETERMINEE (pas d'uptime exploitable)"
    fi
    printf '  %-22s %s s / %s h\n' "allocation" "$THROTTLE_BUDGET_SPD" "24"
    [ -n "$ALLOC_LO" ] && printf '  %-22s %s s\n' "  sur fenetre min" "$ALLOC_LO"
    [ -n "$ALLOC_HI" ] && printf '  %-22s %s s\n' "  sur fenetre max" "$ALLOC_HI"

    # Le verdict, dans cet ordre : la borne la plus generouse d'abord (alerte
    # certaine), puis la borne la plus stricte (passe sound).
    if [ -n "$ALLOC_HI" ] && awk -v t="$THR_S" -v a="$ALLOC_HI" 'BEGIN{exit !(t>a)}'; then
      THROTTLE_VERDICT="ALERTE CERTAINE"
      THROTTLE_ALERT=1
    elif [ -n "$ALLOC_LO" ] && awk -v t="$THR_S" -v a="$ALLOC_LO" 'BEGIN{exit !(t>a)}'; then
      THROTTLE_VERDICT="ALERTE INCERTAINE"
      THROTTLE_ALERT=1
    elif [ -n "$ALLOC_LO" ]; then
      THROTTLE_VERDICT="passe"
    else
      THROTTLE_VERDICT="INDETERMINE (fenetre minimale inconnue -- aucun « passe » possible)"
    fi
    say "  TEMOIN THROTTLING : $THROTTLE_VERDICT"
    case "$THROTTLE_VERDICT" in
      ALERTE*)
        say "  -> le noyau a refuse du temps CPU. La declaration de budget est"
        say "     contredite par la MESURE : ce n'est pas une hypothese."
        ;;
      passe)
        say "  -> la slice n'a pas ete throttlee au-dela du seuil de"
        say "     ${THROTTLE_BUDGET_SPD} s / 24 h. La declaration de budget"
        say "     n'est PAS contredite par la mesure. Cela ne prouve pas"
        say "     qu'elle est optimale -- cela etablit qu'elle n'est pas"
        say "     contredite par le noyau."
        ;;
    esac

    # --- 4bis-ter. Le meme temoin, mais PAR DELTA ---------------------------
    #
    # Le verdict ci-dessus compare un compteur CUMULE a une allocation
    # proportionnelle a l'age de la slice : il reste sound (une slice ne peut
    # pas avoir ete comptee plus longtemps que son age), mais sa sensibilite
    # DECROIT avec l'age. Le delta entre deux lectures datees garde une fenetre
    # bornee, donc un seuil qui ne se dilue pas. Le cumule reste comme borne de
    # long terme : les deux sont imprimes, aucun ne remplace l'autre.
    #
    # TROIS ETATS, comme le cumule -- un instrument en panne ne rend jamais
    # « passe » :
    #   passe            le delta mesure est sous l'allocation de la fenetre
    #   ALERTE CERTAINE  le delta depasse l'allocation de la fenetre (la
    #                    fenetre du delta est EXACTE : deux lectures datees,
    #                    aucune borne a encadrer)
    #   INDETERMINE      pas d'etat anterieur, etat illisible, horloge non
    #                    monotone, ou compteurs remis a zero (slice recreee)
    _now="$(date -u +%s)"
    case "$_now" in ''|*[!0-9]*) _now="" ;; esac
    _delta_state=""
    # Remise a vide : la valeur initiale « INDISPONIBLE » ne doit pas etre
    # confondue avec un verdict rendu par la chaine ci-dessous, sans quoi le
    # calcul serait saute et le temoin afficherait un etat qu'il n'a pas etabli.
    THROTTLE_DELTA_VERDICT=""
    if [ -z "$THROTTLE_STATE" ]; then
      THROTTLE_DELTA_VERDICT="INDETERMINE (aucun repertoire d'etat : ni COURSIA_DRYRUN_STATE, ni LOCALAPPDATA, ni /var/lib)"
    elif [ ! -r "$THROTTLE_STATE" ]; then
      THROTTLE_DELTA_VERDICT="INDETERMINE (premiere lecture -- aucun etat anterieur a comparer)"
    elif [ -z "$_now" ]; then
      THROTTLE_DELTA_VERDICT="INDETERMINE (horodatage courant illisible)"
    else
      # Format : <epoch> <nr_throttled> <throttled_usec>
      _t0=""; _n0=""; _u0=""
      read -r _t0 _n0 _u0 < "$THROTTLE_STATE" 2>/dev/null || true
      if [ -z "$_t0" ] || [ -z "$_u0" ]; then
        THROTTLE_DELTA_VERDICT="INDETERMINE (etat anterieur vide ou incomplet)"
      else
        case "$_t0$_u0" in
          *[!0-9]*) THROTTLE_DELTA_VERDICT="INDETERMINE (etat anterieur illisible : « $(head -c 80 "$THROTTLE_STATE" 2>/dev/null | tr '\n' ' ') »)" ;;
        esac
      fi
      if [ -z "$THROTTLE_DELTA_VERDICT" ]; then
        _dw=$((_now - _t0))
        _dt=$((THR_US - _u0))
        if [ "$_dw" -le 0 ]; then
          THROTTLE_DELTA_VERDICT="INDETERMINE (horloge non monotone : fenetre de ${_dw} s)"
        elif [ "$_dt" -lt 0 ]; then
          THROTTLE_DELTA_VERDICT="INDETERMINE (compteurs remis a zero : la slice a ete recreee)"
        else
          _alloc="$(awk -v s="$THROTTLE_BUDGET_SPD" -v w="$_dw" 'BEGIN{printf "%.2f", s*w/86400}')"
          _dt_s="$(awk -v u="$_dt" 'BEGIN{printf "%.2f", u/1e6}')"
          _delta_state="fenetre ${_dw} s ; delta ${_dt_s} s ; allocation ${_alloc} s"
          if awk -v t="$_dt_s" -v a="$_alloc" 'BEGIN{exit !(t>a)}'; then
            THROTTLE_DELTA_VERDICT="ALERTE CERTAINE"
            THROTTLE_ALERT=1
            # Le refus eventuel doit porter la mesure qui a parle : le delta est
            # la lecture la plus sensible des deux.
            case "$THROTTLE_VERDICT" in
              passe) THROTTLE_VERDICT="ALERTE CERTAINE (delta)" ;;
            esac
          else
            THROTTLE_DELTA_VERDICT="passe"
          fi
        fi
      fi
    fi
    say "  TEMOIN THROTTLING (delta) : $THROTTLE_DELTA_VERDICT"
    [ -n "$_delta_state" ] && say "    $_delta_state"
    case "$THROTTLE_DELTA_VERDICT" in
      passe)
        say "  -> sur cette fenetre, le noyau n'a pas refuse plus que"
        say "     l'allocation : la declaration n'est pas contredite RECEMMENT."
        ;;
      ALERTE*)
        say "  -> sur cette fenetre, le noyau a refuse du temps CPU au-dela de"
        say "     l'allocation. La fenetre du delta est exacte : ce n'est pas une"
        say "     borne, c'est une mesure."
        ;;
      INDETERMINE*)
        say "  -> aucun « passe » n'est rendu ici : l'absence de comparaison ne"
        say "     prouve pas l'absence de throttling."
        ;;
    esac

    # Ecriture de l'etat : le rend POSSIBLE pour la lecture suivante. Un echec
    # d'ecriture degrade le temoin suivant en INDETERMINE, il ne rend pas la
    # mesure courante fausse -- d'ou un avertissement et non un refus.
    if [ -n "$THROTTLE_STATE" ] && [ -n "$_now" ] && is_uint "${THR_US:-}"; then
      if mkdir -p "$STATE_DIR" 2>/dev/null \
         && printf '%s %s %s\n' "$_now" "${THR_NR:-0}" "$THR_US" > "$THROTTLE_STATE.tmp.$$" 2>/dev/null \
         && mv -f "$THROTTLE_STATE.tmp.$$" "$THROTTLE_STATE" 2>/dev/null; then
        say "    etat enregistre : $THROTTLE_STATE"
      else
        rm -f "$THROTTLE_STATE.tmp.$$" 2>/dev/null || true
        warn "etat du temoin de throttling NON ECRIT ($THROTTLE_STATE) : la prochaine lecture rendra INDETERMINE sur le delta."
      fi
    fi

    # calme alors que des slots individuels sont satures -- c'est le cas
    # mesure le 2026-10-28 sur ai-01 (slice : 7 evenements / 2,4 s ; un
    # conteneur de slot : 3 688 evenements / 856 s). Le plafond agrege n'etait
    # alors pas la contrainte : le cap PAR SLOT l'etait.
    #
    # UNE LIMITE DE CE TEMOIN PAR S LOT, a ne pas oublier : le compteur d'un
    # conteneur est RECREE quand le slot est recycle (le superviseur remplace
    # le conteneur a chaque job). Un slot qui a beaucoup throttle peut donc
    # avoir un compteur revenu a zero le lendemain. Le temoin DUREL est celui
    # de la slice, dont le cgroup n'est pas recree.
    say "  slots (informatif) : throttling cumule par conteneur de la slice"
    _slots=0
    _list=""
    for C in "$SLICE_CG"/docker-*.scope; do
      [ -e "$C" ] || continue
      _slots=$((_slots + 1))
      _u="$(awk '/^throttled_usec /{print $2; exit}' "$C/cpu.stat" 2>/dev/null)"
      is_uint "$_u" || _u=0
      _list="$_list$_u	$(basename "$C")
"
    done
    if [ "$_slots" -eq 0 ]; then
      say "    (aucun scope docker-* lisible dans la slice)"
    else
      printf '    %s conteneur(s) ; les 5 plus throttles :\n' "$_slots"
      printf '%s' "$_list" | sort -rn 2>/dev/null | head -5 | while IFS="$(printf '\t')" read -r u n; do
        printf '    %-64s %s s\n' "$n" "$(awk -v u="$u" 'BEGIN{printf "%.2f", u/1e6}')"
      done
      say "    (compteur par conteneur : il repart a zero quand le slot est"
      say "     recycle -- seul celui de la slice est durable)"
    fi
  fi
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
  # Le marqueur passe en ARGUMENT de « %s », jamais en chaine de format : une
  # chaine de format qui commence par « - » est lue comme une OPTION par
  # printf, qui refuse et n'imprime RIEN. C'est ce qui s'est produit ici --
  # la ligne rendait « TOTAL 16.00 / 8 » sans son verdict, sur la machine
  # reelle, pendant que le harnais restait vert. Mesure du 2026-09-08 :
  # identique en Git Bash 5.2.37 et en bash 5.2.21 sous Ubuntu, ce n'est donc
  # pas un ecart de plateforme.
  if [ "$BUDGET" -eq 0 ]; then printf '%s' 'garde desactive (budget=0)'
  elif over "$1" "$BUDGET";  then printf '%s' '-> REFUSE'
  else                            printf '%s' '-> passe'
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

# CE QUI DECLENCHE LE REFUS A CHANGE (#23051, decision du coordinateur).
#
# La version precedente refusait des qu'un drop-in etait lu APRES la cible
# d'apres l'ordre LEXICOGRAPHIQUE des noms de fichiers. C'etait une PREDICTION
# presentee comme un fait : sur ai-01 trois drop-ins lus apres la cible
# (20-pids.conf, 30-budget.conf, 40-scale-14.conf) suffisaient a faire refuser
# un controle que rien ne surchargait. Un ordre de fichiers ne dit pas si une
# directive est reellement surchargee -- la valeur EFFECTIVE, elle, le dit.
#
# Le refus est donc desormais adosse a la MESURE de la section 1 : pour chaque
# directive que la proposition porte, on cherche QUI fournit la valeur effective.
# Le test est sound sans jamais raisonner sur l'ordre (les cinq branches sont
# reprises en tete de attr_directive) :
#
#   - proposition == effective : le fichier ecrit ne change rien -> PASS ;
#   - aucun drop-in ne declare la directive -> PASS : la proposition s'applique ;
#   - un drop-in declare la valeur effective -> il est en vigueur (ou
#     indiscernable de celui qui l'est), et l'ecriture ne le dessaisit pas ->
#     REFUS, en le nommant avec sa valeur mesuree ;
#   - des drop-ins declarent autre chose, et la CIBLE fournit la valeur
#     effective -> ils sont surclasses et le resteront -> PASS, en les signalant ;
#   - aucun des cas ci-dessus : la valeur effective n'est attribuable a rien de
#     releve -> REFUS (fail-closed : une approbation sans attribution n'est pas
#     une approbation etayee).
#
# La lecture effective etant fatale a la section 1 (unite injoignable, valeur
# ineligible), le cas « mesure impossible » est deja un refus : le fail-closed
# est conserve, il n'est simplement plus declenche par une prediction.
#
# Aucun drop-in n'est renomme par ce script : renommer la cible pour faire taire
# un garde est un contournement, et la resolution d'une surcharge reelle est une
# decision de configuration, pas un ajustement mecanique.
#
# Ordre de precedence des racines de drop-ins, du plus FORT au plus faible, tel
# que le rend « systemd-analyze unit-paths » (mesure sur systemd 255) et que le
# documente systemd.unit(5). Deux regles distinctes, souvent confondues :
#   - a nom de fichier EGAL, la racine la plus forte l'emporte (masquage) ;
#   - a noms DIFFERENTS, la fusion est lexicographique sur le nom de fichier,
#     quelle que soit la racine.
# Le classement ne sert qu'a la premiere. La seconde n'est PLUS traitee par
# l'ordre des noms mais par la valeur effective (voir plus bas).
rank_of() {
  case "$1" in
    /etc/systemd/system.control/*)  echo 1 ;;
    /run/systemd/system.control/*)  echo 2 ;;
    /run/systemd/transient/*)       echo 3 ;;
    /etc/systemd/system/*)          echo 4 ;;
    /run/systemd/system/*)          echo 5 ;;
    /usr/local/lib/systemd/system/*) echo 6 ;;
    /usr/lib/systemd/system/*)      echo 7 ;;
    # Racine inconnue : on ne sait pas la classer, donc on la traite comme la
    # plus forte. L'erreur va vers le REFUS, jamais vers l'approbation.
    *)                              echo 0 ;;
  esac
}

TARGET_BASE="$(basename "$TARGET")"
TARGET_REL="${TARGET#"$ROOT"}"
DROPINS=""
for D in $(sc_show coursia-runner.service DropInPaths); do
  DB="$(basename "$D")"
  # La cible se reconnait a son CHEMIN, jamais a son seul basename. Sauter tout
  # homonyme revenait a ignorer un fichier qu'on ne controle pas, en le prenant
  # pour soi. Les chemins sont compares hors racine d'inspection : sous
  # COURSIA_DRYRUN_ROOT la cible est prefixee, pas ce que rend DropInPaths.
  [ "${D#"$ROOT"}" = "$TARGET_REL" ] && continue
  if [ "$DB" = "$TARGET_BASE" ]; then
    # A nom de fichier EGAL, c'est la racine de plus haute precedence qui
    # l'emporte -- pas le dernier lu. Un homonyme d'une racine plus FAIBLE est
    # donc masque par la cible : l'ignorer est correct. Refuser sur tout
    # homonyme, comme le faisait la version precedente, bloquait une
    # configuration parfaitement definie. Seul l'homonyme d'une racine plus
    # FORTE est dangereux : il masquerait la cible, et le verdict porterait sur
    # un fichier que le processus ne verra jamais.
    R_HOME="$(rank_of "${D#"$ROOT"}")"
    R_CIBLE="$(rank_of "$TARGET_REL")"
    if [ "$R_HOME" -lt "$R_CIBLE" ]; then
      die "drop-in HOMONYME dans une racine de precedence SUPERIEURE :
  $D                (rang $R_HOME)
  cible inspectee : $TARGET   (rang $R_CIBLE)
A nom de fichier egal, systemd retient celui de la racine la plus forte : cet
homonyme MASQUE la cible. Le verdict porterait sur un fichier que le processus
ne verra pas. Refus."
    fi
    # Homonyme plus faible : masque par la cible, sans effet. On passe.
    continue
  fi
  DROPINS="$DROPINS $D"
done

# Ce qu'un FICHIER declare -- pas ce qui s'applique. N'est employe que pour
# ATTRIBUER une valeur effective deja mesuree, jamais pour la deduire.
# Les chemins rendus par DropInPaths sont absolus, comme sur la machine ; sous
# COURSIA_DRYRUN_ROOT ils sont resolus sous la racine d'inspection, sauf s'ils
# la portent deja (fixtures).
resolve_dropin() {   # $1 = chemin rendu par DropInPaths
  case "$1" in
    "$ROOT"/*) printf '%s' "$1" ;;
    *)         printf '%s' "${ROOT}$1" ;;
  esac
}
# Un drop-in liste mais illisible rend l'attribution IMPOSSIBLE : on ne peut ni
# prouver qu'il surcharge, ni prouver qu'il ne surcharge pas. L'erreur va vers
# le refus, comme partout ailleurs dans ce script.
for D in $DROPINS; do
  DP="$(resolve_dropin "$D")"
  [ -r "$DP" ] || die "drop-in liste par systemd mais ILLISIBLE :
  $D
  (resolu en : $DP)
Sans son contenu, la valeur effective ne peut pas etre ATTRIBUEE : on ne sait
pas si ce fichier surcharge la proposition. Ni « surcharge » ni « non
surcharge » n'est etabli, et l'erreur irait dans le sens permissif. Refus."
done

decl_env() {   # $1 = fichier, $2 = variable
  sed -e 's/#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' "$1" 2>/dev/null \
    | sed -n "s/^Environment=$2=\(.*\)$/\1/p" \
    | tail -1
}
decl_exec_slots() {   # $1 = fichier
  sed -n 's/^[[:space:]]*ExecStart=[[:space:]]*//p' "$1" 2>/dev/null \
    | grep -v '^$' | tail -1 | awk '{print $NF}'
}

# Une directive que la proposition porte, confrontee a la MESURE.
#
# Regle (aucune branche ne raisonne sur l'ordre des noms de fichiers) :
#   1. proposition == effective            -> PASS : le fichier ecrit ne change
#      rien a ce qui s'applique ;
#   2. aucun drop-in ne declare            -> PASS : la valeur vient de la
#      cible, de l'unite ou du defaut du wrapper, la proposition s'applique ;
#   3. un drop-in declare la valeur EFFECTIVE -> REFUS : il est en vigueur (ou
#      indiscernable de l'etant), et changer la valeur de la cible ne le dessaisit
#      pas -- l'ordre de fusion ne bouge pas ;
#   4. des drop-ins declarent, aucun la valeur effective, et la CIBLE declare la
#      valeur effective -> PASS : ils sont surclasses par la cible aujourd'hui,
#      et le resteront ;
#   5. aucun cas ci-dessus : la valeur effective n'est attribuable ni a la cible
#      ni a un drop-in identifie -> REFUS (attribution impossible, fail-closed).
# $1 = libelle  $2 = valeur proposee  $3 = valeur effective  $4 = type (env|exec)
# $5 = variable (pour env)
OVERRIDE_DORMANT=""
attr_directive() {
  _label="$1"; _prop="$2"; _eff="$3"; _kind="$4"; _var="${5:-}"
  # (1) La proposition ne change rien a la valeur appliquee.
  [ "$_prop" = "$_eff" ] && return 0
  _claimers=""
  for _D in $DROPINS; do
    _p="$(resolve_dropin "$_D")"
    if [ "$_kind" = exec ]; then
      _v="$(decl_exec_slots "$_p")"
    else
      _v="$(decl_env "$_p" "$_var")"
    fi
    [ -n "$_v" ] || continue
    _claimers="$_claimers $_D=$_v"
    # (3) Il declare la valeur APPLIQUEE : il est en vigueur, ou indiscernable
    # de celui qui l'est (memes valeurs possibles). Ecrire la cible ne peut pas
    # le dessaisir -- l'ordre de fusion ne change pas. Refus.
    if [ "$_v" = "$_eff" ]; then
      die "surcharge MESUREE sur $_label : la valeur effective est declaree par
  un drop-in autre que la cible :
  $_D
  valeur appliquee : $_eff
  valeur proposee  : $_prop
La proposition serait ecrite dans $TARGET_BASE et ne dessaisirait pas ce
fichier : le verdict porterait sur une configuration qui ne s'applique pas.
Refus -- la resolution (retirer la surcharge, ou changer la valeur a la source)
est une decision de configuration, pas un ajustement de ce script. Aucun
fichier n'est renomme pour faire taire ce controle."
    fi
  done
  if [ -z "$_claimers" ]; then
    return 0   # (2)
  fi
  # (4) La cible declare-t-elle la valeur effective ? Si oui, elle est en force
  # et les claimants ci-dessus (tous != effective) sont surclasses : ils le
  # resteront apres l'ecriture. On passe, en les signalant.
  if [ "$_kind" = exec ]; then
    _t="$(decl_exec_slots "$TARGET")"
  else
    _t="$(decl_env "$TARGET" "$_var")"
  fi
  if [ -n "$_t" ] && [ "$_t" = "$_eff" ]; then
    for _c in $_claimers; do
      OVERRIDE_DORMANT="$OVERRIDE_DORMANT
  $_label : ${_c%%=*} declare ${_c#*=}, la valeur appliquee est $_eff (fournie par la cible)"
    done
    return 0
  fi
  # (5) La valeur effective n'est attribuable ni a la cible ni a un claimant :
  # la mesure ne suffit pas a etablir qui s'appliquera apres l'ecriture.
  die "attribution IMPOSSIBLE sur $_label :
  claimants releves :$_claimers
  valeur appliquee : $_eff
  valeur declaree par la cible : ${_t:-<rien>}
Aucun fichier releve ne fournit la valeur qui s'applique. Le verdict ne peut
pas etre etaye par la mesure : refus plutot qu'une approbation sans preuve."
}

attr_directive "COURSIA_RUNNER_CPUS" "$CPUS" "${EFF_START_CPUS:-}" env COURSIA_RUNNER_CPUS
attr_directive "COURSIA_RUNNER_MEMORY" "$EFF_START_MEM" "${EFF_START_MEM:-}" env COURSIA_RUNNER_MEMORY
attr_directive "ExecStart (slots)" "$SLOTS" "${EFF_START_N:-}" exec

if [ -n "$OVERRIDE_DORMANT" ]; then
  warn "drop-in(s) declarant une directive de la proposition SANS etre en vigueur :$OVERRIDE_DORMANT"
  say "  (surclasses par la cible aujourd'hui ; la proposition ne change pas"
  say "   l'ordre de fusion, donc elle ne les met pas en vigueur. Signale, non decisif.)"
fi
say "  surcharge : aucune valeur proposee n'est fournie par un drop-in en vigueur"
say "              (attribution mesuree sur la configuration effective de la section 1)."

# Le drop-in propose porte exactement trois directives. Si la cible vivante en
# porte d'autres, l'ecrire A LA PLACE les perdrait en silence. Les reconduire
# serait un choix de configuration, pas une transformation mecanique que ce
# script puisse s'autoriser.
#
# L'ExecStart se compare par sa VALEUR, jamais en jetant la ligne. La version
# precedente filtrait « ^ExecStart= » en bloc : une cible portant un AUTRE
# binaire rendait EXTRA vide, donc « rien n'est perdu » -- alors que la
# proposition emet « ExecStart= » (reset) puis SON binaire, remplacant la liste
# entiere. Le trou vivait dans le garde meme cense l'attraper. Ne sont donc
# tolerees que les deux formes que la proposition reproduit a l'identique : la
# ligne de reset, et l'invocation du wrapper avec un unique argument. Tout le
# reste -- autre binaire, arguments supplementaires, prefixes systemd (- @ + !)
# -- survit au filtre et fait refuser. L'erreur va vers le REFUS.
if [ "$TARGET_STATE" = "PRESENT" ]; then
  EXTRA="$(sed -e 's/#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' "$TARGET" \
    | grep -v '^$' \
    | grep -v '^\[Service\]$' \
    | grep -v '^Environment=COURSIA_RUNNER_MEMORY=' \
    | grep -v '^Environment=COURSIA_RUNNER_CPUS=' \
    | grep -v '^ExecStart=$' \
    | grep -v '^ExecStart=/usr/local/bin/coursia-runner-start\.sh [^ ]*$' || true)"
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
if [ "$THROTTLE_ALERT" -eq 1 ]; then
  say ""
  say "TEMOIN THROTTLING : $THROTTLE_VERDICT -- sortie 3."
  say "  Le bundle est complet et la proposition franchit le garde ; c'est la"
  say "  MESURE du noyau qui le contredit. Traiter l'alerte comme un fait, et"
  say "  non comme une hypothèse a verifier."
  exit 3
fi
exit 0
