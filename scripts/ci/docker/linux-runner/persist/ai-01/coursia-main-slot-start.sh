#!/usr/bin/env bash
# Wrapper du SLOT RESERVE a la verification de `main` (ai-01, WSL Ubuntu).
# Copie de REFERENCE : l'original vit sous /usr/local/bin/ sur l'hote.
# Meme patron que `coursia-runner-start.sh` (le superviseur de runners) :
# le wrapper est mince, il prepare l'ENVIRONNEMENT et appelle l'organe ;
# l'organe lui-meme (create-main-slot.sh) reste lu dans l'arbre de travail.
#
# CE QUE CE WRAPPER APPORTE PAR RAPPORT A L'ORGANE
# -------------------------------------------------
# `create-main-slot.sh` (tranche T-L de #25510) sait creer un slot reserve
# et le VERIFIER (`--dry-run`, `--check`, `--apply`). Il ne sait pas le
# faire REVI[V]IR : rien ne le relance au boot, et rien ne surveille sa
# disparition.
#
# C'est le trou que ce wrapper ferme, et il est mesure : le job CPU de
# `main` est un job REQUIS, et le slot reserve est sa SEULE place propre
# (mesure du 2026-11-12 : 27 minutes de file, 31 runners occupes par des
# PRs). Un slot reserve qui ne revient pas apres un reboot, ou qui a ete
# supprime, rend cette garantie illusoire -- et le job de `main` attend
# derriere les PRs, exactement comme avant T-L.
#
# LES TROIS GESTES, ET LEUR FRONTIERE
# -----------------------------------
#   start  : etat au BOOT -- cree le slot s'il est absent, le relance s'il
#            est arrete, ne fait RIEN s'il tourne deja (create-main-slot.sh
#            est idempotent : un slot deja present est signale, pas recree).
#   check  : etat PERIODIQUE -- verifie la conformance, et REPARE ce qui se
#            repare (absent -> creation ; arrete -> redemarrage). Une
#            derive qui ne se repare pas (labels, image, cgroup-parent)
#            reste une derive : elle est REMONTEE, pas masquee.
#   stop   : arret de l'unite -- ne supprime JAMAIS le slot. Le conteneur
#            d'un slot reserve n'est pas un artefact ephemere : le supprimer
#            sur un `systemctl stop` rendrait le service destructif, et le
#            script de creation lui-meme refuse de supprimer un slot.
#
# LE SECRET NE SE DUPLIQUE PAS
# -----------------------------
# Le jeton d'enregistrement est MINT par `create-main-slot.sh --apply`, via
# `gh api`, avec le jeton lu dans l'environnement. Ce wrapper le fourre
# donc depuis `master.env` -- relu a chaque invocation, jamais copie dans
# un fichier de l'unite, jamais ecrit sur la ligne de commande.
# C'est exactement le traitement du wrapper du superviseur (#21527).
#
# LE DAEMON DOCKER EST EPINGLE
# -----------------------------
# Sans epinglage, l'integration WSL de Docker Desktop peut remplacer
# /var/run/docker.sock par le socket de SON daemon : le slot reserve
# repartirait sur Docker Desktop, donc rattache a la session utilisateur
# -- et disparaitrait a la fermeture de cette session. L'echec serait
# muet. On epingle donc le socket du daemon `systemd` de la distro.
# La variable est DEDICEE (`COURSIA_MAIN_DOCKER_HOST`) et non reprise de
# l'environnement : un `DOCKER_HOST` deja pose par un contexte arbitraire
# ne doit pas pouvoir détourner le slot reserve vers un autre daemon.
#
# Les DEFAUTS DU NOM DU SLOT sont ceux de `create-main-slot.sh`. Ils sont
# dupliques ici -- le wrapper doit pouvoir nommer le conteneur pour
# distinguer « absent » de « arrete ». Le risque de derive est verrouille
# par `scripts/tests/test_main_slot_persistence.py`, qui lit les deux
# fichiers et compare les defauts.
#
# Refs : #25510 (T-L) ; `persist/README.md` (table de correspondance) ;
#        `create-main-slot.sh` (l'organe) ; `coursia-runner-start.sh`
#        (le patron suivi ici).
set -uo pipefail

REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/CoursIA}"
MASTER_ENV="${COURSIA_MASTER_ENV:-/mnt/d/CoursIA/.secrets/master.env}"
# L'organe. Surchargeable parce que le wrapper est PINLE hors arbre de
# travail : le chemin vivant du wrapper est /usr/local/bin, mais
# l'organe se lit dans le checkout partage.
SLOT_SCRIPT="${COURSIA_MAIN_SLOT_SCRIPT:-$REPO_DIR/scripts/ci/docker/linux-runner/persist/ai-01/create-main-slot.sh}"
# Les DEFAUTS de `create-main-slot.sh`, repores tels quels (verrou par le
# test) : PREFIX et SLOT composent le NOM du conteneur.
PREFIX="${COURSIA_MAIN_PREFIX:-myia-ai-01-linux-main}"
SLOT="${COURSIA_MAIN_SLOT:-1}"
# Le socket du daemon `systemd` de la distro WSL -- PAS celui de Docker
# Desktop, qui rattacherait le slot a la session utilisateur.
DOCKER_HOST="${COURSIA_MAIN_DOCKER_HOST:-unix:///var/run/docker-ce.sock}"
export DOCKER_HOST

MODE="${1:-start}"

usage() {
  sed -n '2,/^set -uo pipefail$/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'
  exit "${1:-0}"
}

log() { printf '%s\n' "$*"; }
err() { printf 'ERREUR : %s\n' "$*" >&2; }

slot_name() { printf '%s-%s' "$PREFIX" "$SLOT"; }

# Le jeton d'administration des runners, relu dans master.env a chaque
# invocation. Jamais copie, jamais sur la ligne de commande : il passe par
# l'environnement du seul process qui en a besoin (le mint de
# `create-main-slot.sh --apply`).
load_token() {
  [ -r "$MASTER_ENV" ] || { err "master.env illisible : $MASTER_ENV"; return 1; }
  GH_TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$MASTER_ENV" | head -1 | tr -d '"'"'"'\r')"
  [ -n "$GH_TOKEN" ] || { err "GH_RUNNERS_ADMIN_TOKEN absent de master.env -- abandon"; return 1; }
  export GH_TOKEN
}

# Etat VIVANT du conteneur du slot : absent / arrete / en marche.
# La seule source de verite est `docker inspect` sur le daemon epingle.
slot_state() {
  local name running
  name="$(slot_name)"
  if ! docker inspect "$name" >/dev/null 2>&1; then
    printf 'ABSENT'
    return 0
  fi
  running="$(docker inspect --format '{{.State.Running}}' "$name" 2>/dev/null || printf 'false')"
  if [ "$running" = "true" ]; then
    printf 'RUNNING'
  else
    printf 'STOPPED'
  fi
}

# Reparation de l'etat du slot. Les trois cas :
#   ABSENT  -> creation (l'organe, qui mint le jeton et lance le conteneur)
#   STOPPED -> redemarrage du conteneur (PAS de recreation : le jeton
#              d'enregistrement est a usage unique, et l'etat du runner
#              est dans le volume de configuration)
#   RUNNING -> rien a faire
ensure_slot() {
  local name state
  name="$(slot_name)"
  state="$(slot_state)"
  case "$state" in
    ABSENT)
      log "slot ${name} ABSENT -- creation"
      load_token || return 1
      "$SLOT_SCRIPT" --apply || return $?
      ;;
    STOPPED)
      log "slot ${name} ARRETE -- redemarrage du conteneur"
      docker start "$name" >/dev/null || { err "docker start a echoue"; return 1; }
      ;;
    RUNNING)
      log "slot ${name} en marche -- rien a faire"
      ;;
  esac
  return 0
}

case "$MODE" in
  start)
    ensure_slot || exit $?
    ;;
  check)
    # La VERIFICATION est celle de l'organe (c'est lui qui connait la
    # specification : labels, image, caps, cgroup-parent, etat de marche).
    # Le wrapper se contente de REPARER ce qui se repare, puis de RENDRE
    # LA MAIN a l'organe pour le verdict final.
    state="$(slot_state)"
    if [ "$state" = "ABSENT" ]; then
      log "slot absent -- creation (reparation)"
      ensure_slot || exit $?
    elif [ "$state" = "STOPPED" ]; then
      log "slot arrete -- redemarrage (reparation)"
      ensure_slot || exit $?
    fi
    "$SLOT_SCRIPT" --check
    exit $?
    ;;
  stop)
    # JAMAIS de suppression. Le slot reserve est un service, pas un
    # artefact : `systemctl stop` ne doit pas le detruire.
    log "arret de l'unite : le slot reserve n'est PAS supprime (il est recree au prochain boot)"
    exit 0
    ;;
  -h|--help)
    usage 0
    ;;
  *)
    err "mode inconnu : $MODE"
    usage 1
    ;;
esac
