#!/usr/bin/env bash
# Lanceur PERSISTANT du pool d'attente PR-gate (label coursia-waiter).
#
# POURQUOI CE FICHIER EXISTE (#14612, #14846)
# -------------------------------------------
# La jambe `waiters` n'avait de persistance sur AUCUNE machine : elle etait
# lancee a la main dans une session, et mourait avec elle. Consequence mesuree
# le 2026-09-07 : les 12 waiters d'ai-01 morts depuis la veille, po-2024 seul
# fournisseur du label, et quand ses conteneurs se sont mis a etre fauches a
# 10 min, le `PR gate` -- check REQUIS -- a echoue 5 fois sur 5 (00:06Z ->
# 00:30Z) : gel de tous les merges de la flotte. #14612 nommait le defaut
# structurel (aucune redondance) ; ce fichier le ferme cote ai-01.
#
# STATE_DIR DEDIE, ET C'EST LE POINT DELICAT. supervise.sh place sa sentinelle
# d'arret gracieux en "$STATE_DIR/stop", et cmd_waiters REFUSE de demarrer si
# elle est posee. Partager le state dir avec coursia-runner.service ferait donc
# qu'un `systemctl stop coursia-runner` empeche le pool d'attente de redemarrer
# -- deux jambes independantes couplees par un fichier. D'ou /var/lib/coursia-waiters.
#
# LE SECRET NE SE DUPLIQUE PAS : GH_RUNNERS_ADMIN_TOKEN est relu dans master.env
# a chaque demarrage (jamais recopie dans un EnvironmentFile, jamais en argv).
set -uo pipefail

MASTER_ENV="${COURSIA_MASTER_ENV:-/mnt/d/CoursIA/.secrets/master.env}"
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/CoursIA}"
ARG="${1:-12}"

[ -r "$MASTER_ENV" ] || { echo "master.env illisible : $MASTER_ENV" >&2; exit 1; }

GH_TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$MASTER_ENV" | head -1 | tr -d '"'"'"'\r')"
[ -n "$GH_TOKEN" ] || { echo "GH_RUNNERS_ADMIN_TOKEN absent de master.env -- abandon" >&2; exit 1; }
export GH_TOKEN

# Daemon EPINGLE (meme raison que coursia-runner-start.sh) : sans cela
# l'integration WSL de Docker Desktop rattacherait les conteneurs a la session.
export DOCKER_HOST="${DOCKER_HOST:-unix:///var/run/docker-ce.sock}"

export COURSIA_RUNNER_WAITER_NAME_PREFIX="${COURSIA_RUNNER_WAITER_NAME_PREFIX:-myia-ai-01-linux-waiter}"
export COURSIA_RUNNER_STATE_DIR="${COURSIA_RUNNER_STATE_DIR:-/var/lib/coursia-waiters}"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

cd "$REPO_DIR" || exit 1

if [ "$ARG" = "stop" ]; then
  exec ./scripts/ci/docker/linux-runner/supervise.sh stop
fi
# --- PURGE SENTINELLE PERIMEE (#15163) -----------------------------
# supervise.sh pose "$STATE_DIR/stop" a l'arret gracieux et REFUSE de demarrer
# tant qu'elle est la. La sentinelle est un FICHIER : elle survit au reboot.
# Un arret gracieux suivi d'un redemarrage machine laissait donc l'unite
# echouer, et le pool restait a ZERO jusqu'a intervention humaine.
#
# Mesure ai-01 du 2026-09-07 :
#   22:37:01  stop gracieux (sentinelle posee)
#   <reboot>
#   22:53:29  Started coursia-runner.service
#   22:53:30  ERREUR: sentinel STOP_FILE present -- status=1/FAILURE
#
# C'est arrive QUATRE fois dans cette seule journee, chaque fois avec un
# deplacement physique jusqu'a la machine pour la redemarrer. C'est le defaut
# que ce bloc existe pour fermer.
#
# Un ExecStart est une demande EXPLICITE de demarrage : si aucun superviseur
# n'est vivant, la sentinelle ne protege plus rien -- elle wedge. On la retire.
# Si un superviseur EST vivant, un arret est en cours : on n'interfere pas, et
# on sort en erreur plutot que de lui couper l'herbe sous le pied.
#
# LE PREDICAT EST PAR-JAMBE, PAS FLOTTE-ENTIERE (#15163).
# La sentinelle, elle, etait deja par-jambe : /var/lib/coursia-runner/stop et
# /var/lib/coursia-waiters/stop sont deux fichiers distincts. Un predicat
# `supervise\.sh (start|waiters)` repondrait « un superviseur QUELCONQUE
# vit-il ? » -- si bien que chaque jambe refuserait de purger SA PROPRE
# sentinelle perimee tant que L'AUTRE tourne. Un verrou par jambe garde par un
# test global ne garde rien : il wedge.
#
# Les deux formes ne divergent que sur (runner vivant, waiters mort) -- soit
# exactement le wedge observe sur cette jambe le 2026-09-07, resolu a la main.
# Un futur `supervise.sh lean` prendra son propre predicat, pour la meme raison.
if [ -e "$COURSIA_RUNNER_STATE_DIR/stop" ]; then
  if pgrep -f 'supervise\.sh waiters' >/dev/null 2>&1; then
    echo "sentinelle presente ET superviseur vivant -- arret en cours, on n'interfere pas" >&2
    exit 1
  fi
  echo "sentinelle perimee (aucun superviseur vivant) -- purge avant demarrage" >&2
  rm -f "$COURSIA_RUNNER_STATE_DIR/stop"
fi
# ---------------------------------------------------------------------------
exec ./scripts/ci/docker/linux-runner/supervise.sh waiters "$ARG"
