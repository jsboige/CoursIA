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
exec ./scripts/ci/docker/linux-runner/supervise.sh waiters "$ARG"
