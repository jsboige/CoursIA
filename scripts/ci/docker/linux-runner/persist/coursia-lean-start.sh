#!/usr/bin/env bash
# Lanceur PERSISTANT du pool LEAN specialise (label coursia-lean).
#
# POURQUOI CE FICHIER EXISTE (incident 2026-09-09)
# -------------------------------------------
# La jambe `lean` n'avait de persistance sur AUCUNE machine : elle etait
# lancee a la main dans une session, et mourait avec elle. Consequence
# mesuree le 2026-09-09 : apres le reboot de po-2024 (restauration
# coursia-runner + coursia-waiters), le pool lean est reste a ZERO toute
# la journee -- aucun runner ne portait le label `coursia-lean`, le run
# main de lean-knot y est mort "runner lost communication" (check-run
# 102437210604), et deux jobs lean de PR sont restes en queue de 12:39Z a
# 15:00Z+ pendant que les runners generaux servaient tout le reste.
# po-2027 a nomme le defaut ; ce fichier le ferme cote po-2024, sur le
# meme pattern que coursia-waiters-start.sh (#14612, #14846).
#
# STATE_DIR DEDIE, ET C'EST LE POINT DELICAT. L'appel manuel d'avant
# l'incident tournait SANS COURSIA_RUNNER_STATE_DIR : supervise.sh
# retombait sur /var/lib/coursia-runner, PARTAGE avec la jambe
# d'execution. Deux consequences mesurees : la sentinelle d'arret etait
# commune (un `systemctl stop coursia-runner` aurait arrete le pool lean
# au passage), et les pid files des deux familles vivaient entremelles.
# D'ou /var/lib/coursia-lean -- la sentinelle et le verrou pid redeviennent
# par-jambe, comme pour les waiters.
#
# LE SECRET NE SE DUPLIQUE PAS : GH_RUNNERS_ADMIN_TOKEN est relu dans
# master.env a chaque demarrage (jamais recopie dans un EnvironmentFile,
# jamais en argv).
set -uo pipefail

MASTER_ENV="${COURSIA_MASTER_ENV:-/mnt/c/dev/CoursIA/.secrets/master.env}"
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/c/dev/CoursIA}"
ARG="${1:-2}"

[ -r "$MASTER_ENV" ] || { echo "master.env illisible : $MASTER_ENV" >&2; exit 1; }

GH_TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$MASTER_ENV" | head -1 | tr -d '"'"'"'\r')"
[ -n "$GH_TOKEN" ] || { echo "GH_RUNNERS_ADMIN_TOKEN absent de master.env -- abandon" >&2; exit 1; }
export GH_TOKEN

# Daemon EPINGLE (meme raison que coursia-runner-start.sh) : sans cela
# l'integration WSL de Docker Desktop rattacherait les conteneurs a la session.
export DOCKER_HOST="${DOCKER_HOST:-unix:///var/run/docker-ce.sock}"

export COURSIA_LEAN_RUNNER_NAME_PREFIX="${COURSIA_LEAN_RUNNER_NAME_PREFIX:-myia-po-2024-lean-docker}"
export COURSIA_RUNNER_STATE_DIR="${COURSIA_RUNNER_STATE_DIR:-/var/lib/coursia-lean}"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

cd "$REPO_DIR" || exit 1

if [ "$ARG" = "stop" ]; then
  exec ./scripts/ci/docker/linux-runner/supervise.sh stop
fi
# --- PURGE SENTINELLE PERIMEE (#15163) -----------------------------
# Meme bloc que coursia-waiters-start.sh, avec le predicat PAR-JAMBE que
# son commentaire annoncait (« un futur supervise.sh lean prendra son
# propre predicat ») : `supervise\.sh lean`. Un predicat global ferait
# que chaque jambe refuserait de purger SA sentinelle tant qu'une AUTRE
# tourne -- un verrou par jambe garde par un test global ne garde rien.
if [ -e "$COURSIA_RUNNER_STATE_DIR/stop" ]; then
  if pgrep -f 'supervise\.sh lean' >/dev/null 2>&1; then
    echo "sentinelle presente ET superviseur vivant -- arret en cours, on n'interfere pas" >&2
    exit 1
  fi
  echo "sentinelle perimee (aucun superviseur vivant) -- purge avant demarrage" >&2
  rm -f "$COURSIA_RUNNER_STATE_DIR/stop"
fi
# ---------------------------------------------------------------------------
# Les pid files perimes (reboot) ne bloquent pas cmd_lean -- son garde
# teste le pid au kill -0 -- mais un fichier de pids d'un etat anterieur
# n'a aucune valeur : purge defensive coherente avec le rm -f de cmd_lean.
if [ -f "$COURSIA_RUNNER_STATE_DIR/lean-pids" ]; then
  head_pid="$(head -1 "$COURSIA_RUNNER_STATE_DIR/lean-pids" 2>/dev/null || true)"
  if [ -z "$head_pid" ] || ! kill -0 "$head_pid" 2>/dev/null; then
    rm -f "$COURSIA_RUNNER_STATE_DIR/lean-pids"
  fi
fi
exec ./scripts/ci/docker/linux-runner/supervise.sh lean "$ARG"
