#!/usr/bin/env bash
# Wrapper de demarrage du superviseur de runners Linux CoursIA -- po-2025.
# Copie de reference : l'original vit dans la distro Ubuntu de l'hote, sous
# /usr/local/bin/coursia-runner-start.sh.
#
# Design repris de po-2024 (persist/coursia-runner-start.sh) :
#   - le token admin GitHub ne vit JAMAIS dans la distro ni dans un argv : il
#     est relu a CHAQUE invocation depuis master.env cote Windows
#     (/mnt/d via sed + tr -d '\r' -- CRLF tuerait la valeur) ;
#   - DOCKER_HOST epingle le socket docker-ce, pas le Docker Desktop ;
#   - l'etat superviseur (sentinel, logs slots) vit sous /var/lib/coursia-runner.
#
# ECART DE SITUATION PAR RAPPORT A po-2024 : la machine de po-2025 est un
# portable, pas une tour de datacenter. C'est ce qui fixe N=2 et les deux
# budgets ci-dessous, pas une preference.
set -euo pipefail

REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/dev/CoursIA}"

TOKEN_FILE="${COURSIA_MASTER_ENV:-$REPO_DIR/.secrets/master.env}"
TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$TOKEN_FILE" | tr -d '\r')"
if [ -z "$TOKEN" ]; then
    echo "FATAL: GH_RUNNERS_ADMIN_TOKEN absent de $TOKEN_FILE" >&2
    exit 1
fi

export DOCKER_HOST="unix:///var/run/docker-ce.sock"
export GH_TOKEN="$TOKEN"
export COURSIA_RUNNER_REPO="jsboige/CoursIA"
export COURSIA_RUNNER_NAME_PREFIX="myia-po-2025-linux-docker"
export COURSIA_RUNNER_STATE_DIR="/var/lib/coursia-runner"
export COURSIA_RUNNER_TOOLCACHE_VOLUME="coursia-runner-toolcache"

# BUDGET MEMOIRE AGREGE DE LA CI SUR CETTE MACHINE (Go) -- declare, pas subi.
#
# LA COMPOSITION QUE CE BUDGET DECLARE :
#     2 slots docker x 1536 Mo =  3 072 Mo   (start 2, caps par defaut)
#     --------------------------------------
#     total CAPS                3 072 Mo   sur 32 095 Mo -> marge ~29 Go
#
# 12 EST UN PLAFOND D'ADMISSION VOLONTAIREMENT LARGE : l'hote (un portable qui
# sert aussi de poste interactif) garde 20 Go pour lui-meme, et la VM WSL n'en
# a que 27 disponibles. 12 laisse de la place a un elargissement mesure sans
# re-editer ce fichier, tout en refusant une composition qui mangerait l'hote.
export COURSIA_RUNNER_BUDGET_GB=12

# BUDGET CPU INTER-FAMILLES : somme des caps CPU des familles d'EXECUTION.
# Ici une seule famille (start 2 x 3 vCPU = 6). 10 = la MOITIE des 20 vCPU
# logiques de la VM WSL, la valeur nommee par l'addendum de dispatch du
# 2026-10-24 : l'hote doit primer, et cette garde est aussi ce qui empechera
# un `start N` ulterieur de depasser la moitie de la machine sans qu'on
# re-edite le wrapper en connaissance de cause.
export COURSIA_RUNNER_CPU_BUDGET=10

# #15095 : echec immediat si le demon du socket epingle ne repond pas -- AVANT
# tout demarrage de slot et tout fetch de registration token (gh). Sans cette
# garde, un daemon arrete + Restart=always = le superviseur martele docker/gh
# indefiniment (incident 07/09 : 2 gels machine, ecriture ext4.vhdx 94-96 Mo/s).
if ! docker info >/dev/null 2>&1; then
    echo "FATAL: demon Docker indisponible sur DOCKER_HOST=$DOCKER_HOST (docker info echoue, #15095) -- reparer le daemon avant de relancer le service." >&2
    exit 1
fi

SUPERVISE="$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

# --- PURGE SENTINELLE PERIMEE (#15163) -----------------------------
# supervise.sh pose "$STATE_DIR/stop" a l'arret gracieux et REFUSE de demarrer
# tant qu'elle est la. La sentinelle est un FICHIER : elle survit au reboot. Un
# arret gracieux suivi d'un redemarrage machine laissait donc l'unite echouer,
# et le pool restait a ZERO jusqu'a intervention humaine.
#
# Le predicat est PAR-JAMBE, pas flotte-entiere : la sentinelle est deja
# par-jambe, et un predicat global ferait refuser a chaque jambe la purge de SA
# propre sentinelle tant que l'AUTRE tourne (cas 4 de test_sentinel_purge.sh).
if [ "${1:-start}" = "start" ] && [ -e "$COURSIA_RUNNER_STATE_DIR/stop" ]; then
  # Predicat PER-CHECKOUT (#21527) : le superviseur d'un AUTRE checkout
  # (orphelin de test d'un autre worktree) ne doit pas bloquer le purge
  # de CETTE sentinelle -- il bloquait le service en failed, pool a zero.
  #
  # L'organe est lu par `bash`, pas execute : son bit executable est 100644
  # dans l'index, donc le noyau ne le rend pas executable sur un checkout
  # Linux natif ; un exec refuse rendrait le predicat FAUX -- il repondrait
  # « aucun superviseur vivant » et purgerait a tort.
  #
  # Repli CONSERVATEUR : si l'organe n'est pas lisible (depot perime sur la
  # machine, ou wrapper deploye avant la mise a jour du checkout), on
  # retombe sur le predicat per-machine : le repli peut REFUSER un purge
  # a tort, jamais PURGER a tort.
  HELPER="$REPO_DIR/scripts/ci/docker/linux-runner/persist/supervisor_live_for.sh"
  SUPERVISOR_ALIVE=0
  if [ -r "$HELPER" ]; then
    if bash "$HELPER" "$REPO_DIR" start >/dev/null 2>&1; then SUPERVISOR_ALIVE=1; fi
  else
    if pgrep -f 'supervise\.sh start' >/dev/null 2>&1; then SUPERVISOR_ALIVE=1; fi
  fi
  if [ "$SUPERVISOR_ALIVE" -eq 1 ]; then
    echo "sentinelle presente ET superviseur vivant -- arret en cours, on n'interfere pas" >&2
    exit 1
  fi
  echo "sentinelle perimee (aucun superviseur vivant) -- purge avant demarrage" >&2
  rm -f "$COURSIA_RUNNER_STATE_DIR/stop"
fi
# ---------------------------------------------------------------------------

exec "$SUPERVISE" "$@"
