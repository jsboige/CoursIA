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

# Le defaut de chemin a DEJA demenage : la migration du 2026-09-17 a deplace le
# depot `C:\dev\CoursIA` -> `D:\Dev\CoursIA`, et ce fichier pointait encore
# l'arborescence purgee. Ce n'etait pas cosmetique : `[ -r "$MASTER_ENV" ]`
# echoue AVANT la lecture du token, donc le lanceur sortait en `exit 1` et le
# pool lean restait a ZERO jusqu'a intervention -- exactement l'incident du
# 2026-09-09 que ce fichier existe pour fermer (#16578).
MASTER_ENV="${COURSIA_MASTER_ENV:-/mnt/d/Dev/CoursIA/.secrets/master.env}"
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/Dev/CoursIA}"
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

# MEME BUDGET QUE LES DEUX AUTRES JAMBES DE CETTE MACHINE -- 42 Go depuis
# l'agrandissement VM du 2026-09-21 (24 032 -> 40 110 Mo, arbitrage user,
# mission ai-01 msg-20260921T203652-qxg3en). Cette jambe est celle qui a rendu
# l'ecart visible : ses 2 slots a 6 Go demandent 12 288 Mo, et le garde les
# refusait tant que les 18 432 Mo des deux autres familles etaient en vol
# (18 432 + 12 288 > 12 288) -- sous l'ancien budget 12 Go, les slots lean ne
# DEMARRAIENT JAMAIS. Le refus etait correct ; ce qui manquait etait un budget
# couvrant la composition complete (8x1536 + 12x1536 + 2x6144 = 43 008 Mo).
# Les trois jambes doivent annoncer le meme nombre : assert_memory_budget
# somme les familles entre elles, une divergence refuserait des slots sans
# nommer sa cause.
export COURSIA_RUNNER_BUDGET_GB="${COURSIA_RUNNER_BUDGET_GB:-42}"

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
