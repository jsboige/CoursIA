#!/usr/bin/env bash
# Wrapper de demarrage du superviseur de runners Linux CoursIA sous systemd.
# Deploiement po-2028 (2026-10-20, mandat user runners via ai-01:CoursIA) --
# adapte de persist/coursia-runner-start.sh (po-2024, 2026-09-02). L'original
# vit dans la distro Ubuntu sous /usr/local/bin/coursia-runner-start.sh ; ce
# fichier est la copie de reference (C:\dev\CoursIA-runners-p0\).
#
# DELTAS po-2028 vs po-2024 (tous deux pesees du 2026-10-20) :
#   1. REPO_DIR=/mnt/d/dev/CoursIA-2 -- le checkout de cette machine (po-2024 :
#      /mnt/d/Dev/CoursIA). La bascule C:\dev -> D:\dev annoncee ici a eu lieu le
#      2026-10-27 ; l'ancien chemin C: n'est plus qu'un clone residuel, que les
#      mandats disque peuvent purger. Coder C: en dur faisait mourir le service
#      au premier redemarrage apres purge, sans rien dire.
#   2. TOKEN : pas de master.env sur cette machine. Le token admin GitHub est
#      relu a CHAQUE invocation depuis gh.exe cote Windows via l'interop WSL
#      (--with-token doctrine inchangee : jamais persistant dans la distro,
#      jamais dans un argv, relu a chaque fois). L'interop depuis un contexte
#      systemd est un precedent de flotte : la sonde de detresse hote
#      (persist/host-distress-probe.ps1) resout powershell.exe de la meme facon.
#   3. Composition de depart : 3 slots x (cpus=3, memory=4g, pids=512) --
#      classe Scripts Tests (pic mesure 3,5 Gio, #16643). Mandat du 20/10 :
#      dimensionnement prudent par slot (crochet #20174 : les slots persist
#      perdent _work/node24 -- ne pas dependre d'un grand nombre de slots).
#   4. Budgets : BUDGET_GB=12 (3 x 4096 Mo -- LA SOMME DES CAPS, regle #19802),
#      CPU_BUDGET=9 (3 x 3 ; pas de jambe lean ni waiters sur cette machine).
#   5. Slice : coursia-ci.slice po-2028 -- MemoryHigh=12G / MemoryMax=14G /
#      MemorySwapMax=0 pour une VM WSL de 31 Go : 17 Go restent aux lanes
#      CoursIA interactives et au daemon. Copie de reference a cote de ce
#      fichier (coursia-ci.slice).
#   6. Bornes I/O PAR CONTENEUR : write 40 Mio/s, read 80 Mio/s. La slice
#      porte l'agrege (200 Mo/s write / 400 Mo/s read sur /var/lib/docker).
set -euo pipefail

REPO_DIR="/mnt/d/dev/CoursIA-2"

# --- TOKEN (doctrine po-2024 : relu a chaque invocation, jamais persistant) ---
GH_WIN="/mnt/c/Program Files/GitHub CLI/gh.exe"
[ -x "$GH_WIN" ] || GH_WIN="$(command -v gh.exe || true)"
TOKEN=""
if [ -n "${GH_WIN:-}" ]; then
    TOKEN="$("$GH_WIN" auth token 2>/dev/null | tr -d '\r\n')"
fi
if [ -z "$TOKEN" ]; then
    echo "FATAL: token GitHub indisponible (gh.exe auth token muet cote Windows) -- reparer l'auth gh.exe de la session avant de relancer le service." >&2
    exit 1
fi
export GH_TOKEN="$TOKEN"

export DOCKER_HOST="unix:///var/run/docker-ce.sock"
export COURSIA_RUNNER_REPO="jsboige/CoursIA"
export COURSIA_RUNNER_NAME_PREFIX="myia-po-2028-linux-docker"
export COURSIA_RUNNER_STATE_DIR="/var/lib/coursia-runner"
export COURSIA_RUNNER_TOOLCACHE_VOLUME="coursia-runner-toolcache"

export COURSIA_RUNNER_BUDGET_GB=12
export COURSIA_RUNNER_CGROUP_PARENT="coursia-ci.slice"
export COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET=1
export COURSIA_RUNNER_CPU_BUDGET=9
export COURSIA_RUNNER_CPUS=3
export COURSIA_RUNNER_MEMORY=4g
export COURSIA_RUNNER_PIDS=512
export COURSIA_RUNNER_DEVICE_WRITE_BPS=41943040
export COURSIA_RUNNER_DEVICE_READ_BPS=83886080

# Le contexte systemd n'herite ni du PATH utilisateur ni du PATH Windows : gh
# (host contract, installe SHA-pine dans ~/.local/bin de jesse) doit etre
# resolvable pour le garde `command -v gh` (supervise.sh) ; GH_TOKEN ambiant
# couvre l'auth (fetch_token honore GH_TOKEN, #14259).
export PATH="/home/jesse/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

# #15095 : echec immediat si le demon du socket epingle ne repond pas -- AVANT
# tout demarrage de slot et tout fetch de registration token. Sans cette garde,
# un daemon arrete + Restart=always = le superviseur martele docker/gh
# indefiniment (incident 07/09 ai-01 : 2 gels machine, ecriture ext4.vhdx
# 94-96 Mo/s).
if ! docker info >/dev/null 2>&1; then
    echo "FATAL: demon Docker indisponible sur DOCKER_HOST=$DOCKER_HOST (docker info echoue, #15095) -- reparer le daemon avant de relancer le service." >&2
    exit 1
fi

SUPERVISE="$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

# --- PURGE SENTINELLE PERIMEE (#15163) --------------------------------------
# Copie conforme du bloc po-2024 : la sentinelle "$STATE_DIR/stop" survit au
# reboot ; un ExecStart explicite sans superviseur vivant la purge, sinon on
# sort en erreur sans interferer avec un arret en cours.
if [ "${1:-start}" = "start" ] && [ -e "$COURSIA_RUNNER_STATE_DIR/stop" ]; then
  if pgrep -f 'supervise\.sh start' >/dev/null 2>&1; then
    echo "sentinelle presente ET superviseur vivant -- arret en cours, on n'interfere pas" >&2
    exit 1
  fi
  echo "sentinelle perimee (aucun superviseur vivant) -- purge avant demarrage" >&2
  rm -f "$COURSIA_RUNNER_STATE_DIR/stop"
fi
# -----------------------------------------------------------------------------

exec "$SUPERVISE" "$@"
