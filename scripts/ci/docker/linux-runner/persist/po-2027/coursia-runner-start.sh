#!/usr/bin/env bash
# Wrapper de demarrage du superviseur de runners Linux CoursIA sous systemd.
# Deploiement myia-po-2027 (2026-10-24) : copie de reference -- l'original vit
# dans la distro Ubuntu de l'hote, sous /usr/local/bin/coursia-runner-start.sh.
# Adapte de persist/coursia-runner-start.sh (po-2024) et de
# persist/po-2028/coursia-runner-start.sh, dont la structure de jetons est
# reprise : le jeton n'est ni stocke ni passe en argv, il est relu a CHAQUE
# invocation.
#
# DELTAS po-2027, mesures le 2026-10-24 :
#   - distro Ubuntu 26.04 « resolute », systemd PID 1, 20 vCPU / 31 Go vus ;
#   - `GH_RUNNERS_ADMIN_TOKEN` est ABSENT du master.env de cette machine : la
#     voie de repli de po-2028 (gh.exe + APPDATA Windows) est donc la voie
#     nominale ici, le master.env restant prioritaire s'il est renseigne un
#     jour (une seule lecture, deux sources ordonnees) ;
#   - `gh` natif installe dans la distro (2.103.2) parce que supervise.sh
#     l'appelle directement (`command -v gh`, lignes 1858/2366/2406) et que le
#     conteneur ne peut pas executer un .exe Windows ;
#   - le daemon est docker-ce 29.9.2 epingle sur /var/run/docker-ce.sock ; le
#     drop-in de flotte ne suffisait pas sur ce systemd (Requires/After vers
#     docker.socket non vidables), d'ou l'override d'unite
#     persist/po-2027/docker.service, pose avec persist/po-2027/coursia-socket.conf.
set -euo pipefail

# Racine du depot. Le defaut suit le chemin REEL de cette machine : la migration
# du 2026-09-17 a deplace `C:\dev\CoursIA` -> `D:\Dev\CoursIA` (le `dev` est en
# minuscules ici, et /mnt/d est insensible a la casse).
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/dev/CoursIA}"

# --- JETON (jamais en argv, jamais stocke dans la distro) -------------------
# Ordre : master.env d'abord (doctrine de flotte, CRLF interdit -> tr -d '\r'),
# puis le CLI Windows, dont le jeton vit dans le trousseau Windows. Le `gh.exe`
# lance depuis la distro n'herite pas de APPDATA : sans cette variable il rend
# une chaine vide (mesure du 2026-10-24), ce qui produisait un FATAL opaque.
TOKEN_FILE="${COURSIA_MASTER_ENV:-$REPO_DIR/.secrets/master.env}"
TOKEN=""
if [ -r "$TOKEN_FILE" ]; then
    TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$TOKEN_FILE" | tr -d '\r')"
fi
if [ -z "$TOKEN" ]; then
    GH_WIN="/mnt/c/Program Files/GitHub CLI/gh.exe"
    [ -x "$GH_WIN" ] || GH_WIN="$(command -v gh.exe || true)"
    if [ -n "${GH_WIN:-}" ] && [ -x "$GH_WIN" ]; then
        TOKEN="$(APPDATA='C:\Users\Jesse\AppData\Roaming' "$GH_WIN" auth token 2>/dev/null | tr -d '\r\n')"
    fi
fi
if [ -z "$TOKEN" ]; then
    echo "FATAL: aucun jeton GitHub -- GH_RUNNERS_ADMIN_TOKEN absent de $TOKEN_FILE ET gh.exe muet (auth Windows). Reparer l'un des deux avant de relancer le service." >&2
    exit 1
fi

export DOCKER_HOST="unix:///var/run/docker-ce.sock"
export GH_TOKEN="$TOKEN"
export COURSIA_RUNNER_REPO="jsboige/CoursIA"
export COURSIA_RUNNER_NAME_PREFIX="myia-po-2027-linux-docker"
export COURSIA_RUNNER_STATE_DIR="/var/lib/coursia-runner"
export COURSIA_RUNNER_TOOLCACHE_VOLUME="coursia-runner-toolcache"

# --- DIMENSIONNEMENT (l'hote prime : c'est aussi un poste GPU interactif) ----
# N = 4 slots, caps 3 vCPU / 4 Go / 512 pids. Pourquoi ces caps et pas les
# 1536 Mo du defaut du superviseur : la classe « Scripts Tests » culmine a
# 3,5 Gio (mesure po-2028 du 2026-10-20, #16643) ; a 1536 Mo elle meurt sur
# KeyError xdist, c'est-a-dire sur des workers tues par le cap, pas sur un test
# rouge. On reduit donc le NOMBRE de slots, jamais le cap unitaire.
#
# ARITHMETIQUE DECLAREE (regle #19802 : le budget est la somme des caps) :
#     4 slots x 4 Go   = 16 384 Mo            -> COURSIA_RUNNER_BUDGET_GB=16
#     4 slots x 3 vCPU = 12 vCPU sur 20       -> COURSIA_RUNNER_CPU_BUDGET=12
#     slice : MemoryHigh=16G, MemoryMax=18G, MemorySwapMax=0 (mur kernel)
# La VM WSL est plafonnee a 32 Go (.wslconfig) et l'hote a 63,6 Go : 18 Go de
# CI laissent 13 Go dans la VM aux lanes interactives, et >= 45 Go a Windows.
# Aucune jambe coursia-waiter n'est installee sur cette machine (dispatch
# ai-01 du 2026-10-24) : la famine se traite par des slots d'execution, pas
# par des places dans la file.
export COURSIA_RUNNER_BUDGET_GB=16
export COURSIA_RUNNER_CPU_BUDGET=12
export COURSIA_RUNNER_CPUS=3
export COURSIA_RUNNER_MEMORY=4g
export COURSIA_RUNNER_PIDS=512

# Le mur kernel des conteneurs : la meme slice que daemon.json declare en
# cgroup-parent. assert_slice REFUSE le demarrage si elle est absente ou sans
# io.max -- d'ou REQUIRE_CGROUP_BUDGET=1 (fail-closed, jamais un pool non
# borne en silence).
export COURSIA_RUNNER_CGROUP_PARENT="coursia-ci.slice"
export COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET=1

# I/O : valeurs reprises de la mesure ai-01 (2026-09-07, 221 Mo/s cumules sous
# plafond contre 16,9 Go/s sans). Role : empecher qu'un thrash passe l'echelle,
# pas reguler un debit normal.
export COURSIA_RUNNER_DEVICE_WRITE_BPS=41943040
export COURSIA_RUNNER_DEVICE_READ_BPS=83886080

# PATH explicite : l'unite systemd ne charge pas de profil de shell, et le CLI
# GitHub installe par apt vit sous /usr/bin.
export PATH="/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

# #15095 : echec immediat si le demon du socket epingle ne repond pas --
# AVANT tout demarrage de slot et tout fetch de registration token (gh).
# Sans cette garde, un daemon arrete + Restart=always = le superviseur
# martelait docker/gh indefiniment (incident 07/09 : 2 gels machine ai-01,
# ecriture ext4.vhdx 94-96 Mo/s). Le superviseur porte la meme garde en
# profondeur (assert_docker_daemon) -- celle-ci rend l'echec visible au
# niveau systemd des l'ExecStart.
if ! docker info >/dev/null 2>&1; then
    echo "FATAL: demon Docker indisponible sur DOCKER_HOST=$DOCKER_HOST (docker info echoue, #15095) -- reparer le daemon avant de relancer le service." >&2
    exit 1
fi

SUPERVISE="$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

# --- PURGE SENTINELLE PERIMEE (#15163) -----------------------------
# supervise.sh pose "$STATE_DIR/stop" a l'arret gracieux et REFUSE de
# demarrer tant qu'elle est la. La sentinelle est un FICHIER : elle survit
# au reboot. Un arret gracieux suivi d'un redemarrage machine laissait donc
# l'unite echouer, et le pool restait a ZERO jusqu'a intervention humaine.
#
# Le predicat est PAR-JAMBE : un `supervise.sh (start|waiters)` repondrait
# « un superviseur QUELCONQUE vit-il ? » et chaque jambe refuserait de purger
# SA sentinelle perimee tant que l'autre tourne.
if [ "${1:-start}" = "start" ] && [ -e "$COURSIA_RUNNER_STATE_DIR/stop" ]; then
  if pgrep -f 'supervise\.sh start' >/dev/null 2>&1; then
    echo "sentinelle presente ET superviseur vivant -- arret en cours, on n'interfere pas" >&2
    exit 1
  fi
  echo "sentinelle perimee (aucun superviseur vivant) -- purge avant demarrage" >&2
  rm -f "$COURSIA_RUNNER_STATE_DIR/stop"
fi
# ---------------------------------------------------------------------------

exec "$SUPERVISE" "$@"
