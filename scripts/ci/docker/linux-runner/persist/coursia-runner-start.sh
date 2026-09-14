#!/usr/bin/env bash
# Wrapper de demarrage du superviseur de runners Linux CoursIA sous systemd.
# Deploiement po-2024 (2026-09-02) : copie de reference -- l'original vit
# dans la distro Ubuntu de l'hote, sous /usr/local/bin/coursia-runner-start.sh.
#
# Design :
#   - le token admin GitHub ne vit JAMAIS dans la distro ni dans un argv :
#     il est relu a CHAQUE invocation depuis master.env cote Windows
#     (/mnt/c/... via sed + tr -d '\r' -- CRLF tuerait la valeur) ;
#   - DOCKER_HOST epingle le socket docker-ce, pas le Docker Desktop ;
#   - l'etat superviseur (sentinel, logs slots) vit sous /var/lib/coursia-runner.
set -euo pipefail

TOKEN_FILE="/mnt/c/dev/CoursIA/.secrets/master.env"
TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$TOKEN_FILE" | tr -d '\r')"
if [ -z "$TOKEN" ]; then
    echo "FATAL: GH_RUNNERS_ADMIN_TOKEN absent de $TOKEN_FILE" >&2
    exit 1
fi

export DOCKER_HOST="unix:///var/run/docker-ce.sock"
export GH_TOKEN="$TOKEN"
export COURSIA_RUNNER_REPO="jsboige/CoursIA"
export COURSIA_RUNNER_NAME_PREFIX="myia-po-2024-linux-docker"
export COURSIA_RUNNER_STATE_DIR="/var/lib/coursia-runner"
export COURSIA_RUNNER_TOOLCACHE_VOLUME="coursia-runner-toolcache"

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

SUPERVISE="/mnt/c/dev/CoursIA/scripts/ci/docker/linux-runner/supervise.sh"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

# --- PURGE SENTINELLE PERIMEE (#15163) -----------------------------
# supervise.sh pose "$STATE_DIR/stop" a l'arret gracieux et REFUSE de
# demarrer tant qu'elle est la. La sentinelle est un FICHIER : elle survit
# au reboot. Un arret gracieux suivi d'un redemarrage machine laissait donc
# l'unite echouer, et le pool restait a ZERO jusqu'a intervention humaine.
#
# C'est la 4e jambe, et la derniere non couverte : ai-01/runner, waiters et
# lean portent ce bloc depuis #15188. Ce wrapper-ci relaie n'importe quelle
# sous-commande (`exec "$SUPERVISE" "$@"`), et l'unite po-2024 route EXPRES
# son ExecStart ET son ExecStop vers lui (`start 12` / `stop`) : d'ou la
# garde sur `start` ci-dessous. Un bloc inconditionnel -- la forme d'ai-01,
# dont la branche `stop` est ecrite AVANT la purge -- refuserait ici l'arret
# gracieux des qu'un superviseur vit, puisque `stop` retombe sur ce meme
# bloc.
#
# Un ExecStart est une demande EXPLICITE de demarrage : si aucun superviseur
# n'est vivant, la sentinelle ne protege plus rien -- elle wedge. On la
# retire. Si un superviseur EST vivant, un arret est en cours : on
# n'interfere pas, et on sort en erreur plutot que de lui couper l'herbe
# sous le pied.
#
# LE PREDICAT EST PAR-JAMBE, PAS FLOTTE-ENTIERE (#15163). La sentinelle est
# deja par-jambe (/var/lib/coursia-runner/stop et
# /var/lib/coursia-waiters/stop sont deux fichiers distincts). Un predicat
# `supervise\.sh (start|waiters)` repondrait « un superviseur QUELCONQUE
# vit-il ? » -- chaque jambe refuserait alors de purger SA PROPRE sentinelle
# perimee tant que L'AUTRE tourne. Un verrou par jambe garde par un test
# global ne garde rien : il wedge. C'est le seul point ou les deux formes
# divergent, et c'est ce que le cas 4 de persist/test_sentinel_purge.sh
# mesure.
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
