#!/usr/bin/env bash
# Wrapper de demarrage du superviseur de runners Linux CoursIA sous systemd.
# Deploiement po-2024 (2026-09-02) : copie de reference -- l'original vit
# dans la distro Ubuntu de l'hote, sous /usr/local/bin/coursia-runner-start.sh.
#
# Design :
#   - le token admin GitHub ne vit JAMAIS dans la distro ni dans un argv :
#     il est relu a CHAQUE invocation depuis master.env cote Windows
#     (sous /mnt/... via sed + tr -d '\r' -- CRLF tuerait la valeur) ;
#   - DOCKER_HOST epingle le socket docker-ce, pas le Docker Desktop ;
#   - l'etat superviseur (sentinel, logs slots) vit sous /var/lib/coursia-runner.
set -euo pipefail

# Racine du depot. Le defaut a DEJA demenage : la migration du 2026-09-17 a
# deplace `C:\dev\CoursIA` -> `D:\Dev\CoursIA`, et ce wrapper pointait encore
# l'arborescence purgee. Consequence, mesuree (#16578) : `TOKEN_FILE` illisible
# -> `FATAL` AVANT tout demarrage de slot, donc le pool d'execution reste a ZERO
# jusqu'a intervention. Les deux surcharges sont celles de la jambe lean, pour
# que les deux lanceurs po-2024 se reglent de la meme facon.
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/Dev/CoursIA}"

TOKEN_FILE="${COURSIA_MASTER_ENV:-$REPO_DIR/.secrets/master.env}"
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

# BUDGET MEMOIRE AGREGE DE LA CI SUR CETTE MACHINE, en Go -- declare, pas subi.
# supervise.sh le lit dans l'environnement ; faute de declaration il retombe sur
# 12 en le SIGNALANT desormais a chaque demarrage. Le declarer ici est ce qui le
# rend auditable : la valeur effective vit dans un fichier que l'operateur ouvre,
# pas dans un defaut de shell que personne ne lit.
#
# 42 POUR po-2024 (arbitrage user 2026-09-21, mission ai-01
# msg-20260921T203652-qxg3en) : la VM WSL est passee de 24 032 a 40 110 Mo
# (.wslconfig memory=40GB). Le nombre est le PLAFOND D'ADMISSION, egal a la
# somme des caps declares des trois jambes (8x1536 docker + 12x1536 waiters +
# 2x6144 lean = 43 008 Mo) : sous l'ancien 12 Go, la garde refusait des slots
# sains -- les 2 slots lean ne demarraient JAMAIS tant que les autres familles
# etaient en vol. Les vrais murs restent les caps par conteneur (docker
# --memory) et le plafond vmmem de la VM ; l'hote garde sa moitie au-dela de
# la VM, comme `MemoryHigh` de coursia-ci.slice sur les machines qui deployent
# la slice (po-2024 ne la deploie pas : ici le budget n'a pas de mur kernel
# derriere lui).
#
# LES TROIS JAMBES DOIVENT ANNONCER LE MEME NOMBRE. `assert_memory_budget`
# somme les conteneurs label `coursia-ci=1` de TOUTES les familles : deux jambes
# qui divergeraient refuseraient leurs slots l'une contre l'autre, et le message
# d'erreur ne nommerait pas la divergence -- il parlerait de memoire en vol.
export COURSIA_RUNNER_BUDGET_GB=42

# BUDGET CPU INTER-FAMILLES (#15574 item 3, arbitrage coordinateur du
# 2026-10-01, comment 5933689033). supervise.sh le lit (assert_cpu_budget) :
# somme des caps CPU des familles d'EXECUTION -- cette jambe-ci (start) et la
# jambe lean ; les waiters, oisifs, en sont EXCLUS depuis la meme decision.
# Refus au demarrage au depassement, jamais avertissement. Inerte a 0 ou
# absent : c'etait l'etat anterieur de cette machine, et la mesure #18673
# (637 jobs lourds / 7 j, p90/mediane ~9,4x, co-residence 0 -> 3+ voisins :
# mediane x21) a nomme la sur-souscription 48 vCPU declares / 16 disponibles
# comme mecanisme.
#
# DEUX ECARTS CONSIGNES par rapport au texte de l'arbitrage :
#   - 30, pas 24 : docker 6x3 + lean 2x6 = 30. A 24, la jambe lean serait
#     REFUSEE au demarrage (le garde somme les familles d'execution, waiters
#     exclus -- test 60 de test_supervise_guards.sh le demontre sur les deux
#     sens) : exactement le verrou « service failed » que l'arbitrage citait
#     pour ECARTER le budget 16. 30 est le plus petit budget ou la flotte
#     ordonnee (docker 6 + lean 2) demarre -- sur-souscription 1,875x au
#     lieu de 3,0x.
#   - le service passe de start 8 a start 6 (conforme a l'arbitrage) dans
#     coursia-runner.service : la reduction de 24 a 18 vCPU docker vit la.
#
# Point de retour mesure J+7 (prevu par l'arbitrage) : rejeu de
# characterize_runner_variance.py sur la meme fenetre ; si le ratio
# p90/mediane des jobs lourds ne descend pas sous 5x, passage a 16 avec
# right-sizing -- qui devra alors aussi redimensionner la jambe lean, sinon
# elle seule depasse le budget.
#
# LES DEUX JAMBES D'EXECUTION PORTENT LE MEME NOMBRE (runner et lean) : le
# garde fire au demarrage de chacune et somme l'autre. La jambe waiters n'en
# declare pas : depuis l'exclusion, un demarrage de waiters n'ajoute rien a
# la somme -- la declarer serait du decor.
export COURSIA_RUNNER_CPU_BUDGET=30

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
