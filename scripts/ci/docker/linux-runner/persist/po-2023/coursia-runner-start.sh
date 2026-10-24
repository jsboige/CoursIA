#!/usr/bin/env bash
# Wrapper de demarrage du superviseur de runners Linux CoursIA -- myia-po-2023.
# Deploye le 2026-10-24 ; copie de reference dans
# scripts/ci/docker/linux-runner/persist/po-2023/coursia-runner-start.sh.
#
# Adapte de persist/coursia-runner-start.sh (po-2024, 2026-09-02) et de
# persist/po-2028/coursia-runner-start.sh (2026-10-20). Ce qui change ici :
#
#   - JETON : po-2023 n'a PAS de GH_RUNNERS_ADMIN_TOKEN dans son master.env
#     (verifie le 2026-10-24). La cascade ci-dessous essaie le jeton dedie
#     d'abord -- pour que la machine se range d'elle-meme dans la doctrine des
#     que le jeton sera provisionne -- puis les deux jetons generaux, puis
#     l'interop gh.exe. Les trois voies ont ete mesurees admin=true sur
#     jsboige/CoursIA le 2026-10-24.
#   - MEMOIRE : 3 slots de 4g au lieu de 8x1536, et une slice a 10G/12G au lieu
#     de 12G/14G -- cette VM porte 20 conteneurs GenAI vivants (~16,9 Go).
#     Detail de l'arithmetique dans /etc/systemd/system/coursia-ci.slice.
#   - DOCKER : docker-ce installe le 2026-10-24 avec /usr/sbin/policy-rc.d en
#     place, pour que son postinst ne prenne pas /var/run/docker.sock a Docker
#     Desktop (piege mesure sur po-2028 le 2026-10-20).
set -euo pipefail

REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/Dev/CoursIA}"
TOKEN_FILE="${COURSIA_MASTER_ENV:-$REPO_DIR/.secrets/master.env}"

# --- JETON D'ENREGISTREMENT ------------------------------------------------
# Il ne passe jamais par argv, ni par un commit, ni par un dashboard : il est
# relu a CHAQUE invocation, et meurt avec ce processus.
TOKEN=""
TOKEN_SOURCE=""
# Un jeton PRESENT n'est pas un jeton VALIDE. Mesure du 2026-10-25 sur cette
# machine : GITHUB_ACCESS_TOKEN et GITHUB_TOKEN existaient dans master.env
# (40 caracteres chacun) mais l'API les refusait -- « Bad credentials », 401.
# La cascade s'arretait sur le premier nom NON VIDE, le service demarrait,
# chaque enregistrement echouait en 401, et `Restart=always` rendait l'unite
# « active » : la panne se lisait comme un demarrage reussi. On VALIDE donc
# chaque candidat avant de l'accepter, et un candidat mort ne coupe plus la
# cascade.
#
# `gh api user` est le test le moins couteux qui distingue un jeton mort d'un
# jeton vivant, et il ne consomme aucun droit particulier.
_token_alive() {
    [ -n "${1:-}" ] || return 1
    command -v gh >/dev/null 2>&1 || return 1
    GH_TOKEN="$1" gh api user --jq .login >/dev/null 2>&1
}

# supervise.sh s'arrete sur « gh introuvable » -- autant le dire ici, avec le
# remede, plutot que de laisser l'unite echouer sur un message qui ne dit pas
# quoi installer.
if ! command -v gh >/dev/null 2>&1; then
    echo "FATAL: gh introuvable dans la distro -- supervise.sh en a besoin pour le registration-token. Installer le binaire (voir persist/po-2023/README.md)." >&2
    exit 1
fi

for _var in GH_RUNNERS_ADMIN_TOKEN GITHUB_ACCESS_TOKEN GITHUB_TOKEN; do
    if [ -f "$TOKEN_FILE" ]; then
        _v="$(sed -n "s/^${_var}=//p" "$TOKEN_FILE" | head -1 | tr -d '\r"')"
        if [ -n "$_v" ]; then
            if _token_alive "$_v"; then
                TOKEN="$_v"
                TOKEN_SOURCE="master.env:$_var"
                break
            fi
            echo "jeton mort ignore : master.env:$_var refuse par l'API (401) -- candidat suivant" >&2
        fi
    fi
done
if [ -z "$TOKEN" ]; then
    _GH_WIN="/mnt/c/Program Files/GitHub CLI/gh.exe"
    if [ -x "$_GH_WIN" ]; then
        _v="$("$_GH_WIN" auth token 2>/dev/null | tr -d '\r\n')"
        if _token_alive "$_v"; then
            TOKEN="$_v"
            TOKEN_SOURCE="gh.exe auth token"
        elif [ -n "$_v" ]; then
            echo "jeton mort ignore : gh.exe auth token refuse par l'API (401)" >&2
        fi
    fi
fi
if [ -z "$TOKEN" ]; then
    echo "FATAL: aucun jeton d'enregistrement VALIDE -- GH_RUNNERS_ADMIN_TOKEN / GITHUB_ACCESS_TOKEN / GITHUB_TOKEN de $TOKEN_FILE sont absents ou refuses (401), et gh.exe n'a rien rendu de valide" >&2
    exit 1
fi
echo "jeton d'enregistrement lu depuis $TOKEN_SOURCE (valide)" >&2

export DOCKER_HOST="unix:///var/run/docker-ce.sock"
export GH_TOKEN="$TOKEN"
export COURSIA_RUNNER_REPO="jsboige/CoursIA"
export COURSIA_RUNNER_NAME_PREFIX="myia-po-2023-linux-docker"
export COURSIA_RUNNER_STATE_DIR="/var/lib/coursia-runner"
export COURSIA_RUNNER_TOOLCACHE_VOLUME="coursia-runner-toolcache"

# BUDGET MEMOIRE AGREGE -- declare, pas subi (#19802 : la valeur est la SOMME
# DES CAPS de la composition vive).
#     3 slots docker x 4096 Mo = 12 288 Mo  (classe "Scripts Tests (CPU)")
#     --------------------------------------
#     total CAPS                12 288 Mo = 12 Go
# Aucune autre famille sur cette machine : pas de waiters (consigne ai-01),
# pas de jambe lean (consigne ai-01). Le budget reste un PLAFOND D'ADMISSION :
# il refuse de demarrer un slot au-dela de 12 Go, il ne borne pas ce qu'un slot
# deja lance consomme -- le mur kernel est la slice, ci-dessous.
export COURSIA_RUNNER_BUDGET_GB=12

# Parent cgroup : la seule limite inter-familles qui existe. Le nom EST
# `coursia-ci.slice` (pas le chemin imbrique) parce que ce daemon est docker-ce
# pilote systemd, qui resout une slice sur son nom.
export COURSIA_RUNNER_CGROUP_PARENT="coursia-ci.slice"
# assert_ci_slice REFUSE le demarrage si la slice est introuvable ou sans
# io.max. Elle est posee AVANT les conteneurs (ordre documente dans son en-tete).
export COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET=1

# BUDGET CPU INTER-FAMILLES -- somme des caps CPU des familles d'EXECUTION :
# 3 slots x 3 vCPU = 9. La consigne ai-01 demande la MOITIE des coeurs
# logiques de la VM WSL : 20 / 2 = 10. Declare a 10, donc 1 vCPU de marge
# non allouee. Le garde refuse au demarrage au depassement, jamais en
# avertissement ; a 0 ou absent il serait INERTE, c'est pourquoi il est ecrit.
export COURSIA_RUNNER_CPU_BUDGET=10

# Dimensionnement par slot -- classe "Scripts Tests (CPU)" (#16643) : pic
# mesure 3,5 Gio + agent + marge ~15 %. 1536m ferait tuer le job par OOM.
export COURSIA_RUNNER_CPUS=3
export COURSIA_RUNNER_MEMORY=4g
export COURSIA_RUNNER_PIDS=512

# Debit disque plafonne (valeurs de la doctrine po-2028). Role : interdire
# qu'un thrash PASSE L'ECHELLE, pas reguler un debit normal.
export COURSIA_RUNNER_DEVICE_WRITE_BPS=41943040
export COURSIA_RUNNER_DEVICE_READ_BPS=83886080

# #15095 : echec immediat si le demon du socket epingle ne repond pas --
# AVANT tout demarrage de slot et tout fetch de registration token (gh).
# Sans cette garde, un daemon arrete + Restart=always = le superviseur
# martelait docker/gh indefiniment.
if ! docker info >/dev/null 2>&1; then
    echo "FATAL: demon Docker indisponible sur DOCKER_HOST=$DOCKER_HOST (docker info echoue, #15095) -- reparer le daemon avant de relancer le service." >&2
    exit 1
fi

SUPERVISE="$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

# --- PURGE SENTINELLE PERIMEE (#15163) -------------------------------------
# supervise.sh pose "$STATE_DIR/stop" a l'arret gracieux et REFUSE de demarrer
# tant qu'elle est la. La sentinelle est un FICHIER : elle survit au reboot.
# Un arret gracieux suivi d'un redemarrage machine laissait donc l'unite
# echouer, et le pool restait a ZERO jusqu'a intervention humaine. Un ExecStart
# est une demande EXPLICITE : si aucun superviseur n'est vivant, la sentinelle
# ne protege plus rien, on la retire. Si un superviseur EST vivant, un arret est
# en cours : on n'interfere pas, et on sort en erreur.
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
