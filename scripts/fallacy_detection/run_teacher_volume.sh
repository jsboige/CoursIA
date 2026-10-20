#!/usr/bin/env bash
# Wrapper POSIX du run volume tranche B #17578 -- lane myia-po-2027:CoursIA
# Jumeau de `run_teacher_volume.ps1` (critere 2a de l'EPIC #10643, organe
# `scripts/ci/check_companion_coverage.py`).
#
# Detache par le planificateur de la plateforme (cron/systemd --user) ; la
# reprise se fait par checkpoint append-par-paire, comme cote Windows.
# La cle VLLM_API_KEY_MEDIUM est lue de master.env (gitignore) et N'EST
# JAMAIS ecrite ni echoee : pas de `set -x` dans ce script, jamais.
#
# Historique des corrections (mesure du 2026-10-10, identique au jumeau .ps1) :
#  * L'etape `--split val` a ete RETIREE. val_fr etait deja complet
#    (1629/1629) : la passe ne generait rien mais reecrivait
#    `report_val_fr.json` a chaque run, donc churnait un fichier du scope
#    revendique par `myia-po-2023:CoursIA` (`.../data/teacher/**`) sans rien
#    produire. Le scope de cette lane est `test_fr.jsonl` + `report_test_fr.json`.
#  * Un PRE-FLIGHT a ete ajoute. Sans lui, un hub injoignable faisait bruler
#    le budget de retries (~70 s) et rendre un rc=1 indiscernable d'un defaut
#    de donnees -- 4 relances ont ete perdues ainsi.
#
# Usage :
#   ./run_teacher_volume.sh [--repo-root DIR] [--master-env FILE]
#                           [--venv-scripts DIR] [--log FILE]
#                           [--hub-host HOST] [--hub-port N]
#                           [--split S] [--lang L] [--limit N]
#
# Les memes valeurs sont acceptees en variables d'environnement
# (REPO_ROOT, MASTER_ENV_PATH, VENV_SCRIPTS, LOG_PATH, HUB_HOST, HUB_PORT,
# SPLIT, LANG, LIMIT) ; les options de ligne de commande l'emportent.

set -u

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT="${REPO_ROOT:-$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)}"
MASTER_ENV_PATH="${MASTER_ENV_PATH:-$REPO_ROOT/.secrets/master.env}"
# Adaptation bi-OS : le venv Windows expose `Scripts/`, POSIX expose `bin/`.
VENV_SCRIPTS="${VENV_SCRIPTS:-$REPO_ROOT/venv/bin}"
LOG_PATH="${LOG_PATH:-$REPO_ROOT/.tmp/teacher_volume.log}"
HUB_HOST="${HUB_HOST:-192.168.0.47}"
HUB_PORT="${HUB_PORT:-5002}"
SPLIT="${SPLIT:-test}"
LANG_OPT="${LANG:-fr}"
LIMIT="${LIMIT:-0}"

while [ $# -gt 0 ]; do
    case "$1" in
        --repo-root)    REPO_ROOT="$2"; shift 2 ;;
        --master-env)   MASTER_ENV_PATH="$2"; shift 2 ;;
        --venv-scripts) VENV_SCRIPTS="$2"; shift 2 ;;
        --log)          LOG_PATH="$2"; shift 2 ;;
        --hub-host)     HUB_HOST="$2"; shift 2 ;;
        --hub-port)     HUB_PORT="$2"; shift 2 ;;
        --split)        SPLIT="$2"; shift 2 ;;
        --lang)         LANG_OPT="$2"; shift 2 ;;
        --limit)        LIMIT="$2"; shift 2 ;;
        -h|--help)
            sed -n 's/^# \{0,1\}//p' "$0" | sed -n '/^Usage :/,/^$/p'
            exit 0 ;;
        *)
            printf 'option inconnue : %s (voir --help)\n' "$1" >&2
            exit 64 ;;
    esac
done

mkdir -p -- "$(dirname -- "$LOG_PATH")"

log() {
    printf '[%s] %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*" >> "$LOG_PATH"
}

# --- Lecture de la cle : jamais echoee, jamais tracee. ---
KEY=""
if [ -r "$MASTER_ENV_PATH" ]; then
    KEY=$(sed -n -E 's/^[[:space:]]*VLLM_API_KEY_MEDIUM[[:space:]]*=[[:space:]]*//p' \
          "$MASTER_ENV_PATH" | tail -n 1 | sed -E 's/[[:space:]]+$//')
fi
if [ -z "$KEY" ]; then
    log "FATAL: VLLM_API_KEY_MEDIUM absente de $MASTER_ENV_PATH"
    exit 1
fi
VLLM_API_KEY_MEDIUM="$KEY"
export VLLM_API_KEY_MEDIUM
unset KEY

# --- Pre-flight : le hub vit sur le LAN MyIA, cette machine peut etre un portable. ---
probe_hub() {
    if command -v timeout >/dev/null 2>&1; then
        timeout 5 bash -c "exec 3<>/dev/tcp/$HUB_HOST/$HUB_PORT" 2>/dev/null
    elif command -v gtimeout >/dev/null 2>&1; then
        gtimeout 5 bash -c "exec 3<>/dev/tcp/$HUB_HOST/$HUB_PORT" 2>/dev/null
    elif command -v nc >/dev/null 2>&1; then
        nc -z -w 5 "$HUB_HOST" "$HUB_PORT" 2>/dev/null
    else
        # Dernier recours : pas de garde de duree, mais le refus reste propre.
        bash -c "exec 3<>/dev/tcp/$HUB_HOST/$HUB_PORT" 2>/dev/null
    fi
}

if ! probe_hub; then
    ipv4=$(ip -4 -o addr show scope global 2>/dev/null \
           | awk '{split($4,a,"/"); printf "%s/%s [%s], ", a[1], a[2], $2}')
    # Repli sans `ip` (macOS, MSYS) : liste nue, sans masque ni interface.
    [ -n "$ipv4" ] || ipv4=$(hostname -I 2>/dev/null | tr ' ' '\n' \
                             | grep -vE '^(127\.|169\.254\.|$)' | tr '\n' ' ')
    [ -n "$ipv4" ] || ipv4="(non lisible)"
    log "FATAL: hub ${HUB_HOST}:${HUB_PORT} INJOIGNABLE -- generation NON lancee, aucun checkpoint touche."
    log "  IPv4 actives : ${ipv4%, }"
    log "  Attendu : une interface dans 192.168.0.x (LAN MyIA). Voir docs/reference/cluster-agents.md, regle de routage."
    exit 2
fi
log "pre-flight OK : hub ${HUB_HOST}:${HUB_PORT} joignable"

PYTHON="${PYTHON:-python3}"
if [ -x "$VENV_SCRIPTS/python" ]; then
    PYTHON="$VENV_SCRIPTS/python"
elif [ -x "$VENV_SCRIPTS/python3" ]; then
    PYTHON="$VENV_SCRIPTS/python3"
fi

log "=== ${SPLIT}_${LANG_OPT} start (reprise depuis checkpoint) ==="
(
    cd -- "$REPO_ROOT/scripts" || exit 3
    "$PYTHON" -m fallacy_detection.generate_teacher_corpus \
        --split "$SPLIT" --lang "$LANG_OPT" --limit "$LIMIT"
) >> "$LOG_PATH" 2>&1
RC=$?
log "=== ${SPLIT}_${LANG_OPT} rc=${RC} === DONE ==="
exit "$RC"