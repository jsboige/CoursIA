#!/usr/bin/env bash
# Slot runner RESERVE a la verification de `main` (ai-01, WSL Ubuntu).
#
# POURQUOI CE SCRIPT EXISTE (#25510, tranche T-L)
# ----------------------------------------------
# Le job CPU de `main` (push) est un job REQUIS : tant qu'il n'a pas de
# verdict, `main` n'est pas verifie. Il etait route sur le meme pool que les
# PRs (`coursia-ephemeral`), et il a donc attendu derriere elles.
#
# MESURE (2026-11-12, job CPU de `main`) : le job est reste en file plus de
# 27 minutes, avec 31 runners sur 31 occupes par des PRs. La verification de
# `main` n'a donc pas de place propre : elle est un client de plus d'une file
# qui sert d'abord les PRs.
#
# CE QUE CE SCRIPT FAIT
# ---------------------
#   1. decrit UN slot reserve, dont les labels sont
#      `self-hosted,coursia-main,coursia-linux` ;
#   2. pose des labels DISJOINTS du pool PR : le slot ne porte JAMAIS
#      `coursia-ephemeral` (le script REFUSE un `COURSIA_MAIN_LABELS` qui le
#      contiendrait -- sinon le slot reserve redeviendrait un client du pool PR,
#      et le probleme qu'il est cense resoudre revient) ;
#   3. ne supprime JAMAIS un slot, et ne touche JAMAIS un slot occupe ;
#   4. est idempotent : un slot deja present est signale, pas recree.
#
# LES TROIS MODES (rien n'est fait sans `--apply`)
# --------------------------------------------------
#   --dry-run (defaut) : affiche la commande `docker run` exacte. Aucun
#                         conteneur n'est cree, aucun token n'est mint, et
#                         docker n'est meme pas requis : ce mode est donc
#                         verifiable partout (CI comprise).
#   --check             : compare l'etat VIVANT (docker inspect) a la
#                         specification ; sort en 1 sur derive (labels,
#                         famille, cap memoire, etat de marche). C'est
#                         l'organe du critere "le slot existe et il est
#                         vraiment reserve".
#   --apply             : cree le slot s'il est absent. Mint du registration
#                         token via `gh` (GH_TOKEN fourni par l'environnement,
#                         jamais en dur).
#
# LE REPLI ECRIT (quand le runner tombe)
# ---------------------------------------
# Un slot reserve qui tombe laisse le job de `main` en file : le workflow
# `scripts-tests.yml` porte alors une entree `workflow_dispatch` nommee
# `runner_override`, qui rejoue la MEME verification sur `ubuntu-latest` :
#
#   gh workflow run scripts-tests.yml -f runner_override=ubuntu-latest
#
# La commande est ecrit ici, dans le corps du workflow, et verrouillee par
# `scripts/tests/test_main_slot_reserved.py` (qui verifie aussi que le
# dry-run porte les bons labels et que le script REFUSE un label
# `coursia-ephemeral`).
#
# EXEMPLE
# -------
#   ./create-main-slot.sh --check
#   ./create-main-slot.sh --dry-run
#   GH_TOKEN=... ./create-main-slot.sh --apply
#
# Refs : #25510 (T-L) ; `persist/README.md` (table de correspondance) ;
#        `po-2024/create-persist-slots.sh` (modele : memes trois modes,
#        memes labels disjoints).
set -u

REPO="${COURSIA_REPO:-jsboige/CoursIA}"
PREFIX="${COURSIA_MAIN_PREFIX:-myia-ai-01-linux-main}"
SLOT="${COURSIA_MAIN_SLOT:-1}"
MEMORY="${COURSIA_MAIN_MEMORY:-4g}"
PIDS="${COURSIA_MAIN_PIDS:-512}"
CPUS="${COURSIA_MAIN_CPUS:-3}"
IMAGE="${COURSIA_MAIN_IMAGE:-ghcr.io/jsboige/coursia-runner:latest}"
LABELS="${COURSIA_MAIN_LABELS:-self-hosted,coursia-main,coursia-linux}"
CGROUP_PARENT="${COURSIA_CGROUP_PARENT:-coursia-ci.slice}"
BASE="${COURSIA_MAIN_BASE:-$HOME/CoursIA-runners-main}"
WORK_MOUNT="/home/runner/_work"
TOOLCACHE_MOUNT="/opt/hostedtoolcache"

# Le label de la famille PR. Un slot reserve qui le porterait ne serait plus
# reserve : il redeviendrait un client du pool PR, et la file de `main`
# recommencerait a attendre derriere les PRs.
EPHEMERAL_LABEL="coursia-ephemeral"

MODE="dry-run"

usage() {
  sed -n '2,58p' "$0" | sed 's/^# \{0,1\}//'
  exit "${1:-0}"
}

log() { printf '%s\n' "$*"; }
err() { printf 'ERREUR : %s\n' "$*" >&2; }

# --- arguments --------------------------------------------------------------
while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run) MODE="dry-run" ;;
    --apply) MODE="apply" ;;
    --check) MODE="check" ;;
    -h|--help) usage 0 ;;
    *) err "argument inconnu : $1" ; usage 1 ;;
  esac
  shift
done

# --- garde des labels : DISJOINTS du pool PR --------------------------------
# Ce controle est fail-closed et precede toute sortie : un slot reserve qui
# porterait `coursia-ephemeral` ne resoudrait pas le probleme qu'il est cense
# resoudre, et la erreur serait invisible (le job tournerait, mais en queue).
case ",${LABELS}," in
  *",${EPHEMERAL_LABEL},"*)
    err "labels '${LABELS}' : un slot reserve ne peut PAS porter '${EPHEMERAL_LABEL}' (il redeviendrait un client du pool PR)"
    exit 2
    ;;
esac
case ",${LABELS}," in
  *,coursia-main,*) : ;;
  *)
    err "labels '${LABELS}' : le label 'coursia-main' est obligatoire (c'est lui que vise le job CPU de main)"
    exit 2
    ;;
esac

# --- garde : docker n'est requis que pour l'etat VIVANT ----------------------
# Le `--dry-run` n'a besoin de rien : il imprime une commande. C'est ce qui
# rend la forme verifiable en CI, ou docker n'est pas installe.
if [ "$MODE" != "dry-run" ]; then
  command -v docker >/dev/null 2>&1 || { err "docker absent de ce PATH"; exit 2; }
fi

slot_name() { printf '%s-%s' "$PREFIX" "$SLOT"; }

# Commande de creation du slot. Le corps isole pour que `--dry-run` imprime
# exactement la ligne executee en `--apply` (une seule source de verite).
run_cmd() {
  local name slot_vol cfg_vol
  name="$(slot_name)"
  slot_vol="${BASE}/${name}-work"
  cfg_vol="${BASE}/${name}-config"

  cat <<EOF
docker run -d --name ${name} \\
  --cpus=${CPUS} --memory=${MEMORY} --pids-limit=${PIDS} \\
  --label coursia-ci=1 --label coursia-family=main \\
  ${CGROUP_PARENT:+--cgroup-parent=${CGROUP_PARENT}} \\
  --security-opt=no-new-privileges \\
  -v ${TOOLCACHE_MOUNT}:${TOOLCACHE_MOUNT} \\
  -v ${slot_vol}:${WORK_MOUNT} \\
  -v ${cfg_vol}:/home/runner/.runner \\
  -e RUNNER_MODE=persistent \\
  -e ACTIONS_RUNNER_INPUT_TOKEN=\${TOKEN} \\
  -e ACTIONS_RUNNER_INPUT_URL=https://github.com/${REPO} \\
  -e ACTIONS_RUNNER_INPUT_NAME=${name} \\
  -e ACTIONS_RUNNER_INPUT_LABELS=${LABELS} \\
  ${IMAGE}
EOF
}

# --- etat vivant du slot ---------------------------------------------------
slot_state() {
  local name
  name="$(slot_name)"
  if ! docker inspect "$name" >/dev/null 2>&1; then
    printf 'ABSENT'
    return
  fi
  docker inspect --format '{{.HostConfig.Memory}} {{.HostConfig.PidsLimit}} {{.HostConfig.NanoCpus}} {{.State.Running}}' "$name" 2>/dev/null
}

expected_memory_bytes() {
  case "$1" in
    *g) printf '%s' "$((${1%g} * 1024 * 1024 * 1024))" ;;
    *m) printf '%s' "$((${1%m} * 1024 * 1024))" ;;
    *) printf '%s' "$1" ;;
  esac
}

expected_nano_cpus() {
  case "$1" in
    ''|*[!0-9]*) err "COURSIA_MAIN_CPUS doit etre un entier (mesure : '$1')" ; return 1 ;;
  esac
  printf '%s' "$(( $1 * 1000000000 ))"
}

# --- mode --check : derive entre l'etat vivant et la specification ---------
mode_check() {
  local rc=0 name state mem pids nano running want_mem want_nano
  want_mem="$(expected_memory_bytes "$MEMORY")"
  want_nano="$(expected_nano_cpus "$CPUS")" || return 2
  log "Specification : slot=$(slot_name) cpus=${CPUS} memory=${MEMORY} pids=${PIDS} labels=${LABELS}"
  log ""
  name="$(slot_name)"
  state="$(slot_state)"
  if [ "$state" = "ABSENT" ]; then
    log "[ABSENT ] ${name} — a creer (--apply)"
    rc=1
  else
    mem="$(printf '%s' "$state" | cut -d' ' -f1)"
    pids="$(printf '%s' "$state" | cut -d' ' -f2)"
    nano="$(printf '%s' "$state" | cut -d' ' -f3)"
    running="$(printf '%s' "$state" | cut -d' ' -f4)"
    log "[PRESENT] ${name} memory=${mem} pids=${pids} cpus=${nano} running=${running}"
    if [ "$mem" != "$want_mem" ]; then
      log "  DERIVE : cap memoire attendu ${want_mem} (${MEMORY}), mesure ${mem}"
      rc=1
    fi
    if [ "$pids" != "$PIDS" ]; then
      log "  DERIVE : cap pids attendu ${PIDS}, mesure ${pids}"
      rc=1
    fi
    if [ "$nano" != "$want_nano" ]; then
      log "  DERIVE : cap cpus attendu ${want_nano}, mesure ${nano}"
      rc=1
    fi
    # fail-closed : un slot present mais ARRETE ne peut pas executer de job.
    # Son etat de marche est donc une derive, au meme titre qu'un cap ou un
    # label non conforme.
    if [ "$running" != "true" ]; then
      log "  DERIVE : slot attendu en marche (running=true), mesure '${running}'"
      rc=1
    fi
    if ! docker inspect --format '{{range .Config.Env}}{{println .}}{{end}}' "$name" 2>/dev/null \
        | grep -qx "ACTIONS_RUNNER_INPUT_LABELS=${LABELS}"; then
      log "  DERIVE : labels attendus '${LABELS}', mesure :"
      docker inspect --format '{{range .Config.Env}}{{println .}}{{end}}' "$name" 2>/dev/null \
        | grep '^ACTIONS_RUNNER_INPUT_LABELS=' | sed 's/^/    /'
      rc=1
    fi
  fi
  log ""
  if [ "$rc" -eq 0 ]; then
    log "OK : le slot reserve est conforme a la specification."
  else
    log "DERIVE : le slot reserve s'ecarte de la specification (voir ci-dessus)."
  fi
  return $rc
}

# --- mint du registration token (jamais en dur) -----------------------------
mint_token() {
  local out tok
  out="$(gh api -X POST "repos/${REPO}/actions/runners/registration-token" --jq .token 2>&1)" || return 1
  tok="$(printf '%s' "$out" | tr -d '\r' | grep -m1 -oE '^[A-Za-z0-9]{20,}$')"
  [ -n "$tok" ] || { err "mint du token impossible : $(printf '%s' "$out" | cut -c1-200)"; return 1; }
  printf '%s' "$tok"
}

# --- mode --dry-run / --apply ----------------------------------------------
mode_create() {
  local name state token created=0 skipped=0
  mkdir -p "$BASE"
  name="$(slot_name)"

  if [ "$MODE" = "apply" ]; then
    token="$(mint_token)" || { err "abandon : pas de token d'enregistrement"; exit 3; }
  fi

  state="$(slot_state)"
  if [ "$state" != "ABSENT" ]; then
    log "[EXISTANT] ${name} — laisse en place (le script ne supprime jamais un slot)"
    skipped=$((skipped + 1))
  elif [ "$MODE" = "dry-run" ]; then
    log "--- creation prevue : ${name} ---"
    run_cmd
    log ""
    created=$((created + 1))
  else
    log "--- creation : ${name} ---"
    TOKEN="$token" eval "$(run_cmd)" || { err "echec de creation de ${name}"; exit 4; }
    created=$((created + 1))
  fi

  if [ "$MODE" = "dry-run" ]; then
    log "DRY-RUN : ${created} creation(s) prevue(s), ${skipped} slot(s) existant(s) laisse(s) en place."
    log "Aucun conteneur n'a ete cree. Rejouer avec --apply (et GH_TOKEN) pour creer."
    return 0
  fi
  log "APPLY : ${created} slot(s) cree(s), ${skipped} existant(s)."
  log "Verification : ./create-main-slot.sh --check"
  return 0
}

case "$MODE" in
  check) mode_check ;;
  *) mode_create ;;
esac
