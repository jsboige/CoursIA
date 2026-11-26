#!/usr/bin/env bash
# Creation versionnee des slots runner PERSIST de myia-po-2024 (WSL Ubuntu).
#
# POURQUOI CE SCRIPT EXISTE (issue #21978, volet 3)
# ---------------------------------------------------
# Les slots `myia-po-2024-linux-persist-*` ont ete crees A LA MAIN (7
# conteneurs, `--memory 1610612736` = 1,5 Gio, `--pids-limit 384`, et AUCUNE
# borne pids sur persist-5/6/7). Aucun fichier du depot ne les decrit : le
# grep `linux-persist` sur /etc/systemd et /usr/local/bin ne rend rien, et le
# wrapper `coursia-runner-start.sh` ne declare que
# `COURSIA_RUNNER_NAME_PREFIX="myia-po-2024-linux-docker"` (famille docker
# ephemere). La composition des caps n'etait donc ni versionnee ni
# verifiable -- c'est ce que ce script ferme.
#
# CE QUE LE SCRIPT FAIT
# ---------------------
#   1. cree les slots PERSIST (mode `RUNNER_MODE=persistent` : un conteneur
#      par slot, vivant entre les jobs, volume de config par slot) ;
#   2. pose les CAPS explicites : `--cpus 3 --memory 4g --pids-limit 512` ;
#   3. pose des LABELS DISJOINTS par famille : un slot persist porte
#      `coursia-persistent` et NE porte PAS `coursia-ephemeral` ;
#   4. ne supprime JAMAIS un slot, et ne touche JAMAIS un slot occupe ;
#   5. est idempotent : un slot deja present est signale, pas recree.
#
# LES TROIS MODES (rien n'est fait sans `--apply`)
# --------------------------------------------------
#   --dry-run (defaut) : affiche les commandes `docker run` exactes. Aucun
#                         conteneur n'est cree, aucun token n'est mint.
#   --check             : compare l'etat VIVANT (docker inspect) a la
#                         specification ; sort en 1 sur derive (caps, labels,
#                         famille). C'est l'organe du critere 3 de #21978.
#   --apply             : cree les slots manquants. Mint du registration
#                         token via `gh` (GH_TOKEN fourni par l'environnement,
#                         jamais en dur).
#
# CE QUE LE SCRIPT NE FAIT PAS (et pourquoi)
# --------------------------------------------
#   - Il ne retire aucun conteneur : le_diminution de la famille est un
#     arbitrage de flotte (composition des caps sous `MemoryMax=22G` de
#     `coursia-ci.slice`), pas un geste de lane.
#   - Il ne touche pas aux workflows : le routage "job lourd -> slot lourd"
#     passe par un label de famille, et un label doit exister sur les runners
#     de TOUTES les machines avant qu'un workflow le vise. C'est une decision
#     de coordination (cf issue #21978, volet 1 et 2).
#
# EXEMPLE
# -------
#   ./create-persist-slots.sh --check
#   ./create-persist-slots.sh --dry-run
#   GH_TOKEN=... ./create-persist-slots.sh --apply
#
# Refs : issue #21978 (routage par label + creation versionnee) ;
#        issue #21802 (le -n xdist suit la limite memoire du conteneur) ;
#        persist/README.md ; po-2026/pool.sh (meme famille, slots ephemeres).
set -u

REPO="${COURSIA_REPO:-jsboige/CoursIA}"
PREFIX="${COURSIA_PERSIST_PREFIX:-myia-po-2024-linux-persist}"
SLOTS="${COURSIA_PERSIST_SLOTS:-2}"
MEMORY="${COURSIA_PERSIST_MEMORY:-4g}"
PIDS="${COURSIA_PERSIST_PIDS:-512}"
CPUS="${COURSIA_PERSIST_CPUS:-3}"
IMAGE="${COURSIA_PERSIST_IMAGE:-ghcr.io/jsboige/coursia-runner:latest}"
LABELS="${COURSIA_PERSIST_LABELS:-self-hosted,coursia-persistent,coursia-linux}"
CGROUP_PARENT="${COURSIA_CGROUP_PARENT:-coursia-ci.slice}"
BASE="${COURSIA_PERSIST_BASE:-$HOME/CoursIA-runners-persist}"
WORK_MOUNT="/home/runner/_work"
TOOLCACHE_MOUNT="/opt/hostedtoolcache"

MODE="dry-run"

usage() {
  sed -n '2,45p' "$0" | sed 's/^# \{0,1\}//'
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

# --- garde : la version du script doit etre lisible -------------------------
command -v docker >/dev/null 2>&1 || { err "docker absent de ce PATH"; exit 2; }

slot_name() { printf '%s-%s' "$PREFIX" "$1"; }

# Commande de creation d'un slot. Le corps est isole pour que `--dry-run`
# imprime exactement la ligne qui sera executee en `--apply` (une seule
# source de verite : pas de divergence entre ce qui est montre et ce qui est
# fait).
run_cmd() {
  local idx="$1" name slot_vol cfg_vol
  name="$(slot_name "$idx")"
  slot_vol="${BASE}/${name}-work"
  cfg_vol="${BASE}/${name}-config"

  cat <<EOF
docker run -d --name ${name} \\
  --cpus=${CPUS} --memory=${MEMORY} --pids-limit=${PIDS} \\
  --label coursia-ci=1 --label coursia-family=persistent \\
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

# --- etat vivant d'un slot --------------------------------------------------
slot_state() {
  local idx="$1" name
  name="$(slot_name "$idx")"
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

# `--cpus=N` est materialise par docker en `NanoCpus` (N * 1e9). La valeur
# attendue est un ENTIER de cpus (defaut 3) : une valeur decimale n'est pas
# supportee ici et serait refusee explicitement plutot que tronquee.
expected_nano_cpus() {
  case "$1" in
    ''|*[!0-9]*) err "COURSIA_PERSIST_CPUS doit etre un entier (mesure : '$1')" ; return 1 ;;
  esac
  printf '%s' "$(( $1 * 1000000000 ))"
}

# --- mode --check : derive entre l'etat vivant et la specification ---------
mode_check() {
  local rc=0 idx name state mem pids nano running want_mem want_nano
  want_mem="$(expected_memory_bytes "$MEMORY")"
  want_nano="$(expected_nano_cpus "$CPUS")" || return 2
  log "Specification : slots=${SLOTS} cpus=${CPUS} memory=${MEMORY} pids=${PIDS} labels=${LABELS}"
  log ""
  for idx in $(seq 1 "$SLOTS"); do
    name="$(slot_name "$idx")"
    state="$(slot_state "$idx")"
    if [ "$state" = "ABSENT" ]; then
      log "[ABSENT ] ${name} — a creer (--apply)"
      rc=1
      continue
    fi
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
      log "  DERIVE : cap cpus attendu ${want_nano} (${CPUS}), mesure ${nano}"
      rc=1
    fi
    # Reserve de la revue tierce (point 1 du crible #21985) : un slot ARRETE
    # dont les caps et les labels sont conformes sortait de `--check` avec
    # rc=0 -- l'etat de marche etait journalise mais jamais teste. `--check`
    # est fail-closed : un slot present mais arrete est une derive, au meme
    # titre qu'un cap ou un label non conforme (le slot ne peut pas executer
    # de job dans cet etat).
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
  done
  log ""
  if [ "$rc" -eq 0 ]; then
    log "OK : les ${SLOTS} slots persist sont conformes a la specification."
  else
    log "DERIVE : au moins un slot s'ecarte de la specification (voir ci-dessus)."
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
  local idx name state token created=0 skipped=0
  mkdir -p "$BASE"

  if [ "$MODE" = "apply" ]; then
    token="$(mint_token)" || { err "abandon : pas de token d'enregistrement"; exit 3; }
  fi

  for idx in $(seq 1 "$SLOTS"); do
    name="$(slot_name "$idx")"
    state="$(slot_state "$idx")"
    if [ "$state" != "ABSENT" ]; then
      log "[EXISTANT] ${name} — laisse en place (le script ne supprime jamais un slot)"
      skipped=$((skipped + 1))
      continue
    fi
    if [ "$MODE" = "dry-run" ]; then
      log "--- creation prevue : ${name} ---"
      run_cmd "$idx"
      log ""
      created=$((created + 1))
      continue
    fi
    log "--- creation : ${name} ---"
    TOKEN="$token" eval "$(run_cmd "$idx")" || { err "echec de creation de ${name}"; exit 4; }
    created=$((created + 1))
  done

  if [ "$MODE" = "dry-run" ]; then
    log "DRY-RUN : ${created} creation(s) prevue(s), ${skipped} slot(s) existant(s) laisse(s) en place."
    log "Aucun conteneur n'a ete cree. Rejouer avec --apply (et GH_TOKEN) pour creer."
    return 0
  fi
  log "APPLY : ${created} slot(s) cree(s), ${skipped} existant(s)."
  log "Verification : docker inspect --format '{{.HostConfig.Memory}} {{.HostConfig.PidsLimit}}' <nom>"
  return 0
}

case "$MODE" in
  check) mode_check ;;
  *) mode_create ;;
esac
