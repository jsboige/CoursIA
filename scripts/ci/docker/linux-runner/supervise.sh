#!/usr/bin/env bash
# Superviseur de conteneurs runner ephemeres (mission #13378, finalisation
# ai-01 2026-09-01 sur demande user « debrayer le CI sur po-2024 »).
#
# POURQUOI CE SCRIPT EXISTE
# -------------------------
# Le census #13378 avait nomme le vrai facteur limitant du volet self-hosted :
# le runner est --ephemeral, donc il traite AU PLUS UN JOB puis se desenregistre.
# Cote Windows, chaque job supplementaire exigeait un re-register porte par une
# tache planifiee -- c'est ce qui rendait tout elargissement contre-productif.
#
# Le conteneur dissout ce verrou : la re-inscription n'est plus une tache a
# orchestrer, c'est un `docker run` de plus. Ce script est la boucle qui en
# tire la consequence -- un slot = une boucle, N slots = N jobs concurrents.
#
# CONTRAINTE QUI PRIME SUR TOUT : l'hote est AUSSI une workstation GPU et
# interactive. Les caps par conteneur et le N par defaut sont volontairement
# bas. Si l'empreinte gene la machine, baisser N ou arreter -- l'hote prime,
# et cette clause survit a toute decision d'elargissement (docs/ci/self-hosted-runners.md).
#
# USAGE
#   ./supervise.sh start [N] [--force]
#                                  # N slots (defaut 2) ; --force leve
#                                  # un sentinel STOP_FILE prealable
#   ./supervise.sh stop          # arret gracieux : pas de nouveau conteneur
#   ./supervise.sh status
#
# PREREQUIS : docker, gh authentifie avec droit admin sur le depot (le fetch
# du registration token l'exige). Le token n'est JAMAIS passe en argv --
# uniquement par -e, comme entrypoint.sh et manage_self_hosted_runner.py.
set -uo pipefail

REPO="${COURSIA_RUNNER_REPO:-jsboige/CoursIA}"
IMAGE="${COURSIA_RUNNER_IMAGE:-coursia-linux-runner:2.336.0}"
LABELS="${COURSIA_RUNNER_LABELS:-self-hosted,coursia-ephemeral,coursia-linux}"
NAME_PREFIX="${COURSIA_RUNNER_NAME_PREFIX:-myia-po-2024-linux-docker}"
STATE_DIR="${COURSIA_RUNNER_STATE_DIR:-$HOME/.coursia-runner}"
STOP_FILE="$STATE_DIR/stop"

# Caps par conteneur. Volontairement conservateurs : l'hote prime sur la CI.
CPUS="${COURSIA_RUNNER_CPUS:-3}"
MEMORY="${COURSIA_RUNNER_MEMORY:-4g}"
PIDS="${COURSIA_RUNNER_PIDS:-384}"

# Toolcache persistant : sans lui, chaque conteneur ephemere (un par job)
# re-telechargerait interpretes et outils via les actions setup-*. Le volume
# nomme survit aux conteneurs ; RUNNER_TOOL_CACHE dit aux actions ou chercher.
# Sa propriete runner:runner vient du point de montage du Dockerfile.
TOOLCACHE_VOLUME="${COURSIA_RUNNER_TOOLCACHE_VOLUME:-coursia-runner-toolcache}"
TOOLCACHE_MOUNT="${COURSIA_RUNNER_TOOLCACHE_MOUNT:-/opt/hostedtoolcache}"

# Cache de depot persistant, PAR SLOT (#14285) : --rm detruit /home/runner/_work
# avec le conteneur, donc actions/checkout re-clonait le depot ENTIER (3,54 GiB,
# 228 683 objets) a chaque job -- mesure #14285 : checkout 80-148 s contre
# 40-51 s sur ubuntu-latest, ~97 % du temps du job. Le volume nomme survit au
# conteneur ; checkout y trouve un clone existant et fait un git fetch
# incremental (son clean par defaut nettoie l'arbre entre jobs). Un volume PAR
# SLOT, jamais partage : deux jobs concurrents sur le meme _work se battraient
# sur le meme .git. Cout disque ~4 GiB par slot.
#
# GARDE LIEE (ne jamais dissocier) : la persistance de _work est acceptable
# UNIQUEMENT parce qu'aucun code de fork n'atteint ces runners (garde fork
# universelle + aucun trigger pull_request, cf linux-self-hosted-tests.yml ;
# ~95 forks etudiants). Un job voit les restes du precedent. Si cette garde
# saute un jour, ce volume devient un vecteur -- retirer la persistance AVANT
# d'ouvrir le runner aux forks.
WORK_VOLUME_PREFIX="${COURSIA_RUNNER_WORK_VOLUME_PREFIX:-coursia-runner-work}"
WORK_MOUNT="${COURSIA_RUNNER_WORK_MOUNT:-/home/runner/_work}"

mkdir -p "$STATE_DIR"

# Git Bash (MSYS) sous Windows reecrit les arguments de forme /posix/path des
# appels a docker.exe : -e RUNNER_TOOL_CACHE=/opt/hostedtoolcache devenait
# "C:/Program Files/Git/opt/hostedtoolcache" dans le conteneur (mesure :
# docker inspect Config.Env apres le premier demarrage). Ces deux variables
# sont inertes sous Linux et figent la conversion cote Windows.
export MSYS_NO_PATHCONV=1
export MSYS2_ARG_CONV_EXCL='*'

die() { echo "ERREUR: $*" >&2; exit 1; }

# #14259 Defaut 1+3 : compte et liste les PIDs des superviseurs actifs du
# meme `NAME_PREFIX`. La cle est `PPID==1` : un superviseur est le parent
# direct d'un slot_loop fork (mesure : PPID 72469 = LE superviseur ;
# les slot_loop forks heritent de l'argv du superviseur mais leur PPID
# est 72469, pas 1). Les subshells `$(fetch_token)` ont un PPID
# transitoire egalement != 1. Le `awk '$3==1'` est donc non cosmetique
# -- sans lui, un `start 4` rend 5 PIDs et le defense-positif echoue.
# Sortie : liste espacee de PIDs (vide si aucun superviseur).
supervisor_pids() {
  local me out
  # #14347 : `$$` = PID du bash principal, stable dans les subshells.
  # `$PPID` vaut 1 sous systemd (herite du lancement par PID 1 ; bash ne le
  # recompute pas pour les subshells) -- mesure : self=PPID=1 avec out=mon
  # propre PID, donc le garde s'auto-matchait et le service crash-loopait.
  me="$$"
  out="$(ps -ef 2>/dev/null | grep '[s]upervise\.sh start' | awk -v me="$me" '$2 != me && $3==1 {print $2}')"
  printf '%s\n' "$out"
}

fetch_token() {
  # Le registration token vaut 1 h et est jetable : un par demarrage de
  # conteneur. C'est la raison pour laquelle la boucle vit sur l'HOTE et non
  # dans l'image -- `gh` et ses credentials ne descendent jamais dans le
  # conteneur.
  gh api --method POST "repos/$REPO/actions/runners/registration-token" --jq .token 2>/dev/null
}

slot_loop() {
  local slot="$1"
  local name="${NAME_PREFIX}-${slot}"
  echo "[slot $slot] demarrage, nom runner=$name"
  while [ ! -f "$STOP_FILE" ]; do
    local token
    token="$(fetch_token)"
    if [ -z "$token" ]; then
      echo "[slot $slot] token indisponible (droit admin gh ?) -- nouvelle tentative dans 60 s" >&2
      sleep 60
      continue
    fi
    # --rm : le conteneur disparait avec le job. --ephemeral (dans l'entrypoint)
    # desenregistre le runner cote GitHub. Un cycle = un job, proprement --
    # mais le cache de depot (volume par slot) survit au conteneur (#14285).
    docker run --rm \
      --name "$name" \
      --cpus="$CPUS" --memory="$MEMORY" --pids-limit="$PIDS" \
      --security-opt=no-new-privileges \
      -v "$TOOLCACHE_VOLUME":"$TOOLCACHE_MOUNT" \
      -v "${WORK_VOLUME_PREFIX}-${slot}":"$WORK_MOUNT" \
      -e RUNNER_TOOL_CACHE="$TOOLCACHE_MOUNT" \
      -e ACTIONS_RUNNER_INPUT_TOKEN="$token" \
      -e ACTIONS_RUNNER_INPUT_URL="https://github.com/$REPO" \
      -e ACTIONS_RUNNER_INPUT_NAME="$name" \
      -e ACTIONS_RUNNER_INPUT_LABELS="$LABELS" \
      "$IMAGE" >>"$STATE_DIR/$name.log" 2>&1
    local rc=$?
    echo "[slot $slot] conteneur termine (rc=$rc)"
    # Anti-emballement : si le conteneur meurt immediatement et en boucle
    # (image absente, token refuse), on ne martele ni docker ni l'API.
    [ "$rc" -ne 0 ] && sleep 15 || sleep 2
  done
  echo "[slot $slot] arret demande, boucle terminee"
}

cmd_start() {
  local n="${1:-2}"
  local force=0
  # #14259 Defaut 2 : `--force` permet de lever un sentinel STOP pose
  # prealablement (par `cmd_stop`). Sans `--force`, un start en presence
  # du sentinel est REFUSE pour eviter qu'un operateur (ou un cron)
  # n'annule un arret gracieux par accident. La portee est la meme
  # qu'un `rm -f` historique -- seuls les appels explicites passent.
  [ "${2:-}" = "--force" ] && force=1
  command -v docker >/dev/null || die "docker introuvable"
  command -v gh >/dev/null || die "gh introuvable"
  docker image inspect "$IMAGE" >/dev/null 2>&1 \
    || die "image $IMAGE absente -- construire d'abord :
    docker build -t $IMAGE scripts/ci/docker/linux-runner/"
  docker volume create "$TOOLCACHE_VOLUME" >/dev/null \
    || die "volume $TOOLCACHE_VOLUME impossible a creer -- docker volume create"
  # #14259 Defaut 1 : garde d'idempotence. `pgrep` n'existe PAS sous Git
  # Bash (mesure 2026-09-02 : command-not-found silencieux derriere
  # `2>/dev/null`). La forme portable utilise `ps -ef` + `awk '$3==1'`
  # (PPID==1 filtre les slot_loop forks et les subshells `$(...)` qui
  # heritent de l'argv du parent -- mesure : un `start 4` produit 5
  # lignes de `ps -ef | grep` mais UN seul superviseur, PPID==1). Si
  # un superviseur du meme `NAME_PREFIX` est deja actif, on REFUSE et
  # on nomme les PIDs -- un deuxieme `start` produirait deux boucles
  # concurrantes portant des copies differentes de l'environnement
  # (incident po-2024 2026-09-02, plusieurs PRs de contenu bloquees).
  local existing_pids
  existing_pids="$(supervisor_pids)"
  if [ -n "$existing_pids" ]; then
    die "un superviseur $NAME_PREFIX est deja actif (PID $existing_pids) ;
utiliser '$0 stop' d'abord, ou relancer sous une machine differente."
  fi
  # #14259 Defaut 2 : si le sentinel STOP_FILE est pose, refuser sauf
  # `--force`. C'est le mecanisme cle qui protege un arret gracieux :
  # un `stop` pose le sentinel, les boucles existantes ne relancent
  # plus de conteneur, et un `start` ulterieur NE DOIT PAS effacer
  # le sentinel sinon le superviseur (s'il survit) reprendrait. Le
  # seul moyen de re-marcher apres un stop est `--force`, qui dit
  # explicitement « j'ai conscience que je relance sur un stop en
  # cours ».
  if [ -f "$STOP_FILE" ] && [ "$force" -ne 1 ]; then
    die "sentinel STOP_FILE present ($STOP_FILE) -- un arret gracieux
est en cours. Attendre la fin des jobs, faire '$0 stop' (no-op si deja
fait) puis '$0 start', OU relancer avec '$0 start $n --force'."
  fi
  # Sur succes, on leve le sentinel -- le superviseur qui demarre prend
  # la main sur l'etat precedent (Defaut 2 dans son volet `start`
  # historiquement effacait sans condition ; ici il n'efface que si
  # on a passe la garde --force).
  rm -f "$STOP_FILE"
  echo "demarrage de $n slot(s) ; caps par conteneur : cpus=$CPUS memory=$MEMORY pids=$PIDS ; toolcache=$TOOLCACHE_VOLUME -> $TOOLCACHE_MOUNT ; cache depot=${WORK_VOLUME_PREFIX}-{1..$n} -> $WORK_MOUNT"
  for i in $(seq 1 "$n"); do
    # Volume de cache de depot par slot : cree ici pour echouer tot avec un
    # message clair (docker run -v creerait le volume tout seul, mais muet).
    docker volume create "${WORK_VOLUME_PREFIX}-${i}" >/dev/null \
      || die "volume ${WORK_VOLUME_PREFIX}-${i} impossible a creer -- docker volume create"
    slot_loop "$i" &
    echo "$!" >> "$STATE_DIR/pids"
  done
  echo "slots lances. Arret gracieux : $0 stop"
  wait
}

cmd_stop() {
  # Arret GRACIEUX : on pose le sentinel, les boucles ne relancent plus de
  # conteneur. Le job en cours va a son terme -- on ne tue pas un job qui
  # tourne, il rendrait un rouge qui ne veut rien dire.
  touch "$STOP_FILE"
  echo "sentinel pose : aucun nouveau conteneur ne sera lance."
  echo "Les jobs en cours vont a leur terme. Pour couper net (deconseille) :"
  echo "  docker ps --filter name=$NAME_PREFIX -q | xargs -r docker kill"
}

cmd_status() {
  echo "== superviseurs actifs =="
  # #14259 Defaut 3 : compte par PPID==1 (cf supervisor_pids). Un compte
  # > 1 signale une anomalie (deux superviseurs concurrents portant des
  # copies differentes de l'environnement -- incident 2026-09-02). On
  # ixe le format pour qu'un grep ulterieur (alerting, sweep CI)
  # puisse matcher une ligne `superviseurs actifs : N`.
  local pids
  pids="$(supervisor_pids)"
  if [ -z "$pids" ]; then
    echo "  superviseurs actifs : 0"
  else
    local count
    count="$(echo "$pids" | wc -l | tr -d ' ')"
    if [ "$count" -gt 1 ]; then
      echo "  superviseurs actifs : $count (PID $pids) -- ANOMALIE : >1 superviseur concurrent"
    else
      echo "  superviseurs actifs : $count (PID $pids)"
    fi
  fi
  echo "== conteneurs runner en cours =="
  docker ps --filter "name=$NAME_PREFIX" --format '  {{.Names}}  {{.Status}}  {{.RunningFor}}' 2>/dev/null || true
  echo "== runners enregistres cote GitHub =="
  gh api "repos/$REPO/actions/runners" \
    --jq '.runners[]|"  \(.name) [\(.status)] busy=\(.busy) labels=\([.labels[].name]|join(","))"' 2>/dev/null \
    || echo "  (droit admin requis pour lire l'inventaire)"
  [ -f "$STOP_FILE" ] && echo "== sentinel STOP pose : les boucles ne relancent plus =="
}

case "${1:-}" in
  start)  shift; cmd_start "${1:-2}" "${2:-}" ;;
  stop)   cmd_stop ;;
  status) cmd_status ;;
  *) echo "usage: $0 {start [N] [--force]|stop|status}"; exit 2 ;;
esac
