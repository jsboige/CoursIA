#!/usr/bin/env bash
# Pool d'exécuteurs éphémères GitHub Actions — myia-po-2026 (WSL Ubuntu)
# Labels: coursia-ephemeral,coursia-linux — 1 job = 1 runner, re-spawn auto.
# Source maintenue: D:\Dev\CoursIA-runners-p0\pool.sh (copie LF normalisée dans WSL).
set -u
POOL_SIZE="${POOL_SIZE:-8}"
REPO="jsboige/CoursIA"
BASE="$HOME/CoursIA-runners-p0"
BUNDLE="$BASE/actions-runner.tar.gz"
LOCK="$BASE/pool.lock"
# Cache d'outils PERSISTANT, hors de l'arbre ephemere (#17407/Q5, arbitrage ai-01
# 2026-09-22) : sans lui, setup-python telecharge un CPython nu sous slot-N/_work/_tool/
# que spawn_slot detruit (rm -rf) au job suivant — les appels par chemin absolu
# (test_guard_gauntlet.py:102 -> sys.executable) visent alors une cible disparue
# (exit 127, stdout vide = indiscernable de « le garde n'a rien detecte »). L'image
# Docker garde ce cache sous /opt/hostedtoolcache (persistant par construction).
# Par-SLOT : slot-N/toolcache survit au rm -rf de slot-N (chemin distinct) et un
# numero de slot n'est jamais concurrent avec lui-meme (spawn_slot bloque sur son
# job) — pas de race d'extraction partagee entre jobs simultanes.
TOOLCACHE_BASE="$BASE/toolcache"
export RUNNER_TOOL_CACHE="${RUNNER_TOOL_CACHE:-$TOOLCACHE_BASE/default}"
mkdir -p "$BASE"
exec >>"$BASE/pool.log" 2>&1

# Singleton: la tâche planifiee a RestartCount=3 — jamais deux superviseurs
exec 9>"$LOCK" || exit 1
flock -n 9 || { echo "$(date -Is) pool deja actif ($LOCK)"; exit 0; }

# Contrat de l'image (scripts/ci/docker/linux-runner/Dockerfile), volet ENV — qu'un slot natif ne peut
# PAS heriter, faute de conteneur. Mesure du 2026-09-22 sur cet hote : le python systeme est marque
# EXTERNALLY-MANAGED (/usr/lib/python3.12/EXTERNALLY-MANAGED) et `python3 -m pip install --dry-run
# pyyaml` est REFUSE (PEP 668). C'est le cas exact que le Dockerfile l.14-21 documente : « un workflow
# qui fait `import yaml || pip install pyyaml` meurt sur le pip ». Le pool pose donc lui-meme la
# variable ; elle est heritee par run.sh -> Runner.Worker -> etapes du job, par le meme canal que le
# PATH (mesure : le PATH de pool.sh se retrouve dans /proc/<pid>/environ des listeners).
export PIP_BREAK_SYSTEM_PACKAGES=1

# PATH (Q6, 2026-09-23, reserve secretaire c.37 + mesure /proc/<pid>/environ) :
# la relance du superviseur depuis une session interactive (fenetre Q5) herite le
# PATH de CETTE session — ~/.local/bin ABSENT des listeners. Le pool rend son
# contrat independant du contexte de lancement : ~/.local/bin en tete (gh 2.90.0
# et python y sont poses).
export PATH="$HOME/.local/bin:$PATH"

mint_token() { gh.exe api -X POST "repos/$REPO/actions/runners/registration-token" --jq .token; }

# Contrat de l'image, volet BINAIRES. Le pool ne telecharge PAS `gh` (l'image l'epingle par SHA-256 :
# un telechargement non verifie serait un maillon de supply chain pour rien) — il cree le seul lien
# localement sur (`python` -> python3, idempotent) et CRIE si `gh` manque. Non bloquant a dessein :
# couper le pool priverait la flotte de capacite pour un defaut qui, lui, produit surtout des verts
# suspects (les gardes sortent en exit 0 SANS poster, cf. README) — un log qu'on ne peut pas manquer
# vaut mieux qu'un pool a l'arret. `~/.local/bin` est en TETE du PATH du pool par construction (export Q6, 2026-09-23) — plus dependant du contexte de lancement.
ensure_host_contract() {
  local bin="$HOME/.local/bin" rc=0
  mkdir -p "$bin"
  [ -x "$bin/python" ] || ln -sf "$(command -v python3)" "$bin/python"
  [ -x "$bin/python" ] || { echo "$(date -Is) CONTRAT: python nu ABSENT de $bin"; rc=1; }
  [ -x "$bin/gh" ]     || { echo "$(date -Is) CONTRAT: gh ABSENT de $bin — poser la release Linux officielle (l'image epingle 2.99.0+SHA256) ; sans lui des gardes sortent en exit 0 SANS poster"; rc=1; }
  [ -n "${PIP_BREAK_SYSTEM_PACKAGES:-}" ] || { echo "$(date -Is) CONTRAT: PIP_BREAK_SYSTEM_PACKAGES non pose"; rc=1; }
  command -v gh >/dev/null 2>&1 || { echo "$(date -Is) CONTRAT: gh INVISIBLE du PATH du pool (relance depuis session interactive ?) — existence du fichier ne suffit pas (reserve #17406 c.5784716255)"; rc=1; }
  mkdir -p "$RUNNER_TOOL_CACHE" 2>/dev/null || { echo "$(date -Is) CONTRAT: RUNNER_TOOL_CACHE non creable ($RUNNER_TOOL_CACHE)"; rc=1; }
  [ "$rc" -eq 0 ] && echo "$(date -Is) contrat d'image: bins/python OK ($( "$bin/gh" --version 2>/dev/null | head -1 )), toolcache=$RUNNER_TOOL_CACHE"
  return $rc
}

ensure_bundle() {
  [ -s "$BUNDLE" ] && return 0
  local url ver
  url=$(curl -sL -o /dev/null -w '%{url_effective}' https://github.com/actions/runner/releases/latest)
  ver=${url##*v}
  curl -sL -o "$BUNDLE" "https://github.com/actions/runner/releases/download/v${ver}/actions-runner-linux-x64-${ver}.tar.gz"
  [ -s "$BUNDLE" ]
}

spawn_slot() { # $1 = slot — bloque jusqu'a la fin du job (ephemere = 1 job)
  local slot="$1"
  local dir="$BASE/slot-$slot"
  local tok
  tok="$(mint_token)"
  if [ ${#tok} -lt 20 ]; then echo "$(date -Is) slot$slot: mint token echoue"; return 1; fi
  rm -rf "$dir"; mkdir -p "$dir"
  tar -xzf "$BUNDLE" -C "$dir" || { echo "$(date -Is) slot$slot: extraction echouee"; return 1; }
  # Isolation par slot (cf. TOOLCACHE_BASE) : heritee par run.sh -> Runner.Worker ->
  # setup-python, meme canal que PIP_BREAK_SYSTEM_PACKAGES (mesure /proc/<pid>/environ).
  RUNNER_TOOL_CACHE="$TOOLCACHE_BASE/slot-$slot"; export RUNNER_TOOL_CACHE
  mkdir -p "$RUNNER_TOOL_CACHE"
  ( cd "$dir" && \
    ./config.sh --url "https://github.com/$REPO" --token "$tok" \
      --labels "coursia-ephemeral,coursia-linux" --ephemeral \
      --name "myia-po-2026-wsl-$slot" --unattended --replace \
      && ./run.sh --once ) || echo "$(date -Is) slot$slot: runner termine (rc=$?)"
  rm -rf "$dir"
}

ensure_bundle || { echo "$(date -Is) telechargement bundle echoue"; exit 1; }
# Verifie le contrat AVANT d'ouvrir des slots : un contrat incomplet se lit dans pool.log au demarrage,
# pas trois heures plus tard dans le rouge d'une PR d'une autre lane.
ensure_host_contract || echo "$(date -Is) contrat d'image INCOMPLET — les jobs servis par ce pool peuvent rendre des faux rouges ou des verts fabriques"

declare -A PIDS
echo "$(date -Is) pool demarre (POOL_SIZE=$POOL_SIZE)"
while :; do
  for i in $(seq 1 "$POOL_SIZE"); do
    if [ -z "${PIDS[$i]:-}" ] || ! kill -0 "${PIDS[$i]}" 2>/dev/null; then
      echo "$(date -Is) spawn slot$i"
      spawn_slot "$i" & PIDS[$i]=$!
    fi
  done
  sleep 30
done
