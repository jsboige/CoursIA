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
mkdir -p "$BASE"
exec >>"$BASE/pool.log" 2>&1

# Singleton: la tâche planifiee a RestartCount=3 — jamais deux superviseurs
exec 9>"$LOCK" || exit 1
flock -n 9 || { echo "$(date -Is) pool deja actif ($LOCK)"; exit 0; }

mint_token() { gh.exe api -X POST "repos/$REPO/actions/runners/registration-token" --jq .token; }

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
  ( cd "$dir" && \
    ./config.sh --url "https://github.com/$REPO" --token "$tok" \
      --labels "coursia-ephemeral,coursia-linux" --ephemeral \
      --name "myia-po-2026-wsl-$slot" --unattended --replace \
      && ./run.sh --once ) || echo "$(date -Is) slot$slot: runner termine (rc=$?)"
  rm -rf "$dir"
}

ensure_bundle || { echo "$(date -Is) telechargement bundle echoue"; exit 1; }

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
