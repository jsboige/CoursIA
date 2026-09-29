#!/usr/bin/env bash
# Tests du mode persistent de entrypoint.sh (#14329) : enregistrement unique,
# restart sans token, restauration des binaires depuis runner-dist.
#
# Methode (famille test_entrypoint_disarm.sh) : on extrait le bloc REEL du
# script sous test (marqueurs de section) et on l'execute contre des fixtures
# de repertoire -- pas de stub de runner, la decision se teste sur l'etat du
# filesystem. RUNNER_HOME/RUNNER_DIST sont parametrables par env justement
# pour ce test.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/entrypoint-persistent-test-$$"
mkdir -p "$TEST_DIR"
LOG="$TEST_DIR/test.log"
: > "$LOG"

RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# Extraction du bloc reel : du marqueur START au marqueur END.
if ! sed -n '/# TEST-ENTRYPOINT-PERSISTENT-START/,/# TEST-ENTRYPOINT-PERSISTENT-END/p' \
     "$SCRIPT_DIR/entrypoint.sh" > "$TEST_DIR/block.sh" || \
   ! grep -q "runner_is_registered" "$TEST_DIR/block.sh"; then
  echo "FAIL extraction du bloc persistent de entrypoint.sh" >&2
  exit 1
fi

# Fixture : un runner-dist "image" avec run.sh executable, un runner-home vide
# (volume frais) ou enregistre (.runner present).
make_dist() {  # $1 = chemin dist
  mkdir -p "$1"
  printf '#!/bin/sh\nexit 0\n' > "$1/run.sh"
  chmod +x "$1/run.sh"
  printf '#!/bin/sh\nexit 0\n' > "$1/config.sh"
  chmod +x "$1/config.sh"
}

HOME_DIR="$TEST_DIR/runner-home"
DIST_DIR="$TEST_DIR/runner-dist"
make_dist "$DIST_DIR"

# --- Test 1 : volume vide -> restauration des binaires depuis dist ----------
(
  rm -rf "$HOME_DIR"; mkdir -p "$HOME_DIR"
  out="$(RUNNER_HOME="$HOME_DIR" RUNNER_DIST="$DIST_DIR" bash -c '
    set -euo pipefail
    . "'"$TEST_DIR"'/block.sh"
    runner_restore_dist
  ' 2>&1)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -ne 0 ]; then ko "T1 restore exit 0 (rc=$rc)"; else ok "T1 restore exit 0"; fi
  if [ -x "$HOME_DIR/run.sh" ]; then ok "T1 binaires restaures"; else ko "T1 run.sh absent apres restore"; fi
  if echo "$out" | grep -q "restauration"; then ok "T1 restauration journalisee"; else ko "T1 aucune trace de restauration"; fi
)

# --- Test 2 : binaires presents -> restore silencieux (idempotent) -----------
(
  out="$(RUNNER_HOME="$HOME_DIR" RUNNER_DIST="$DIST_DIR" bash -c '
    set -euo pipefail
    . "'"$TEST_DIR"'/block.sh"
    runner_restore_dist
  ' 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ]; then ko "T2 second restore exit 0 (rc=$rc)"; else ok "T2 second restore exit 0"; fi
  if [ -n "$out" ]; then ko "T2 doit etre silencieux si run.sh present (sort: $out)"; else ok "T2 silencieux quand binaires presents"; fi
)

# --- Test 3 : .runner present -> enregistre, token non requis ---------------
(
  touch "$HOME_DIR/.runner"
  out="$(RUNNER_HOME="$HOME_DIR" bash -c '
    set -euo pipefail
    . "'"$TEST_DIR"'/block.sh"
    if runner_is_registered; then echo REGISTERED; else echo NOT-REGISTERED; fi
  ' 2>&1)"; rc=$?
  # Aucune variable ACTIONS_RUNNER_INPUT_* definie : ne doit pas echouer.
  if [ "$rc" -ne 0 ]; then ko "T3 detection .runner sans env (rc=$rc)"; else ok "T3 detection exit 0 sans token"; fi
  if [ "$out" = "REGISTERED" ]; then ok "T3 .runner detecte"; else ko "T3 .runner non detecte (sort: $out)"; fi
)

# --- Test 4 : .runner absent -> NON enregistre (premier boot) ----------------
(
  rm -f "$HOME_DIR/.runner"
  out="$(RUNNER_HOME="$HOME_DIR" bash -c '
    set -euo pipefail
    . "'"$TEST_DIR"'/block.sh"
    if runner_is_registered; then echo REGISTERED; else echo NOT-REGISTERED; fi
  ' 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ]; then ko "T4 detection exit 0 (rc=$rc)"; else ok "T4 detection exit 0"; fi
  if [ "$out" = "NOT-REGISTERED" ]; then ok "T4 absence .runner detectee"; else ko "T4 devrait lire NOT-REGISTERED (sort: $out)"; fi
)

# --- Test 5 : require_registration_env exige le token (premier boot) ---------
(
  out="$(bash -c '
    set -euo pipefail
    . "'"$TEST_DIR"'/block.sh"
    require_registration_env
  ' 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ] && echo "$out" | grep -q "token manquant"; then
    ok "T5 token exigee au premier enregistrement"
  else ko "T5 require_registration_env devait echouer sur token manquant (rc=$rc, sort: $out)"; fi
)

# --- Test 6 : mode par defaut = ephemeral (retro-compatible) -----------------
(
  out="$(bash -c '
    . "'"$TEST_DIR"'/block.sh"
    runner_mode
  ' 2>&1)"
  if [ "$out" = "ephemeral" ]; then ok "T6 defaut ephemeral"; else ko "T6 defaut doit etre ephemeral (sort: $out)"; fi
  out2="$(RUNNER_MODE=persistent bash -c '
    . "'"$TEST_DIR"'/block.sh"
    runner_mode
  ' 2>&1)"
  if [ "$out2" = "persistent" ]; then ok "T6 RUNNER_MODE=persistent lu"; else ko "T6 RUNNER_MODE=persistent non respecte (sort: $out2)"; fi
)

# --- Test 7 : le bloc persistant ne modifie pas un home enregistre ----------
(
  touch "$HOME_DIR/.runner"
  RUNNER_HOME="$HOME_DIR" RUNNER_DIST="$DIST_DIR" bash -c '
    set -euo pipefail
    . "'"$TEST_DIR"'/block.sh"
    runner_restore_dist
  ' >/dev/null 2>&1
  if [ -f "$HOME_DIR/.runner" ] && [ -x "$HOME_DIR/run.sh" ]; then
    ok "T7 .runner et binaires conserves"
  else ko "T7 l'etat du home a ete altere"; fi
)

# --- Verdict agrege -----------------------------------------------------------
n_pass="$(grep -c '^PASS' "$RESULTS" || true)"
n_fail="$(grep -c '^FAIL' "$RESULTS" || true)"
echo "============================================================"
echo "entrypoint persistent mode : $n_pass PASS, $n_fail FAIL"
echo "============================================================"
if [ "$n_fail" -gt 0 ]; then
  echo "(logs: $LOG)"
  exit 1
fi
rm -rf "$TEST_DIR"
exit 0
