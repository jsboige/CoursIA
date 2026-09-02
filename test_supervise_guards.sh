#!/usr/bin/env bash
# Tests des gardes #14259 par observation directe du comportement.
# On execute le script supervise.sh avec des PATH detournes (docker, gh, ps
# sont des stubs) et on verifie les return codes + stderr.

set -o pipefail

TEST_DIR="/tmp/supervise-test-$$"
mkdir -p "$TEST_DIR/bin" "$TEST_DIR/state-A" "$TEST_DIR/state-B" "$TEST_DIR/state-C"
LOG="$TEST_DIR/test.log"
: > "$LOG"

ok() { echo "  PASS: $1"; }
ko() { echo "  FAIL: $1"; }

# Stubs docker + gh + ps.
cat > "$TEST_DIR/bin/docker" <<'STUB'
#!/usr/bin/env bash
exit 0
STUB
chmod +x "$TEST_DIR/bin/docker"

cat > "$TEST_DIR/bin/gh" <<'STUB'
#!/usr/bin/env bash
if echo "$@" | grep -q 'registration-token'; then echo "FAKE_TOKEN"; exit 0; fi
if echo "$@" | grep -q 'actions/runners'; then echo '{"runners":[]}'; exit 0; fi
exit 0
STUB
chmod +x "$TEST_DIR/bin/gh"

cat > "$TEST_DIR/bin/ps" <<'STUB'
#!/usr/bin/env bash
if [ -n "$PS_OUTPUT" ]; then
  printf '%s\n' "$PS_OUTPUT"
fi
exit 0
STUB
chmod +x "$TEST_DIR/bin/ps"

# Helper : executer supervise.sh avec env detourne. Timeout strict pour
# eviter le hang de wait() -- cmd_start lance wait() qui attend les
# slot_loop infinis.
run_supervise() {
  local args="$1"
  local prefix="$2"
  local state="$3"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="$prefix"
  export COURSIA_RUNNER_STATE_DIR="$state"
  timeout --kill-after=1 1 bash "scripts/ci/docker/linux-runner/supervise.sh" $args >/dev/null 2>"$TEST_DIR/last.err"
  echo "rc=$?"
  cat "$TEST_DIR/last.err"
}

# --- Test 1 : start quand un superviseur est deja actif refuse -----
echo "Test 1 : start quand un superviseur est deja actif (Defaut 1)"
(
  cd /c/dev/CoursIA-c182-14259
  export PS_OUTPUT="jsboige  12345    1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  rc="$(run_supervise 'start 1' 'test-prefix-A' "$TEST_DIR/state-A" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "deja actif"; then
    ok "start refuse, message nomme PID (rc=$rc)"
  else
    ko "start aurait du refuser, rc=$rc err=$err"
  fi
)
echo ""

# --- Test 2 : start apres stop sans --force refuse -----
echo "Test 2 : start apres stop refuse, sentinel preserve (Defaut 2 sans --force)"
(
  cd /c/dev/CoursIA-c182-14259
  unset PS_OUTPUT
  touch "$TEST_DIR/state-B/stop"
  rc="$(run_supervise 'start 1' 'test-prefix-B' "$TEST_DIR/state-B" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "sentinel STOP_FILE present"; then
    ok "start apres stop refuse (rc=$rc)"
  else
    ko "start aurait du refuser sur sentinel, rc=$rc err=$err"
  fi
  if [ -f "$TEST_DIR/state-B/stop" ]; then
    ok "sentinel preserve apres start refuse"
  else
    ko "sentinel aurait du etre preserve"
  fi
)
echo ""

# --- Test 3 : start --force leve le sentinel et demarre -----
echo "Test 3 : start --force leve sentinel (Defaut 2 avec --force)"
(
  cd /c/dev/CoursIA-c182-14259
  unset PS_OUTPUT
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-C"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-C"
  touch "$TEST_DIR/state-C/stop"
  timeout --kill-after=1 2 bash "scripts/ci/docker/linux-runner/supervise.sh" start 1 --force >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  sleep 0.5
  if [ ! -f "$TEST_DIR/state-C/stop" ]; then
    ok "sentinel leve par start --force"
  else
    ko "sentinel aurait du etre leve par start --force (encore present)"
  fi
  pkill -P $TPID 2>/dev/null
  pkill -f 'supervise.sh start' 2>/dev/null
  wait 2>/dev/null
)
echo ""

# --- Test 4 : status compte les superviseurs par PPID==1 -----
echo "Test 4 : status affiche le compte par PPID==1"
(
  cd /c/dev/CoursIA-c182-14259
  export PS_OUTPUT="jsboige  100    1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-status-1"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-status"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  out="$(bash "scripts/ci/docker/linux-runner/supervise.sh" status 2>&1)"
  if echo "$out" | grep -q "superviseurs actifs : 1 (PID 100)"; then
    ok "status compte 1 superviseur (PPID==1)"
  else
    ko "status aurait du compter 1 (PID 100), output: $out"
  fi
  unset PS_OUTPUT
)
echo ""

# --- Test 5 : status ANOMALIE si >1 superviseurs -----
echo "Test 5 : status detecte >1 superviseur (ANOMALIE)"
(
  cd /c/dev/CoursIA-c182-14259
  export PS_OUTPUT="jsboige  100    1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  101    1   10:28:12  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-status-2"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-status-2"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  out="$(bash "scripts/ci/docker/linux-runner/supervise.sh" status 2>&1)"
  if echo "$out" | grep -q "superviseurs actifs : 2" && echo "$out" | grep -q "ANOMALIE"; then
    ok "status detecte anomalie >1 superviseur"
  else
    ko "status aurait du signaler anomalie, output: $out"
  fi
  unset PS_OUTPUT
)
echo ""

# --- Test 6 : status ignore les forks (PPID != 1) -----
echo "Test 6 : status ignore les slot_loop forks (PPID != 1)"
(
  cd /c/dev/CoursIA-c182-14259
  export PS_OUTPUT="jsboige  100    1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  101  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  102  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  103  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  104  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-status-3"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-status-3"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  out="$(bash "scripts/ci/docker/linux-runner/supervise.sh" status 2>&1)"
  if echo "$out" | grep -q "superviseurs actifs : 1 (PID 100)" && ! echo "$out" | grep -q "ANOMALIE"; then
    ok "status compte 1 superviseur + ignore les forks PPID!=1"
  else
    ko "status aurait du compter 1 et ignorer forks, output: $out"
  fi
  unset PS_OUTPUT
)
echo ""
