#!/usr/bin/env bash
# Tests des gardes #14259 par observation directe du comportement.
# On execute le script supervise.sh avec des PATH detournes (docker, gh, ps
# sont des stubs) et on verifie les return codes + stderr.

set -o pipefail

# Portabilite (#14259) : le test vit a cote du script sous test -- plus de
# chemin de worktree hardcode (l original cassait hors de sa session d origine).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

TEST_DIR="/tmp/supervise-test-$$"
mkdir -p "$TEST_DIR/bin" "$TEST_DIR/state-A" "$TEST_DIR/state-B" "$TEST_DIR/state-C"
LOG="$TEST_DIR/test.log"
: > "$LOG"

ok() { echo "  PASS: $1"; }
ko() { echo "  FAIL: $1"; }

# Stubs docker + gh + ps. Le stub docker simule une image A JOUR pour le
# garde de fraicheur #14801 : au probe `run --entrypoint sha256sum`, il rend
# le sha256 du VRAI entrypoint.sh sibling (bake a la generation du stub).
# STUB_IMG_ENTRYPOINT_SHA force un ecart pour tester le refus (test 9).
REPO_ENTRYPOINT_SHA="$(sha256sum "$SCRIPT_DIR/entrypoint.sh" 2>/dev/null | awk '{print $1}')"
cat > "$TEST_DIR/bin/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "run" ]; then
  echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
  exit 0
fi
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
  timeout --kill-after=1 1 bash "$SCRIPT_DIR/supervise.sh" $args >/dev/null 2>"$TEST_DIR/last.err"
  echo "rc=$?"
  cat "$TEST_DIR/last.err"
}

# --- Test 1 : start quand un superviseur est deja actif refuse -----
echo "Test 1 : start quand un superviseur est deja actif (Defaut 1)"
(
  cd "$SCRIPT_DIR"
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
  cd "$SCRIPT_DIR"
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
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-C"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-C"
  touch "$TEST_DIR/state-C/stop"
  timeout --kill-after=1 2 bash "$SCRIPT_DIR/supervise.sh" start 1 --force >/dev/null 2>"$TEST_DIR/last.err" &
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
  cd "$SCRIPT_DIR"
  export PS_OUTPUT="jsboige  100    1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-status-1"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-status"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  out="$(bash "$SCRIPT_DIR/supervise.sh" status 2>&1)"
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
  cd "$SCRIPT_DIR"
  export PS_OUTPUT="jsboige  100    1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  101    1   10:28:12  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-status-2"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-status-2"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  out="$(bash "$SCRIPT_DIR/supervise.sh" status 2>&1)"
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
  cd "$SCRIPT_DIR"
  export PS_OUTPUT="jsboige  100    1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  101  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  102  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  103  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4
jsboige  104  100   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-status-3"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-status-3"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  out="$(bash "$SCRIPT_DIR/supervise.sh" status 2>&1)"
  if echo "$out" | grep -q "superviseurs actifs : 1 (PID 100)" && ! echo "$out" | grep -q "ANOMALIE"; then
    ok "status compte 1 superviseur + ignore les forks PPID!=1"
  else
    ko "status aurait du compter 1 et ignorer forks, output: $out"
  fi
  unset PS_OUTPUT
)
echo ""

# --- Test 7 : COURSIA_RUNNER_GH_ACCOUNT epingle le compte du fetch -----
echo "Test 7 : COURSIA_RUNNER_GH_ACCOUNT epingle le compte (epinglage #14259)"
(
  cd "$SCRIPT_DIR"
  mkdir -p "$TEST_DIR/bin7" "$TEST_DIR/state-7"
  cat > "$TEST_DIR/bin7/gh" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$GH_CALLS_LOG"
if echo "$@" | grep -q 'auth token'; then echo "FAKE_ACCOUNT_TOKEN"; exit 0; fi
if echo "$@" | grep -q 'registration-token'; then echo "FAKE_TOKEN"; exit 0; fi
if echo "$@" | grep -q 'actions/runners'; then echo '{"runners":[]}'; exit 0; fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin7/gh"
  cp "$TEST_DIR/bin/docker" "$TEST_DIR/bin7/docker"
  chmod +x "$TEST_DIR/bin7/docker"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin7/ps"
  export PATH="$TEST_DIR/bin7:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-7"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-7"
  export COURSIA_RUNNER_GH_ACCOUNT="fake-account"
  export GH_CALLS_LOG="$TEST_DIR/gh7.calls"
  : > "$GH_CALLS_LOG"
  timeout --kill-after=1 2 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  sleep 1
  pkill -P $TPID 2>/dev/null
  pkill -f 'supervise.sh start' 2>/dev/null
  wait 2>/dev/null
  if grep -q 'auth token --user fake-account' "$GH_CALLS_LOG"; then
    ok "fetch_token resout le token via gh auth token --user fake-account"
  else
    ko "gh auth token --user attendu, appels: $(cat "$GH_CALLS_LOG")"
  fi
  if grep -q 'registration-token' "$GH_CALLS_LOG"; then
    ok "le registration fetch a bien eu lieu apres epinglage"
  else
    ko "registration-token absent des appels gh"
  fi
)
echo ""

# --- Test 8 : status nomme la contradiction conteneurs/runners -----
echo "Test 8 : status nomme la contradiction conteneurs vs inventaire (Defaut #14259 residuel)"
(
  cd "$SCRIPT_DIR"
  mkdir -p "$TEST_DIR/bin8" "$TEST_DIR/state-8"
  cat > "$TEST_DIR/bin8/gh" <<'STUB'
#!/usr/bin/env bash
if echo "$@" | grep -q 'registration-token'; then echo "FAKE_TOKEN"; exit 0; fi
if echo "$@" | grep -q 'actions/runners'; then echo '{"runners":[]}'; exit 0; fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin8/gh"
  cat > "$TEST_DIR/bin8/docker" <<'STUB'
#!/usr/bin/env bash
if [ "${1:-}" = "ps" ]; then printf 'fakeid1\nfakeid2\n'; exit 0; fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin8/docker"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin8/ps"
  export PATH="$TEST_DIR/bin8:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-8"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-8"
  unset PS_OUTPUT || true
  out="$(bash "$SCRIPT_DIR/supervise.sh" status 2>&1)"
  if echo "$out" | grep -q "CONTRADICTION : 2 conteneur(s)"; then
    ok "status nomme la contradiction 2 conteneurs / 0 runner"
  else
    ko "ligne CONTRADICTION attendue, output: $out"
  fi
  if echo "$out" | grep -q "COURSIA_RUNNER_GH_ACCOUNT"; then
    ok "le message pointe vers l'epinglage"
  else
    ko "renvoi vers epinglage attendu"
  fi
)
echo ""

# --- Test 9 : garde de fraicheur -- image perimee refuse (#14801) -----
echo "Test 9 : start refuse si entrypoint de l'image != checkout (#14801)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-9"
  STUB_IMG_ENTRYPOINT_SHA=f0000000000000000000000000000000000000000000000000000000000000f00
  export STUB_IMG_ENTRYPOINT_SHA
  rc="$(run_supervise 'start 1' 'test-prefix-9' "$TEST_DIR/state-9" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "PERIMEE" && echo "$err" | grep -q "docker build -t"; then
    ok "image perimee refusee avec la commande de rebuild (rc=$rc)"
  else
    ko "refus attendu sur image perimee, rc=$rc err=$err"
  fi
  unset STUB_IMG_ENTRYPOINT_SHA
)
echo ""

# --- Test 10 : garde de fraicheur -- image a jour ne bloque pas -----
echo "Test 10 : start passe le garde quand l'image est a jour (#14801)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-10"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-10"
  mkdir -p "$TEST_DIR/state-10"
  timeout --kill-after=1 2 bash "$SCRIPT_DIR/supervise.sh" start 1 >"$TEST_DIR/out-10.log" 2>"$TEST_DIR/last.err" &
  TPID=$!
  sleep 0.7
  if grep -q "slots lances" "$TEST_DIR/out-10.log" && ! grep -q "PERIMEE" "$TEST_DIR/last.err"; then
    ok "image a jour : garde passe, slots lances"
  else
    ko "le garde a tort ou le start a echoue, out=$(cat "$TEST_DIR/out-10.log") err=$(cat "$TEST_DIR/last.err")"
  fi
  pkill -P $TPID 2>/dev/null
  pkill -f 'supervise.sh start' 2>/dev/null
  wait 2>/dev/null
)
echo ""
