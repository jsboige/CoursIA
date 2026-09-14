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

# Le verdict est TENU DANS UN FICHIER, pas dans une variable (#15091). Chaque
# test tourne dans un sous-shell `( ... )` : un compteur shell y serait
# incremente dans une copie et le parent lirait toujours zero. Le meme piege a
# fait passer le test 15 a cote de son objet -- une fonction appelee dans
# $( ) reinitialise un tableau que le parent ne voit jamais.
#
# Sans cet agregat, ce harnais SORTAIT 0 quoi qu'il arrive : un `ko` s'affiche,
# et le code de retour reste celui du dernier echo. Un cablage CI l'aurait vu
# vert en permanence -- exactement la classe de defaut que les gardes testes
# ici existent pour empecher, reproduite dans l'outil qui les mesure.
RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# Stubs docker + gh + ps + hostname. Le stub docker simule une image A JOUR
# pour le garde de fraicheur #14801/#15105 : au probe `run --entrypoint
# sha256sum`, il rend le sha256 du VRAI sibling du checkout (bake a la
# generation du stub). La fonction assert_image_fresh lit DEUX fichiers
# depuis #15105 (work_cache_health.sh est source par l'entrypoint) : le stub
# repond aux deux probes. STUB_IMG_ENTRYPOINT_SHA / STUB_IMG_HEALTH_SHA
# forcent un ecart pour tester le refus (tests 9 et 29).
# Le stub hostname rend le defaut de supervise.sh (#15152) deterministe :
# le prefixe derive de la machine, il ne doit jamais dependre de l'hote qui
# execute la suite.
REPO_ENTRYPOINT_SHA="$(sha256sum "$SCRIPT_DIR/entrypoint.sh" 2>/dev/null | awk '{print $1}')"
REPO_HEALTH_SHA="$(sha256sum "$SCRIPT_DIR/work_cache_health.sh" 2>/dev/null | awk '{print $1}')"
cat > "$TEST_DIR/bin/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "run" ]; then
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
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

# REAL_SLEEP : chemin absolu du sleep systeme, capture AVANT la creation du
# stub global (le resolveur `command -v` toucherait sinon le stub). Les polls
# du HARNAIS (tests 3 et 10) doivent attendre pour de vrai ; le stub ne sert
# qu'aux backoffs du programme teste.
REAL_SLEEP="$(command -v sleep)"

# Stub sleep GLOBAL : depuis que les boucles VIVENT (la fusion a corrige t0),
# un cycle court attendait un backoff reel de 15 s ; les tests 1-3/7/10/22
# (timeouts 1-3 s) timeout-rent au lieu de mesurer. Ce stub rend toutes les
# attentes de supervise.sh instantanees ; les tests 12-28 posent LEURS stubs
# sleep logues pour compter les backoffs (non affectes : leurs bins passent
# d'abord dans le PATH).
cat > "$TEST_DIR/bin/sleep" <<'STUB'
#!/usr/bin/env bash
echo "sleep $*" >> "${SLEEP_LOG:-/dev/null}"
exit 0
STUB
chmod +x "$TEST_DIR/bin/sleep"

# Stub hostname (#15152) : le prefixe des runners derive du hostname, le
# rendre deterministe -- la suite ne doit jamais dependre de l'hote qui
# l'execute.
cat > "$TEST_DIR/bin/hostname" <<'STUB'
#!/usr/bin/env bash
printf '%s\n' "${HOSTNAME_STUB:-myia-default-host}"
STUB
chmod +x "$TEST_DIR/bin/hostname"

# Helper : executer supervise.sh avec env detourne. Timeout pour eviter le
# hang de wait() -- cmd_start lance wait() qui attend les slot_loop infinis.
# La fenetre (8 s) est large : elle borne execute() sans dependre d'une
# machine rapide -- les refus testes arrivent en tete de cmd_start, la
# charge machine ne doit pas les transformer en timeout.
run_supervise() {
  local args="$1"
  local prefix="$2"
  local state="$3"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="$prefix"
  export COURSIA_RUNNER_STATE_DIR="$state"
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" $args >/dev/null 2>"$TEST_DIR/last.err"
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
  timeout --kill-after=1 15 bash "$SCRIPT_DIR/supervise.sh" start 1 --force >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  # Poll (pas de fenetre fixe) : la chaine de gardes pre-rebase fait vivre
  # N processus stub ; sa duree depend de la charge machine.
  leve=0
  for _ in $(seq 1 24); do
    [ ! -f "$TEST_DIR/state-C/stop" ] && { leve=1; break; }
    "$REAL_SLEEP" 0.5
  done
  if [ "$leve" = "1" ]; then
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
  timeout --kill-after=1 15 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  sleep 5
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
  timeout --kill-after=1 15 bash "$SCRIPT_DIR/supervise.sh" start 1 >"$TEST_DIR/out-10.log" 2>"$TEST_DIR/last.err" &
  TPID=$!
  # Signal fiable de "slots lances" : $STATE_DIR/pids est ecrit par
  # redirection directe (immediate), alors que les echoes stdout du
  # supervise sont bufferises (visibles seulement a la sortie du process).
  # Poll : la chaine de gardes depend de la charge machine.
  slots=0
  for _ in $(seq 1 24); do
    [ -s "$TEST_DIR/state-10/pids" ] && { slots=1; break; }
    "$REAL_SLEEP" 0.5
  done
  if [ "$slots" = "1" ] && ! grep -q "PERIMEE" "$TEST_DIR/last.err"; then
    ok "image a jour : garde passe, slots lances ($(tr '\n' ' ' < "$TEST_DIR/state-10/pids"))"
  else
    ko "le garde a tort ou le start a echoue, out=$(cat "$TEST_DIR/out-10.log") err=$(cat "$TEST_DIR/last.err")"
  fi
  pkill -P $TPID 2>/dev/null
  pkill -f 'supervise.sh start' 2>/dev/null
  wait 2>/dev/null
)
echo ""

# ===========================================================================
# Gardes #15091 -- bornes d'I/O, budget inter-familles, backoff, rotation.
#
# Ces tests appellent les fonctions DIRECTEMENT, en sourcant supervise.sh avec
# l'argument `status` : le `case` final choisit alors la branche la moins
# couteuse et rend la main sans `exit`, laissant les fonctions definies dans le
# shell du test. Sourcer sans argument tomberait sur `*) ... exit 2`.
#
# Le sourcage se fait TOUJOURS avec un environnement de bornes VIERGE, et les
# variables sont posees APRES : `cmd_status` appelle lui-meme assert_cgroup_budget,
# qui appelle die() -- donc exit -- quand la slice manque sous exigence. Armer
# les bornes avant de sourcer tuerait le sous-shell du test avant son premier
# assert.
# ===========================================================================

mkdir -p "$TEST_DIR/state-G"
source_supervise() {
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-G"
  unset COURSIA_RUNNER_CGROUP_PARENT COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET
  unset COURSIA_RUNNER_DEVICE_WRITE_BPS COURSIA_RUNNER_DEVICE_READ_BPS
  unset COURSIA_RUNNER_BLKIO_DEVICE COURSIA_RUNNER_CPU_BUDGET
  # shellcheck disable=SC1090
  . "$SCRIPT_DIR/supervise.sh" status >/dev/null 2>&1
}

# --- Test 11 : daemon Docker indisponible -> start refuse AVANT tout (#15095)
echo "Test 11 : start refuse si docker info echoue, avant gh et avant docker run"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin11" "$TEST_DIR/state-11"
  cat > "$TEST_DIR/bin11/docker" <<'STUB'
#!/usr/bin/env bash
echo "$1" >> "$DOCKER_CALLS_LOG"
if [ "$1" = "info" ]; then exit 1; fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin11/docker"
  cat > "$TEST_DIR/bin11/gh" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$GH_CALLS_LOG"
if echo "$@" | grep -q 'registration-token'; then echo "FAKE_TOKEN"; exit 0; fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin11/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin11/ps"
  export PATH="$TEST_DIR/bin11:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-11"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-11"
  export DOCKER_CALLS_LOG="$TEST_DIR/docker11.calls"
  export GH_CALLS_LOG="$TEST_DIR/gh11.calls"
  : > "$DOCKER_CALLS_LOG"
  : > "$GH_CALLS_LOG"
  out="$(bash "$SCRIPT_DIR/supervise.sh" start 1 2>"$TEST_DIR/err11.log")"
  rc=$?
  if [ "$rc" != "0" ] && grep -q "demon Docker indisponible" "$TEST_DIR/err11.log"; then
    ok "start refuse (rc=$rc), message nomme le daemon absent"
  else
    ko "refus attendu, rc=$rc err=$(cat "$TEST_DIR/err11.log")"
  fi
  if [ "$(cat "$DOCKER_CALLS_LOG")" = "info" ]; then
    ok "docker n'a ete appele QUE pour le probe info (pas de run/inspect)"
  else
    ko "appels docker inattendus : $(cat "$DOCKER_CALLS_LOG")"
  fi
  if [ ! -s "$GH_CALLS_LOG" ]; then
    ok "aucun appel gh -- le registration token n'est jamais solicite"
  else
    ko "gh appele malgre daemon absent : $(cat "$GH_CALLS_LOG")"
  fi
)
echo ""

# --- Test 12 : cycles courts -> backoff exponentiel plafonne, rc-agnostique
echo "Test 12 : backoff exponentiel 3,6,12,24... plafonne 24, identique rc=0 et rc!=0"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin12" "$TEST_DIR/state-12"
  cat > "$TEST_DIR/bin12/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  # assert_image_fresh sonde DEUX fichiers (#15105) : repondre au bon sha
  # selon la probe, sinon l'image est jugee PERIMEE et toute la boucle meurt.
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  if [ "\$RUNS" -ge "\${STUB_STOP_AFTER:-8}" ]; then touch "\$STUB_STOP_FILE"; fi
  exit "\${STUB_DOCKER_RC:-0}"
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin12/docker"
  cat > "$TEST_DIR/bin12/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin12/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin12/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin12/ps"
  run_case() {
    local rc="$1"
    rm -f "$TEST_DIR/state-12/stop" "$TEST_DIR/state-12/pids" "$TEST_DIR/run12.count"
    : > "$TEST_DIR/sleep12.log"
    (
      export PATH="$TEST_DIR/bin12:$PATH"
      export COURSIA_RUNNER_NAME_PREFIX="test-prefix-12"
      export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-12"
      export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
      export COURSIA_RUNNER_BACKOFF_BASE=3
      export COURSIA_RUNNER_BACKOFF_CAP=24
      export STUB_STOP_FILE="$TEST_DIR/state-12/stop"
      export STUB_RUN_COUNT="$TEST_DIR/run12.count"
      export SLEEP_LOG="$TEST_DIR/sleep12.log"
      export STUB_DOCKER_RC="$rc"
      timeout --kill-after=2 20 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err12.log"
    )
    paste -sd, "$TEST_DIR/sleep12.log"
  }
  seq0="$(run_case 0)"
  seq1="$(run_case 1)"
  if [ "$seq0" = "3,6,12,24,24,24,24,24" ]; then
    ok "rc=0 : 3,6,12 puis plafond 24 jusqu'a la 8e -- plus de rafale 4-8/min"
  else
    ko "rc=0 : attendu 3,6,12,24,24,24,24,24, obtenu [$seq0] err=$(head -3 "$TEST_DIR/err12.log")"
  fi
  if [ "$seq0" = "$seq1" ]; then
    ok "rc=1 : sequence identique -- la duree de vie pilote, pas le rc"
  else
    ko "divergence rc : [$seq1] vs [$seq0]"
  fi
  if grep -q "cycle court" "$TEST_DIR/err12.log"; then
    ok "le journal nomme les cycles courts (backoff observable)"
  else
    ko "ligne 'cycle court' absente de stderr"
  fi
)
echo ""

# --- Test 13 : plafond BACKOFF_CAP effectif (queue du test 12) -------------
echo "Test 13 : le plafond CAP borne la file (entries 4+ toutes = CAP)"
(
  # Derive direct du test 12 : avec BASE=3/CAP=24, les cycles 4 a 8 valent
  # tous 24 -- 5 valeurs consecutives egales au cap prouvent le clamp sans
  # avoir besoin d'attendre 15*2^N secondes avec les vrais defauts.
  if [ "$(tail -5 "$TEST_DIR/sleep12.log" | sort -u)" = "24" ]; then
    ok "5 respirations consecutives au plafond 24 -- clamp effectif"
  else
    ko "queue incoherente : $(tail -5 "$TEST_DIR/sleep12.log" | tr '\n' ' ')"
  fi
)
echo ""

# --- Test 14 : un cycle sain remet le compteur de backoff a zero -----------
echo "Test 14 : cycle ayant vecu >= HEALTHY_CYCLE_SECS -> reset + sleep 2"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin14" "$TEST_DIR/state-14"
  cat > "$TEST_DIR/bin14/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  # assert_image_fresh sonde DEUX fichiers (#15105) : repondre au bon sha
  # selon la probe, sinon l'image est jugee PERIMEE et toute la boucle meurt.
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  if [ "\$RUNS" -ge "\${STUB_STOP_AFTER:-6}" ]; then touch "\$STUB_STOP_FILE"; fi
  if [ "\$RUNS" = "\${STUB_BURN_AT:-3}" ]; then
    start=\$(date +%s)
    while [ \$(( \$(date +%s) - start )) -lt "\${STUB_BURN_SECS:-2}" ]; do :; done
  fi
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin14/docker"
  cat > "$TEST_DIR/bin14/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin14/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin14/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin14/ps"
  rm -f "$TEST_DIR/state-14/stop" "$TEST_DIR/state-14/pids" "$TEST_DIR/run14.count"
  : > "$TEST_DIR/sleep14.log"
  (
    export PATH="$TEST_DIR/bin14:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-14"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-14"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=2
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=999
    export STUB_STOP_FILE="$TEST_DIR/state-14/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run14.count"
    export SLEEP_LOG="$TEST_DIR/sleep14.log"
    export STUB_BURN_AT=3
    export STUB_BURN_SECS=3
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >"$TEST_DIR/out14.log" 2>"$TEST_DIR/err14.log"
  )
  seq="$(paste -sd, "$TEST_DIR/sleep14.log")"
  if [ "$seq" = "3,6,2,3,6,12" ]; then
    ok "reset prouve : 3,6 -> cycle sain (2) -> REPART a 3,6 (le 3e cycle de 2s a vecu >= HEALTHY=1)"
  else
    ko "attendu 3,6,2,3,6,12, obtenu [$seq]"
  fi
  if grep -q "conteneur termine sainement" "$TEST_DIR/out14.log"; then
    ok "le cycle long est journalise comme sain (pas comme echec)"
  else
    ko "ligne 'termine sainement' absente : $(head -3 "$TEST_DIR/out14.log")"
  fi
)
echo ""

# --- Test 15 : persist/ -- unit systemd fail-closed + garde wrapper ---------
echo "Test 15 : checks textuels persist/ (unit systemd + wrapper) et bash -n"
(
  cd "$SCRIPT_DIR"
  svc="$SCRIPT_DIR/persist/coursia-runner.service"
  wrap="$SCRIPT_DIR/persist/coursia-runner-start.sh"
  if grep -q '^Requires=docker.service' "$svc" && grep -q '^BindsTo=docker.service' "$svc" \
     && grep -q '^StartLimitIntervalSec=' "$svc" && grep -q '^StartLimitBurst=' "$svc" \
     && ! grep -q '^Wants=docker.service' "$svc"; then
    ok "unit : Requires+BindsTo+StartLimit presents, Wants retire (inversion #14347)"
  else
    ko "unit systemd non conforme a #15095"
  fi
  if grep -q 'docker info' "$wrap" && grep -q 'FATAL: demon Docker indisponible' "$wrap"; then
    ok "wrapper : garde docker info avec message FATAL avant l'exec du superviseur"
  else
    ko "garde docker info absente du wrapper"
  fi
  if bash -n "$SCRIPT_DIR/supervise.sh" && bash -n "$wrap"; then
    ok "bash -n : syntaxe OK sur supervise.sh et wrapper"
  else
    ko "erreur de syntaxe detectee par bash -n"
  fi
)
echo ""
# --- Test 16 : backoff exponentiel, plafonne, jitter borne -----------------
echo "Test 16 : backoff exponentiel plafonne et disperse (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  source_supervise
  BACKOFF_MIN_SEC=5; BACKOFF_MAX_SEC=300
  BACKOFF_JITTER_PCT=0   # jitter neutralise : on teste d'abord la loi
  d1="$(backoff_delay 1)"; d2="$(backoff_delay 2)"; d3="$(backoff_delay 3)"
  d9="$(backoff_delay 9)"; d20="$(backoff_delay 20)"
  if [ "$d1" = "5" ] && [ "$d2" = "10" ] && [ "$d3" = "20" ]; then
    ok "doublement a chaque echec consecutif : 5 10 20"
  else
    ko "loi de doublement attendue 5/10/20, obtenu $d1/$d2/$d3"
  fi
  if [ "$d9" = "300" ] && [ "$d20" = "300" ]; then
    ok "plafond respecte (300 s a 9 et a 20 echecs)"
  else
    ko "plafond 300 attendu, obtenu $d9 (9 echecs) et $d20 (20 echecs)"
  fi
  # Controle POSITIF du jitter : sans lui, N slots repartent dans la MEME
  # seconde -- le backoff deplace la rafale sans la disperser. On verifie donc
  # qu'il produit reellement plusieurs valeurs distinctes, ET qu'elles restent
  # dans la bande annoncee (+/- 25 % de 20 s -> [15, 25]).
  BACKOFF_JITTER_PCT=25
  distinct="$(for i in $(seq 1 40); do backoff_delay 3; done | sort -u | wc -l | tr -d ' ')"
  outside="$(for i in $(seq 1 40); do backoff_delay 3; done | awk '$1 < 15 || $1 > 25' | wc -l | tr -d ' ')"
  if [ "$distinct" -gt 1 ] && [ "$outside" = "0" ]; then
    ok "jitter actif : $distinct valeurs distinctes, toutes dans [15,25]"
  else
    ko "jitter attendu disperse et borne, distinct=$distinct hors-bande=$outside"
  fi
)
echo ""

# --- Test 17 : budget CPU inter-familles -- REFUS au depassement -----------
echo "Test 17 : budget CPU inter-familles refuse le depassement (#15091, trou #14337)"
(
  cd "$SCRIPT_DIR"
  # 12 waiters a 1 vCPU deja actifs ; on demande 2 slots lean a 6 vCPU.
  # 12 + 12 = 24 > 8 -> refus. C'est exactement la configuration que le cap
  # --cpus PAR CONTENEUR declare conforme et qui prend 24 coeurs.
  export PS_OUTPUT="jsboige  4242     1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh waiters 12"
  source_supervise
  CPU_BUDGET=8
  err="$( (assert_cpu_budget "lean" 2 6) 2>&1 )"; rc=$?
  if [ "$rc" != "0" ] && echo "$err" | grep -q "budget CPU inter-familles depasse"; then
    ok "depassement refuse (rc=$rc)"
  else
    ko "refus attendu, rc=$rc err=$err"
  fi
  if echo "$err" | grep -q "deja actif : waiters n=12 cpus=1" \
     && echo "$err" | grep -q "demande    : lean n=2 cpus=6"; then
    ok "le message NOMME les deux termes de la somme"
  else
    ko "detail par famille attendu dans le message, err=$err"
  fi
)
echo ""

# --- Test 18 : controle negatif -- le budget n'accuse pas a tort -----------
echo "Test 18 : budget CPU -- controle negatif (sous le plafond, puis non arme)"
(
  cd "$SCRIPT_DIR"
  export PS_OUTPUT="jsboige  4242     1   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh waiters 4"
  source_supervise
  CPU_BUDGET=8
  out="$( (assert_cpu_budget "start" 1 3) 2>&1 )"; rc=$?
  if [ "$rc" = "0" ] && echo "$out" | grep -q "7.00 / 8"; then
    ok "4x1 + 1x3 = 7 <= 8 : accepte, total affiche"
  else
    ko "acceptation attendue avec total 7.00, rc=$rc out=$out"
  fi
  # Non arme (0) : aucune machine ne se voit imposer un plafond non declare.
  CPU_BUDGET=0
  out="$( (assert_cpu_budget "lean" 8 6) 2>&1 )"; rc=$?
  if [ "$rc" = "0" ] && [ -z "$out" ]; then
    ok "budget non arme : inerte et muet, meme sur 48 vCPU demandes"
  else
    ko "inertie attendue quand CPU_BUDGET=0, rc=$rc out=$out"
  fi
)
echo ""

# --- Test 19 : borne agregee -- REFUS fail-closed quand elle manque --------
echo "Test 19 : slice absente -- refus fail-closed et commande de deploiement (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  source_supervise
  CGROUP_PARENT="coursia-absente-xyz.slice"
  REQUIRE_CGROUP_BUDGET=1
  err="$( (assert_cgroup_budget) 2>&1 )"; rc=$?
  if [ "$rc" != "0" ] && echo "$err" | grep -q "REFUS de demarrer"; then
    ok "slice introuvable : demarrage refuse (rc=$rc)"
  else
    ko "refus attendu, rc=$rc err=$err"
  fi
  if echo "$err" | grep -q "persist/coursia-ci.slice" \
     && echo "$err" | grep -q "systemctl daemon-reload"; then
    ok "le refus porte la commande de deploiement"
  else
    ko "commande de deploiement attendue dans le message, err=$err"
  fi
  # Meme situation SANS l'exigence : avertit, ne bloque pas. C'est le
  # comportement des machines qui n'ont pas deploye la slice (po-2024).
  REQUIRE_CGROUP_BUDGET=0
  err="$( (assert_cgroup_budget) 2>&1 )"; rc=$?
  if [ "$rc" = "0" ] && echo "$err" | grep -q "AVERTISSEMENT"; then
    ok "sans exigence : avertit et laisse passer (aucun defaut impose)"
  else
    ko "avertissement non bloquant attendu, rc=$rc err=$err"
  fi
)
echo ""

# --- Test 20 : plafond par conteneur -- drapeaux et aveu de non-application -
echo "Test 20 : --device-write-bps cable, et non-resolution AVOUEE (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  source_supervise
  DEVICE_WRITE_BPS=20971520; DEVICE_READ_BPS=41943040; BLKIO_DEVICE=/dev/fake0
  compute_blkio_args >/dev/null 2>&1
  joined="${BLKIO_ARGS[*]-}"
  if [ "$joined" = "--device-write-bps /dev/fake0:20971520 --device-read-bps /dev/fake0:41943040" ]; then
    ok "drapeaux construits exactement : $joined"
  else
    ko "drapeaux attendus write+read sur /dev/fake0, obtenu: $joined"
  fi
  # Controle negatif. Le point du test n'est pas que la liste soit vide --
  # c'est que le script le DISE. Un plafond demande et silencieusement non
  # applique laisse croire qu'on est borne.
  BLKIO_DEVICE=""
  # Appel DIRECT, pas $( ) : une substitution de commande execute la fonction
  # dans un sous-shell, ou son `BLKIO_ARGS=()` de tete ne reinitialise que la
  # copie du sous-shell -- le parent garderait les drapeaux du cas precedent et
  # le test lirait une valeur perimee. Le script, lui, l'appelle bien dans son
  # propre shell.
  compute_blkio_args 2> "$TEST_DIR/blkio.err" >/dev/null
  err="$(cat "$TEST_DIR/blkio.err")"
  if [ "${#BLKIO_ARGS[@]}" = "0" ] && echo "$err" | grep -q "AUCUN plafond ne sera applique"; then
    ok "device non resolvable : liste vide ET aveu explicite"
  else
    ko "aveu attendu quand le device n'est pas resolvable, err=$err args=${BLKIO_ARGS[*]-}"
  fi
)
echo ""

# --- Test 21 : rotation des journaux ---------------------------------------
echo "Test 21 : rotation du journal de slot au-dela du seuil (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  source_supervise
  LOG_MAX_BYTES=100
  f="$TEST_DIR/state-G/rot.log"
  head -c 40 /dev/zero | tr '\0' 'a' > "$f"
  rotate_log "$f"
  if [ "$(wc -c < "$f" | tr -d ' ')" = "40" ] && [ ! -f "$f.1" ]; then
    ok "sous le seuil : journal intact, aucune generation creee"
  else
    ko "aucune rotation attendue sous le seuil"
  fi
  head -c 250 /dev/zero | tr '\0' 'b' > "$f"
  rotate_log "$f"
  if [ "$(wc -c < "$f" | tr -d ' ')" = "0" ] && [ "$(wc -c < "$f.1" | tr -d ' ')" = "250" ]; then
    ok "au-dela du seuil : journal tronque, une generation conservee"
  else
    ko "rotation attendue : courant=$(wc -c < "$f") precedent=$(wc -c < "$f.1" 2>/dev/null)"
  fi
  # Inerte a seuil 0 -- personne ne perd ses journaux par un defaut non choisi.
  LOG_MAX_BYTES=0
  head -c 250 /dev/zero | tr '\0' 'c' > "$f"
  rotate_log "$f"
  if [ "$(wc -c < "$f" | tr -d ' ')" = "250" ]; then
    ok "seuil a 0 : rotation desactivee"
  else
    ko "inertie attendue a seuil 0"
  fi
)
echo ""

# --- Test 22 : le toolcache des waiters atteint reellement docker run ------
echo "Test 22 : waiters -- toolcache monte, et JAMAIS de volume _work (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin17" "$TEST_DIR/state-17" "$TEST_DIR/state-17b"
  # Stub docker distinct : il doit repondre aux probes de fraicheur #14801/
  # #15105 (`docker run --rm --entrypoint sha256sum` sur entrypoint.sh ET
  # work_cache_health.sh) AVANT de journaliser l'argv du vrai lancement,
  # sinon un probe serait compte comme un lancement de waiter.
  cat > "$TEST_DIR/bin17/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "run" ] && printf '%s' "\$*" | grep -q -- '--entrypoint sha256sum'; then
  printf '%s' "\$*" | grep -q 'work_cache_health.sh' \
    && echo "$REPO_HEALTH_SHA  /opt/runner/work_cache_health.sh" \
    || echo "$REPO_ENTRYPOINT_SHA  /opt/runner/entrypoint.sh"
  exit 0
fi
if [ "\$1" = "run" ]; then
  printf '%s\n' "\$*" >> "\$ARGV_LOG"
  sleep 3
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin17/docker"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin17/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin17/ps"
  # PAS de stub sleep ici (contrairement au bin/ global) : le `sleep 3` du
  # stub docker ci-dessus + le backoff reel bornent le rythme de la boucle
  # waiter -- sans eux, ARGV_LOG explose et `echo | grep -q` prend un
  # SIGPIPE sous pipefail (mesure CI Linux 2026-09-09).
  export PATH="$TEST_DIR/bin17:$PATH"
  export COURSIA_RUNNER_WAITER_NAME_PREFIX="test-waiter-17"

  export ARGV_LOG="$TEST_DIR/state-17/docker-argv.txt"
  : > "$ARGV_LOG"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-17"
  timeout --kill-after=1 20 bash "$SCRIPT_DIR/supervise.sh" waiters 1 >/dev/null 2>&1
  touch "$TEST_DIR/state-17/stop"   # les boucles orphelines sortent d'elles-memes
  argv="$(cat "$ARGV_LOG" 2>/dev/null)"
  if echo "$argv" | grep -q -- "-v coursia-runner-toolcache:/opt/hostedtoolcache" \
     && echo "$argv" | grep -q -- "-e RUNNER_TOOL_CACHE=/opt/hostedtoolcache"; then
    ok "toolcache monte sur le waiter (volume + RUNNER_TOOL_CACHE)"
  else
    ko "toolcache attendu dans l'argv du waiter, argv=$argv"
  fi
  # Garde #14385 : un _work PERSISTANT sur un pool sparse-checkout est le
  # vecteur ferme par cette issue. Le toolcache n'est pas _work ; ce controle
  # negatif est ce qui empeche la confusion de se glisser plus tard.
  if [ -n "$argv" ] && ! echo "$argv" | grep -q -- "/home/runner/_work"; then
    ok "aucun volume _work sur le waiter (garde #14385 preservee)"
  else
    ko "un volume _work est apparu sur le waiter -- REGRESSION #14385, argv=$argv"
  fi
  # Desactivable : la machine qui ne veut pas du toolcache le dit.
  export ARGV_LOG="$TEST_DIR/state-17b/docker-argv.txt"
  : > "$ARGV_LOG"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-17b"
  export COURSIA_RUNNER_WAITER_TOOLCACHE=0
  timeout --kill-after=1 3 bash "$SCRIPT_DIR/supervise.sh" waiters 1 >/dev/null 2>&1
  touch "$TEST_DIR/state-17b/stop"
  argv="$(cat "$ARGV_LOG" 2>/dev/null)"
  if [ -n "$argv" ] && ! echo "$argv" | grep -q -- "coursia-runner-toolcache"; then
    ok "COURSIA_RUNNER_WAITER_TOOLCACHE=0 : aucun montage"
  else
    ko "desactivation attendue, argv=$argv"
  fi
)
echo ""

# --- Test 23 : recensement inter-familles distinct du garde d'idempotence --
echo "Test 23 : supervisor_families voit les 3 familles, supervisor_pids seulement start"
(
  cd "$SCRIPT_DIR"
  export PS_OUTPUT="jsboige  111    1   10:00:00  bash scripts/ci/docker/linux-runner/supervise.sh start 8
jsboige  222    1   10:00:00  bash scripts/ci/docker/linux-runner/supervise.sh waiters 12
jsboige  333    1   10:00:00  bash scripts/ci/docker/linux-runner/supervise.sh lean 2
jsboige  444  111   10:00:00  bash scripts/ci/docker/linux-runner/supervise.sh start 8"
  source_supervise
  fams="$(supervisor_families)"
  n_fams="$(printf '%s\n' "$fams" | grep -c . )"
  n_pids="$(supervisor_pids | grep -c . )"
  if [ "$n_fams" = "3" ] && echo "$fams" | grep -q "222 waiters 12" \
     && echo "$fams" | grep -q "333 lean 2"; then
    ok "supervisor_families rend les 3 familles avec leur N"
  else
    ko "3 familles attendues, obtenu $n_fams : $fams"
  fi
  if [ "$n_pids" = "1" ]; then
    ok "supervisor_pids reste borne a start (idempotence #14259 inchangee)"
  else
    ko "supervisor_pids doit voir 1 seul start, obtenu $n_pids"
  fi
  # Le fork PPID=111 ne doit compter dans NI l'un NI l'autre.
  if ! echo "$fams" | grep -q "^444 "; then
    ok "le fork slot_loop (PPID!=1) est exclu du recensement"
  else
    ko "un fork a ete compte comme superviseur : $fams"
  fi
)
echo ""

# --- Test 24 : l'arret gracieux ne peut plus annoncer un succes inerte ------
# Defaut #15091 mesure sur ai-01 : cmd_stop rendait 0 quoi qu'il arrive. Le
# script tourne sous `set -uo pipefail` SANS `-e`, donc l'echec du `touch`
# n'interrompait rien et le code de retour etait celui du dernier `echo`. Un
# arret inerte etait indiscernable d'un arret reussi -- et c'est exactement ce
# qui s'est produit : l'unite ecrivait son sentinel dans /root/.coursia-runner/
# pendant que le superviseur surveillait /var/lib/coursia-runner/.
#
# Le controle NEGATIF est la moitie qui compte. Un `touch` sur un chemin dont
# le parent est un FICHIER ordinaire echoue (ENOTDIR) sur toutes les
# plateformes, y compris MSYS -- la ou un test par permissions serait muet
# sous Windows.
echo "Test 24 : cmd_stop rend != 0 quand le sentinel n'a PAS pu etre pose (#15091)"
(
  cd "$SCRIPT_DIR"
  source_supervise

  # (a) cas nominal : le sentinel est pose, rc=0, et le chemin est ANNONCE
  #     (l'ancienne version ne le disait pas -- c'est ce silence qui a rendu
  #     le mauvais STATE_DIR invisible pendant des semaines).
  STATE_DIR="$TEST_DIR/state-19"
  mkdir -p "$STATE_DIR"
  STOP_FILE="$STATE_DIR/stop"
  out="$(cmd_stop 2>&1)"; rc=$?
  if [ "$rc" = "0" ] && [ -e "$STOP_FILE" ]; then
    ok "cmd_stop nominal : sentinel pose, rc=0"
  else
    ko "cmd_stop nominal devrait poser $STOP_FILE et rendre 0 (rc=$rc)"
  fi
  if echo "$out" | grep -qF "$STOP_FILE"; then
    ok "cmd_stop annonce le CHEMIN du sentinel"
  else
    ko "le chemin du sentinel doit etre annonce, obtenu : $out"
  fi

  # (b) controle negatif : parent = fichier ordinaire -> touch impossible.
  printf 'ceci est un fichier, pas un repertoire\n' > "$TEST_DIR/pas-un-dir"
  STATE_DIR="$TEST_DIR/pas-un-dir"
  STOP_FILE="$STATE_DIR/stop"
  out="$(cmd_stop 2>&1)"; rc=$?
  if [ "$rc" != "0" ]; then
    ok "cmd_stop rend rc=$rc quand le sentinel ne peut pas etre ecrit"
  else
    ko "REGRESSION : cmd_stop rend 0 sur un sentinel non pose"
  fi
  if echo "$out" | grep -q "sentinel NON pose" \
     && echo "$out" | grep -q "COURSIA_RUNNER_STATE_DIR"; then
    ok "le message nomme la cause ET la variable qui la gouverne"
  else
    ko "message d'echec insuffisant : $out"
  fi
  # Et surtout : il ne doit PAS annoncer le succes.
  if ! echo "$out" | grep -q "aucun nouveau conteneur ne sera lance"; then
    ok "aucun message de succes n'est emis sur un arret inerte"
  else
    ko "l'echec annonce quand meme le succes : $out"
  fi
)
echo ""

# --- Test 25 : saturation >65 cycles -- l'exponentiel ne deborde plus -------
echo "Test 25 : 70 cycles courts consecutifs -- plafond tenu jusqu'au bout, jamais negatif ni nul (review #15166)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin25" "$TEST_DIR/state-25"
  cat > "$TEST_DIR/bin25/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  # assert_image_fresh sonde DEUX fichiers (#15105) : repondre au bon sha
  # selon la probe, sinon l'image est jugee PERIMEE et toute la boucle meurt.
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  if [ "\$RUNS" -ge "\${STUB_STOP_AFTER:-70}" ]; then touch "\$STUB_STOP_FILE"; fi
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin25/docker"
  cat > "$TEST_DIR/bin25/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin25/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin25/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin25/ps"
  rm -f "$TEST_DIR/state-25/stop" "$TEST_DIR/state-25/pids" "$TEST_DIR/run25.count"
  : > "$TEST_DIR/sleep25.log"
  (
    export PATH="$TEST_DIR/bin25:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-25"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-25"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=24
    export STUB_STOP_FILE="$TEST_DIR/state-25/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run25.count"
    export SLEEP_LOG="$TEST_DIR/sleep25.log"
    timeout --kill-after=2 60 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err25.log"
  )
  n="$(wc -l < "$TEST_DIR/sleep25.log")"
  if [ "$n" -eq 70 ]; then
    ok "70 cycles effectivement deroules (obtenu $n)"
  else
    ko "attendu 70 respirations, obtenu $n (err=$(head -2 "$TEST_DIR/err25.log"))"
  fi
  # Sans saturation, 3*2^62 deborde au cycle ~63 : negatif puis 0 (sleep 0 =
  # martellement). Avec BASE=3/CAP=24, les cycles 4+ doivent TOUS valoir 24.
  if [ "$(tail -n +4 "$TEST_DIR/sleep25.log" | sort -u)" = "24" ]; then
    ok "cycles 4-70 tous au plafond 24 -- saturation effective au-dela de 65 cycles"
  else
    ko "queue debordante : $(tail -5 "$TEST_DIR/sleep25.log" | tr '\n' ' ')"
  fi
  if grep -qE '^-[0-9]|^0$' "$TEST_DIR/sleep25.log"; then
    ko "valeurs negatives/nulles dans la file : $(grep -nE '^-[0-9]|^0$' "$TEST_DIR/sleep25.log" | head -2)"
  else
    ok "aucune valeur negative ni nule sur 70 cycles (le debordement 61+ est mort)"
  fi
)
echo ""

# --- Test 26 : controle positif -- cycle court AVEC travail reel ------------
echo "Test 26 : cycle court portant une execution de job -> pas de backoff, compteur remis a zero (review #15166)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin26" "$TEST_DIR/state-26"
  cat > "$TEST_DIR/bin26/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  # assert_image_fresh sonde DEUX fichiers (#15105) : repondre au bon sha
  # selon la probe, sinon l'image est jugee PERIMEE et toute la boucle meurt.
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  # Cycles 1-5 : le runner affiche l'execution d'un job (le log du cycle
  # porte la preuve de travail). Cycles 6+ : plus de travail -> boucle vide.
  if [ "\$RUNS" -le "\${STUB_WORK_UNTIL:-5}" ]; then
    echo "  Running job: test-job-\$RUNS"
  fi
  if [ "\$RUNS" -ge "\${STUB_STOP_AFTER:-8}" ]; then touch "\$STUB_STOP_FILE"; fi
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin26/docker"
  cat > "$TEST_DIR/bin26/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin26/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin26/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin26/ps"
  rm -f "$TEST_DIR/state-26/stop" "$TEST_DIR/state-26/pids" "$TEST_DIR/run26.count"
  : > "$TEST_DIR/sleep26.log"
  (
    export PATH="$TEST_DIR/bin26:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-26"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-26"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=24
    export STUB_STOP_FILE="$TEST_DIR/state-26/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run26.count"
    export SLEEP_LOG="$TEST_DIR/sleep26.log"
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err26.log"
  )
  seq="$(paste -sd, "$TEST_DIR/sleep26.log")"
  if [ "$seq" = "2,2,2,2,2,3,6,12" ]; then
    ok "5 cycles AVEC travail -> sleep 2 sans backoff, puis boucle vide REPART a 3,6,12 (compteur remis a zero par le travail)"
  else
    ko "attendu 2,2,2,2,2,3,6,12, obtenu [$seq]"
  fi
  if grep -q "cycle court AVEC travail" "$TEST_DIR/err26.log"; then
    ok "le travail reel est journalise comme tel"
  else
    ko "ligne 'cycle court AVEC travail' absente : $(head -3 "$TEST_DIR/err26.log")"
  fi
)
echo ""

# --- Test 27 : cycle long rc!=0 n'est PAS automatiquement sain --------------
echo "Test 27 : cycle vecu mais rc!=0 -> non qualifie sain, compteur conserve (review #15166)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin27" "$TEST_DIR/state-27"
  cat > "$TEST_DIR/bin27/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  # assert_image_fresh sonde DEUX fichiers (#15105) : repondre au bon sha
  # selon la probe, sinon l'image est jugee PERIMEE et toute la boucle meurt.
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  if [ "\$RUNS" = "\${STUB_BURN_AT:-3}" ]; then
    start=\$(date +%s)
    while [ \$(( \$(date +%s) - start )) -lt "\${STUB_BURN_SECS:-2}" ]; do :; done
  fi
  if [ "\$RUNS" -ge "\${STUB_STOP_AFTER:-6}" ]; then touch "\$STUB_STOP_FILE"; fi
  exit "\${STUB_DOCKER_RC:-1}"
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin27/docker"
  cat > "$TEST_DIR/bin27/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin27/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin27/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin27/ps"
  rm -f "$TEST_DIR/state-27/stop" "$TEST_DIR/state-27/pids" "$TEST_DIR/run27.count"
  : > "$TEST_DIR/sleep27.log"
  (
    export PATH="$TEST_DIR/bin27:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-27"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-27"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=2
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=24
    export COURSIA_RUNNER_BACKOFF_MIN_SEC=7
    export STUB_STOP_FILE="$TEST_DIR/state-27/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run27.count"
    export SLEEP_LOG="$TEST_DIR/sleep27.log"
    export STUB_BURN_AT=3
    export STUB_BURN_SECS=3
    export STUB_DOCKER_RC=1
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >"$TEST_DIR/out27.log" 2>"$TEST_DIR/err27.log"
  )
  seq="$(paste -sd, "$TEST_DIR/sleep27.log")"
  # Cycles 1-2 courts (3,6) ; cycle 3 brule 3s >= HEALTHY=2 mais rc=1 ->
  # respiration MIN 7 SANS remise a zero ; cycle 4 : le compteur etait
  # conserve a 2 -> 3*2^2=12 ; cycles 5-6 : plafond 24. (Avec l'ancien
  # reset inconditionnel on aurait vu 3,6,2,3,6,12.) HEALTHY=2 + burn 3s
  # pour qu'un cycle instantane ne puisse pas chevaucher un tick de
  # seconde et passer pour long par accident.
  if [ "$seq" = "3,6,7,12,24,24" ]; then
    ok "3,6 -> cycle long rc=1 : 7 (non sain) -> compteur conserve : 12,24,24"
  else
    ko "attendu 3,6,7,12,24,24, obtenu [$seq]"
  fi
  if grep -q "non qualifie sain" "$TEST_DIR/err27.log" \
     && ! grep -q "termine sainement" "$TEST_DIR/out27.log"; then
    ok "le cycle long rc!=0 n'est JAMAIS journalise sain"
  else
    ko "qualification saine indue : err=$(grep -c 'non qualifie' "$TEST_DIR/err27.log") out=$(grep -c 'sainement' "$TEST_DIR/out27.log")"
  fi
)
echo ""

# --- Test 28 : grand log de cycle -- grep -q tuait tail en SIGPIPE (#15166) --
echo "Test 28 : cycle court AVEC travail sur un log de cycle >64 Ko -- le travail est reconnu malgre le volume (review #15166)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin28" "$TEST_DIR/state-28"
  cat > "$TEST_DIR/bin28/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  # assert_image_fresh sonde DEUX fichiers (#15105) : repondre au bon sha
  # selon la probe, sinon l'image est jugee PERIMEE et toute la boucle meurt.
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  # Le signal de travail en tete, puis un corps volumineux (>> tampon pipe
  # ~64 Ko) : avec l'ancien grep -q, grep sortait des la premiere ligne pendant
  # que tail ecrivait encore le corps -> SIGPIPE 141 -> pipeline non nul ->
  # worked=0 -> un cycle AYANT travaille etait classe en boucle vide et partait
  # en backoff. Le corps doit depasser largement le tampon pour que tail soit
  # encore a ecrire quand grep -q se retire.
  echo "  Running job: test-job-\$RUNS"
  if [ "\${STUB_BIG_LOG:-0}" = "1" ]; then
    yes x | head -c 1048576
  fi
  if [ "\$RUNS" -ge "\${STUB_STOP_AFTER:-3}" ]; then touch "\$STUB_STOP_FILE"; fi
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin28/docker"
  cat > "$TEST_DIR/bin28/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin28/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin28/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin28/ps"
  rm -f "$TEST_DIR/state-28/stop" "$TEST_DIR/state-28/pids" "$TEST_DIR/run28.count"
  : > "$TEST_DIR/sleep28.log"
  (
    export PATH="$TEST_DIR/bin28:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-28"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-28"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=24
    export STUB_STOP_FILE="$TEST_DIR/state-28/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run28.count"
    export SLEEP_LOG="$TEST_DIR/sleep28.log"
    export STUB_BIG_LOG=1
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err28.log"
  )
  seq="$(paste -sd, "$TEST_DIR/sleep28.log")"
  # 3 cycles courts portant un gros log AVEC le signal de travail : chacun
  # doit etre reconnu -> sleep 2 sans backoff. L'ancien grep -q (SIGPIPE 141
  # -> worked=0) donnait 3,6,12 : le travail etait rejete en boucle vide.
  if [ "$seq" = "2,2,2" ]; then
    ok "3 cycles AVEC travail sur un grand log -> sleep 2 sans backoff (travail reconnu malgre le volume)"
  else
    ko "attendu 2,2,2, obtenu [$seq] -- un cycle a gros log portant du travail n'est PAS reconnu (grep -q / SIGPIPE 141 ?)"
  fi
  if grep -q "cycle court AVEC travail" "$TEST_DIR/err28.log"; then
    ok "les cycles a gros log sont bien journalises comme travailles"
  else
    ko "ligne 'cycle court AVEC travail' absente pour un cycle a gros log : $(head -3 "$TEST_DIR/err28.log")"
  fi
)
echo ""

# --- Test 29 : garde de fraicheur -- health script perime refuse (#15105) ---
# Le garde lit DEUX fichiers depuis #15105 (work_cache_health.sh est source
# par l'entrypoint). Le controle positif du COTE garde : un ecart sur le
# SEUL fichier ajoute doit refuser exactement comme un ecart d'entrypoint --
# sinon la porte que le nouveau fichier ouvre serait garde par personne.
echo "Test 29 : start refuse si work_cache_health.sh de l'image != checkout (#15105)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-29"
  STUB_IMG_HEALTH_SHA=e000000000000000000000000000000000000000000000000000000000000000e
  export STUB_IMG_HEALTH_SHA
  rc="$(run_supervise 'start 1' 'test-prefix-29' "$TEST_DIR/state-29" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "PERIMEE" && echo "$err" | grep -q "work_cache_health.sh"; then
    ok "health script perime refuse, fichier FAUTIF nomme (rc=$rc)"
  else
    ko "refus sur work_cache_health.sh attendu, rc=$rc err=$err"
  fi
  unset STUB_IMG_HEALTH_SHA
)
echo ""

# --- Test 30 : validation fail-closed des 3 bornes env (review #15166 v2) ---
# Une config operateur invalide doit tuer le start AVANT toute boucle :
# BASE=0 bouclait sur un backoff nul sans fin, et BASE/CAP proches de la
# borne signee faisaient deborder le probe de cap_exp vers le negatif puis 0.
# Chaque cas : rc!=0 (et !=124 : pas un timeout = pas de boucle), message
# nommant la variable fautive.
echo "Test 30 : bornes backoff invalides rejetees au demarrage (fail-closed)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-30"
  neg_case() {
    local desc="$1" expect="$2"
    rc="$(run_supervise 'start 1' 'test-prefix-30' "$TEST_DIR/state-30" 2>&1 | head -1 | sed 's/rc=//')"
    err="$(cat "$TEST_DIR/last.err")"
    if [ "$rc" != "0" ] && [ "$rc" != "124" ] && echo "$err" | grep -q "$expect"; then
      ok "$desc : refuse (rc=$rc)"
    else
      ko "$desc : attendu refus [$expect], rc=$rc err=$err"
    fi
  }
  export COURSIA_RUNNER_BACKOFF_BASE=0
  neg_case "BASE=0" "strictement positif"
  export COURSIA_RUNNER_BACKOFF_BASE=15x
  neg_case "BASE non numerique" "entier decimal"
  export COURSIA_RUNNER_BACKOFF_BASE=30
  export COURSIA_RUNNER_BACKOFF_CAP=24
  neg_case "BASE>CAP" "plafond doit dominer"
  export COURSIA_RUNNER_BACKOFF_BASE=15
  export COURSIA_RUNNER_BACKOFF_CAP=9999999999999999999
  neg_case "CAP 19 chiffres (hors domaine)" "18 chiffres"
  unset COURSIA_RUNNER_BACKOFF_BASE COURSIA_RUNNER_BACKOFF_CAP
)
echo ""

# --- Test 31 : frontiere puissance de deux -- le doublement garde (v2) -----
# Repro review : BASE proche de la borne signee + CAP au-dela debordait le
# probe (p=2^63 -> -2^63 -> 0 -> boucle infinie). Config valide limite : la
# plus grande puissance de deux du domaine (2^59, 18 chiffres) en BASE=CAP.
# Le backoff doit terminer (rc=0, pas de timeout) et rendre exactement la
# borne, jamais un negatif ni un zero.
echo "Test 31 : BASE=CAP=2^59 -- frontiere puissance de deux, pas de debordement"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin31" "$TEST_DIR/state-31"
  cat > "$TEST_DIR/bin31/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  case "\$*" in
    *work_cache_health.sh*)
      echo "$REPO_HEALTH_SHA  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "$REPO_ENTRYPOINT_SHA  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  if [ "\$RUNS" -ge 3 ]; then touch "\$STUB_STOP_FILE"; fi
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin31/docker"
  cat > "$TEST_DIR/bin31/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin31/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin31/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin31/ps"
  rm -f "$TEST_DIR/state-31/stop" "$TEST_DIR/state-31/pids" "$TEST_DIR/run31.count"
  : > "$TEST_DIR/sleep31.log"
  (
    export PATH="$TEST_DIR/bin31:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-31"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-31"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=576460752303423488
    export COURSIA_RUNNER_BACKOFF_CAP=576460752303423488
    export STUB_STOP_FILE="$TEST_DIR/state-31/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run31.count"
    export SLEEP_LOG="$TEST_DIR/sleep31.log"
    timeout --kill-after=2 15 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err31.log"
    echo "rc=$?" > "$TEST_DIR/rc31"
  )
  rc31="$(sed 's/rc=//' "$TEST_DIR/rc31")"
  seq31="$(paste -sd, "$TEST_DIR/sleep31.log")"
  bad=0
  for v in $(cat "$TEST_DIR/sleep31.log"); do
    [ "$v" -le 0 ] && bad=1
  done
  if [ "$rc31" = "0" ] && [ "$bad" = "0" ] && [ "$(sort -u "$TEST_DIR/sleep31.log" | wc -l)" = "1" ] && grep -q "^576460752303423488$" "$TEST_DIR/sleep31.log"; then
    ok "frontiere 2^59 : 3 backoffs exactement egaux a la borne, jamais negatifs/nuls, boucle TERMINEE (rc=0)"
  else
    ko "attendu rc=0 et backoff=2^59 plat ; rc=$rc31 seq=[$seq31] bad=$bad err=$(head -3 "$TEST_DIR/err31.log")"
  fi
)
echo ""

# --- Test 32 : les trois prefixes par defaut derivent du hostname (#15152) --
# L'ancien defaut codait myia-po-2024 en dur dans les trois familles : les
# runners de toute autre machine s'enregistraient sous l'identite de po-2024.
# Le test source le script AVEC un hostname stubbe en majuscules -- le
# hostname donne doit produire les trois prefixes, lowercasses, SANS qu'aucune
# variable ENV ne soit posee ; puis la surcharge ENV explicite (le contrat des
# wrappers persist/) doit rester prioritaire sur la derivation.
echo "Test 32 : hostname donne -> les trois prefixes de famille derives (#15152)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  export HOSTNAME_STUB="MYIA-TestHost-32"
  unset COURSIA_RUNNER_NAME_PREFIX COURSIA_RUNNER_WAITER_NAME_PREFIX \
        COURSIA_LEAN_RUNNER_NAME_PREFIX COURSIA_RUNNER_MACHINE_ID
  source_supervise
  if [ "${NAME_PREFIX:-}" = "myia-testhost-32-linux-docker" ]; then
    ok "NAME_PREFIX derive du hostname lowercasse (${NAME_PREFIX:-vide})"
  else
    ko "NAME_PREFIX='${NAME_PREFIX:-vide}', attendu myia-testhost-32-linux-docker"
  fi
  if [ "${WAITER_NAME_PREFIX:-}" = "myia-testhost-32-linux-waiter" ]; then
    ok "WAITER_NAME_PREFIX derive (${WAITER_NAME_PREFIX:-vide})"
  else
    ko "WAITER_NAME_PREFIX='${WAITER_NAME_PREFIX:-vide}', attendu myia-testhost-32-linux-waiter"
  fi
  if [ "${LEAN_NAME_PREFIX:-}" = "myia-testhost-32-lean-docker" ]; then
    ok "LEAN_NAME_PREFIX derive (${LEAN_NAME_PREFIX:-vide})"
  else
    ko "LEAN_NAME_PREFIX='${LEAN_NAME_PREFIX:-vide}', attendu myia-testhost-32-lean-docker"
  fi
  export COURSIA_RUNNER_WAITER_NAME_PREFIX="wrapper-explicit-w"
  source_supervise
  if [ "$WAITER_NAME_PREFIX" = "wrapper-explicit-w" ] \
     && [ "$NAME_PREFIX" = "myia-testhost-32-linux-docker" ]; then
    ok "surcharge ENV prioritaire, familles non surchargees restent derivees"
  else
    ko "surcharge ENV cassee : W='$WAITER_NAME_PREFIX' N='$NAME_PREFIX'"
  fi
  unset COURSIA_RUNNER_WAITER_NAME_PREFIX HOSTNAME_STUB
)
echo ""

# --- Test 33 : nom detenu par un conteneur EN COURS -- on attend, on ne tue
# pas (#15278). Le verrou de nom est GLOBAL au daemon : un restart tue le
# client `docker run` mais PAS le conteneur, qui garde son nom jusqu'a la fin
# de son job. Le garde doit attendre la liberation -- jamais retirer un
# conteneur en cours (ce serait tuer un job legitime) -- et le dire, en
# nommant le journal ou lire la cause.
echo "Test 33 : nom detenu par un conteneur EN COURS -- attente, AUCUN retrait, avertissement nommant le journal (#15278)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin33" "$TEST_DIR/state-33"
  cat > "$TEST_DIR/bin33/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "inspect" ]; then
  # Le job orphelin rend le nom au sondage STUB_ORPHAN_POLLS+1.
  N="\$(cat "\$STUB_INSPECT_COUNT" 2>/dev/null || echo 0)"
  N=\$(( N + 1 ))
  echo "\$N" > "\$STUB_INSPECT_COUNT"
  if [ "\$N" -le "\${STUB_ORPHAN_POLLS:-3}" ]; then echo "running"; fi
  exit 0
fi
if [ "\$1" = "rm" ]; then echo "\$*" >> "\$STUB_RM_LOG"; exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  touch "\$STUB_STOP_FILE"
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin33/docker"
  cat > "$TEST_DIR/bin33/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin33/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin33/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin33/ps"
  rm -f "$TEST_DIR/state-33/stop" "$TEST_DIR/state-33/pids" \
        "$TEST_DIR/run33.count" "$TEST_DIR/inspect33.count"
  : > "$TEST_DIR/sleep33.log"; : > "$TEST_DIR/rm33.log"
  (
    export PATH="$TEST_DIR/bin33:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-33"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-33"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=6
    export COURSIA_RUNNER_NAME_RECLAIM_POLL_SECS=5
    export COURSIA_RUNNER_NAME_RECLAIM_WARN_SECS=10
    export STUB_STOP_FILE="$TEST_DIR/state-33/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run33.count"
    export STUB_INSPECT_COUNT="$TEST_DIR/inspect33.count"
    export STUB_RM_LOG="$TEST_DIR/rm33.log"
    export SLEEP_LOG="$TEST_DIR/sleep33.log"
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err33.log"
  )
  # Le conteneur en cours NE DOIT JAMAIS etre retire : c'est l'acceptance
  # « la solution retenue ne peut pas tuer un conteneur executant un job
  # legitime ». Un `docker rm` sur le nom, meme une fois, la viole.
  if [ ! -s "$TEST_DIR/rm33.log" ]; then
    ok "aucun docker rm sur le nom detenu par un conteneur en cours (le job legitime survit)"
  else
    ko "retrait interdit d'un conteneur EN COURS : $(cat "$TEST_DIR/rm33.log")"
  fi
  polls="$(head -3 "$TEST_DIR/sleep33.log" | paste -sd,)"
  if [ "$polls" = "5,5,5" ]; then
    ok "3 sondages de 5 s pendant que le nom est detenu (attente, pas de relance en conflit)"
  else
    ko "attendu 3 sondages de 5 s, obtenu [$polls]"
  fi
  if grep -q "nom toujours detenu (running)" "$TEST_DIR/err33.log" \
     && grep -q "state-33/test-prefix-33-1.log" "$TEST_DIR/err33.log"; then
    ok "l'attente est journalisee, nomme l'etat et NOMME le journal du slot (diagnostic possible)"
  else
    ko "avertissement de reprise absent ou sans chemin de journal : $(head -3 "$TEST_DIR/err33.log")"
  fi
  runs="$(cat "$TEST_DIR/run33.count" 2>/dev/null || echo 0)"
  inspects="$(cat "$TEST_DIR/inspect33.count" 2>/dev/null || echo 0)"
  if [ "$runs" = "1" ] && [ "$inspects" = "4" ]; then
    ok "le slot reprend des que le nom est rendu (1 run apres 4 sondages, pas de cycle perdu)"
  else
    ko "reprise attendue apres liberation : runs=$runs inspects=$inspects"
  fi
)
echo ""

# --- Test 34 : nom detenu par un residu NON en cours -- retire, sans risque
# (#15278). Un conteneur `exited`/`created`/`dead` n'execute AUCUN job : le
# retirer ne peut tuer aucun travail. C'est la seule force que le garde
# s'autorise, et elle est bornee par ce discriminant d'etat.
echo "Test 34 : nom detenu par un residu NON en cours -- retire, aucun job en vol (#15278)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin34" "$TEST_DIR/state-34"
  cat > "$TEST_DIR/bin34/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "inspect" ]; then
  # Le residu existe tant que docker rm ne l'a pas enleve.
  if [ -f "\$STUB_RESIDUE" ]; then echo "exited"; fi
  exit 0
fi
if [ "\$1" = "rm" ]; then
  echo "\$*" >> "\$STUB_RM_LOG"
  rm -f "\$STUB_RESIDUE"
  exit 0
fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  touch "\$STUB_STOP_FILE"
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin34/docker"
  cat > "$TEST_DIR/bin34/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin34/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin34/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin34/ps"
  rm -f "$TEST_DIR/state-34/stop" "$TEST_DIR/state-34/pids" "$TEST_DIR/run34.count"
  : > "$TEST_DIR/residue34"; : > "$TEST_DIR/rm34.log"; : > "$TEST_DIR/sleep34.log"
  (
    export PATH="$TEST_DIR/bin34:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-34"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-34"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=6
    export STUB_STOP_FILE="$TEST_DIR/state-34/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run34.count"
    export STUB_RESIDUE="$TEST_DIR/residue34"
    export STUB_RM_LOG="$TEST_DIR/rm34.log"
    export SLEEP_LOG="$TEST_DIR/sleep34.log"
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err34.log"
  )
  if [ "$(wc -l < "$TEST_DIR/rm34.log")" = "1" ] \
     && grep -q "rm -f test-prefix-34-1" "$TEST_DIR/rm34.log"; then
    ok "le residu non en cours est retire exactement une fois, par son nom"
  else
    ko "retrait du residu attendu une fois sur test-prefix-34-1, obtenu [$(paste -sd';' "$TEST_DIR/rm34.log")]"
  fi
  if grep -q "residu de conteneur en etat 'exited' retire" "$TEST_DIR/err34.log"; then
    ok "le retrait est journalise avec l'etat qui l'autorise"
  else
    ko "ligne de retrait du residu absente : $(head -3 "$TEST_DIR/err34.log")"
  fi
  # Controle negatif : aucun avertissement de job en cours ne doit apparaitre --
  # le garde a distingue le residu du job vivant, il n'a pas simplement attendu.
  if ! grep -q "nom toujours detenu" "$TEST_DIR/err34.log" \
     && [ "$(cat "$TEST_DIR/run34.count" 2>/dev/null || echo 0)" = "1" ]; then
    ok "aucune attente declenchee (discriminant d'etat, pas un sursis) et le slot a repris"
  else
    ko "attente indue ou reprise manquante : err=$(head -2 "$TEST_DIR/err34.log") runs=$(cat "$TEST_DIR/run34.count" 2>/dev/null || echo 0)"
  fi
)
echo ""

# --- Test 35 : un rc != 0 NOMME le journal ou lire la cause (#15278) --------
# Defaut 2 de l'issue : le journal systemd ne portait que « rc=125 », alors que
# le message docker (« Conflict. The container name ... is already in use »,
# image perimee, daemon) part dans $STATE_DIR/<nom>.log par la redirection du
# `docker run`. Sans ce rappel, l'operateur n'est oriente vers rien.
echo "Test 35 : un cycle rc != 0 nomme le journal du slot dans le message d'echec (#15278)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin35" "$TEST_DIR/state-35"
  cat > "$TEST_DIR/bin35/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  touch "\$STUB_STOP_FILE"
  exit "\${STUB_DOCKER_RC:-1}"
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin35/docker"
  cat > "$TEST_DIR/bin35/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin35/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin35/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin35/ps"
  rm -f "$TEST_DIR/state-35/stop" "$TEST_DIR/state-35/pids" "$TEST_DIR/run35.count"
  : > "$TEST_DIR/sleep35.log"
  (
    export PATH="$TEST_DIR/bin35:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-35"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-35"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=6
    export STUB_STOP_FILE="$TEST_DIR/state-35/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run35.count"
    export STUB_DOCKER_RC=1
    export SLEEP_LOG="$TEST_DIR/sleep35.log"
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err35.log"
  )
  if grep -q "cycle court (rc=1" "$TEST_DIR/err35.log" \
     && grep -q -- "-- voir $TEST_DIR/state-35/test-prefix-35-1.log" "$TEST_DIR/err35.log"; then
    ok "le message de cycle court rc=1 nomme $TEST_DIR/state-35/test-prefix-35-1.log"
  else
    ko "journal non nomme sur rc=1 : $(head -3 "$TEST_DIR/err35.log")"
  fi
)
echo ""

# --- Test 36 : controle negatif du precedent -- rc=0 ne nomme RIEN (#15278)
# Le rappel est pose sur rc != 0 seulement. Sans ce controle, un `-- voir`
# ajoute inconditionnellement passerait le test 35 tout en alourdissant chaque
# cycle sain du journal.
echo "Test 36 : controle negatif -- un cycle rc=0 ne porte PAS le rappel de journal (#15278)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin36" "$TEST_DIR/state-36"
  cat > "$TEST_DIR/bin36/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  touch "\$STUB_STOP_FILE"
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin36/docker"
  cat > "$TEST_DIR/bin36/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin36/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin36/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin36/ps"
  rm -f "$TEST_DIR/state-36/stop" "$TEST_DIR/state-36/pids" "$TEST_DIR/run36.count"
  : > "$TEST_DIR/sleep36.log"
  (
    export PATH="$TEST_DIR/bin36:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-36"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-36"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=6
    export STUB_STOP_FILE="$TEST_DIR/state-36/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run36.count"
    export SLEEP_LOG="$TEST_DIR/sleep36.log"
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err36.log"
  )
  if grep -q "cycle court (rc=0" "$TEST_DIR/err36.log" \
     && ! grep -q -- "-- voir " "$TEST_DIR/err36.log"; then
    ok "cycle rc=0 journalise sans rappel de journal (le rappel reste reserve aux echecs)"
  else
    ko "rappel indu sur rc=0, ou ligne rc=0 absente : $(head -3 "$TEST_DIR/err36.log")"
  fi
)
echo ""
# --- Test 37 : etat NON QUALIFIE -- fail-closed, jamais retire (#15278) -----
# Le retrait est borne par une LISTE d'etats prouves non en cours
# (created/exited/dead), pas par une liste d'exclusion. Un etat que ce script
# ne qualifie pas (`restarting`, ou un etat qu'une version future de docker
# introduirait) ne doit donc PAS autoriser une destruction : c'est le seul
# cote ou l'erreur tue un job legitime.
echo "Test 37 : etat non qualifie (restarting) -- nom considere detenu, jamais retire (#15278)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin37" "$TEST_DIR/state-37"
  cat > "$TEST_DIR/bin37/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "info" ]; then exit 0; fi
if [ "\$1" = "image" ] || [ "\$1" = "volume" ]; then exit 0; fi
if [ "\$1" = "inspect" ]; then
  # 'restarting' n'est ni en cours ni prouve mort : le garde doit attendre.
  # Le conteneur rend le nom au sondage STUB_ORPHAN_POLLS+1.
  N="\$(cat "\$STUB_INSPECT_COUNT" 2>/dev/null || echo 0)"
  N=\$(( N + 1 ))
  echo "\$N" > "\$STUB_INSPECT_COUNT"
  if [ "\$N" -le "\${STUB_ORPHAN_POLLS:-2}" ]; then echo "restarting"; fi
  exit 0
fi
if [ "\$1" = "rm" ]; then echo "\$*" >> "\$STUB_RM_LOG"; exit 0; fi
if [ "\$1" = "run" ] && [ "\$3" = "--entrypoint" ]; then
  case "\$*" in
    *work_cache_health.sh*)
      echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh"
      ;;
    *)
      echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh"
      ;;
  esac
  exit 0
fi
if [ "\$1" = "run" ]; then
  RUNS="\$(cat "\$STUB_RUN_COUNT" 2>/dev/null || echo 0)"
  RUNS=\$(( RUNS + 1 ))
  echo "\$RUNS" > "\$STUB_RUN_COUNT"
  touch "\$STUB_STOP_FILE"
  exit 0
fi
exit 0
STUB
  chmod +x "$TEST_DIR/bin37/docker"
  cat > "$TEST_DIR/bin37/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$@" >> "$SLEEP_LOG"
STUB
  chmod +x "$TEST_DIR/bin37/sleep"
  cp "$TEST_DIR/bin/gh" "$TEST_DIR/bin37/gh"
  cp "$TEST_DIR/bin/ps" "$TEST_DIR/bin37/ps"
  rm -f "$TEST_DIR/state-37/stop" "$TEST_DIR/state-37/pids" \
        "$TEST_DIR/run37.count" "$TEST_DIR/inspect37.count"
  : > "$TEST_DIR/rm37.log"; : > "$TEST_DIR/sleep37.log"
  (
    export PATH="$TEST_DIR/bin37:$PATH"
    export COURSIA_RUNNER_NAME_PREFIX="test-prefix-37"
    export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-37"
    export COURSIA_RUNNER_HEALTHY_CYCLE_SECS=9999
    export COURSIA_RUNNER_BACKOFF_BASE=3
    export COURSIA_RUNNER_BACKOFF_CAP=6
    export COURSIA_RUNNER_NAME_RECLAIM_POLL_SECS=5
    export COURSIA_RUNNER_NAME_RECLAIM_WARN_SECS=10
    # 3 sondages tenus : c'est ce qui fait atteindre le seuil d'avertissement
    # (waited=10 au 3e) avant que le nom ne soit rendu au 4e. A 2 sondages la
    # boucle sort a waited=5 et l'avertissement ne peut pas tomber -- c'est un
    # fait de cadence, pas un defaut du garde.
    export STUB_ORPHAN_POLLS=3
    export STUB_STOP_FILE="$TEST_DIR/state-37/stop"
    export STUB_RUN_COUNT="$TEST_DIR/run37.count"
    export STUB_INSPECT_COUNT="$TEST_DIR/inspect37.count"
    export STUB_RM_LOG="$TEST_DIR/rm37.log"
    export SLEEP_LOG="$TEST_DIR/sleep37.log"
    timeout --kill-after=2 30 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/err37.log"
  )
  if [ ! -s "$TEST_DIR/rm37.log" ]; then
    ok "aucun retrait sur un etat non qualifie (fail-closed : l'inconnu ne detruit rien)"
  else
    ko "retrait interdit sur etat non qualifie : $(cat "$TEST_DIR/rm37.log")"
  fi
  if grep -q "nom toujours detenu (restarting)" "$TEST_DIR/err37.log" \
     && [ "$(cat "$TEST_DIR/run37.count" 2>/dev/null || echo 0)" = "1" ]; then
    ok "l'etat non qualifie est traite comme 'detenu', puis le slot reprend a la liberation"
  else
    ko "attente sur etat non qualifie attendue : err=$(head -2 "$TEST_DIR/err37.log") runs=$(cat "$TEST_DIR/run37.count" 2>/dev/null || echo 0)"
  fi
)
echo ""


# --- Verdict agrege ---------------------------------------------------------
# `|| echo 0` serait un piege ici, et il l'a ete : `grep -c` IMPRIME "0" avant
# de sortir 1 quand il ne trouve rien, donc le repli SUFFIXE un second zero au
# lieu de remplacer -- n_fail vaut alors "0\n0", qui n'est pas egal a "0", et
# le harnais se declare rouge avec 0 echec. Un gestionnaire d'erreur qui
# fabrique un resultat plus grand que le vrai. Le repli ne sert qu'au fichier
# absent : c'est ${x:-0} qui le couvre, apres coup.
n_pass="$(grep -c '^PASS ' "$RESULTS" 2>/dev/null)"; n_pass="${n_pass:-0}"
n_fail="$(grep -c '^FAIL ' "$RESULTS" 2>/dev/null)"; n_fail="${n_fail:-0}"
echo "==========================================================="
echo "  $n_pass PASS / $n_fail FAIL"
if [ "$n_fail" != "0" ]; then
  echo ""
  echo "Assertions en echec :"
  grep '^FAIL ' "$RESULTS" | sed 's/^FAIL /  - /'
  echo ""
  echo "Repertoire de travail conserve pour diagnostic : $TEST_DIR"
  exit 1
fi
# Controle de vivacite : un harnais qui n'a rien assere sort vert sans avoir
# rien mesure. Zero assertion est un ECHEC, pas un succes -- c'est ce que rend
# un fichier de test dont le chemin de stubs est casse.
if [ "$n_pass" = "0" ]; then
  echo "ERREUR: aucune assertion executee -- le harnais n'a rien mesure." >&2
  exit 2
fi
rm -rf "$TEST_DIR"
exit 0
