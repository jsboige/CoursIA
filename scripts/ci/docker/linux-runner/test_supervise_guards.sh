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

# Stubs docker + gh + ps. Le stub docker simule une image A JOUR pour le
# garde de fraicheur #14801 : au probe `run --entrypoint sha256sum`, il rend
# le sha256 du VRAI script sibling demande (entrypoint.sh, et depuis #15105
# work_cache_health.sh -- le garde lit les DEUX, le stub dispatche sur le
# chemin passe en argument). STUB_IMG_ENTRYPOINT_SHA / STUB_IMG_HEALTH_SHA
# forcent un ecart pour tester le refus (tests 9 et 20).
REPO_ENTRYPOINT_SHA="$(sha256sum "$SCRIPT_DIR/entrypoint.sh" 2>/dev/null | awk '{print $1}')"
REPO_HEALTH_SHA="$(sha256sum "$SCRIPT_DIR/work_cache_health.sh" 2>/dev/null | awk '{print $1}')"
cat > "$TEST_DIR/bin/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "run" ]; then
  case "\$*" in
    *'/opt/runner/entrypoint.sh')        echo "\${STUB_IMG_ENTRYPOINT_SHA:-$REPO_ENTRYPOINT_SHA}  /opt/runner/entrypoint.sh" ;;
    *'/opt/runner/work_cache_health.sh') echo "\${STUB_IMG_HEALTH_SHA:-$REPO_HEALTH_SHA}  /opt/runner/work_cache_health.sh" ;;
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
  timeout --kill-after=1 4 bash "$SCRIPT_DIR/supervise.sh" start 1 --force >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  # 1.5 s : le garde de fraicheur #15105 lit DEUX scripts embarques, soit
  # deux probes docker de plus avant le rm du sentinel -- sous Git Bash ou
  # chaque fork de stub coute ~100 ms, 0.5 s coupaient parfois AVANT le rm
  # et le test echouait sur une question de delai, pas d'intention.
  sleep 1.5
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

# --- Test 11 : backoff exponentiel, plafonne, jitter borne -----------------
echo "Test 11 : backoff exponentiel plafonne et disperse (#15091)"
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

# --- Test 12 : budget CPU inter-familles -- REFUS au depassement -----------
echo "Test 12 : budget CPU inter-familles refuse le depassement (#15091, trou #14337)"
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

# --- Test 13 : controle negatif -- le budget n'accuse pas a tort -----------
echo "Test 13 : budget CPU -- controle negatif (sous le plafond, puis non arme)"
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

# --- Test 14 : borne agregee -- REFUS fail-closed quand elle manque --------
echo "Test 14 : slice absente -- refus fail-closed et commande de deploiement (#15091)"
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

# --- Test 15 : plafond par conteneur -- drapeaux et aveu de non-application -
echo "Test 15 : --device-write-bps cable, et non-resolution AVOUEE (#15091)"
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

# --- Test 16 : rotation des journaux ---------------------------------------
echo "Test 16 : rotation du journal de slot au-dela du seuil (#15091)"
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

# --- Test 17 : le toolcache des waiters atteint reellement docker run ------
echo "Test 17 : waiters -- toolcache monte, et JAMAIS de volume _work (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/bin17" "$TEST_DIR/state-17" "$TEST_DIR/state-17b"
  # Stub docker distinct : il doit repondre au probe de fraicheur #14801
  # (`docker run --rm --entrypoint sha256sum`) AVANT de journaliser l'argv du
  # vrai lancement, sinon le probe serait compte comme un lancement de waiter.
  cat > "$TEST_DIR/bin17/docker" <<STUB
#!/usr/bin/env bash
if [ "\$1" = "run" ] && printf '%s' "\$*" | grep -q -- '--entrypoint sha256sum'; then
  case "\$*" in
    *'/opt/runner/entrypoint.sh')        echo "$REPO_ENTRYPOINT_SHA  /opt/runner/entrypoint.sh" ;;
    *'/opt/runner/work_cache_health.sh') echo "$REPO_HEALTH_SHA  /opt/runner/work_cache_health.sh" ;;
  esac
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
  export PATH="$TEST_DIR/bin17:$PATH"
  export COURSIA_RUNNER_WAITER_NAME_PREFIX="test-waiter-17"

  export ARGV_LOG="$TEST_DIR/state-17/docker-argv.txt"
  : > "$ARGV_LOG"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-17"
  timeout --kill-after=1 3 bash "$SCRIPT_DIR/supervise.sh" waiters 1 >/dev/null 2>&1
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

# --- Test 18 : recensement inter-familles distinct du garde d'idempotence --
echo "Test 18 : supervisor_families voit les 3 familles, supervisor_pids seulement start"
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

# --- Test 19 : l'arret gracieux ne peut plus annoncer un succes inerte ------
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
echo "Test 19 : cmd_stop rend != 0 quand le sentinel n'a PAS pu etre pose (#15091)"
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

# --- Test 20 : garde de fraicheur -- health script perime refuse (#15105) ---
# Le garde lit DEUX fichiers depuis #15105 (work_cache_health.sh est source
# par l'entrypoint). Le controle positif du COTE garde : un ecart sur le
# SEUL fichier ajoute doit refuser exactement comme un ecart d'entrypoint --
# sinon la porte que le nouveau fichier ouvre serait garde par personne.
echo "Test 20 : start refuse si work_cache_health.sh de l'image != checkout (#15105)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-20"
  STUB_IMG_HEALTH_SHA=e000000000000000000000000000000000000000000000000000000000000000e
  export STUB_IMG_HEALTH_SHA
  rc="$(run_supervise 'start 1' 'test-prefix-20' "$TEST_DIR/state-20" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "PERIMEE" && echo "$err" | grep -q "work_cache_health.sh"; then
    ok "health script perime refuse, fichier FAUTIF nomme (rc=$rc)"
  else
    ko "refus sur work_cache_health.sh attendu, rc=$rc err=$err"
  fi
  unset STUB_IMG_HEALTH_SHA
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
