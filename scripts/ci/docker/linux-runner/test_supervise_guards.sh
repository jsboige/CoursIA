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
# forcent un ecart pour tester le refus (tests 9 et 41).
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
# un cycle court attendait un backoff reel de 15 s ; les tests 1-3/7/10/34
# (timeouts 1-3 s) timeout-rent au lieu de mesurer. Ce stub rend toutes les
# attentes de supervise.sh instantanees ; les tests 22 a 40 posent LEURS stubs
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

# Le garde d'hote (#15091) prend DEUX echantillons espaces de DISTRESS_GAP_S et
# lit des compteurs de performance Windows. Les tests 1 a 10 ne portent PAS sur
# lui : on DECLARE une mesure nominale et un ecart nul. Sans cela chaque test
# paierait 15 s d'attente et son verdict dependrait de l'etat reel de la machine
# qui l'execute -- une suite dont le resultat varie avec la charge de l'hote ne
# mesure plus les gardes qu'elle pretend mesurer.
# Format : pagewrites pagesout file_disque idle%_min vmmem_Mo mapped_Mo
export COURSIA_RUNNER_HOST_PROBE="0 0 0 95 40000 50000"
export COURSIA_RUNNER_DISTRESS_GAP_S=0

# Meme raison que le garde d'hote ci-dessus, pour le mur agrege (#15091) :
# `assert_ci_slice` lit la slice CI, et sans declaration il lirait la VRAIE
# slice de la machine -- via `wsl.exe`, a ~135 ms l'aller-retour, et en
# echouant en bloc sur toute machine ou elle n'est pas deployee. Les tests 1
# a 16 ne portent pas sur ce garde : on declare une slice PLAFONNEE, en
# fichiers ordinaires (lus directement, sans interop). Les tests 17, 29, 30 et 31,
# eux, surchargent ce chemin -- c'est leur objet.
COURSIA_CI_SLICE_PATH="$TEST_DIR/slice-nominale"
mkdir -p "$COURSIA_CI_SLICE_PATH"
echo 17179869184 > "$COURSIA_CI_SLICE_PATH/memory.max"
echo 12884901888 > "$COURSIA_CI_SLICE_PATH/memory.high"
export COURSIA_CI_SLICE_PATH

# Helper : executer supervise.sh avec env detourne. Timeout pour eviter le
# hang de wait() -- cmd_start lance wait() qui attend les slot_loop infinis.
# La fenetre (8 s) est large : elle borne execute() sans dependre d'une
# machine rapide -- les refus testes arrivent en tete de cmd_start, la
# charge machine ne doit pas les transformer en timeout.

# Arret du superviseur d'UN test, et de lui seul.
#
# La version precedente terminait par `pkill -f 'supervise.sh start'`, non
# scope : sur une machine ou un superviseur REEL tourne, lancer cette suite
# le tuait en plein job -- et un job tue rend un rouge qui ne veut rien dire
# (c'est la raison d'etre de `cmd_stop`, qui pose un sentinel au lieu de
# tuer). On tue les enfants du test, puis les slot_loop que le superviseur a
# lui-meme inscrits dans SON state dir : deux ensembles bornes au test.
kill_test_supervisor() {
  local tpid="$1" state="$2"
  [ -n "$tpid" ] && pkill -P "$tpid" 2>/dev/null
  if [ -f "$state/pids" ]; then
    while read -r pid; do
      [ -n "$pid" ] && kill "$pid" 2>/dev/null
    done < "$state/pids"
  fi
  wait 2>/dev/null
  return 0
}

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

# Attente BORNEE plutot que `sleep <constante>`. Un `sleep 0.5` suivi d'une
# assertion n'est pas un test, c'est une course : sur cette machine le prelude
# de cmd_start met 680 a 924 ms (spawns de processus Git Bash + la sonde d'hote
# a deux echantillons), et le test rendait donc FAIL sur un comportement
# correct. On attend la CONDITION, avec un plafond -- l'echec reste un echec,
# il cesse d'etre un chronometre.
wait_until() {
  local deadline_ms="$1"; shift
  local waited=0
  while [ "$waited" -lt "$deadline_ms" ]; do
    if "$@"; then return 0; fi
    # REAL_SLEEP, pas le stub : les tests exportent le PATH stubbe AVANT
    # d'appeler wait_until -- un sleep nu tournerait instantanement et le
    # plafond expirerait en millisecondes reelles, pas en deadline_ms.
    "$REAL_SLEEP" 0.05
    waited=$(( waited + 50 ))
  done
  return 1
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

# --- Test 2 : start apres stop, SUPERVISEUR VIVANT -> refus -----
#
# #15163 -- ce test verifiait auparavant le refus AVEC `unset PS_OUTPUT`,
# c'est-a-dire dans le cas ou aucun superviseur ne tourne. C'etait pinner le
# defaut : le sentinel est un fichier, il survit au reboot, et le refus
# inconditionnel wedgeait donc le pool au demarrage de la machine (mesure du
# 2026-09-07 : quatre redemarrages a la main dans la journee).
#
# Ce qui est teste ici est la moitie du Defaut 2 qui reste VRAIE : un arret
# gracieux reellement en cours ne doit pas etre pietine. Le PPID du stub est
# volontairement != 1 -- un superviseur de PPID 1 serait deja intercepte par la
# garde `existing_pids` en amont, et le test ne mesurerait pas la porte.
echo "Test 2 : start apres stop AVEC superviseur vivant refuse, sentinel preserve (#15163)"
(
  cd "$SCRIPT_DIR"
  export PS_OUTPUT="jsboige  33594  9876   10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  touch "$TEST_DIR/state-B/stop"
  rc="$(run_supervise 'start 1' 'test-prefix-B' "$TEST_DIR/state-B" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "sentinel STOP_FILE present"; then
    ok "start apres stop refuse (rc=$rc)"
  else
    ko "start aurait du refuser sur sentinel, rc=$rc err=$err"
  fi
  # Le refus doit NOMMER le superviseur qui le motive : c'est ce qui distingue
  # un arret en cours d'une sentinelle perimee pour qui lit le journal.
  if echo "$err" | grep -q "superviseur est vivant" && echo "$err" | grep -q "33594"; then
    ok "le refus nomme le superviseur vivant (PID 33594)"
  else
    ko "le refus aurait du nommer le PID 33594, err=$err"
  fi
  if [ -f "$TEST_DIR/state-B/stop" ]; then
    ok "sentinel preserve apres start refuse"
  else
    ko "sentinel aurait du etre preserve"
  fi
  unset PS_OUTPUT
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
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" start 1 --force >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  if wait_until 4000 test ! -f "$TEST_DIR/state-C/stop"; then
    ok "sentinel leve par start --force"
  else
    ko "sentinel aurait du etre leve par start --force (encore present)"
  fi
  kill_test_supervisor "$TPID" "$COURSIA_RUNNER_STATE_DIR"
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
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  # `sleep 1` n'etait pas une attente, c'etait un chronometre : le prelude de
  # cmd_start met 680 a 924 ms (cf. wait_until ci-dessus) et le fetch du
  # registration-token vit APRES lui. La marge etait de 76 ms -- le test
  # passait ou echouait selon la charge, sans rien dire du code teste. On
  # attend la CONDITION, plafonnee.
  wait_until 5000 grep -q 'registration-token' "$GH_CALLS_LOG"
  kill_test_supervisor "$TPID" "$COURSIA_RUNNER_STATE_DIR"
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
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" start 1 >"$TEST_DIR/out-10.log" 2>"$TEST_DIR/last.err" &
  TPID=$!
  # Signal fiable de "slots lances" : $STATE_DIR/pids est ecrit par
  # redirection directe (immediate), alors que les echoes stdout du
  # supervise sont bufferises (visibles seulement a la sortie du process).
  # Poll borne : la chaine de gardes depend de la charge machine.
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
  kill_test_supervisor "$TPID" "$COURSIA_RUNNER_STATE_DIR"
)
echo ""

# --- Test 11 : CONTROLE POSITIF -- detresse soutenue refuse (#15091) -----
#
# Ce test est la raison d'etre des quatre suivants. Un garde qui ne rougit
# jamais est indiscernable d'un garde debranche, et la version precedente de
# celui-ci l'etait litteralement : elle lisait AvgDisksecPerRead, un UInt32 EN
# SECONDES, contre un seuil en millisecondes -- il ne POUVAIT pas se declencher.
# On verifie donc d'abord qu'il sait dire non.
echo "Test 11 : start refuse sur une detresse soutenue sur les DEUX points (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-11"
  # pagewrites>0 ET pagesout>0 ET file>=1 ET idle<=50 -- sur les deux points.
  export COURSIA_RUNNER_HOST_PROBE="120 340 3 12 90000 50000"
  export COURSIA_RUNNER_HOST_PROBE_2="98 410 2 18 91000 49800"
  rc="$(run_supervise 'start 1' 'test-prefix-11' "$TEST_DIR/state-11" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "DETRESSE"; then
    ok "detresse soutenue refusee (rc=$rc)"
  else
    ko "refus attendu sur detresse soutenue, rc=$rc err=$err"
  fi
  unset COURSIA_RUNNER_HOST_PROBE_2
)
echo ""

# --- Test 11b : CONTROLE NEGATIF -- la detresse doit mordre alors que les deux
# compteurs disque restent muets (#15091) -----
#
# C'est le test qui manquait, et son absence a laisse passer un garde mort.
# Le Test 11 declare une detresse ou LES QUATRE termes sont vrais : il passait
# aussi bien avant qu'apres, parce qu'il ne pouvait pas distinguer « la
# conjonction fonctionne » de « la conjonction n'est jamais evaluee ».
#
# La signature reelle d'ai-01, mesuree le 2026-09-08T00:14Z : file d'attente
# disque a 0 et disque a 92-99 % d'inactivite MEME sous 320 Mo d'ecriture
# write-through. Avec les termes `q >= 1` et `id <= 50` dans la conjonction,
# une machine qui pagine franchement (pagewrites ET pagesout soutenus sur les
# deux points) etait declaree SAINE. Ce test rougit sur l'ancienne version.
echo "Test 11b : detresse retenue meme avec file=0 et disque inactif (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-11b"
  # pagewrites>0 ET pagesout>0 sur les deux points -- mais file=0 et idle=99,
  # les valeurs que ces deux compteurs rendent TOUJOURS sur cet hote.
  export COURSIA_RUNNER_HOST_PROBE="140 520 0 99 96000 50000"
  export COURSIA_RUNNER_HOST_PROBE_2="155 610 0 98 97000 49900"
  rc="$(run_supervise 'start 1' 'test-prefix-11b' "$TEST_DIR/state-11b" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "DETRESSE SOUTENUE"; then
    if echo "$err" | grep -q "cote disque MUET"; then
      ok "detresse retenue sans les compteurs disque, et le silence est dit (rc=$rc)"
    else
      ko "detresse retenue mais le silence des compteurs disque n'est pas signale, err=$err"
    fi
  else
    ko "GARDE MORT : pagination soutenue declaree saine parce que file=0, rc=$rc err=$err"
  fi
  unset COURSIA_RUNNER_HOST_PROBE_2
)
echo ""

# --- Test 12 : un SEUL point en detresse ne suffit pas (#15091) -----
#
# Le faux positif que Maintenance a elle-meme produit le 2026-09-07T22:53Z (un
# pic isole a 293 lectures/s, latence 0, file 0) est exactement ce qu'un
# echantillon unique ne sait pas ecarter. « Soutenu » veut dire deux points.
echo "Test 12 : un pic isole ne declenche pas le refus (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-12"
  export COURSIA_RUNNER_HOST_PROBE="120 340 3 12 90000 50000"
  export COURSIA_RUNNER_HOST_PROBE_2="0 0 0 97 40000 50000"
  rc="$(run_supervise 'start 1' 'test-prefix-12' "$TEST_DIR/state-12" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if ! echo "$err" | grep -q "DETRESSE"; then
    ok "pic isole non retenu comme detresse (rc=$rc)"
  else
    ko "faux positif : un seul point a fait rougir le garde, err=$err"
  fi
  unset COURSIA_RUNNER_HOST_PROBE_2
)
echo ""

# --- Test 13 : chute de Mapped -- critere d'abandon qdrant (#15091) -----
echo "Test 13 : start refuse quand Mapped chute au-dela du seuil (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-13"
  # Machine par ailleurs calme : seul le mmap qdrant se fait evincer (-2000 Mo).
  export COURSIA_RUNNER_HOST_PROBE="0 0 0 95 40000 52000"
  export COURSIA_RUNNER_HOST_PROBE_2="0 0 0 95 40000 50000"
  rc="$(run_supervise 'start 1' 'test-prefix-13' "$TEST_DIR/state-13" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "Mapped"; then
    ok "eviction du mmap qdrant refusee (rc=$rc)"
  else
    ko "refus attendu sur chute de Mapped, rc=$rc err=$err"
  fi
  unset COURSIA_RUNNER_HOST_PROBE_2
)
echo ""

# --- Test 14 : sonde injoignable -- fail-CLOSED (#15091) -----
#
# Le controle qui manquait a la version precedente : une sonde muette doit
# couter un REFUS. Si la panne de mesure etait le chemin le plus permissif,
# il suffirait de casser la sonde pour desarmer le garde.
echo "Test 14 : sonde injoignable = refus, jamais un vert par defaut (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-14" "$TEST_DIR/bin14"
  # Stub powershell.exe muet, en tete de PATH : la sonde ne rend rien.
  printf '#!/usr/bin/env bash
exit 1
' > "$TEST_DIR/bin14/powershell.exe"
  chmod +x "$TEST_DIR/bin14/powershell.exe"
  export PATH="$TEST_DIR/bin14:$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-14"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-14"
  unset COURSIA_RUNNER_HOST_PROBE
  unset COURSIA_RUNNER_HOST_PROBE_2
  timeout --kill-after=1 5 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/last.err"
  rc=$?
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "NON MESURABLE"; then
    ok "sonde injoignable : refus fail-closed (rc=$rc)"
  else
    ko "refus attendu sur sonde injoignable, rc=$rc err=$err"
  fi
)
echo ""

# --- Test 15 : variable RETIREE -- avertissement bruyant (#15091) -----
#
# Les deux seuils precedents (free reel, % de commit) ont ete retires par leur
# auteur. Un operateur qui les positionne encore doit l'APPRENDRE, pas croire
# qu'il gouverne un garde qui ne les lit plus.
echo "Test 15 : une variable retiree produit un avertissement (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-15"
  export COURSIA_RUNNER_HOST_FREE_FLOOR_GB=8
  run_supervise 'status' 'test-prefix-15' "$TEST_DIR/state-15" >/dev/null 2>&1
  err="$(cat "$TEST_DIR/last.err")"
  if echo "$err" | grep -q "RETIREE"; then
    ok "variable retiree signalee a l'operateur"
  else
    ko "aucun avertissement sur variable retiree, err=$err"
  fi
  unset COURSIA_RUNNER_HOST_FREE_FLOOR_GB
)
echo ""

# --- Test 16 : sonde TRONQUEE -- refus, pas un vert silencieux (#15091) -----
#
# Le controle qui manquait a la version precedente du garde, sous une autre
# forme. Une sonde qui rend CINQ champs au lieu de six laisse `mapped` vide :
# le test arithmetique echoue en silence, la conjonction de detresse ne se
# declenche pas non plus, et la fonction tombe sur son chemin sain. Le garde
# serait alors VERT PAR MANQUE DE MESURE -- indiscernable d'un garde debranche.
echo "Test 16 : une sonde tronquee refuse au lieu de rendre vert (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-16"
  export COURSIA_RUNNER_HOST_PROBE="0 0 0 95 40000"
  rc="$(run_supervise 'start 1' 'test-prefix-16' "$TEST_DIR/state-16" 2>&1 | head -1 | sed 's/rc=//')"
  err="$(cat "$TEST_DIR/last.err")"
  if [ "$rc" != "0" ] && echo "$err" | grep -q "ILLISIBLE"; then
    ok "sonde tronquee refusee (rc=$rc)"
  else
    ko "refus attendu sur sonde tronquee, rc=$rc err=$err"
  fi
)
echo ""

# --- Test 17 : CONTROLE POSITIF -- slice plafonnee = mur annonce actif -----
#
# Le defaut repare ici : la slice existait, portait bien MemoryHigh 12 Gio et
# MemoryMax 16 Gio, et AUCUN conteneur n'y entrait -- le `docker run` n'avait
# pas de `--cgroup-parent`. Mesure ai-01 2026-09-08T00:56Z : memory.peak
# rendait 0 pendant que deux conteneurs CI consommaient 198 Mio dehors. Le
# mur agrege etait decoratif, et son propre instrument de pic le confirmait
# en disant « aucune charge n'a jamais tourne » -- ce qui etait vrai de la
# slice, et faux de la CI.
echo "Test 17 : slice plafonnee -> le mur est annonce ACTIF (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  mkdir -p "$TEST_DIR/state-17" "$TEST_DIR/slice-ok"
  echo "17179869184" > "$TEST_DIR/slice-ok/memory.max"
  echo "12884901888" > "$TEST_DIR/slice-ok/memory.high"
  export COURSIA_CI_SLICE_PATH="$TEST_DIR/slice-ok"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-17"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-17"
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" start 1 >"$TEST_DIR/out-17.log" 2>"$TEST_DIR/last.err" &
  TPID=$!
  wait_until 4000 grep -q "slots lances" "$TEST_DIR/out-17.log"
  if grep -q "mur agrege ACTIF" "$TEST_DIR/out-17.log" && grep -q "slots lances" "$TEST_DIR/out-17.log"; then
    ok "slice plafonnee : mur actif, slots lances"
  else
    ko "attendu 'mur agrege ACTIF' + demarrage, out=$(cat "$TEST_DIR/out-17.log") err=$(cat "$TEST_DIR/last.err")"
  fi
  kill_test_supervisor "$TPID" "$COURSIA_RUNNER_STATE_DIR"
)
echo ""

# --- Test 18 : sentinelle perimee (aucun superviseur) -> purge -----
#
# Le cas du reboot, qui est la raison d'etre de #15163. Le sentinel est un
# FICHIER : il survit a l'extinction de la machine. Au demarrage suivant plus
# aucun superviseur ne peut "reprendre", donc il n'y a plus rien a proteger --
# et le refus inconditionnel ne faisait que garder le pool a zero.
echo "Test 18 : sentinelle sans superviseur vivant -> purgee, le start procede (#15163)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-20"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-20"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  touch "$COURSIA_RUNNER_STATE_DIR/stop"
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  if wait_until 4000 test ! -f "$COURSIA_RUNNER_STATE_DIR/stop"; then
    ok "sentinelle perimee purgee, sans --force"
  else
    ko "sentinelle aurait du etre purgee (aucun superviseur vivant)"
  fi
  err="$(cat "$TEST_DIR/last.err")"
  if echo "$err" | grep -q "perimee"; then
    ok "la purge est tracee en clair sur stderr"
  else
    ko "la purge aurait du etre tracee sur stderr, err=$err"
  fi
  kill_test_supervisor "$TPID" "$COURSIA_RUNNER_STATE_DIR"
)
echo ""

# --- Test 19 : jeton non-numerique ne fabrique pas un superviseur -----
#
# Controle NEGATIF du scan de processus. Une ligne `ps -ef` a colonnes glissees
# met un jeton non-numerique en $2 ; sans le filtre `$2 ~ /^[0-9]+$/`, il est
# rendu comme un PID et la porte refuse au nom d'un superviseur qui n'existe
# pas. Le PPID du stub est != 1 pour que `supervisor_pids` laisse passer et que
# ce soit bien `any_supervisor_alive` qui soit mesure ici.
echo "Test 19 : ligne ps a colonnes decalees -> aucun faux superviseur (#15163)"
(
  cd "$SCRIPT_DIR"
  export PS_OUTPUT="jsboige  -c  9876  10:28:11  bash scripts/ci/docker/linux-runner/supervise.sh start 4"
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-21"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-21"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  touch "$COURSIA_RUNNER_STATE_DIR/stop"
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" start 1 >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  if wait_until 4000 test ! -f "$COURSIA_RUNNER_STATE_DIR/stop"; then
    ok "le jeton non-numerique n'a pas fabrique de superviseur"
  else
    ko "purge attendue : '-c' n'est pas un PID"
  fi
  err="$(cat "$TEST_DIR/last.err")"
  if echo "$err" | grep -q "PID -c"; then
    ko "un jeton non-numerique a ete rendu comme PID, err=$err"
  else
    ok "aucun PID non-numerique dans le diagnostic"
  fi
  kill_test_supervisor "$TPID" "$COURSIA_RUNNER_STATE_DIR"
  unset PS_OUTPUT
)
echo ""

# --- Test 20 : la porte couvre aussi la famille waiters -----
#
# Le wedge etait porte par TROIS sites (`start`, `waiters`, `lean`) ; corriger
# `start` seul aurait laisse le pool d'attente bloque au reboot. La porte est
# appelee avant `assert_memory_budget`, donc la purge est observable meme si la
# suite refuse pour une autre raison.
echo "Test 20 : la porte a sentinelle couvre aussi waiters (#15163)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  export PATH="$TEST_DIR/bin:$PATH"
  export COURSIA_RUNNER_NAME_PREFIX="test-prefix-22"
  export COURSIA_RUNNER_STATE_DIR="$TEST_DIR/state-22"
  mkdir -p "$COURSIA_RUNNER_STATE_DIR"
  touch "$COURSIA_RUNNER_STATE_DIR/stop"
  timeout --kill-after=1 8 bash "$SCRIPT_DIR/supervise.sh" waiters 1 >/dev/null 2>"$TEST_DIR/last.err" &
  TPID=$!
  if wait_until 4000 test ! -f "$COURSIA_RUNNER_STATE_DIR/stop"; then
    ok "sentinelle perimee purgee aussi sur waiters"
  else
    ko "waiters aurait du purger la sentinelle perimee"
  fi
  kill_test_supervisor "$TPID" "$COURSIA_RUNNER_STATE_DIR"
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
  unset COURSIA_REQUIRE_CI_SLICE COURSIA_CI_SLICE_PATH
  unset COURSIA_RUNNER_DEVICE_WRITE_BPS COURSIA_RUNNER_DEVICE_READ_BPS
  unset COURSIA_RUNNER_BLKIO_DEVICE COURSIA_RUNNER_CPU_BUDGET
  # shellcheck disable=SC1090
  . "$SCRIPT_DIR/supervise.sh" status >/dev/null 2>&1
}

# --- Test 21 : daemon Docker indisponible -> start refuse AVANT tout (#15095)
echo "Test 21 : start refuse si docker info echoue, avant gh et avant docker run"
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

# --- Test 22 : cycles courts -> backoff exponentiel plafonne, rc-agnostique
echo "Test 22 : backoff exponentiel 3,6,12,24... plafonne 24, identique rc=0 et rc!=0"
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

# --- Test 23 : plafond BACKOFF_CAP effectif (queue du test 22) -------------
echo "Test 23 : le plafond CAP borne la file (entries 4+ toutes = CAP)"
(
  # Derive direct du test 22 : avec BASE=3/CAP=24, les cycles 4 a 8 valent
  # tous 24 -- 5 valeurs consecutives egales au cap prouvent le clamp sans
  # avoir besoin d'attendre 15*2^N secondes avec les vrais defauts.
  if [ "$(tail -5 "$TEST_DIR/sleep12.log" | sort -u)" = "24" ]; then
    ok "5 respirations consecutives au plafond 24 -- clamp effectif"
  else
    ko "queue incoherente : $(tail -5 "$TEST_DIR/sleep12.log" | tr '\n' ' ')"
  fi
)
echo ""

# --- Test 24 : un cycle sain remet le compteur de backoff a zero -----------
echo "Test 24 : cycle ayant vecu >= HEALTHY_CYCLE_SECS -> reset + sleep 2"
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

# --- Test 25 : persist/ -- unit systemd fail-closed + garde wrapper ---------
echo "Test 25 : checks textuels persist/ (unit systemd + wrapper) et bash -n"
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
# --- Test 26 : backoff exponentiel, plafonne, jitter borne -----------------
echo "Test 26 : backoff exponentiel plafonne et disperse (#15091)"
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

# --- Test 27 : budget CPU inter-familles -- REFUS au depassement -----------
echo "Test 27 : budget CPU inter-familles refuse le depassement (#15091, trou #14337)"
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

# --- Test 28 : controle negatif -- le budget n'accuse pas a tort -----------
echo "Test 28 : budget CPU -- controle negatif (sous le plafond, puis non arme)"
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

# --- Test 29 : borne agregee -- REFUS fail-closed quand elle manque --------
echo "Test 29 : slice absente -- refus fail-closed et commande de deploiement (#15091)"
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

# --- Test 30 : mur MEMOIRE, slice ABSENTE -> refus SOUS EXIGENCE, avertissement sinon ---
#
# Sous le pilote cgroupfs, `docker run --cgroup-parent <chemin absent>` CREE
# le cgroup. Sans garde, un deploiement manquant produirait donc un cgroup
# neuf SANS plafond : le mur ne bornerait rien, mais memory.peak monterait et
# la slice aurait l'air cablee.
#
# La reponse a ce risque n'est PAS un refus inconditionnel : la slice est
# deployee sur ai-01 SEULEMENT (persist/README.md), et un refus par defaut
# ferait refuser de demarrer les runners de po-2024, qui ne l'ont jamais eue.
# C'est la discipline opt-in que #15103 a posee pour assert_cgroup_budget, et
# ce test verifie que le mur MEMOIRE la suit : refus si COURSIA_REQUIRE_CI_SLICE=1,
# sinon avertissement + CI_CGROUP_PARENT vide (donc pas de --cgroup-parent
# passe a docker, donc aucun cgroup fabrique).
echo "Test 30 : slice absente -> refus sous exigence, avertissement sinon (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  source_supervise
  CI_SLICE_PATH="$TEST_DIR/slice-nexiste-pas-$$"
  CI_CGROUP_PARENT="fantome.slice"
  REQUIRE_CI_SLICE=1
  err="$( (assert_ci_slice) 2>&1 )"; rc=$?
  if [ "$rc" != "0" ] && echo "$err" | grep -q "REFUS de demarrer"; then
    ok "slice absente sous exigence : demarrage refuse (rc=$rc)"
  else
    ko "refus attendu sur slice absente sous exigence, rc=$rc err=$err"
  fi
  if echo "$err" | grep -q "persist/coursia-ci.slice"      && echo "$err" | grep -q "systemctl daemon-reload"; then
    ok "le refus porte la commande de deploiement"
  else
    ko "commande de deploiement attendue dans le message, err=$err"
  fi
  # Sans exigence : la machine sans slice demarre, mais NON placee.
  REQUIRE_CI_SLICE=0
  CI_CGROUP_PARENT="fantome.slice"
  # Appel NU (pas de $(...)) : c est la forme des vrais sites d appel, et la
  # seule ou l effet de bord CI_CGROUP_PARENT="" atteint le shell appelant.
  assert_ci_slice > "$TEST_DIR/slice-warn.out" 2>&1; rc=$?
  err="$(cat "$TEST_DIR/slice-warn.out")"
  if [ "$rc" = "0" ] && echo "$err" | grep -q "NON ACTIF"; then
    ok "sans exigence : avertit et laisse passer (aucun defaut impose)"
  else
    ko "avertissement non bloquant attendu, rc=$rc err=$err"
  fi
  if [ -z "$CI_CGROUP_PARENT" ]; then
    ok "placement neutralise : --cgroup-parent ne sera pas passe"
  else
    ko "CI_CGROUP_PARENT devait etre vide, vaut '$CI_CGROUP_PARENT'"
  fi
)
echo ""

# --- Test 31 : mur MEMOIRE, slice presente mais SANS plafond -> meme discipline ---------
#
# Le cas que `slice_read` ne peut pas distinguer : il ne rend que des chiffres,
# donc il rend "" pour un fichier illisible ET pour la valeur litterale `max`.
# Ces deux cas commandent des actions opposees. C'est pour ce cas precis que
# `slice_read_raw` existe -- un cgroup sans plafond est present, lisible, et
# ne borne rien. Meme opt-in que le Test 28 : sur ai-01 c'est un refus, sur une
# machine qui ne deploie pas la slice c'est un avertissement.
echo "Test 31 : slice sans plafond (memory.max=max) -> refus sous exigence (#15091)"
(
  cd "$SCRIPT_DIR"
  unset PS_OUTPUT
  source_supervise
  mkdir -p "$TEST_DIR/slice-illimitee"
  echo "max" > "$TEST_DIR/slice-illimitee/memory.max"
  echo "max" > "$TEST_DIR/slice-illimitee/memory.high"
  CI_SLICE_PATH="$TEST_DIR/slice-illimitee"
  REQUIRE_CI_SLICE=1
  err="$( (assert_ci_slice) 2>&1 )"; rc=$?
  if [ "$rc" != "0" ] && echo "$err" | grep -q "SANS plafond"; then
    ok "slice sans plafond refusee sous exigence (rc=$rc)"
  else
    ko "refus attendu sur memory.max=max, rc=$rc err=$err"
  fi
  REQUIRE_CI_SLICE=0
  CI_CGROUP_PARENT="fantome.slice"
  assert_ci_slice > "$TEST_DIR/slice-warn2.out" 2>&1; rc=$?
  err="$(cat "$TEST_DIR/slice-warn2.out")"
  if [ "$rc" = "0" ] && echo "$err" | grep -q "SANS plafond"      && echo "$err" | grep -q "NON ACTIF" && [ -z "$CI_CGROUP_PARENT" ]; then
    ok "sans exigence : avertit, nomme la cause, et ne place pas"
  else
    ko "avertissement non bloquant attendu, rc=$rc err=$err parent='$CI_CGROUP_PARENT'"
  fi
)
echo ""

# --- Test 32 : plafond par conteneur -- drapeaux et aveu de non-application -
echo "Test 32 : --device-write-bps cable, et non-resolution AVOUEE (#15091)"
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

# --- Test 33 : rotation des journaux ---------------------------------------
echo "Test 33 : rotation du journal de slot au-dela du seuil (#15091)"
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

# --- Test 34 : le toolcache des waiters atteint reellement docker run ------
echo "Test 34 : waiters -- toolcache monte, et JAMAIS de volume _work (#15091)"
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

# --- Test 35 : recensement inter-familles distinct du garde d'idempotence --
echo "Test 35 : supervisor_families voit les 3 familles, supervisor_pids seulement start"
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

# --- Test 36 : l'arret gracieux ne peut plus annoncer un succes inerte ------
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
echo "Test 36 : cmd_stop rend != 0 quand le sentinel n'a PAS pu etre pose (#15091)"
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

# --- Test 37 : saturation >65 cycles -- l'exponentiel ne deborde plus -------
echo "Test 37 : 70 cycles courts consecutifs -- plafond tenu jusqu'au bout, jamais negatif ni nul (review #15166)"
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

# --- Test 38 : controle positif -- cycle court AVEC travail reel ------------
echo "Test 38 : cycle court portant une execution de job -> pas de backoff, compteur remis a zero (review #15166)"
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

# --- Test 39 : cycle long rc!=0 n'est PAS automatiquement sain --------------
echo "Test 39 : cycle vecu mais rc!=0 -> non qualifie sain, compteur conserve (review #15166)"
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

# --- Test 40 : grand log de cycle -- grep -q tuait tail en SIGPIPE (#15166) --
echo "Test 40 : cycle court AVEC travail sur un log de cycle >64 Ko -- le travail est reconnu malgre le volume (review #15166)"
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

# --- Test 41 : garde de fraicheur -- health script perime refuse (#15105) ---
# Le garde lit DEUX fichiers depuis #15105 (work_cache_health.sh est source
# par l'entrypoint). Le controle positif du COTE garde : un ecart sur le
# SEUL fichier ajoute doit refuser exactement comme un ecart d'entrypoint --
# sinon la porte que le nouveau fichier ouvre serait garde par personne.
echo "Test 41 : start refuse si work_cache_health.sh de l'image != checkout (#15105)"
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

# --- Test 42 : validation fail-closed des 3 bornes env (review #15166 v2) ---
# Une config operateur invalide doit tuer le start AVANT toute boucle :
# BASE=0 bouclait sur un backoff nul sans fin, et BASE/CAP proches de la
# borne signee faisaient deborder le probe de cap_exp vers le negatif puis 0.
# Chaque cas : rc!=0 (et !=124 : pas un timeout = pas de boucle), message
# nommant la variable fautive.
echo "Test 42 : bornes backoff invalides rejetees au demarrage (fail-closed)"
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

# --- Test 43 : frontiere puissance de deux -- le doublement garde (v2) -----
# Repro review : BASE proche de la borne signee + CAP au-dela debordait le
# probe (p=2^63 -> -2^63 -> 0 -> boucle infinie). Config valide limite : la
# plus grande puissance de deux du domaine (2^59, 18 chiffres) en BASE=CAP.
# Le backoff doit terminer (rc=0, pas de timeout) et rendre exactement la
# borne, jamais un negatif ni un zero.
echo "Test 43 : BASE=CAP=2^59 -- frontiere puissance de deux, pas de debordement"
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
