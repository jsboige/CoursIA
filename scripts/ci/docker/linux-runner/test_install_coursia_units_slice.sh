#!/usr/bin/env bash
# Test sans machine cible : install-coursia-units.sh gere correctement une
# slice (*.slice) sans [Install] -- `enable` ne doit JAMAIS etre tente sur
# une slice, et l'assertion A3 doit se satisfaire de `is-active` seul.
#
# Bug vise (#19440, review Hermes du 06/10) : avant le fix, le script
# (1) appelait `systemctl enable --now coursia-ci.slice` -- refuse par
# systemd (« The unit files have no [Install] section »), ce qui faisait
# sortir le script en `die` AVANT la verification A3 ; (2) meme sans le
# die, `is-enabled` rendait `static` pour la slice et l'assertion A3
# sortait en code 2 garanti.
#
# Le test monte un mini-persist/ qui imite le layout reel (persist/ai-01/
# pour les services machine, persist/ a la racine pour la slice et le
# daemon.json) et un stub systemctl qui rend les valeurs documentees.
# Si le fix est correct, le script sort en 0 sans jamais tenter
# `enable --now` sur la slice.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

TEST_DIR="/tmp/install-coursia-units-test-$$"
mkdir -p "$TEST_DIR/bin" "$TEST_DIR/persist/ai-01/coursia-runner.service.d"
RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# Fixture : un service avec [Install] (reference pour le bon chemin) et une
# slice sans [Install] (le cas vise par le fix #19440). Layout fidele au
# reel : services de ai-01 sous persist/ai-01/, slice et daemon.json sous
# persist/ directement.

# Services ai-01 (avec [Install])
cat > "$TEST_DIR/persist/ai-01/coursia-runner.service" <<'UNIT'
[Unit]
Description=fixture runner service

[Service]
ExecStart=/bin/true

[Install]
WantedBy=multi-user.target
UNIT

cat > "$TEST_DIR/persist/ai-01/coursia-runner-start.sh" <<'SH'
#!/usr/bin/env bash
exit 0
SH
chmod +x "$TEST_DIR/persist/ai-01/coursia-runner-start.sh"

cat > "$TEST_DIR/persist/ai-01/coursia-waiters.service" <<'UNIT'
[Unit]
Description=fixture waiters service

[Service]
ExecStart=/bin/true

[Install]
WantedBy=multi-user.target
UNIT

cat > "$TEST_DIR/persist/coursia-waiters-start.sh" <<'SH'
#!/usr/bin/env bash
exit 0
SH
chmod +x "$TEST_DIR/persist/coursia-waiters-start.sh"

# Drop-in minimal (juste la presence compte).
cat > "$TEST_DIR/persist/ai-01/coursia-runner.service.d/10-sizing.conf" <<'CONF'
[Service]
CPUQuota=200%
CONF

# Slice SANS [Install] -- c'est precisement le cas teste.
cat > "$TEST_DIR/persist/coursia-ci.slice" <<'UNIT'
[Unit]
Description=fixture slice (test sans machine cible -- pas d'[Install] par construction)

[Slice]
CPUQuota=100%
UNIT

# daemon.json minimal
printf '{\n  "cgroup-parent": "coursia-ci.slice"\n}\n' > "$TEST_DIR/persist/daemon.json"

# Stub systemctl : rend les valeurs documentees pour les unites du test, et
# JOURNALISE chaque appel dans $SYSTEMCTL_LOG. La trace sert de preuve :
# `enable --now coursia-ci.slice` ne doit JAMAIS apparaitre.
cat > "$TEST_DIR/bin/systemctl" <<'STUB'
#!/usr/bin/env bash
echo "$*" >> "${SYSTEMCTL_LOG:-/tmp/icc-systemctl.log}"
# `is-enabled` : la slice rend `static` (pas d'[Install]), les services rendent `enabled`.
if [ "$1" = "is-enabled" ]; then
  case "$2" in
    coursia-ci.slice)        printf 'static\n'; exit 0 ;;
    coursia-runner.service|coursia-waiters.service) printf 'enabled\n'; exit 0 ;;
    *) printf 'disabled\n'; exit 0 ;;
  esac
fi
# `is-active` : tout est `active` (start reussi plus haut).
if [ "$1" = "is-active" ]; then
  case "$2" in
    coursia-ci.slice|coursia-runner.service|coursia-waiters.service) printf 'active\n'; exit 0 ;;
    *) printf 'inactive\n'; exit 0 ;;
  esac
fi
# `enable --now` : OK pour les services, REFUSE pour les slices (ce qu'aurait
# fait systemd sur la machine cible). Le bug vise consistait a appeler ce
# chemin pour les slices -- le test echoue si la trace le revele.
if [ "$1" = "enable" ] && [ "$2" = "--now" ]; then
  case "$3" in
    coursia-ci.slice)
      echo "Failed to enable unit: Unit file $3 has no [Install] section" >&2
      exit 1
      ;;
    coursia-runner.service|coursia-waiters.service) exit 0 ;;
    *) exit 0 ;;
  esac
fi
# `start` : OK partout.
if [ "$1" = "start" ]; then exit 0; fi
# `daemon-reload` : OK.
if [ "$1" = "daemon-reload" ]; then exit 0; fi
exit 0
STUB
chmod +x "$TEST_DIR/bin/systemctl"

# Stub install(1) : simule l'installation reussie. (Le test ne tourne pas
# en root, donc le VRAI install(1) refuserait.)
cat > "$TEST_DIR/bin/install" <<'STUB'
#!/usr/bin/env bash
echo "install $*" >> "${INSTALL_LOG:-/tmp/icc-install.log}"
exit 0
STUB
chmod +x "$TEST_DIR/bin/install"

# Stub id(1) : faire croire au script qu'il est root (le die racine sinon).
cat > "$TEST_DIR/bin/id" <<'STUB'
#!/usr/bin/env bash
if [ "$1" = "-u" ]; then printf '0\n'; else printf 'uid=0(root) gid=0(root) groups=0(root)\n'; fi
STUB
chmod +x "$TEST_DIR/bin/id"

# Stub hostname : forcer ai-01 (la machine ou le bug se manifeste -- po-2024
# n'a pas de slice dans son inventaire, cf. L122-128 du script).
cat > "$TEST_DIR/bin/hostname" <<'STUB'
#!/usr/bin/env bash
printf 'myia-ai-01\n'
STUB
chmod +x "$TEST_DIR/bin/hostname"

# COURSIA_REPO_DIR : on pointe sur un depot qui contient le sous-arbre
# `scripts/ci/docker/linux-runner/persist/` (la fixture ci-dessus).
DEPO_FAKE="$TEST_DIR/depo"
mkdir -p "$DEPO_FAKE/scripts/ci/docker/linux-runner"
ln -s "$TEST_DIR/persist" "$DEPO_FAKE/scripts/ci/docker/linux-runner/persist"

export SYSTEMCTL_LOG="$TEST_DIR/systemctl.log"
export INSTALL_LOG="$TEST_DIR/install.log"
: > "$SYSTEMCTL_LOG"
: > "$INSTALL_LOG"

export PATH="$TEST_DIR/bin:$PATH"
export COURSIA_REPO_DIR="$DEPO_FAKE"

# On execute le script SANS --dry-run : le dry-run shunte `enable --now`,
# et le bug ne se manifeste qu'a l'execution reelle. Le stub systemctl rend
# l'environnement testable. `bash -e` attrape un die.
echo "Test : install-coursia-units.sh gere une slice sans [Install] (#19440)"
(
  rc=0
  bash -e "$SCRIPT_DIR/install-coursia-units.sh" --machine ai-01 \
    >"$TEST_DIR/out.log" 2>"$TEST_DIR/err.log" || rc=$?
  echo "rc=$rc"
) > "$TEST_DIR/run.log" 2>&1
run_rc="$(grep -m1 '^rc=' "$TEST_DIR/run.log" | sed 's/rc=//')"

# Assertion 1 : le script sort en code 0.
if [ "$run_rc" = "0" ]; then
  ok "script sort en rc=0 sur slice sans [Install]"
else
  ko "script sorti en rc=$run_rc (le bug #19440 est-il toujours la ?)"
  echo "  -- run.log --"; sed 's/^/    /' "$TEST_DIR/run.log"
fi

# Assertion 2 : `enable --now coursia-ci.slice` n'a JAMAIS ete appele.
# (Le fix doit exclure la slice du pattern enable ; si elle apparait dans la
# trace, soit le fix n'est pas applique, soit le stub est mal cable.)
if grep -q 'enable --now coursia-ci.slice' "$SYSTEMCTL_LOG"; then
  ko "enable --now coursia-ci.slice APPELE -- le fix ne couvre pas le pattern enable"
else
  ok "enable --now coursia-ci.slice JAMAIS appele (slice exclue du pattern)"
fi

# Assertion 3 : `enable --now` a ete appele pour les services (le fix ne
# doit pas les sur-exclure).
if grep -q 'enable --now coursia-runner.service' "$SYSTEMCTL_LOG" \
   && grep -q 'enable --now coursia-waiters.service' "$SYSTEMCTL_LOG"; then
  ok "enable --now appele pour les 2 services (services non touches par le fix)"
else
  ko "enable --now services MANQUANT -- le fix a sur-exclu"
fi

# Assertion 4 : la verification A3 declare la slice `active` (le `is-active`
# seul suffit apres le fix). Note : la log() du script ecrit sur stderr
# (cf. `printf ... >&2` en tete du script), donc la trace A3 vit dans
# $TEST_DIR/err.log, pas dans out.log.
if grep -q 'coursia-ci.slice  is-active=active' "$TEST_DIR/err.log"; then
  ok "verification A3 : slice verifiee via is-active seul (comportement attendu)"
else
  ko "A3 ne reconnait pas la slice comme active (rc=$run_rc)"
fi

# Assertion 5 : la verification A3 declare les services `enabled` ET `active`.
if grep -q 'coursia-runner.service  is-enabled=enabled  is-active=active' "$TEST_DIR/err.log" \
   && grep -q 'coursia-waiters.service  is-enabled=enabled  is-active=active' "$TEST_DIR/err.log"; then
  ok "verification A3 : services valides via is-enabled + is-active"
else
  ko "A3 ne valide pas les services (rc=$run_rc)"
fi

# Assertion 6 : la trace ne contient pas de `die` ni de refus.
if grep -q 'ABANDON' "$TEST_DIR/run.log"; then
  ko "le journal contient un ABANDON (le fix n'a pas tenu)"
else
  ok "aucun ABANDON dans le journal"
fi

echo ""
echo "==="
PASS_COUNT="$(grep -c '^PASS' "$RESULTS" 2>/dev/null | tr -d '[:space:]' || echo 0)"
FAIL_COUNT="$(grep -c '^FAIL' "$RESULTS" 2>/dev/null | tr -d '[:space:]' || echo 0)"
PASS_COUNT="${PASS_COUNT:-0}"
FAIL_COUNT="${FAIL_COUNT:-0}"
echo "  $PASS_COUNT PASS / $FAIL_COUNT FAIL"
echo "==="

# Verdict agrégé : exit 0 si tout passe, exit 1 sinon. Le harnais CI agrege
# par le code de retour -- c'est le SEUL signal qu'il lit.
[ "$FAIL_COUNT" -eq 0 ]
