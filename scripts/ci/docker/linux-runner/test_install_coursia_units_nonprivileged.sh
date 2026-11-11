#!/usr/bin/env bash
# Test #23342 : install-coursia-units.sh exerce ses DEUX modes non privilegies.
#
# Le test precedent (test_install_coursia_units_slice.sh, #19440) stubbe `id`
# pour rendre 0 (root) et n'exerce que le mode reel. Les deux modes NON
# privilegies restaient sans preuve, alors que c'est tout le point du correctif
# (porte par #23228, consigne #23342) :
#   (a) --dry-run non privilegue  -> doit aboutir (rc=0), plan evalue,
#       AUCUNE ecriture : c'est ce qui autorise l'evaluation sans ouvrir de
#       fenetre d'elevation (la discipline de flotte l'exige).
#   (b) mode reel non privilegue   -> doit abandonner (rc=1, "root requis") :
#       le mode reel ne s'execute QUE privilegie, et la garde l.114 le porte.
#
# Ce test stubbe `id` pour rendre 1000 (NON root) -- la difference de fond
# avec le test precedent -- et verifie les deux modes ci-dessus.
#
# CONTROLE POSITIF (le test a des dents) : une copie MUTEE du script, ou la
# ligne de garde l.114 est remplacee par un `die` INCONDITIONNEL (c.-a-d.
# l'exemption dry-run est RETIREE), doit faire ECHEC au cas (a). C'est la
# preuve que le test detecte la regression de la garde -- il ne rend pas un
# vert aveugle.
#
# Perimetre hermetique : les trois racines absolues du script
# (/etc/systemd/system, /etc/docker, /usr/local/bin) sont redirigees sous
# $TEST_DIR par une copie sed ; les sources des unites sont des fixtures crees
# par le test. Le test ne lit ni n'ecrit rien du systeme reel.
#
# Machine de fixture : po-2024 (4 unites, la plus petite liste) -- le choix ne
# change pas le verdict, il borne la surface de fixture.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGET_SCRIPT="$SCRIPT_DIR/install-coursia-units.sh"
[ -r "$TARGET_SCRIPT" ] || { echo "FAIL: cible introuvable : $TARGET_SCRIPT"; exit 1; }

TEST_DIR="/tmp/install-coursia-units-np-$$"
mkdir -p "$TEST_DIR/bin" "$TEST_DIR/persist"
RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# --- fixture : les 4 unites sources de po-2024 -----------------------------
# Elles DOIVENT exister : icc_install_unit verifie `[ -r "$src" ]` AVANT la
# gate dry-run (l.201), donc un fichier manquant ferait sortir en ABANDON
# meme en dry-run.
cat > "$TEST_DIR/persist/coursia-runner.service" <<'UNIT'
[Unit]
Description=fixture runner
[Service]
ExecStart=/bin/true
[Install]
WantedBy=multi-user.target
UNIT
printf '#!/usr/bin/env bash\nexit 0\n' > "$TEST_DIR/persist/coursia-runner-start.sh"
chmod +x "$TEST_DIR/persist/coursia-runner-start.sh"
cat > "$TEST_DIR/persist/coursia-lean.service" <<'UNIT'
[Unit]
Description=fixture lean
[Service]
ExecStart=/bin/true
[Install]
WantedBy=multi-user.target
UNIT
printf '#!/usr/bin/env bash\nexit 0\n' > "$TEST_DIR/persist/coursia-lean-start.sh"
chmod +x "$TEST_DIR/persist/coursia-lean-start.sh"

# --- stubs des outils du chemin -------------------------------------------
# systemctl : journalise + rend des etats plausibles. En dry-run il n'est JAMAIS
# appele (les 6 sites sont gates) ; en mode reel le script meurt a la garde
# l.114 avant d'ici.
cat > "$TEST_DIR/bin/systemctl" <<'STUB'
#!/usr/bin/env bash
echo "$*" >> "${SYSTEMCTL_LOG:-/tmp/icc-systemctl.log}"
if [ "$1" = "is-enabled" ]; then printf 'enabled\n'; exit 0; fi
if [ "$1" = "is-active" ]; then printf 'active\n'; exit 0; fi
exit 0
STUB
chmod +x "$TEST_DIR/bin/systemctl"

# install(1) : journalise, ne fait rien. S'il est JAMAIS appele en dry-run,
# c'est un defaut (le dry-run ne doit rien ecrire) -- detection par le log.
cat > "$TEST_DIR/bin/install" <<'STUB'
#!/usr/bin/env bash
echo "install $*" >> "${INSTALL_LOG:-/tmp/icc-install.log}"
exit 0
STUB
chmod +x "$TEST_DIR/bin/install"

# id(1) : NON privilegie (uid=1000) -- le point central de ce test.
cat > "$TEST_DIR/bin/id" <<'STUB'
#!/usr/bin/env bash
if [ "$1" = "-u" ]; then printf '1000\n'; else printf 'uid=1000(user) gid=1000(user) groups=1000(user)\n'; fi
STUB
chmod +x "$TEST_DIR/bin/id"

# hostname : coherent avec --machine po-2024 (le --machine prime, donc
# detect_machine n'est en realite jamais appele).
cat > "$TEST_DIR/bin/hostname" <<'STUB'
#!/usr/bin/env bash
printf 'myia-po-2024\n'
STUB
chmod +x "$TEST_DIR/bin/hostname"

# Depot fake pointant sur la fixture (le script exige <repo>/scripts/ci/docker/
# linux-runner/persist/).
DEPO_FAKE="$TEST_DIR/depo"
mkdir -p "$DEPO_FAKE/scripts/ci/docker/linux-runner"
ln -s "$TEST_DIR/persist" "$DEPO_FAKE/scripts/ci/docker/linux-runner/persist"

export SYSTEMCTL_LOG="$TEST_DIR/systemctl.log"
export INSTALL_LOG="$TEST_DIR/install.log"
: > "$SYSTEMCTL_LOG"
: > "$INSTALL_LOG"
export PATH="$TEST_DIR/bin:$PATH"
export COURSIA_REPO_DIR="$DEPO_FAKE"

# Copie hermetique : les trois racines absolues sont redirigees sous $TEST_DIR.
make_iso() {
  sed -e "s#/etc/systemd/system#$TEST_DIR/root/etc/systemd/system#g" \
      -e "s#/etc/docker#$TEST_DIR/root/etc/docker#g" \
      -e "s#/usr/local/bin#$TEST_DIR/root/usr/local/bin#g" \
      "$TARGET_SCRIPT" > "$1"
  chmod +x "$1"
}
make_iso "$TEST_DIR/iso.sh"

# Copie MUTEE : la ligne de garde l.114 (celle qui contient "root requis") est
# remplacee par un `die` INCONDITIONNEL -- l'exemption dry-run est RETIREE.
# Le cas (a) doit alors echouer : c'est le controle positif.
make_iso "$TEST_DIR/iso-mutated.sh"
sed -i 's#^.*root requis.*$#die "root requis (mutation : exemption dry-run retiree)"#' "$TEST_DIR/iso-mutated.sh"

# run_case <script> <prefix> <args...> : renvoie le code de retour du script.
run_case() {
  local script="$1" prefix="$2"; shift 2
  ( rc=0; bash -e "$script" "$@" >"$prefix.out" 2>"$prefix.err" || rc=$?; echo "rc=$rc" ) >"$prefix.rc" 2>&1
  grep -m1 '^rc=' "$prefix.rc" | sed 's/rc=//'
}

echo "Test #23342 : install-coursia-units.sh -- deux modes non privilegies (id=1000)"
echo "============================================================================"

# (a) --dry-run non privilegue -> rc=0, aucune ecriture.
rc_a="$(run_case "$TEST_DIR/iso.sh" "$TEST_DIR/case_a" --machine po-2024 --dry-run)"
if [ "$rc_a" = "0" ]; then
  ok "(a) --dry-run non privilegue : rc=0 (garde l.114 shunte sur icc_DRY_RUN)"
else
  ko "(a) --dry-run non privilegue : rc=$rc_a (attendu 0)"
  sed 's/^/      /' "$TEST_DIR/case_a.err"
fi
if [ -s "$INSTALL_LOG" ]; then
  ko "(a) le dry-run a appele install(1) -- aucun site d'ecriture ne doit s'executer"
else
  ok "(a) dry-run : install(1) jamais appele"
fi
if [ -s "$SYSTEMCTL_LOG" ]; then
  ko "(a) le dry-run a appele systemctl ($(tr '\n' ',' < "$SYSTEMCTL_LOG")) -- aucun site d'ecriture ne doit s'executer"
else
  ok "(a) dry-run : systemctl jamais appele (les sites d'ecriture sont gates)"
fi

# (b) mode reel non privilegue -> rc=1, die "root requis".
rc_b="$(run_case "$TEST_DIR/iso.sh" "$TEST_DIR/case_b" --machine po-2024)"
if [ "$rc_b" = "1" ]; then
  ok "(b) mode reel non privilegue : rc=1 (root requis)"
else
  ko "(b) mode reel non privilegue : rc=$rc_b (attendu 1)"
  sed 's/^/      /' "$TEST_DIR/case_b.err"
fi
if grep -q 'root requis' "$TEST_DIR/case_b.err"; then
  ok "(b) le die 'root requis' est present (predicat de la discipline)"
else
  ko "(b) pas de die 'root requis' dans le journal"
fi

# Controle positif : la copie mutee (exemption l.114 retiree) fait ECHEC au
# cas (a) -- le test detecte bien la regression.
rc_mut="$(run_case "$TEST_DIR/iso-mutated.sh" "$TEST_DIR/case_mut" --machine po-2024 --dry-run)"
if [ "$rc_mut" != "0" ]; then
  ok "controle positif : copie mutee fait echouer le dry-run (rc=$rc_mut) -- regression detectee"
else
  ko "controle positif : la copie mutee PASSE le dry-run (rc=0) -- regression NON detectee"
fi

echo ""
echo "==="
PASS_COUNT="$(grep -c '^PASS' "$RESULTS" 2>/dev/null | tr -d '[:space:]')"
FAIL_COUNT="$(grep -c '^FAIL' "$RESULTS" 2>/dev/null | tr -d '[:space:]')"
PASS_COUNT="${PASS_COUNT:-0}"
FAIL_COUNT="${FAIL_COUNT:-0}"
echo "  $PASS_COUNT PASS / $FAIL_COUNT FAIL"
echo "==="
[ "$FAIL_COUNT" -eq 0 ]
