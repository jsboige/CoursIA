#!/usr/bin/env bash
# Tests du bloc PIP_USER de entrypoint.sh (isolation des installs pip par
# job, #22502 : le volume toolcache partage servait de site-packages a tous
# les jobs, deux pip concurrents y corrompaient des paquets -- pygments a
# 0 octet, ImportError retombes sur la PR mesuree, instance #22281).
#
# Methode : on extrait le bloc REEL du script sous test (marqueurs de
# section) et on verifie, sans stub :
#   1. que le bloc exporte PIP_USER=1 et prefixe PATH de ~/.local/bin ;
#   2. (controle mecanisme, Linux non-root) qu'un pip sous ce regime installe
#      un paquet DANS la base utilisateur (preuve par existence du paquet),
#      la ou le meme pip SANS la redirection echoue sur l'arbre systeme.
# Le paquet installe est fabrique localement (pyproject minimal) : zero
# reseau, garanti absent de tout site-packages preexistant.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/entrypoint-pipuser-test-$$"
mkdir -p "$TEST_DIR"
LOG="$TEST_DIR/test.log"
: > "$LOG"

RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

cleanup() { rm -rf "$TEST_DIR"; }
trap cleanup EXIT

# --- 1. Extraction du bloc reel ------------------------------------------
if ! sed -n '/# --- Isolation des installs pip par job/,/# TEST-ENTRYPOINT-PIP-USER-END/p' \
     "$SCRIPT_DIR/entrypoint.sh" > "$TEST_DIR/block.sh" || \
   ! grep -q 'export PIP_USER=1' "$TEST_DIR/block.sh"; then
  echo "FAIL extraction du bloc PIP_USER de entrypoint.sh" >&2
  exit 1
fi

# --- 2. Effet d'environnement du bloc -------------------------------------
(
  unset PIP_USER || true
  HOME="$TEST_DIR/home"
  export HOME
  mkdir -p "$HOME"
  # shellcheck disable=SC1091
  . "$TEST_DIR/block.sh"
  [ "$PIP_USER" = "1" ] || exit 10
  case ":$PATH:" in
    *":$HOME/.local/bin:"*) ;;
    *) exit 11 ;;
  esac
  exit 0
) >> "$LOG" 2>&1
rc=$?
if [ "$rc" -eq 0 ]; then
  ok "le bloc exporte PIP_USER=1 et prefixe PATH de ~/.local/bin"
else
  ko "effet d'environnement du bloc (rc=$rc)"
fi

# --- 3. Controle mecanisme : redirection verifiable, non-root, Linux ------
# Interpretation cible : le python SYSTEME (site-packages non inscriptible
# pour un utilisateur ordinaire -- le role du toolcache partage). Un paquet
# local garant absent est installe deux fois :
#   (a) sous le regime du bloc (PIP_USER=1 + PYTHONUSERBASE confine) :
#       reussite ET presence dans la base utilisateur ;
#   (b) sans la redirection (PIP_USER=0) : echec -- l'ecriture vise l'arbre
#       systeme.
# (b) prouve que la reussite de (a) vient de la redirection, pas d'un
# site-packages qui serait resté inscriptible.
if [ "$(id -u)" -eq 0 ] || [ "$(uname -s)" != "Linux" ]; then
  echo "  SKIP: controle mecanisme (requiert Linux non-root)"
  echo "SKIP mecanisme (non-Linux ou root)" >> "$RESULTS"
elif ! SETUPTOOLS_DIR=$(python3 -c "import setuptools, os; print(os.path.dirname(os.path.dirname(setuptools.__file__)))" 2>/dev/null) || [ -z "$SETUPTOOLS_DIR" ]; then
  # Le paquet fixture se construit sans reseau (--no-build-isolation) :
  # setuptools introuvable => le controle ne peut pas tourner.
  echo "  SKIP: controle mecanisme (setuptools introuvable)"
  echo "SKIP mecanisme (setuptools absent)" >> "$RESULTS"
else
  PY=python3

  PKGDIR="$TEST_DIR/pipusertest"
  mkdir -p "$PKGDIR/pipusertest"
  cat > "$PKGDIR/pyproject.toml" <<'EOF'
[build-system]
requires = ["setuptools>=40.8"]
build-backend = "setuptools.build_meta"
[project]
name = "pipusertest"
version = "0.1"
EOF
  printf 'VALUE = 42\n' > "$PKGDIR/pipusertest/__init__.py"

  USERBASE="$TEST_DIR/userbase"
  PIP_FLAGS="--quiet --no-cache-dir --disable-pip-version-check --no-build-isolation"
  # PIP_BREAK_SYSTEM_PACKAGES=1 reproduit l'ENV du Dockerfile du runner : le
  # test juge la redirection PIP_USER, pas la garde PEP 668 de l'hote (sans
  # ce drapeau, un python externally-managed ferait echouer (a) pour une
  # raison etrangere au mecanisme teste).
  PIPENV="PIP_BREAK_SYSTEM_PACKAGES=1"
  # Le backend de build vit la ou setuptools est installe -- souvent le
  # user-site (le toolcache des runners coursia EST un user-site). Comme le
  # controle redirige PYTHONUSERBASE vers une base vide, ce backend
  # deviendrait introuvable et (a) echouerait sur un mecanisme sain. On le
  # re-expose par PYTHONPATH, qui ne change que la resolution d'import, pas
  # la destination d'installation mesuree par (a)/(b).
  BACKEND_PATH="PYTHONPATH=$SETUPTOOLS_DIR"

  if env $PIPENV $BACKEND_PATH PIP_USER=1 PYTHONUSERBASE="$USERBASE" "$PY" -m pip install $PIP_FLAGS "$PKGDIR" >/dev/null 2>"$TEST_DIR/err_a.log"; then
    if [ -n "$(find "$USERBASE" -maxdepth 8 -name 'pipusertest*' -print -quit 2>/dev/null)" ] \
       && PYTHONUSERBASE="$USERBASE" "$PY" -c "import pipusertest, sys; sys.exit(0 if pipusertest.VALUE == 42 else 1)" 2>>"$TEST_DIR/err_a.log"; then
      ok "sous PIP_USER=1, l'install atterrit dans la base utilisateur et l'import y lit le paquet"
    else
      ko "install reussie mais paquet absent de la base utilisateur ou import muet"
    fi
  else
    ko "install sous PIP_USER=1 a echoue (voir $TEST_DIR/err_a.log)"
  fi

  # (b) recoit le meme backend : sans lui, l'echec viendrait d'un
  # BackendUnavailable et non de l'arbre systeme non inscriptible -- un
  # PASS faux, qui prouverait l'inverse de ce que le controle affirme.
  if env $PIPENV $BACKEND_PATH PIP_USER=0 "$PY" -m pip install $PIP_FLAGS --force-reinstall "$PKGDIR" >/dev/null 2>"$TEST_DIR/err_b.log"; then
    ko "install SANS redirection a reussi vers l'arbre systeme -- le controle ne prouve rien (site inscriptible ?)"
  else
    ok "sans redirection, l'ecriture vise l'arbre systeme et echoue (non-root)"
  fi
fi

# --- Bilan -----------------------------------------------------------------
if grep -q '^FAIL' "$RESULTS"; then
  echo "entrypoint pip-user: AU MOINS UN FAIL"
  exit 1
fi
echo "entrypoint pip-user: OK ($(grep -c '^PASS' "$RESULTS") PASS)"
