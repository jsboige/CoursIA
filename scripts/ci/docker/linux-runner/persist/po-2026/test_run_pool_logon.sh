#!/usr/bin/env bash
# Banc de l'attente du gestionnaire utilisateur dans run-pool-po2026.sh (#22937).
# On execute le VRAI lanceur, sa ligne de lancement du pool remplacee par un
# marqueur, avec des stubs `wsl.exe` et `sleep` en tete de PATH : le pool reel
# n'est jamais atteint et le banc dure moins d'une seconde.
#
# Ce que le banc doit separer : « attend puis lance », « lance sans attendre » et
# « attend sans borne » rendent tous rc=0 quand le gestionnaire repond. Seuls le
# nombre d'appels du stub, le nombre de pauses et le marqueur de lancement
# discriminent -- et ils vivent dans un FICHIER, pas dans une variable shell
# (cf. test_pool_mint.sh : chaque appel du stub est un processus).
#
# Chaque comparaison porte sur sa propre ligne. Un jugement en chaine `A && B || C`
# a marque ECART les cas reussis (mesure du 2026-11-25). Un controle negatif est
# un ecart ATTENDU : il ne compte pas comme un echec du banc.
#
# Piege de forme : une entree de PATH ecrite `C:/...` n'est pas resolue par la
# recherche de binaire de Git Bash ; le stub serait saute au profit du vrai
# wsl.exe. Le banc n'utilise donc que des chemins POSIX, et un temoin verifie que
# chaque stub se resout bien en tete de PATH : sans lui, INVALIDE.

set -o pipefail
set -o nounset

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/pool-logon-test-$$"
mkdir -p "$TEST_DIR/bin"
# Le nettoyage est attache a la sortie : un arret anticipe (transformation
# introuvable) ne laisse rien dans /tmp.
nettoyer() {
  find "$TEST_DIR" -type f -delete 2>/dev/null
  rmdir "$TEST_DIR/bin" "$TEST_DIR" 2>/dev/null
}
trap nettoyer EXIT

# --- Stub wsl.exe -------------------------------------------------------------
# SIM_LOG trace chaque appel, SIM_COUNT les compte, SIM_FAILS fixe le nombre de
# premiers appels en echec (100000 = le gestionnaire ne repond jamais).
cat > "$TEST_DIR/bin/wsl.exe" <<'STUB'
#!/usr/bin/env bash
echo "appel" >> "$SIM_LOG"
n=$(cat "$SIM_COUNT" 2>/dev/null || echo 0)
n=$((n + 1))
echo "$n" > "$SIM_COUNT"
[ "$n" -le "$SIM_FAILS" ] && exit 1
echo "STUB-VERSION"
exit 0
STUB
# --- Stub sleep : aucune attente reelle, la pause est tracee -----------------
cat > "$TEST_DIR/bin/sleep" <<'STUB'
#!/usr/bin/env bash
echo "pause $1" >> "$SIM_LOG"
STUB
chmod +x "$TEST_DIR/bin/wsl.exe" "$TEST_DIR/bin/sleep"

# Verdict dans un FICHIER (cf. test_pool_mint.sh) : un `ko` doit faire sortir
# non-zero, sinon le harnais est vert a jamais.
RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# Copies du lanceur. Chaque transformation doit porter exactement une fois.
#   marqueur      : la ligne de lancement du pool devient un echo (une ligne).
#   sans_attente  : le bloc d'attente est retire (comportement d'avant).
#   borne_mutee   : la borne passe de 60 a 3 essais.
avec_marqueur() { # $1 = source, $2 = copie
  sed 's|^exec wsl.exe .*|echo LANCEMENT-POOL-ATTEINT; exit 0|' "$1" > "$2"
  [ "$(grep -c '^echo LANCEMENT-POOL-ATTEINT' "$2")" = 1 ] \
    || { echo "ligne de lancement introuvable dans $1"; exit 1; }
}
sans_attente() { # $1 = source, $2 = copie
  sed '/^attempt=0$/,/^done$/d' "$1" > "$2"
  if [ "$(grep -c '^attempt=0$' "$2")" != 0 ] || [ "$(grep -c '^done$' "$2")" != 0 ]; then
    echo "bloc d'attente introuvable dans $1"
    exit 1
  fi
}
borne_mutee() { # $1 = source, $2 = copie
  sed 's/-ge 60 \]/-ge 3 ]/' "$1" > "$2"
  [ "$(grep -c -- '-ge 3 ]' "$2")" = 1 ] || { echo "borne introuvable dans $1"; exit 1; }
}

avec_marqueur "$SCRIPT_DIR/run-pool-po2026.sh" "$TEST_DIR/lanceur.sh"
sans_attente "$TEST_DIR/lanceur.sh" "$TEST_DIR/lanceur-sans-attente.sh"
borne_mutee "$TEST_DIR/lanceur.sh" "$TEST_DIR/lanceur-borne-mutee.sh"

# mesure <nom> <lanceur> <echecs> : execute le lanceur, remplit MESURE_*.
# Les compteurs se lisent dans le FICHIER de trace : un stub non appele ne laisse
# aucune trace, et c'est le signe distinctif de l'INVALIDE.
mesure() {
  MESURE_LOG="$TEST_DIR/$1.log"
  MESURE_OUT="$TEST_DIR/$1.out"
  SIM_LOG="$MESURE_LOG" SIM_COUNT="$TEST_DIR/$1.count" SIM_FAILS="$3" \
    PATH="$TEST_DIR/bin:$PATH" bash "$2" > "$MESURE_OUT" 2> "$TEST_DIR/$1.err"
  MESURE_RC=$?
  MESURE_APPELS=0
  MESURE_PAUSES=0
  [ -f "$MESURE_LOG" ] && { MESURE_APPELS=$(grep -c '^appel$' "$MESURE_LOG"); MESURE_PAUSES=$(grep -c '^pause ' "$MESURE_LOG"); }
}

# ecart <appels> <pauses> <rc> : rend 0 si la mesure courante concorde, 1 si elle
# est en ecart, 2 si elle est en ecart SANS qu'aucun appel du stub n'ait eu lieu
# (le lanceur s'est termine sans attendre). Le cas 2 n'est un INVALIDE que si le
# temoin de PATH a echoue : c'est lui, pas la mesure, qui dit si la simulation a
# pu s'exercer.
ecart() {
  if [ "$1" -gt 0 ] && [ ! -f "$MESURE_LOG" ]; then
    return 2
  fi
  [ "$MESURE_RC" = "$3" ] || return 1
  [ "$MESURE_APPELS" = "$1" ] || return 1
  [ "$MESURE_PAUSES" = "$2" ] || return 1
  if [ "$3" = 0 ]; then
    grep -q '^LANCEMENT-POOL-ATTEINT$' "$MESURE_OUT" || return 1
  fi
  return 0
}

describe() { # $1 = appels, $2 = pauses, $3 = rc attendus
  echo "rc=$MESURE_RC (attendu $3), appels=$MESURE_APPELS (attendu $1), pauses=$MESURE_PAUSES (attendu $2)"
}

# cas <libelle> <appels> <pauses> <rc> : la mesure courante DOIT concorder.
# Un ecart sans appel du stub n'est une mesure que si le temoin de PATH a passe.
invalide() { # $1 = libelle de l'ecart
  if grep -qx wsl.exe "$SIMULATION_VUE"; then
    ko "$1 -- la trace d'appels est absente"
  else
    ko "$1 -- INVALIDE : le stub wsl.exe n'est pas en tete de PATH (voir le temoin)"
  fi
}
cas() {
  ecart "$2" "$3" "$4"; local code=$?
  if [ "$code" = 0 ]; then
    ok "$1"
  elif [ "$code" = 2 ]; then
    invalide "$1"
  else
    ko "$1 -- $(describe "$2" "$3" "$4")"
  fi
}

# controle <libelle> <appels> <pauses> <rc> : la mesure courante doit DIFFERER de
# ces valeurs (lanceur casse). Un banc qui ne voit pas un lanceur casse ne prouve rien.
controle() {
  ecart "$2" "$3" "$4"; local code=$?
  if [ "$code" = 2 ]; then
    if grep -qx wsl.exe "$SIMULATION_VUE"; then
      ok "controle negatif vu : $1 -- $(describe "$2" "$3" "$4"), aucun appel du stub"
    else
      ko "controle negatif INVALIDE : stub wsl.exe hors PATH ($1)"
    fi
  elif [ "$code" = 0 ]; then
    ko "controle negatif NON vu : $1"
  else
    ok "controle negatif vu : $1 -- $(describe "$2" "$3" "$4")"
  fi
}

echo "== banc de l'attente du gestionnaire utilisateur (run-pool-po2026.sh) =="

# Temoin de simulation : sous le PATH du banc, wsl.exe et sleep DOIVENT se resoudre
# aux stubs. Sans lui, un PATH non resolu (entree `C:/...` : voir en tete) fait
# passer le vrai wsl.exe pour un lanceur silencieux. SIMULATION_VUE porte le
# verdict du temoin dans un fichier, lu par les cas.
SIMULATION_VUE="$TEST_DIR/simulation-vue"
: > "$SIMULATION_VUE"
for stub in wsl.exe sleep; do
  resolu="$(export PATH="$TEST_DIR/bin:$PATH"; command -v "$stub")"
  if [ "$resolu" = "$TEST_DIR/bin/$stub" ]; then
    ok "temoin : $stub se resout au stub du banc"
    echo "$stub" >> "$SIMULATION_VUE"
  else
    ko "temoin : $stub se resout a '${resolu:-inconnu}' au lieu de $TEST_DIR/bin/$stub"
  fi
done

mesure present "$TEST_DIR/lanceur.sh" 0
cas "gestionnaire present : 1 appel, 0 pause, lancement" 1 0 0

mesure deux-echecs "$TEST_DIR/lanceur.sh" 2
cas "deux echecs puis reponse : 3 appels, 2 pauses, lancement" 3 2 0
# Ordre et contenu de la trace : appel et pause alternent, la pause vaut 5 s.
printf 'appel\npause 5\nappel\npause 5\nappel\n' > "$TEST_DIR/trace-attendue"
if diff "$TEST_DIR/trace-attendue" "$TEST_DIR/deux-echecs.log" > "$TEST_DIR/trace.diff"; then
  ok "trace du cas « deux echecs » : appel et pause de 5 s alternent"
else
  ko "trace du cas « deux echecs » : $(tr '\n' '|' < "$TEST_DIR/trace.diff")"
fi

mesure jamais-la "$TEST_DIR/lanceur.sh" 100000
cas "gestionnaire jamais la : 60 appels, 59 pauses, exit 1" 60 59 1
if grep -q 'absent apres' "$TEST_DIR/jamais-la.err"; then
  ok "echec borne : message sur stderr"
else
  ko "echec borne : message absent de stderr"
fi

mesure sans-attente "$TEST_DIR/lanceur-sans-attente.sh" 100000
controle "bloc d'attente supprime" 60 59 1

mesure borne-mutee "$TEST_DIR/lanceur-borne-mutee.sh" 100000
controle "borne mutee a 3 essais" 60 59 1

PASSES=$(grep -c '^PASS ' "$RESULTS")
FAILS=$(grep -c '^FAIL ' "$RESULTS")
echo
echo "== $PASSES PASS / $FAILS FAIL =="
[ "$FAILS" -eq 0 ]
