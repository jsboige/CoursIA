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
# chaque stub se resout bien au dossier du banc. Si l'un des deux ne s'y resout
# pas, le banc s'arrete AVANT tout scenario (exit 1) : un scenario lance sans son
# stub peut invoquer le vrai WSL ou attendre reellement. Un temoin de garde (en
# fin de banc) rejoue le banc mute pour prouver cet arret.

set -o pipefail
set -o nounset

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/pool-logon-test-$$"
mkdir -p "$TEST_DIR/bin"
# Le nettoyage est attache a la sortie : un arret anticipe (transformation
# introuvable) ne laisse rien dans /tmp.
nettoyer() {
  find "$TEST_DIR" -type f -delete 2>/dev/null
  find "$TEST_DIR" -depth -type d -empty -delete 2>/dev/null
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
# aucune trace. C'est la SEULE fonction qui lance le lanceur : le temoin de garde
# la remplace, dans le banc mute, par un marqueur.
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
# (le lanceur s'est termine sans attendre). Le cas 2 n'est lu que derriere la
# garde : un stub non resolu a deja arrete le banc.
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
cas() {
  ecart "$2" "$3" "$4"; local code=$?
  if [ "$code" = 0 ]; then
    ok "$1"
  elif [ "$code" = 2 ]; then
    ko "$1 -- la trace d'appels est absente"
  else
    ko "$1 -- $(describe "$2" "$3" "$4")"
  fi
}

# controle <libelle> <appels> <pauses> <rc> : la mesure courante doit DIFFERER de
# ces valeurs (lanceur casse). Un banc qui ne voit pas un lanceur casse ne prouve rien.
controle() {
  ecart "$2" "$3" "$4"; local code=$?
  if [ "$code" = 2 ]; then
    ok "controle negatif vu : $1 -- $(describe "$2" "$3" "$4"), aucun appel du stub"
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
# verdict du temoin dans un fichier, lu par la garde qui suit.
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

# Un echec du temoin interdit toute execution du lanceur, meme simule : la garde
# precede le premier appel de `mesure`. Le temoin de garde (fin de banc) prouve
# qu'elle arrete bien avant tout scenario.
if ! grep -qx wsl.exe "$SIMULATION_VUE" || ! grep -qx sleep "$SIMULATION_VUE"; then
  echo "Banc invalide : scenarios non executes, resolution des stubs incorrecte" >&2
  exit 1
fi

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

# --- Temoin de la garde -------------------------------------------------------
# Le temoin rejoue le banc LUI-MEME, mute par sed comme l'est le lanceur :
#   absent   : UN stub est renomme juste apres sa creation ; il ne se resout plus
#              au dossier du banc, l'autre si ;
#   mesure   : la fonction ne lance plus rien -- elle pose un marqueur et sort
#              (code 42). Le vrai wsl.exe n'est donc jamais a portee du mutant,
#              et le `command -v` du temoin CHERCHE un binaire sans l'appeler ;
#   temoin   : la section presente est retiree (le mutant ne se rejoue pas) ;
#   garde    : pour le controle, le bloc de garde est retire.
# Avec la garde, le mutant s'arrete (code 1) sans poser le marqueur ; sans la
# garde, il le pose. Sans ce controle, un temoin qui ne verrait jamais de
# scenario passerait tout seul.
BANC="$SCRIPT_DIR/$(basename -- "$0")"
[ -r "$BANC" ] || { echo "banc introuvable ($0) : le temoin de garde lit son propre fichier"; exit 1; }
GARDE="$TEST_DIR/garde"
mkdir -p "$GARDE"

# muter <nom> <stub absent> <avec|sans> : ecrit le banc mute dans $GARDE/<nom>.sh.
# Chaque mutation doit porter. La presence de la garde ne s'y verifie PAS : c'est
# le verdict qui la dit.
muter() {
  local cible="$GARDE/$1.sh" sedscript="$GARDE/$1.sed"
  cat > "$sedscript" <<MUTATION
s|^SCRIPT_DIR=.*|SCRIPT_DIR="$SCRIPT_DIR"|
s|^chmod +x "\$TEST_DIR/bin/wsl.exe" "\$TEST_DIR/bin/sleep"$|&; mv "\$TEST_DIR/bin/$2" "\$TEST_DIR/bin/$2.absent"|
s|^mesure() {\$|mesure() {\n  : > "\$MARQUEUR"; exit 42|
/^# --- Temoin de la garde/,/^# --- fin du temoin de la garde/d
MUTATION
  if [ "$3" = sans ]; then
    echo '/^# Un echec du temoin interdit/,/^fi$/d' >> "$sedscript"
  fi
  sed -f "$sedscript" "$BANC" > "$cible"
  [ "$(grep -c -- "bin/$2.absent" "$cible")" = 1 ] || { echo "mutation du stub manquante ($1)"; exit 1; }
  [ "$(grep -c 'exit 42' "$cible")" = 1 ] || { echo "mutation de mesure manquante ($1)"; exit 1; }
  [ "$(grep -c 'Temoin de la garde' "$cible")" = 0 ] || { echo "mutation du temoin manquante ($1)"; exit 1; }
  [ "$(grep -cF "SCRIPT_DIR=\"$SCRIPT_DIR\"" "$cible")" = 1 ] || { echo "mutation de SCRIPT_DIR manquante ($1)"; exit 1; }
  if [ "$3" = sans ]; then
    [ "$(grep -c 'Banc invalide' "$cible")" = 0 ] || { echo "garde encore la ($1)"; exit 1; }
  fi
}

# joue <nom> <stub absent> <avec|sans> : execute le mutant et rend 0 s'il s'est
# comporte comme attendu. Chaque comparaison porte sur sa propre ligne.
joue() {
  local marqueur="$GARDE/$1.marqueur" rc
  MARQUEUR="$marqueur" bash "$GARDE/$1.sh" > "$GARDE/$1.out" 2> "$GARDE/$1.err"
  rc=$?
  grep -q "FAIL: temoin : $2 se resout" "$GARDE/$1.out" || return 1
  if [ "$3" = avec ]; then
    [ "$rc" = 1 ] || return 1
    grep -q 'Banc invalide' "$GARDE/$1.err" || return 1
    [ ! -e "$marqueur" ] || return 1
    ! grep -q 'gestionnaire present' "$GARDE/$1.out" || return 1
  else
    [ "$rc" = 42 ] || return 1
    [ -e "$marqueur" ] || return 1
  fi
  return 0
}

for stub in wsl.exe sleep; do
  muter "avec-$stub" "$stub" avec
  muter "sans-$stub" "$stub" sans
  if joue "avec-$stub" "$stub" avec; then
    ok "temoin de la garde : $stub non resolu -- arret avant tout scenario"
  else
    ko "temoin de la garde : $stub non resolu -- $(tr '\n' '|' < "$GARDE/avec-$stub.out")$(tr '\n' '|' < "$GARDE/avec-$stub.err")"
  fi
  if joue "sans-$stub" "$stub" sans; then
    ok "controle negatif vu : sans la garde, $stub non resolu lance un scenario"
  else
    ko "controle negatif NON vu : sans la garde, $stub non resolu -- $(tr '\n' '|' < "$GARDE/sans-$stub.out")$(tr '\n' '|' < "$GARDE/sans-$stub.err")"
  fi
done
# --- fin du temoin de la garde ---

PASSES=$(grep -c '^PASS ' "$RESULTS")
FAILS=$(grep -c '^FAIL ' "$RESULTS")
echo
echo "== $PASSES PASS / $FAILS FAIL =="
[ "$FAILS" -eq 0 ]
