#!/usr/bin/env bash
# Tests de dryrun-sizing-control.sh sur FIXTURES.
#
# Ne touche AUCUNE machine reelle : pas de systemd (un faux `systemctl` est
# fabrique ici), pas de /etc, pas de redemarrage, pas de docker. Tout vit sous
# un repertoire temporaire efface a la sortie.
#
# Ce qui est teste en priorite est le mode de DEFAILLANCE : la premiere version
# du script rendait « passe » quand le budget etait illisible. Un dry-run dont
# la panne d'instrument ressemble a une approbation est pire qu'aucun dry-run.
# La moitie des cas ci-dessous verifie donc qu'il REFUSE, pas qu'il approuve.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SUT="$HERE/dryrun-sizing-control.sh"
[ -x "$SUT" ] || [ -r "$SUT" ] || { echo "introuvable : $SUT" >&2; exit 2; }

TMP="$(mktemp -d)"
SKIP=0

# --- Garde d isolation : les faux doivent GAGNER sur PATH -------------------
# Toute l isolation de ce harnais repose la-dessus. Avec un TMPDIR en forme
# Windows (C:/...), l entree PATH est inexploitable : systemctl devient absent
# et c est le VRAI chown qui est appele -- mesure sur cette suite, 61/64 au lieu
# de 64/64. Le symptome n avait alors rien qui le nomme. On ne teste pas la
# forme de TMPDIR (un proxy) mais l effet : le faux l emporte-t-il ?
mkdir -p "$TMP/_probe/bin"
printf '#!/bin/sh\nexit 0\n' > "$TMP/_probe/bin/systemctl"
chmod 0755 "$TMP/_probe/bin/systemctl"
_probe_resolved="$(PATH="$TMP/_probe/bin:$PATH" command -v systemctl 2>/dev/null || true)"
case "$_probe_resolved" in
  "$TMP"/_probe/bin/systemctl) : ;;
  *) printf 'ABANDON : les faux ne gagnent pas sur PATH.\n' >&2
     printf '  TMPDIR    = %s\n' "${TMPDIR-<non defini>}" >&2
     printf '  attendu   = %s\n' "$TMP/_probe/bin/systemctl" >&2
     printf '  resolu    = %s\n' "${_probe_resolved:-<rien>}" >&2
     printf 'Sans cette garantie la suite appelle les VRAIS binaires : le vrai\n' >&2
     printf 'chown, et systemctl absent. Elle rendrait des echecs qui ne\n' >&2
     printf 'parlent pas de ce quelle teste. Utiliser un TMPDIR POSIX.\n' >&2
     exit 2 ;;
esac
rm -rf "$TMP/_probe"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0

ok()   { PASS=$((PASS+1)); printf '  ok   %s\n' "$1"; }
skip() { SKIP=$((SKIP+1)); printf '  --   %s\n       motif : %s\n' "$1" "$2"; }
ko()   { FAIL=$((FAIL+1)); printf '  KO   %s\n' "$1"; [ -n "${2:-}" ] && printf '       %s\n' "$2"; }

# --- Fabrique de fixtures ---------------------------------------------------
# Chaque cas repart d'un arbre neuf : aucun test n'herite de l'etat d'un autre.
make_fixture() {
  FX="$TMP/fx$1"; shift
  rm -rf "$FX"
  mkdir -p "$FX/etc/systemd/system/coursia-runner.service.d" \
           "$FX/etc/systemd/system/coursia-waiters.service.d" \
           "$FX/usr/local/bin" \
           "$FX/bin"

  printf '[Unit]\nDescription=coursia runner (fixture)\n[Service]\nExecStart=/usr/local/bin/coursia-runner-start.sh 4\n' \
    > "$FX/etc/systemd/system/coursia-runner.service"
  printf '[Unit]\nDescription=coursia waiters (fixture)\n[Service]\nExecStart=/usr/local/bin/coursia-waiter-start.sh 4\n' \
    > "$FX/etc/systemd/system/coursia-waiters.service"
  printf '[Service]\nEnvironment=COURSIA_RUNNER_MEMORY=6g\nExecStart=\nExecStart=/usr/local/bin/coursia-runner-start.sh 4\n' \
    > "$FX/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
  printf '[Service]\nEnvironment=COURSIA_RUNNER_WAITER_CPUS=1\n' \
    > "$FX/etc/systemd/system/coursia-waiters.service.d/10-sizing.conf"

  {
    echo '#!/usr/bin/env bash'
    echo 'export COURSIA_RUNNER_CPU_BUDGET="${COURSIA_RUNNER_CPU_BUDGET:-8}"'
    echo 'echo fixture wrapper'
  } > "$FX/usr/local/bin/coursia-runner-start.sh"
  chmod 0755 "$FX/usr/local/bin/coursia-runner-start.sh"

  # Faux systemctl. Il lit son comportement dans l'environnement, ce qui permet
  # a chaque cas de simuler une machine differente sans reecrire le script.
  FAKE="$FX/bin/systemctl"
  {
    printf '#!/usr/bin/env bash\n'
    printf '[ -n "${FX_SYSTEMCTL_LOG:-}" ] && printf "%%s\\n" "$*" >> "$FX_SYSTEMCTL_LOG"\n'
    printf '[ "${FX_SYSTEMCTL_DEAD:-0}" = "1" ] && exit 1\n'
    printf 'cmd="$1"; shift\n'
    printf '[ "$cmd" = "daemon-reload" ] && exit 0\n'
    printf 'unit="$1"; shift\n'
    printf 'case "$cmd" in\n'
    printf '  is-active) echo active; exit 0 ;;\n'
    printf '  cat) echo "# /etc/systemd/system/$unit"; exit 0 ;;\n'
    printf '  show) : ;;\n'
    printf '  *) exit 1 ;;\n'
    printf 'esac\n'
    printf 'prop=""\n'
    printf 'while [ $# -gt 0 ]; do case "$1" in -p) prop="$2"; shift 2 ;; *) shift ;; esac; done\n'
    printf 'case "$unit:$prop" in\n'
    printf '  *:Id) echo "$unit" ;;\n'
    printf '  coursia-runner.service:ExecStart)\n'
    printf '    echo "{ path=/usr/local/bin/coursia-runner-start.sh ; argv[]=/usr/local/bin/coursia-runner-start.sh ${FX_START_N-4} ; ignore_errors=no }" ;;\n'
    printf '  coursia-waiters.service:ExecStart)\n'
    printf '    echo "{ path=/usr/local/bin/coursia-waiter-start.sh ; argv[]=/usr/local/bin/coursia-waiter-start.sh ${FX_WAIT_N-4} ; ignore_errors=no }" ;;\n'
    printf '  coursia-runner.service:Environment) echo "${FX_START_ENV-COURSIA_RUNNER_MEMORY=6g}" ;;\n'
    printf '  coursia-waiters.service:Environment) echo "${FX_WAIT_ENV-COURSIA_RUNNER_WAITER_CPUS=1}" ;;\n'
    printf '  *:ExecMainStartTimestamp) echo "Mon 2026-09-08 07:29:40 UTC" ;;\n'
    printf '  coursia-runner.service:EnvironmentFiles) echo "${FX_START_EF-}" ;;\n'
    printf '  coursia-waiters.service:EnvironmentFiles) echo "${FX_WAIT_EF-}" ;;\n'
    printf '  coursia-runner.service:DropInPaths) echo "${FX_DROPINS-}" ;;\n'
    printf '  *) echo "" ;;\n'
    printf 'esac\n'
  } > "$FAKE"
  chmod 0755 "$FAKE"

  # Faux chown. Sur Git Bash (Windows) `stat -c %U:%G` rend « MYIA:UNKNOWN »,
  # que chown refuse -- mesure faite, pas supposee. Le rollback est donc
  # execute avec ce faux, qui ENREGISTRE ce qu'on lui demande.
  # Ce que cela prouve   : le rollback DEMANDE la restauration du proprietaire
  #                        exactement tel que stat l'a releve.
  # Ce que cela ne prouve PAS : que chown reussisse ici. Sur la cible Linux il
  #                        est reel, et c'est la seule machine ou le rollback
  #                        a vocation a tourner.
  {
    printf '#!/usr/bin/env bash\n'
    printf 'printf "%%s\\n" "$1" >> "${FX_CHOWN_LOG:-/dev/null}"\n'
    printf 'exit 0\n'
  } > "$FX/bin/chown"
  chmod 0755 "$FX/bin/chown"
}

# Empreinte de l'arbre fixture : chemin + taille + sha, tries. Sert de temoin
# de NON-MUTATION -- le script n'a le droit d'ecrire que dans son bundle.
fingerprint() {
  find "$1" -type f -print0 \
    | sort -z \
    | xargs -0 sha256sum 2>/dev/null \
    | sed "s#$1##"
}

run_sut() {   # $1 = fixture, reste = arguments ; sortie combinee dans $OUTPUT
  # FX_PATH_PREFIX permet a un cas de faire gagner un faux binaire sur PATH.
  # Non defini -- le cas nominal -- PATH est rendu inchange : aucun test
  # existant ne change de comportement.
  local fx="$1"; shift
  OUTPUT="$(PATH="${FX_PATH_PREFIX:+$FX_PATH_PREFIX:}$PATH" \
            COURSIA_DRYRUN_ROOT="$fx" \
            COURSIA_DRYRUN_SYSTEMCTL="$fx/bin/systemctl" \
            COURSIA_DRYRUN_OUT="$fx/bundle" \
            bash "$SUT" "$@" 2>&1)"
  RC=$?
  return 0
}

expect_refus() {   # $1 = libelle, $2 = motif attendu dans la sortie
  if [ "$RC" -eq 0 ]; then
    ko "$1" "attendu un refus, obtenu exit 0"
  elif ! printf '%s' "$OUTPUT" | grep -q "$2"; then
    ko "$1" "refus obtenu mais sans le motif « $2 »"
  else
    ok "$1"
  fi
}

expect_succes() {   # $1 = libelle
  if [ "$RC" -ne 0 ]; then
    ko "$1" "attendu exit 0, obtenu $RC : $(printf '%s' "$OUTPUT" | tail -3)"
  else
    ok "$1"
  fi
}

echo "=== A. Validation des entrees ==="

make_fixture a
run_sut "$TMP/fxa" --slots abc
expect_refus "--slots non numerique refuse" "entier attendu"

run_sut "$TMP/fxa" --slots 0
expect_refus "--slots 0 refuse" "entier attendu"

run_sut "$TMP/fxa" --cpus -2
expect_refus "--cpus negatif refuse" "entier attendu"

run_sut "$TMP/fxa" --slots
expect_refus "--slots sans valeur refuse" "exige une valeur"

run_sut "$TMP/fxa" --slots 4
expect_refus "protocole #15095 : plusieurs slots sans attestation" "ack-one-slot"

run_sut "$TMP/fxa" --slots 4 --ack-one-slot --cpus 1
expect_succes "protocole #15095 : attestation acceptee (4x1 + 4x1 = 8 <= 8)"

echo "=== B. Sources requises : absent et illisible sont FATAUX ==="

make_fixture b
rm -f "$TMP/fxb/usr/local/bin/coursia-runner-start.sh"
run_sut "$TMP/fxb"
expect_refus "wrapper ABSENT refuse" "ABSENTE"

make_fixture c
printf '#!/usr/bin/env bash\necho pas de budget ici\n' > "$TMP/fxc/usr/local/bin/coursia-runner-start.sh"
run_sut "$TMP/fxc"
expect_refus "budget introuvable dans le wrapper : refus, jamais « passe »" "COURSIA_RUNNER_CPU_BUDGET introuvable"
# Assertion NEGATIVE : elle ne vaut que parce que les deux controles positifs
# de la section D prouvent, dans le meme harnais, que ces marqueurs PEUVENT
# s'imprimer. Sans eux elle serait verte meme si le marqueur etait mort --
# c'est exactement ce qui s'est passe jusqu'au 2026-09-08.
if printf '%s' "$OUTPUT" | grep -q -- "-> passe"; then
  ko "budget introuvable n'imprime aucun « passe »" "un verdict permissif a ete rendu malgre l'absence de budget"
else
  ok "budget introuvable n'imprime aucun « passe »"
fi

make_fixture d
run_sut "$TMP/fxd" ; SAVE_RC=$RC
FX_SYSTEMCTL_DEAD=1 run_sut "$TMP/fxd"
expect_refus "systemd injoignable refuse" "systemd injoignable"

echo "=== C. Configuration effective incomplete = FATALE ==="

make_fixture e
FX_START_ENV="COURSIA_RUNNER_CPUS=2" run_sut "$TMP/fxe"
expect_refus "memoire absente de l'Environment effectif refuse" "memoire par conteneur"

make_fixture f
FX_WAIT_N="" run_sut "$TMP/fxf"
expect_refus "waiters non denombrables refuse (sous-estimation interdite)" "Un waiter non compte"

make_fixture g
FX_START_N="zero" run_sut "$TMP/fxg"
expect_refus "slots start non denombrables refuse" "la somme du budget est fausse"

echo "=== D. Arithmetique du garde ==="

make_fixture h
run_sut "$TMP/fxh" --slots 1 --cpus 8
expect_refus "proposition au-dessus du budget refusee" "serait refusee par le garde"

make_fixture i
run_sut "$TMP/fxi" --slots 1 --cpus 2
expect_succes "proposition sous le budget acceptee (1x2 + 4x1 = 6 <= 8)"
# L'arithmetique ET le marqueur. La version precedente grepait « 16.00 / 8 »
# -- les NOMBRES -- puis s'intitulait « rendu comme REFUSE » : elle nommait un
# verdict qu'elle ne testait pas, et elle est restee verte pendant que le
# marqueur ne s'imprimait jamais.
printf '%s' "$OUTPUT" | grep -q "actuel  : TOTAL" \
  && printf '%s' "$OUTPUT" | grep -q "16.00 / 8" \
  && ok "l'arithmetique de l'etat actuel est rendue (4x3 + 4x1 = 16)" \
  || ko "l'arithmetique de l'etat actuel est rendue" "$(printf '%s' "$OUTPUT" | grep 'TOTAL' || true)"

printf '%s' "$OUTPUT" | grep -q -- "actuel  : TOTAL.*-> REFUSE" \
  && ok "CONTROLE POSITIF : le marqueur « -> REFUSE » s imprime vraiment" \
  || ko "CONTROLE POSITIF : le marqueur « -> REFUSE » s imprime vraiment" \
        "$(printf '%s' "$OUTPUT" | grep 'actuel  : TOTAL' || true)"

printf '%s' "$OUTPUT" | grep -q -- "propose : TOTAL.*-> passe" \
  && ok "CONTROLE POSITIF : le marqueur « -> passe » s imprime vraiment" \
  || ko "CONTROLE POSITIF : le marqueur « -> passe » s imprime vraiment" \
        "$(printf '%s' "$OUTPUT" | grep 'propose : TOTAL' || true)"

echo "=== E. Bundle et rollback ==="

make_fixture j
BEFORE="$(fingerprint "$TMP/fxj")"
run_sut "$TMP/fxj" --slots 1 --cpus 2
expect_succes "bundle : execution nominale"
B="$TMP/fxj/bundle"

[ -s "$B/manifest.tsv" ] && ok "manifeste ecrit" || ko "manifeste ecrit"
[ -s "$B/state-before.txt" ] && ok "etat consigne" || ko "etat consigne"
[ -s "$B/proposed/10-sizing.conf" ] && ok "drop-in propose ecrit" || ko "drop-in propose ecrit"
[ -x "$B/rollback.sh" ] && ok "rollback executable" || ko "rollback executable"

cmp -s "$TMP/fxj/etc/systemd/system/coursia-runner.service.d/10-sizing.conf" \
       "$B/live/etc/systemd/system/coursia-runner.service.d/10-sizing.conf" \
  && ok "octets de la CIBLE captures a l'identique" \
  || ko "octets de la CIBLE captures a l'identique"

grep -q 'Environment=COURSIA_RUNNER_MEMORY=6g' "$B/proposed/10-sizing.conf" \
  && ok "la memoire vivante est RECONDUITE dans le drop-in propose" \
  || ko "la memoire vivante est RECONDUITE dans le drop-in propose"
grep -q 'Environment=COURSIA_RUNNER_CPUS=2' "$B/proposed/10-sizing.conf" \
  && ok "le cap CPU propose est ecrit" || ko "le cap CPU propose est ecrit"
grep -q 'coursia-runner-start.sh 1$' "$B/proposed/10-sizing.conf" \
  && ok "le nombre de slots propose est ecrit" || ko "le nombre de slots propose est ecrit"

grep -q 'install -D -m' "$B/rollback.sh" \
  && ok "rollback d'une cible PRESENTE : reinstalle les octets" \
  || ko "rollback d'une cible PRESENTE : reinstalle les octets"
if grep -qE '^(install|rm) ' "$B/rollback.sh" \
   && [ "$(grep -cE '^(install -D|rm -f) ' "$B/rollback.sh")" -eq 1 ]; then
  ok "rollback borne a UNE cible (pas de reinstallation des preuves)"
else
  ko "rollback borne a UNE cible" "$(grep -nE '^(install|rm) ' "$B/rollback.sh" | tr '\n' ' ')"
fi
grep -q 'coursia-waiters' "$B/rollback.sh" \
  && ko "rollback ne touche pas les fichiers non modifies" "il mentionne les waiters" \
  || ok "rollback ne touche pas les fichiers non modifies"
grep -qE '^systemctl (restart|start) ' "$B/rollback.sh" \
  && ko "rollback ne redemarre rien" \
  || ok "rollback ne redemarre rien"

echo "=== F. Cible initialement ABSENTE : la restaurer, c'est la supprimer ==="

make_fixture k
rm -f "$TMP/fxk/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
rmdir "$TMP/fxk/etc/systemd/system/coursia-runner.service.d"
run_sut "$TMP/fxk" --slots 1 --cpus 2
expect_succes "cible absente : execution nominale"
RB="$TMP/fxk/bundle/rollback.sh"
# NB : la racine n est plus codee en dur ici -- le rollback vise desormais la
# racine INSPECTEE (correctif du defaut latent : sous COURSIA_DRYRUN_ROOT il
# pointait sur le vrai /etc). La verification forte est en J1/J2, qui EXECUTENT
# le rollback et constatent l effet dans la fixture.
grep -q 'rm -f ".*/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"' "$RB" \
  && ok "rollback SUPPRIME un drop-in initialement absent" \
  || ko "rollback SUPPRIME un drop-in initialement absent" "$(grep -E '^(install|rm)' "$RB" | tr '\n' ' ')"
grep -q 'install -D' "$RB" \
  && ko "rollback n'installe rien quand la cible etait absente" \
  || ok "rollback n'installe rien quand la cible etait absente"
grep -q 'rmdir' "$RB" \
  && ok "rollback retire le repertoire .d qui n'existait pas" \
  || ko "rollback retire le repertoire .d qui n'existait pas"
grep -q 'ABSENT' "$TMP/fxk/bundle/manifest.tsv" \
  && ok "le manifeste distingue ABSENT" || ko "le manifeste distingue ABSENT"

echo "=== G. Non-mutation (le temoin central) ==="

AFTER="$(fingerprint "$TMP/fxj" | grep -v '/bundle/')"
BEFORE_NOBUNDLE="$(printf '%s\n' "$BEFORE" | grep -v '/bundle/')"
if [ "$BEFORE_NOBUNDLE" = "$AFTER" ]; then
  ok "aucun fichier de la fixture modifie hors du bundle"
else
  ko "aucun fichier de la fixture modifie hors du bundle" \
     "$(diff <(printf '%s\n' "$BEFORE_NOBUNDLE") <(printf '%s\n' "$AFTER") | head -5 | tr '\n' ' ')"
fi

# Controle POSITIF du temoin : sans lui, l'egalite ci-dessus ne prouve rien --
# elle pourrait venir d'une empreinte qui ne mesure rien.
printf 'mutation deliberee\n' >> "$TMP/fxj/etc/systemd/system/coursia-runner.service"
MUTATED="$(fingerprint "$TMP/fxj" | grep -v '/bundle/')"
if [ "$MUTATED" != "$AFTER" ]; then
  ok "controle positif : le temoin VOIT une mutation quand il y en a une"
else
  ko "controle positif : le temoin VOIT une mutation" "le temoin est aveugle -- le test G ne prouve rien"
fi

echo "=== H. La source du budget : Environment effectif > defaut du wrapper ==="

# Le wrapper ecrit VAR:-8 -- « 8 SAUF si deja defini ». Un drop-in qui definit
# la variable gagne donc, sans que le wrapper change d un octet. Lire le seul
# fichier rendrait un budget faux tout en ayant l air de l avoir mesure.
make_fixture m
FX_START_ENV="COURSIA_RUNNER_MEMORY=6g COURSIA_RUNNER_CPU_BUDGET=32" \
  run_sut "$TMP/fxm" --slots 4 --ack-one-slot --cpus 3
expect_succes "budget porte par l Environment effectif (32) : 4x3+4x1=16 passe"
printf "%s" "$OUTPUT" | grep -q "Environment effectif (fait foi)" \
  && ok "la source du budget est NOMMEE dans la sortie" \
  || ko "la source du budget est NOMMEE dans la sortie"
printf "%s" "$OUTPUT" | grep -q "32" \
  && ok "l Environment effectif l emporte sur le defaut du wrapper (8)" \
  || ko "l Environment effectif l emporte sur le defaut du wrapper"

# Contre-epreuve : le MEME dimensionnement, sans la surcharge, doit etre refuse.
# Sans elle, le test ci-dessus passerait aussi si le budget n etait pas lu du tout.
make_fixture n
run_sut "$TMP/fxn" --slots 4 --ack-one-slot --cpus 3
expect_refus "controle : le meme 4x3 est REFUSE sous le defaut 8" "serait refusee"

# budget=0 signifie garde DESARME, jamais « la configuration passe ».
make_fixture o
FX_START_ENV="COURSIA_RUNNER_MEMORY=6g COURSIA_RUNNER_CPU_BUDGET=0" \
  run_sut "$TMP/fxo" --slots 1 --cpus 2
expect_succes "budget=0 : execution nominale"
printf "%s" "$OUTPUT" | grep -q "GARDE DESACTIVE" \
  && ok "budget=0 est rendu comme GARDE DESACTIVE" \
  || ko "budget=0 est rendu comme GARDE DESACTIVE"
# Meme remarque qu'en section C : negative, donc adossee aux controles
# positifs de la section D.
if printf "%s" "$OUTPUT" | grep -q -- "-> passe"; then
  ko "budget=0 n imprime jamais « passe »" "un garde desarme a ete lu comme une approbation"
else
  ok "budget=0 n imprime jamais « passe »"
fi

echo "=== I. Bornage des configurations supportees ==="
# Review coursia-1d : `systemctl show -p Environment` ne voit ni les
# EnvironmentFile ni une valeur quotee ; un drop-in lu apres la cible peut
# ecraser la proposition ; remplacer une cible qui porte d'autres directives
# les perd. Ces quatre formes doivent REFUSER -- et deux controles negatifs
# verifient que le refus ne se declenche pas sur la forme nominale.

make_fixture p
FX_START_EF="/etc/coursia/runner.env" run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "EnvironmentFile sur le runner : refus" "EnvironmentFile"

make_fixture p
FX_WAIT_EF="/etc/coursia/waiters.env" run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "EnvironmentFile sur les waiters : refus" "EnvironmentFile"

make_fixture p
FX_START_ENV='COURSIA_RUNNER_MEMORY="6 g"' run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "valeur quotee dans l Environment : refus" "valeur quotee"

make_fixture p
FX_DROPINS="/etc/systemd/system/coursia-runner.service.d/20-autre.conf" \
  run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "drop-in lu APRES la cible : refus" "lus APRES la cible"

# Controle negatif : un drop-in lu AVANT ne peut pas ecraser la proposition.
make_fixture p
FX_DROPINS="/etc/systemd/system/coursia-runner.service.d/05-base.conf" \
  run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_succes "drop-in lu AVANT la cible : pas de refus (controle negatif)"

# Une directive que la proposition ne reconduit pas doit bloquer.
make_fixture p
printf 'CPUQuota=300%%\n' \
  >> "$TMP/fxp/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "directive supplementaire dans la cible : refus" "ne reconduit pas"

# Controle negatif : la cible nominale ne porte que les trois directives.
make_fixture p
run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_succes "cible nominale : pas de refus (controle negatif)"

echo "=== J. Rollback REELLEMENT execute ==="
# La version precedente de ces tests grepait le TEXTE du rollback. Un
# detecteur se valide par ses faux negatifs, jamais par ses hits : un rollback
# syntaxiquement present peut ne rien restaurer. On l'EXECUTE donc sur une
# fixture, et on compare les octets.

# J1 -- cible PRESENTE : le rollback doit rendre les octets d'origine.
make_fixture q
TGT="$TMP/fxq/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
cp -p "$TGT" "$TMP/fxq.avant"
run_sut "$TMP/fxq" --slots 1 --cpus 2
expect_succes "rollback J1 : le controle s execute (cible PRESENTE)"
RBS="$TMP/fxq/bundle/rollback.sh"
if [ ! -r "$RBS" ]; then
  ko "rollback J1 : script genere"
else
  ok "rollback J1 : script genere"
  # Le rollback doit viser la fixture, jamais le vrai /etc de cet hote.
  if grep -q "$TMP/fxq" "$RBS"; then
    ok "rollback J1 : la destination est la racine inspectee"
  else
    ko "rollback J1 : la destination est la racine inspectee" \
       "le rollback pointe hors de la fixture -- il ecrirait sur le systeme reel"
  fi
  # On simule l application : la cible est remplacee par la proposition.
  cp "$TMP/fxq/bundle/proposed/10-sizing.conf" "$TGT"
  if cmp -s "$TMP/fxq.avant" "$TGT"; then
    ko "rollback J1 : temoin, la cible a bien change avant rollback" \
       "proposition identique a l original : le test ne prouverait rien"
  else
    ok "rollback J1 : temoin, la cible a bien change avant rollback"
  fi
  FX_CHOWN_LOG="$TMP/fxq.chown" FX_SYSTEMCTL_LOG="$TMP/fxq.systemctl" \
    PATH="$TMP/fxq/bin:$PATH" bash "$RBS" > "$TMP/fxq.rbout" 2>&1
  RBRC=$?
  [ "$RBRC" -eq 0 ] \
    && ok "rollback J1 : execution rc=0" \
    || ko "rollback J1 : execution rc=0" "rc=$RBRC : $(tail -2 "$TMP/fxq.rbout")"
  cmp -s "$TMP/fxq.avant" "$TGT" \
    && ok "rollback J1 : octets restaures a l identique" \
    || ko "rollback J1 : octets restaures a l identique"
  # Controle POSITIF du temoin : sans lui, l egalite ci-dessus pourrait venir
  # d une comparaison qui ne compare rien.
  printf 'mutation deliberee\n' >> "$TGT"
  cmp -s "$TMP/fxq.avant" "$TGT" \
    && ko "rollback J1 : controle positif, cmp detecte une divergence" \
    || ok "rollback J1 : controle positif, cmp detecte une divergence"
  # Le proprietaire releve doit etre celui que stat a rendu, pas un defaut.
  ATTENDU="$(stat -c '%U:%G' "$TMP/fxq.avant" 2>/dev/null)"
  if [ -s "$TMP/fxq.chown" ] && grep -qx "$ATTENDU" "$TMP/fxq.chown"; then
    ok "rollback J1 : le proprietaire demande est celui releve ($ATTENDU)"
  else
    ko "rollback J1 : le proprietaire demande est celui releve ($ATTENDU)" \
       "journal chown : $(cat "$TMP/fxq.chown" 2>/dev/null)"
  fi
  # Aucun redemarrage : seul daemon-reload est admis.
  if grep -qE '^(restart|start|stop|reload-or-restart) ' "$TMP/fxq.systemctl" 2>/dev/null; then
    ko "rollback J1 : ne redemarre RIEN" "$(cat "$TMP/fxq.systemctl")"
  else
    ok "rollback J1 : ne redemarre RIEN"
  fi
fi

# J2 -- cible ABSENTE : restaurer, c est SUPPRIMER, et retirer le .d cree.
make_fixture r
rm -rf "$TMP/fxr/etc/systemd/system/coursia-runner.service.d"
run_sut "$TMP/fxr" --slots 1 --cpus 2
expect_succes "rollback J2 : le controle s execute (cible ABSENTE)"
RBS2="$TMP/fxr/bundle/rollback.sh"
if [ ! -r "$RBS2" ]; then
  ko "rollback J2 : script genere"
else
  ok "rollback J2 : script genere"
  # On simule l application : le fichier et son repertoire sont crees.
  mkdir -p "$TMP/fxr/etc/systemd/system/coursia-runner.service.d"
  cp "$TMP/fxr/bundle/proposed/10-sizing.conf" \
     "$TMP/fxr/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
  FX_SYSTEMCTL_LOG="$TMP/fxr.systemctl" PATH="$TMP/fxr/bin:$PATH" \
    bash "$RBS2" > "$TMP/fxr.rbout" 2>&1
  RBRC2=$?
  [ "$RBRC2" -eq 0 ] \
    && ok "rollback J2 : execution rc=0" \
    || ko "rollback J2 : execution rc=0" "rc=$RBRC2 : $(tail -2 "$TMP/fxr.rbout")"
  [ ! -e "$TMP/fxr/etc/systemd/system/coursia-runner.service.d/10-sizing.conf" ] \
    && ok "rollback J2 : le fichier cree a ete supprime" \
    || ko "rollback J2 : le fichier cree a ete supprime"
  [ ! -d "$TMP/fxr/etc/systemd/system/coursia-runner.service.d" ] \
    && ok "rollback J2 : le repertoire .d cree a ete retire" \
    || ko "rollback J2 : le repertoire .d cree a ete retire"
fi


# --- K. Les cas concrets releves par coursia-1d sur c9f3cfcd5 ---------------
echo
echo "K. bornage des cas releves en contre-verification"

# K1. Un ExecStart dont le BINAIRE differe doit refuser. C etait le trou : le
# filtre jetait la ligne, donc « rien n est perdu » -- alors que la proposition
# remplace la liste entiere.
make_fixture p
sed -i 's|^ExecStart=/usr/local/bin/coursia-runner-start\.sh.*|ExecStart=/usr/local/bin/autre-lanceur.sh 4|' \
  "$TMP/fxp/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "K1 ExecStart a binaire different : refus" "ne reconduit pas"

# K2. Controle negatif indispensable : l ExecStart NOMINAL ne doit pas refuser,
# sinon K1 prouverait seulement que le script refuse tout.
make_fixture p
run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_succes "K2 ExecStart nominal : pas de refus (controle negatif)"

# K3. Homonyme dans une racine plus FAIBLE (/run alors que la cible est en
# /etc) : la cible le masque, il est sans effet. Ne doit PAS refuser. C'est le
# controle qui empeche de re-durcir ce refus au-dela du cas dangereux -- ma
# premiere version refusait ici, et aurait bloque une configuration saine.
make_fixture p
FX_DROPINS="/run/systemd/system/coursia-runner.service.d/10-sizing.conf" \
  run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_succes "K3 homonyme d une racine plus faible : masque, pas de refus"

# K3b. Le cas reellement dangereux : homonyme dans une racine plus FORTE
# (system.control, ou ecrit « systemctl set-property »). Il masque la cible :
# refus.
make_fixture p
FX_DROPINS="/etc/systemd/system.control/coursia-runner.service.d/10-sizing.conf" \
  run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "K3b homonyme d une racine plus forte : refus" "precedence SUPERIEURE"

# K3c. Racine inconnue au classement : non classable, donc traitee comme la
# plus forte -- l erreur va vers le refus. Sans ce test, le « *) echo 0 » ne
# serait qu une intention ecrite en commentaire.
make_fixture p
FX_DROPINS="/opt/ailleurs/coursia-runner.service.d/10-sizing.conf" \
  run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_refus "K3c homonyme en racine inconnue : refus (fail-closed)" "precedence SUPERIEURE"

# K4. Controle negatif : la cible elle-meme, rendue par DropInPaths a son propre
# chemin, reste reconnue comme soi et ne declenche rien.
make_fixture p
FX_DROPINS="/etc/systemd/system/coursia-runner.service.d/10-sizing.conf" \
  run_sut "$TMP/fxp" --slots 1 --cpus 2
expect_succes "K4 la cible se reconnait a son chemin (controle negatif)"

# K5/K6. DEUX capacites distinctes, donc DEUX conditions distinctes.
#
# La version precedente les suspendait au meme « if » : le skip K6 vivait dans
# le « else » du test de capacite symlink. Mesure du 2026-09-08, la meme suite
# sur les deux plateformes :
#   Git Bash : reussis=72 echoues=0 non-exercables=2   (K5 et K6 declares)
#   WSL      : reussis=72 echoues=1 non-exercables=0   (K6 : ZERO occurrence)
# Sur une plateforme capable de liens reels, la non-couverture ACL ne se
# degradait pas -- elle disparaissait de la sortie. La ligne finale « ils
# restent NON couverts, ce n est pas un succes » ne pouvait alors plus la
# nommer, faute de compteur. Un aveu qui s efface est pire qu un aveu bruyant.

# --- capacite 1 : « ln -s » fabrique-t-il un VRAI lien ? --------------------
_symlink_ok=0
if ln -s "$TMP/_lnsrc" "$TMP/_lndst" 2>/dev/null && [ -L "$TMP/_lndst" ]; then
  _symlink_ok=1
fi
rm -f "$TMP/_lndst" 2>/dev/null || true

if [ "$_symlink_ok" -eq 1 ]; then
  # K5a. La CIBLE est un lien. « install -D » ecrirait a travers le lien, donc
  # ailleurs ; le rollback reposerait ensuite un fichier reel la ou il y avait
  # un lien. Le fichier pointe est une copie conforme du drop-in nominal, pour
  # qu aucun autre refus ne se declenche avant celui qu on teste.
  make_fixture s1
  _T="$FX/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
  cp "$_T" "$FX/etc/systemd/system/ailleurs.conf"
  ln -sf "$FX/etc/systemd/system/ailleurs.conf" "$_T"
  run_sut "$FX" --slots 1 --cpus 2
  expect_refus "K5a la cible est un lien symbolique : refus" \
    "la cible est un LIEN SYMBOLIQUE"

  # K5b. Le REPERTOIRE .d est un lien, et la cible dedans est un fichier reel :
  # « [ -L cible ] » est donc FAUX ici, et c est le SECOND garde qui doit
  # mordre. Sans ce cas, un seul des deux refus serait exerce.
  make_fixture s2
  _D="$FX/etc/systemd/system/coursia-runner.service.d"
  mkdir -p "$FX/etc/systemd/system/reel.d"
  cp "$_D/10-sizing.conf" "$FX/etc/systemd/system/reel.d/10-sizing.conf"
  rm -rf "$_D"
  ln -s "$FX/etc/systemd/system/reel.d" "$_D"
  run_sut "$FX" --slots 1 --cpus 2
  expect_refus "K5b le repertoire .d est un lien symbolique : refus" \
    "repertoire .d de la cible est un LIEN SYMBOLIQUE"
else
  skip "K5 refus symlink (cible et repertoire .d)" \
    "ln -s rend une copie sur cette plateforme : [ -L ] faux, refus jamais atteint"
fi

# --- capacite 2 : sait-on poser une ACL etendue VISIBLE dans « ls -ld » ? ---
# La capacite se mesure par son EFFET -- le « + » apparait-il ? -- pas par la
# presence de setfacl : un setfacl present mais inoperant sur le systeme de
# fichiers du scratch rendrait un test vert sans rien exercer.
_acl_ok=0
if command -v setfacl >/dev/null 2>&1; then
  mkdir -p "$TMP/_aclprobe"
  if setfacl -m "u:$(id -un):rwx" "$TMP/_aclprobe" 2>/dev/null \
     && ls -ld "$TMP/_aclprobe" | cut -c1-11 | grep -q '+'; then
    _acl_ok=1
  fi
  rm -rf "$TMP/_aclprobe"
fi

if [ "$_acl_ok" -eq 1 ]; then
  # K6a. Le cas fort : une ACL etendue REELLE posee sur la cible.
  make_fixture a1
  _T="$FX/etc/systemd/system/coursia-runner.service.d/10-sizing.conf"
  setfacl -m "u:$(id -un):rwx" "$_T"
  run_sut "$FX" --slots 1 --cpus 2
  expect_refus "K6a cible portant une ACL etendue REELLE : refus" "ACL etendues"
else
  skip "K6a refus sur ACL etendue REELLE" \
    "aucune ACL etendue posable ici (setfacl absent, ou sans effet sur ce FS) : le « + » de ls -ld ne serait jamais produit"
fi

# K6b/K6c. Exercables PARTOUT, parce qu ils ne demandent aucune ACL : un faux
# « ls » fournit la ligne de mode. « ls » n est appele qu a UN endroit du
# script de controle -- le test ACL lui-meme -- donc le faux est chirurgical.
#
# Ce que ces deux cas prouvent  : le predicat « *+ » est bien branche sur un
#   « die », et il ne mord QUE sur le « + ».
# Ce qu ils ne prouvent PAS     : que « ls -ld » rende un « + » face a une
#   vraie ACL. Cela, seul K6a le montre -- d ou son skip explicite ci-dessus.
#
# K6c est indispensable : un script qui refuserait TOUJOURS passerait K6b sans
# rien prouver. C est le defaut du marqueur printf sous une autre forme -- une
# assertion qui ne peut pas echouer n atteste rien.
make_fixture a2
{ echo '#!/usr/bin/env bash'
  echo 'echo "-rw-r--r--+ 1 u g 42 Jan  1 00:00 cible"'
} > "$FX/bin/ls"
chmod 0755 "$FX/bin/ls"
FX_PATH_PREFIX="$FX/bin" run_sut "$FX" --slots 1 --cpus 2
expect_refus "K6b le « + » de ls -ld declenche le refus" "ACL etendues"

make_fixture a3
{ echo '#!/usr/bin/env bash'
  echo 'echo "-rw-r--r--  1 u g 42 Jan  1 00:00 cible"'
} > "$FX/bin/ls"
chmod 0755 "$FX/bin/ls"
FX_PATH_PREFIX="$FX/bin" run_sut "$FX" --slots 1 --cpus 2
expect_succes "K6c CONTROLE NEGATIF : sans « + », le meme faux ls ne refuse rien"
echo
printf 'reussis=%d  echoues=%d  non-exercables=%d\n' "$PASS" "$FAIL" "$SKIP"
[ "$FAIL" -eq 0 ] || exit 1
echo "TOUS LES TESTS PASSENT -- aucune machine reelle touchee, aucun redemarrage."
[ "$SKIP" -eq 0 ] || printf '(%d refus non exercables sur cette plateforme, motifs ci-dessus :\n ils restent NON couverts, ce n est pas un succes.)\n' "$SKIP"
