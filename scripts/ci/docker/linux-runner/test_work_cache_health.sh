#!/usr/bin/env bash
# Tests de sante du cache _work (#15105), par observation directe du
# comportement sur des fixtures git REELLES (pas de stub : les semantiques
# testees -- warning stderr, rc=0, marqueurs .promisor -- sont celles de git
# lui-meme, mesurees sur 2.43, la version de l'image ubuntu:24.04 de la
# flotte).
#
# L'acceptance de #15105 exige que le detecteur soit « valide par ses faux
# negatifs, pas par ses hits » : chaque garde a donc son controle NEGATIF
# (ce que l'organe ne doit PAS faire) a cote de son controle positif.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

TEST_DIR="$(mktemp -d /tmp/wch-test-XXXXXX)"
LOG="$TEST_DIR/test.log"
: > "$LOG"

# Verdict tenu dans un fichier (pattern test_supervise_guards.sh : un
# compteur shell dans un sous-shell ( ... ) n'est jamais vu du parent).
RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# shellcheck disable=SC1091
. "$SCRIPT_DIR/work_cache_health.sh"

# --- Fixture : depot source avec historique, et clone --no-local -----------
# Le --no-local force le transport (pas de hardlinks) : chaque fetch ecrit
# un pack distinct, exactement le mecanisme d'accumulation de la flotte
# (mesure #15105 : 1 pack promisor par job).
mk_source() {
  local src="$1" i
  git init -q --bare "$src"
  # allowFilter : sans lui le file:// ignore --filter et le clone n'est PAS
  # partiel -- or la flotte l'est (blob:none), et c'est ce qui fait qu'un
  # fetch ecrit un PACK promisor (un clone complet ecrit des objets meubles
  # pour les petits lots : le fixture ne reproduirait pas l'accumulation).
  git -C "$src" config uploadpack.allowFilter true
  git init -q "$TEST_DIR/seed"
  git -C "$TEST_DIR/seed" config user.email t@t
  git -C "$TEST_DIR/seed" config user.name t
  for i in 1 2 3; do
    head -c 1024 /dev/urandom | base64 > "$TEST_DIR/seed/f$i.txt"
    git -C "$TEST_DIR/seed" add .
    git -C "$TEST_DIR/seed" commit -qm "c$i"
  done
  git -C "$TEST_DIR/seed" push -q "$src" HEAD:main
}

add_commit_and_fetch() {
  local src="$1" dst="$2" i="$3"
  head -c 512 /dev/urandom | base64 > "$TEST_DIR/seed/g$i.txt"
  git -C "$TEST_DIR/seed" add .
  git -C "$TEST_DIR/seed" commit -qm "g$i"
  git -C "$TEST_DIR/seed" push -q "$src" HEAD:main
  git -C "$dst" fetch -q origin 2>/dev/null
}

echo "Test 1 : depot sain -- le detecteur VOIT les refs (controle positif du faux negatif « 0 refs saines »)"
(
  R="$TEST_DIR/healthy"
  git init -q -b main "$R"
  git -C "$R" config user.email t@t; git -C "$R" config user.name t
  echo x > "$R/f"; git -C "$R" add .; git -C "$R" commit -qm x
  nrefs="$(wch_ref_count "$R")"
  if [ "$nrefs" -gt 0 ]; then
    ok "un depot sain rend $nrefs refs lisibles (jamais 0)"
  else
    ko "0 refs sur un depot sain -- le faux negatif ownership/lecture est DE retour"
  fi
  out="$(wch_integrity_pass "$R")"
  if [ -d "$R" ] && [ -n "$(ls -A "$R" 2>/dev/null)" ]; then
    ok "depot sain conserve (aucune purge intempestive)"
  else
    ko "un depot sain a ete purge -- regression"
  fi
)
echo ""

echo "Test 2 : refs cassees -- le canal est STDERR, le rc est 0"
(
  R="$TEST_DIR/broken"
  git init -q -b main "$R"
  git -C "$R" config user.email t@t; git -C "$R" config user.name t
  echo x > "$R/f"; git -C "$R" add .; git -C "$R" commit -qm x
  mkdir -p "$R/.git/refs/remotes/origin"
  : > "$R/.git/refs/remotes/origin/zero1"
  : > "$R/.git/refs/heads/zero2"
  # Controle du canal : for-each-ref rend rc=0 (mesure git 2.43) -- tout
  # detecteur fonde sur le code de retour est aveugle par construction.
  wch_git -C "$R" for-each-ref >/dev/null 2>&1
  fer_rc=$?
  if [ "$fer_rc" = "0" ]; then
    ok "rc=0 confirme avec refs cassees -- la detection DOIT lire stderr"
  else
    ko "rc=$fer_rc inattendu (le fixture ne reproduit plus la semantique mesuree)"
  fi
  broken="$(wch_broken_refs "$R")"
  if [ "$(printf '%s\n' "$broken" | grep -c .)" = "2" ]; then
    ok "wch_broken_refs nomme les 2 refs cassees via stderr"
  else
    ko "2 refs cassees attendues, obtenu: [$broken]"
  fi
  out="$(wch_integrity_pass "$R" 2>&1)"
  if echo "$out" | grep -q "reparation" && echo "$out" | grep -q "retire(s)"; then
    ok "passe integrite journalise la reparation"
  else
    ko "journal de reparation attendu, obtenu: $out"
  fi
  if [ ! -e "$R/.git/refs/remotes/origin/zero1" ] && [ ! -e "$R/.git/refs/heads/zero2" ]; then
    ok "fichiers de ref de zero octet retires"
  else
    ko "des refs vides survivent a la reparation"
  fi
  # La reparation ne doit avoir emporte AUCUNE ref valide.
  if git -C "$R" rev-parse -q --verify main >/dev/null 2>&1 \
     && git -C "$R" rev-parse -q --verify refs/remotes/origin/zero1 >/dev/null 2>&1; then
    ko "main valide + ref cassee resolue ? etat incoherent"
  elif git -C "$R" rev-parse -q --verify main >/dev/null 2>&1; then
    ok "ref valide main intacte apres reparation"
  else
    ko "la reparation a emporte la ref valide main"
  fi
  if [ -z "$(wch_broken_refs "$R")" ]; then
    ok "plus aucune ref cassee apres reparation"
  else
    ko "refs cassees residuelles: $(wch_broken_refs "$R")"
  fi
)
echo ""

echo "Test 3 : garde .promisor -- la reparation ne touche JAMAIS objects/ (controle negatif)"
(
  R="$TEST_DIR/promisor"
  git init -q -b main "$R"
  git -C "$R" config user.email t@t; git -C "$R" config user.name t
  echo x > "$R/f"; git -C "$R" add .; git -C "$R" commit -qm x
  mkdir -p "$R/.git/objects/pack" "$R/.git/objects/info"
  # Un marqueur .promisor est un fichier de ZERO octet legitime ; un find
  # -type f -empty -delete naif sur .git en emporterait un par pack.
  : > "$R/.git/objects/pack/pack-deadbeef.promisor"
  : > "$R/.git/objects/pack/pack-cafebabe.promisor"
  : > "$R/.git/objects/info/commit-graph.vierge"
  mkdir -p "$R/.git/refs/heads"; : > "$R/.git/refs/heads/zero"
  wch_drop_empty_refs "$R" >/dev/null
  if [ -e "$R/.git/objects/pack/pack-deadbeef.promisor" ] \
     && [ -e "$R/.git/objects/pack/pack-cafebabe.promisor" ] \
     && [ -e "$R/.git/objects/info/commit-graph.vierge" ]; then
    ok "les fichiers vides d'objects/ survivent tous (perimetre = garde)"
  else
    ko "la reparation a touche .git/objects -- le geste naif est DE dans l'organe"
  fi
  if [ ! -e "$R/.git/refs/heads/zero" ]; then
    ok "la ref vide sous refs/ est bien retiree (le perimetre n'est pas trop etroit)"
  else
    ko "refs/ non couvert -- perimetre trop etroit"
  fi
)
echo ""

echo "Test 4 : depot muet (0 refs lisibles) -- purge, jamais un « sain » non prouve"
(
  R="$TEST_DIR/muet"
  git init -q -b main "$R"
  rm -rf "$R/.git/refs"/* "$R/.git/logs" 2>/dev/null
  rm -f "$R/.git/packed-refs"
  out="$(wch_integrity_pass "$R" 2>&1)"
  if [ ! -d "$R" ]; then
    ok "depot sans ref lisible purge (le job suivant reclonera)"
  else
    ko "un depot muet a ete conserve comme sain -- le faux negatif est DE"
  fi
  if echo "$out" | grep -q "IRRECUPERABLE"; then
    ok "la purge est NOMMEE dans le journal"
  else
    ko "journal de purge attendu, obtenu: $out"
  fi
)
echo ""

echo "Test 5 : compte de packs borne -- mesure avant/apres journalisee"
(
  SRC="$TEST_DIR/src5"; R="$TEST_DIR/clone5"
  mk_source "$SRC"
  git clone -q --no-local --filter=blob:none "file://$SRC" "$R" 2>/dev/null
  for i in 4 5 6; do add_commit_and_fetch "$SRC" "$R" "$i"; done
  n_packs="$(wch_pack_count "$R")"
  if [ "$n_packs" -ge 4 ]; then
    ok "fixture fidèle : $n_packs packs accumulés (1 par fetch, comme la flotte)"
  else
    ko "fixture insuffisante ($n_packs packs) -- le test ne prouve plus rien"
  fi
  out="$(wch_maintenance_pass "$R" 2)"
  after="$(wch_pack_count "$R")"
  if [ "$after" = "1" ]; then
    ok "repack : $n_packs -> $after packs"
  else
    ko "1 pack attendu apres repack, obtenu $after"
  fi
  if echo "$out" | grep -q "repack $n_packs -> $after"; then
    ok "la mesure avant/apres est dans le journal (acceptance #15105)"
  else
    ko "journal de mesure attendu, obtenu: $out"
  fi
  # Le clone consolide reste un clone : fetch incremental + rev-parse.
  git -C "$R" rev-parse -q --verify origin/main >/dev/null 2>&1 \
    && ok "depot fonctionnel apres repack (rev-parse origin/main)" \
    || ko "rev-parse casse apres repack"
  n_prom="$(ls "$R"/.git/objects/pack/*.promisor 2>/dev/null | wc -l | tr -d ' ')"
  if [ "$n_prom" -ge 1 ]; then
    ok "marqueur .promisor preserve sur le pack consolide ($n_prom)"
  else
    ko "promisor disparu -- le pack consolide serait pris pour complet"
  fi
  add_commit_and_fetch "$SRC" "$R" 7
  if git -C "$R" rev-parse -q --verify origin/main >/dev/null 2>&1; then
    ok "fetch incremental OK apres repack"
  else
    ko "fetch incremental casse apres repack"
  fi
)
echo ""

echo "Test 6 : seuils inertes -- 0 desactive, sous-le-seil ne repack pas (controles negatifs)"
(
  SRC="$TEST_DIR/src6"; R="$TEST_DIR/clone6"
  mk_source "$SRC"
  git clone -q --no-local --filter=blob:none "file://$SRC" "$R" 2>/dev/null
  for i in 4 5 6; do add_commit_and_fetch "$SRC" "$R" "$i"; done
  before="$(wch_pack_count "$R")"
  out="$(wch_maintenance_pass "$R" 0)"
  if [ "$(wch_pack_count "$R")" = "$before" ] && [ -z "$out" ]; then
    ok "seuil 0 : inerte et muet"
  else
    ko "seuil 0 doit desactiver la maintenance, out=[$out]"
  fi
  out="$(wch_maintenance_pass "$R" 9999)"
  if [ "$(wch_pack_count "$R")" = "$before" ] && [ -z "$out" ]; then
    ok "sous le seuil : aucun repack (le cache incremental n'est pas derange)"
  else
    ko "un repack a eu lieu sous le seuil, out=[$out]"
  fi
)
echo ""

echo "Test 7 : passe complete sur un _work -- layout <workdir>/<repo>/<repo> (glob entrypoint)"
(
  W="$TEST_DIR/work"
  # Layout actions/checkout : _work/<repo>/<repo>/.git -- DEUX niveaux, le
  # meme glob que l'entrypoint (*/*/.git). Un niveau de plus serait invisible
  # a la passe.
  ORG="$W/CoursIA/CoursIA"
  mkdir -p "$ORG"
  SRC="$TEST_DIR/src7"
  mk_source "$SRC"
  git clone -q --no-local "file://$SRC" "$ORG" 2>/dev/null
  mkdir -p "$ORG/.git/refs/remotes/origin"
  : > "$ORG/.git/refs/remotes/origin/broken"
  out="$(wch_check_workdir "$W" 2)"
  if [ ! -e "$ORG/.git/refs/remotes/origin/broken" ] && [ -d "$ORG" ]; then
    ok "workdir : ref cassee reparee, clone conserve"
  else
    ko "workdir : etat inattendu (broken presente: $([ -e "$ORG/.git/refs/remotes/origin/broken" ] && echo oui || echo non), clone: $([ -d "$ORG" ] && echo oui || echo non))"
  fi
  # Le rapport de sante ne doit jamais casser l'appelant (entrypoint set -e).
  if wch_check_workdir "$W" 2 >/dev/null 2>&1; then
    ok "wch_check_workdir rend toujours 0 (garde jamais fatal)"
  else
    ko "wch_check_workdir a rendu non-zero -- il tuerait l'entrypoint sous set -e"
  fi
)
echo ""

# --- Verdict agrege ---------------------------------------------------------
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
if [ "$n_pass" = "0" ]; then
  echo "ERREUR: aucune assertion executee -- le harnais n'a rien mesure." >&2
  exit 2
fi
rm -rf "$TEST_DIR"
exit 0
