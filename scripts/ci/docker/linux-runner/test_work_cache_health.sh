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
  # Le journal nomme les drapeaux (#18225) : `-ad` ici, puisque ce depot
  # n'emprunte aucun objet. C'est cette trace qui distingue un repack qui
  # consolide d'un repack qui rapatrie les objets d'un miroir.
  if echo "$out" | grep -q "repack -ad $n_packs -> $after"; then
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

echo "Test 6b : 0 pack MAIS objets en vrac -- etat anormal, consolide (#21557)"
(
  # L'etat mesure sur les slots 8/9/12 d'ai-01 (2026-10-20) : 0 packfile et
  # 3,9 Go d'objets en vrac. Le compte de packs est SOUS le seuil, donc l'ancien
  # predicat rendait 0 sans rien faire -- et `gc.auto=0` (actions/checkout) fait
  # que rien d'autre ne consolide : l'etat est stable et chaque `cat-file` y
  # coute le parcours des repertoires d'objets (~600 s de scan par cycle).
  SRC="$TEST_DIR/src6b"; R="$TEST_DIR/clone6b"
  mk_source "$SRC"
  git init -q "$R"
  # transfer.unpackLimit eleve : le fetch DEPOSE les objets en vrac au lieu
  # d'ecrire un packfile -- c'est la forme anormale, reproduite sans bricolage.
  git -C "$R" -c transfer.unpackLimit=99999 fetch -q "file://$SRC" \
    '+refs/heads/main:refs/remotes/origin/main' 2>/dev/null
  if [ "$(wch_pack_count "$R")" = "0" ] && wch_loose_object_dirs "$R"; then
    ok "fixture fidèle : 0 pack et objets en vrac"
  else
    ko "fixture insuffisante (packs=$(wch_pack_count "$R")) -- le test ne prouve plus rien"
  fi
  out="$(wch_maintenance_pass "$R" 16)"
  after="$(wch_pack_count "$R")"
  if [ "$after" -ge 1 ]; then
    ok "repack declenche sur 0 pack + vrac : $after pack(s)"
  else
    ko "aucun pack apres passage -- le cycle resterait a ~600 s de scan"
  fi
  if echo "$out" | grep -q "repack -ad 0 ->"; then
    ok "la cause est journalisee (repack -ad 0 -> N, #21557)"
  else
    ko "journal de la cause attendu, obtenu: [$out]"
  fi
  # Controle negatif : un depot VIDE n'a ni pack ni vrac -- cache frais, muet.
  E="$TEST_DIR/empty6b"
  git init -q "$E"
  out="$(wch_maintenance_pass "$E" 16)"
  if [ -z "$out" ] && [ "$(wch_pack_count "$E")" = "0" ]; then
    ok "depot frais (0 pack, 0 vrac) : inerte et muet"
  else
    ko "un depot frais ne doit pas declencher de repack, out=[$out]"
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
  # ATTENTION : cette assertion mesure « rend 0 », elle ne mesure PAS « ne tue
  # pas l'appelant ». `if cmd; then` desarme set -e pour tout le corps de la
  # fonction appelee -- meme chose pour `||` et `&&` -- donc cette forme restait
  # verte alors que le garde tuait bel et bien le conteneur. Le mode d'echec de
  # production est mesure au Test 8, par sentinelle sous le shell de
  # l'entrypoint (#16938).
)
echo ""

echo "Test 8 : shell de PRODUCTION -- le garde ne tue pas l'appelant (#16938)"
(
  # LE DEFAUT MESURE. L'entrypoint porte `set -euo pipefail` (entrypoint.sh:12) ;
  # ce banc ne portait que `set -o pipefail` (L12). Sous le shell de production,
  # les 3 mesures laissaient fuir leur code de retour et l'appelant mourait :
  #   - git for-each-ref sur un depot illisible (HEAD detruit) -> rc=128
  #   - ls sur un glob sans correspondance (depot sans pack, etat NOMINAL d'un
  #     cache frais) -> rc=2, qui traverse le `| wc -l` sous pipefail
  # Mesure 2026-09-21, seuil 16 de production, sentinelle posee apres l'appel :
  # 128 et 2, sentinelle jamais atteinte. Sur le depot illisible la mort survient
  # a la PREMIERE ligne de wch_integrity_pass, donc AVANT la branche de purge --
  # le geste de reparation du cas ne pouvait pas s'executer (slot 8 : 174
  # demarrages morts consecutifs, aucune trace au journal du job).
  #
  # L'INSTRUMENT QUI VOIT CE DEFAUT est une SENTINELLE posee APRES l'appel, dans
  # un sous-shell qui porte le SHELL DE PRODUCTION. Ni le rc seul, ni un
  # `if cmd; then` ne le voient : `if`, comme `||` et `&&`, desarme set -e pour
  # TOUT le corps de la fonction appelee.
  replay_production() {
    local workdir="$1" threshold="$2"
    bash -c '
      set -euo pipefail
      . "$1"
      wch_check_workdir "$2" "$3"
      echo SENTINELLE-ATTEINTE
    ' _ "$SCRIPT_DIR/work_cache_health.sh" "$workdir" "$threshold" 2>&1
  }

  # CONTROLE NEGATIF DE L'INSTRUMENT : les lignes AVANT correctif, recopiees
  # litteralement et sans neutralisation de rc, doivent TUER le sous-shell.
  # Sans ce controle, une sentinelle atteinte ne prouve rien : un banc incapable
  # de rougir est vert par construction.
  pre_fix_broken_refs() {
    bash -c '
      set -euo pipefail
      broken="$(git -c safe.directory="*" -C "$1" for-each-ref 2>&1 >/dev/null | sed -n "s/^warning: ignoring broken ref //p")"
      echo SENTINELLE-ATTEINTE
    ' _ "$1" 2>&1
  }
  pre_fix_pack_count() {
    bash -c '
      set -euo pipefail
      before="$(ls "$1"/.git/objects/pack/*.pack 2>/dev/null | wc -l | tr -d " ")"
      echo SENTINELLE-ATTEINTE
    ' _ "$1" 2>&1
  }

  # Depot ILLISIBLE (HEAD detruit) : la forme mesuree sur le slot 8.
  mk_unreadable() {
    local R="$1/CoursIA/CoursIA"
    mkdir -p "$R"
    git init -q -b main "$R" 2>/dev/null
    git -C "$R" config user.email t@t; git -C "$R" config user.name t
    echo x > "$R/f"; git -C "$R" add . 2>/dev/null; git -C "$R" commit -qm x 2>/dev/null
    printf '\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0' > "$R/.git/HEAD"
  }
  # Depot SAIN sans aucun pack : le cas NOMINAL d'un cache frais.
  mk_healthy_no_pack() {
    local R="$1/CoursIA/CoursIA"
    mkdir -p "$R"
    git init -q -b main "$R" 2>/dev/null
    git -C "$R" config user.email t@t; git -C "$R" config user.name t
    # gc.auto=0 : la fixture doit porter 0 pack de facon DETERMINISTE, sinon un
    # git qui packerait au commit ferait passer (ou echouer) le cas pour une
    # raison de version, pas de comportement.
    git -C "$R" config gc.auto 0
    echo x > "$R/f"; git -C "$R" add . 2>/dev/null; git -C "$R" commit -qm x 2>/dev/null
  }

  # --- Fixtures, avec leur propre controle de fidelite ----------------------
  W_ILL="$TEST_DIR/p8-ill"; mk_unreadable "$W_ILL"
  W_HP="$TEST_DIR/p8-hp";    mk_healthy_no_pack "$W_HP"
  if [ -z "$(wch_broken_refs "$W_ILL/CoursIA/CoursIA")" ] \
     && [ "$(wch_ref_count "$W_ILL/CoursIA/CoursIA")" = "0" ]; then
    ok "fixture fidele : depot illisible (0 ref lisible, aucune ref cassee nommable)"
  else
    ko "la fixture « illisible » reste lisible -- le test ne prouve plus rien"
  fi
  n_hp="$(ls "$W_HP"/CoursIA/CoursIA/.git/objects/pack/*.pack 2>/dev/null | wc -l | tr -d ' ')"
  if [ "$n_hp" = "0" ]; then
    ok "fixture fidele : depot sain avec 0 pack (le glob sans correspondance est bien exerce)"
  else
    ko "fixture insuffisante ($n_hp pack) -- le cas « sans pack » n'est pas exerce"
  fi

  # --- Controle NEGATIF : l'instrument peut rougir ---------------------------
  out="$(pre_fix_broken_refs "$W_ILL/CoursIA/CoursIA")"; rc=$?
  if ! echo "$out" | grep -q "SENTINELLE-ATTEINTE" && [ "$rc" != "0" ]; then
    ok "controle negatif : la ligne AVANT correctif tue l'appelant (rc=$rc) -- l'instrument sait rougir"
  else
    ko "la forme non gardee n'a pas tue l'appelant (rc=$rc) -- l'instrument est aveugle"
  fi
  out="$(pre_fix_pack_count "$W_HP/CoursIA/CoursIA")"; rc=$?
  if ! echo "$out" | grep -q "SENTINELLE-ATTEINTE" && [ "$rc" != "0" ]; then
    ok "controle negatif : le compte de packs non garde tue l'appelant sur un depot SAIN (rc=$rc)"
  else
    ko "le compte de packs non garde n'a pas tue l'appelant (rc=$rc)"
  fi

  # --- Controle POSITIF 1 : depot illisible -> la branche de purge est ATTEINTE
  out="$(replay_production "$W_ILL" 16)"; rc=$?
  if echo "$out" | grep -q "SENTINELLE-ATTEINTE"; then
    ok "depot illisible : l'appelant CONTINUE (sentinelle atteinte sous set -euo pipefail)"
  else
    ko "depot illisible : l'appelant est mort avant la sentinelle (rc=$rc) -- le garde tue le slot"
  fi
  if [ ! -d "$W_ILL/CoursIA/CoursIA" ]; then
    ok "depot illisible : la branche de PURGE a bien ete atteinte (clone retire, le job suivant reclonera)"
  else
    ko "depot illisible : purge jamais atteinte -- le cache empoisonne survit"
  fi
  if echo "$out" | grep -q "IRRECUPERABLE"; then
    ok "depot illisible : la purge est NOMMEE dans le journal"
  else
    ko "journal de purge attendu, obtenu: $out"
  fi

  # --- Controle POSITIF 2 : depot sain sans pack -> conserve, et appelant vivant
  out="$(replay_production "$W_HP" 16)"; rc=$?
  if echo "$out" | grep -q "SENTINELLE-ATTEINTE"; then
    ok "depot sain sans pack : l'appelant CONTINUE sous set -euo pipefail"
  else
    ko "depot sain sans pack : l'appelant est mort avant la sentinelle (rc=$rc)"
  fi
  if [ -d "$W_HP/CoursIA/CoursIA" ]; then
    ok "depot sain sans pack : conserve (aucune purge intempestive d'un cache sain)"
  else
    ko "un depot sain sans pack a ete purge -- regression"
  fi

  # --- SECONDE BARRIERE du point d'appel (entrypoint.sh) --------------------
  # Deux assertions, qui mesurent deux choses differentes et le disent :
  #   (a) BEHAVIORALE : la FORME `if ! f; then ... fi` suffit a rendre un
  #       appelant insensible a un rc qui fuit -- rejouee contre une mesure qui
  #       fuit exprES, sentinelle posee apres.
  #   (b) PIN DE STRUCTURE : l'entrypoint emploie bien cette forme aujourd'hui.
  #       Elle seule est un test de texte ; elle ne prouve pas la garantie, elle
  #       empeche qu'un futur correctif retire la barriere en silence. Un pin
  #       rougit sur une suppression, pas sur un comportement.
  out="$(bash -c '
    set -euo pipefail
    leaking() { return 128; }
    if ! leaking; then
      echo "BARRIERE-A-JOURNALISE"
    fi
    echo SENTINELLE-ATTEINTE
  ' 2>&1)"; rc=$?
  if echo "$out" | grep -q "SENTINELLE-ATTEINTE"; then
    ok "la forme du point d'appel absorbe un rc qui fuit (sentinelle tenue, rc=$rc)"
  else
    ko "la forme du point d'appel ne suffit pas a absorber un rc qui fuit (rc=$rc)"
  fi
  if echo "$out" | grep -q "BARRIERE-A-JOURNALISE"; then
    ok "l'echec est JOURNALISE par la barriere (jamais avale en silence -- la cause reste diagnosticable)"
  else
    ko "la barriere avale l'echec sans le journaliser, obtenu: $out"
  fi
  if grep -q 'if ! wch_check_workdir' "$SCRIPT_DIR/entrypoint.sh"; then
    ok "PIN : entrypoint.sh porte toujours la seconde barriere sur wch_check_workdir"
  else
    ko "la seconde barriere a disparu de entrypoint.sh -- un futur rc qui fuit tuerait le slot en silence"
  fi
)
echo ""

# --- Le contrat sous le shell REEL de l'entrypoint (#16643) -----------------
# Tout ce banc source work_cache_health.sh sous `set -o pipefail` SANS
# `set -e` -- plus laxiste que entrypoint.sh, qui porte `set -euo pipefail`
# (ligne 9). C'est la raison pour laquelle l'assertion
# « wch_check_workdir rend toujours 0 » ci-dessus passait pendant que la
# production mourait : elle mesurait le CODE DE RETOUR d'une fonction qui,
# sous set -e, ne REVENAIT pas. Un `if cmd; then` desarme en plus set -e
# pendant la condition, donc meme un banc qui le porterait ne verrait rien.
#
# Ces cas rejouent le shell reel et verifient que l'appelant CONTINUE : le
# sentinel n'est imprime que si la ligne qui SUIT l'appel s'est executee.
# Le troisieme cas est le controle NEGATIF exige par l'en-tete de ce
# fichier -- sans lui, rien ne prouve que les deux premiers ont des dents.
SENTINEL="LAPPELANT-A-SURVECU"

run_under_entrypoint_shell() {
  local workdir="$1" child="$TEST_DIR/child.$$.sh"
  {
    echo "set -euo pipefail"
    echo ". '$SCRIPT_DIR/work_cache_health.sh'"
    cat                       # corps optionnel (redefinitions du controle negatif)
    echo "wch_check_workdir \"\$WCHT_DIR\" 16"
    echo "echo '$SENTINEL'"
  } > "$child"
  WCHT_DIR="$workdir" bash "$child" 2>&1
}

# Depot ILLISIBLE : .git present, HEAD reduit a des octets NUL, aucune ref.
# Signature mesuree firsthand sur le slot myia-ai-01-wsl-8 le 2026-09-18
# (174 demarrages consecutifs morts en rc=128, zero ligne de journal).
(
  D="$TEST_DIR/euo_illisible"
  R="$D/CoursIA/CoursIA"
  mkdir -p "$R/.git"
  printf '\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0' > "$R/.git/HEAD"
  out="$(run_under_entrypoint_shell "$D" < /dev/null)"
  if printf '%s' "$out" | grep -q "$SENTINEL"; then
    ok "set -euo pipefail : depot illisible -- l'appelant SURVIT a la passe"
  else
    ko "set -euo pipefail : depot illisible -- l'appelant est MORT [$out]"
  fi
  if [ ! -d "$R" ]; then
    ok "set -euo pipefail : depot illisible PURGE (la branche de reparation est atteinte)"
  else
    ko "set -euo pipefail : depot illisible conserve -- la purge n'a pas eu lieu"
  fi
)

# Depot SAIN mais SANS AUCUN PACK : etat banal d'un clone interrompu, pas une
# corruption. `ls <glob sans match>` rend rc=2 et tuait wch_maintenance_pass.
(
  D="$TEST_DIR/euo_nopack"
  R="$D/CoursIA/CoursIA"
  mkdir -p "$R"
  git -c init.defaultBranch=main init -q "$R"
  git -C "$R" -c user.email=t@t -c user.name=t commit -q --allow-empty -m seed
  out="$(run_under_entrypoint_shell "$D" < /dev/null)"
  if printf '%s' "$out" | grep -q "$SENTINEL"; then
    ok "set -euo pipefail : depot sans pack -- l'appelant SURVIT"
  else
    ko "set -euo pipefail : depot sans pack -- l'appelant est MORT [$out]"
  fi
  if [ -d "$R/.git" ]; then
    ok "set -euo pipefail : depot sain sans pack CONSERVE (non-regression)"
  else
    ko "set -euo pipefail : depot sain sans pack purge a tort"
  fi
)

# CONTROLE NEGATIF -- le seul cas qui prouve que les deux precedents mesurent
# quelque chose. On redefinit wch_broken_refs dans sa forme d'AVANT #16643
# (sans `|| true`) et on exige que l'appelant MEURE. Si le sentinel sort
# quand meme, c'est le banc qui est creux, pas le code qui est sain.
(
  D="$TEST_DIR/euo_negatif"
  R="$D/CoursIA/CoursIA"
  mkdir -p "$R/.git"
  printf '\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0' > "$R/.git/HEAD"
  out="$(run_under_entrypoint_shell "$D" <<'UNGUARDED'
wch_broken_refs() {
  wch_git -C "$1" for-each-ref 2>&1 >/dev/null \
    | sed -n 's/^warning: ignoring broken ref //p'
}
UNGUARDED
)"
  if printf '%s' "$out" | grep -q "$SENTINEL"; then
    ko "controle NEGATIF CREUX : la forme non gardee survit -- le banc ne prouve rien"
  else
    ok "controle NEGATIF : la forme non gardee TUE l'appelant (le banc a des dents)"
  fi
)
echo ""

echo "Test 10 : echecs consecutifs de repack -> escalade en quarantaine (#21745 limb B)"
# Controle positif ET negatif du compteur : N-1 echecs laissent le clone en
# place, le N-ieme le renomme. Le renommage est REVERSIBLE (jamais rm) : le
# test verifie que l'arbre survit sous <repo>.stale-<ts>.
(
  RQ="$TEST_DIR/repack-streak"
  mkdir -p "$RQ"
  git init -q "$RQ"
  git -C "$RQ" -c user.email=t@t -c user.name=t commit -q --allow-empty -m init
  mkdir -p "$RQ/.git/objects/pack"
  : > "$RQ/.git/objects/pack/a.pack"
  : > "$RQ/.git/objects/pack/b.pack"

  # Substitution locale : repack echoue TOUJOURS, tout le reste delegue au
  # vrai git (memes semantiques, meme safe.directory).
  wch_git() {
    case "$*" in
      *" repack "*) return 1 ;;
    esac
    git -c safe.directory='*' "$@"
  }
  WCH_REPACK_FAIL_MAX=3

  out1="$(wch_maintenance_pass "$RQ" 1 2>&1)"
  ck="$(wch_repack_streak_read "$RQ")"
  if [ "$ck" = "1" ]; then ok "echec 1/3 : compteur = 1"; else ko "compteur apres 1 echec = [$ck], attendu 1"; fi
  if [ -d "$RQ" ]; then ok "echec 1/3 : clone conserve (pas d'escalade avant le seuil)"; else ko "clone renomme des le 1er echec"; fi
  if echo "$out1" | grep -q "echec consecutif 1/3"; then ok "echec 1/3 : le seuil est journalise"; else ko "seuil absent du journal: $out1"; fi

  wch_maintenance_pass "$RQ" 1 >/dev/null 2>&1
  ck="$(wch_repack_streak_read "$RQ")"
  if [ "$ck" = "2" ]; then ok "echec 2/3 : compteur = 2"; else ko "compteur apres 2 echecs = [$ck], attendu 2"; fi

  wch_maintenance_pass "$RQ" 1 >/dev/null 2>&1
  if [ -d "$RQ" ]; then ko "3e echec : clone toujours en place (escalade attendue)"; else ok "3e echec : clone retire du chemin (quarantaine)"; fi
  if ls -d "$TEST_DIR"/repack-streak.stale-* >/dev/null 2>&1; then
    ok "3e echec : arbre PRESERVE sous <repo>.stale-<ts> (renommage, pas suppression)"
  else
    ko "3e echec : aucun <repo>.stale-* -- preservation non prouvee"
  fi

  # Controle NEGATIF : un succes remet le compteur a zero (sinon la moindre
  # panne transitoire accumulerait jusqu'a la quarantaine).
  RS="$TEST_DIR/repack-reset"
  mkdir -p "$RS"
  git init -q "$RS"
  git -C "$RS" -c user.email=t@t -c user.name=t commit -q --allow-empty -m init
  mkdir -p "$RS/.git/objects/pack"
  : > "$RS/.git/objects/pack/a.pack"
  : > "$RS/.git/objects/pack/b.pack"
  wch_repack_streak_write "$RS" 2
  wch_git() { git -c safe.directory='*' "$@"; }
  wch_maintenance_pass "$RS" 1 >/dev/null 2>&1
  ck="$(wch_repack_streak_read "$RS")"
  if [ "$ck" = "0" ]; then ok "controle NEGATIF : un repack reussi remet le compteur a 0"; else ko "compteur apres succes = [$ck], attendu 0"; fi
)
echo ""

# --- Repack sous alternates (#18225) --------------------------------------
# Le slot d'un parc a miroir emprunte ses objets ; le repack de maintenance ne
# doit PAS les rapatrier. Le controle est un couple : MEME fixture, deux formes
# de repack, verdicts OPPOSES. Un test qui ne montrerait que la bonne forme ne
# prouverait pas que c'est le drapeau qui decide -- il pourrait passer parce que
# git ne copie jamais, ou parce que la fixture ne contient rien a copier.
echo "Test : repack -- un depot a alternates ne copie pas les objets empruntes (#18225)"
(
  M="$TEST_DIR/mirror-objs.git"
  S="$TEST_DIR/slot-alt"
  S2="$TEST_DIR/slot-alt-oldfl"
  SRC="$TEST_DIR/src-alt"
  git init -q --bare "$M"
  git init -q -b main "$SRC"
  git -C "$SRC" config user.email t@t; git -C "$SRC" config user.name t
  for i in 1 2 3; do
    head -c 512 /dev/urandom | base64 > "$SRC/m$i.txt"
    git -C "$SRC" add .
    git -C "$SRC" commit -qm "m$i"
  done
  git -C "$SRC" push -q "$M" main
  # Objet qui n'existe QUE dans le miroir : sa presence locale apres repack
  # signifie « recopie », son absence signifie « emprunte ».
  BLOB="$(git -C "$SRC" rev-parse main:m1.txt)"

  git clone -q --shared "$M" "$S"
  git clone -q --shared "$M" "$S2"

  if wch_has_alternates "$S"; then
    ok "predicat : un clone --shared porte des alternates"
  else
    ko "predicat : alternates non detecte sur un clone --shared"
  fi
  if wch_has_alternates "$SRC"; then
    ko "predicat : alternates detecte sur un depot ordinaire (faux positif)"
  else
    ok "predicat : un depot ordinaire n'a pas d'alternates (controle negatif)"
  fi
  if [ "$(wch_repack_flags "$S")" = "-adl" ] && [ "$(wch_repack_flags "$SRC")" = "-ad" ]; then
    ok "drapeaux : -adl sous alternates, -ad sinon"
  else
    ko "drapeaux : $(wch_repack_flags "$S") / $(wch_repack_flags "$SRC")"
  fi

  # Deux packs locaux pour franchir le seuil (sinon la maintenance sort avant
  # le repack et le test ne mesurerait rien).
  for s in "$S" "$S2"; do
    echo local1 > "$s/l1.txt"; git -C "$s" add .
    git -C "$s" -c user.email=t@t -c user.name=t commit -qm l1
    git -C "$s" repack -adl -q
    echo local2 > "$s/l2.txt"; git -C "$s" add .
    git -C "$s" -c user.email=t@t -c user.name=t commit -qm l2
    git -C "$s" repack -d -q
  done
  before="$(wch_pack_count "$S")"
  if [ "${before:-0}" -ge 2 ]; then
    ok "fixture : $before packs locaux (le seuil 1 est franchi, le repack aura lieu)"
  else
    ko "fixture : seulement $before pack(s) -- le repack ne serait pas declenche"
  fi

  out="$(wch_maintenance_pass "$S" 1 2>&1)"
  echo "$out" >> "$LOG"
  if echo "$out" | grep -q -- "-adl"; then
    ok "maintenance : le journal nomme les drapeaux -adl"
  else
    ko "maintenance : drapeaux -adl absents du journal ($out)"
  fi
  # Verdict du depot sous maintenance, mesure par RETRAIT des alternates : si
  # l'objet du miroir reste resolvable sans eux, il a ete copie.
  mv "$S/.git/objects/info/alternates" "$S/.git/objects/info/alternates.off"
  if git -C "$S" cat-file -e "$BLOB" 2>/dev/null; then
    ko "les objets du miroir ont ete COPIES dans le volume du slot (repack sans -l)"
  else
    ok "objets du miroir non copies : le miroir supprime bien le telechargement par slot"
  fi
  mv "$S/.git/objects/info/alternates.off" "$S/.git/objects/info/alternates"

  # Controle par le MECANISME : la meme fixture sous l'ancienne forme doit,
  # elle, copier. Sans ce temoin, le vert precedent pourrait venir de la
  # fixture et non du drapeau.
  git -C "$S2" repack -ad >/dev/null 2>&1
  mv "$S2/.git/objects/info/alternates" "$S2/.git/objects/info/alternates.off"
  if git -C "$S2" cat-file -e "$BLOB" 2>/dev/null; then
    ok "temoin : repack -ad (sans -l) copie l'objet du miroir -- le drapeau est bien la cause"
  else
    ko "temoin : même -ad n'a pas copie -- la mesure precedente ne prouve rien"
  fi
  mv "$S2/.git/objects/info/alternates.off" "$S2/.git/objects/info/alternates"
)
echo ""

# --- Retention des quarantaines `.stale-*` ---------------------------------
# Le defaut mesure : le renommage de quarantaine etait reversible mais rien
# ne le retirait, si bien que la retention etait infinie par construction.
# Les trois controles NEGATIFS comptent autant que le positif : un clone
# vivant, un suffixe non conforme et le plafond bas doivent tous survivre.
(
  echo "--- retention des quarantaines .stale-* ---"
  P="$TEST_DIR/prune"
  rm -rf "$P"
  mkdir -p "$P/slug1"
  for ts in 20260101T000000Z 20260102T000000Z 20260103T000000Z 20260104T000000Z; do
    mkdir -p "$P/slug1/CoursIA.stale-$ts"
    # contenu non vide : `du -sk` doit rendre un compte exploitable
    head -c 4096 /dev/zero > "$P/slug1/CoursIA.stale-$ts/payload"
  done
  # Temoin 1 : le clone VIVANT, cote a cote des quarantaines.
  mkdir -p "$P/slug1/CoursIA/.git"
  # Temoin 2 : suffixe non conforme -- ecrit a la main, jamais emis par les
  # deux sites. Il doit survivre, meme s'il est plus ancien que la borne.
  mkdir -p "$P/slug1/notes.stale-manuel"

  out="$(WCH_STALE_KEEP=2 WCH_STALE_MAX_AGE_HOURS=0 wch_prune_quarantines "$P" 2>&1)"
  echo "$out" >> "$LOG"

  if [ -d "$P/slug1/CoursIA.stale-20260101T000000Z" ] || [ -d "$P/slug1/CoursIA.stale-20260102T000000Z" ]; then
    ko "retention : les deux quarantaines les plus anciennes auraient du partir"
  else
    ok "retention : les deux plus anciennes sont retirees (plafond 2)"
  fi
  if [ -d "$P/slug1/CoursIA.stale-20260103T000000Z" ] && [ -d "$P/slug1/CoursIA.stale-20260104T000000Z" ]; then
    ok "retention : les deux plus recentes sont conservees (l'arbre reste inspectable)"
  else
    ko "retention : les plus recentes ont ete retirees -- le geste perd sa preuve de preservation"
  fi
  if [ -d "$P/slug1/CoursIA/.git" ]; then
    ok "temoin : le clone vivant n'est jamais touche"
  else
    ko "temoin : le clone VIVANT a ete retire -- le motif est trop large"
  fi
  if [ -d "$P/slug1/notes.stale-manuel" ]; then
    ok "temoin : un suffixe .stale- non conforme a l'horodatage survit"
  else
    ko "temoin : le filtre par forme n'a pas joue (notes.stale-manuel retire)"
  fi
  if echo "$out" | grep -q "retention des quarantaines -- 2 retiree"; then
    ok "retention : le journal nomme le compte retire"
  else
    ko "retention : le journal ne porte pas le compte retire ($out)"
  fi

  # Plafond bas : 0 retirerait TOUT, y compris la quarantaine du dernier
  # incident. La borne doit se clamper a 1, pas obeir.
  out="$(WCH_STALE_KEEP=0 WCH_STALE_MAX_AGE_HOURS=0 wch_prune_quarantines "$P" 2>&1)"
  echo "$out" >> "$LOG"
  n_left="$(find "$P/slug1" -mindepth 1 -maxdepth 1 -type d -name 'CoursIA.stale-*' | wc -l)"
  if [ "$n_left" = "1" ]; then
    ok "plafond 0 : clampe a 1, la derniere quarantaine survit"
  else
    ko "plafond 0 : $n_left quarantaine(s) restante(s) -- le clamp n'a pas joue"
  fi

  # Passages repetes : le second ne doit plus rien retirer (idempotence).
  out="$(WCH_STALE_KEEP=2 WCH_STALE_MAX_AGE_HOURS=0 wch_prune_quarantines "$P" 2>&1)"
  if [ -z "$out" ]; then
    ok "idempotence : un passage sans rien a retirer n'ecrit rien"
  else
    ko "idempotence : un passage a vide a ecrit dans le journal ($out)"
  fi
)
echo ""

# --- Empilement des quarantaines (defaut po-2023 du 2026-10-30) -------------
# Deux defauts mesures sur po-2023, dans le meme organe, se tiennent par la main :
#
#  1. une quarantaine EST un clone complet, donc elle porte un `.git` -- et la
#     boucle `$workdir/*/*/.git` de `wch_check_workdir` la reprenait comme un
#     depot VIVANT. La maintenance la repackait ; le repack echoue et AJOUTE des
#     packs (2,4 -> 4,8 Gio mesures), puis l'echec la re-quarantinait SOUS
#     ELLE-MEME : `X.stale-A.stale-B…stale-J`, une generation par demarrage,
#     dix sur disque depuis le 27/10 pour 4,8 Gio dans un volume de 7,2 Gio.
#  2. la retention comptait des NOMS : la chaine entiere valait UNE entree et
#     survivait a `keep=2`, donc elle ne pouvait pas se resorber toute seule.
#
# Le premier controle est un COUPLE (clone vivant maintenu / quarantaine
# epargnee) : sans le membre positif, un organe qui ne fait plus rien passerait.
echo "Test : quarantaines empilees -- maintenance exclue, retention par generation"
(
  W="$TEST_DIR/stack"
  mkdir -p "$W/slug1"

  # --- Controle 1 : l'empilement cesse a la source ------------------------
  git init -q "$W/slug1/CoursIA"
  git -C "$W/slug1/CoursIA" -c user.email=t@t -c user.name=t commit -q --allow-empty -m init

  Q="$W/slug1/CoursIA.stale-20260101T000000Z"
  mkdir -p "$Q"
  git init -q "$Q"            # c'est CE `.git` qui faisait la quarantaine passer pour vivante
  git -C "$Q" -c user.email=t@t -c user.name=t commit -q --allow-empty -m old
  head -c 4096 /dev/zero > "$Q/payload"

  seen="$TEST_DIR/stack-maintained.txt"
  : > "$seen"
  # Substitutions bornees a la MAINTENANCE : c'est elle qui re-quarantinait.
  # `wch_prune_quarantines` reste le vrai (une seule quarantaine ici, donc un
  # passage a vide) -- le stubber ici priverait le controle 3 de son organe.
  wch_maintenance_pass() { printf '%s\n' "${1##*/}" >> "$seen"; return 0; }
  wch_integrity_pass() { return 0; }

  # La borne d'AGE est desactivee ici : ce controle porte sur l'EXCLUSION de
  # la maintenance, pas sur la retention (la borne d'age a ses propres
  # controles, plus bas).
  WCH_STALE_MAX_AGE_HOURS=0 wch_check_workdir "$W" 1 >/dev/null 2>&1

  if grep -qx 'CoursIA' "$seen"; then
    ok "quarantaine : controle POSITIF -- le clone vivant passe bien en maintenance"
  else
    ko "quarantaine : le clone VIVANT n'est pas passe en maintenance -- le banc ne prouve rien"
  fi
  if grep -qx 'CoursIA.stale-20260101T000000Z' "$seen"; then
    ko "quarantaine : reprise comme un depot vivant (c'est l'empilement qu'on veut tuer)"
  else
    ok "quarantaine : exclue de la maintenance -- l'empilement cesse a la source"
  fi
  nq="$(find "$W/slug1" -mindepth 1 -maxdepth 1 -type d -name '*.stale-*' | wc -l)"
  if [ "$nq" = "1" ]; then
    ok "quarantaine : aucune generation ajoutee, le nom est inchange"
  else
    ko "quarantaine : $nq quarantaine(s) sur disque -- une generation a ete empilee"
  fi
  if [ "$(wc -c < "$Q/payload" 2>/dev/null | tr -d ' ')" = "4096" ]; then
    ok "quarantaine : le contenu mis de cote est intact"
  else
    ko "quarantaine : le contenu mis de cote a ete altere"
  fi

  # --- Controle 2 : la profondeur se mesure, elle ne se devine pas --------
  d="$(wch_quarantine_depth 'CoursIA.stale-20260101T000000Z.stale-20260102T000000Z.stale-20260103T000000Z')"
  if [ "$d" = "3" ]; then ok "profondeur : une chaine de 3 se lit 3 generations, pas une entree"
  else ko "profondeur de la chaine = [$d], attendu 3"; fi
  d="$(wch_quarantine_depth 'CoursIA.stale-20260101T000000Z')"
  if [ "$d" = "1" ]; then ok "profondeur : une quarantaine simple vaut 1"
  else ko "profondeur simple = [$d], attendu 1"; fi
  d="$(wch_quarantine_depth 'CoursIA')"
  if [ "$d" = "0" ]; then ok "profondeur : un clone vivant vaut 0"
  else ko "profondeur d'un clone = [$d], attendu 0"; fi

  # --- Controle 3 : une chaine deja sur disque se ramene a `keep` ---------
  S="$TEST_DIR/stack-prune/slug1"
  mkdir -p "$S/CoursIA/.git"   # temoin : le clone vivant du meme slot
  CH="$S/CoursIA.stale-20260101T000000Z.stale-20260102T000000Z.stale-20260103T000000Z"
  mkdir -p "$CH"
  head -c 4096 /dev/zero > "$CH/payload"

  out="$(WCH_STALE_KEEP=2 WCH_STALE_MAX_AGE_HOURS=0 wch_prune_quarantines "$TEST_DIR/stack-prune" 2>&1)"
  echo "$out" >> "$LOG"
  if [ -d "$S/CoursIA.stale-20260102T000000Z.stale-20260103T000000Z" ]; then
    ok "empilement : ramene a 2 generations (les plus anciennes ecartees)"
  else
    ko "empilement : la chaine n'a pas ete ramenee a 2 generations ($(ls "$S"))"
  fi
  if [ -d "$CH" ]; then ko "empilement : l'ancien nom est encore la -- deux chaines pour un volume"; else ok "empilement : un seul nom subsiste"; fi
  if [ "$(wc -c < "$S/CoursIA.stale-20260102T000000Z.stale-20260103T000000Z/payload" 2>/dev/null | tr -d ' ')" = "4096" ]; then
    ok "empilement : RENOMMAGE, pas suppression -- le contenu suit la chaine"
  else
    ko "empilement : le contenu n'a pas suivi le renommage -- la preuve de preservation manque"
  fi
  if echo "$out" | grep -q "ramenee a CoursIA.stale-20260102T000000Z.stale-20260103T000000Z"; then
    ok "empilement : le journal nomme la chaine ramenee"
  else
    ko "empilement : le journal ne nomme pas le resultat ($out)"
  fi
  if [ -d "$S/CoursIA/.git" ]; then
    ok "empilement : le clone vivant du meme slot n'est jamais touche"
  else
    ko "empilement : le clone VIVANT a ete touche -- le motif est trop large"
  fi

  # Plafond 1 : la chaine se ramene a sa seule generation la plus recente.
  out="$(WCH_STALE_KEEP=1 WCH_STALE_MAX_AGE_HOURS=0 wch_prune_quarantines "$TEST_DIR/stack-prune" 2>&1)"
  echo "$out" >> "$LOG"
  if [ -d "$S/CoursIA.stale-20260103T000000Z" ] && [ ! -d "$S/CoursIA.stale-20260102T000000Z.stale-20260103T000000Z" ]; then
    ok "empilement : plafond 1 ramene la chaine a une generation"
  else
    ko "empilement : plafond 1 inoperant ($(ls "$S"))"
  fi
)
echo ""

# --- Borne d'AGE des quarantaines -------------------------------------------
# La borne de NOMBRE (#23076) borne la retention en NOMBRE, pas en DUREE :
# mesure ai-01 du 2026-10-31, 15 clones en quarantaine (24 Gio) ages de
# 59 a 114 h, tous retenus par la seule borne de nombre. La borne d'AGE ferme
# la DUREE.
#
# Le controle DISCRIMINANT est l'age lu dans le NOM : le mtime d'une
# quarantaine est preserve par le renommage (`rename(2)`), donc un mtime
# ancien ne prouve rien -- et un age lu dans le mtime supprimerait des clones
# recemment mis de cote.
echo "Test : borne d'age des quarantaines (fenetre d'inspection)"
(
  P="$TEST_DIR/age"
  mkdir -p "$P/slug1"
  # temoin permanent : le clone VIVANT du slot
  mkdir -p "$P/slug1/CoursIA/.git"
  # quarantaine VIEILLE (nom de 2025) et quarantaine RECENTE (nom d'aujourd'hui)
  mkdir -p "$P/slug1/CoursIA.stale-20250101T000000Z"
  head -c 4096 /dev/zero > "$P/slug1/CoursIA.stale-20250101T000000Z/payload"
  recent="$(date -u +%Y%m%dT%H%M%SZ)"
  mkdir -p "$P/slug1/CoursIA.stale-$recent"
  head -c 4096 /dev/zero > "$P/slug1/CoursIA.stale-$recent/payload"
  # temoin du discriminant : mtime ANCIEN, nom RECENT -> doit SURVIVRE
  touch -d '2020-01-01 00:00:00' "$P/slug1/CoursIA.stale-$recent" 2>/dev/null || true

  # Plafond de nombre 5 : le compte seul ne retirerait RIEN (une seule
  # quarantaine passe le seuil). Ce qui part, c'est l'AGE.
  out="$(WCH_STALE_KEEP=5 WCH_STALE_MAX_AGE_HOURS=48 wch_prune_quarantines "$P" 2>&1)"
  echo "$out" >> "$LOG"

  if [ -d "$P/slug1/CoursIA.stale-20250101T000000Z" ]; then
    ko "borne d'age : une quarantaine de 2025 a survecu (plafond 5, fenetre 48 h)"
  else
    ok "borne d'age : la quarantaine hors fenetre part malgre le plafond de nombre"
  fi
  if [ -d "$P/slug1/CoursIA.stale-$recent" ]; then
    ok "borne d'age : la quarantaine recente survit (meme avec un mtime ancien)"
  else
    ko "borne d'age : la quarantaine RECENTE a ete retiree -- l'age n'est pas lu dans le nom"
  fi
  if [ -d "$P/slug1/CoursIA/.git" ]; then
    ok "temoin : le clone vivant n'est jamais touche"
  else
    ko "temoin : le clone VIVANT a ete retire -- le motif est trop large"
  fi
  if echo "$out" | grep -q "hors fenetre d'age"; then
    ok "borne d'age : le journal nomme la cause du retrait"
  else
    ko "borne d'age : le journal ne nomme pas la cause ($out)"
  fi

  # La borne d'AGE est DESACTIVABLE (0) : un parc qui veut la seule borne de
  # nombre la pose explicitement.
  mkdir -p "$P/slug1/CoursIA.stale-20250101T000000Z"
  out="$(WCH_STALE_KEEP=5 WCH_STALE_MAX_AGE_HOURS=0 wch_prune_quarantines "$P" 2>&1)"
  echo "$out" >> "$LOG"
  if [ -d "$P/slug1/CoursIA.stale-20250101T000000Z" ]; then
    ok "borne d'age desactivee (0) : la quarantaine hors fenetre survit"
  else
    ko "borne d'age desactivee (0) : la quarantaine a ete retiree quand meme"
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
