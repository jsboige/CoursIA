#!/usr/bin/env bash
# Tests de la moitie CONSOMMATRICE du magasin d'objets partage (#18225) --
# le bloc `TEST-ENTRYPOINT-MIRROR` de entrypoint.sh : alternates sur les clones
# existants, semis du _work quand il n'y en a pas.
#
# Methode identique a test_entrypoint_disarm.sh : on extrait le bloc REEL du
# script sous test (marqueurs de section) et on l'execute contre des depots git
# fixture reels. Aucun stub : ce qui est observe est le comportement de git et
# du systeme de fichiers, pas une reimplementation du comportement attendu.
#
# Les cinq cas couvrent les deux facons de se tromper :
#   - trop en faire : semer par-dessus un clone sain (perte du cache #14285),
#     ecrire un alternates en double, copier les objets du miroir ;
#   - ne rien faire : un miroir absent doit rendre la main SANS rien ecrire
#     (fail-open), un slot froid doit etre seme (le gain), un _work sans .git
#     doit etre ecarte sans perte (jamais `rm -rf`).

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="$(mktemp -d /tmp/entrypoint-mirror-test-XXXXXX)"
LOG="$TEST_DIR/test.log"
: > "$LOG"

RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

if ! sed -n '/# TEST-ENTRYPOINT-MIRROR-START/,/# TEST-ENTRYPOINT-MIRROR-END/p' \
    "$SCRIPT_DIR/entrypoint.sh" > "$TEST_DIR/block.sh" || \
   ! grep -q "mirror_ensure_alternates" "$TEST_DIR/block.sh"; then
  echo "FAIL extraction du bloc miroir de entrypoint.sh" >&2
  exit 1
fi

WORK="$TEST_DIR/_work"
MIRROR="$TEST_DIR/coursia-mirror.git"
REMOTE="https://example.invalid/CoursIA.git"
# Le bloc lit ces deux variables comme l'entrypoint les recoit (le superviseur
# les passe en -e) ; les fixer ici, c'est tester le cablage reel.
export ACTIONS_RUNNER_INPUT_WORK="$WORK"
export COURSIA_RUNNER_MIRROR_PATH="$MIRROR"
export COURSIA_RUNNER_MIRROR_REMOTE="$REMOTE"
mkdir -p "$WORK"

run_block() { bash "$TEST_DIR/block.sh" 2>&1; }

# Nombre de lignes de l'alternates qui designent le miroir, en comparant la
# QUEUE du chemin et non sa forme. Sous Git Bash, git ecrit
# `C:/Users/.../coursia-mirror.git/objects` alors que le bloc manipule
# `/tmp/.../coursia-mirror.git/objects` : deux formes du MEME repertoire, que
# ni l'egalite de chaines ni realpath ne rapprochent sur cet hote (montage
# /tmp distinct). C'est un artefact de l'hote de test -- dans le conteneur les
# deux formes coincident -- donc le test compte ce qui est vrai partout : une
# seule ligne designe le miroir, quelle que soit la forme.
mirror_lines() {
  local f="$1/.git/objects/info/alternates" n
  [ -f "$f" ] || { printf '%s\n' 0; return 0; }
  # `grep -c` IMPRIME 0 quand il ne trouve rien, et rend 1 : un `|| printf 0`
  # ajouterait un second 0 et la comparaison echouerait sur "0\n0". Le repli
  # porte donc sur une sortie VIDE, pas sur le code de retour.
  n="$(grep -c '/coursia-mirror\.git/objects$' "$f" 2>/dev/null)"
  printf '%s\n' "${n:-0}"
}

# Miroir bare de fixture : trois commits sur main, plus un blob temoin dont le
# SHA n'existe QUE dans le miroir (sert au controle « aucun objet copie »).
make_mirror() {
  local src="$TEST_DIR/src"
  git init -q --bare "$MIRROR"
  git init -q -b main "$src"
  git -C "$src" config user.email t@t
  git -C "$src" config user.name t
  local i
  for i in 1 2 3; do
    echo "contenu $i" > "$src/f$i.txt"
    git -C "$src" add .
    git -C "$src" commit -qm "c$i"
  done
  git -C "$src" push -q "$MIRROR" main
  git -C "$MIRROR" symbolic-ref HEAD refs/heads/main
}

# --- Test 1 : miroir absent = aucun geste (fail-open) -----------------------
echo "Test 1 : miroir absent -- le bloc rend 0 et n'ecrit rien (fail-open)"
(
  out="$(COURSIA_RUNNER_MIRROR_PATH="$TEST_DIR/absent.git" run_block)"; rc=$?
  echo "$out" >> "$LOG"
  if [ "$rc" -eq 0 ]; then ok "T1 bloc exit 0 sans miroir"; else ko "T1 rc=$rc attendu 0"; fi
  if [ -e "$WORK/CoursIA" ]; then
    ko "T1 un semis a eu lieu sans miroir -- exactement ce que le fail-open interdit"
  else
    ok "T1 aucun _work cree sans miroir"
  fi
)
echo ""

make_mirror

# --- Test 2 : slot froid seme, zero objet copie -----------------------------
echo "Test 2 : slot froid -- clone --shared du miroir, alternates, origin HTTPS"
(
  out="$(run_block)"
  echo "$out" >> "$LOG"
  R="$WORK/CoursIA/CoursIA"
  if [ -d "$R/.git" ]; then ok "T2 _work/CoursIA/CoursIA cree"; else ko "T2 semis absent"; fi
  if [ "$(mirror_lines "$R")" = "1" ]; then
    ok "T2 alternates pointe les objets du miroir"
  else
    ko "T2 alternates absent/faux : $(cat "$R/.git/objects/info/alternates" 2>/dev/null)"
  fi
  url="$(git -C "$R" remote get-url origin 2>/dev/null)"
  if [ "$url" = "$REMOTE" ]; then
    ok "T2 origin remis sur HTTPS ($url)"
  else
    ko "T2 origin laisse sur '$url' -- les jobs fetcheraient un depot local"
  fi
  # Le gain EST ici : zero objet copie. Un `clone` sans --shared rendrait
  # plusieurs Mo et le test passerait quand meme sur les lignes precedentes.
  nloose="$(git -C "$R" count-objects -v 2>/dev/null | awk '/^count:/{print $2}')"
  npack="$(ls "$R"/.git/objects/pack/*.pack 2>/dev/null | wc -l | tr -d ' ')"
  if [ "${nloose:-x}" = "0" ] && [ "${npack:-x}" = "0" ]; then
    ok "T2 aucun objet copie ($nloose en vrac, $npack pack) -- le semis est instantane"
  else
    ko "T2 des objets ont ete copies (count=$nloose, packs=$npack)"
  fi
  # Le HEAD doit rester lisible : un clone sans checkout dont HEAD serait
  # casse ferait echouer actions/checkout AVANT le fetch.
  if git -C "$R" rev-parse --verify -q HEAD >/dev/null; then
    ok "T2 HEAD resolvable dans le repo seme (objets atteints via alternates)"
  else
    ko "T2 HEAD non resolvable -- le semis ne sert a rien"
  fi
)
echo ""

# --- Test 3 : alternates idempotents ---------------------------------------
echo "Test 3 : alternates idempotent -- une ligne, quel que soit le nombre de boots"
(
  R="$WORK/CoursIA/CoursIA"
  # Sequence REELLE : T2 vient de semer, donc l'alternates porte la forme ecrite
  # par GIT, qui n'est pas celle que le bloc passe (mesure de cet hote :
  # `C:/Users/.../x/objects` cote git, `/tmp/.../x/objects` cote bash). Un bloc
  # qui compare les chaines brutes ne reconnait pas sa propre ligne et en ajoute
  # une SECONDE : le fichier grossit a chaque boot. Le test compte les deux
  # formes (cf mirror_lines), donc il voit ce doublon.
  run_block >/dev/null 2>&1
  n="$(mirror_lines "$R")"
  if [ "$n" = "1" ]; then
    ok "T3a une seule ligne apres un boot sur un slot seme (les deux formes du chemin coincident)"
  else
    ko "T3a $n ligne(s) apres un boot sur un slot seme -- le bloc reecrit la ligne ecrite par git"
  fi
  # Etat de depart FIXE (alternates absent) : c'est l'idempotence du geste du
  # bloc qui est mesuree ici, pas la forme du chemin ecrit par git au semis.
  rm -f "$R/.git/objects/info/alternates"
  run_block >/dev/null 2>&1
  run_block >/dev/null 2>&1
  run_block >/dev/null 2>&1
  n="$(mirror_lines "$R")"
  if [ "$n" = "1" ]; then
    ok "T3b une seule ligne apres trois passages"
  else
    ko "T3b $n lignes dans alternates (attendu 1) -- un fichier qui grossit a chaque boot"
  fi
)
echo ""

# --- Test 4 : purge puis re-semis -----------------------------------------
echo "Test 4 : purge du clone -- le boot suivant re-seme (le retour au froid est couvert)"
(
  rm -rf "$WORK/CoursIA/CoursIA"
  out="$(run_block)"
  echo "$out" >> "$LOG"
  if [ -d "$WORK/CoursIA/CoursIA/.git" ]; then
    ok "T4 clone re-seme apres purge"
  else
    ko "T4 pas de re-semis : le slot resterait froid integralement"
  fi
  if echo "$out" | grep -q "seme depuis le miroir"; then
    ok "T4 le semis est journalise"
  else
    ko "T4 semis silencieux -- impossible a distinguer d'un no-op"
  fi
)
echo ""

# --- Test 5 : un clone sain n'est PAS re-seme (controle negatif) ------------
echo "Test 5 : clone existant -- alternates ajoute, cache #14285 preserve"
(
  R="$WORK/CoursIA/CoursIA"
  echo "travail en cours" > "$R/marqueur.txt"
  head_before="$(git -C "$R" rev-parse HEAD 2>/dev/null)"
  # Alternates retire : c'est l'etat d'un _work seme avant #18225.
  rm -f "$R/.git/objects/info/alternates"
  out="$(run_block)"
  echo "$out" >> "$LOG"
  if [ -f "$R/marqueur.txt" ]; then
    ok "T5 fichier du slot conserve (aucune purge, aucune reecriture)"
  else
    ko "T5 le slot a ete recree -- le cache de #14285 est perdu a chaque boot"
  fi
  if [ "$(git -C "$R" rev-parse HEAD 2>/dev/null)" = "$head_before" ]; then
    ok "T5 HEAD inchange (le repo du slot n'est pas reinitialise)"
  else
    ko "T5 HEAD a bouge -- le boot reecrit l'etat du slot"
  fi
  if [ "$(mirror_lines "$R")" = "1" ]; then
    ok "T5 alternates pose sur le clone existant"
  else
    ko "T5 alternates non pose sur un clone existant"
  fi
)
echo ""

# --- Test 6 : _work sans .git -- mis de cote, jamais supprime --------------
echo "Test 6 : repertoire sans .git -- ecarte avec preuve de preservation"
(
  R="$WORK/CoursIA/CoursIA"
  rm -rf "$R"
  mkdir -p "$R"
  echo "reste d'un arret brutal" > "$R/residu.txt"
  out="$(run_block)"
  echo "$out" >> "$LOG"
  if [ -d "$R/.git" ]; then ok "T6 semis effectue par-dessus le residu ecarte"; else ko "T6 pas de semis"; fi
  if grep -rq "reste d'un arret brutal" "$WORK/CoursIA/" 2>/dev/null; then
    ok "T6 le residu survit dans un repertoire .stale- (preservation prouvee)"
  else
    ko "T6 le residu a disparu -- suppression sans preuve de preservation"
  fi
)
echo ""

# --- Test 7 : miroir disparu APRES semis -- alternates pendants retires -----
echo "Test 7 : miroir disparu apres semis -- le boot suivant retire l'alternates pendant"
(
  R="$WORK/CoursIA/CoursIA"
  rm -rf "$R" "$MIRROR"
  make_mirror
  run_block > /dev/null
  # Le slot a fetche une fois (cas nominal d'un job) : il tient ses propres
  # objets, ce qui rend la mesure de `git log` concluante apres la disparition.
  git -C "$R" remote set-url origin "$TEST_DIR/src"
  git -C "$R" fetch -q origin main
  # Une ligne etrangere au miroir, pour mesurer qu'on ne retire pas tout. Elle
  # doit etre ecrite dans la forme que GIT lit sur cet hote : `git.exe` ne
  # convertit pas le contenu d'alternates, donc un `/tmp/...` y designe
  # `C:/tmp/...` et rend rc=128 a lui seul -- le test mesurerait alors sa
  # propre ecriture, pas le retrait.
  foreign="$TEST_DIR/src/.git/objects"
  if command -v cygpath >/dev/null 2>&1; then
    foreign="$(cygpath -m -- "$foreign")"
  fi
  printf '%s\n' "$foreign" >> "$R/.git/objects/info/alternates"
  before="$(mirror_lines "$R")"
  if [ "$before" = "1" ]; then
    ok "T7a alternates du miroir pose apres le semis"
  else
    ko "T7a $before ligne(s) designant le miroir"
  fi
  rm -rf "$MIRROR"
  out="$(run_block 2>&1)"
  echo "$out" >> "$LOG"
  after="$(mirror_lines "$R")"
  if [ "$after" = "0" ]; then
    ok "T7b alternates pendant retire"
  else
    ko "T7b $after ligne(s) designant le miroir disparu"
  fi
  total="$(grep -c . "$R/.git/objects/info/alternates" 2>/dev/null || printf 0)"
  if [ "$total" = "1" ]; then
    ok "T7c l'alternates etranger est conserve"
  else
    ko "T7c $total ligne(s) restantes (attendu 1, l'etrangere)"
  fi
  if git -C "$R" log --oneline -1 >/dev/null 2>&1; then
    ok "T7d git log rc=0 apres retrait"
  else
    ko "T7d git log encore casse apres retrait"
  fi
  if echo "$out" | grep -q "alternates pendant retire"; then
    ok "T7e le retrait est journalise"
  else
    ko "T7e retrait silencieux -- l'operateur ne saurait pas ce qui a change"
  fi
)
echo ""

# --- Test 8 : alternates par l'ENVIRONNEMENT (mission ai-01 26/10, #18225) ---
echo "Test 8 : GIT_ALTERNATE_OBJECT_DIRECTORIES -- posee avec miroir, absente sinon"
(
  # Le contrat mesure ici est celui du VRAI entrypoint : le bloc s'execute dans
  # le processus qui lancera ENSUITE le runner, donc un `export` du bloc doit
  # atteindre ce runner. `run_block` lance un fils -- un fils ne propage jamais
  # son env vers le pere -- donc la sonde SOURCE le bloc dans un sous-shell et
  # lit la variable au MEME endroit : c'est la seule forme qui mesure la
  # propagation, pas la definition.
  probe_env() {
    (
      . "$TEST_DIR/block.sh" >/dev/null 2>&1
      printf '%s' "${GIT_ALTERNATE_OBJECT_DIRECTORIES-UNSET}"
    )
  }
  # T8a : le Test 7 vient de supprimer le miroir -- cas absent d'abord, sans
  # le recreer : la sonde mirror_present doit laisser la variable hors env
  # (fail-open). C'est le controle OBLIGATOIRE de la mission : un chemin
  # d'alternates absent fait echouer toute operation git (mesure :
  # `unable to normalize alternate object path`), donc exporter sans sonde
  # casserait les hotes sans miroir.
  v="$(probe_env)"
  if [ "$v" = "UNSET" ]; then
    ok "T8a miroir absent : variable ABSENTE (fail-open, comportement d'avant #18225)"
  else
    ko "T8a miroir absent : variable posee a '$v' -- un hote sans miroir casserait"
  fi
  # T8b : miroir present -> la variable designe SES objets. Le bloc la construit
  # depuis MIRROR_PATH lui-meme, donc l'egalite litterale ne depend pas de la
  # forme du chemin sur cet hote.
  make_mirror
  v="$(probe_env)"
  if [ "$v" = "$MIRROR/objects" ]; then
    ok "T8b miroir present : variable posee au processus ($v)"
  else
    ko "T8b attendu '$MIRROR/objects', obtenu '${v:-vide}'"
  fi
  # T8c : une valeur DEJA presente n'est pas ecrasee -- le miroir est ajoute en
  # TETE, l'existant est conserve en queue (un operateur qui poserait son
  # propre alternates garde son reglage).
  v="$(
    GIT_ALTERNATE_OBJECT_DIRECTORIES=/tmp/autre-objects probe_env
  )"
  if [ "$v" = "$MIRROR/objects:/tmp/autre-objects" ]; then
    ok "T8c valeur preexistante conservee (ajoutee en tete, pas ecrasee)"
  else
    ko "T8c attendu '$MIRROR/objects:/tmp/autre-objects', obtenu '${v:-vide}'"
  fi
)
echo ""

# --- Verdict agrege --------------------------------------------------------
n_pass="$(grep -c '^PASS' "$RESULTS" || true)"
n_fail="$(grep -c '^FAIL' "$RESULTS" || true)"
echo "============================================================"
echo "entrypoint miroir d'objets (#18225) : $n_pass PASS, $n_fail FAIL"
echo "============================================================"
if [ "$n_fail" -gt 0 ]; then
  echo "(logs: $LOG)"
  exit 1
fi
if [ "$n_pass" -eq 0 ]; then
  echo "ERREUR: aucune assertion executee -- le harnais n'a rien mesure." >&2
  exit 2
fi
rm -rf "$TEST_DIR"
exit 0
