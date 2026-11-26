#!/usr/bin/env bash
# Banc du magasin d'objets partage du pool natif po-2026 (pool.sh, #18225 maillon 3).
# On execute le VRAI pool.sh en mode sonde (POOL_PROBE=mirror-refresh|seed|alternates)
# sur un mini-miroir local : un repo source a deux commits joue le remote, le miroir
# bare est sa clone, et MIRROR_REMOTE est detourne dessus — le banc ne touche JAMAIS
# le reseau ni le vrai $BASE (HOME redirige, comme test_pool_mint.sh).
#
# Ce que le banc doit separer : « le semis marche » et « le semis ne fait rien quand
# le miroir est absent » rendent le meme rc=0. Le discriminant est l'ETAT laissent
# les sondes : fichier alternates ecrit (une seule fois), origin rebascule sur
# MIRROR_REMOTE, objets resolvables SANS checkout, miroir qui gagne le commit du
# remote apres refresh.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/pool-alternates-test-$$"
mkdir -p "$TEST_DIR/home"
BASE="$TEST_DIR/home/CoursIA-runners-p0"
MIRROR="$BASE/objects-mirror.git"
LOG="$TEST_DIR/probe.log"

# Verdict dans un FICHIER (cf. test_pool_mint.sh) : un `ko` doit faire sortir
# non-zero, sinon le harnais est vert a jamais.
RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

G() { git -c user.email=banc@pool -c user.name=banc "$@"; }

probe() { # $1 = nom de sonde — execute pool.sh, rend PROBE_RC, journal dans $LOG
  POOL_PROBE="$1" HOME="$TEST_DIR/home" MIRROR_REMOTE="$TEST_DIR/src" \
    bash "$SCRIPT_DIR/pool.sh" > "$LOG" 2>&1
  PROBE_RC=$?
}

# --- Terrain : remote a deux commits, miroir bare pose au premier -------------
mkdir -p "$TEST_DIR/src"
G -C "$TEST_DIR/src" init -q -b main
G -C "$TEST_DIR/src" commit -q --allow-empty -m c1
mkdir -p "$BASE"
git clone --bare --quiet "$TEST_DIR/src" "$MIRROR"
C1=$(G -C "$TEST_DIR/src" rev-parse HEAD)
# Le remote avance APRES la pose du miroir : c2 n'est PAS encore dans le miroir.
G -C "$TEST_DIR/src" commit -q --allow-empty -m c2
C2=$(G -C "$TEST_DIR/src" rev-parse HEAD)

echo "== banc du magasin d'objets partage (pool natif po-2026) =="

# --- 1. mirror-refresh : le miroir gagne le commit du remote ------------------
probe mirror-refresh
if [ "$PROBE_RC" -eq 0 ] && git --git-dir="$MIRROR" cat-file -e "$C2^{commit}" 2>/dev/null \
   && grep -q "miroir rafraichi" "$LOG"; then
  ok "refresh : le commit c2 (postérieur à la pose) entre dans le miroir, journal nomme le refresh"
else
  ko "refresh (rc=$PROBE_RC, c2 present: $(git --git-dir="$MIRROR" cat-file -e "$C2^{commit}" 2>/dev/null && echo oui || echo non))"
fi

# --- 2. seed : repo pre-materialise, alternates vers le miroir, origin HTTPS --
probe seed
SEEDED="$BASE/slot-probe/_work/CoursIA/CoursIA"
if [ "$PROBE_RC" -eq 0 ] && [ -d "$SEEDED/.git" ] \
   && grep -qxF "$MIRROR/objects" "$SEEDED/.git/objects/info/alternates" 2>/dev/null \
   && [ "$(git -C "$SEEDED" remote get-url origin)" = "$TEST_DIR/src" ]; then
  ok "seed : _work/CoursIA/CoursIA cloné --shared, alternates vers le miroir, origin rebasculé sur MIRROR_REMOTE"
else
  ko "seed (rc=$PROBE_RC, alternates: $(cat "$SEEDED/.git/objects/info/alternates" 2>/dev/null | tr '\n' '|'), origin: $(git -C "$SEEDED" remote get-url origin 2>/dev/null))"
fi

# --- 3. seed : les objets sont resolvables SANS checkout ni reseau ------------
# C'est la promesse du semis : checkout@v4 materialisera depuis des objets DEJA
# locaux (via alternates). Si cat-file echoue, le semis n'a servi a rien.
if git -C "$SEEDED" cat-file -e "$C2^{commit}" 2>/dev/null; then
  ok "seed : HEAD du miroir résolvable dans le repo semé (objets atteints via alternates)"
else
  ko "seed : objet $C2 non résolvable dans le repo semé"
fi

# --- 4. alternates : idempotent, exactement une ligne --------------------------
mkdir -p "$BASE/probe-warm/CoursIA/CoursIA"
G -C "$BASE/probe-warm/CoursIA/CoursIA" init -q -b main
G -C "$BASE/probe-warm/CoursIA/CoursIA" commit -q --allow-empty -m warm
probe alternates; probe alternates   # deux fois : l'idempotence est le contrat
LINES=$(grep -cxF "$MIRROR/objects" "$BASE/probe-warm/CoursIA/CoursIA/.git/objects/info/alternates" 2>/dev/null || echo 0)
if [ "$PROBE_RC" -eq 0 ] && [ "$LINES" -eq 1 ]; then
  ok "alternates : posé une fois, pas dupliqué au 2e appel (repo chaud gardé intact)"
else
  ko "alternates (rc=$PROBE_RC, lignes miroir: $LINES)"
fi

# --- 5. fail-open : miroir absent => les sondes ne font RIEN, rc=0 -------------
rm -rf "$TEST_DIR/home2"; mkdir -p "$TEST_DIR/home2"
POOL_PROBE=seed HOME="$TEST_DIR/home2" bash "$SCRIPT_DIR/pool.sh" > "$LOG" 2>&1
NORC=$?
if [ "$NORC" -eq 0 ] && [ ! -d "$TEST_DIR/home2/CoursIA-runners-p0/slot-probe/_work" ]; then
  ok "fail-open : sans miroir, seed rend rc=0 et ne crée rien (parc nominal d'avant)"
else
  ko "fail-open (rc=$NORC, _work créé: $([ -d "$TEST_DIR/home2/CoursIA-runners-p0/slot-probe/_work" ] && echo oui || echo non))"
fi

PASSES=$(grep -c '^PASS ' "$RESULTS")
FAILS=$(grep -c '^FAIL ' "$RESULTS")
echo
echo "== $PASSES PASS / $FAILS FAIL =="
rm -rf "$TEST_DIR"
[ "$FAILS" -eq 0 ]
