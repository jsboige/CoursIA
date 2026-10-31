#!/usr/bin/env bash
# Banc de la resolution POOL_SIZE du pool natif po-2026 (pool.sh, Q17/persistence).
# On extrait le BLOC de resolution du VRAI pool.sh (depuis `POOL_SIZE=` jusqu'au
# premier `esac`) et on le source sous des env/HOME controles. Le bloc est la seule
# piece qu'on teste : lancer le pool entier demarrerait 8 slots.
#
# Ce que le banc doit separer : « le fichier conf est lu » et « il est IGNORE »
# rendent le meme rc=0 — seul POOL_SIZE APRES resolution discrimine.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/pool-size-test-$$"
mkdir -p "$TEST_DIR/home"

RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# Extraction du bloc : de la ligne POOL_SIZE= au premier esac qui la suit.
awk '/^POOL_SIZE=/{grab=1} grab{print} grab && /^esac$/{exit}' \
  "$SCRIPT_DIR/pool.sh" > "$TEST_DIR/block.sh"
[ -s "$TEST_DIR/block.sh" ] || { echo "bloc de resolution introuvable dans pool.sh"; exit 1; }
grep -q '^esac$' "$TEST_DIR/block.sh" || { echo "bloc incomplet (pas de esac)"; exit 1; }

# resolve <nom-de-cas> : prepare home/<cas> (conf eventuelle) + env POOL_SIZE
# eventuel, source le bloc, rend RESOLVED.
resolve() { # $1 = conf content ou "none" ; $2 = env POOL_SIZE ou "unset"
  local conf="$1" envps="$2"
  rm -rf "$TEST_DIR/home/CoursIA-runners-p0"
  mkdir -p "$TEST_DIR/home/CoursIA-runners-p0"
  [ "$conf" != "none" ] && printf '%s\n' "$conf" > "$TEST_DIR/home/CoursIA-runners-p0/pool-size.conf"
  RESOLVED="$(POOL_SIZE_VALUE="$envps" bash -c '
    [ "$POOL_SIZE_VALUE" = unset ] && unset POOL_SIZE || export POOL_SIZE="$POOL_SIZE_VALUE"
    export HOME="'"$TEST_DIR"'/home"
    source "'"$TEST_DIR"'/block.sh"
    echo "$POOL_SIZE"')"
}

echo "== banc de la resolution POOL_SIZE (pool natif po-2026) =="

resolve 3 unset
[ "$RESOLVED" = "3" ] && ok "conf=3, env absent -> 3 (le confinement survit au redemarrage)" \
  || ko "conf=3, env absent -> '$RESOLVED' (attendu 3)"

resolve 3 5
[ "$RESOLVED" = "5" ] && ok "conf=3, env=5 -> 5 (l'env explicite garde la priorite)" \
  || ko "conf=3, env=5 -> '$RESOLVED' (attendu 5)"

resolve none unset
[ "$RESOLVED" = "8" ] && ok "sans conf ni env -> 8 (defaut historique)" \
  || ko "sans conf ni env -> '$RESOLVED' (attendu 8)"

resolve abc unset
[ "$RESOLVED" = "8" ] && ok "conf pourrie (abc) -> 8, jamais acceptee" \
  || ko "conf abc -> '$RESOLVED' (attendu 8)"

resolve 0 unset
[ "$RESOLVED" = "8" ] && ok "conf 0 (hors bornes) -> 8" \
  || ko "conf 0 -> '$RESOLVED' (attendu 8)"

resolve 9 unset
[ "$RESOLVED" = "8" ] && ok "conf 9 (hors bornes) -> 8" \
  || ko "conf 9 -> '$RESOLVED' (attendu 8)"

resolve none 42
[ "$RESOLVED" = "8" ] && ok "env 42 (hors bornes) -> 8" \
  || ko "env 42 -> '$RESOLVED' (attendu 8)"

# Fichier sans newline final : read rend 1 APRES avoir peuple la variable.
rm -rf "$TEST_DIR/home/CoursIA-runners-p0"; mkdir -p "$TEST_DIR/home/CoursIA-runners-p0"
printf '3' > "$TEST_DIR/home/CoursIA-runners-p0/pool-size.conf"
RESOLVED="$(bash -c 'unset POOL_SIZE; export HOME="'"$TEST_DIR"'/home"; source "'"$TEST_DIR"'/block.sh"; echo "$POOL_SIZE"')"
[ "$RESOLVED" = "3" ] && ok "conf 3 sans newline final -> 3 (le read echouant apres peuplement n'efface pas)" \
  || ko "conf 3 sans newline -> '$RESOLVED' (attendu 3)"

PASSES=$(grep -c '^PASS ' "$RESULTS")
FAILS=$(grep -c '^FAIL ' "$RESULTS")
echo
echo "== $PASSES PASS / $FAILS FAIL =="
rm -rf "$TEST_DIR"
[ "$FAILS" -eq 0 ]
