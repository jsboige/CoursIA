#!/usr/bin/env bash
# Test du script de creation des slots persist po-2024 (#21978, volet 3).
#
# CE QUE CE TEST PROUVE
# ---------------------
#  1. Le mode `--dry-run` n'execute AUCUNE creation et imprime les caps et
#     les labels attendus (4g / 512 / `coursia-persistent` sans
#     `coursia-ephemeral`).
#  2. Le script NE SUPPRIME JAMAIS un slot : ni `docker rm`, ni `docker stop`,
#     ni `docker kill` dans sa source (contrainte de l'issue : « aucune
#     suppression de slot en cours de job »).
#  3. Le mode `--check` signale un slot absent (code 1) et nomme la derive,
#     au lieu de la tolerer en silence.
#
# Le test utilise un `docker` STUB (un script qui fait comme si aucun
# conteneur n'existait) : il ne touche ni la machine ni ses runners.
set -u

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT="${HERE}/create-persist-slots.sh"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fails=0
ok()   { printf 'OK   : %s\n' "$1"; }
ko()   { printf 'ECHEC: %s\n' "$1"; fails=$((fails + 1)); }

# --- stub docker : aucun conteneur n'existe --------------------------------
cat > "$TMP/docker" <<'STUB'
#!/usr/bin/env bash
# stub : `inspect` -> absent (code 1), tout le reste -> no-op silencieux
for arg in "$@"; do
  if [ "$arg" = "inspect" ]; then exit 1; fi
done
exit 0
STUB
chmod +x "$TMP/docker"

# --- 1. le mode dry-run imprime la specification, sans creer ---------------
out="$(PATH="$TMP:$PATH" "$SCRIPT" --dry-run 2>&1)"
rc=$?

if [ "$rc" -eq 0 ]; then
  ok "--dry-run se termine en 0"
else
  ko "--dry-run se termine en $rc (attendu 0)"
fi

for attendu in "--memory=4g" "--pids-limit=512" "coursia-persistent" "RUNNER_MODE=persistent" \
               "myia-po-2024-linux-persist-1" "myia-po-2024-linux-persist-2" "coursia-ci.slice"; do
  if printf '%s' "$out" | grep -qF -- "$attendu"; then
    ok "--dry-run contient '$attendu'"
  else
    ko "--dry-run ne contient pas '$attendu'"
  fi
done

if printf '%s' "$out" | grep -qF "coursia-ephemeral"; then
  ko "--dry-run mentionne 'coursia-ephemeral' (les labels de famille doivent etre disjoints)"
else
  ok "--dry-run ne mentionne pas 'coursia-ephemeral' (labels disjoints)"
fi

if printf '%s' "$out" | grep -qi "DRY-RUN" && printf '%s' "$out" | grep -qi "Aucun conteneur"; then
  ok "--dry-run annonce qu'aucun conteneur n'a ete cree"
else
  ko "--dry-run n'annonce pas explicitement l'absence de creation"
fi

# --- 2. le script ne supprime jamais un slot -------------------------------
if grep -nE "docker[[:space:]]+(rm|stop|kill)" "$SCRIPT" >/dev/null 2>&1; then
  ko "la source du script contient une suppression de slot (docker rm/stop/kill)"
  grep -nE "docker[[:space:]]+(rm|stop|kill)" "$SCRIPT" | sed 's/^/    /'
else
  ok "la source du script ne contient aucune suppression de slot"
fi

# --- 3. le mode check signale un slot absent -------------------------------
out_check="$(PATH="$TMP:$PATH" "$SCRIPT" --check 2>&1)"
rc_check=$?
if [ "$rc_check" -eq 1 ]; then
  ok "--check sort en 1 quand un slot est absent"
else
  ko "--check sort en $rc_check (attendu 1 : slot absent = derive)"
fi
if printf '%s' "$out_check" | grep -qF "ABSENT"; then
  ok "--check nomme le slot absent"
else
  ko "--check ne nomme pas le slot absent"
fi
if printf '%s' "$out_check" | grep -qi "DERIVE"; then
  ok "--check nomme la derive"
else
  ko "--check ne nomme pas la derive"
fi

# --- 4. le nombre de slots est parametrable --------------------------------
out2="$(PATH="$TMP:$PATH" COURSIA_PERSIST_SLOTS=3 "$SCRIPT" --dry-run 2>&1)"
if printf '%s' "$out2" | grep -qF "myia-po-2024-linux-persist-3"; then
  ok "COURSIA_PERSIST_SLOTS=3 cree un troisieme slot prevu"
else
  ko "COURSIA_PERSIST_SLOTS=3 ne prevoyait pas de troisieme slot"
fi

printf '\n'
if [ "$fails" -eq 0 ]; then
  printf 'TOUS LES TESTS PASSENT\n'
  exit 0
fi
printf '%d TEST(S) EN ECHEC\n' "$fails"
exit 1
