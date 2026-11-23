#!/usr/bin/env bash
# Test du script de creation des slots persist po-2024 (#21978, volet 3).
#
# CE QUE CE TEST PROUVE
# ---------------------
#  1. Le mode `--dry-run` n'execute AUCUNE creation et imprime les caps et
#     les labels attendus (cpus 3 / 4g / 512 / `coursia-persistent` sans
#     `coursia-ephemeral`).
#  2. Le script NE SUPPRIME JAMAIS un slot : ni `docker rm`, ni `docker stop`,
#     ni `docker kill`, ni les formes `docker container rm|stop|kill`, dans sa
#     source (contrainte de l'issue : « aucune suppression de slot en cours de
#     job »).
#  3. Le mode `--check` signale un slot absent (code 1) et nomme la derive,
#     au lieu de la tolerer en silence.
#  4. Le mode `--check` accepte un slot CONFORME (caps et labels exacts) et
#     signale une derive de cap cpus.
#
# Le test utilise un `docker` STUB (un script qui fait comme si aucun
# conteneur n'existait, puis un second qui simule un slot conforme) : il ne
# touche ni la machine ni ses runners.
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

# --- stub docker : un slot conforme existe (memoire 4g, pids 512, cpus 3) --
TMP2="${TMP}/with-slot"
mkdir -p "$TMP2"
cat > "$TMP2/docker" <<'STUB'
#!/usr/bin/env bash
# stub : un slot existe ; son etat (memoire/pids/cpus/running) est pilote par
# `PERSIST_STUB_STATE`, ses labels par `PERSIST_STUB_LABELS`.
fmt=""
prev=""
for arg in "$@"; do
  if [ "$prev" = "--format" ]; then fmt="$arg"; fi
  prev="$arg"
done
case "$fmt" in
  *NanoCpus*) printf '%s\n' "${PERSIST_STUB_STATE:-4294967296 512 3000000000 true}" ;;
  *Config.Env*) printf '%s\n' "ACTIONS_RUNNER_INPUT_LABELS=${PERSIST_STUB_LABELS:-self-hosted,coursia-persistent,coursia-linux}" ;;
esac
exit 0
STUB
chmod +x "$TMP2/docker"

# --- 1. le mode dry-run imprime la specification, sans creer ---------------
out="$(PATH="$TMP:$PATH" "$SCRIPT" --dry-run 2>&1)"
rc=$?

if [ "$rc" -eq 0 ]; then
  ok "--dry-run se termine en 0"
else
  ko "--dry-run se termine en $rc (attendu 0)"
fi

for attendu in "--cpus=3" "--memory=4g" "--pids-limit=512" "coursia-persistent" "RUNNER_MODE=persistent" \
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
# Le garde couvre les formes directes (`docker rm|stop|kill`) ET les formes
# avec le sous-commande `container` (`docker container rm|stop|kill`).
if grep -nE "docker[[:space:]]+(container[[:space:]]+)?(rm|stop|kill)" "$SCRIPT" >/dev/null 2>&1; then
  ko "la source du script contient une suppression de slot (docker rm/stop/kill, docker container rm/stop/kill)"
  grep -nE "docker[[:space:]]+(container[[:space:]]+)?(rm|stop|kill)" "$SCRIPT" | sed 's/^/    /'
else
  ok "la source du script ne contient aucune suppression de slot (ni docker rm/stop/kill, ni docker container rm/stop/kill)"
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

# --- 4. le mode check accepte un slot conforme et detecte une derive cpus --
out_ok="$(PATH="$TMP2:$PATH" "$SCRIPT" --check 2>&1)"
rc_ok=$?
if [ "$rc_ok" -eq 0 ]; then
  ok "--check sort en 0 sur un slot conforme (caps et labels exacts)"
else
  ko "--check sort en $rc_ok sur un slot conforme (attendu 0)"
  printf '%s\n' "$out_ok" | sed 's/^/    /'
fi
if printf '%s' "$out_ok" | grep -qF "OK : les 2 slots persist sont conformes"; then
  ok "--check annonce la conformite quand tout est exact"
else
  ko "--check n'annonce pas la conformite"
  printf '%s\n' "$out_ok" | sed 's/^/    /'
fi

out_cpus="$(PATH="$TMP2:$PATH" PERSIST_STUB_STATE="4294967296 512 0 true" "$SCRIPT" --check 2>&1)"
rc_cpus=$?
if [ "$rc_cpus" -eq 1 ]; then
  ok "--check sort en 1 quand le cap cpus derive"
else
  ko "--check sort en $rc_cpus (attendu 1 : cap cpus non conforme)"
fi
if printf '%s' "$out_cpus" | grep -q "cap cpus attendu"; then
  ok "--check nomme la derive du cap cpus"
else
  ko "--check ne nomme pas la derive du cap cpus"
  printf '%s\n' "$out_cpus" | sed 's/^/    /'
fi

# --- 5. un slot ARRETE est une derive (point 1 du crible #21985) ------------
# `running=false` : les caps et les labels sont conformes, mais le slot ne peut
# pas executer de job. `--check` doit donc sortir en 1 et nommer la derive.
out_stopped="$(PATH="$TMP2:$PATH" PERSIST_STUB_STATE="4294967296 512 3000000000 false" "$SCRIPT" --check 2>&1)"
rc_stopped=$?
if [ "$rc_stopped" -eq 1 ]; then
  ok "--check sort en 1 quand un slot present est arrete"
else
  ko "--check sort en $rc_stopped (attendu 1 : slot arrete = derive)"
  printf '%s\n' "$out_stopped" | sed 's/^/    /'
fi
if printf '%s' "$out_stopped" | grep -q "slot attendu en marche"; then
  ok "--check nomme la derive de l'etat de marche"
else
  ko "--check ne nomme pas la derive de l'etat de marche"
  printf '%s\n' "$out_stopped" | sed 's/^/    /'
fi

# --- 6. le nombre de slots est parametrable --------------------------------
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
