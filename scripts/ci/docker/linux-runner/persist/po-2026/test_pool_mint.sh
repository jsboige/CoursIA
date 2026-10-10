#!/usr/bin/env bash
# Banc du mint de registration token du pool natif po-2026 (pool.sh, #15154 porte
# au parc natif). On execute le VRAI pool.sh en mode sonde (POOL_PROBE=mint-token)
# avec un stub `gh.exe` en tete de PATH, et on lit le nombre d'appels du stub.
#
# Pourquoi le nombre d'appels est la mesure qui compte : « a retente » et « n'a pas
# retente » rendent le meme rc sur une panne transitoire qui finit par reussir. Seul
# le compteur les separe — et il vit dans un FICHIER, pas dans une variable shell :
# chaque invocation du stub est un processus, un compteur en variable serait remis a
# zero a chaque appel (meme piege que #15091, ou le verdict etait perdu par le
# sous-shell des tests).

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_DIR="/tmp/pool-mint-test-$$"
mkdir -p "$TEST_DIR/bin" "$TEST_DIR/home"
LOG="$TEST_DIR/probe.log"
: > "$LOG"

# Verdict dans un FICHIER (cf. test_supervise_guards.sh) : un `ko` doit faire
# sortir non-zero, sinon le harnais est vert a jamais.
RESULTS="$TEST_DIR/results"
: > "$RESULTS"
ok() { echo "  PASS: $1"; echo "PASS $1" >> "$RESULTS"; }
ko() { echo "  FAIL: $1"; echo "FAIL $1" >> "$RESULTS"; }

# --- Stub gh.exe -------------------------------------------------------------
# STUB_GH_MODE choisit la reponse ; STUB_GH_COUNT comptabilise les appels.
# `empty` reproduit la panne dominante mesuree le 2026-10-07 (305/310 echecs) :
# l'interop WSL -> gh.exe qui expire (UtilAcceptVsock accept4 failed 110) ne rend
# RIEN du tout — pas un code d'erreur, pas un octet.
cat > "$TEST_DIR/bin/gh.exe" <<'STUB'
#!/usr/bin/env bash
n=$(cat "$STUB_GH_COUNT" 2>/dev/null || echo 0)
n=$((n + 1))
echo "$n" > "$STUB_GH_COUNT"
case "${STUB_GH_MODE:-ok}" in
  ok)        echo "STUBTOKEN0000000000000000001"; exit 0 ;;
  empty)     exit 1 ;;
  fail1)     [ "$n" -le 1 ] && exit 1; echo "STUBTOKEN0000000000000000002"; exit 0 ;;
  fail2)     [ "$n" -le 2 ] && exit 1; echo "STUBTOKEN0000000000000000003"; exit 0 ;;
  http403)   echo "HTTP 403: You must have repository read permissions (https://api.github.com/repos/x/actions/runners/registration-token)" >&2; exit 1 ;;
  badcreds)  echo "HTTP 401: Bad credentials (https://api.github.com/)" >&2; exit 1 ;;
  http500)   echo "HTTP 500: Internal Server Error" >&2; exit 1 ;;
  *)         echo "mode inconnu: $STUB_GH_MODE" >&2; exit 9 ;;
esac
STUB
chmod +x "$TEST_DIR/bin/gh.exe"

# probe <mode> <tentatives> — execute la sonde et rend rc / stdout / journal / appels.
# HOME est detourne : pool.sh fait `mkdir -p "$HOME/CoursIA-runners-p0"` des ses
# premieres lignes, le banc ne doit pas ecrire dans le vrai repertoire du parc.
probe() {
  local mode="$1" attempts="${2:-4}"
  export STUB_GH_MODE="$mode" STUB_GH_COUNT="$TEST_DIR/count"
  echo 0 > "$STUB_GH_COUNT"
  POOL_PROBE=mint-token MINT_ATTEMPTS="$attempts" HOME="$TEST_DIR/home" \
    PATH="$TEST_DIR/bin:$PATH" bash "$SCRIPT_DIR/pool.sh" > "$LOG" 2>&1
  PROBE_RC=$?
  PROBE_CALLS=$(cat "$STUB_GH_COUNT")
  # `{19}` et non `+` : mint_token rend le token SANS saut de ligne (forme de
  # l'original), donc il se colle a la ligne de sonde qui suit — une classe
  # ouverte avalait alors les chiffres de l'horodatage (« STUBTOKEN…00012026 »).
  # La borne vient de la longueur du token du stub, defini plus haut dans ce
  # fichier : les deux doivent bouger ensemble.
  PROBE_TOKEN=$(grep -m1 -oE 'STUBTOKEN[0-9]{19}' "$LOG" || true)
}

echo "== banc du mint de token (pool natif po-2026) =="

# --- 1. Controle nominal : un token rendu du premier coup ---------------------
probe ok 4
if [ "$PROBE_RC" -eq 0 ] && [ "$PROBE_TOKEN" = "STUBTOKEN0000000000000000001" ] && [ "$PROBE_CALLS" -eq 1 ]; then
  ok "token nominal : rc=0, le token ATTENDU est rendu, 1 appel"
else
  ko "token nominal (rc=$PROBE_RC appels=$PROBE_CALLS token='$PROBE_TOKEN')"
fi

# --- 2. 403 : structurel, TERMINAL, aucun retry ------------------------------
probe http403 4
if [ "$PROBE_RC" -ne 0 ] && grep -q "TERMINAL" "$LOG" && [ "$PROBE_CALLS" -eq 1 ]; then
  ok "403 terminal : rc!=0, nomme TERMINAL, 1 SEUL appel (pas de retry)"
else
  ko "403 terminal (rc=$PROBE_RC appels=$PROBE_CALLS) : $(grep -c TERMINAL "$LOG") ligne(s) TERMINAL"
fi

# --- 3. 401 Bad credentials : structurel aussi --------------------------------
probe badcreds 4
if [ "$PROBE_RC" -ne 0 ] && grep -q "TERMINAL" "$LOG" && [ "$PROBE_CALLS" -eq 1 ]; then
  ok "401 Bad credentials : terminal, 1 SEUL appel"
else
  ko "401 Bad credentials (rc=$PROBE_RC appels=$PROBE_CALLS)"
fi

# --- 4. Controle positif : transitoire qui finit par reussir ------------------
# C'est LE cas de production : une expiration vsock isolee ne doit plus couter
# un cycle de slot. Avant ce correctif, le slot etait rendu des le 1er hoquet.
probe fail1 4
if [ "$PROBE_RC" -eq 0 ] && [ "$PROBE_TOKEN" = "STUBTOKEN0000000000000000002" ] && [ "$PROBE_CALLS" -eq 2 ]; then
  ok "transitoire isole : retente et reussit (2 appels) — le slot n'est plus perdu"
else
  ko "transitoire isole (rc=$PROBE_RC appels=$PROBE_CALLS token='$PROBE_TOKEN')"
fi

# --- 5. Interop muette (la panne dominante) : retentee, pas abandonnee --------
probe fail2 4
if [ "$PROBE_RC" -eq 0 ] && [ "$PROBE_TOKEN" = "STUBTOKEN0000000000000000003" ] && [ "$PROBE_CALLS" -eq 3 ]; then
  ok "deux hoquets puis succes : 3 appels (panne dominante couverte)"
else
  ko "deux hoquets puis succes (rc=$PROBE_RC appels=$PROBE_CALLS)"
fi

# --- 6. Sortie vide permanente : retente jusqu'au plafond, puis abandonne ----
# `empty` ne rend aucun octet : c'est la signature d'UtilAcceptVsock. Le budget
# est borne (MINT_ATTEMPTS), le pool ne boucle pas indefiniment dessus.
probe empty 3
if [ "$PROBE_RC" -ne 0 ] && [ "$PROBE_CALLS" -eq 3 ] && grep -q "sortie vide" "$LOG"; then
  ok "interop muette : 3 tentatives bornees, cause nommee, rc!=0"
else
  ko "interop muette (rc=$PROBE_RC appels=$PROBE_CALLS)"
fi

# --- 7. 5xx : transitoire, borne, et le journal nomme la cause ---------------
probe http500 3
if [ "$PROBE_RC" -ne 0 ] && [ "$PROBE_CALLS" -eq 3 ] \
   && grep -q "transitoire" "$LOG" && grep -q "epuise" "$LOG"; then
  ok "500 transitoire : 3 tentatives, journal nomme transitoire + epuise"
else
  ko "500 transitoire (rc=$PROBE_RC appels=$PROBE_CALLS)"
fi

# --- 8. Garde : un 403 ne doit JAMAIS rallonger la panne ---------------------
# Si la classification regressait (403 classe transitoire), le pool perdrait
# 3 x plus de temps par hoquet structurel — et bouclerait comme avant #15154.
probe http403 4
if [ "$PROBE_CALLS" -le 1 ]; then
  ok "garde anti-regression : un structurel ne consomme pas le budget de retry"
else
  ko "garde anti-regression : $PROBE_CALLS appels sur un 403"
fi

PASSES=$(grep -c '^PASS ' "$RESULTS")
FAILS=$(grep -c '^FAIL ' "$RESULTS")
echo
echo "== $PASSES PASS / $FAILS FAIL =="
rm -rf "$TEST_DIR"
[ "$FAILS" -eq 0 ]
