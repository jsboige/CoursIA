#!/usr/bin/env bash
# Harnais du GARDE DE LIEN FACTURE (#28916).
#
# LE DEFAULT QUE CE HARNAIS EMPECHE (mesure po-2027, 27/11 18:02Z) : sur un
# lien facture (partage USB du telephone), les runners CI ont tourne environ
# 45 min et consomme 3,6 Go -- debit hote 52,23 MiB/min, RX 2 859,4 MiB a
# 17:50:16Z puis 3 589,2 MiB a 17:56:31Z. Trois defauts distincts :
#   1. le verdict n'etait rendu qu'AU DEMARRAGE (branche LAUNCH prise deux
#      fois a 17:06:53Z, 86 s apres le boot) ; le test rendait BILLED a 17:46Z
#      puis 17:59Z sans que personne le relise ;
#   2. le holder contournait `systemctl disable` : hold-runner.ps1 lance
#      lui-meme `systemctl start coursia-runner` (lignes 33 et 40) ;
#   3. un verdict BILLED n'arretait rien : un SKIP empeche un lancement, il
#      ne stoppe pas un runner deja en marche.
#
# LES TROIS CAS COUVERTS ICI, tous en dry-run :
#   cas 1 -- le lancement est REFUSE sur un verdict BILLED (et sur UNKNOWN) ;
#   cas 2 -- la veille, deja en route, ARRETE l'unite et sa slice quand le
#            verdict bascule en BILLED ;
#   cas 3 -- le holder respecte le verdict : sur BILLED, il ne lance pas le
#            service (le stub wsl n'est pas appele).
#
# Chaque cas a un CONTROLE : une variante qui doit passer. Un garde qui
# refuse tout ne prouverait rien -- c'est ce que le harnais reproche aux
# autres (le cas « aucun superviseur vivant » du harnais de sentinelle).
#
# Aucun service reel n'est arrete, aucune unite n'est demarree, aucun contrat
# publie n'est appele : la sonde est un STUB local, le wsl.exe est un STUB
# local, et le systeme n'est jamais sollicite.
#
# Usage : bash scripts/ci/docker/linux-runner/persist/test_link_verdict_guard.sh
# Sortie : "N PASS / M FAIL / K SKIP", rc=0 si M==0.
set -uo pipefail

ICI="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

: >"$TMP/pass"; : >"$TMP/fail"; : >"$TMP/skip"
ok() { echo "$1" >>"$TMP/pass"; echo "  PASS $1"; }
ko() { echo "$1" >>"$TMP/fail"; echo "  FAIL $1"; }
skip() { echo "$1" >>"$TMP/skip"; echo "  SKIP $1"; }

# --- STUBS DE SONDE -------------------------------------------------------
# Un stub imite le contrat publie : il imprime UNE ligne dont le premier mot
# est le verdict, et rend le code de sortie correspondant.
fabrique_verdict() {  # <fichier> <mot> <code> [detail]
  cat >"$1" <<EOF
#!/usr/bin/env bash
echo "$2 ${4:-reason=stub}"
exit $3
EOF
  chmod +x "$1"
}

fabrique_verdict "$TMP/v-unbilled.sh" UNBILLED 0 "reason=adapter=test cost=Unrestricted"
fabrique_verdict "$TMP/v-billed.sh" BILLED 3 "reason=adapter=test-hotshot cost=Metered"
fabrique_verdict "$TMP/v-unknown.sh" UNKNOWN 4 "reason=probe-failed"
# Desaccord entre le mot et le code de sortie : la sonde se contredit. Le
# lecteur doit alors rendre UNKNOWN (jamais « va » suppose).
fabrique_verdict "$TMP/v-incoherent.sh" BILLED 0 "reason=adapter=test"

# La sonde qui bascule : UNBILLED au premier tour, BILLED ensuite.
cat >"$TMP/v-bascule.sh" <<EOF
#!/usr/bin/env bash
c=\$(cat "$TMP/compteur" 2>/dev/null || echo 0)
c=\$((c + 1)); echo "\$c" > "$TMP/compteur"
if [ "\$c" -ge 2 ]; then echo "BILLED reason=bascule"; exit 3; fi
echo "UNBILLED reason=encore"; exit 0
EOF
chmod +x "$TMP/v-bascule.sh"

# --- CAS 1 : LANCEMENT REFUSE --------------------------------------------
echo "cas 1 -- la porte refuse un lancement sur lien facture"

sortie="$(LINK_GUARD_VERDICT_CMD="bash $TMP/v-billed.sh" bash "$ICI/link-guard.sh" 2>&1)"
code=$?
if [ "$code" -ne 4 ]; then
  ko "cas 1a BILLED -> refus (code attendu 4, obtenu $code)"
elif ! printf '%s' "$sortie" | grep -q 'REFUSE'; then
  ko "cas 1a BILLED -> refus (mot REFUSE absent : $sortie)"
else
  ok "cas 1a BILLED -> refus (code 4, motif REFUSE)"
fi

sortie="$(LINK_GUARD_VERDICT_CMD="bash $TMP/v-unknown.sh" bash "$ICI/link-guard.sh" 2>&1)"
code=$?
if [ "$code" -ne 4 ]; then
  ko "cas 1b UNKNOWN -> refus fail-closed (code attendu 4, obtenu $code)"
else
  ok "cas 1b UNKNOWN -> refus fail-closed (code 4)"
fi

sortie="$(LINK_GUARD_VERDICT_CMD="bash $TMP/v-unbilled.sh" bash "$ICI/link-guard.sh" 2>&1)"
code=$?
if [ "$code" -ne 0 ]; then
  ko "cas 1c CONTROLE UNBILLED -> passage (code attendu 0, obtenu $code)"
else
  ok "cas 1c CONTROLE UNBILLED -> passage (code 0)"
fi

# Le lecteur lui-meme : un mot et un code qui se contredisent donnent
# UNKNOWN, pas un feu vert.
sortie="$(COURSIA_LINK_VERDICT_CMD="bash $TMP/v-incoherent.sh" bash "$ICI/link-verdict.sh" 2>&1)"
code=$?
if [ "$code" -ne 4 ]; then
  ko "cas 1d mot et code de sortie divergents -> UNKNOWN (code attendu 4, obtenu $code)"
elif ! printf '%s' "$sortie" | grep -q 'UNKNOWN'; then
  ko "cas 1d mot et code de sortie divergents -> UNKNOWN (sortie : $sortie)"
else
  ok "cas 1d mot et code de sortie divergents -> UNKNOWN"
fi

# --- CAS 2 : ARRET SUR BASCULE -------------------------------------------
echo "cas 2 -- la veille arrete l'unite et sa slice quand le verdict bascule"

sortie="$(LINK_WATCH_VERDICT_CMD="bash $TMP/v-bascule.sh" \
  LINK_WATCH_INTERVAL=1 LINK_WATCH_MAX=2 LINK_WATCH_DRYRUN=1 \
  bash "$ICI/link-watch.sh" 2>&1)"
if ! printf '%s' "$sortie" | grep -q 'stop coursia-runner.service'; then
  ko "cas 2a bascule BILLED -> arret de l'unite (sortie : $sortie)"
elif ! printf '%s' "$sortie" | grep -q 'stop coursia-ci.slice'; then
  ko "cas 2b bascule BILLED -> arret de la slice (sortie : $sortie)"
elif ! printf '%s' "$sortie" | grep -q 'UNBILLED'; then
  ko "cas 2c le premier tour est bien UNBILLED (sortie : $sortie)"
else
  ok "cas 2a/b/c bascule BILLED -> unite et slice arretees, le premier tour etait UNBILLED"
fi

# CONTROLE : un verdict qui reste UNBILLED ne doit declencher aucun arret.
sortie="$(LINK_WATCH_VERDICT_CMD="bash $TMP/v-unbilled.sh" \
  LINK_WATCH_INTERVAL=1 LINK_WATCH_MAX=2 LINK_WATCH_DRYRUN=1 \
  bash "$ICI/link-watch.sh" 2>&1)"
if printf '%s' "$sortie" | grep -q 'DRYRUN systemctl'; then
  ko "cas 2d CONTROLE UNBILLED -> aucun arret (sortie : $sortie)"
else
  ok "cas 2d CONTROLE UNBILLED -> aucun arret"
fi

# --- CAS 3 : LE HOLDER RESPECTE LE VERDICT ------------------------------
echo "cas 3 -- le holder respecte le verdict"

POWERSHELL=""
for candidat in powershell.exe pwsh; do
  if command -v "$candidat" >/dev/null 2>&1; then POWERSHELL="$candidat"; break; fi
done

if [ -z "$POWERSHELL" ]; then
  skip "cas 3 -- holder : aucun PowerShell sur cette machine (le cas est rejoue sur le siege WSL)"
else
  # Contrat publie STUB : il imite la premiere ligne et le code de sortie.
  cat >"$TMP/contrat-billed.ps1" <<'EOF'
Write-Output "BILLED reason=adapter=test-hotshot cost=Metered"
exit 3
EOF
  cat >"$TMP/contrat-unbilled.ps1" <<'EOF'
Write-Output "UNBILLED reason=adapter=test cost=Unrestricted"
exit 0
EOF
  # wsl.exe STUB : il note qu'on l'a appele, sans lancer de distro.
  printf '@echo off\r\necho START CALLED %%*>> "%%COURSIA_FAKE_WSL_LOG%%"\r\nexit /b 0\r\n' >"$TMP/wsl-stub.cmd"

  : >"$TMP/wsl.log"
  COURSIA_LINK_BILLED_SCRIPT="$TMP/contrat-billed.ps1" \
  COURSIA_WSL_EXE="$TMP/wsl-stub.cmd" \
  COURSIA_HOLDER_LOG="$TMP/holder.log" \
  COURSIA_FAKE_WSL_LOG="$TMP/wsl.log" \
    "$POWERSHELL" -NoProfile -ExecutionPolicy Bypass -File "$ICI/hold-runner.ps1" \
    -Distro coursia-link-guard-test >"$TMP/holder-billed.out" 2>&1
  code=$?
  if [ -s "$TMP/wsl.log" ]; then
    ko "cas 3a BILLED -> le holder ne lance PAS le service (wsl stub appele : $(cat "$TMP/wsl.log"))"
  elif [ "$code" -ne 3 ]; then
    ko "cas 3a BILLED -> refus avec code 3 (code obtenu $code)"
  else
    ok "cas 3a BILLED -> le holder ne lance pas le service (code 3, wsl stub jamais appele)"
  fi

  : >"$TMP/wsl.log"
  COURSIA_LINK_BILLED_SCRIPT="$TMP/contrat-unbilled.ps1" \
  COURSIA_WSL_EXE="$TMP/wsl-stub.cmd" \
  COURSIA_HOLDER_LOG="$TMP/holder.log" \
  COURSIA_FAKE_WSL_LOG="$TMP/wsl.log" \
    "$POWERSHELL" -NoProfile -ExecutionPolicy Bypass -File "$ICI/hold-runner.ps1" \
    -Distro coursia-link-guard-test >"$TMP/holder-unbilled.out" 2>&1
  if [ ! -s "$TMP/wsl.log" ]; then
    ko "cas 3b CONTROLE UNBILLED -> le holder lance le service (rien dans le stub wsl)"
  else
    ok "cas 3b CONTROLE UNBILLED -> le holder lance le service (stub wsl appele)"
  fi

  # CAS 3c -- TEMOIN NEGATIF : le holder D'AVANT le correctif (telecharge
  # depuis origin/main) lance le service meme sur un verdict BILLED. Sans ce
  # cas, un harnais vert pourrait travaillez sur un holder qui ne protege
  # rien : c'est le controle qui prouve que le cas 3a discriminate.
  if git -C "$ICI" cat-file -e "origin/main:scripts/ci/docker/linux-runner/persist/hold-runner.ps1" 2>/dev/null; then
    git -C "$ICI" show "origin/main:scripts/ci/docker/linux-runner/persist/hold-runner.ps1" >"$TMP/hold-runner-avant.ps1"
    # La copie d'avant n'a pas les deux knobs de testabilite (chemin wsl et
    # chemin du journal) : on les lui ajoute par sed. Le point demontrable
    # reste intact -- elle n'a AUCUNE porte de verdict.
    sed -i 's|\$wsl = "\$env:WINDIR\\System32\\wsl.exe"|$wsl = $env:COURSIA_WSL_EXE|' "$TMP/hold-runner-avant.ps1"
    sed -i 's|\$log = "\$env:USERPROFILE\\\.coursia-runner\\holder.log"|$log = $env:COURSIA_HOLDER_LOG|' "$TMP/hold-runner-avant.ps1"
    : >"$TMP/wsl.log"
    COURSIA_LINK_BILLED_SCRIPT="$TMP/contrat-billed.ps1" \
    COURSIA_WSL_EXE="$TMP/wsl-stub.cmd" \
    COURSIA_HOLDER_LOG="$TMP/holder-avant.log" \
    COURSIA_FAKE_WSL_LOG="$TMP/wsl.log" \
      "$POWERSHELL" -NoProfile -ExecutionPolicy Bypass -File "$TMP/hold-runner-avant.ps1" \
      -Distro coursia-link-guard-test >"$TMP/holder-avant.out" 2>&1
    if [ -s "$TMP/wsl.log" ]; then
      ok "cas 3c TEMOIN NEGATIF -> le holder d'avant le correctif lance bien le service sur BILLED (le cas 3a discrimine)"
    else
      ko "cas 3c TEMOIN NEGATIF -> le holder d'avant le correctif n'a pas lance le service : le cas 3a ne prouve rien"
    fi
  else
    skip "cas 3c temoin negatif : version d'avant le correctif introuvable (origin/main indisponible)"
  fi
fi

# --- BILAN ----------------------------------------------------------------
p=$(wc -l <"$TMP/pass"); f=$(wc -l <"$TMP/fail"); s=$(wc -l <"$TMP/skip")
echo
echo "$p PASS / $f FAIL / $s SKIP"
[ "$f" -eq 0 ] || exit 1
exit 0
