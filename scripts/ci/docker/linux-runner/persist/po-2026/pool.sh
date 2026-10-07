#!/usr/bin/env bash
# Pool d'exécuteurs éphémères GitHub Actions — myia-po-2026 (WSL Ubuntu)
# Labels: coursia-ephemeral,coursia-linux — 1 job = 1 runner, re-spawn auto.
# Source maintenue: D:\Dev\CoursIA-runners-p0\pool.sh (copie LF normalisée dans WSL).
set -u
POOL_SIZE="${POOL_SIZE:-8}"
REPO="jsboige/CoursIA"
BASE="$HOME/CoursIA-runners-p0"
BUNDLE="$BASE/actions-runner.tar.gz"
LOCK="$BASE/pool.lock"
# Cache d'outils PERSISTANT, hors de l'arbre ephemere (#17407/Q5, arbitrage ai-01
# 2026-09-22) : sans lui, setup-python telecharge un CPython nu sous slot-N/_work/_tool/
# que spawn_slot detruit (rm -rf) au job suivant — les appels par chemin absolu
# (test_guard_gauntlet.py:102 -> sys.executable) visent alors une cible disparue
# (exit 127, stdout vide = indiscernable de « le garde n'a rien detecte »). L'image
# Docker garde ce cache sous /opt/hostedtoolcache (persistant par construction).
# Par-SLOT : slot-N/toolcache survit au rm -rf de slot-N (chemin distinct) et un
# numero de slot n'est jamais concurrent avec lui-meme (spawn_slot bloque sur son
# job) — pas de race d'extraction partagee entre jobs simultanes.
TOOLCACHE_BASE="$BASE/toolcache"
export RUNNER_TOOL_CACHE="${RUNNER_TOOL_CACHE:-$TOOLCACHE_BASE/default}"
mkdir -p "$BASE"

# --- Mint du registration token, et sonde testable (POOL_PROBE) --------------
# Ce bloc vit AVANT la redirection vers pool.log et AVANT le verrou de singleton :
# une sonde lancee pendant que le pool tourne serait sinon rejetee par
# « pool deja actif » avant d'avoir exerce ce qu'elle mesure. La sonde n'ouvre
# aucun slot et n'ecrit rien hors de son propre stdout/stderr.
MINT_ATTEMPTS="${MINT_ATTEMPTS:-4}"

# mint_token — registration token, avec discrimination transitoire / terminal.
# Porte au pool NATIF la doctrine que le superviseur Docker a recue par #15154
# (#16086 pour la classification, #19597 pour le compte nomme) : 4xx hors 408 =
# terminal, reseau / 5xx = retry. Le pool natif ne l'avait jamais recue.
#
# Mesure du 2026-10-07 sur pool.log (310 echecs depuis le 28/09, tous slots) :
#   - 305 precedes d'un `UtilAcceptVsock:271: accept4 failed 110` — ETIMEDOUT du
#     canal d'interop WSL -> gh.exe, transitoire par nature ;
#   - 5 restants : reponses tronquees (`unexpected EOF`, `unexpected end of JSON
#     input`) et un crash de gh.exe cote Windows — transitoires aussi.
# AUCUN n'etait structurel. La forme mono-coup rendait pourtant le slot au tick
# suivant du superviseur (30 s) a chaque hoquet : 247 cycles de slot perdus dans
# la seule fenetre 05/10 23h -> 06/10 02h — et le log ne nommait pas la cause.
mint_token() {
  local attempt=1 out tok cause
  while :; do
    out="$(gh.exe api -X POST "repos/$REPO/actions/runners/registration-token" --jq .token 2>&1)"
    # Un registration token est une ligne alphanumerique d'au moins 20 caracteres ;
    # toute autre sortie est un message d'erreur (ou du vide — interop muette).
    tok="$(printf '%s' "$out" | tr -d '\r' | grep -m1 -oE '^[A-Za-z0-9]{20,}$')"
    if [ -n "$tok" ]; then printf '%s' "$tok"; return 0; fi
    cause="$(printf '%s' "$out" | tr '\n' ' ' | cut -c1-200)"
    [ -n "$cause" ] || cause="<sortie vide : interop WSL->gh.exe muette>"
    # Cause structurelle : le compte n'a pas le droit sur les endpoints runners.
    # Ni le retry ni l'attente ne la levent (#15154) — terminal immediat.
    if printf '%s' "$out" | grep -qE 'HTTP 40[134]|must have repository|Resource not accessible|Bad credentials'; then
      echo "$(date -Is) mint token TERMINAL (droits du compte) — $cause"
      return 1
    fi
    if [ "$attempt" -ge "$MINT_ATTEMPTS" ]; then
      echo "$(date -Is) mint token epuise apres $MINT_ATTEMPTS tentatives (transitoire) — $cause"
      return 1
    fi
    echo "$(date -Is) mint token transitoire (tentative $attempt/$MINT_ATTEMPTS) — $cause ; essai suivant dans $((attempt * 2))s"
    sleep $((attempt * 2))
    attempt=$((attempt + 1))
  done
}

# Magasin d'objets partage (#18225, 2026-10-07) : maillon 3 de la chaine. Les deux
# premiers (workspace persistant + quarantaine) ont rendu le slot chaud LE chemin
# nominal, mais mesuraient son echec au prix d'un retour au froid complet : un _work
# ecarte (2353 en 9 jours, cf pool.log) ou un premier spawn redescendait le pack
# HTTPS integral (5.49 GiB, mesure run 36420237212). Le miroir bare local casse ce
# cout : pose UNE fois hors bande (`git clone --mirror`), maintenu incrementalement
# par mirror_refresh, consomme par les repos de slot via git alternates — le contenu
# traverse le reseau une fois pour huit slots, et un slot froid materialise en
# local sans re-telecharger l'historique. Fail-open par construction : miroir
# absent => le parc se comporte exactement comme avant cette section.
# Ces definitions vivent AVANT le bloc POOL_PROBE : les sondes les appellent.
MIRROR="$BASE/objects-mirror.git"
MIRROR_REMOTE="${MIRROR_REMOTE:-https://github.com/jsboige/CoursIA.git}"
MIRROR_REFRESH_EVERY="${MIRROR_REFRESH_EVERY:-300}"

# mirror_refresh — fetch incrementalement le miroir (append-only : les objets sont
# immuables, les refs se deplacent atomiquement ; les emprunteurs alternates lisent
# sans verrou). Throttle par horodatage pour que le tick de 30 s du superviseur ne
# fasse pas un fetch par tick ; flock non bloquant : une refresh concurrente (relance
# interactive) est sautee, pas attendue. Recharge d'urgence : voir le README.
mirror_refresh() {
  [ -d "$MIRROR/objects" ] || return 0
  local now
  now=$(date +%s)
  [ $(( now - ${MIRROR_LAST_REFRESH:-0} )) -ge "$MIRROR_REFRESH_EVERY" ] || return 0
  MIRROR_LAST_REFRESH=$now
  # NB : pas de `2>/dev/null` sur ce exec — la redirection y serait PERSISTANTE
  # (elle masquerait le stderr de tout le script, pas seulement celui de l'ouverture).
  exec 8>"$BASE/mirror.lock" || return 0
  flock -n 8 || return 0
  if git --git-dir="$MIRROR" fetch --prune "$MIRROR_REMOTE" '+refs/*:refs/*' 2>&1; then
    echo "$(date -Is) miroir rafraichi"
  else
    echo "$(date -Is) miroir : refresh echoue (pool continue sur l'etat precedent)"
  fi
  return 0
}

# ensure_alternates — $1 : un repo de slot (avec .git). Ajoute le miroir comme
# source d'objets du repo : un fetch negocie alors avec le serveur en pretendant
# deja tenir tout l'historique du miroir (has_object consulte les alternates), donc
# le delta HTTPS tombe au contenu reellement nouveau ; et un blob manquant d'un
# clone promisor blob:none (signature (b) de #14801, #18312) se materialise depuis
# le miroir AVANT qu'un lazy-fetch reseau ne puisse echouer. Idempotent : une seule
# ligne par miroir, quel que soit le nombre d'appels.
ensure_alternates() {
  [ -d "$MIRROR/objects" ] || return 0
  local alt="$1/.git/objects/info/alternates"
  mkdir -p "$(dirname "$alt")"
  if [ -s "$alt" ]; then
    grep -qxF "$MIRROR/objects" "$alt" || printf '%s\n' "$MIRROR/objects" >> "$alt"
  else
    printf '%s\n' "$MIRROR/objects" > "$alt"
  fi
}

# seed_work — $1 : slot. Pre-materialise _work/CoursIA/CoursIA comme clone --shared
# du miroir (alternates vers le miroir, zero objet copie, instantane) puis rebascule
# origin sur HTTPS : checkout@v4 trouve un repo existant, fetch un delta quasi nul
# (tout le contenu du miroir est deja "eu"), et checkout --force materialise l'arbre
# depuis les objets locaux. Remplace le slot froid integral de restore_work.
seed_work() {
  local repo="$BASE/slot-$1/_work/CoursIA/CoursIA"
  [ -d "$MIRROR/objects" ] || return 0
  mkdir -p "$(dirname "$repo")"
  if git clone --quiet --shared --no-checkout "$MIRROR" "$repo" 2>/dev/null; then
    git -C "$repo" remote set-url origin "$MIRROR_REMOTE"
    echo "$(date -Is) slot$1: _work seme depuis le miroir (checkout@v4 -> fetch quasi nul)"
  else
    echo "$(date -Is) slot$1: semis _work echoue -> slot froid integral (nominal)"
    rm -rf "$BASE/slot-$1/_work"
    return 1
  fi
}

if [ -n "${POOL_PROBE:-}" ]; then
  case "$POOL_PROBE" in
    mint-token) mint_token; rc=$?; echo "$(date -Is) PROBE mint-token rc=$rc"; exit $rc ;;
    mirror-refresh) mirror_refresh; rc=$?; echo "$(date -Is) PROBE mirror-refresh rc=$rc"; exit $rc ;;
    seed) seed_work probe; rc=$?; echo "$(date -Is) PROBE seed rc=$rc"; exit $rc ;;
    alternates) ensure_alternates "$BASE/probe-warm/CoursIA/CoursIA"; rc=$?; echo "$(date -Is) PROBE alternates rc=$rc"; exit $rc ;;
    *) echo "$(date -Is) PROBE inconnue: $POOL_PROBE"; exit 2 ;;
  esac
fi

exec >>"$BASE/pool.log" 2>&1

# Singleton: la tâche planifiee a RestartCount=3 — jamais deux superviseurs
exec 9>"$LOCK" || exit 1
flock -n 9 || { echo "$(date -Is) pool deja actif ($LOCK)"; exit 0; }

# Contrat de l'image (scripts/ci/docker/linux-runner/Dockerfile), volet ENV — qu'un slot natif ne peut
# PAS heriter, faute de conteneur. Mesure du 2026-09-22 sur cet hote : le python systeme est marque
# EXTERNALLY-MANAGED (/usr/lib/python3.12/EXTERNALLY-MANAGED) et `python3 -m pip install --dry-run
# pyyaml` est REFUSE (PEP 668). C'est le cas exact que le Dockerfile l.14-21 documente : « un workflow
# qui fait `import yaml || pip install pyyaml` meurt sur le pip ». Le pool pose donc lui-meme la
# variable ; elle est heritee par run.sh -> Runner.Worker -> etapes du job, par le meme canal que le
# PATH (mesure : le PATH de pool.sh se retrouve dans /proc/<pid>/environ des listeners).
export PIP_BREAK_SYSTEM_PACKAGES=1

# PATH (Q6, 2026-09-23, reserve secretaire c.37 + mesure /proc/<pid>/environ) :
# la relance du superviseur depuis une session interactive (fenetre Q5) herite le
# PATH de CETTE session — ~/.local/bin ABSENT des listeners. Le pool rend son
# contrat independant du contexte de lancement : ~/.local/bin en tete (gh 2.90.0
# et python y sont poses).
export PATH="$HOME/.local/bin:$PATH"

# Garde anti-stall HTTPS (#18225, 2026-09-28) : un fetch stallé (zero octet, connexion
# etablie puis muette — discriminant du user sur run 36420237212) pendait jusqu'au
# plafond timeout-minutes du job. git abort des que le debit tombe sous 1 KiB/s pendant
# 90 s : le job echoue en ~2 min (rejouable sur slot chaud) au lieu de manger 10 min.
# Miroir en ~/.gitconfig (pose le 28/09) — l'env reste le porteur durable du contrat.
export GIT_HTTP_LOW_SPEED_LIMIT=1024
export GIT_HTTP_LOW_SPEED_TIME=90

# Contrat de l'image, volet BINAIRES. Le pool ne telecharge PAS `gh` (l'image l'epingle par SHA-256 :
# un telechargement non verifie serait un maillon de supply chain pour rien) — il cree le seul lien
# localement sur (`python` -> python3, idempotent) et CRIE si `gh` manque. Non bloquant a dessein :
# couper le pool priverait la flotte de capacite pour un defaut qui, lui, produit surtout des verts
# suspects (les gardes sortent en exit 0 SANS poster, cf. README) — un log qu'on ne peut pas manquer
# vaut mieux qu'un pool a l'arret. `~/.local/bin` est en TETE du PATH du pool par construction (export Q6, 2026-09-23) — plus dependant du contexte de lancement.
ensure_host_contract() {
  local bin="$HOME/.local/bin" rc=0
  mkdir -p "$bin"
  [ -x "$bin/python" ] || ln -sf "$(command -v python3)" "$bin/python"
  [ -x "$bin/python" ] || { echo "$(date -Is) CONTRAT: python nu ABSENT de $bin"; rc=1; }
  [ -x "$bin/gh" ]     || { echo "$(date -Is) CONTRAT: gh ABSENT de $bin — poser la release Linux officielle (l'image epingle 2.99.0+SHA256) ; sans lui des gardes sortent en exit 0 SANS poster"; rc=1; }
  [ -n "${PIP_BREAK_SYSTEM_PACKAGES:-}" ] || { echo "$(date -Is) CONTRAT: PIP_BREAK_SYSTEM_PACKAGES non pose"; rc=1; }
  command -v gh >/dev/null 2>&1 || { echo "$(date -Is) CONTRAT: gh INVISIBLE du PATH du pool (relance depuis session interactive ?) — existence du fichier ne suffit pas (reserve #17406 c.5784716255)"; rc=1; }
  command -v patchelf >/dev/null 2>&1 || { echo "$(date -Is) CONTRAT: patchelf INVISIBLE ($bin/patchelf) — re-patch RUNPATH du toolcache impossible (ASK secretary c.37 2026-09-23)"; rc=1; }
  mkdir -p "$RUNNER_TOOL_CACHE" 2>/dev/null || { echo "$(date -Is) CONTRAT: RUNNER_TOOL_CACHE non creable ($RUNNER_TOOL_CACHE)"; rc=1; }
  [ "$rc" -eq 0 ] && echo "$(date -Is) contrat d'image: bins/python OK ($( "$bin/gh" --version 2>/dev/null | head -1 )), toolcache=$RUNNER_TOOL_CACHE"
  return $rc
}

ensure_bundle() {
  [ -s "$BUNDLE" ] && return 0
  local url ver
  url=$(curl -sL -o /dev/null -w '%{url_effective}' https://github.com/actions/runner/releases/latest)
  ver=${url##*v}
  curl -sL -o "$BUNDLE" "https://github.com/actions/runner/releases/download/v${ver}/actions-runner-linux-x64-${ver}.tar.gz"
  [ -s "$BUNDLE" ]
}

# RUNPATH du CPython exporte depuis l'image Docker (ld-loader, 2026-09-23, ASK
# secretary c.37) : le binaire porte RUNPATH=/opt/hostedtoolcache/Python/.../lib
# (chemin Docker, ABSENT en WSL natif) — sous un env minimal (gauntlet, anciennes
# bases anterieures a #17415) le loader meurt en exit 127 stdout vide sur
# libpython3.11.so.1.0. Le patch $ORIGIN/../lib rend la resolution independante
# de l'env. Une extraction setup-python le perd : re-application au boot (slots
# existants) et a chaque tick (extraction survenue depuis le tick precedent) —
# idempotent, 8 readelf par 30s.
repatch_toolcache_pythons() {
  local py
  while IFS= read -r -d '' py; do
    if readelf -d "$py" 2>/dev/null | grep -q '/opt/hostedtoolcache'; then
      patchelf --set-rpath '$ORIGIN/../lib' "$py" 2>/dev/null \
        && echo "$(date -Is) rpath repatche: $py" || echo "$(date -Is) rpath ECHEC: $py"
    fi
  done < <(find "$TOOLCACHE_BASE" -path '*/Python/3.11.16/x64/bin/python3.11' -type f -print0 2>/dev/null)
}

# Workspace persistant par slot (#18225, 2026-09-28) : le rm -rf integral par spawn
# faisait de CHAQUE job un slot froid -> checkout@v4 rejouait un fetch complet du depot
# (pack mesure : 5.49 GiB) ; les plafonds timeout-minutes calibres sur la baseline
# chaude d'ai-01 (2-3 s, run 36423208982 : clean -ffdx + fetch incremental) devenaient
# atteignables par tout ralentissement, et un stall HTTPS les garantissait (issue
# #18225). En preservant slot-N/_work d'un job au suivant, le checkout retrouve le
# regime chaud : il ne re-telecharge que le delta. ~7 GiB par slot stables (8 x 7 =
# 56 GiB, 676 GiB libres). Un workspace corrompu s'auto-guérit : checkout retombe
# en "Deleting the contents" + re-clone complet (une fois, puis re-chauffe).
keep_work() { # $1 = slot — parque _work hors de l'arbre qu'on va detruire
  local dir="$BASE/slot-$1" keep="$BASE/work-$1.keep"
  [ -d "$dir/_work" ] || return 0
  rm -rf "$keep"
  mv "$dir/_work" "$keep" || { echo "$(date -Is) slot$1: conservation _work echouee"; return 1; }
}
# Quarantaine des _work endommages (#14801, mesures 28/09). Un job qui fait
# actions/checkout@v4 AVEC sparse-checkout laisse des bits skip-worktree et des
# fichiers absents dans le depot LOCAL du slot ; le _work chaud les transporte au
# job suivant. Deux signatures mesurees : (a) bits > 0 avec git status PROPRE
# (l'arbre se declare sain, le checkout ne nettoie jamais, l'auto-guerison
# supposee ci-dessus ne se declenche pas) ; (b) pire : bits = 0, fichiers absents
# et statut propre (sparse-checkout disable a efface les bits SANS re-materialiser
# les blobs du clone partiel). Effacer les bits ne suffit donc pas : on VALIDE
# l'arbre parque, et tout arbre endommage est ecarte -- le slot repart froid,
# seul etat de confiance. Un arbre sain reste chaud (objectif #18225 preserve).
validate_keep() { # $1 = keep dir — rc=0 si l'arbre est materialise et coherent
  local repo="$1/CoursIA/CoursIA"
  [ -d "$repo/.git" ] || return 1
  git -C "$repo" rev-parse --git-dir >/dev/null 2>&1 || return 1
  # (a) residu skip-worktree
  git -C "$repo" ls-files -v 2>/dev/null | grep -q '^S' && return 1
  # (b) index menteur : le refresh stat rend visibles les fichiers trackes absents
  git -C "$repo" update-index --really-refresh -q >/dev/null 2>&1
  [ -n "$(git -C "$repo" status --porcelain 2>/dev/null)" ] && return 1
  return 0
}

restore_work() { # $1 = slot — remet le _work parque dans le slot frais, s'il est sain
  local dir="$BASE/slot-$1" keep="$BASE/work-$1.keep"
  if [ ! -d "$keep" ]; then
    seed_work "$1"   # pas de parc : semis depuis le miroir (no-op si miroir absent)
    return 0
  fi
  [ -d "$dir/_work" ] && { echo "$(date -Is) slot$1: _work inattendu deja present, conserve ecarte"; rm -rf "$keep"; return 0; }
  if validate_keep "$keep"; then
    if mv "$keep" "$dir/_work"; then
      echo "$(date -Is) slot$1: _work restaure (regime chaud, valide)"
      ensure_alternates "$dir/_work/CoursIA/CoursIA"
    fi
  else
    echo "$(date -Is) slot$1: _work ecarte (endommage) -> semis miroir"
    rm -rf "$keep"
    seed_work "$1"
  fi
}

spawn_slot() { # $1 = slot — bloque jusqu'a la fin du job (ephemere = 1 job)
  local slot="$1"
  local dir="$BASE/slot-$slot"
  local tok
  tok="$(mint_token)"
  if [ ${#tok} -lt 20 ]; then echo "$(date -Is) slot$slot: mint token echoue"; return 1; fi
  keep_work "$slot"
  rm -rf "$dir"; mkdir -p "$dir"
  tar -xzf "$BUNDLE" -C "$dir" || { echo "$(date -Is) slot$slot: extraction echouee"; return 1; }
  # Isolation par slot (cf. TOOLCACHE_BASE) : heritee par run.sh -> Runner.Worker ->
  # setup-python, meme canal que PIP_BREAK_SYSTEM_PACKAGES (mesure /proc/<pid>/environ).
  RUNNER_TOOL_CACHE="$TOOLCACHE_BASE/slot-$slot"; export RUNNER_TOOL_CACHE
  mkdir -p "$RUNNER_TOOL_CACHE"
  restore_work "$slot"
  ( cd "$dir" && \
    ./config.sh --url "https://github.com/$REPO" --token "$tok" \
      --labels "coursia-ephemeral,coursia-linux" --ephemeral \
      --name "myia-po-2026-wsl-$slot" --unattended --replace \
      && ./run.sh --once ) || echo "$(date -Is) slot$slot: runner termine (rc=$?)"
  keep_work "$slot"
  rm -rf "$dir"
}

ensure_bundle || { echo "$(date -Is) telechargement bundle echoue"; exit 1; }
# Rafraichit le miroir au boot (si pose), puis a chaque tick via le throttle.
mirror_refresh
# Verifie le contrat AVANT d'ouvrir des slots : un contrat incomplet se lit dans pool.log au demarrage,
# pas trois heures plus tard dans le rouge d'une PR d'une autre lane.
ensure_host_contract || echo "$(date -Is) contrat d'image INCOMPLET — les jobs servis par ce pool peuvent rendre des faux rouges ou des verts fabriques"
repatch_toolcache_pythons

declare -A PIDS
echo "$(date -Is) pool demarre (POOL_SIZE=$POOL_SIZE)"
while :; do
  for i in $(seq 1 "$POOL_SIZE"); do
    if [ -z "${PIDS[$i]:-}" ] || ! kill -0 "${PIDS[$i]}" 2>/dev/null; then
      echo "$(date -Is) spawn slot$i"
      spawn_slot "$i" & PIDS[$i]=$!
    fi
  done
  repatch_toolcache_pythons
  mirror_refresh
  sleep 30
done
