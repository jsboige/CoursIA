#!/bin/bash
# Enregistrement ephemere du runner conteneurise. Le token ne passe JAMAIS
# par argv (pattern manage_self_hosted_runner.py) : config.sh lit
# ACTIONS_RUNNER_INPUT_TOKEN. Requis a l'appel (docker run -e ...) :
#   ACTIONS_RUNNER_INPUT_TOKEN   token d'enregistrement (valable 1 h)
#   ACTIONS_RUNNER_INPUT_URL     https://github.com/jsboige/CoursIA
#   ACTIONS_RUNNER_INPUT_NAME    myia-po-2024-linux-docker
#   ACTIONS_RUNNER_INPUT_LABELS  self-hosted,coursia-ephemeral,coursia-linux
# Sauf en mode persistent deja enregistre (RUNNER_MODE=persistent avec un
# volume de config qui porte .runner/.credentials : aucune de ces variables
# n'est requise au restart -- #14329).
set -euo pipefail

# --- Mode persistent : enregistrement unique, restart sans token (#14329) ----
# TEST-ENTRYPOINT-PERSISTENT-START
# RUNNER_HOME porte le layout runner complet (binaires + .runner + .credentials)
# et est le point de montage du volume de config PAR SLOT en mode persistent.
# RUNNER_DIST est la copie vierge de l'image : source de restauration quand le
# volume est cree vide (un volume nomme existant masque les binaires de l'image).
RUNNER_HOME="${RUNNER_HOME:-/opt/runner}"
RUNNER_DIST="${RUNNER_DIST:-/opt/runner-dist}"
RUNNER_MODE="${RUNNER_MODE:-ephemeral}"

runner_mode() { printf '%s' "$RUNNER_MODE"; }

runner_restore_dist() {
  # Un volume monté vide sur RUNNER_HOME masque les binaires extraits au build :
  # on les restaure depuis RUNNER_DIST. Idempotent (cp -a écrase sans risque,
  # source identique a l'image epinglee).
  if [ ! -x "$RUNNER_HOME/run.sh" ] && [ -x "$RUNNER_DIST/run.sh" ]; then
    echo "entrypoint: $RUNNER_HOME vide -- restauration des binaires depuis $RUNNER_DIST"
    cp -a "$RUNNER_DIST/." "$RUNNER_HOME/"
  fi
}

runner_is_registered() { [ -f "$RUNNER_HOME/.runner" ]; }

require_registration_env() {
  : "${ACTIONS_RUNNER_INPUT_TOKEN:?RUNNER token manquant}"
  : "${ACTIONS_RUNNER_INPUT_URL:?RUNNER url manquante}"
  : "${ACTIONS_RUNNER_INPUT_NAME:?RUNNER name manquant}"
  : "${ACTIONS_RUNNER_INPUT_LABELS:?RUNNER labels manquants}"
}

# Externals requis par le runner (#21745, limb C). Un seul manquant tue le job
# AVANT sa premiere commande : `actions/checkout` ne demarre pas et le log fait
# 45 lignes, sans aucune signature de clone ni de ref (mesure po-2024, job
# 118588912210 : `/opt/runner/externals/node24/bin/node` -> No such file or
# directory). Un slot enregistre RECOIT des jobs, et chacun meurt en portant un
# rouge que rien ne rattache a sa cause ; refuser l'enregistrement est la seule
# facon, depuis le depot, de signaler AVANT le dispatch. Le message est celui
# que reconnait scripts/ci/classify_infra_leg.py.
runner_require_externals() {
  local ext missing=""
  for ext in ${RUNNER_REQUIRED_EXTERNALS:-node24}; do
    [ -e "$RUNNER_HOME/externals/$ext/bin/node" ] || missing="$missing $ext"
  done
  [ -n "$missing" ] || return 0
  for ext in $missing; do
    echo "entrypoint: INFRA_EXTERNALS_MISSING externals/$ext/bin/node absent sous $RUNNER_HOME -- enregistrement REFUSE, aucun job ne sera dispatche sur ce slot" >&2
  done
  exit 1
}
# TEST-ENTRYPOINT-PERSISTENT-END

export ACTIONS_RUNNER_INPUT_WORK=/home/runner/_work

# --- Desarmement de l'etat sparse-checkout residuel (slot poisoning) ---------
# Le volume _work est persistant PAR SLOT (#14285/#14288) et le conteneur est
# recree a chaque job : ce bloc est donc un hook job-started, sans plomberie.
#
# actions/checkout ne desarme le sparse qu'AU DEBUT du job suivant -- trop tard.
# Sequence mesuree (job 100417132588, slot myia-ai-01-linux-docker-2) :
#   git reset --hard HEAD        <- sparse encore ACTIF : ne reset que le sous-ensemble
#   git sparse-checkout disable  <- leve les skip-worktree ; l index reclame les absents
#   git checkout --force <ref>
#     error: Path '...test_hmm_regime_vol.py' not uptodate; will not remove from working tree.
#                                <- git ABANDONNE la materialisation, HEAD bouge quand meme
# Le job herite alors de l arbre sparse du precedent -- 1 fichier sous scripts/
# au lieu de 1087 -- et echoue en [Errno 2] sur un fichier pourtant versionne.
#
# Deux cas, deux couts : le flag arme est le seul etat cassant (git materialise
# le sous-ensemble), le fichier de motifs seul est inerte (flag absent = motifs
# ignores -- mesure du 2026-09-02 : slots 3-8 le portent avec un arbre complet).
# On ne purge donc le clone que dans le premier cas ; sinon on retire le fichier
# et on garde le cache incremental que #14285 a achete (~40-51 s/job).
for gitdir in "$ACTIONS_RUNNER_INPUT_WORK"/*/*/.git; do
  [ -e "$gitdir" ] || continue
  repo="${gitdir%/.git}"
  if [ -n "$(git -C "$repo" config --local --get core.sparseCheckout 2>/dev/null || true)" ]; then
    echo "entrypoint: sparse ARME dans $repo -- purge du clone (le checkout suivant reclonera)"
    rm -rf "$repo"
  elif [ -f "$gitdir/info/sparse-checkout" ]; then
    echo "entrypoint: motifs sparse inertes dans $repo -- retrait du fichier, clone conserve"
    rm -f "$gitdir/info/sparse-checkout"
  fi
done
# ---------------------------------------------------------------------------

# --- Desarmement des refs distantes dangling (slot poisoning checkout) -------
# Le volume _work persiste PAR SLOT (#14285/#14288) : une branche rebasee ou
# force-poussee cote origin laisse refs/remotes/origin/<branche> pointant sur
# un objet absent du depot -- le fetch de actions/checkout (--depth=1, refspec
# EXPLICITE +<sha>:refs/remotes/pull/N/merge) ne met a jour NI ne prune les
# autres refs distantes. Le checkout du job suivant meurt alors avant toute
# etape utile :
#   git checkout --force <ref> -> fatal: bad object refs/remotes/origin/<b>
# (incident PR #15089, job 101812399772, 2026-09-07 : chore/11840-iit-zero-pad
# rebasee entre-temps sur un slot persistant). On ne supprime QUE les refs dont
# l'objet manque -- le cache incrementale de #14285 reste conserve (contraire-
# ment au purge rm -rf du cas sparse arme, ~40-51 s/job).
# Complementaire au bloc work_cache_health (#15105) place juste apres : son
# detecteur (for-each-ref par defaut) ne nomme que les refs INPARSABLES
# (fichier zero octet -> reparation ou purge du clone) ; une ref au SHA
# parsable mais d'objet absent tue son scan en fatal non reconnu et son
# compte de refs reste > 0 -- il conclurait "sain". Verifie par mesure :
# for-each-ref defaut -> fatal rc=128 ; format '%(refname) %(objectname)'
# -> liste rc=0. D'ou l'ordre : disarm chirurgical ici, integrite large
# ensuite.
for gitdir in "$ACTIONS_RUNNER_INPUT_WORK"/*/*/.git; do
  [ -e "$gitdir" ] || continue
  repo="${gitdir%/.git}"
  # Borne du cout (fix #20697, myia-ai-01-wsl pool down 2 jours) : avec ~4 600
  # refs distantes et ~21 000 packs par cache, l'ancienne boucle faisait un
  # `cat-file -e` par ref -- chaque appel parcourt l'index de packs, cout
  # O(refs * packs) = 23 min sur le slot mesure. La borne est ici O(refs + packs) :
  # UN seul `cat-file --batch-check` pour toutes les SHAs de la liste, puis
  # suppression des refs dont le SHA est dans la liste des `missing`. Le
  # fd de la liste temporaire est ferme par redirection explicite pour eviter
  # un `lsof` permanent sur le slot (le bloc tourne avant l'enregistrement).
  _el_refs="$(mktemp -t el-refs.XXXXXX)" && _el_miss="$(mktemp -t el-miss.XXXXXX)" || {
    # mktemp a echoue (saturation /tmp) : on retombe sur l'ancienne boucle pour
    # ne pas empecher le slot de s'enregistrer, et on consigne.
    # Le test d'existence d'un objet (cat-file -e) declenche le fetch paresseux
    # en clone partiel (promisor=true, partialclonefilter=blob:none -- slot 3
    # po-2024 en incidence) ; sans garde, git tente un fetch sans timeout et le
    # 2>/dev/null masque tout. GIT_NO_LAZY_FETCH=1 (git >= 2.46, no-op avant)
    # desactive le fetch, timeout 10 borne le pire cas. Le de-masquage de stderr
    # permet de voir la cause d'un timeout (sinon le bloc est muet, et c'est
    # exactement la panne slot 3).
    echo "entrypoint: mktemp indisponible -- fallback boucle O(refs*packs)" >&2
    while read -r ref sha; do
      if ! GIT_NO_LAZY_FETCH=1 timeout 10 git -C "$repo" cat-file -e "$sha^{object}"; then
        echo "entrypoint: ref distante dangling $ref -- suppression (objet absent ou timeout cat-file)"
        git -C "$repo" update-ref -d "$ref" 2>/dev/null || true
      fi
    done < <(git -C "$repo" for-each-ref --format='%(refname) %(objectname)' refs/remotes 2>/dev/null)
    continue
  }
  git -C "$repo" for-each-ref --format='%(refname) %(objectname)' refs/remotes 2>/dev/null > "$_el_refs" || true
  if [ -s "$_el_refs" ]; then
    # Meme garde que pour le fallback : cat-file --batch-check en clone partiel
    # declenche un fetch paresseux par objet absent. GIT_NO_LAZY_FETCH=1
    # (no-op sur git < 2.46) desactive le fetch ; timeout 60 borne le batch
    # (4 600 refs mesure, batch process unique). Le 2>/dev/null historique
    # est retire -- un timeout doit etre visible sur stderr (cf. incident slot 3
    # po-2024 c.327).
    awk '{print $NF}' "$_el_refs" | sort -u \
      | GIT_NO_LAZY_FETCH=1 timeout 60 git -C "$repo" cat-file --batch-check \
      | awk '$2 == "missing" { print $1 }' > "$_el_miss" || true
    if [ -s "$_el_miss" ]; then
      while read -r sha; do
        awk -v s="$sha" '$NF == s { print $1 }' "$_el_refs" | while read -r ref; do
          [ -n "$ref" ] || continue
          echo "entrypoint: ref distante dangling $ref -- suppression (objet absent)"
          git -C "$repo" update-ref -d "$ref" 2>/dev/null || true
        done
      done < "$_el_miss"
    fi
  fi
  rm -f "$_el_refs" "$_el_miss"

  # Prune des refs pull/* (fix #20697 point 2) : chaque PR vue depose un
  # `refs/remotes/{remote}/pull/N/{head,merge}` (fetch --refspec EXPLICITE de
  # actions/checkout, jamais prune auto, mesure : ~4 600 refs dont la majorite
  # obsolete apres merge/close). `update-ref --stdin` borne le cout a un
  # processus par depot (au lieu d'un update-ref par ref) ; les refs seront
  # recreees au prochain fetch si encore pertinentes.
  _el_pull="$(mktemp -t el-pull.XXXXXX)" || continue
  git -C "$repo" for-each-ref --format='delete %(refname)' refs/remotes 2>/dev/null \
    | grep '^delete .*/pull/' > "$_el_pull" || true
  if [ -s "$_el_pull" ]; then
    git -C "$repo" update-ref --stdin < "$_el_pull" 2>/dev/null || true
  fi
  rm -f "$_el_pull"
done
# TEST-ENTRYPOINT-DANGLING-REFS-END

# --- Magasin d'objets partage (#18225, portage de persist/po-2026/pool.sh) ---
# Le volume _work persistant (#14285) a rendu le slot chaud le chemin nominal,
# mais chaque retour au froid (clone purge, slot neuf) redescendait l'historique
# integral en HTTPS : 5,49 Gio mesures. Le miroir bare du volume toolcache casse
# ce cout -- il traverse le reseau UNE fois pour tous les slots.
#
# Ce bloc est la moitie CONSOMMATRICE de la recette ; le superviseur tient la
# moitie productrice (bootstrap + refresh periodique). Deux gestes, dans cet
# ordre :
#
#   1. alternates sur chaque clone deja present : le fetch de actions/checkout
#      negocie en pretendant tenir tout l'historique du miroir, donc le delta
#      HTTPS tombe au contenu reellement nouveau ; et un blob manquant d'un
#      clone promisor blob:none (#14801 signature (b), #18312) se materialise
#      depuis le miroir AVANT qu'un lazy-fetch reseau n'echoue ;
#   2. semis du _work quand il n'existe pas : `clone --shared --no-checkout`
#      (alternates, ZERO objet copie, instantane) puis origin remis sur HTTPS.
#
# POSITION : avant le bloc work_cache ci-dessous, et c'est deliberе -- le repack
# de maintenance choisit `-ad` ou `-adl` selon la presence d'alternates. Pose
# apres, le premier passage sur un slot seme copierait les objets du miroir dans
# le volume du slot (cf wch_repack_flags).
#
# FAIL-OPEN : miroir absent => le bloc rend 0, n'ajoute rien, et RETIRE les
# lignes d'alternates qui designent un miroir disparu. Sans ce retrait, un slot
# seme AVANT la disparition gardait un alternates pendant et git rendait rc=128
# sur log/status/fetch : le garde work_cache ne le voit pas (il lit les refs,
# pas la resolvabilite des objets) et son repack -adl rend rc=0. Alternates
# vide => le slot est exactement dans l'etat d'avant ce bloc.
# TEST-ENTRYPOINT-MIRROR-START
MIRROR_PATH="${COURSIA_RUNNER_MIRROR_PATH:-/opt/hostedtoolcache/coursia-mirror.git}"
MIRROR_REMOTE="${COURSIA_RUNNER_MIRROR_REMOTE:-https://github.com/jsboige/CoursIA.git}"
MIRROR_SLUG="${COURSIA_RUNNER_MIRROR_SLUG:-}"

mirror_present() { [ -d "$MIRROR_PATH/objects" ]; }

# Cle de comparaison d'un chemin. Dans le conteneur, elle vaut le chemin
# lui-meme : aucune dependance ajoutee. Sur un hote MSYS (Git Bash), le meme
# repertoire s'ecrit `C:/Users/.../x` quand c'est GIT qui l'ecrit et
# `/tmp/x` quand c'est le shell : mesure -- `realpath -m` rend chaque forme
# verbatim, donc une egalite normalisee ne mord jamais sur cet hote, et le
# moindre des degats est un alternates duplique a chaque boot. `cygpath -m`
# ramene les deux formes a la meme chaine ; absent du conteneur, ou les formes
# coincident de toute facon.
mirror_path_key() {
  if command -v cygpath >/dev/null 2>&1; then
    cygpath -m -- "$1" 2>/dev/null || printf '%s' "$1"
  else
    printf '%s' "$1"
  fi
}

# Un depot de slot emprunte-t-il les objets du miroir ? Idempotent par
# construction : la ligne n'est ajoutee que si le fichier ne la porte pas deja,
# donc N boots donnent une ligne, pas N.
#
# La comparaison est NORMALISEE (realpath) et pas textuelle : un alternates
# ecrit par git lui-meme peut porter une autre forme du meme chemin que celle
# que le superviseur passe (mesure Git Bash : `/tmp/x` cote bash,
# `C:/Users/.../x` cote git). Une egalite de chaines laisserait alors passer une
# SECONDE ligne designant le meme repertoire -- sans consequence fonctionnelle,
# mais le fichier grossirait a chaque boot, et le compte d'emprunteurs du
# `status` deviendrait faux. Si realpath manque, on retombe sur l'egalite
# textuelle (jamais sur « considere comme present »).
mirror_ensure_alternates() {  # $1 = repo de slot (avec .git)
  local repo="$1" alt="$1/.git/objects/info/alternates" needle="$MIRROR_PATH/objects"
  local line a b have=0 key
  key="$(mirror_path_key "$needle")"
  mkdir -p "$(dirname "$alt")" 2>/dev/null || return 0
  if [ -s "$alt" ]; then
    while IFS= read -r line; do
      [ -n "$line" ] || continue
      if [ "$line" = "$needle" ] || [ "$(mirror_path_key "$line")" = "$key" ]; then
        have=1; break
      fi
      if command -v realpath >/dev/null 2>&1; then
        a="$(realpath -- "$line" 2>/dev/null || true)"
        b="$(realpath -- "$needle" 2>/dev/null || true)"
        if [ -n "$a" ] && [ -n "$b" ] && [ "$a" = "$b" ]; then have=1; break; fi
      fi
    done < "$alt"
  fi
  [ "$have" -eq 1 ] && return 0
  # `printf` vers un fichier existant AJOUTE ; vers un fichier absent il cree.
  # Le rc est neutralise : sous `set -e`, un disque plein ne doit pas tuer le
  # conteneur avant l'enregistrement du runner (meme classe que #16938).
  printf '%s\n' "$needle" >> "$alt" 2>/dev/null || return 0
  echo "entrypoint: alternates pose sur $repo -> $needle"
  return 0
}

# Retrait symetrique, pour le cas que le fail-open ne couvrait pas : le miroir
# disparait APRES qu'un slot ait ete seme. Une ligne d'alternates qui designe
# un repertoire absent rend le clone inutilisable -- `git log`, `status`,
# `fetch` rendent rc=128 avec `unable to normalize alternate object path` --
# alors que le bloc se contentait de journaliser « miroir absent ». Le garde
# work_cache ne le repere pas : il lit les refs (lisibles) et jamais la
# resolvabilite des objets, et son repack -adl rend rc=0. Retirer la ligne
# ramene le slot a l'etat d'avant #18225 (alternates vide => wch_repack_flags
# retombe sur -ad).
#
# Meme normalisation que mirror_ensure_alternates : la cle de l'hote d'abord
# (elle seule rapproche les deux formes d'ecriture du meme chemin), puis
# `realpath -m` quand il existe -- le chemin du miroir n'existe PLUS, donc un
# `realpath` strict echouerait. Repli textuel sinon, jamais « considere comme
# absent ».
mirror_drop_alternates() {  # $1 = repo de slot (avec .git)
  local repo="$1" alt="$1/.git/objects/info/alternates" needle="$MIRROR_PATH/objects"
  local line a b tmp dropped=0 key
  [ -s "$alt" ] || return 0
  key="$(mirror_path_key "$needle")"
  tmp="$alt.tmp.$$"
  : > "$tmp" 2>/dev/null || return 0
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    if [ "$line" = "$needle" ] || [ "$(mirror_path_key "$line")" = "$key" ]; then
      dropped=1; continue
    fi
    if command -v realpath >/dev/null 2>&1; then
      a="$(realpath -m -- "$line" 2>/dev/null || realpath -- "$line" 2>/dev/null || true)"
      b="$(realpath -m -- "$needle" 2>/dev/null || realpath -- "$needle" 2>/dev/null || true)"
      if [ -n "$a" ] && [ -n "$b" ] && [ "$a" = "$b" ]; then dropped=1; continue; fi
    fi
    printf '%s\n' "$line" >> "$tmp" 2>/dev/null || true
  done < "$alt"
  if [ "$dropped" -eq 1 ]; then
    if mv -- "$tmp" "$alt" 2>/dev/null; then
      echo "entrypoint: alternates pendant retire de $repo -> $needle (miroir disparu)"
    else
      rm -f -- "$tmp" 2>/dev/null || true
    fi
  else
    rm -f -- "$tmp" 2>/dev/null || true
  fi
  return 0
}

# Semis du _work : ne s'applique QUE s'il n'y a pas de clone exploitable. Un
# repertoire present sans .git (arret brutal entre mkdir et clone) est MIS DE
# COTE, jamais supprime : meme compromis que wch_quarantine_clone -- l'arbre
# reste inspectable, et le job suivant reclone.
mirror_seed_work() {
  local slug="${MIRROR_SLUG:-$(basename "$MIRROR_REMOTE" .git)}"
  local repo="$ACTIONS_RUNNER_INPUT_WORK/$slug/$slug" aside
  if [ -e "$repo/.git" ]; then return 0; fi
  if [ -e "$repo" ]; then
    aside="$repo.stale-$(date -u +%Y%m%dT%H%M%SZ)"
    if mv -- "$repo" "$aside" 2>/dev/null; then
      echo "entrypoint: $repo sans .git -- mis de cote en $aside"
    else
      echo "entrypoint: $repo sans .git et impossible a ecarter -- semis saute (slot froid, nominal)" >&2
      return 0
    fi
  fi
  mkdir -p "$(dirname "$repo")" 2>/dev/null || return 0
  if git clone --quiet --shared --no-checkout "$MIRROR_PATH" "$repo" 2>/dev/null; then
    # origin doit revenir sur HTTPS : un origin laisse sur le miroir ferait
    # fetcher et pousser les jobs contre un depot local, hors du remote reel.
    git -C "$repo" remote set-url origin "$MIRROR_REMOTE" 2>/dev/null || true
    echo "entrypoint: _work seme depuis le miroir (checkout@v4 -> fetch quasi nul)"
  else
    # Echec du semis = slot froid integral, exactement l'etat d'avant #18225.
    # On ne retire RIEN : un clone partiel laisse par git est repris par le bloc
    # work_cache (integrite) ou par le boot suivant.
    echo "entrypoint: semis _work ECHOUE -> slot froid integral (nominal)" >&2
  fi
  return 0
}

if mirror_present; then
  for gitdir in "$ACTIONS_RUNNER_INPUT_WORK"/*/*/.git; do
    [ -e "$gitdir" ] || continue
    mirror_ensure_alternates "${gitdir%/.git}"
  done
  mirror_seed_work
else
  # Miroir absent : retirer les lignes qui le designent (slot seme avant sa
  # disparition). Les autres lignes d'alternates, si un slot en porte, sont
  # conservees telles quelles.
  for gitdir in "$ACTIONS_RUNNER_INPUT_WORK"/*/*/.git; do
    [ -e "$gitdir" ] || continue
    mirror_drop_alternates "${gitdir%/.git}"
  done
  if [ -n "${MIRROR_VERBOSE:-}" ]; then
    echo "entrypoint: miroir absent ($MIRROR_PATH) -- comportement d'avant #18225"
  fi
fi
# TEST-ENTRYPOINT-MIRROR-END
# ---------------------------------------------------------------------------

# --- Sante du cache de depot persistant (#15105) ---------------------------
# Meme hook job-started que le bloc sparse ci-dessus : le volume _work survit
# au conteneur, l'entrypoint est le seul point qui s'execute avant
# l'enregistrement du runner -- donc avant qu'un job n'attrape le cache.
# Deux passes par clone : integrite (refs cassees -> reparation ou purge,
# le gate de la flotte etait une loterie 1-sur-8 sans que rien le nomme),
# puis maintenance (repack -ad, ou -adl sur un depot qui emprunte ses objets a
# un miroir -- cf wch_repack_flags, #18225 ; gc.auto=0 fait que rien d'autre ne
# consolide jamais). Le detail et les
# trois controles positifs (safe.directory, stderr, .promisor) sont dans
# work_cache_health.sh.
WCH_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
. "$WCH_DIR/work_cache_health.sh"
# SECONDE BARRIERE (#16938, meme defaut que #16643). Le correctif est dans
# work_cache_health.sh, dont chaque mesure neutralise desormais son propre rc
# (wch_read) ; ce point d'appel porte la meme garantie, au cas ou une mesure
# future l'oublierait. Sans elle, un rc qui fuit ici tue le conteneur AVANT
# l'enregistrement du runner : aucun job ne tourne, et rien au journal du job
# ne l'explique -- c'est la forme exacte de la panne du slot
# myia-ai-01-wsl-8 (mesure firsthand 2026-09-18 : .git/HEAD reduit a 16 octets
# NUL, aucune ref lisible, 174 demarrages consecutifs morts en rc=128 sans une
# ligne de journal). Ce fichier tourne sous `set -euo pipefail` (ligne 9) et se
# trouve AVANT config.sh : un appel NU y meurt en rc=128 ; en condition de
# `if`, `set -e` est suspendu jusque DANS la fonction appelee, donc l'appel
# survit.
# Forme retenue : `if ! ...` plutot que `|| true` -- les deux survivent, mais
# `|| true` avale la cause en silence, alors qu'un garde de sante doit rester
# diagnosticable (epingle par le test BARRIERE-A-JOURNALISE). La regle que
# porte ce garde -- « un garde de sante ne doit jamais etre la raison pour
# laquelle un slot meurt avant de s'enregistrer » -- vaut aussi contre les
# editions futures du garde lui-meme.
if ! wch_check_workdir "$ACTIONS_RUNNER_INPUT_WORK" "${RUNNER_WORK_CACHE_PACK_THRESHOLD:-16}"; then
  echo "work_cache: garde en echec -- enregistrement POURSUIVI (un garde de sante n'est jamais fatal, #16938)" >&2
fi
# ---------------------------------------------------------------------------

cd "$RUNNER_HOME"

if [ "$(runner_mode)" = "persistent" ]; then
  # Mode #14329 : le conteneur est --restart unless-stopped et le runner
  # NON-ephemere. Enregistrement UNE fois : .runner/.credentials vivent dans
  # le volume monte sur RUNNER_HOME, un restart (daemon, reboot machine) reprend
  # run.sh sans token -- c'est la propriete que le mode achete. --replace couvre
  # la recreeation du volume (l'ancien slot offline est remplace par le nouveau).
  # Semantique des hooks _work ci-dessus en persistent : ils s'executent au BOOT
  # du conteneur, pas a chaque job -- le runner enchaine les jobs sans relancer
  # l'entrypoint. Le trade-off est ecrit dans docs/ci/self-hosted-runners.md.
  runner_restore_dist
  runner_require_externals
  if runner_is_registered; then
    echo "entrypoint: .runner present -- reprise sans re-enregistrement (token non requis)"
  else
    echo "entrypoint: mode persistent, premier enregistrement"
    require_registration_env
    # Pas d'ACTIONS_RUNNER_INPUT_EPHEMERAL : absent = runner non-ephemere.
    export ACTIONS_RUNNER_INPUT_REPLACE=true
    ./config.sh --unattended --disableupdate
  fi
  # Pas de trap 'config.sh remove' : desenregistrer au EXIT tuerait la
  # propriete meme du mode (le restart doit retrouver le slot enregistre).
  exec ./run.sh
fi

# --disableupdate : le conteneur est --rm et le runner --ephemeral (un seul
# job puis mort). Un self-update n'y est donc jamais CONSERVE -- GitHub ordonne
# la mise a jour, le runner telecharge le tarball apres le job, le conteneur
# meurt, --rm efface le telechargement, le suivant repart de l'image epinglee
# et retelecharge. Le travail de mise a jour n'est jamais reutilise.
# Mesure sur les 8 logs de slot de la flotte A, ~6 jours, pivot au rebuild de
# l'image (2026-09-08T07:10Z), image epinglee 2.336.0 alors que GitHub exigeait
# 2.337.0 :
#                              avant     apres
#   'Downloading ... runner'    7939         0
#   'update process finished'   5566         0
#   jobs termines               7535       169
# Soit ~1,05 telechargement par job, et une borne basse d'egress de
# 5566 x 215 Mio = 1,14 Tio perdus pour la seule flotte A sur la periode.
# Les jobs se terminaient normalement : le defaut est du gaspillage de bande
# passante, pas une famine CI -- ne pas invoquer ce bloc pour diagnostiquer
# des jobs qui ne partent pas, la cause serait ailleurs.
# La version du runner EST celle de l'image : elle se bumpe par un rebuild
# (ARG RUNNER_VERSION du Dockerfile), jamais a chaud. Sans ce flag, la prochaine
# exigence de version rearme exactement la meme boucle. Cf #15153, #15164.
# (Ces mesures sont ephemeral-specific ; en persistent le self-update garde
# le meme interdit d'image epinglee, la version se bumpe par rebuild.)
require_registration_env
runner_require_externals
export ACTIONS_RUNNER_INPUT_EPHEMERAL=true
export ACTIONS_RUNNER_INPUT_REPLACE=true
./config.sh --unattended --ephemeral --replace --disableupdate

# Teardown symetrique : --ephemeral desenregistre de lui-meme apres le job ;
# le trap couvre les sorties en erreur (config echoue, run.sh interrompu).
trap './config.sh remove --unattended || true' EXIT

exec ./run.sh
