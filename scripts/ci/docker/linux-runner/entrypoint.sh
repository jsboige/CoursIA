#!/bin/bash
# Enregistrement ephemere du runner conteneurise. Le token ne passe JAMAIS
# par argv (pattern manage_self_hosted_runner.py) : config.sh lit
# ACTIONS_RUNNER_INPUT_TOKEN. Requis a l'appel (docker run -e ...) :
#   ACTIONS_RUNNER_INPUT_TOKEN   token d'enregistrement (valable 1 h)
#   ACTIONS_RUNNER_INPUT_URL     https://github.com/jsboige/CoursIA
#   ACTIONS_RUNNER_INPUT_NAME    myia-po-2024-linux-docker
#   ACTIONS_RUNNER_INPUT_LABELS  self-hosted,coursia-ephemeral,coursia-linux
set -euo pipefail

: "${ACTIONS_RUNNER_INPUT_TOKEN:?RUNNER token manquant}"
: "${ACTIONS_RUNNER_INPUT_URL:?RUNNER url manquante}"
: "${ACTIONS_RUNNER_INPUT_NAME:?RUNNER name manquant}"
: "${ACTIONS_RUNNER_INPUT_LABELS:?RUNNER labels manquants}"

export ACTIONS_RUNNER_INPUT_EPHEMERAL=true
export ACTIONS_RUNNER_INPUT_REPLACE=true
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
  while read -r ref sha; do
    if ! git -C "$repo" cat-file -e "$sha^{object}" 2>/dev/null; then
      echo "entrypoint: ref distante dangling $ref -- suppression (objet absent)"
      git -C "$repo" update-ref -d "$ref" 2>/dev/null || true
    fi
  done < <(git -C "$repo" for-each-ref --format='%(refname) %(objectname)' refs/remotes 2>/dev/null)
done
# TEST-ENTRYPOINT-DANGLING-REFS-END

# --- Sante du cache de depot persistant (#15105) ---------------------------
# Meme hook job-started que le bloc sparse ci-dessus : le volume _work survit
# au conteneur, l'entrypoint est le seul point qui s'execute avant
# l'enregistrement du runner -- donc avant qu'un job n'attrape le cache.
# Deux passes par clone : integrite (refs cassees -> reparation ou purge,
# le gate de la flotte etait une loterie 1-sur-8 sans que rien le nomme),
# puis maintenance (repack -ad si le compte de packs depasse le seuil ;
# gc.auto=0 fait que rien d'autre ne consolide jamais). Le detail et les
# trois controles positifs (safe.directory, stderr, .promisor) sont dans
# work_cache_health.sh.
WCH_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
. "$WCH_DIR/work_cache_health.sh"
wch_check_workdir "$ACTIONS_RUNNER_INPUT_WORK" "${RUNNER_WORK_CACHE_PACK_THRESHOLD:-16}"
# ---------------------------------------------------------------------------

cd /opt/runner
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
./config.sh --unattended --ephemeral --replace --disableupdate

# Teardown symetrique : --ephemeral desenregistre de lui-meme apres le job ;
# le trap couvre les sorties en erreur (config echoue, run.sh interrompu).
trap './config.sh remove --unattended || true' EXIT

exec ./run.sh
