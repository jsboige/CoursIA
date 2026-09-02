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

cd /opt/runner
./config.sh --unattended --ephemeral --replace

# Teardown symetrique : --ephemeral desenregistre de lui-meme apres le job ;
# le trap couvre les sorties en erreur (config echoue, run.sh interrompu).
trap './config.sh remove --unattended || true' EXIT

exec ./run.sh
