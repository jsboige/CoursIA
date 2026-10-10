#!/usr/bin/env bash
# Crochet JOB-STARTED pour slots persistants : desarmement inter-jobs du
# residu sparse-checkout et des refs distantes dangling (#20174).
#
# POURQUOI CE FICHIER EXISTE. En mode persistent l'entrypoint ne rejoue ses
# blocs de desarmement qu'au BOOT du conteneur : entre deux jobs, un workflow
# qui pose `core.sparseCheckout` (ex. catalog-cron, checkout partiel) laisse
# le drapeau arme au suivant, qui herite d'un arbre ampute (« git status »
# propre, 1 fichier sous scripts/ au lieu de 1087) et echoue en [Errno 2]
# sur un fichier pourtant versionne. Le retrait du label `coursia-ephemeral`
# des slots persistants (2026-10-10T14:12Z) a arrete l'hemorragie ; ce
# crochet est la condition du retour au pool -- SANS lui, remettre le label
# referait le cycle de rouges en quelques heures.
#
# SEMANTIQUE IDENTIQUE aux blocs de l'entrypoint (source de verite :
# entrypoint.sh, « desarmement de l'etat sparse-checkout residuel » et
# « desarmement des refs distantes dangling ») -- deux cas, deux couts :
#   drapeau arme    = purge du clone (le checkout suivant reclonera) ;
#   motifs seuls    = retrait du fichier, cache incremental conserve
#                     (~40-51 s/job, #14285).
#
# FAIL-OPEN PAR CONSTRUCTION (#16938) : un garde de sante n'est jamais la
# raison pour laquelle un job meurt. Tout echec est journalise sur stderr et
# le script rend 0. Le crochet est invoque par le runner via
# ACTIONS_RUNNER_HOOK_JOB_STARTED et est idempotent : un second passage ne
# trouve rien a desarmer.
#
# Deploiement (detail dans docs/ci/self-hosted-runners.md, section Mode
# persistent) : copier ce script dans le volume de config du slot
# (/opt/runner/job-start-disarm.sh, chmod +x) puis re-creer le conteneur avec
# -e ACTIONS_RUNNER_HOOK_JOB_STARTED=/opt/runner/job-start-disarm.sh
set -uo pipefail   # PAS -e : chaque clone est traite independamment, un echec
                   # local ne doit couvrir ni les autres clones ni le rc final.

WORK="${ACTIONS_RUNNER_INPUT_WORK:-/home/runner/_work}"

disarm_one() {  # <chemin-du-clone>
  local repo="$1" gitdir="$1/.git" ref sha
  if [ -n "$(git -C "$repo" config --local --get core.sparseCheckout 2>/dev/null || true)" ]; then
    echo "job-start-disarm: sparse ARME dans $repo -- purge du clone (le checkout suivant reclonera)" >&2
    rm -rf "$repo" || echo "job-start-disarm: purge impossible de $repo -- signale, job poursuivi" >&2
    return 0
  fi
  if [ -f "$gitdir/info/sparse-checkout" ]; then
    echo "job-start-disarm: motifs sparse inertes dans $repo -- retrait du fichier, clone conserve" >&2
    rm -f "$gitdir/info/sparse-checkout" || true
  fi
  while read -r ref sha; do
    if ! git -C "$repo" cat-file -e "$sha^{object}" 2>/dev/null; then
      echo "job-start-disarm: ref distante dangling $ref -- suppression (objet absent)" >&2
      git -C "$repo" update-ref -d "$ref" 2>/dev/null || true
    fi
  done < <(git -C "$repo" for-each-ref --format='%(refname) %(objectname)' refs/remotes 2>/dev/null)
}

for gitdir in "$WORK"/*/*/.git; do
  [ -e "$gitdir" ] || continue
  disarm_one "${gitdir%/.git}"
done
exit 0
