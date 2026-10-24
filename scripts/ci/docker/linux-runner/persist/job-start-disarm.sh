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
# SEMANTIQUE DERIVEE des blocs de l'entrypoint (source de verite :
# entrypoint.sh, « desarmement de l'etat sparse-checkout residuel » et
# « desarmement des refs distantes dangling »), avec une divergence
# ASSUMEE sur le cas « drapeau arme » -- l'entrypoint purge au BOOT du
# conteneur (sans job en vol, donc sans course) ; ce crochet purgeait
# AUSSI, mais il tourne entre le prepare du job et son premier step :
# purger le clone supprime le CWD du step checkout, et le runner ne peut
# alors PAS DEMARRER le process (ENOENT .NET attribue a tort a
# « externals/node24/bin/node », erreur « No such file or directory » au
# checkout -- mesure 2026-10-20 sur les 7 slots persist, 22-54 occurrences
# par slot, chaque job suivant un job sparse-arme tué en paire
# step/post-step ; diagnostic croise ai-01:CoursIA-2 sur #20921
# c.6298429793). Deux cas, deux couts :
#   drapeau arme    = desarmement EN PLACE (git sparse-checkout disable :
#                     drapeau retire + arbre complet rematerialise depuis
#                     les objets locaux, sans reseau, clone conserve) ;
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
RUNNER_HOME="${RUNNER_HOME:-/opt/runner}"
# Externals dont l'absence tue le job AVANT sa premiere commande (#21745,
# limb C : `externals/node24/bin/node` absent -> actions/checkout ne demarre
# meme pas, log de 45 lignes, aucune signature de clone). La liste est un
# knob : un parc qui n'embarque pas node24 pourra la reduire sans patcher
# ce fichier. Ce crochet ne peut pas empecher le dispatch (il tourne APRES
# le prepare du job) : il NOMME la cause sur le canal que lit
# `scripts/ci/classify_infra_leg.py`, pour que la jambe soit classee infra
# et non imputee au diff. Le refus de dispatch, lui, est porte par
# entrypoint.sh (avant config.sh).
RUNNER_REQUIRED_EXTERNALS="${RUNNER_REQUIRED_EXTERNALS:-node24}"

signal_missing_externals() {
  local name missing=""
  for name in $RUNNER_REQUIRED_EXTERNALS; do
    [ -e "$RUNNER_HOME/externals/$name/bin/node" ] || missing="$missing $name"
  done
  [ -n "$missing" ] || return 0
  for name in $missing; do
    echo "job-start-disarm: INFRA_EXTERNALS_MISSING externals/$name/bin/node absent sous $RUNNER_HOME -- la jambe ne peut pas demarrer (cause infra, pas diff de PR)" >&2
  done
  return 0
}

# Supprime les refs `pull/*` sans LIRE AUCUN objet : `update-ref --stdin`
# ne touche que les fichiers de ref, donc aucun fetch paresseux n'est
# declenche (contraste avec `cat-file -e`, qui materialise l'objet et cache
# le dangling -- piege mesure du limb A). Chaque PR vue depose un
# `refs/remotes/{remote}/pull/N/{head,merge}` que le refspec explicite de
# actions/checkout ne purge jamais : mesure 4 600 refs dont la majorite
# obsolete. Les refs encore pertinentes sont recreees au prochain fetch.
prune_pull_refs() {  # <repo>
  local repo="$1" list
  list="$(mktemp -t jsd-pull.XXXXXX 2>/dev/null)" || return 0
  git -C "$repo" for-each-ref --format='delete %(refname)' refs/remotes 2>/dev/null \
    | grep '^delete .*/pull/' > "$list" 2>/dev/null || true
  if [ -s "$list" ]; then
    git -C "$repo" update-ref --stdin < "$list" 2>/dev/null || true
  fi
  rm -f "$list" 2>/dev/null || true
  return 0
}

disarm_one() {  # <chemin-du-clone>
  local repo="$1" gitdir="$1/.git" ref sha
  if [ -n "$(git -C "$repo" config --local --get core.sparseCheckout 2>/dev/null || true)" ]; then
    echo "job-start-disarm: sparse ARME dans $repo -- desarmement en place (sparse-checkout disable)" >&2
    if git -C "$repo" sparse-checkout disable >/dev/null 2>&1; then
      # Ceinture obligatoire : selon la version de git, disable peut laisser
      # core.sparseCheckout=true sans fichier de motifs -- le checkout suivant
      # amputerait alors TOUT l'arbre (motifs vides). Le drapeau est leve
      # explicitement quoi qu'il arrive.
      git -C "$repo" config --local --unset core.sparseCheckout 2>/dev/null || true
      return 0
    fi
    # Repli (fail-open) : retirer drapeau et motifs SANS toucher au repertoire
    # de travail -- le CWD du job suivant doit exister au demarrage du step.
    git -C "$repo" config --local --unset core.sparseCheckout 2>/dev/null || true
    rm -f "$gitdir/info/sparse-checkout" 2>/dev/null || true
    echo "job-start-disarm: sparse-checkout disable a echoue dans $repo -- drapeau et motifs retires, arbre partiel assume (le checkout suivant le reparera)" >&2
    return 0
  fi
  if [ -f "$gitdir/info/sparse-checkout" ]; then
    echo "job-start-disarm: motifs sparse inertes dans $repo -- retrait du fichier, clone conserve" >&2
    rm -f "$gitdir/info/sparse-checkout" || true
  fi
  # Les refs pull/* partent d'abord : aucune lecture d'objet, donc aucun
  # fetch paresseux possible, et cela retire d'un coup la majorite du parc
  # de refs (mesure : ~4 600 dont la majorite obsolete).
  prune_pull_refs "$repo"

  # Reste des refs distantes : detection par LOT, bornee. Le `cat-file -e`
  # par ref de la version precedente coutait O(refs * packs) -- ~23 min sur
  # un cache a 21 000 packs (fix #20697) -- et chaque appel pouvait
  # declencher un fetch paresseux sans plafond sur un clone partiel.
  # Ici : UN seul `--batch-check` pour toutes les SHAs, GIT_NO_LAZY_FETCH=1
  # (no-op avant git 2.46) pour interdire le fetch, timeout 60 en borne
  # haute. stderr reste visible : un timeout doit etre diagnosticable
  # (l'incident du slot 3 po-2024 etait muet a cause du 2>/dev/null).
  local refs_list miss_list
  refs_list="$(mktemp -t jsd-refs.XXXXXX 2>/dev/null)" || return 0
  miss_list="$(mktemp -t jsd-miss.XXXXXX 2>/dev/null)" || { rm -f "$refs_list"; return 0; }
  git -C "$repo" for-each-ref --format='%(refname) %(objectname)' refs/remotes 2>/dev/null > "$refs_list" || true
  if [ -s "$refs_list" ]; then
    awk '{print $NF}' "$refs_list" | sort -u \
      | GIT_NO_LAZY_FETCH=1 timeout 60 git -C "$repo" cat-file --batch-check 2>/dev/null \
      | awk '$2 == "missing" { print $1 }' > "$miss_list" || true
    if [ -s "$miss_list" ]; then
      while read -r sha; do
        [ -n "$sha" ] || continue
        awk -v s="$sha" '$NF == s { print $1 }' "$refs_list" | while read -r ref; do
          [ -n "$ref" ] || continue
          echo "job-start-disarm: ref distante dangling $ref -- suppression (objet absent)" >&2
          git -C "$repo" update-ref -d "$ref" 2>/dev/null || true
        done
      done < "$miss_list"
    fi
  fi
  rm -f "$refs_list" "$miss_list" 2>/dev/null || true
}

signal_missing_externals

for gitdir in "$WORK"/*/*/.git; do
  [ -e "$gitdir" ] || continue
  disarm_one "${gitdir%/.git}"
done
exit 0
