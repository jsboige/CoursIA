#!/usr/bin/env bash
# Harnais du crochet JOB-STARTED (job-start-disarm.sh), #20174.
#
# CE QUE CE HARNAIS EXISTE POUR EMPECHER
# --------------------------------------
# Le bloc de desarmement de l'entrypoint ne tourne qu'au BOOT du conteneur :
# en persistent, un job qui pose le drapeau sparse arme le suivant. Le crochet
# job-started est la piece qui retablit la couverture PAR JOB. Retirer la
# purge du clone arme (cas 1), retirer la distinction armes/inertes (cas 2),
# rendre le crochet fatal (cas 6-7) ou non idempotent (cas 5) fait rougir
# ici -- silencieusement autrement.
#
# Aucun etat reel n'est touche : les clones de fixture vivent dans un
# repertoire jetable (mktemp -d), le crochet est appele avec
# ACTIONS_RUNNER_INPUT_WORK pointant dessus.
#
# Usage : bash scripts/ci/docker/linux-runner/persist/test_job_start_disarm.sh
# Sortie : "N PASS / M FAIL", rc=0 si M==0.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HOOK="$HERE/job-start-disarm.sh"
PASS=0; FAIL=0

ck() { # <nom> <attendu> <rendu>
  if [ "$2" = "$3" ]; then PASS=$((PASS+1)); else FAIL=$((FAIL+1)); echo "FAIL $1: attendu [$2] rendu [$3]" >&2; fi
}

T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
export ACTIONS_RUNNER_INPUT_WORK="$T"

mk_repo() { # <nom> : un vrai mini-depot git sous $T/<nom>
  mkdir -p "$T/$1"
  git -C "$T/$1" init -q -b main 2>/dev/null || git -C "$T/$1" init -q
  git -C "$T/$1" -c user.email=t@t -c user.name=t commit -q --allow-empty -m init
}

run_hook() { bash "$HOOK" >/dev/null 2>"$T/hook.err"; }

# --- Fixtures : CoursIA/CoursIA est le layout reel _work/<repo>/<repo> -----
mkdir -p "$T/CoursIA"

# Cas 1 : drapeau ARME -> clone purge (le checkout suivant reclonera).
mk_repo CoursIA/arme
git -C "$T/CoursIA/arme" config core.sparseCheckout true
printf '/*\n' > "$T/CoursIA/arme/.git/info/sparse-checkout"

# Cas 2 : motifs SEULS (drapeau absent) -> fichier retire, clone conserve.
mk_repo CoursIA/inertes
printf '/*\n' > "$T/CoursIA/inertes/.git/info/sparse-checkout"

# Cas 3 : clone sain -> rien a faire, clone conserve.
mk_repo CoursIA/sain

# Cas 4 : ref distante dangling -> supprimee ; ref valide -> conservee.
mk_repo CoursIA/dangl
sha_bon="$(git -C "$T/CoursIA/dangl" rev-parse HEAD)"
git -C "$T/CoursIA/dangl" update-ref refs/remotes/origin/vivante "$sha_bon"
sha_mort="$(printf 'temoin' | git -C "$T/CoursIA/dangl" hash-object -w --stdin)"
git -C "$T/CoursIA/dangl" update-ref refs/remotes/origin/morte "$sha_mort"
obj="$T/CoursIA/dangl/.git/objects/${sha_mort:0:2}/${sha_mort:2}"
rm -f "$obj"   # l'objet disparait, la ref pointe dans le vide

# Cas 5-6 : repertoire .git vide (clone avorte par un crash anterieur) ->
# ignore sans echec, rc 0.
mkdir -p "$T/CoursIA/vide/.git"

run_hook

ck "cas1 clone arme purge"        "absent" "$([ -d "$T/CoursIA/arme" ] && echo present || echo absent)"
ck "cas2 clone inertes conserve"  "present" "$([ -d "$T/CoursIA/inertes" ] && echo present || echo absent)"
ck "cas2 motifs retires"          "absent" "$([ -f "$T/CoursIA/inertes/.git/info/sparse-checkout" ] && echo present || echo absent)"
ck "cas3 clone sain conserve"     "present" "$([ -d "$T/CoursIA/sain" ] && echo present || echo absent)"
ck "cas4 ref dangling supprimee"  "absent"  "$([ -n "$(git -C "$T/CoursIA/dangl" rev-parse --verify -q refs/remotes/origin/morte && echo x)" ] && echo present || echo absent)"
ck "cas4 ref vivante conservee"   "present" "$([ -n "$(git -C "$T/CoursIA/dangl" rev-parse --verify -q refs/remotes/origin/vivante && echo x)" ] && echo present || echo absent)"
ck "cas6 rc hook"                 "0" "$?"

# Cas 7 : idempotence -- un second passage ne trouve rien et rend 0.
run_hook
ck "cas7 second passage rc"       "0" "$?"
ck "cas7 sain toujours conserve"  "present" "$([ -d "$T/CoursIA/sain" ] && echo present || echo absent)"

echo "$PASS PASS / $FAIL FAIL"
[ "$FAIL" -eq 0 ]
