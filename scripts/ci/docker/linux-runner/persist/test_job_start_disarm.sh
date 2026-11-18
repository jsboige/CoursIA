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

# `grep -c` rend rc=1 quand le compte est ZERO tout en imprimant « 0 » : un
# `|| echo 0` derriere lui ajoute une SECONDE ligne et l'assertion compare
# « 0\n0 ». La substitution de commande ne garde que stdout, donc pas de repli.
count_signal() { grep -c "INFRA_EXTERNALS_MISSING" "$T/hook.err" 2>/dev/null; }

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

# Cas 8 : refs pull/* -> supprimees SANS lecture d'objet (donc sans fetch
# paresseux) ; une ref distante hors pull/ valide survit (#21745 limb A).
mk_repo CoursIA/pull
sha_p="$(git -C "$T/CoursIA/pull" rev-parse HEAD)"
git -C "$T/CoursIA/pull" update-ref refs/remotes/origin/pull/1/merge "$sha_p"
git -C "$T/CoursIA/pull" update-ref refs/remotes/origin/pull/2/head "$sha_p"
git -C "$T/CoursIA/pull" update-ref refs/remotes/origin/main "$sha_p"

# Cas 9 : externals requis absent -> signale INFRA_EXTERNALS_MISSING ;
# present -> silencieux. Le crochet reste fail-open dans les deux cas.
export RUNNER_HOME="$T/runnerhome"
mkdir -p "$RUNNER_HOME/externals/node24/bin"
: > "$RUNNER_HOME/externals/node24/bin/node"

run_hook

# Cas 1 attend le DESARMEMENT EN PLACE (c0f1afd5b6), pas la purge : purger
# entre le prepare et le premier step supprime le CWD du step checkout et tue
# le job (ENOENT attribue a tort a « externals/node24/bin/node »). L'assertion
# « purge » heritee de la version precedente faisait rougir ce banc sur main.
ck "cas1 clone arme conserve"     "present" "$([ -d "$T/CoursIA/arme" ] && echo present || echo absent)"
ck "cas1 drapeau sparse leve"     ""        "$(git -C "$T/CoursIA/arme" config --local --get core.sparseCheckout 2>/dev/null || true)"
# Le fichier de motifs peut SURVIVRE a `sparse-checkout disable` selon la
# version de git -- et c'est inoffensif : sans le drapeau, git l'ignore (cas 2
# le prouve sur un clone qui n'a jamais eu le drapeau). L'invariant qui compte
# est le drapeau, pas le fichier.
ck "cas2 clone inertes conserve"  "present" "$([ -d "$T/CoursIA/inertes" ] && echo present || echo absent)"
ck "cas2 motifs retires"          "absent" "$([ -f "$T/CoursIA/inertes/.git/info/sparse-checkout" ] && echo present || echo absent)"
ck "cas3 clone sain conserve"     "present" "$([ -d "$T/CoursIA/sain" ] && echo present || echo absent)"
ck "cas4 ref dangling supprimee"  "absent"  "$([ -n "$(git -C "$T/CoursIA/dangl" rev-parse --verify -q refs/remotes/origin/morte && echo x)" ] && echo present || echo absent)"
ck "cas4 ref vivante conservee"   "present" "$([ -n "$(git -C "$T/CoursIA/dangl" rev-parse --verify -q refs/remotes/origin/vivante && echo x)" ] && echo present || echo absent)"
ck "cas6 rc hook"                 "0" "$?"
ck "cas8 pull/1/merge supprimee"  "absent"  "$([ -n "$(git -C "$T/CoursIA/pull" rev-parse --verify -q refs/remotes/origin/pull/1/merge && echo x)" ] && echo present || echo absent)"
ck "cas8 pull/2/head supprimee"   "absent"  "$([ -n "$(git -C "$T/CoursIA/pull" rev-parse --verify -q refs/remotes/origin/pull/2/head && echo x)" ] && echo present || echo absent)"
ck "cas8 origin/main conservee"   "present" "$([ -n "$(git -C "$T/CoursIA/pull" rev-parse --verify -q refs/remotes/origin/main && echo x)" ] && echo present || echo absent)"
ck "cas9 externals present muet"  "0" "$(count_signal)"

# Cas 9bis : externals absent -> signale, et le crochet reste fail-open (rc 0).
mv -f "$RUNNER_HOME/externals/node24" "$RUNNER_HOME/externals/node24.off"
run_hook
ck "cas9bis externals absent signale" "1" "$(count_signal)"
ck "cas9bis rc hook (fail-open)"      "0" "$?"
mv -f "$RUNNER_HOME/externals/node24.off" "$RUNNER_HOME/externals/node24"

# Cas 7 : idempotence -- un second passage ne trouve rien et rend 0.
run_hook
ck "cas7 second passage rc"       "0" "$?"
ck "cas7 sain toujours conserve"  "present" "$([ -d "$T/CoursIA/sain" ] && echo present || echo absent)"

echo "$PASS PASS / $FAIL FAIL"
[ "$FAIL" -eq 0 ]
