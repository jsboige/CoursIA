#!/usr/bin/env bash
# Sante du cache de depot persistant `_work` (#15105).
#
# POURQUOI CE FICHIER EXISTE
# --------------------------
# `actions/checkout` pose `gc.auto = 0` dans le depot du slot : correct pour
# un workspace jetable, faux depuis que #14285 a rendu ce workspace persistant.
# Deux defauts d'une meme cause, mesures firsthand sur ai-01 le 2026-09-07 :
#
#   1. Croissance des packs sans borne. Chaque job depose un pack promisor de
#      plus (recuperation paresseuse sous partialclonefilter=blob:none) ; slot 1
#      : 264 packs dont 263 promisor, 849M de .git, et le compte croit a
#      chaque job. Rien ne consolide jamais rien.
#   2. Aucune precondition d'integrite. Le slot 7 portait 1471 fichiers de
#      ref de ZERO octet (sequelle d'arrets brutaux : dirent validee, contenu
#      jamais ecrit). `git fetch` bute dessus et abandonne -- le gate de toute
#      la flotte etait devenu une loterie 1-sur-8, et AUCUN organe ne l'avait
#      nomme.
#
# Ce fichier est la moitie executante ; l'autre moitie (cablement, knob,
# garde de fraicheur) vit dans entrypoint.sh et supervise.sh. Il est SOURCE,
# jamais execute seul -- les tests le sourcent de la meme facon
# (test_work_cache_health.sh).
#
# LES TROIS CONTROLES POSITIFS que tout organe ecrit ici doit porter
# (chacun vient d'un faux negatif REEL, cf #15105) :
#
#   - safe.directory : `git` refuse un depot d'un autre uid ("dubious
#     ownership") ET, stderr supprime, rend ZERO ref sans erreur visible --
#     indiscernable d'un cache sain. Toute lecture passe par wch_git, qui
#     porte -c safe.directory='*'.
#   - stderr, pas le code de retour : `git for-each-ref` rend rc=0 avec une
#     ref cassee ; le seul canal qui la nomme est le warning "ignoring broken
#     ref" sur STDERR (mesure, git 2.43 : rc=0 + warning).
#   - .promisor vide est LEGITIME : c'est un marqueur de pack a recuperation
#     paresseuse. La reparation ne touche QUE .git/refs et .git/logs -- JAMAIS
#     .git/objects, ou un `find -type f -empty -delete` naif emporterait les
#     marqueurs et fabriquerait une seconde corruption deguisee en reparation.
#
# Le geste de reparation (refs vides retirees, objects/ hors perimetre) est
# celui prouve sur le slot 7 : 1472 refs cassees -> 0, les 2,5 Gio d'objets
# intacts, 0 octet de clone.
#
# La reparation irrecuperable est le PURGE du clone (rm -rf du checkout) :
# le job suivant reclonera (cout ~80-148 s mesure #14285, contre un cache qui
# empoisonne silencieusement tout job qui l'attrape). C'est le meme geste que
# le desarmement sparse #14385, et il accepte le meme cout sur les pools lean
# (un .lake chaud perdu se reconstruit ; un cache corrompu ne se diagnostique
# pas tout seul).

# Toute lecture git du cache passe par ici : le controle positif
# "dubious ownership" est porte par l'appel, pas par la chance que l'uid
# d'execution coincide avec celui d'actions/checkout.
wch_git() {
  git -c safe.directory='*' "$@"
}

# NEUTRALISATION DU CODE DE RETOUR DES MESURES (#16938).
#
# Le banc porte `set -o pipefail` sans `-e` ; l'entrypoint, lui, porte
# `set -euo pipefail` (entrypoint.sh:12). Sous ce shell, une LECTURE qui
# echoue remonte son rc et TUE l'appelant :
#
#   - git sur un depot illisible (HEAD detruit, ownership refuse) -> rc=128
#   - ls sur un glob sans correspondance (depot sans pack -- etat NOMINAL
#     d'un cache frais) -> rc=2, qui traverse le `| wc -l` sous pipefail
#
# Mesure du 2026-09-21, seuil 16 (la valeur de production), sentinelle posee
# apres l'appel : `wch_check_workdir` rend 128 sur un depot illisible et 2 sur
# un depot sain sans pack ; dans les deux cas la sentinelle n'est JAMAIS
# atteinte, donc l'entrypoint meurt avant d'enregistrer le runner -- aucun job
# ne tourne, aucun journal ne l'explique (174 demarrages morts consecutifs sur
# le slot 8). Sur le depot illisible la mort survient a la PREMIERE ligne de
# wch_integrity_pass, donc AVANT la branche de purge qui est precisement le
# geste de reparation de ce cas.
#
# C'est ce que le contrat de wch_integrity_pass interdit : un garde de sante ne
# doit JAMAIS etre la raison pour laquelle un slot meurt. La consequence de
# fond : le rc d'une lecture n'est pas une mesure. wch_broken_refs mesure sur
# stderr, wch_ref_count et wch_pack_count sur stdout -- aucun des trois n'a
# d'autorite sur le sort du conteneur. Neutralise A LA SOURCE, une fois, ici ;
# le point d'appel porte une seconde barriere (entrypoint.sh).
wch_read() {
  # `"$@"` en position gauche d'un `||` : le rc de la lecture est consomme ici.
  # Rendre 0 est le SEUL contrat de cette fonction -- sa sortie est la mesure.
  "$@" || true
}

# Refs cassees du depot, une par ligne -- lues sur le CANAL stderr de
# for-each-ref (rc=0 avec une ref cassee : le code de retour ne dit rien).
# Sortie vide = aucune ref cassee detectee. Un depot illisible (fatal:
# dubious ownership, .git detruit a moitie) rend une sortie vide AUSSI --
# c'est pourquoi l'appelant croise toujours avec wch_ref_count, et ne
# conclut "sain" que sur un compte > 0.
wch_broken_refs() {
  local repo="$1"
  # #16643 neutralisait le meme rc en ligne (`{ ...; } || true`) ; #16938 le
  # neutralise A LA SOURCE, ici, une fois pour les trois lectures (cf l'en-tete
  # l.60-87). Meme effet, un seul point a maintenir.
  wch_read wch_git -C "$repo" for-each-ref 2>&1 >/dev/null \
    | sed -n 's/^warning: ignoring broken ref //p'
}

# Nombre de refs lisibles. Le controle positif du detecteur : un depot
# existant dont ce compte rend 0 est INDISSERNABLE d'un depot refuse pour
# ownership ou d'un .git muet -- on ne conclut jamais "sain" dessus.
wch_ref_count() {
  local repo="$1"
  wch_read wch_git -C "$repo" for-each-ref --format 'x' 2>/dev/null | wc -l | tr -d ' '
}

# Retire les fichiers de ref/reflog de ZERO octet, dans .git/refs et
# .git/logs UNIQUEMENT. Le perimetre EST la garde .promisor : les marqueurs
# promisor vivent sous .git/objects/pack et ne peuvent pas etre atteints
# d'ici. Rend le nombre de fichiers retires.
wch_drop_empty_refs() {
  local repo="$1" n=0 d f
  for d in "$repo/.git/refs" "$repo/.git/logs"; do
    [ -d "$d" ] || continue
    # -print0/read -d '' : un nom de ref contenant un saut de ligne resterait
    # invisible a un `for` sur la sortie texte.
    while IFS= read -r -d '' f; do
      # if et pas && : l'entrypoint tourne sous set -e ; un rm echoue
      # n'a jamais le droit de tuer le conteneur avant l'enregistrement.
      if rm -f -- "$f"; then n=$(( n + 1 )); fi
    done < <(find "$d" -type f -empty -print0 2>/dev/null)
  done
  printf '%s\n' "$n"
}

# Compte de packs du depot -- la grandeur que la maintenance borne.
# Le glob sans correspondance est le cas NOMINAL d'un cache frais (aucun pack
# tant qu'aucun fetch n'a eu lieu) : `ls` rend alors rc=2, neutralise par
# wch_read -- sans quoi la maintenance tuait un slot SAIN.
wch_pack_count() {
  local repo="$1"
  wch_read ls "$repo"/.git/objects/pack/*.pack 2>/dev/null | wc -l | tr -d ' '
}

# Compte de lignes non vides d'un bloc de texte. `grep -c` rend rc=1 quand le
# compte est ZERO -- exactement le cas de la ligne de purge, ou `broken` est
# vide (depot illisible) alors que le compte de refs est nul. Sous `set -e`, un
# `grep -c` non garde tuerait le conteneur au moment precis ou il traite
# l'incident (#16643, mesure du 2026-09-18 sur le slot myia-ai-01-wsl-8).
wch_count_lines() {
  printf '%s
' "$1" | grep -c . || true
}

# Precondition d'integrite AVANT qu'un slot n'accepte un job : detecte les
# refs cassees, repare (refs/logs vides retires), re-verifie, et purge le
# clone si le depot reste muet. Rend 0 dans tous les cas -- un garde de sante
# ne doit JAMAIS etre la raison pour laquelle un slot meurt avant de
# s'enregistrer ; ses decisions se lisent dans son journal.
wch_integrity_pass() {
  local repo="$1" broken n refs_purged
  [ -d "$repo/.git" ] || return 0

  broken="$(wch_broken_refs "$repo")"
  if [ -n "$broken" ]; then
    n="$(wch_count_lines "$broken")"
    echo "work_cache: $n ref(s) cassee(s) dans $repo -- reparation (refs/logs vides retires, objects/ hors perimetre)"
    refs_purged="$(wch_drop_empty_refs "$repo")"
    echo "work_cache: $refs_purged fichier(s) de zero octet retire(s) sous .git/refs et .git/logs"
  fi

  # Re-verification APRES reparation. Les deux conditions qui suivent sont
  # les deux faces du meme faux negatif : un depot qui rend encore des refs
  # cassees est mal repare ; un depot dont AUCUNE ref n'est lisible est
  # indiscernable d'un cache refuse (ownership) ou muet -- dans les deux cas
  # le seul etat honnete est le clone frais, pas un "sain" non prouve.
  broken="$(wch_broken_refs "$repo")"
  n="$(wch_ref_count "$repo")"
  # ${n:-0} : un compte vide ferait echouer `[ -eq ]` en rc=2, et le garde
  # mourrait une derniere fois juste avant de prononcer la purge.
  if [ -n "$broken" ] || [ "${n:-0}" -eq 0 ]; then
    echo "work_cache: $repo IRRECUPERABLE (${n} refs lisibles, encore $(wch_count_lines "$broken") cassees) -- purge du clone, le job suivant reclonera"
    rm -rf -- "$repo"
    return 0
  fi
  [ -n "${WCH_VERBOSE:-}" ] && echo "work_cache: $repo sain ($n refs lisibles)"
  return 0
}

# Maintenance PERIODIQUE du cache : consolide les packs quand leur compte
# depasse le seuil, avec la mesure avant/apres dans le journal. gc.auto=0
# (pose par actions/checkout) fait que rien d'autre ne consolidera jamais --
# sans cette borne, le compte croit a chaque job sans plafond (#15105
# defaut 1 : 264 packs sur le slot 1).
#
# `git repack -ad` est SUR sur un clone partiel blob:none, mesure sur un
# fixture au filtre reellement honore (blobs absents du depot local) :
# 5 packs promisor -> 1, reseau nul pendant le repack, marqueur .promisor
# preserve sur le pack consolide, et le lazy-fetch comme le fetch
# incremental fonctionnent apres. Le seuil fait que le repack ne se paye
# qu'une fois tous les N jobs, jamais a chaque job.
#
# Un echec de repack n'est PAS fatal : il se dit dans le journal et le
# prochain passage retentera -- le compte reste alors ce qu'il etait, le
# garde ne cree pas de regression.
wch_maintenance_pass() {
  local repo="$1" threshold="$2" before after
  [ "$threshold" -gt 0 ] || return 0
  [ -d "$repo/.git" ] || return 0
  before="$(wch_pack_count "$repo")"
  if [ "$before" -le "$threshold" ]; then
    return 0
  fi
  if ! wch_git -C "$repo" repack -ad >/dev/null 2>&1; then
    echo "work_cache: repack ECHEC dans $repo ($before packs) -- cache conserve tel quel, nouvelle tentative au prochain passage" >&2
    return 0
  fi
  after="$(wch_pack_count "$repo")"
  echo "work_cache: $repo repack $before -> $after packs (seuil $threshold)"
  return 0
}

# Passe complete sur un _work : integrite puis maintenance, sur chaque clone
# trouve sous <workdir>/<repo>/<repo>. Cote entrypoint, ce bloc tourne
# AVANT config.sh : le runner n'est pas encore enregistre, donc aucun job
# n'est ralenti en vol -- le cout de la maintenance est paye par le slot
# entre deux jobs, sous les bornes d'I/O de son propre conteneur
# (--device-write-bps + slice agregee, #15091/#15103), sans plomberie hote.
wch_check_workdir() {
  local workdir="$1" threshold="${2:-0}" gitdir repo
  [ -d "$workdir" ] || return 0
  for gitdir in "$workdir"/*/*/.git; do
    [ -e "$gitdir" ] || continue
    repo="${gitdir%/.git}"
    wch_integrity_pass "$repo"
    wch_maintenance_pass "$repo" "$threshold"
  done
  return 0
}
