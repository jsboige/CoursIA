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

# Un clone porte-t-il ses objets EN VRAC ? (#21557) Un depot sans aucun packfile
# oblige chaque `git cat-file` a parcourir les repertoires d'objets au lieu d'un
# index : mesure ai-01 du 2026-10-20, trois slots a 0 pack et 3,9 Go de vrac
# payaient ~600 s de scan par cycle la ou un slot a 294 packs payait 0,2 s.
# Le predicat est un simple test de repertoire : les objets en vrac vivent sous
# .git/objects/<2 hex>/ et sont absents d'un clone frais, qui a un pack.
wch_loose_object_dirs() {
  local repo="$1" d
  for d in "$repo"/.git/objects/[0-9a-f][0-9a-f]; do
    [ -d "$d" ] && return 0
  done
  return 1
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

# --- Escalade d'un repack qui echoue N fois de suite (#21745, limb B) ------
#
# Mesure ai-01 : `git repack -ad` echoue 4 fois de suite, packs 17 -> 20 -> 23
# -> 24. Avant ce bloc, l'echec etait SEULEMENT journalise : le compte de
# packs croissait sans borne et degradait le lazy fetch (limb A). Le compteur
# vit dans .git/ -- il survit au conteneur, meurt avec le clone, et ne
# voyage donc jamais d'un slot a l'autre.
#
# L'escalade est un RENOMMAGE, jamais une suppression : l'arbre reste
# inspectable sous <repo>.stale-<ts>, et le job suivant reclone. C'est le
# meme compromis que la purge de wch_integrity_pass, avec la preuve de
# preservation en plus.
wch_repack_streak_file() {
  printf '%s/.git/work_cache_repack_failures\n' "$1"
}

wch_repack_streak_read() {
  local f n
  f="$(wch_repack_streak_file "$1")"
  n="$(cat "$f" 2>/dev/null || true)"
  case "$n" in
    ''|*[!0-9]*) printf '0\n' ;;
    *) printf '%s\n' "$n" ;;
  esac
}

wch_repack_streak_write() {  # <repo> <n>
  local f
  f="$(wch_repack_streak_file "$1")"
  printf '%s\n' "$2" > "$f" 2>/dev/null || true
}

wch_quarantine_clone() {  # <repo>
  local repo="$1" parent base dest stamp
  parent="$(dirname "$repo")"
  base="$(basename "$repo")"
  stamp="$(date -u +%Y%m%dT%H%M%SZ)"
  dest="$parent/$base.stale-$stamp"
  if mv -- "$repo" "$dest" 2>/dev/null; then
    echo "work_cache: $repo QUARANTAINE -> $dest (renommage reversible, le job suivant reclonera)"
    return 0
  fi
  echo "work_cache: quarantaine IMPOSSIBLE pour $repo -- cache conserve tel quel" >&2
  return 0
}

# --- Retention des quarantaines `<repo>.stale-<ts>` -----------------------
#
# `wch_quarantine_clone` ci-dessus et `mirror_seed_work` (entrypoint.sh)
# ecartent un clone en le RENOMMANT, jamais en le supprimant : le geste est
# reversible et l'arbre reste inspectable. Rien ne retirait ensuite ces
# repertoires -- et le renommage se repete a chaque echec de repack comme a
# chaque `_work` trouve sans `.git`, si bien que la retention etait INFINIE
# par construction. Mesure rapportee par po-2027 (offerte sur roo-extensions
# #4376, 2026-10-28), non reproduite ici : 17,4 Gio de `.stale-*` sur les
# cinq work-volumes d'ai-01 (5,8 + 2,9 + 1,4 + 2,9 + 4,4).
#
# La borne GARDE les plus recents et retire les autres : ce que l'intention
# « inspectable » vise est le dernier incident, pas l'historique complet. Un
# repertoire n'est retire que si son nom porte EXACTEMENT la forme emise par
# les deux sites (`<base>.stale-<AAAAMMJJ>T<HHMMSS>Z`) -- un `*.stale-*`
# cree a la main, ou un clone vivant, ne matche jamais.
wch_is_quarantine_name() {  # <basename>
  case "$1" in
    *.stale-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]T[0-9][0-9][0-9][0-9][0-9][0-9]Z) return 0 ;;
    *) return 1 ;;
  esac
}

# Profondeur d'empilement d'une quarantaine : `X.stale-A.stale-B` vaut 2.
#
# La borne ci-dessous comptait des NOMS, donc une chaine de dix generations
# valait UNE entree et survivait a `keep=2`. Mesure po-2023 du 2026-10-30 :
# `CoursIA.stale-…stale-…` (10 generations, du 27/10) = **4,8 Gio** a cote
# d'un clone vivant de 2,4 Gio dans le meme volume -- soit un tiers du volume
# pour un historique que l'intention « inspectable » ne vise pas.
wch_quarantine_depth() {  # <basename> -> profondeur (0 si ce n'est pas une quarantaine)
  local n="$1" depth=0
  while case "$n" in
          *.stale-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]T[0-9][0-9][0-9][0-9][0-9][0-9]Z) true ;;
          *) false ;;
        esac; do
    n="${n%.stale-*}"
    depth=$((depth + 1))
  done
  printf '%s\n' "$depth"
}

# Les horodatages sont de largeur fixe et en UTC : sous LC_ALL=C le tri
# lexicographique EST un tri chronologique. `head -n -<keep>` rend tout SAUF
# les <keep> derniers, c'est-a-dire les plus anciens -- ceux qu'on retire.
wch_prune_quarantines() {  # <workdir>
  local workdir="$1" keep="${WCH_STALE_KEEP:-2}" slot path base sz parent prefix rest tail
  local removed=0 reclaimed=0 idx
  local -a list=()
  case "$keep" in ''|*[!0-9]*) keep=2 ;; esac
  # `keep=0` retirerait TOUT, y compris la quarantaine du dernier incident :
  # la borne la plus basse qui preserve l'intention est 1.
  [ "$keep" -ge 1 ] || keep=1
  [ -d "$workdir" ] || return 0
  for slot in "$workdir"/*; do
    [ -d "$slot" ] || continue
    list=()
    # Le filtre de FORME passe AVANT le comptage. L'inverse a ete mesure : un
    # `notes.stale-manuel` present dans le slot decalait la borne et faisait
    # retirer une quarantaine de plus que le plafond demande (test dedie).
    while IFS= read -r path; do
      [ -n "$path" ] || continue
      base="${path##*/}"
      wch_is_quarantine_name "$base" || continue
      # Une chaine empilee vaut `depth` generations, pas une : la ramener a
      # `keep` est un RENOMMAGE (on retire les suffixes les plus ANCIENS, aucune
      # donnee n'est supprimee) -- c'est ce qui rend la borne effective sur un
      # empilement deja present sur disque, sans attendre qu'il se resorbe.
      while [ "$(wch_quarantine_depth "$base")" -gt "$keep" ]; do
        parent="${path%/*}"
        prefix="${base%%.stale-*}"
        rest="${base#*.stale-}"
        tail="${rest#*.stale-}"
        # Pas de seconde generation a retirer, ou le nom cible existe deja :
        # on laisse la chaine telle quelle plutot que de la fusionner.
        [ "$tail" != "$rest" ] || break
        newname="$prefix.stale-$tail"
        [ -e "$parent/$newname" ] && break
        if mv -- "$path" "$parent/$newname" 2>/dev/null; then
          echo "work_cache: quarantaine $base ramenee a $newname (generations les plus anciennes ecartees, contenu intact)"
          path="$parent/$newname"
          base="$newname"
        else
          break
        fi
      done
      list+=("$path")
    done < <(find "$slot" -mindepth 1 -maxdepth 1 -type d -name '*.stale-*' -print 2>/dev/null \
               | LC_ALL=C sort)
    [ "${#list[@]}" -gt "$keep" ] || continue
    for (( idx = 0; idx < ${#list[@]} - keep; idx++ )); do
      path="${list[idx]}"
      base="${path##*/}"
      sz="$(du -sk -- "$path" 2>/dev/null | awk '{print $1}')"
      case "$sz" in ''|*[!0-9]*) sz=0 ;; esac
      if rm -rf -- "$path" 2>/dev/null; then
        removed=$((removed + 1))
        reclaimed=$((reclaimed + sz))
        echo "work_cache: quarantaine $base retiree (${sz} Kio)"
      else
        echo "work_cache: quarantaine $base NON retirable -- conservee" >&2
      fi
    done
  done
  # Un passage qui ne retire rien ne dit rien : le journal d'un slot sain
  # reste lisible, et l'absence de ligne n'est pas un echec silencieux -- le
  # retrait se prouve par l'arbre, jamais par le journal seul.
  if [ "$removed" -gt 0 ]; then
    echo "work_cache: retention des quarantaines -- $removed retiree(s), $reclaimed Kio rendus"
  fi
  return 0
}

# Le depot emprunte-t-il ses objets a un magasin partage (#18225) ? Un slot
# seme par `git clone --shared` du miroir porte un fichier alternates non vide,
# et c'est LUI qui distingue « ce slot ne tient que ses propres objets » de
# « une partie de son contenu vit ailleurs ». Le predicat est le fichier, pas un
# compte : un alternates vide ne fait emprunter aucun objet (`-s` est faux, et
# le repack retombe alors sur le comportement d'avant).
wch_has_alternates() {
  [ -s "$1/.git/objects/info/alternates" ]
}

# Drapeaux de repack. `-a` SEUL parcourt tous les objets joignables, ALTERNATES
# COMPRIS, et les COPIE dans le pack local : sur un slot seme, un `repack -ad`
# ramene les ~5,5 Gio du miroir dans le volume du slot, et le miroir devient un
# cout fixe au lieu de supprimer le telechargement par slot. `-l` (--local)
# borne pack-objects aux objets du depot courant ; les objets empruntes restent
# la ou ils sont. Les DEUX sites de repack passent par ici, pour qu'une seule
# decision serve les deux -- un `-ad` oublie sur l'un remettrait la copie, et
# seulement sur le chemin le moins frequent, donc le moins surveille.
wch_repack_flags() {
  if wch_has_alternates "$1"; then printf '%s\n' '-adl'; else printf '%s\n' '-ad'; fi
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
  local repo="$1" threshold="$2" before after streak max flags
  max="${WCH_REPACK_FAIL_MAX:-3}"
  case "$max" in ''|*[!0-9]*) max=3 ;; esac
  [ "$threshold" -gt 0 ] || return 0
  [ -d "$repo/.git" ] || return 0
  flags="$(wch_repack_flags "$repo")"
  before="$(wch_pack_count "$repo")"
  if [ "$before" -le "$threshold" ]; then
    # Cas NORMAL d'un cache frais : aucun pack, aucun objet en vrac non plus.
    # Cas ANORMAL (#21557) : aucun pack ET des objets en vrac -- le clone a
    # perdu ses packs (ou n'en a jamais recu) sans etre un clone frais. Le
    # compte de packs est alors sous le seuil, donc la borne ci-dessus ne se
    # declencherait jamais, et `gc.auto=0` fait que rien d'autre ne consolide :
    # l'etat est stable et auto-entretenu, chaque `git cat-file` payant le
    # parcours des repertoires d'objets (mesure du 2026-10-20 : ~600 s de scan
    # par cycle contre 0,2 s sur un depot a 294 packs).
    if [ "$before" -ne 0 ] || ! wch_loose_object_dirs "$repo"; then
      return 0
    fi
    if ! wch_git -C "$repo" repack "$flags" >/dev/null 2>&1; then
      streak=$(( $(wch_repack_streak_read "$repo") + 1 ))
      wch_repack_streak_write "$repo" "$streak"
      echo "work_cache: repack $flags ECHEC dans $repo (0 pack, objets en vrac, echec consecutif $streak/$max)" >&2
      if [ "$streak" -ge "$max" ]; then wch_quarantine_clone "$repo"; fi
      return 0
    fi
    wch_repack_streak_write "$repo" 0
    after="$(wch_pack_count "$repo")"
    echo "work_cache: $repo repack $flags 0 -> $after packs (0 pack mais objets en vrac, #21557)"
    return 0
  fi
  # Stderr du repack : avant #20697, il partait dans `>/dev/null 2>&1` et
  # les 223 'repack ECHEC' du journal du slot 1 (myia-ai-01-wsl) restaient
  # sans cause nommee. On capture stderr vers un tmpfile et on le CAT-a-la-ligne
  # sur le journal du slot. Le rc du repack reste 0 en sortie -- un garde de
  # sante ne doit jamais etre la raison pour laquelle un slot meurt.
  _wch_rep_err="$(mktemp -t wch-rep.XXXXXX 2>/dev/null)" || _wch_rep_err=""
  if ! wch_git -C "$repo" repack "$flags" >/dev/null 2>"${_wch_rep_err:-/dev/null}"; then
    streak=$(( $(wch_repack_streak_read "$repo") + 1 ))
    wch_repack_streak_write "$repo" "$streak"
    echo "work_cache: repack $flags ECHEC dans $repo ($before packs, echec consecutif $streak/$max)" >&2
    if [ -n "$_wch_rep_err" ] && [ -s "$_wch_rep_err" ]; then
      while IFS= read -r line; do
        echo "work_cache: repack stderr: $line" >&2
      done < "$_wch_rep_err"
    fi
    [ -n "$_wch_rep_err" ] && rm -f "$_wch_rep_err"
    if [ "$streak" -ge "$max" ]; then wch_quarantine_clone "$repo"; fi
    return 0
  fi
  [ -n "$_wch_rep_err" ] && rm -f "$_wch_rep_err"
  wch_repack_streak_write "$repo" 0
  after="$(wch_pack_count "$repo")"
  echo "work_cache: $repo repack $flags $before -> $after packs (seuil $threshold)"
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
    # Une quarantaine EST un clone complet : elle porte donc un `.git`, et
    # cette boucle la reprenait comme un depot vivant. Consequences mesurees
    # sur po-2023 le 2026-10-30 : la maintenance la repackait (le repack
    # echoue et AJOUTE des packs -- 2,4 -> 4,8 Gio), puis l'echec la
    # re-quarantinait SOUS ELLE-MEME, d'ou `X.stale-A.stale-B…stale-J` : une
    # generation par demarrage, dix au total. L'intention « inspectable » ne
    # demande aucune maintenance : on passe, et l'empilement cesse a la source.
    wch_is_quarantine_name "${repo##*/}" && continue
    wch_integrity_pass "$repo"
    wch_maintenance_pass "$repo" "$threshold"
  done
  # Les quarantaines vivent a COTE des clones (`<workdir>/<slug>/<base>.stale-<ts>`),
  # sous un nom qui porte un `.git` -- la boucle ci-dessus les exclut
  # desormais explicitement, et c'est la retention ci-dessous qui les borne.
  wch_prune_quarantines "$workdir"
  return 0
}
