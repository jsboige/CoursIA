#!/usr/bin/env bash
# Superviseur de conteneurs runner ephemeres (mission #13378, finalisation
# ai-01 2026-09-01 sur demande user « debrayer le CI sur po-2024 »).
#
# POURQUOI CE SCRIPT EXISTE
# -------------------------
# Le census #13378 avait nomme le vrai facteur limitant du volet self-hosted :
# le runner est --ephemeral, donc il traite AU PLUS UN JOB puis se desenregistre.
# Cote Windows, chaque job supplementaire exigeait un re-register porte par une
# tache planifiee -- c'est ce qui rendait tout elargissement contre-productif.
#
# Le conteneur dissout ce verrou : la re-inscription n'est plus une tache a
# orchestrer, c'est un `docker run` de plus. Ce script est la boucle qui en
# tire la consequence -- un slot = une boucle, N slots = N jobs concurrents.
#
# CONTRAINTE QUI PRIME SUR TOUT : l'hote est AUSSI une workstation GPU et
# interactive. Les caps par conteneur et le N par defaut sont volontairement
# bas. Si l'empreinte gene la machine, baisser N ou arreter -- l'hote prime,
# et cette clause survit a toute decision d'elargissement (docs/ci/self-hosted-runners.md).
#
# USAGE
#   ./supervise.sh start [N] [--force]
#                                  # N slots (defaut 2) ; --force leve
#                                  # un sentinel STOP_FILE prealable
#   ./supervise.sh waiters [N]   # N slots d'attente PR-gate (label coursia-waiter, defaut 24)
#   ./supervise.sh lean [N]      # N slots Lean specialises (label coursia-lean, image
#                                  # dediee elan+toolchain, .lake chaud par slot, defaut 2)
#   ./supervise.sh stop          # arret gracieux : pas de nouveau conteneur
#   ./supervise.sh status        # familles actives + etat des trois bornes
#
# BORNES (#15091) -- toutes declarees par ENVIRONNEMENT.
#
# Les bornes de RESSOURCES sont vides ou a 0 par defaut : une machine qui tire
# cette version sans rien declarer ne se voit imposer aucun plafond qu'elle
# n'a pas demande, et garde exactement son comportement anterieur. C'est le
# wrapper de chaque machine qui arme ce qu'elle veut (voir persist/README.md).
#
# Les deux valeurs qui ne sont PAS inertes -- backoff et rotation -- ne sont
# pas des plafonds : elles ne refusent rien et ne ralentissent aucun travail
# qui aboutit. Elles ne mordent que sur ce qui echoue en boucle ou grossit
# sans borne, c'est-a-dire exactement les deux comportements qui ont mis la
# machine par terre. Les laisser inertes aurait demande a chaque machine de
# reclamer explicitement de ne pas marteler l'API et de ne pas remplir son
# disque.
#
#   COURSIA_RUNNER_CGROUP_PARENT        slice systemd attendue (ex.
#                                       coursia-ci.slice). Le script la
#                                       VERIFIE, il ne la re-impose pas.
#   COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET  1 = REFUSER de demarrer si elle
#                                       manque ou n'a pas d'io.max. 0 =
#                                       avertir et continuer.
#   COURSIA_RUNNER_DEVICE_WRITE_BPS     plafond d'ecriture PAR conteneur, en
#   COURSIA_RUNNER_DEVICE_READ_BPS      octets/s (ex. 41943040 = 40 Mio/s).
#   COURSIA_RUNNER_BLKIO_DEVICE         device porteur ; auto-detecte si vide.
#   COURSIA_RUNNER_CPU_BUDGET           somme MAX de vCPU, toutes familles
#                                       confondues. 0 = pas de garde.
#   COURSIA_RUNNER_LOG_MAX_BYTES        rotation des journaux de slot.
#                                       NON inerte : 32 Mio. 0 = desactive.
#   COURSIA_RUNNER_BACKOFF_MIN_SEC      backoff exponentiel des boucles de
#   COURSIA_RUNNER_BACKOFF_MAX_SEC      slot. NON inertes : 5 s -> 300 s.
#   COURSIA_RUNNER_BACKOFF_JITTER_PCT   dispersion du backoff. NON inerte :
#                                       25 %. 0 = rafale synchronisee.
#
# Le detail de chaque borne -- ce qu'elle couvre, ce qu'elle ne peut PAS
# couvrir, et la mesure qui l'etablit -- est dans le bloc BORNES plus bas et
# dans persist/README.md.
#
# PREREQUIS : docker, gh authentifie avec droit admin sur le depot (le fetch
# du registration token l'exige). Le token n'est JAMAIS passe en argv --
# uniquement par -e, comme entrypoint.sh et manage_self_hosted_runner.py.
set -uo pipefail

REPO="${COURSIA_RUNNER_REPO:-jsboige/CoursIA}"
IMAGE="${COURSIA_RUNNER_IMAGE:-coursia-linux-runner:2.337.0}"
LABELS="${COURSIA_RUNNER_LABELS:-self-hosted,coursia-ephemeral,coursia-linux}"
# #15152 : le prefixe de nom derive de la MACHINE, pas d'un hote code en dur.
# L'ancien defaut `myia-po-2024-*` faisait enregistrer les runners de toute
# autre machine sous l'identite de po-2024 cote GitHub -- inventaire menteur
# (un runner d'ai-01 lu comme fantome de po-2024) + collision de nom si les
# deux machines montent des pools simultanement. La surcharge ENV explicite
# reste prioritaire ; hostname lowercasse pour les hotes a nom Windowsien.
MACHINE_ID="${COURSIA_RUNNER_MACHINE_ID:-$(hostname | tr 'A-Z' 'a-z')}"
NAME_PREFIX="${COURSIA_RUNNER_NAME_PREFIX:-${MACHINE_ID}-linux-docker}"
STATE_DIR="${COURSIA_RUNNER_STATE_DIR:-$HOME/.coursia-runner}"
STOP_FILE="$STATE_DIR/stop"

# Caps par conteneur. Volontairement conservateurs : l'hote prime sur la CI.
CPUS="${COURSIA_RUNNER_CPUS:-3}"
MEMORY="${COURSIA_RUNNER_MEMORY:-4g}"
PIDS="${COURSIA_RUNNER_PIDS:-384}"

# Toolcache persistant : sans lui, chaque conteneur ephemere (un par job)
# re-telechargerait interpretes et outils via les actions setup-*. Le volume
# nomme survit aux conteneurs ; RUNNER_TOOL_CACHE dit aux actions ou chercher.
# Sa propriete runner:runner vient du point de montage du Dockerfile.
TOOLCACHE_VOLUME="${COURSIA_RUNNER_TOOLCACHE_VOLUME:-coursia-runner-toolcache}"
TOOLCACHE_MOUNT="${COURSIA_RUNNER_TOOLCACHE_MOUNT:-/opt/hostedtoolcache}"

# Cache de depot persistant, PAR SLOT (#14285) : --rm detruit /home/runner/_work
# avec le conteneur, donc actions/checkout re-clonait le depot ENTIER (3,54 GiB,
# 228 683 objets) a chaque job -- mesure #14285 : checkout 80-148 s contre
# 40-51 s sur ubuntu-latest, ~97 % du temps du job. Le volume nomme survit au
# conteneur ; checkout y trouve un clone existant et fait un git fetch
# incremental (son clean par defaut nettoie l'arbre entre jobs). Un volume PAR
# SLOT, jamais partage : deux jobs concurrents sur le meme _work se battraient
# sur le meme .git. Cout disque ~4 GiB par slot.
#
# GARDE LIEE (ne jamais dissocier) : la persistance de _work est acceptable
# UNIQUEMENT parce qu'aucun code de fork n'atteint ces runners (garde fork
# universelle + aucun trigger pull_request, cf linux-self-hosted-tests.yml ;
# ~95 forks etudiants). Un job voit les restes du precedent. Si cette garde
# saute un jour, ce volume devient un vecteur -- retirer la persistance AVANT
# d'ouvrir le runner aux forks.
WORK_VOLUME_PREFIX="${COURSIA_RUNNER_WORK_VOLUME_PREFIX:-coursia-runner-work}"
WORK_MOUNT="${COURSIA_RUNNER_WORK_MOUNT:-/home/runner/_work}"

# Pool d'attente PR-gate (#13363, 2026-09-02) : le PR gate agrege jusqu'a
# 35 min en polling, occupant un slot d'execution pendant que les jobs reels
# attendent derriere. Le label DEDIE `coursia-waiter` (JAMAIS coursia-linux)
# porte ~24 slots sur-provisionnes -- un slot qui attend ne coute rien. Pas
# de volume toolcache/_work : aucun job d'execution ne doit leur atterrir,
# le gate bascule dessus uniquement (item B, ai-01).
WAITER_LABELS="${COURSIA_RUNNER_WAITER_LABELS:-self-hosted,coursia-waiter}"
WAITER_NAME_PREFIX="${COURSIA_RUNNER_WAITER_NAME_PREFIX:-${MACHINE_ID}-linux-waiter}"
WAITER_CPUS="${COURSIA_RUNNER_WAITER_CPUS:-1}"
WAITER_MEMORY="${COURSIA_RUNNER_WAITER_MEMORY:-1g}"
WAITER_PIDS="${COURSIA_RUNNER_WAITER_PIDS:-128}"
# Toolcache partage sur les waiters (#15091). La premisse d'origine etait
# « un slot qui attend ne coute rien », donc aucun volume. Elle tombe sur le
# seul workflow route ici : le job `PR gate` commence par un checkout PUIS un
# `setup-python@v5`, qui sans RUNNER_TOOL_CACHE re-telecharge et reinstalle
# CPython a CHAQUE job -- ~300 jobs/jour sur ce pool. Le toolcache est le
# MEME volume nomme que celui des slots d'execution : partage, en lecture
# quasi exclusive, il ne croit pas avec le nombre de jobs. Ce n'est PAS le
# volume _work, dont la persistance est le vecteur ferme par #14385 -- les
# waiters n'en ont toujours aucun, et cette distinction est la garde.
WAITER_TOOLCACHE="${COURSIA_RUNNER_WAITER_TOOLCACHE:-1}"

# Pool Lean specialise (#14337 tranche 1) : le cout d'un job Lean n'est pas le
# toolchain mais MATHLIB. Image dediee (Dockerfile.lean : elan + toolchain
# stable pinnnes), labels dedies (JAMAIS coursia-linux -- le label distinct
# est la garantie de routage), caps hautes (lake build est CPU/RAM lourd).
# Le .lake chaud vit dans le volume _work PAR SLOT au prefixe dedie
# coursia-runner-work-lean-{N} (pattern #14285) : .lake/packages et .lake/build
# survivent aux conteneurs, lake build devient incremental.
LEAN_IMAGE="${COURSIA_LEAN_RUNNER_IMAGE:-coursia-lean-runner:2.337.0}"
LEAN_LABELS="${COURSIA_LEAN_RUNNER_LABELS:-self-hosted,coursia-ephemeral,coursia-lean}"
LEAN_NAME_PREFIX="${COURSIA_LEAN_RUNNER_NAME_PREFIX:-${MACHINE_ID}-lean-docker}"
LEAN_WORK_VOLUME_PREFIX="${COURSIA_LEAN_RUNNER_WORK_VOLUME_PREFIX:-coursia-runner-work-lean}"
# 2 slots * 6 cpus = 12 des 16 coeurs au pire ; l'hote workstation prime
# (cf CONTRAINTE en tete de fichier) -- baisser N ou les caps si la machine
# gene pendant un lake build.
LEAN_CPUS="${COURSIA_LEAN_RUNNER_CPUS:-6}"
LEAN_MEMORY="${COURSIA_LEAN_RUNNER_MEMORY:-8g}"
LEAN_PIDS="${COURSIA_LEAN_RUNNER_PIDS:-512}"
# Swap au-dela de la RAM du slot : les modules Hashlife de conway_lean
# pointent a >16 Go au build a froid (exit 137 mesure sous --memory 8g,
# 8716/8727 modules OK puis Walls.{SE,SW,NE} tues ; les runners hosted
# s'en sortent par 32G de fallocate swap, lean-axiom.yml L~100). Un job
# conteneurise n'a pas sudo pour creer son swap, donc le pool le porte :
# memory-swap 24g = 8g RAM + 16g swap. Le swap n'est PAS de la RAM
# reservee -- l'hote ne paie que si le pic survient.
LEAN_MEMORY_SWAP="${COURSIA_LEAN_RUNNER_MEMORY_SWAP:-24g}"

# ---------------------------------------------------------------------------
# BORNES D'I/O ET BUDGET INTER-FAMILLES (#15091 pieces 2 et 4)
# ---------------------------------------------------------------------------
# Le mandat : « optimiser au mieux tout le traffic et les acces engendres par
# le superviseur et ses workers avec de vrais gardes surtout en cas de panne ».
# Les trois mots qui comptent sont VRAIS et EN CAS DE PANNE : un cap qui ne se
# verifie pas et une boucle qui retente a cadence fixe ne sont pas des gardes,
# ce sont des intentions.
#
# Trois bornes distinctes, qui ne se remplacent pas :
#
#   1. PAR CONTENEUR -- COURSIA_RUNNER_DEVICE_WRITE_BPS. Empeche UN slot de
#      monopoliser le disque. Mesure ai-01 2026-09-07 : dd 256 Mio oflag=direct
#      rend 7,4 GB/s sans cap et 21,2 MB/s sous --device-write-bps 20 Mio/s --
#      facteur 350, a 1 % de la valeur demandee. Le cap est REEL.
#   2. AGREGE -- la slice systemd coursia-ci.slice, appliquee par defaut du
#      daemon (/etc/docker/daemon.json "cgroup-parent"). C'est la seule borne
#      qui somme les familles ; voir persist/coursia-ci.slice.
#   3. CPU INTER-FAMILLES -- assert_cpu_budget() ci-dessous, qui ferme le trou
#      que cmd_lean documente depuis #14337 (« la somme des caps CPU des
#      familles actives n'est gardee par RIEN »).
#
# La borne 2 est daemon-wide et donc independante de l'appelant ; ce script
# n'a pas a la re-imposer, il a a VERIFIER qu'elle est en vigueur. La
# difference n'est pas cosmetique : re-passer --cgroup-parent sur une machine
# ou la slice n'existe pas cree un cgroup vide qui a l'air d'un garde et n'en
# est pas -- exactement la classe de defaut ou un outil manquant rend un garde
# vert.
#
# Vide = borne desactivee, explicitement. Aucun defaut n'est impose aux
# machines qui n'ont pas deploye la slice (po-2024) : elles gardent le
# comportement anterieur et recoivent un avertissement nomme.
CGROUP_PARENT="${COURSIA_RUNNER_CGROUP_PARENT:-}"
# 1 = refuser de demarrer si CGROUP_PARENT est declare mais introuvable /
# sans io.max. La machine qui a deploye la slice veut un echec LISIBLE
# (unite en `failed`, cf StartLimitBurst) plutot qu'un pool non borne qui
# tourne comme si de rien n'etait -- c'est ce silence-la qui a gele ai-01.
REQUIRE_CGROUP_BUDGET="${COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET:-0}"
# Plafond d'ecriture PAR CONTENEUR, en octets/s. Vide = pas de cap.
DEVICE_WRITE_BPS="${COURSIA_RUNNER_DEVICE_WRITE_BPS:-}"
DEVICE_READ_BPS="${COURSIA_RUNNER_DEVICE_READ_BPS:-}"
# Device porteur de /var/lib/docker. Auto-detecte si vide (df sur le
# DockerRootDir REEL du daemon vise, pas un chemin suppose : ai-01 a deux
# daemons et le socket epingle decide lequel repond).
BLKIO_DEVICE="${COURSIA_RUNNER_BLKIO_DEVICE:-}"
# Budget CPU total de la CI, toutes familles confondues. 0 = pas de garde.
# 8 sur les 16 coeurs d'ai-01 : la workstation garde la moitie de sa machine
# quoi que fasse la CI (clause « l'hote prime » en tete de ce fichier).
CPU_BUDGET="${COURSIA_RUNNER_CPU_BUDGET:-0}"
# Rotation des journaux de slot. Sans elle, $STATE_DIR/<nom>.log croit sans
# borne : mesure ai-01 2026-09-07, /var/lib/coursia-runner = 14 Mo pour un
# pool eteint la majeure partie de la journee. 32 Mio par fichier, une
# generation conservee -- assez pour diagnostiquer le dernier incident, borne
# pour ne jamais devenir la fuite disque qu'on pretend surveiller.
LOG_MAX_BYTES="${COURSIA_RUNNER_LOG_MAX_BYTES:-33554432}"

# #15095 Anti-emballement borne. Incident 07/09 (ai-01, 2 gels machine en
# 90 min) : docker.service arrete + Restart=always => chaque slot recreait
# un runner et rejouait son bootstrap 4 a 8 fois par minute (journal :
# « conteneur termine (rc=0) » en boucle), ecriture ext4.vhdx 94-96 Mo/s,
# load 69. L'ancien garde `[ rc -ne 0 ] && sleep 15 || sleep 2` etait plat
# et traitait differemment rc=0 et rc!=0 alors que le martelement observe
# etait precisement la branche rc=0. Le nouveau garde ne regarde PAS le
# code de retour mais la DUREE DE VIE du conteneur : un cycle plus court
# que HEALTHY_CYCLE_SECS est anormal (le bootstrap seul depasse), et la
# respiration suit un backoff exponentiel plafonne, remis a zero uniquement
# apres un cycle ayant vecu assez longtemps.
HEALTHY_CYCLE_SECS="${COURSIA_RUNNER_HEALTHY_CYCLE_SECS:-60}"
BACKOFF_BASE="${COURSIA_RUNNER_BACKOFF_BASE:-15}"
BACKOFF_CAP="${COURSIA_RUNNER_BACKOFF_CAP:-900}"

# Backoff exponentiel des boucles de slot (#15091 : « de vrais gardes surtout
# en cas de panne »).
#
# Le defaut ferme ici : la boucle retentait a CADENCE FIXE -- `sleep 15` apres
# un echec, `sleep 60` apres un token refuse. Sous panne (image absente, token
# expire, daemon docker mort), 12 slots produisaient donc ~48 appels
# `registration-token` par minute, indefiniment, pendant que rien ne pouvait
# aboutir. Une panne se transformait en charge soutenue sur l'API GitHub et
# sur le daemon -- l'inverse d'un garde.
#
# Le backoff double a chaque echec consecutif jusqu'a un plafond, et se
# REINITIALISE des qu'un conteneur se termine proprement (rc=0) : une panne
# franche se calme en quelques minutes, un job normal ne paie rien.
BACKOFF_MIN_SEC="${COURSIA_RUNNER_BACKOFF_MIN_SEC:-5}"
BACKOFF_MAX_SEC="${COURSIA_RUNNER_BACKOFF_MAX_SEC:-300}"
# Jitter, en pourcentage du delai. NON cosmetique : les N slots sont lances
# dans la meme seconde, echouent dans la meme seconde et repartiraient dans la
# meme seconde -- le backoff seul deplace la rafale sans la disperser. Le
# jitter la disperse.
BACKOFF_JITTER_PCT="${COURSIA_RUNNER_BACKOFF_JITTER_PCT:-25}"

# Seuil de packs du cache _work persistant (#15105). Au-dela, l'entrypoint du
# conteneur repack le clone (gc.auto=0 pose par actions/checkout : rien
# d'autre ne consolide jamais -- slot 1 : 264 packs, compte croissant a
# chaque job). NON inerte au meme titre que LOG_MAX_BYTES : son absence est
# une croissance de disque sans borne, pas un plafond qu'une machine n'a pas
# demande. 0 = desactive. Le knob descend au conteneur par -e ; la passe
# integrite (refs cassees) est, elle, inconditionnelle -- cf
# work_cache_health.sh et le bloc entrypoint #15105.
CACHE_PACK_THRESHOLD="${COURSIA_RUNNER_CACHE_PACK_THRESHOLD:-16}"

mkdir -p "$STATE_DIR"

# Git Bash (MSYS) sous Windows reecrit les arguments de forme /posix/path des
# appels a docker.exe : -e RUNNER_TOOL_CACHE=/opt/hostedtoolcache devenait
# "C:/Program Files/Git/opt/hostedtoolcache" dans le conteneur (mesure :
# docker inspect Config.Env apres le premier demarrage). Ces deux variables
# sont inertes sous Linux et figent la conversion cote Windows.
export MSYS_NO_PATHCONV=1
export MSYS2_ARG_CONV_EXCL='*'

die() { echo "ERREUR: $*" >&2; exit 1; }

# #15095 Garde de disponibilite du demon. Avant cette garde, un daemon
# docker arrete laissait chaque cmd_* echouer sur image inspect / volume
# create puis se faire relancer par Restart=always -- le superviseur ne
# devait jamais marteler un daemon absent (cf incident en tete du bloc
# HEALTHY_CYCLE_SECS). `docker info` sur le DOCKER_HOST epingle (le wrapper
# persist/ l'exporte) est le probe le plus proche de ce que fera docker run.
assert_docker_daemon() {
  if ! docker info >/dev/null 2>&1; then
    die "demon Docker indisponible sur DOCKER_HOST='${DOCKER_HOST:-default}' (docker info echoue, #15095) -- ne pas marteler : reparer le daemon, puis relancer. Le service systemd est BindsTo=docker.service (fail-closed)."
  fi
}

# Review #15166 (v2) : les 3 bornes du backoff sont env-overridable ; une
# config operateur invalide ne doit JAMAIS pouvoir atteindre les boucles --
# BASE=0 produisait un backoff nul sans fin, et des valeurs proches de la
# borne signee 64 bits faisaient deborder le doublement vers le negatif
# puis 0 (boucle infinie dans cycle_backoff). Fail-closed AVANT tout cycle :
# decimal strictement positif, domaine arithmetique garanti (18 chiffres
# max < 2^60 : tout produit garde du calcul iteratif reste < 2^61, loin de
# la borne signee), et BASE <= CAP (le plafond doit dominer la base).
_validate_backoff_value() {
  # $1 = nom de la variable d'environnement, $2 = valeur
  case "$2" in
    ''|*[!0-9]*)
      die "COURSIA_RUNNER_* : $1='$2' n'est pas un entier decimal (#15166)."
      ;;
  esac
  [ "${#2}" -le 18 ] \
    || die "COURSIA_RUNNER_* : $1='$2' depasse le domaine arithmetique (18 chiffres max, #15166)."
  [ "$2" -ge 1 ] \
    || die "COURSIA_RUNNER_* : $1='$2' doit etre strictement positif (#15166)."
}

validate_backoff_env() {
  _validate_backoff_value HEALTHY_CYCLE_SECS "$HEALTHY_CYCLE_SECS"
  _validate_backoff_value BACKOFF_BASE "$BACKOFF_BASE"
  _validate_backoff_value BACKOFF_CAP "$BACKOFF_CAP"
  [ "$BACKOFF_BASE" -le "$BACKOFF_CAP" ] \
    || die "COURSIA_RUNNER_* : BACKOFF_BASE=$BACKOFF_BASE > BACKOFF_CAP=$BACKOFF_CAP -- le plafond doit dominer la base (#15166)."
}

# #15095 Backoff post-cycle partage par slot_loop et waiter_loop. La duree
# de vie (pas le rc) classe le cycle : court = anormal, exponentiel plafonne
# (15,30,60,...,900 s) ; sain = respiration courte et remise a zero. Le rc
# n'est plus qu'informatif -- l'incident 07/09 etait des rc=0 en rafale.
# Review #15166 (3 durecissements) :
# (1) l'exponentiel SATURE AVANT l'exponentiation : 15*2^60 deborde
#     l'arithmetique signee 64 bits de bash -- cycle 61 negatif, cycle 65+
#     nul, et le plafond n'atteint jamais ces valeurs (sleep 0 = retour du
#     martellement ; StartLimitBurst ne couvre pas cette boucle interne) ;
# (2) un cycle court qui a REELLEMENT execute un job (log du cycle portant
#     l'execution) est du travail utile, pas une boucle vide -- il ne nourrit
#     pas l'exponentiel ;
# (3) un cycle long avec rc!=0 n'est PAS automatiquement sain -- compteur
#     de courts conserve, respiration intermediaire, pas de "sainement".
cycle_backoff() {
  local tag="$1" lifetime="$2" rc="$3" work_log="${4:-}" log_off="${5:-0}"
  local worked=0
  if [ -n "$work_log" ] && [ -f "$work_log" ]; then
    # Le log du cycle est CUMULATIF (rotate_log ne borne que par taille) :
    # le signal de travail ne lit que la portion ecrite PAR CE cycle, a
    # partir de l'offset capture avant le docker run.
    # #15166 : `grep -q` sort des la premiere ligne et FERME le pipe pendant
    # que tail ecrit encore -> SIGPIPE 141 -> sous `set -uo pipefail` la
    # pipeline est non nulle et un cycle AYANT travaille est classe en boucle
    # vide (backoff au lieu de sleep 2). Un gros log de cycle (>> tampon ~64
    # Ko, cf test 28) revele la faute. `grep ... >/dev/null` lit tout jusqu'a
    # EOF : tail se termine proprement, rc=0 sur match.
    if tail -c "+$(( log_off + 1 ))" "$work_log" 2>/dev/null | grep "Running job" >/dev/null; then
      worked=1
    fi
  fi
  if [ "$lifetime" -lt "$HEALTHY_CYCLE_SECS" ]; then
    if [ "$worked" -eq 1 ]; then
      SHORT_CYCLES=0
      echo "$tag cycle court AVEC travail (rc=$rc, ${lifetime}s) -- travail reel, pas une boucle vide : pas de backoff (#15166)" >&2
      sleep 2
      return
    fi
    SHORT_CYCLES=$(( SHORT_CYCLES + 1 ))
    # Review #15166 (v2) : le doublement ne doit JAMAIS pouvoir depasser la
    # borne signee 64 bits, quelle que soit la config valide. d est calcule
    # ITERATIVEMENT : on ne double que si d <= CAP/2 (chaque produit reste
    # <= 2*floor(CAP/2) <= CAP, dans le domaine) ; si les exp doublons ne
    # tiennent pas tous dans la garde, la vraie valeur depasse CAP ->
    # plafond. L'ancien probe `while p<=CAP && p<=2^62; p=p*2` debordait sur
    # BASE=2^62/CAP maximale (p=2^63 -> -2^63 -> 0 -> boucle infinie) et
    # sur BASE=0 (0 sans fin) ; ces configs sont desormais rejetees au
    # demarrage (validate_backoff_env), et le calcul lui-meme est garde.
    local exp=$(( SHORT_CYCLES - 1 ))
    local d="$BACKOFF_BASE" i=0
    while [ "$i" -lt "$exp" ] && [ "$d" -le "$(( BACKOFF_CAP / 2 ))" ]; do
      d=$(( d * 2 ))
      i=$(( i + 1 ))
    done
    [ "$i" -lt "$exp" ] && d="$BACKOFF_CAP"
    echo "$tag cycle court (rc=$rc, ${lifetime}s, consecutifs=$SHORT_CYCLES) -- backoff ${d}s (#15095)" >&2
    sleep "$d"
  elif [ "$rc" -eq 0 ]; then
    SHORT_CYCLES=0
    echo "$tag conteneur termine sainement (rc=$rc, ${lifetime}s)"
    sleep 2
  else
    echo "$tag cycle long mais rc=$rc (${lifetime}s) -- non qualifie sain, compteur de courts conserve a $SHORT_CYCLES (#15166)" >&2
    sleep "$BACKOFF_MIN_SEC"
  fi
}
SHORT_CYCLES=0

# Contexte de build du runner : le dossier qui porte ce script porte aussi
# Dockerfile et entrypoint.sh -- le garde de fraicheur compare le sibling du
# checkout d'ou l'operateur lance le superviseur a ce que porte l'image.
RUNNER_CTX="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# #14801 Garde de fraicheur d'image. Un correctif d'entrypoint.sh merge mais
# dont l'image n'a pas ete reconstruite est INERTE : #14385 (purge sparse au
# demarrage du slot) est reste inerte 3 jours sur la moitie du parc (image du
# daemon docker-ce WSL construite 5 h AVANT le merge, jamais rebatie), et ce
# silence a produit les rouges fantomes du sparse-checkout empoisonne. Le
# demarrage d'un pool est le seul point qui s'execute inconditionnellement
# (un job annule ne joue aucun step post) : on y compare le sha256 de CHAQUE
# script embarque de CE checkout (entrypoint.sh, et depuis #15105
# work_cache_health.sh qu'il source) a celui porte par l'image. La lecture
# cote image passe par `docker run --entrypoint sha256sum` -- le Dockerfile
# place les scripts sous /opt/runner/ et MSYS_NO_PATHCONV (exporte plus haut)
# protege l'argument POSIX sous Git Bash.
assert_image_fresh() {
  local image="$1" build_cmd="$2"
  local f repo_sha img_sha
  for f in entrypoint.sh work_cache_health.sh; do
    repo_sha="$(sha256sum "$RUNNER_CTX/$f" 2>/dev/null | awk '{print $1}')"
    [ -n "$repo_sha" ] || die "$f introuvable a cote de supervise.sh ($RUNNER_CTX) -- lancer depuis un checkout du depot"
    img_sha="$(docker run --rm --entrypoint sha256sum "$image" /opt/runner/$f 2>/dev/null | awk '{print $1}')"
    [ -n "$img_sha" ] || die "lecture de /opt/runner/$f dans $image impossible (docker run --entrypoint sha256sum)"
    [ "$repo_sha" = "$img_sha" ] || die "image $image PERIMEE : $f du checkout ($repo_sha) != version embarquee ($img_sha).
Un correctif merge mais non deploye est indiscernable d'un correctif absent (#14801, #14385). Reconstruire :
    $build_cmd"
  done
}

# --- Bornes d'I/O : resolution du device et des drapeaux docker -------------

# Device bloc qui porte le repertoire de donnees du daemon VISE. La resolution
# passe par `docker info` et non par un chemin suppose : ai-01 porte deux
# daemons (docker-ce sur /var/run/docker-ce.sock, Docker Desktop sur le socket
# par defaut) et c'est DOCKER_HOST qui decide lequel repond. Les deux
# annoncent le meme DockerRootDir -- s'y fier sans passer par le socket epingle
# est un leurre verifie firsthand.
resolve_blkio_device() {
  [ -n "$BLKIO_DEVICE" ] && { printf '%s\n' "$BLKIO_DEVICE"; return 0; }
  local root dev
  root="$(docker info --format '{{.DockerRootDir}}' 2>/dev/null)"
  [ -n "$root" ] || return 1
  # df --output n'existe pas partout ; la forme POSIX (colonne 1 de la 2e
  # ligne) marche sur coreutils comme sur busybox.
  dev="$(df -P "$root" 2>/dev/null | awk 'NR==2 {print $1}')"
  case "$dev" in
    /dev/*) printf '%s\n' "$dev" ;;
    *) return 1 ;;
  esac
}

# Drapeaux --device-{read,write}-bps a passer a docker run. Rend une liste
# vide si aucun plafond n'est demande, ou si le device n'a pas pu etre resolu
# -- et dans ce dernier cas le DIT : un plafond demande et silencieusement non
# applique est pire que pas de plafond, parce qu'on se croit borne.
BLKIO_ARGS=()
compute_blkio_args() {
  BLKIO_ARGS=()
  [ -z "$DEVICE_WRITE_BPS$DEVICE_READ_BPS" ] && return 0
  local dev
  if ! dev="$(resolve_blkio_device)"; then
    echo "AVERTISSEMENT: plafond d'I/O par conteneur demande (write=$DEVICE_WRITE_BPS read=$DEVICE_READ_BPS) mais le device de DockerRootDir n'a pas pu etre resolu -- AUCUN plafond ne sera applique. Nommer le device : COURSIA_RUNNER_BLKIO_DEVICE=/dev/sdX" >&2
    return 0
  fi
  [ -n "$DEVICE_WRITE_BPS" ] && BLKIO_ARGS+=(--device-write-bps "$dev:$DEVICE_WRITE_BPS")
  [ -n "$DEVICE_READ_BPS" ] && BLKIO_ARGS+=(--device-read-bps "$dev:$DEVICE_READ_BPS")
  echo "plafond d'I/O par conteneur : $dev write=${DEVICE_WRITE_BPS:-illimite} read=${DEVICE_READ_BPS:-illimite} (octets/s)"
  return 0
}

# --- Borne agregee : VERIFIER la slice, ne pas la re-imposer ----------------

# La slice systemd est appliquee par defaut du daemon. Ce garde ne la pose pas,
# il constate qu'elle est en vigueur ET qu'elle porte reellement un io.max --
# une slice qui existe sans limite est un cgroup vide qui a l'exacte apparence
# d'un garde. La verification lit le kernel, pas la configuration :
# /sys/fs/cgroup/<parent imbrique>/io.max.
#
# systemd imbrique une slice sur son nom : `coursia-ci.slice` vit sous
# `coursia.slice`. On essaie les formes plausibles plutot que de coder
# l'imbrication en dur.
assert_cgroup_budget() {
  [ -z "$CGROUP_PARENT" ] && return 0
  local base path found="" io=""
  base="${CGROUP_PARENT%.slice}"
  for path in \
      "/sys/fs/cgroup/${base%%-*}.slice/${CGROUP_PARENT}" \
      "/sys/fs/cgroup/${CGROUP_PARENT}" \
      "/sys/fs/cgroup/system.slice/${CGROUP_PARENT}"; do
    if [ -d "$path" ]; then found="$path"; break; fi
  done
  if [ -n "$found" ] && [ -r "$found/io.max" ]; then
    io="$(cat "$found/io.max" 2>/dev/null)"
  fi
  if [ -n "$io" ]; then
    echo "budget agrege en vigueur : $found"
    echo "  io.max  = $io"
    [ -r "$found/cpu.max" ] && echo "  cpu.max = $(cat "$found/cpu.max")"
    return 0
  fi
  local msg="budget agrege $CGROUP_PARENT INTROUVABLE ou sans io.max"
  local how="Deployer la slice et le defaut du daemon :
    sudo cp scripts/ci/docker/linux-runner/persist/coursia-ci.slice /etc/systemd/system/
    sudo cp scripts/ci/docker/linux-runner/persist/daemon.json /etc/docker/daemon.json
    sudo systemctl daemon-reload && sudo systemctl restart docker.service
  Puis relire : cat /sys/fs/cgroup/coursia.slice/coursia-ci.slice/io.max"
  if [ "$REQUIRE_CGROUP_BUDGET" = "1" ]; then
    die "$msg -- REFUS de demarrer (COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET=1).
Un pool non borne est precisement ce qui a gele cette machine ; un echec
lisible vaut mieux qu'un demarrage silencieux.
$how"
  fi
  echo "AVERTISSEMENT: $msg -- les familles tourneront SANS plafond agrege." >&2
  echo "$how" >&2
  return 0
}

# --- Budget CPU inter-familles ---------------------------------------------

# Enumere TOUTES les familles de superviseur actives, une par ligne :
#   <pid> <famille> <n>
#
# Distinct de supervisor_pids() a dessein. supervisor_pids() est le garde
# d'idempotence de `start` : il ne doit voir que `start`, sinon un pool de
# waiters actif ferait refuser un `start` legitime (les familles coexistent
# par design). Ce recensement-ci repond a l'autre question -- « que tourne-t-il
# en tout sur cette machine ? » -- et c'est celle que le budget CPU pose.
#
# La table des processus est la source : elle porte deja la famille et le N
# dans l'argv, elle traverse les state dirs (ai-01 en a deux, un par jambe) et
# elle ne peut pas deriver d'un fichier d'etat oublie.
supervisor_families() {
  local me="$$"
  ps -ef 2>/dev/null \
    | grep -E '[s]upervise\.sh (start|waiters|lean)' \
    | awk -v me="$me" '$2 != me && $3==1 {
        for (i=1; i<=NF; i++) {
          if ($i ~ /supervise\.sh$/) {
            fam = $(i+1); n = $(i+2);
            if (n !~ /^[0-9]+$/) n = "";
            print $2, fam, n;
            break;
          }
        }
      }'
}

# Cap CPU par conteneur DECLARE par un superviseur donne, lu dans son propre
# environnement (/proc/<pid>/environ) -- pas dans le mien. Deux superviseurs
# lances par des wrappers differents portent des caps differents ; supposer les
# miens rendrait un budget faux et confiant.
family_cpus_of() {
  local pid="$1" fam="$2" var fallback val=""
  case "$fam" in
    start)   var="COURSIA_RUNNER_CPUS";        fallback="$CPUS" ;;
    waiters) var="COURSIA_RUNNER_WAITER_CPUS"; fallback="$WAITER_CPUS" ;;
    lean)    var="COURSIA_LEAN_RUNNER_CPUS";   fallback="$LEAN_CPUS" ;;
    *)       printf '0\n'; return 0 ;;
  esac
  if [ -r "/proc/$pid/environ" ]; then
    val="$(tr '\0' '\n' < "/proc/$pid/environ" 2>/dev/null | sed -n "s/^${var}=//p" | head -1)"
  fi
  printf '%s\n' "${val:-$fallback}"
}

# Ferme le trou nomme dans cmd_lean depuis #14337 :
#   « La somme des caps CPU des familles actives n'est gardee par RIEN --
#     c'est l'operateur qui dimensionne. »
# Un cap `--cpus` est PAR CONTENEUR : 12 waiters a 1 vCPU sont conformes un a
# un et prennent 12 coeurs ensemble. Le seul endroit ou la somme existe est
# ici, avant de lancer la famille suivante.
#
# Refus, jamais avertissement : depasser le budget est exactement l'etat qui a
# gele la machine, et un demarrage refuse se repare en une commande.
assert_cpu_budget() {
  local new_fam="$1" new_n="$2" new_cpus="$3"
  [ "${CPU_BUDGET:-0}" = "0" ] && return 0
  local total detail pid fam n c sub
  total=0; detail=""
  while read -r pid fam n; do
    [ -z "${n:-}" ] && continue
    c="$(family_cpus_of "$pid" "$fam")"
    sub="$(awk -v a="$n" -v b="$c" 'BEGIN{printf "%.2f", a*b}')"
    total="$(awk -v a="$total" -v b="$sub" 'BEGIN{printf "%.2f", a+b}')"
    detail="$detail
  deja actif : $fam n=$n cpus=$c -> $sub"
  done < <(supervisor_families)
  sub="$(awk -v a="$new_n" -v b="$new_cpus" 'BEGIN{printf "%.2f", a*b}')"
  total="$(awk -v a="$total" -v b="$sub" 'BEGIN{printf "%.2f", a+b}')"
  detail="$detail
  demande    : $new_fam n=$new_n cpus=$new_cpus -> $sub"
  if awk -v t="$total" -v b="$CPU_BUDGET" 'BEGIN{exit !(t > b)}'; then
    die "budget CPU inter-familles depasse : $total vCPU demandes pour un plafond de $CPU_BUDGET.$detail

Le cap --cpus de docker est PAR CONTENEUR ; il ne borne pas une flotte (#14337).
Baisser N, arreter une autre famille, ou relever COURSIA_RUNNER_CPU_BUDGET en
connaissance de cause -- l'hote prime sur la CI (clause en tete de ce fichier)."
  fi
  echo "budget CPU inter-familles : $total / $CPU_BUDGET vCPU$detail"
}

# --- Rotation des journaux de slot ------------------------------------------

# Appelee avant chaque `docker run`. Une generation conservee, pas de
# dependance a logrotate : le superviseur tourne sous une unite systemd qui
# n'a pas de hook de rotation, et un journal non borne dans le repertoire
# d'etat est une fuite disque de plus dans un script qui existe pour les
# fermer. Mesure ai-01 2026-09-07 : /var/lib/coursia-runner = 14 Mo alors que
# le pool etait eteint la majeure partie de la journee.
rotate_log() {
  local f="$1" sz
  [ "${LOG_MAX_BYTES:-0}" = "0" ] && return 0
  [ -f "$f" ] || return 0
  sz="$(wc -c < "$f" 2>/dev/null | tr -d ' ')"
  [ -n "$sz" ] || return 0
  if [ "$sz" -gt "$LOG_MAX_BYTES" ]; then
    mv -f "$f" "$f.1" 2>/dev/null || true
    : > "$f"
  fi
}

# --- Backoff exponentiel avec jitter ----------------------------------------

# Rend le delai a attendre apres `n` echecs consecutifs : min * 2^(n-1),
# plafonne, puis disperse par un jitter de +/- BACKOFF_JITTER_PCT %.
# $RANDOM suffit ici -- on disperse des rafales, on ne tire rien de sensible.
backoff_delay() {
  local fails="$1" d="$BACKOFF_MIN_SEC" i
  for ((i=1; i<fails; i++)); do
    d=$(( d * 2 ))
    if [ "$d" -ge "$BACKOFF_MAX_SEC" ]; then d="$BACKOFF_MAX_SEC"; break; fi
  done
  [ "$d" -gt "$BACKOFF_MAX_SEC" ] && d="$BACKOFF_MAX_SEC"
  local span=$(( d * BACKOFF_JITTER_PCT / 100 ))
  if [ "$span" -gt 0 ]; then
    d=$(( d - span + (RANDOM % (2 * span + 1)) ))
  fi
  [ "$d" -lt 1 ] && d=1
  printf '%s\n' "$d"
}

# #14259 Defaut 1+3 : compte et liste les PIDs des superviseurs actifs du
# meme `NAME_PREFIX`. La cle est `PPID==1` : un superviseur est le parent
# direct d'un slot_loop fork (mesure : PPID 72469 = LE superviseur ;
# les slot_loop forks heritent de l'argv du superviseur mais leur PPID
# est 72469, pas 1). Les subshells `$(fetch_token)` ont un PPID
# transitoire egalement != 1. Le `awk '$3==1'` est donc non cosmetique
# -- sans lui, un `start 4` rend 5 PIDs et le defense-positif echoue.
# Sortie : liste espacee de PIDs (vide si aucun superviseur).
supervisor_pids() {
  local me out
  # #14347 : `$$` = PID du bash principal, stable dans les subshells.
  # `$PPID` vaut 1 sous systemd (herite du lancement par PID 1 ; bash ne le
  # recompute pas pour les subshells) -- mesure : self=PPID=1 avec out=mon
  # propre PID, donc le garde s'auto-matchait et le service crash-loopait.
  me="$$"
  out="$(ps -ef 2>/dev/null | grep '[s]upervise\.sh start' | awk -v me="$me" '$2 != me && $3==1 {print $2}')"
  printf '%s\n' "$out"
}

fetch_token() {
  # Le registration token vaut 1 h et est jetable : un par demarrage de
  # conteneur. C'est la raison pour laquelle la boucle vit sur l'HOTE et non
  # dans l'image -- `gh` et ses credentials ne descendent jamais dans le
  # conteneur.
  #
  # #14259 epinglage : GH_TOKEN ambiant est honore tel quel par gh ;
  # COURSIA_RUNNER_GH_ACCOUNT (plus specifique) le surpasse en resolvant
  # le token du compte nomme. Sans epinglage, le fetch depend du compte
  # gh ACTIF -- un `gh auth switch` dans une autre session changeait
  # l'identite des registration tokens en silence (incident 2026-09-02).
  if [ -n "${COURSIA_RUNNER_GH_ACCOUNT:-}" ]; then
    GH_TOKEN="$(gh auth token --user "$COURSIA_RUNNER_GH_ACCOUNT")" || return 1
    export GH_TOKEN
  fi
  # Pas de 2>/dev/null (#14259) : l'erreur REELLE de gh (403, token expire,
  # compte sans droit admin) doit atteindre l'operateur. Le message de la
  # boucle resume le symptome ; il ne remplace pas la cause.
  gh api --method POST "repos/$REPO/actions/runners/registration-token" --jq .token
}

# Parametre depuis #14337 : un slot = une boucle, mais nom/labels/image/caps
# dependent du pool (linux genrique, lean). Les volumes toolcache/_work restent
# la regle pour les pools D'EXECUTION (les waiters ont leur propre boucle sans
# volume).
slot_loop() {
  local slot="$1" name="$2" labels="$3" image="$4" cpus="$5" memory="$6" pids="$7"
  local vol_prefix="${8:-$WORK_VOLUME_PREFIX}"
  # Swap optionnel (pool lean : les modules Hashlife pointent >16 Go, mesure
  # #14337). Vide = pas de --memory-swap, docker default (memory == swap).
  local mem_swap="${9:-}"
  local swap_args=()
  [ -n "$mem_swap" ] && swap_args=(--memory-swap "$mem_swap")
  # Compteur d'echecs CONSECUTIFS : c'est lui qui porte le backoff, et il est
  # remis a zero par le premier cycle propre. Une panne franche se calme ; un
  # job qui echoue de temps en temps ne penalise pas le slot.
  local fails=0 wait_s
  echo "[slot $slot] demarrage, nom runner=$name"
  while [ ! -f "$STOP_FILE" ]; do
    local token
    token="$(fetch_token)"
    if [ -z "$token" ]; then
      fails=$(( fails + 1 ))
      wait_s="$(backoff_delay "$fails")"
      echo "[slot $slot] token indisponible (droit admin gh ?) -- echec consecutif #$fails, nouvelle tentative dans ${wait_s}s" >&2
      sleep "$wait_s"
      continue
    fi
    # #15095 : la duree de vie du conteneur est mesuree depuis AVANT le run
    # (offset pris avant rotate_log, comme le log_off du signal de travail).
    local t0=$SECONDS
    rotate_log "$STATE_DIR/$name.log"
    # Offset du log au debut du cycle : le signal de travail de cycle_backoff
    # ne doit lire QUE ce que CE cycle ecrit (le log est cumulatif, cf le
    # commentaire dans cycle_backoff).
    local log_off
    log_off="$(wc -c < "$STATE_DIR/$name.log" 2>/dev/null | tr -d ' ' || echo 0)"
    log_off="${log_off:-0}"
    # --rm : le conteneur disparaît avec le job. --ephemeral (dans l'entrypoint)
    # desenregistre le runner cote GitHub. Un cycle = un job, proprement --
    # mais le cache de depot (volume par slot) survit au conteneur (#14285).
    docker run --rm \
      --name "$name" \
      --cpus="$cpus" --memory="$memory" --pids-limit="$pids" \
      "${swap_args[@]+"${swap_args[@]}"}" \
      "${BLKIO_ARGS[@]+"${BLKIO_ARGS[@]}"}" \
      --security-opt=no-new-privileges \
      -v "$TOOLCACHE_VOLUME":"$TOOLCACHE_MOUNT" \
      -v "${vol_prefix}-${slot}":"$WORK_MOUNT" \
      -e RUNNER_TOOL_CACHE="$TOOLCACHE_MOUNT" \
      -e RUNNER_WORK_CACHE_PACK_THRESHOLD="$CACHE_PACK_THRESHOLD" \
      -e ACTIONS_RUNNER_INPUT_TOKEN="$token" \
      -e ACTIONS_RUNNER_INPUT_URL="https://github.com/$REPO" \
      -e ACTIONS_RUNNER_INPUT_NAME="$name" \
      -e ACTIONS_RUNNER_INPUT_LABELS="$labels" \
      "$image" >>"$STATE_DIR/$name.log" 2>&1
    local rc=$?
    # #15095 : la duree de vie du conteneur, pas son rc, pilote la
    # respiration du cycle (cf cycle_backoff) -- un cycle court rc=0
    # martelait docker 4-8 fois/min sur l'incident 07/09, exactement le
    # trou que le compteur d'echecs rc!=0 laisse passer par construction.
    local lifetime=$(( SECONDS - t0 ))
    # #15091 : le compteur d'echecs consecutifs reste tenu a jour (il
    # alimente le backoff du chemin token ci-dessus) ; la respiration
    # post-run est deleguee a cycle_backoff, qui couvre les deux branches
    # (cycle court quelle que soit rc, cycle sain) sans double sommeil.
    if [ "$rc" -ne 0 ]; then
      fails=$(( fails + 1 ))
    else
      fails=0
    fi
    cycle_backoff "[slot $slot]" "$lifetime" "$rc" "$STATE_DIR/$name.log" "$log_off"
  done
  echo "[slot $slot] arret demande, boucle terminee"
}

cmd_start() {
  local n="${1:-2}"
  local force=0
  # #14259 Defaut 2 : `--force` permet de lever un sentinel STOP pose
  # prealablement (par `cmd_stop`). Sans `--force`, un start en presence
  # du sentinel est REFUSE pour eviter qu'un operateur (ou un cron)
  # n'annule un arret gracieux par accident. La portee est la meme
  # qu'un `rm -f` historique -- seuls les appels explicites passent.
  [ "${2:-}" = "--force" ] && force=1
  command -v docker >/dev/null || die "docker introuvable"
  command -v gh >/dev/null || die "gh introuvable"
  validate_backoff_env
  assert_docker_daemon
  docker image inspect "$IMAGE" >/dev/null 2>&1 \
    || die "image $IMAGE absente -- construire d'abord :
    docker build -t $IMAGE scripts/ci/docker/linux-runner/"
  assert_image_fresh "$IMAGE" "docker build -t $IMAGE scripts/ci/docker/linux-runner/"
  docker volume create "$TOOLCACHE_VOLUME" >/dev/null \
    || die "volume $TOOLCACHE_VOLUME impossible a creer -- docker volume create"
  # #14259 Defaut 1 : garde d'idempotence. `pgrep` n'existe PAS sous Git
  # Bash (mesure 2026-09-02 : command-not-found silencieux derriere
  # `2>/dev/null`). La forme portable utilise `ps -ef` + `awk '$3==1'`
  # (PPID==1 filtre les slot_loop forks et les subshells `$(...)` qui
  # heritent de l'argv du parent -- mesure : un `start 4` produit 5
  # lignes de `ps -ef | grep` mais UN seul superviseur, PPID==1). Si
  # un superviseur du meme `NAME_PREFIX` est deja actif, on REFUSE et
  # on nomme les PIDs -- un deuxieme `start` produirait deux boucles
  # concurrantes portant des copies differentes de l'environnement
  # (incident po-2024 2026-09-02, plusieurs PRs de contenu bloquees).
  local existing_pids
  existing_pids="$(supervisor_pids)"
  if [ -n "$existing_pids" ]; then
    die "un superviseur $NAME_PREFIX est deja actif (PID $existing_pids) ;
utiliser '$0 stop' d'abord, ou relancer sous une machine differente."
  fi
  # #14259 Defaut 2 : si le sentinel STOP_FILE est pose, refuser sauf
  # `--force`. C'est le mecanisme cle qui protege un arret gracieux :
  # un `stop` pose le sentinel, les boucles existantes ne relancent
  # plus de conteneur, et un `start` ulterieur NE DOIT PAS effacer
  # le sentinel sinon le superviseur (s'il survit) reprendrait. Le
  # seul moyen de re-marcher apres un stop est `--force`, qui dit
  # explicitement « j'ai conscience que je relance sur un stop en
  # cours ».
  if [ -f "$STOP_FILE" ] && [ "$force" -ne 1 ]; then
    die "sentinel STOP_FILE present ($STOP_FILE) -- un arret gracieux
est en cours. Attendre la fin des jobs, faire '$0 stop' (no-op si deja
fait) puis '$0 start', OU relancer avec '$0 start $n --force'."
  fi
  # Les trois bornes, verifiees AVANT de lever le sentinel : un refus ne doit
  # laisser aucune trace, sinon un arret gracieux en cours serait annule par
  # une tentative de demarrage que l'on vient justement de refuser.
  assert_cgroup_budget
  assert_cpu_budget "start" "$n" "$CPUS"
  compute_blkio_args
  # Sur succes, on leve le sentinel -- le superviseur qui demarre prend
  # la main sur l'etat precedent (Defaut 2 dans son volet `start`
  # historiquement effacait sans condition ; ici il n'efface que si
  # on a passe la garde --force).
  rm -f "$STOP_FILE"
  echo "demarrage de $n slot(s) ; caps par conteneur : cpus=$CPUS memory=$MEMORY pids=$PIDS ; toolcache=$TOOLCACHE_VOLUME -> $TOOLCACHE_MOUNT ; cache depot=${WORK_VOLUME_PREFIX}-{1..$n} -> $WORK_MOUNT"
  for i in $(seq 1 "$n"); do
    # Volume de cache de depot par slot : cree ici pour echouer tot avec un
    # message clair (docker run -v creerait le volume tout seul, mais muet).
    docker volume create "${WORK_VOLUME_PREFIX}-${i}" >/dev/null \
      || die "volume ${WORK_VOLUME_PREFIX}-${i} impossible a creer -- docker volume create"
    slot_loop "$i" "${NAME_PREFIX}-${i}" "$LABELS" "$IMAGE" "$CPUS" "$MEMORY" "$PIDS" &
    echo "$!" >> "$STATE_DIR/pids"
  done
  echo "slots lances. Arret gracieux : $0 stop"
  wait
}

cmd_stop() {
  # Arret GRACIEUX : on pose le sentinel, les boucles ne relancent plus de
  # conteneur. Le job en cours va a son terme -- on ne tue pas un job qui
  # tourne, il rendrait un rouge qui ne veut rien dire.
  #
  # LE SENTINEL SE VERIFIE APRES L'ECRITURE (#15091). Cette fonction rendait
  # 0 quoi qu'il arrive : sous `set -uo pipefail` SANS `-e`, l'echec du
  # `touch` n'interrompait rien, et le code de retour etait celui du dernier
  # `echo`. Un arret inerte etait donc indiscernable d'un arret reussi.
  #
  # Ce n'est pas une hypothese : sur ai-01, l'unite appelait ce script sans
  # COURSIA_RUNNER_STATE_DIR, le sentinel atterrissait dans un
  # /root/.coursia-runner/ que ce script CREE lui-meme, le superviseur
  # surveillait /var/lib/coursia-runner/ -- et `systemctl stop` annoncait le
  # succes avant de retomber sur son SIGTERM. La reparation du cablage vit
  # dans persist/ai-01/ ; celle-ci est la borne qui rend le meme defaut
  # LISIBLE la prochaine fois, quel que soit l'appelant.
  #
  # Le test verifie la PRESENCE du fichier, pas le code de retour du touch :
  # ce qui compte est qu'un fichier existe a l'endroit que les boucles
  # surveillent -- un touch qui reussit sur un chemin que personne ne lit
  # n'est pas un arret.
  if ! touch "$STOP_FILE" 2>/dev/null || [ ! -e "$STOP_FILE" ]; then
    echo "ERREUR: sentinel NON pose -- $STOP_FILE n'a pas pu etre ecrit." >&2
    echo "  Les boucles de slot continuent de lancer des conteneurs." >&2
    echo "  Verifier les droits sur $STATE_DIR, et que COURSIA_RUNNER_STATE_DIR" >&2
    echo "  designe bien le repertoire surveille par le superviseur en cours" >&2
    echo "  (un STATE_DIR different est cree en silence, et l'arret est inerte)." >&2
    return 1
  fi
  echo "sentinel pose : $STOP_FILE"
  echo "aucun nouveau conteneur ne sera lance."
  echo "Les jobs en cours vont a leur terme. Pour couper net (deconseille) :"
  echo "  docker ps --filter name=$NAME_PREFIX -q | xargs -r docker kill"
  echo "  docker ps --filter name=$LEAN_NAME_PREFIX -q | xargs -r docker kill"
}

cmd_status() {
  echo "== superviseurs actifs =="
  # #14259 Defaut 3 : compte par PPID==1 (cf supervisor_pids). Un compte
  # > 1 signale une anomalie (deux superviseurs concurrents portant des
  # copies differentes de l'environnement -- incident 2026-09-02). On
  # ixe le format pour qu'un grep ulterieur (alerting, sweep CI)
  # puisse matcher une ligne `superviseurs actifs : N`.
  local pids
  pids="$(supervisor_pids)"
  if [ -z "$pids" ]; then
    echo "  superviseurs actifs : 0"
  else
    local count
    count="$(echo "$pids" | wc -l | tr -d ' ')"
    if [ "$count" -gt 1 ]; then
      echo "  superviseurs actifs : $count (PID $pids) -- ANOMALIE : >1 superviseur concurrent"
    else
      echo "  superviseurs actifs : $count (PID $pids)"
    fi
  fi
  echo "== familles actives (toutes, tous state dirs) =="
  # supervisor_pids() ci-dessus ne voit que `start` (c'est son role : garder
  # l'idempotence de start). Le recensement inter-familles repond a l'autre
  # question, celle que pose le budget CPU.
  local fam_lines
  fam_lines="$(supervisor_families)"
  if [ -z "$fam_lines" ]; then
    echo "  aucune famille active"
  else
    local pid fam n c
    while read -r pid fam n; do
      [ -z "${fam:-}" ] && continue
      c="$(family_cpus_of "$pid" "$fam")"
      echo "  $fam n=${n:-?} cpus=$c (pid $pid)"
    done <<< "$fam_lines"
  fi
  echo "== bornes =="
  if [ -n "$CGROUP_PARENT" ]; then
    assert_cgroup_budget 2>&1 | sed 's/^/  /'
  else
    echo "  budget agrege : non declare (COURSIA_RUNNER_CGROUP_PARENT vide)"
  fi
  if [ -n "$DEVICE_WRITE_BPS$DEVICE_READ_BPS" ]; then
    compute_blkio_args 2>&1 | sed 's/^/  /'
  else
    echo "  plafond par conteneur : non declare (COURSIA_RUNNER_DEVICE_WRITE_BPS vide)"
  fi
  echo "  budget CPU inter-familles : ${CPU_BUDGET:-0} vCPU (0 = pas de garde)"
  echo "== conteneurs runner en cours =="
  docker ps --filter "name=$NAME_PREFIX" --format '  {{.Names}}  {{.Status}}  {{.RunningFor}}' 2>/dev/null || true
  echo "== runners enregistres cote GitHub =="
  # #14259 : nommer la contradiction docker-vs-inventaire au lieu
  # d'afficher les deux blocs cote a cote. « N conteneurs / 0 runner
  # enregistre » est l'etat exact de l'incident 2026-09-02 (jetons crees
  # sous un compte, inventaire lu sous un autre). Une fenetre transitoire
  # existe au re-enregistrement entre deux jobs (--ephemeral), d'ou le
  # « si persistant » du message.
  local runners_ok=0 runners_out=""
  if runners_out="$(gh api "repos/$REPO/actions/runners" \
      --jq '.runners[]|"  \(.name) [\(.status)] busy=\(.busy) labels=\([.labels[].name]|join(","))"' 2>/dev/null)"; then
    runners_ok=1
    printf '%s\n' "$runners_out"
  else
    echo "  (droit admin requis pour lire l'inventaire)"
  fi
  if [ "$runners_ok" -eq 1 ]; then
    local n_cont n_run
    n_cont="$(docker ps --filter "name=$NAME_PREFIX" -q 2>/dev/null | wc -l | tr -d ' ')"
    n_run="$(printf '%s\n' "$runners_out" | grep -c '^  ' || true)"
    if [ "$n_cont" -gt 0 ] && [ "$n_run" -eq 0 ]; then
      echo "  -- CONTRADICTION : $n_cont conteneur(s) $NAME_PREFIX actif(s) mais 0 runner enregistre cote GitHub."
      echo "     Si persistant : fetch_token sous un mauvais compte -- cf epinglage COURSIA_RUNNER_GH_ACCOUNT (#14259)."
    fi
  fi
  [ -f "$STOP_FILE" ] && echo "== sentinel STOP pose : les boucles ne relancent plus =="
}

waiter_loop() {
  # Meme mecanique que slot_loop, mais pour le pool d'attente PR-gate : nom,
  # caps et label du pool waiter. Un waiter ne porte JAMAIS coursia-linux :
  # aucun job reel ne doit lui atterrir, il n'existe que pour absorber
  # l'attente du gate. Pas de volume -- rien a persister.
  local slot="$1"
  local name="${WAITER_NAME_PREFIX}-${slot}"
  local fails=0 wait_s
  # Toolcache seul -- jamais de volume _work (cf commentaire WAITER_TOOLCACHE).
  local tc_args=()
  if [ "$WAITER_TOOLCACHE" = "1" ]; then
    tc_args=(-v "$TOOLCACHE_VOLUME":"$TOOLCACHE_MOUNT" -e RUNNER_TOOL_CACHE="$TOOLCACHE_MOUNT")
  fi
  echo "[waiter $slot] demarrage, nom runner=$name"
  while [ ! -f "$STOP_FILE" ]; do
    local token
    token="$(fetch_token)"
    if [ -z "$token" ]; then
      fails=$(( fails + 1 ))
      wait_s="$(backoff_delay "$fails")"
      echo "[waiter $slot] token indisponible (droit admin gh ?) -- echec consecutif #$fails, nouvelle tentative dans ${wait_s}s" >&2
      sleep "$wait_s"
      continue
    fi
    local t0=$SECONDS
    rotate_log "$STATE_DIR/$name.log"
    local log_off
    log_off="$(wc -c < "$STATE_DIR/$name.log" 2>/dev/null | tr -d ' ' || echo 0)"
    log_off="${log_off:-0}"
    docker run --rm \
      --name "$name" \
      --cpus="$WAITER_CPUS" --memory="$WAITER_MEMORY" --pids-limit="$WAITER_PIDS" \
      "${BLKIO_ARGS[@]+"${BLKIO_ARGS[@]}"}" \
      --security-opt=no-new-privileges \
      "${tc_args[@]+"${tc_args[@]}"}" \
      -e ACTIONS_RUNNER_INPUT_TOKEN="$token" \
      -e ACTIONS_RUNNER_INPUT_URL="https://github.com/$REPO" \
      -e ACTIONS_RUNNER_INPUT_NAME="$name" \
      -e ACTIONS_RUNNER_INPUT_LABELS="$WAITER_LABELS" \
      "$IMAGE" >>"$STATE_DIR/$name.log" 2>&1
    local rc=$?
    # #15095 + #15091 composes (cf boucle slot) : duree de vie pilote la
    # respiration, compteur d'echecs tenu pour le chemin token.
    local lifetime=$(( SECONDS - t0 ))
    if [ "$rc" -ne 0 ]; then
      fails=$(( fails + 1 ))
    else
      fails=0
    fi
    cycle_backoff "[waiter $slot]" "$lifetime" "$rc" "$STATE_DIR/$name.log" "$log_off"
  done
  echo "[waiter $slot] arret demande, boucle terminee"
}

cmd_waiters() {
  local n="${1:-24}"
  command -v docker >/dev/null || die "docker introuvable"
  command -v gh >/dev/null || die "gh introuvable"
  validate_backoff_env
  assert_docker_daemon
  docker image inspect "$IMAGE" >/dev/null 2>&1 \
    || die "image $IMAGE absente -- construire d'abord :
    docker build -t $IMAGE scripts/ci/docker/linux-runner/"
  assert_image_fresh "$IMAGE" "docker build -t $IMAGE scripts/ci/docker/linux-runner/"
  [ -f "$STOP_FILE" ] && die "sentinel STOP pose -- arreter d'abord ($0 stop)"
  # Idempotence propre a la famille waiters : le garde de `start` filtre
  # `supervise.sh start` et ne voit pas `waiters`. Verrou porte par le pid
  # de la boucle -- si elle est morte, kill -0 echoue et on relance.
  if [ -f "$STATE_DIR/waiter-pids" ]; then
    local head_pid
    head_pid="$(head -1 "$STATE_DIR/waiter-pids" 2>/dev/null || true)"
    if [ -n "$head_pid" ] && kill -0 "$head_pid" 2>/dev/null; then
      die "waiters deja lancees (pid $head_pid) -- arreter d'abord ($0 stop)"
    fi
  fi
  # Les trois bornes, verifiees AVANT de lever le sentinel : un refus ne doit
  # laisser aucune trace, sinon un arret gracieux en cours serait annule par
  # une tentative de demarrage que l'on vient justement de refuser.
  assert_cgroup_budget
  assert_cpu_budget "waiters" "$n" "$WAITER_CPUS"
  compute_blkio_args
  rm -f "$STATE_DIR/waiter-pids"
  echo "demarrage de $n waiter(s) ; labels=$WAITER_LABELS ; caps : cpus=$WAITER_CPUS memory=$WAITER_MEMORY pids=$WAITER_PIDS"
  for i in $(seq 1 "$n"); do
    waiter_loop "$i" &
    echo "$!" >> "$STATE_DIR/waiter-pids"
  done
  echo "waiters lancees. Arret gracieux : $0 stop"
  wait
}

cmd_lean() {
  local n="${1:-2}"
  command -v docker >/dev/null || die "docker introuvable"
  command -v gh >/dev/null || die "gh introuvable"
  validate_backoff_env
  assert_docker_daemon
  docker image inspect "$LEAN_IMAGE" >/dev/null 2>&1 \
    || die "image $LEAN_IMAGE absente -- construire d'abord :
    docker build -t $LEAN_IMAGE -f scripts/ci/docker/linux-runner/Dockerfile.lean scripts/ci/docker/linux-runner/"
  # Dockerfile.lean FROM coursia-linux-runner : l'entrypoint est herite de la
  # base -- un ecart pointe soit vers l'image lean, soit vers sa base.
  assert_image_fresh "$LEAN_IMAGE" "docker build -t $LEAN_IMAGE -f scripts/ci/docker/linux-runner/Dockerfile.lean scripts/ci/docker/linux-runner/"
  [ -f "$STOP_FILE" ] && die "sentinel STOP pose -- arreter d'abord ($0 stop)"
  # Idempotence calquee sur cmd_waiters : le garde PPID de `start` filtre
  # `supervise.sh start` et ne verrait pas `lean`. Verrou par pid file.
  #
  # Budget CPU inter-familles (#15091, fermeture du trou nomme ici depuis
  # #14337). Le garde PPID ne couvre que les superviseurs d'un MEME prefix,
  # donc `start`, `waiters` et `lean` coexistent par design -- et leur somme
  # n'etait gardee par RIEN : « c'est l'operateur qui dimensionne ». C'est
  # desormais assert_cpu_budget qui la garde, en lisant les familles actives
  # dans la table des processus et leurs caps dans /proc/<pid>/environ.
  # Il reste INACTIF tant que COURSIA_RUNNER_CPU_BUDGET vaut 0 : aucune
  # machine ne se voit imposer un plafond qu'elle n'a pas declare (po-2024
  # garde son comportement ; ai-01 declare 8 dans son wrapper).
  # Le pool lean reste dimensionne pour tourner SEUL sur la jambe CI lourde --
  # avec le budget arme, le demarrage est desormais REFUSE au lieu de degrader
  # la machine en silence.
  if [ -f "$STATE_DIR/lean-pids" ]; then
    local head_pid
    head_pid="$(head -1 "$STATE_DIR/lean-pids" 2>/dev/null || true)"
    if [ -n "$head_pid" ] && kill -0 "$head_pid" 2>/dev/null; then
      die "pool lean deja lance (pid $head_pid) -- arreter d'abord ($0 stop)"
    fi
  fi
  # Les trois bornes, verifiees AVANT de lever le sentinel : un refus ne doit
  # laisser aucune trace, sinon un arret gracieux en cours serait annule par
  # une tentative de demarrage que l'on vient justement de refuser.
  assert_cgroup_budget
  assert_cpu_budget "lean" "$n" "$LEAN_CPUS"
  compute_blkio_args
  rm -f "$STATE_DIR/lean-pids"
  echo "demarrage de $n slot(s) lean ; labels=$LEAN_LABELS ; caps : cpus=$LEAN_CPUS memory=$LEAN_MEMORY pids=$LEAN_PIDS ; image=$LEAN_IMAGE ; .lake chaud=${LEAN_WORK_VOLUME_PREFIX}-{1..$n} -> $WORK_MOUNT"
  for i in $(seq 1 "$n"); do
    docker volume create "${LEAN_WORK_VOLUME_PREFIX}-${i}" >/dev/null \
      || die "volume ${LEAN_WORK_VOLUME_PREFIX}-${i} impossible a creer -- docker volume create"
    slot_loop "$i" "${LEAN_NAME_PREFIX}-${i}" "$LEAN_LABELS" "$LEAN_IMAGE" \
      "$LEAN_CPUS" "$LEAN_MEMORY" "$LEAN_PIDS" "$LEAN_WORK_VOLUME_PREFIX" \
      "$LEAN_MEMORY_SWAP" &
    echo "$!" >> "$STATE_DIR/lean-pids"
  done
  echo "slots lean lances. Arret gracieux : $0 stop"
  wait
}

case "${1:-}" in
  start)   shift; cmd_start "${1:-2}" "${2:-}" ;;
  waiters) shift; cmd_waiters "${1:-24}" ;;
  lean)    shift; cmd_lean "${1:-2}" ;;
  stop)    cmd_stop ;;
  status)  cmd_status ;;
  *) echo "usage: $0 {start [N] [--force]|waiters [N]|lean [N]|stop|status}"; exit 2 ;;
esac
