#!/usr/bin/env bash
# Lanceur PERSISTANT du pool LEAN specialise (label coursia-lean).
#
# POURQUOI CE FICHIER EXISTE (incident 2026-09-09)
# -------------------------------------------
# La jambe `lean` n'avait de persistance sur AUCUNE machine : elle etait
# lancee a la main dans une session, et mourait avec elle. Consequence
# mesuree le 2026-09-09 : apres le reboot de po-2024 (restauration
# coursia-runner + coursia-waiters), le pool lean est reste a ZERO toute
# la journee -- aucun runner ne portait le label `coursia-lean`, le run
# main de lean-knot y est mort "runner lost communication" (check-run
# 102437210604), et deux jobs lean de PR sont restes en queue de 12:39Z a
# 15:00Z+ pendant que les runners generaux servaient tout le reste.
# po-2027 a nomme le defaut ; ce fichier le ferme cote po-2024, sur le
# meme pattern que coursia-waiters-start.sh (#14612, #14846).
#
# STATE_DIR DEDIE, ET C'EST LE POINT DELICAT. L'appel manuel d'avant
# l'incident tournait SANS COURSIA_RUNNER_STATE_DIR : supervise.sh
# retombait sur /var/lib/coursia-runner, PARTAGE avec la jambe
# d'execution. Deux consequences mesurees : la sentinelle d'arret etait
# commune (un `systemctl stop coursia-runner` aurait arrete le pool lean
# au passage), et les pid files des deux familles vivaient entremelles.
# D'ou /var/lib/coursia-lean -- la sentinelle et le verrou pid redeviennent
# par-jambe, comme pour les waiters.
#
# LE SECRET NE SE DUPLIQUE PAS : GH_RUNNERS_ADMIN_TOKEN est relu dans
# master.env a chaque demarrage (jamais recopie dans un EnvironmentFile,
# jamais en argv).
set -uo pipefail

# Le defaut de chemin a DEJA demenage : la migration du 2026-09-17 a deplace le
# depot `C:\dev\CoursIA` -> `D:\Dev\CoursIA`, et ce fichier pointait encore
# l'arborescence purgee. Ce n'etait pas cosmetique : `[ -r "$MASTER_ENV" ]`
# echoue AVANT la lecture du token, donc le lanceur sortait en `exit 1` et le
# pool lean restait a ZERO jusqu'a intervention -- exactement l'incident du
# 2026-09-09 que ce fichier existe pour fermer (#16578).
MASTER_ENV="${COURSIA_MASTER_ENV:-/mnt/d/Dev/CoursIA/.secrets/master.env}"
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/Dev/CoursIA}"
ARG="${1:-2}"

[ -r "$MASTER_ENV" ] || { echo "master.env illisible : $MASTER_ENV" >&2; exit 1; }

GH_TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$MASTER_ENV" | head -1 | tr -d '"'"'"'\r')"
[ -n "$GH_TOKEN" ] || { echo "GH_RUNNERS_ADMIN_TOKEN absent de master.env -- abandon" >&2; exit 1; }
export GH_TOKEN

# Daemon EPINGLE (meme raison que coursia-runner-start.sh) : sans cela
# l'integration WSL de Docker Desktop rattacherait les conteneurs a la session.
export DOCKER_HOST="${DOCKER_HOST:-unix:///var/run/docker-ce.sock}"

export COURSIA_LEAN_RUNNER_NAME_PREFIX="${COURSIA_LEAN_RUNNER_NAME_PREFIX:-myia-po-2024-lean-docker}"
export COURSIA_RUNNER_STATE_DIR="${COURSIA_RUNNER_STATE_DIR:-/var/lib/coursia-lean}"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

# MEME BUDGET QUE LES DEUX AUTRES JAMBES DE CETTE MACHINE -- 21 Go depuis le
# 2026-10-08 (le 42 etait devenu faux deux fois : VM revenue de 40 110 a
# 24 032 Mo, et son arithmetique comptait « 12x1536 waiters » pour des waiters
# a 512 Mo -- detail complet en tete de coursia-runner-start.sh).
#
# CETTE JAMBE EST CELLE QUI REND LE BUDGET VISIBLE, et c'est pour ca qu'elle
# doit le declarer : ses 2 slots a 6 Go demandent 12 288 Mo a eux seuls. Sous
# un budget trop court, le garde refuse leur demarrage -- ce qui est CORRECT,
# et c'est l'incident fondateur ecrit ici : sous l'ancien budget 12 Go, les
# slots lean ne demarraient JAMAIS tant que les autres familles etaient en vol.
# Un budget qui ne couvre pas la composition complete ne protege rien : il
# empeche une jambe entiere de tourner.
#
# Les trois jambes doivent annoncer le meme nombre : assert_memory_budget
# somme les familles entre elles, une divergence refuserait des slots sans
# nommer sa cause.
export COURSIA_RUNNER_BUDGET_GB="${COURSIA_RUNNER_BUDGET_GB:-21}"

# AUCUN SWAP POUR LA JAMBE LEAN (2026-10-08) -- memory-swap = memory.
# Le defaut de supervise.sh est `LEAN_MEMORY_SWAP="${COURSIA_LEAN_RUNNER_MEMORY_SWAP:-12g}"`,
# soit 6 Go de RAM PLUS 6 Go de swap par slot. On l'aligne ici sur LEAN_MEMORY :
# le conteneur dispose de 6 Go en tout, et d'aucune page sur disque.
#
# POURQUOI CE CHOIX, ALORS QUE LE COMMENTAIRE DE supervise.sh DIT LE CONTRAIRE.
# Le bloc LEAN de supervise.sh argumente que le swap n'est pas un dogme mais un
# curseur : « supprimer le swap ne retire pas le pic de Hashlife, il transforme
# un build qui deborde en un exit 137 ». C'est exact, et c'est le but recherche
# ici. Le swap d'une VM WSL est un FICHIER SUR LE DISQUE WINDOWS : chaque page
# poussee la retarde DriveFS, puis `G:`, puis RooSync -- la chaine qui a gele
# ai-01 quatre fois et qui a fait ecrire 104 GiB en 11 h a cette machine le
# 2026-10-08. Un build Lean qui deborde doit mourir (exit 137, echec local,
# retryable, un job perdu) plutot que d'emporter la coordination de la flotte.
#
# CONSEQUENCE NOMMEE : le build Hashlife de conway_lean depassait 16 Go a
# froid ; a 6 Go sans swap il ne passera PAS. La reponse est de router ce lake
# vers un runner hosted (32 Go de fallocate swap, lean-axiom.yml) -- exactement
# la conclusion que le commentaire de supervise.sh tire deja, et non de
# remonter le swap de cette machine.
# La valeur est ecrite ici pour ce qu'elle EST, pas referencee par le nom
# qu'elle porte dans supervise.sh : `LEAN_MEMORY` est une constante de
# supervise.sh, elle n'existe pas dans ce wrapper -- et ce fichier tourne sous
# `set -u`, donc `$LEAN_MEMORY` y serait une erreur de variable non definie,
# pas un defaut silencieux. La coherence avec le cap est gardee en lisant la
# MEME variable d'environnement que supervise.sh (COURSIA_LEAN_RUNNER_MEMORY),
# avec le meme defaut 6g : memory-swap = memory, y compris si le cap est
# surcharge un jour.
export COURSIA_LEAN_RUNNER_MEMORY_SWAP="${COURSIA_LEAN_RUNNER_MEMORY:-6g}"

# BUDGET CPU INTER-FAMILLES (#15574 item 3, arbitrage coordinateur du
# 2026-10-01, comment 5933689033) -- MEME NOMBRE que coursia-runner-start.sh.
# assert_cpu_budget somme les familles d'EXECUTION (start + lean ; les
# waiters, oisifs, en sont exclus) et refuse le demarrage au depassement.
# Valeur 24 depuis le 2026-10-08 : docker 4x3 + lean 2x6 = 24. C'etait 30 tant
# que la composition portait 6 slots docker ; le budget a suivi la composition,
# il ne l'a pas precedee. Le garde est inerte a 0 ou absent (etat anterieur de
# la machine).
export COURSIA_RUNNER_CPU_BUDGET="${COURSIA_RUNNER_CPU_BUDGET:-24}"

# PARENT CGROUP -- meme valeur que coursia-runner-start.sh, meme raison : les
# trois familles doivent entrer dans la MEME slice pour que ses limites
# s'appliquent a leur somme. Ce sont les 2 slots lean qui rendaient l'absence
# de mur visible (12 288 Mo de caps a eux seuls, contre une VM de 24 032) ;
# ils sont desormais sous MemorySwapMax=0 comme le reste de la CI.
export COURSIA_RUNNER_CGROUP_PARENT="coursia-ci.slice"

cd "$REPO_DIR" || exit 1

if [ "$ARG" = "stop" ]; then
  exec ./scripts/ci/docker/linux-runner/supervise.sh stop
fi
# --- PURGE SENTINELLE PERIMEE (#15163) -----------------------------
# Meme bloc que coursia-waiters-start.sh, avec le predicat PAR-JAMBE que
# son commentaire annoncait (« un futur supervise.sh lean prendra son
# propre predicat ») : `supervise\.sh lean`. Un predicat global ferait
# que chaque jambe refuserait de purger SA sentinelle tant qu'une AUTRE
# tourne -- un verrou par jambe garde par un test global ne garde rien.
if [ -e "$COURSIA_RUNNER_STATE_DIR/stop" ]; then
  if pgrep -f 'supervise\.sh lean' >/dev/null 2>&1; then
    echo "sentinelle presente ET superviseur vivant -- arret en cours, on n'interfere pas" >&2
    exit 1
  fi
  echo "sentinelle perimee (aucun superviseur vivant) -- purge avant demarrage" >&2
  rm -f "$COURSIA_RUNNER_STATE_DIR/stop"
fi
# ---------------------------------------------------------------------------
# Les pid files perimes (reboot) ne bloquent pas cmd_lean -- son garde
# teste le pid au kill -0 -- mais un fichier de pids d'un etat anterieur
# n'a aucune valeur : purge defensive coherente avec le rm -f de cmd_lean.
if [ -f "$COURSIA_RUNNER_STATE_DIR/lean-pids" ]; then
  head_pid="$(head -1 "$COURSIA_RUNNER_STATE_DIR/lean-pids" 2>/dev/null || true)"
  if [ -z "$head_pid" ] || ! kill -0 "$head_pid" 2>/dev/null; then
    rm -f "$COURSIA_RUNNER_STATE_DIR/lean-pids"
  fi
fi
exec ./scripts/ci/docker/linux-runner/supervise.sh lean "$ARG"
