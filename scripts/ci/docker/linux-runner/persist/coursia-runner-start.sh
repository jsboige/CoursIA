#!/usr/bin/env bash
# Wrapper de demarrage du superviseur de runners Linux CoursIA sous systemd.
# Deploiement po-2024 (2026-09-02) : copie de reference -- l'original vit
# dans la distro Ubuntu de l'hote, sous /usr/local/bin/coursia-runner-start.sh.
#
# Design :
#   - le token admin GitHub ne vit JAMAIS dans la distro ni dans un argv :
#     il est relu a CHAQUE invocation depuis master.env cote Windows
#     (sous /mnt/... via sed + tr -d '\r' -- CRLF tuerait la valeur) ;
#   - DOCKER_HOST epingle le socket docker-ce, pas le Docker Desktop ;
#   - l'etat superviseur (sentinel, logs slots) vit sous /var/lib/coursia-runner.
set -euo pipefail

# Racine du depot. Le defaut a DEJA demenage : la migration du 2026-09-17 a
# deplace `C:\dev\CoursIA` -> `D:\Dev\CoursIA`, et ce wrapper pointait encore
# l'arborescence purgee. Consequence, mesuree (#16578) : `TOKEN_FILE` illisible
# -> `FATAL` AVANT tout demarrage de slot, donc le pool d'execution reste a ZERO
# jusqu'a intervention. Les deux surcharges sont celles de la jambe lean, pour
# que les deux lanceurs po-2024 se reglent de la meme facon.
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/Dev/CoursIA}"

TOKEN_FILE="${COURSIA_MASTER_ENV:-$REPO_DIR/.secrets/master.env}"
TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$TOKEN_FILE" | tr -d '\r')"
if [ -z "$TOKEN" ]; then
    echo "FATAL: GH_RUNNERS_ADMIN_TOKEN absent de $TOKEN_FILE" >&2
    exit 1
fi

export DOCKER_HOST="unix:///var/run/docker-ce.sock"
export GH_TOKEN="$TOKEN"
export COURSIA_RUNNER_REPO="jsboige/CoursIA"
export COURSIA_RUNNER_NAME_PREFIX="myia-po-2024-linux-docker"
export COURSIA_RUNNER_STATE_DIR="/var/lib/coursia-runner"
export COURSIA_RUNNER_TOOLCACHE_VOLUME="coursia-runner-toolcache"

# BUDGET MEMOIRE AGREGE DE LA CI SUR CETTE MACHINE, en Go -- declare, pas subi.
# supervise.sh le lit dans l'environnement ; faute de declaration il retombe sur
# 12 en le SIGNALANT desormais a chaque demarrage. Le declarer ici est ce qui le
# rend auditable : la valeur effective vit dans un fichier que l'operateur ouvre,
# pas dans un defaut de shell que personne ne lit.
#
# 15 POUR po-2024 (2026-10-08, amendement J+7) -- LE 42 EST TOMBE, ET IL
# ETAIT DEVENU FAUX DEUX FOIS. Il avait ete pose le 2026-09-21 pour une VM de
# 40 110 Mo (.wslconfig memory=40GB, arbitrage user, mission
# msg-20260921T203652-qxg3en). Depuis, la VM est revenue a 24 Go : `.wslconfig
# memory=24GB` et `free -m` (24 032 Mo) le mesurent tous les deux. Et son
# arithmetique de 43 008 Mo n'a jamais ete la vraie : elle comptait
# « 12x1536 waiters » alors que WAITER_MEMORY vaut 512m (supervise.sh l.180).
# La composition REELLE etait 6x1536 + 12x512 + 2x6144 = 27 648 Mo de caps sur
# une VM de 24 032 -- une somme de caps superieure a la RAM, qui se paie en
# swap. Mesure du jour : 6 285 Mo de swap consommes, 104 GiB ecrits depuis le
# boot en moins de 11 h, DriveFS et la coordination de la flotte en premier.
#
# LA COMPOSITION QUE CE BUDGET DECLARE, ET CE QU'ELLE LAISSE :
#     4 slots docker x 1536 Mo = 6 144 Mo   (cap unitaire INCHANGE)
#     6 waiters      x  512 Mo = 3 072 Mo   (cap unitaire INCHANGE)
#     1 slot lean    x 6144 Mo = 6 144 Mo   (2 -> 1, verdict J+7 ci-dessous)
#     --------------------------------------
#     total CAPS                15 360 Mo   sur 24 032 -> marge 8 672 Mo
#
# ON REDUIT DES NOMBRES DE SLOTS, JAMAIS DES CAPS. Mesure du 2026-10-08 :
# 3 des 6 conteneurs docker touchaient leur cap de 1536 Mo a 99 %, donc le cap
# unitaire n'est pas en trop -- c'est la CONCURRENCE qui ne tenait pas. Un job
# lourd garde exactement le meme regime memoire ; il attend son tour au lieu de
# pousser la machine dans le swap. La regle #15202 de persist/README.md interdit
# d'abaisser un cap sans nommer les jobs non mesures qu'il couvre, et cette PR
# ne l'abaisse nulle part.
#
# LE BUDGET RESTE UN PLAFOND D'ADMISSION, PAS UN MUR. Il refuse de DEMARRER un
# slot au-dela de 15 Go ; il ne borne pas ce qu'un slot deja lance consomme.
# Le mur kernel est desormais pose sur cette machine : voir
# persist/po-2024/coursia-ci.slice (MemoryHigh=14G, MemoryMax=16G,
# MemorySwapMax=0), et COURSIA_RUNNER_CGROUP_PARENT plus bas, qui y fait entrer
# les conteneurs.
#
# LES TROIS JAMBES DOIVENT ANNONCER LE MEME NOMBRE. `assert_memory_budget`
# somme les conteneurs label `coursia-ci=1` de TOUTES les familles : deux jambes
# qui divergeraient refuseraient leurs slots l'une contre l'autre, et le message
# d'erreur ne nommerait pas la divergence -- il parlerait de memoire en vol.
# Les trois jambes de po-2024 portent 15 : celle-ci, la jambe lean, et la jambe
# waiters (par le drop-in persist/po-2024/coursia-waiters.service.d/10-sizing.conf,
# dont le wrapper appartient a ai-01 et ne declare aucun budget).
export COURSIA_RUNNER_BUDGET_GB=15

# PARENT CGROUP -- LE MUR KERNEL QUI MANQUAIT A CETTE MACHINE (2026-10-08).
# supervise.sh pose `--cgroup-parent=$COURSIA_RUNNER_CGROUP_PARENT` sur chaque
# conteneur quand cette variable est declaree : les conteneurs des trois
# familles entrent alors dans la meme slice, et les limites du parent
# s'appliquent a leur SOMME. C'est le seul endroit ou un budget inter-familles
# existe -- un plafond par conteneur ne peut pas borner une flotte.
#
# Le nom est `coursia-ci.slice` (pas le chemin imbrique complet) parce que ce
# daemon est docker-ce, pilote systemd : systemd y resout une slice sur son nom,
# donc `coursia-ci.slice` vit sous `coursia.slice` et le chemin cgroup reel est
# /sys/fs/cgroup/coursia.slice/coursia-ci.slice/. La forme litterale
# « coursia.slice/coursia-ci.slice » serait necessaire pour un daemon cgroupfs
# (Docker Desktop), qui ne resout rien -- ce n'est pas le cas ici.
#
# `assert_slice` REFUSE le demarrage si la slice declaree est introuvable ou
# sans `io.max`. La slice doit donc etre posee AVANT de redemarrer ces unites :
# c'est l'ordre documente en tete de persist/po-2024/coursia-ci.slice.
export COURSIA_RUNNER_CGROUP_PARENT="coursia-ci.slice"

# BUDGET CPU INTER-FAMILLES (#15574 item 3, arbitrage coordinateur du
# 2026-10-01, comment 5933689033). supervise.sh le lit (assert_cpu_budget) :
# somme des caps CPU des familles d'EXECUTION -- cette jambe-ci (start) et la
# jambe lean ; les waiters, oisifs, en sont EXCLUS depuis la meme decision.
# Refus au demarrage au depassement, jamais avertissement. Inerte a 0 ou
# absent : c'etait l'etat anterieur de cette machine, et la mesure #18673
# (637 jobs lourds / 7 j, p90/mediane ~9,4x, co-residence 0 -> 3+ voisins :
# mediane x21) a nomme la sur-souscription 48 vCPU declares / 16 disponibles
# comme mecanisme.
#
# DEUX ECARTS CONSIGNES par rapport au texte de l'arbitrage :
#   - 30, pas 24 : docker 6x3 + lean 2x6 = 30. A 24, la jambe lean serait
#     REFUSEE au demarrage (le garde somme les familles d'execution, waiters
#     exclus -- test 60 de test_supervise_guards.sh le demontre sur les deux
#     sens) : exactement le verrou « service failed » que l'arbitrage citait
#     pour ECARTER le budget 16. 30 est le plus petit budget ou la flotte
#     ordonnee (docker 6 + lean 2) demarre -- sur-souscription 1,875x au
#     lieu de 3,0x.
#   - le service passe de start 8 a start 6 (conforme a l'arbitrage) dans
#     coursia-runner.service : la reduction de 24 a 18 vCPU docker vit la.
#
# CE BLOC PASSE DE 30 A 24 PUIS A 18 LE 2026-10-08, ET LES DEUX FOIS CE SONT
# DES CONSEQUENCES, PAS DES ARBITRAGES. Le raisonnement initial tenait pour
# une composition docker 6 : 6x3 + 2x6 = 30, et 24 aurait refuse la jambe
# lean. Le budget memoire de cette PR descend les slots docker a 4, donc la
# somme redevenait 4x3 + 2x6 = 24. L'AMENDEMENT J+7 (verdict mesure, le
# point de retour prevu par l'arbitrage) descend la jambe lean a 1 slot :
# 4x3 + 1x6 = 18. Ce qui a change est la composition, pas la doctrine : le
# budget reste egal a la somme des caps des familles d'execution, jamais un
# chiffre choisi pour lui-meme.
#
# VERDICT J+7 (2026-10-08, characterize_runner_variance.py --days 7, 456 jobs
# lourds) : le ratio p90/mediane des jobs lourds par runner po-2024 est
# docker-1 9,3x · docker-2 5,1x · docker-3 14,5x · docker-4 4,0x ·
# docker-5 23,3x · docker-6 15,4x -- CINQ RUNNERS SUR SIX AU-DESSUS DU SEUIL
# 5x que l'arbitrage avait fixe. La regle s'applique donc : passage a 18 avec
# right-sizing, le right-sizing etant la jambe lean (2 -> 1 slots, son cap
# unitaire de 6 Go et 6 vCPU reste INCHANGE). Noter que la fenetre 7 j couvre
# majoritairement l'ere 6-slots/30 vCPU d'avant le budget memoire -- rapporte
# tel quel, la regle ne conditionnait pas sa decision a la composition.
#
# La sur-souscription CPU reelle de la machine baisse au passage : elle etait
# de 30 vCPU declares pour 16 disponibles (1,875x) avec 6 slots docker ; 24
# pour 16 (1,5x) avec 4 docker + 2 lean ; elle est de 18 pour 16 (1,125x)
# avec 4 docker + 1 lean.
#
# LES DEUX JAMBES D'EXECUTION PORTENT LE MEME NOMBRE (runner et lean) : le
# garde fire au demarrage de chacune et somme l'autre. La jambe waiters n'en
# declare pas : depuis l'exclusion, un demarrage de waiters n'ajoute rien a
# la somme -- la declarer serait du decor.
export COURSIA_RUNNER_CPU_BUDGET=18

# #15095 : echec immediat si le demon du socket epingle ne repond pas --
# AVANT tout demarrage de slot et tout fetch de registration token (gh).
# Sans cette garde, un daemon arrete + Restart=always = le superviseur
# martelait docker/gh indefiniment (incident 07/09 : 2 gels machine ai-01,
# ecriture ext4.vhdx 94-96 Mo/s). Le superviseur porte la meme garde en
# profondeur (assert_docker_daemon) -- celle-ci rend l'echec visible au
# niveau systemd des l'ExecStart.
if ! docker info >/dev/null 2>&1; then
    echo "FATAL: demon Docker indisponible sur DOCKER_HOST=$DOCKER_HOST (docker info echoue, #15095) -- reparer le daemon avant de relancer le service." >&2
    exit 1
fi

SUPERVISE="$REPO_DIR/scripts/ci/docker/linux-runner/supervise.sh"
mkdir -p "$COURSIA_RUNNER_STATE_DIR"

# --- PURGE SENTINELLE PERIMEE (#15163) -----------------------------
# supervise.sh pose "$STATE_DIR/stop" a l'arret gracieux et REFUSE de
# demarrer tant qu'elle est la. La sentinelle est un FICHIER : elle survit
# au reboot. Un arret gracieux suivi d'un redemarrage machine laissait donc
# l'unite echouer, et le pool restait a ZERO jusqu'a intervention humaine.
#
# C'est la 4e jambe, et la derniere non couverte : ai-01/runner, waiters et
# lean portent ce bloc depuis #15188. Ce wrapper-ci relaie n'importe quelle
# sous-commande (`exec "$SUPERVISE" "$@"`), et l'unite po-2024 route EXPRES
# son ExecStart ET son ExecStop vers lui (`start 12` / `stop`) : d'ou la
# garde sur `start` ci-dessous. Un bloc inconditionnel -- la forme d'ai-01,
# dont la branche `stop` est ecrite AVANT la purge -- refuserait ici l'arret
# gracieux des qu'un superviseur vit, puisque `stop` retombe sur ce meme
# bloc.
#
# Un ExecStart est une demande EXPLICITE de demarrage : si aucun superviseur
# n'est vivant, la sentinelle ne protege plus rien -- elle wedge. On la
# retire. Si un superviseur EST vivant, un arret est en cours : on
# n'interfere pas, et on sort en erreur plutot que de lui couper l'herbe
# sous le pied.
#
# LE PREDICAT EST PAR-JAMBE, PAS FLOTTE-ENTIERE (#15163). La sentinelle est
# deja par-jambe (/var/lib/coursia-runner/stop et
# /var/lib/coursia-waiters/stop sont deux fichiers distincts). Un predicat
# `supervise\.sh (start|waiters)` repondrait « un superviseur QUELCONQUE
# vit-il ? » -- chaque jambe refuserait alors de purger SA PROPRE sentinelle
# perimee tant que L'AUTRE tourne. Un verrou par jambe garde par un test
# global ne garde rien : il wedge. C'est le seul point ou les deux formes
# divergent, et c'est ce que le cas 4 de persist/test_sentinel_purge.sh
# mesure.
if [ "${1:-start}" = "start" ] && [ -e "$COURSIA_RUNNER_STATE_DIR/stop" ]; then
  if pgrep -f 'supervise\.sh start' >/dev/null 2>&1; then
    echo "sentinelle presente ET superviseur vivant -- arret en cours, on n'interfere pas" >&2
    exit 1
  fi
  echo "sentinelle perimee (aucun superviseur vivant) -- purge avant demarrage" >&2
  rm -f "$COURSIA_RUNNER_STATE_DIR/stop"
fi
# ---------------------------------------------------------------------------

exec "$SUPERVISE" "$@"
