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
# 21 POUR po-2024 (2026-10-12, arbitrage c2153 d'ai-01) -- la composition
# persist n'avait pas ete comptee depuis le J+7. Historique complet : le 42
# du 2026-09-21 (VM de 40 110 Mo) etait devenu faux deux fois (VM revenuee a
# 24 Go ; arithmetique comptant « 12x1536 waiters » pour des waiters a
# 512 Mo) ; le J+7 du 2026-10-08 a pose 15 pour la composition
# 4x1536 + 6x512 + 1x6144 = 15 360 Mo. Puis #20174 (2026-10-10) a reetiquete
# 4 slots persist -- la famille docker est revenuee a 8 slots de 1536 Mo SANS
# que le budget suive : la somme des caps vivants (21 504 Mo) depassait le
# budget declare (15 360), et assert_memory_budget refusait de DEMARRER tout
# nouveau slot. C'est la famine CI constatee au cycle du 2026-10-12 : le
# garde ne jugeait plus la composition, il la bloquait.
#
# LA COMPOSITION QUE CE BUDGET DECLARE, ET CE QU'ELLE LAISSE :
#     8 slots docker x 1536 Mo = 12 288 Mo  (4 docker + 4 persist, #20174)
#     6 waiters      x  512 Mo =  3 072 Mo  (cap unitaire INCHANGE)
#     1 slot lean    x 6144 Mo =  6 144 Mo  (2 -> 1, verdict J+7)
#     --------------------------------------
#     total CAPS                21 504 Mo   sur 24 032 -> marge 2 528 Mo
#
# La regle de #19802 tranche la valeur : LE BUDGET EST LA SOMME DES CAPS de
# la composition vive. 21 504 Mo = 21 Go, deja valide par #19802 sur cette VM
# de 24 Go (marge 2,5 Go, swap 0 -- la marge etroite est payee par le mur
# kernel MemorySwapMax=0, qui tue le job debordant au lieu de swapper).
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
# slot au-dela de 21 Go ; il ne borne pas ce qu'un slot deja lance consomme.
# Le mur kernel est desormais pose sur cette machine : voir
# persist/po-2024/coursia-ci.slice (MemoryHigh=20G, MemoryMax=22G,
# MemorySwapMax=0 -- REMONTE en meme temps que ce budget, arbitrage c2153 : un
# mur 14G/16G sous une composition de 21 504 Mo de caps tuerait au kernel des
# jobs que le budget d'admission laisse partir), et COURSIA_RUNNER_CGROUP_PARENT
# plus bas, qui y fait entrer les conteneurs.
#
# LES TROIS JAMBES DOIVENT ANNONCER LE MEME NOMBRE. `assert_memory_budget`
# somme les conteneurs label `coursia-ci=1` de TOUTES les familles : deux jambes
# qui divergeraient refuseraient leurs slots l'une contre l'autre, et le message
# d'erreur ne nommerait pas la divergence -- il parlerait de memoire en vol.
# La divergence a existe de fait (mesure du 2026-10-12 : process docker/lean a
# 15 herite d'avant l'edition des wrappers, waiters a 21 redemarre a 04:06 --
# la composition a bouge sous des processus vivants). Les trois jambes de
# po-2024 portent 21 : celle-ci, la jambe lean, et la jambe waiters (par le
# drop-in persist/po-2024/coursia-waiters.service.d/10-sizing.conf, dont le
# wrapper appartient a ai-01 et ne declare aucun budget).
export COURSIA_RUNNER_BUDGET_GB=21

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
