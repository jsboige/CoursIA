#!/usr/bin/env bash
# Lanceur du superviseur de runners Linux -- version ai-01 (systemd/Ubuntu WSL2).
# Copie de REFERENCE : l'original vit dans la distro Ubuntu de l'hote, sous
# /usr/local/bin/coursia-runner-start.sh.
#
# CE QUI DISTINGUE CETTE COPIE DE persist/coursia-runner-start.sh
# ---------------------------------------------------------------
# La copie a la racine de persist/ est celle de po-2024 : depot sous
# /mnt/c/dev/CoursIA, prefixe myia-po-2024-linux-docker, et surtout un
# `exec "$SUPERVISE" "$@"` qui relaie n'importe quelle sous-commande. Celle-ci
# vit sur ai-01 : depot sous /mnt/d/CoursIA, prefixe myia-ai-01-wsl, et le
# premier argument est le NOMBRE DE SLOTS, pas une sous-commande.
#
# Les deux ne sont pas interchangeables, et c'est ce qui a fait qu'un correctif
# porte sur la copie po-2024 (#15094) ne changeait rien a ce qui tourne ici.
# persist/README.md dresse la table de correspondance ; ce commentaire existe
# pour que la question se pose meme sans lire le README.
#
# LE DEFAUT QUE CETTE VERSION CORRIGE (#15091)
# --------------------------------------------
# La version deployee ne connaissait que le demarrage. L'unite routait donc son
# ExecStop directement vers supervise.sh, SANS COURSIA_RUNNER_STATE_DIR --
# lequel retombe alors sur $HOME/.coursia-runner. Or supervise.sh fait lui-meme
# `mkdir -p "$STATE_DIR"` : l'arret CREAIT /root/.coursia-runner/, y posait le
# sentinel, et rendait rc=0. Mesure ai-01 du 2026-09-07 : le repertoire
# n'existait pas avant la sonde, il existait apres, et le superviseur -- qui
# surveille /var/lib/coursia-runner/stop -- n'a jamais rien vu.
#
# L'arret gracieux etait donc inerte depuis son deploiement, en annoncant le
# succes. `systemctl stop` retombait sur le SIGTERM de KillMode=mixed, c'est-a-dire
# exactement ce que le sentinel existe pour eviter : un job en vol tue net, qui
# rend un rouge ne voulant rien dire.
#
# La reparation est la branche `stop` ci-dessous : l'arret repasse par le
# wrapper, donc par le meme STATE_DIR que le demarrage. C'est la forme qu'a
# deja coursia-waiters-start.sh, et la raison pour laquelle la jambe waiters,
# elle, s'arrete proprement.
#
# LE SECRET NE SE DUPLIQUE PAS. GH_RUNNERS_ADMIN_TOKEN est relu dans master.env
# a chaque demarrage plutot que recopie dans un EnvironmentFile : une seconde
# copie serait une seconde chose a rotater et a proteger. `gh auth token` est
# inutilisable ici -- le trousseau gh est attache a la session utilisateur, que
# precisement ce service n'a plus.
set -uo pipefail

MASTER_ENV="${COURSIA_MASTER_ENV:-/mnt/d/CoursIA/.secrets/master.env}"
REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/CoursIA}"
ARG="${1:-8}"

[ -r "$MASTER_ENV" ] || { echo "master.env illisible : $MASTER_ENV" >&2; exit 1; }

# Extraction ciblee : on ne source PAS le fichier entier (des dizaines de
# secrets sans rapport n'ont rien a faire dans l'environnement d'un runner).
GH_TOKEN="$(sed -n 's/^GH_RUNNERS_ADMIN_TOKEN=//p' "$MASTER_ENV" | head -1 | tr -d '"'"'"'\r')"
[ -n "$GH_TOKEN" ] || { echo "GH_RUNNERS_ADMIN_TOKEN absent de master.env -- abandon" >&2; exit 1; }
export GH_TOKEN

# Daemon EPINGLE. Sans cela, si l'integration WSL de Docker Desktop est activee
# sur Ubuntu, elle remplace /var/run/docker.sock par le socket de SON daemon :
# les conteneurs runner repartiraient sur Docker Desktop -- donc a nouveau
# attaches a la session utilisateur, ce que cette installation existe
# precisement pour supprimer. L'echec serait muet.
#
# L'epinglage porte aussi la resolution du device d'I/O : les deux daemons de
# la machine annoncent le MEME DockerRootDir, et c'est le socket qui decide
# lequel repond a `docker info`.
export DOCKER_HOST="${DOCKER_HOST:-unix:///var/run/docker-ce.sock}"

export COURSIA_RUNNER_NAME_PREFIX="${COURSIA_RUNNER_NAME_PREFIX:-myia-ai-01-wsl}"
export COURSIA_RUNNER_STATE_DIR="${COURSIA_RUNNER_STATE_DIR:-/var/lib/coursia-runner}"

# --- Bornes #15091 ---------------------------------------------------------
# ai-01 ARME ce que supervise.sh laisse inerte par defaut. Le script ne suppose
# rien : ses defauts sont vides, po-2024 garde donc son comportement en tirant
# la meme version. C'est ici, sur la machine qui a gele deux fois, que les
# bornes sont declarees.
#
# 1. Budget agrege EXIGE. La slice est appliquee par defaut du daemon
#    (/etc/docker/daemon.json), pas par un drapeau ; le superviseur la VERIFIE
#    et refuse de demarrer si elle manque ou ne porte pas d'io.max. Un pool non
#    borne est exactement ce qui a gele la machine : un refus lisible vaut
#    mieux qu'un demarrage silencieux.
export COURSIA_RUNNER_CGROUP_PARENT="${COURSIA_RUNNER_CGROUP_PARENT:-coursia-ci.slice}"
export COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET="${COURSIA_RUNNER_REQUIRE_CGROUP_BUDGET:-1}"

# 2. Plafond PAR CONTENEUR : 40 Mio/s en ecriture, 80 Mio/s en lecture. Il ne
#    remplace pas le budget agrege (12 conteneurs conformes un a un saturent
#    quand meme le disque) -- il empeche UN slot d'emporter a lui seul la part
#    de toute la famille. Le device est resolu par `docker info` a travers le
#    socket epingle ci-dessus ; le nommer en dur ici masquerait un mauvais
#    epinglage.
export COURSIA_RUNNER_DEVICE_WRITE_BPS="${COURSIA_RUNNER_DEVICE_WRITE_BPS:-41943040}"
export COURSIA_RUNNER_DEVICE_READ_BPS="${COURSIA_RUNNER_DEVICE_READ_BPS:-83886080}"

# 3. Budget CPU inter-familles : 8 vCPU sur les 16 de la machine, la meme
#    moitie que CPUQuota=800% dans la slice. Les deux bornes disent la meme
#    chose a deux endroits differents -- la slice l'impose au kernel, ce budget
#    la fait REFUSER au demarrage, avec un message qui nomme les termes de la
#    somme. Sans lui, `waiters 12` puis `lean 2` sont conformes chacun et
#    demandent 24 coeurs ensemble.
export COURSIA_RUNNER_CPU_BUDGET="${COURSIA_RUNNER_CPU_BUDGET:-8}"

mkdir -p "$COURSIA_RUNNER_STATE_DIR"

cd "$REPO_DIR" || exit 1

# La branche `stop` : c'est elle qui rend l'arret gracieux reel (cf. en-tete).
if [ "$ARG" = "stop" ]; then
  exec ./scripts/ci/docker/linux-runner/supervise.sh stop
fi
exec ./scripts/ci/docker/linux-runner/supervise.sh start "$ARG"
