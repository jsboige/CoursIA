#!/usr/bin/env bash
# VEILLE DE LIEN -- re-verification periodique du verdict pendant que le runner
# tourne (issue #28916).
#
# LE DEFAULT MESURE (po-2027, 27/11 18:02Z) : le verdict n'etait rendu qu'AU
# DEMARRAGE. Le pont avait pris sa branche LAUNCH deux fois a 17:06:53Z, 86 s
# apres le boot ; le meme test du lien rendait BILLED a 17:46Z puis a 17:59Z,
# mais personne ne le relancait une fois le runner demarre. Un SKIP empeche un
# LANCEMENT, il n'arrete pas un runner deja en marche : d'ou les ~45 min de
# fuite et 3,6 Go consommes (debit hote 52,23 MiB/min).
#
# Ce que fait cette veille : elle RELIT le verdict periodiquement, et sur un
# verdict BILLED elle ARRETE reellement l'unite et sa slice. Pas de `mask` :
# le geste demande par l'issue est un arret, pas un desarmement durable --
# `systemctl disable` de toute facon ne bloque pas le holder (il lance
# lui-meme le service, cf hold-runner.ps1:33 et :40).
#
# UNKNOWN PENDANT LA MARCHE : on continue. Le contrat publie laisse ce choix
# a l'appelant ; ici l'appelant est un runner deja en marche, dont l'arret
# stopperait la file CI pour une sonde muette. La porte de LANCEMENT (elle)
# refuse, elle, en fail-closed. Le contraste est delibere : on refuse de
# DEMARRER sur une sonde muette, on ne stoppe pas un travail deja engage sur
# une sonde muette -- et le journal le dit, a chaque tour.
#
# Variables d'environnement :
#   LINK_WATCH_INTERVAL  secondes entre deux lectures (defaut 60)
#   LINK_WATCH_MAX       nombre maximum de tours (defaut 0 = illimite)
#   LINK_WATCH_UNIT      unite a arreter (defaut coursia-runner.service)
#   LINK_WATCH_SLICE     slice a arreter (defaut coursia-ci.slice)
#   LINK_WATCH_DRYRUN    1 = ne rien arreter, afficher les commandes
#   LINK_WATCH_VERDICT_CMD  commande de lecture du verdict (defaut :
#                           link-verdict.sh, a cote de ce fichier)
set -uo pipefail

ICI="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LECTEUR="${LINK_WATCH_VERDICT_CMD:-bash '$ICI/link-verdict.sh'}"
INTERVALLE="${LINK_WATCH_INTERVAL:-60}"
MAX_TOURS="${LINK_WATCH_MAX:-0}"
UNITE="${LINK_WATCH_UNIT:-coursia-runner.service}"
SLICE="${LINK_WATCH_SLICE:-coursia-ci.slice}"
SECHER="${LINK_WATCH_DRYRUN:-0}"

journal() { printf '%s %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*"; }

# L'arret passe par `--no-block` : la veille est un enfant de l'unite qu'elle
# arrete ; une commande bloquante attendrait la fin de l'unite, donc la sienne
# propre -- arret impossible depuis l'interieur. `--no-block` fait JUSTE ce
# qu'il faut : la demande est deposee, puis le client rend la main.
arreter() {
  journal "link-watch: verdict BILLED -- arret de $UNITE et $SLICE (sans mask)"
  if [ "$SECHER" = "1" ]; then
    echo "DRYRUN systemctl --no-block stop $UNITE"
    echo "DRYRUN systemctl --no-block stop $SLICE"
    return 0
  fi
  systemctl --no-block stop "$UNITE" 2>/dev/null || true
  systemctl --no-block stop "$SLICE" 2>/dev/null || true
  return 0
}

tour=0
while :; do
  tour=$((tour + 1))
  sortie="$(bash -c "$LECTEUR" 2>&1)"
  code=$?
  mot="$(printf '%s' "$sortie" | awk '{print $1}' | tr '[:lower:]' '[:upper:]')"
  reste="$(printf '%s' "$sortie" | cut -d' ' -f2- | sed 's/^[[:space:]]*//')"

  case "$code" in
    0)
      journal "link-watch: tour $tour -- UNBILLED ${reste}"
      ;;
    3)
      journal "link-watch: tour $tour -- BILLED ${reste}"
      arreter
      exit 0
      ;;
    *)
      journal "link-watch: tour $tour -- UNKNOWN ${reste} (le runner continue ; la porte de lancement, elle, refuse)"
      ;;
  esac

  if [ "$MAX_TOURS" -gt 0 ] && [ "$tour" -ge "$MAX_TOURS" ]; then
    journal "link-watch: tour $tour -- borne atteinte, fin de veille"
    exit 0
  fi
  sleep "$INTERVALLE"
done
