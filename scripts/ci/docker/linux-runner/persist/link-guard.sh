#!/usr/bin/env bash
# PORTE DE LANCEMENT -- garde de lien facture (issue #28916).
#
# Ce que ce fichier EST : la porte qui sepose AVANT un demarrage de runner.
# Elle lit le verdict (link-verdict.sh, qui appelle le contrat publie cote
# roo-extensions) et rend UNE decision :
#
#     UNBILLED  -> GO      (code de sortie 0)
#     BILLED    -> REFUSE  (code de sortie 4)
#     UNKNOWN   -> REFUSE  (code de sortie 4)   <-- fail-closed
#
# Pourquoi UNKNOWN refuse ici : le contrat publie dit que la sonde doit avoir
# TROIS issues, et que « the caller decides ». Un appelant qui DOIT proteger
# un budget tranche « UNKNOWN = facture » ; un appelant qui doit faire
# avancer une file tranche « UNKNOWN = non facture ». Cette porte protege un
# budget : elle refuse. Le defaut mesure (#28916) est justement un lien
# facture non vu -- on ne rejoue pas l'a priori.
#
# Pourquoi la porte vit dans un fichier separe : elle doit etre REJOUABLE
# seule (test_link_verdict_guard.sh), et lisible sans le superviseur. Le
# superviseur ne decide rien : il appelle la porte, et il obeyit.
#
# Variables d'environnement :
#   LINK_GUARD_VERDICT_CMD  commande de lecture du verdict (defaut : le
#                           lecteur jumeau link-verdict.sh, a cote de ce fichier)
set -uo pipefail

ICI="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LECTEUR="${LINK_GUARD_VERDICT_CMD:-bash '$ICI/link-verdict.sh'}"

sortie="$(bash -c "$LECTEUR" 2>&1)"
code=$?

# Le code du lecteur EST la decision (0 UNBILLED, 3 BILLED, 4 UNKNOWN) ; le
# mot de la ligne ne sert qu'a nommer la cause dans le journal.
mot="$(printf '%s' "$sortie" | awk '{print $1}' | tr '[:lower:]' '[:upper:]')"
reste="$(printf '%s' "$sortie" | cut -d' ' -f2- | sed 's/^[[:space:]]*//')"

case "$code" in
  0)
    echo "GO link-unbilled ${reste}"
    exit 0
    ;;
  3)
    echo "REFUSE link-billed ${reste}" >&2
    exit 4
    ;;
  *)
    echo "REFUSE link-verdict-unknown ${reste}" >&2
    exit 4
    ;;
esac
