#!/usr/bin/env bash
# Lecteur du verdict de lien facture -- cote WSL (le runner Linux vit dans la
# distro, le contrat publie est un script PowerShell cote hote Windows).
#
# Issue #28916, mesure po-2027 du 27/11 18:02Z : sur un lien facture (partage
# USB du telephone), les runners CI ont tourne ~45 min et consomme 3,6 Go.
# Trois defauts mesures :
#   1. le verdict n'etait rendu qu'AU DEMARRAGE -- jamais reconsulte pendant
#      que le runner tournait ;
#   2. le holder contournait `systemctl disable` en lanconant lui-meme
#      `systemctl start coursia-runner` (hold-runner.ps1:33 et :40) ;
#   3. un verdict BILLED n'arretait rien : un SKIP empeche un lancement, il ne
#      stoppe pas un runner deja en marche.
#
# CE FICHIER EST LE LECTEUR, PAS LE JUGE. Il rend le PREMIER MOT de la ligne
# imprimee par le contrat publie, et un code de sortie qui l'encode :
#
#     UNBILLED   exit 0   le lien n'est pas facture -- travail lourd licite
#     BILLED     exit 3   le lien est facture -- ne pas lancer de travail lourd
#     UNKNOWN    exit 4   la sonde n'a pas repondu -- l'appelant tranche
#
# Le contrat publie (roo-extensions) dit : « "exit 0" alone is not enough to
# mean "go": read the first word ». La regle est donc appliquee a l'envers :
# c'est le PREMIER MOT qui fait foi, et le code de sortie du contrat sert de
# CONTRE-VERIFICATION. Mot inattendu ou desaccord entre mot et code de sortie
# => UNKNOWN, jamais un « va » suppose. Le cote Windows a le lecteur jumeau
# `link-verdict.ps1` ; les deux appliquent la MEME regle.
#
# Le contrat est APPELLE, jamais modifie : rien n'est ecrit cote roo-extensions.
#
# Variables d'environnement :
#   COURSIA_LINK_BILLED_SCRIPT   chemin Windows du contrat publie
#                                 (defaut D:\roo-extensions\scripts\monitoring\test-link-billed.ps1)
#   COURSIA_LINK_VERDICT_CMD      commande produisant la ligne de verdict
#                                 (surcharge totale ; utilisee par le harnais
#                                 et par un siege qui a sa propre sonde)
set -uo pipefail

CONTRAT_WIN="${COURSIA_LINK_BILLED_SCRIPT:-D:\\roo-extensions\\scripts\\monitoring\\test-link-billed.ps1}"

# La commande qui produit la ligne de verdict.
if [ -n "${COURSIA_LINK_VERDICT_CMD:-}" ]; then
  commande="$COURSIA_LINK_VERDICT_CMD"
elif command -v powershell.exe >/dev/null 2>&1; then
  # Interop WSL : le contrat est un script PowerShell cote hote.
  commande="powershell.exe -NoProfile -ExecutionPolicy Bypass -File '$CONTRAT_WIN'"
else
  # Pas d'interop : aucune lecture possible. C'est UNKNOWN, pas UNBILLED.
  echo "UNKNOWN reason=no-interop contract=$CONTRAT_WIN" >&2
  exit 4
fi

sortie="$(bash -c "$commande" 2>/dev/null)"
code=$?

ligne=""
while IFS= read -r l; do
  [ -n "$(printf '%s' "$l" | tr -d '[:space:]')" ] || continue
  ligne="$l"
  break
done <<<"$sortie"

if [ -z "$ligne" ]; then
  echo "UNKNOWN reason=no-output command=$commande" >&2
  exit 4
fi

# Le PREMIER MOT de la ligne fait foi.
mot="$(printf '%s' "$ligne" | awk '{print $1}' | tr '[:lower:]' '[:upper:]')"
reste="$(printf '%s' "$ligne" | cut -d' ' -f2- | sed 's/^[[:space:]]*//')"

case "$mot" in
  UNBILLED|BILLED|UNKNOWN) ;;
  *)
    echo "UNKNOWN reason=unexpected-verdict word=$mot line=$ligne" >&2
    exit 4
    ;;
esac

# Contre-verification : le mot et le code de sortie du contrat doivent dire la
# meme chose. Un desaccord est un etat degrade, pas un feu vert.
attendu=4
case "$mot" in
  UNBILLED) attendu=0 ;;
  BILLED) attendu=3 ;;
esac
if [ "$code" -ne "$attendu" ]; then
  echo "UNKNOWN reason=verdict-exit-mismatch word=$mot contract_exit=$code" >&2
  exit 4
fi

echo "$mot $reste"
case "$mot" in
  UNBILLED) exit 0 ;;
  BILLED) exit 3 ;;
esac
exit 4
