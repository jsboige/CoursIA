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
# Contrat roo-extensions : lire le PREMIER MOT et le code, puis garder le
# verdict le plus strict selon BILLED > UNKNOWN > UNBILLED. Une contradiction
# ne doit jamais affaiblir BILLED ; un appel sans mot lisible vaut UNKNOWN.
# Le lecteur jumeau Windows `link-verdict.ps1` applique la meme regle.
#
# Le contrat est APPELE, jamais modifie : rien n'est ecrit cote roo-extensions.
#
# Variables d'environnement :
#   ROO_EXTENSIONS_ROOT        racine Windows du depot roo-extensions
#   ROO_EXTENSIONS_PATH        repli compatible RSM si ROOT absent
#   COURSIA_LINK_BILLED_SCRIPT surcharge directe du chemin vers la sonde
#   COURSIA_LINK_VERDICT_CMD   commande de sonde (surcharge reservee aux tests)
#   WSL_INTEROP               doit etre present pour appeler powershell.exe
#                                 depuis WSL ; son absence produit UNKNOWN
#
# Aucune racine connue ou sonde absente = UNKNOWN (fail-closed). Aucun chemin
# de siege n'est embarque en valeur par defaut.
set -uo pipefail

# La commande injectable n'existe que pour les temoins secs. En production,
# construire le chemin de sonde depuis une racine explicitement fournie.
if [ -n "${COURSIA_LINK_VERDICT_CMD:-}" ]; then
  commande="$COURSIA_LINK_VERDICT_CMD"
  contrat_affiche="test-stub"
else
  if [ -n "${COURSIA_LINK_BILLED_SCRIPT:-}" ]; then
    CONTRAT_WIN="$COURSIA_LINK_BILLED_SCRIPT"
  else
    ROO_ROOT="${ROO_EXTENSIONS_ROOT:-${ROO_EXTENSIONS_PATH:-}}"
    if [ -z "$ROO_ROOT" ]; then
      echo "UNKNOWN reason=probe-dir-missing variable=ROO_EXTENSIONS_ROOT" >&2
      exit 4
    fi
    # Convertir /mnt/<drive>/... en chemin Windows DOS, forme acceptée par -File.
    case "$ROO_ROOT" in
      /mnt/[a-zA-Z]/*)
        drive="$(printf '%s' "$ROO_ROOT" | cut -c6 | tr '[:lower:]' '[:upper:]')"
        rest="$(printf '%s' "$ROO_ROOT" | cut -c8- | tr '/' '\\\\')"
        ROO_ROOT_WIN="${drive}:\\\\${rest}"
        ;;
      *) ROO_ROOT_WIN="$ROO_ROOT" ;;
    esac
    CONTRAT_WIN="${ROO_ROOT_WIN%\\\\}\\\\scripts\\\\monitoring\\\\test-link-billed.ps1"
  fi
  contrat_affiche="$CONTRAT_WIN"
  if [ -z "${WSL_INTEROP:-}" ]; then
    echo "UNKNOWN reason=no-interop contract=$CONTRAT_WIN" >&2
    exit 4
  fi
  if ! command -v powershell.exe >/dev/null 2>&1; then
    echo "UNKNOWN reason=powershell-5.1-missing contract=$CONTRAT_WIN" >&2
    exit 4
  fi
  commande="powershell.exe -NoProfile -ExecutionPolicy Bypass -File '$CONTRAT_WIN'"
fi

# stdout ET stderr sont conserves pour détecter l'erreur de -File absent. Le
# contrat affiche alors une erreur localisée avant sa bannière ; certaines
# versions rendent rc=0 malgré cet échec, donc l'appel reste UNKNOWN.
sortie="$(bash -c "$commande" 2>&1)"
code=$?
# PowerShell localise le diagnostic d'un fichier -File absent. Rejeter les
# messages d'invocation avant de chercher le premier mot ; rc peut être 0.
if printf '%s' "$sortie" | grep -Eiq '(-File.*(n.existe|does not exist|not exist)|argument.*(-File|paramètre)|cannot find.*(path|file))'; then
  echo "UNKNOWN reason=contract-script-missing contract=$contrat_affiche" >&2
  exit 4
fi
case "$code" in 0|3|4) ;; *) code=4 ;; esac

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

# Lire le premier mot non vide de stdout/stderr. Si aucun mot de verdict n'est
# lisible (banniere, exception, sortie vide), classer UNKNOWN.
mot="$(printf '%s\n' "$sortie" | awk 'NF {print toupper($1); exit}')"
ligne="$(printf '%s\n' "$sortie" | awk 'NF {print; exit}')"
[ -n "$mot" ] || { echo "UNKNOWN reason=no-output contract=$contrat_affiche" >&2; exit 4; }
reste="$(printf '%s' "$ligne" | cut -d' ' -f2- | sed 's/^[[:space:]]*//')"
case "$mot" in
  UNBILLED|BILLED|UNKNOWN) ;;
  *) echo "UNKNOWN reason=unexpected-verdict word=$mot contract=$contrat_affiche" >&2; exit 4 ;;
esac

# Fold the two channels conservatively: the strictest evidence wins. A higher
# return code can never downgrade BILLED; a recognized word can never be
# overridden by an apparently more permissive code.
case "$mot:$code" in
  BILLED:0|BILLED:3|BILLED:4) verdict=BILLED ;;
  UNKNOWN:0|UNKNOWN:3|UNKNOWN:4) verdict=UNKNOWN ;;
  UNBILLED:0) verdict=UNBILLED ;;
  UNBILLED:3) verdict=BILLED ;;
  UNBILLED:4) verdict=UNKNOWN ;;
  *) verdict=UNKNOWN ;;
esac
[ -n "$reste" ] || reste="reason=contract-output"
echo "$verdict $reste"
case "$verdict" in
  UNBILLED) exit 0 ;;
  BILLED) exit 3 ;;
  *) exit 4 ;;
esac
