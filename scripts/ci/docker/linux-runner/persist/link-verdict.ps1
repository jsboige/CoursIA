# Lecteur du verdict de lien facture -- cote hote Windows.
#
# POURQUOI CE FICHIER EXISTE (issue #28916, mesure po-2027 du 27/11 18:02Z).
# Le siege po-2027 etait sur un lien facture (partage USB du telephone) : les
# runners CI y ont tourne environ 45 min et consomme 3,6 Go (debit hote releve :
# 52,23 MiB/min, RX 2 859,4 MiB a 17:50:16Z puis 3 589,2 MiB a 17:56:31Z).
# Trois defauts distincts ont ete mesures :
#   1. le verdict n'etait rendu qu'AU DEMARRAGE (branche LAUNCH du pont prise
#      deux fois a 17:06:53Z, 86 s apres le boot) -- personne ne le relancait
#      une fois le runner en marche ;
#   2. le holder contournait `systemctl disable` : hold-runner.ps1 lance
#      lui-meme `systemctl start coursia-runner` (lignes 33 et 40) ;
#   3. un verdict BILLED n'arretait rien : un SKIP empeche un lancement, il ne
#      stoppe pas un runner deja en marche.
#
# CE FICHIER EST LE LECTEUR, PAS LE JUGE. Il rend UN SEUL mot -- le PREMIER
# mot de la ligne imprimee par le contrat publie
# (roo-extensions/scripts/monitoring/test-link-billed.ps1) -- et un code de
# sortie qui encode ce mot :
#
#     UNBILLED   exit 0   le lien n'est pas facture -- le travail lourd est licite
#     BILLED     exit 3   le lien est facture -- ne pas lancer de travail lourd
#     UNKNOWN    exit 4   la sonde n'a pas repondu -- l'appelant tranche
#
# « exit 0 alone is not enough to mean "go": read the first word » -- l'en-tete
# du contrat publie. On applique donc la regle a l'envers et de facon
# verifiable : c'est le PREMIER MOT qui fait foi, et le code de sortie du
# contrat sert de CONTRE-VERIFICATION. Un desaccord entre les deux (ou un mot
# inattendu) donne UNKNOWN -- fail-closed, jamais un « va » suppose.
#
# RIEN N'EST MODIFIE COTE ROO-EXTENSIONS : ce fichier appelle le contrat
# publie, il ne le reecrit pas et ne l'ecrit pas.
#
# Utilisation :
#     powershell -NoProfile -ExecutionPolicy Bypass -File link-verdict.ps1
#     powershell -NoProfile -ExecutionPolicy Bypass -File link-verdict.ps1 -Script <chemin>
#
# Variables d'environnement reconnues :
#     COURSIA_LINK_BILLED_SCRIPT  chemin du contrat publie (defaut ci-dessous)
param(
    [string]$Script = $env:COURSIA_LINK_BILLED_SCRIPT,
    [switch]$Quiet
)

$ErrorActionPreference = 'Continue'

function Verdict([string]$word, [string]$detail) {
    if (-not $Quiet) { Write-Output ("{0} {1}" -f $word, $detail) }
    switch ($word) {
        'UNBILLED' { exit 0 }
        'BILLED'   { exit 3 }
        default    { exit 4 }
    }
}

# Le contrat publie vit dans le depot roo-extensions. Son chemin par defaut
# est celui du siege type (D:\roo-extensions) ; un siege qui l'a ailleurs
# surcharge COURSIA_LINK_BILLED_SCRIPT ou -Script. Un chemin absent n'est pas
# un « lien non facture » : c'est UNKNOWN.
if (-not $Script) { $Script = 'D:\roo-extensions\scripts\monitoring\test-link-billed.ps1' }

if (-not (Test-Path -LiteralPath $Script)) {
    Verdict 'UNKNOWN' ("reason=contract-script-missing path=" + $Script)
}

# Appel du contrat : sa premiere ligne NON VIDE porte le verdict, son code de
# sortie le contre-verifie. On capture stdout ET stderr pour qu'une erreur
# d'invocation ne se fasse pas passer pour une reponse.
$sortie = & $Script 2>&1 | Out-String
$code = $LASTEXITCODE

$ligne = ''
foreach ($l in ($sortie -split "`r?`n")) {
    if ($l.Trim().Length -gt 0) { $ligne = $l.Trim(); break }
}
if (-not $ligne) {
    Verdict 'UNKNOWN' ("reason=no-output path=" + $Script)
}

$mot = ($ligne -split '\s+')[0].ToUpperInvariant()
$reste = $ligne.Substring($ligne.IndexOf($mot)).Trim()

if ($mot -notin @('UNBILLED', 'BILLED', 'UNKNOWN')) {
    Verdict 'UNKNOWN' ("reason=unexpected-verdict word=" + $mot + " line=" + $ligne)
}

# Contre-verification : le mot et le code du contrat doivent dire la meme
# chose. Un desaccord est un etat degrade, pas un feu vert.
$attendu = switch ($mot) { 'UNBILLED' { 0 } 'BILLED' { 3 } default { 4 } }
if ($code -ne $attendu) {
    Verdict 'UNKNOWN' ("reason=verdict-exit-mismatch word=" + $mot + " contract_exit=" + $code)
}

Verdict $mot $reste
