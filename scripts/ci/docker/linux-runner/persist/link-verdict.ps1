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
# Le contrat publie dit de lire le premier mot ET le code de sortie, en gardant
# le verdict le plus strict : BILLED > UNKNOWN > UNBILLED. Une contradiction ne
# peut jamais affaiblir BILLED ; un mot absent ou illisible devient UNKNOWN.
# La commande de service appelle toujours Windows PowerShell 5.1.
#
# RIEN N'EST MODIFIE COTE ROO-EXTENSIONS : ce fichier appelle le contrat
# publie, il ne le reecrit pas et ne l'ecrit pas.
#
# Utilisation :
#     powershell -NoProfile -ExecutionPolicy Bypass -File link-verdict.ps1
#     powershell -NoProfile -ExecutionPolicy Bypass -File link-verdict.ps1 -Script <chemin>
#
# Variables d'environnement reconnues :
#     COURSIA_LINK_BILLED_SCRIPT  chemin du contrat publie (override direct)
#     ROO_EXTENSIONS_ROOT        racine du depot (prioritaire)
#     ROO_EXTENSIONS_PATH        repli compatible RSM
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

# Localiser la sonde : override direct de test, sinon racine explicitement
# injectee par l'environnement du runner. Pas de chemin propre a un siege.
if (-not $Script) {
    $root = $env:ROO_EXTENSIONS_ROOT
    if (-not $root) { $root = $env:ROO_EXTENSIONS_PATH }
    if (-not $root) { Verdict 'UNKNOWN' 'reason=probe-dir-missing variable=ROO_EXTENSIONS_ROOT' }
    $Script = Join-Path $root 'scripts/monitoring/test-link-billed.ps1'
}

if (-not (Test-Path -LiteralPath $Script)) {
    Verdict 'UNKNOWN' ("reason=contract-script-missing path=" + $Script)
}

# Appel du contrat : son premier mot de verdict + code. Les erreurs stderr
# (dont les bannieres localisees de powershell.exe) ne sont pas des verdicts.
$stdout = @(& $Script)
$code = $LASTEXITCODE
$ligne = ''
foreach ($l in $stdout) {
    $candidate = [string]$l
    if ($candidate.Trim().Length -gt 0 -and $candidate.Trim() -match '^(UNBILLED|BILLED|UNKNOWN)(\s|$)') {
        $ligne = $candidate.Trim()
        break
    }
}
if (-not $ligne) {
    Verdict 'UNKNOWN' ("reason=no-output path=" + $Script)
}

$mot = ($ligne -split '\s+')[0].ToUpperInvariant()
$reste = $ligne.Substring($ligne.IndexOf($mot)).Trim()

if ($mot -notin @('UNBILLED', 'BILLED', 'UNKNOWN')) {
    Verdict 'UNKNOWN' ("reason=unexpected-verdict word=" + $mot + " line=" + $ligne)
}

# Les deux canaux peuvent diverger : garder le plus strict. Codes connus 0/3/4 ;
# tout autre code est UNKNOWN, sauf si le mot dit BILLED, qui reste BILLED.
$verdict = $mot
switch ($code) {
    0 { }
    3 { if ($verdict -eq 'UNBILLED') { $verdict = 'BILLED' } }
    4 { if ($verdict -ne 'BILLED') { $verdict = 'UNKNOWN' } }
    default { if ($verdict -ne 'BILLED') { $verdict = 'UNKNOWN' } }
}
Verdict $verdict $reste
