# Holder WSL pour coursia-runner -- copie de reference genrique.
# Deploiement po-2024 (2026-09-02) : l'original vit sur l'hote sous
# %USERPROFILE%\.coursia-runner\hold-myia-po-2024.ps1 (noms hardcodes).
#
# RAISON D'ETRE (mesure 2026-09-02, decisive) : un appel wsl.exe one-shot ne
# maintient PAS la distro. WSL REAPE la distro quand le dernier client sort,
# MEME avec systemd en PID 1, le service actif et les slots online :
#   4/4 online -> exit du client -> < 3 min : distro morte
#   (wsl -l --running : Ubuntu absente, GitHub online: 0).
# Consequence : tout reveil doit etre TENU par une session client ouverte
# indefiniment. Ce script spawn un processus wsl.exe DETACHE qui demarre le
# service puis dort -- la distro ne meurt plus tant que le holder vit.
# C'est aussi la cause racine des echecs de reveil one-shot (pont logon,
# tache S4U "rc=0 sans rien demarrer") : le rc=0 dit seulement que la
# demande a ete acceptee, pas que la distro a survécu au client.
#
# Parametres : DISTRO (defaut Ubuntu), SERVICE (defaut coursia-runner.service).
param(
    [string]$Distro = 'Ubuntu',
    [string]$Service = 'coursia-runner.service'
)
$ErrorActionPreference = 'Stop'
# Journal et executable wsl sont surchargeables : le harnais
# (test_link_verdict_guard.sh) doit pouvoir rejouer le holder sans ecrire
# dans le journal du siege ni lancer wsl.exe pour de vrai.
$log = if ($env:COURSIA_HOLDER_LOG) { $env:COURSIA_HOLDER_LOG } else { "$env:USERPROFILE\.coursia-runner\holder.log" }
function Log($msg) { "$(Get-Date -Format o) $msg" | Add-Content -Encoding utf8 $log }

$wsl = if ($env:COURSIA_WSL_EXE) { $env:COURSIA_WSL_EXE } else { "$env:WINDIR\System32\wsl.exe" }

# --- GARDE DE LIEN FACTURE (#28916) -----------------------------------------
# CE QUE LE HOLDER FAISAIT (defaut mesure, po-2027, 27/11 18:02Z). Ce script
# lance LUI-MEME le service, a deux endroits : le one-shot ligne 33 (holder deja
# vivant) et le spawn ligne 40 (holder neuf). `systemctl disable` ne bloque donc
# NI l'un NI l'autre : desarmer l'unite ne suffit pas, seul le VERDICT du lien
# bloque. Sur un lien facture (partage USB du telephone), les runners CI ont
# tourne environ 45 min et consomme 3,6 Go.
#
# Le verdict vient du contrat publie par roo-extensions
# (test-link-billed.ps1), lu par le lecteur jumeau link-verdict.ps1 (meme
# dossier que ce script, ou surcharge par COURSIA_LINK_VERDICT_PS1). Sa
# premiere ligne porte le verdict, son code de sortie l'encode :
#   UNBILLED exit 0 (on lance) · BILLED exit 3 (on refuse) · UNKNOWN exit 4
# (on refuse). UNKNOWN refuse ici : le contrat laisse ce choix a l'appelant,
# et l'appelant protege un budget. RIEN n'est modifie cote roo-extensions.
function Get-LinkVerdict {
    $reader = $env:COURSIA_LINK_VERDICT_PS1
    if (-not $reader) { $reader = Join-Path $PSScriptRoot 'link-verdict.ps1' }
    if (-not (Test-Path -LiteralPath $reader)) {
        Log "GARDE lien: lecteur de verdict introuvable ($reader) -- demarrage refuse (fail-closed)"
        return 'UNKNOWN'
    }
    try {
        $sortie = & $reader 2>&1 | Out-String
    } catch {
        Log "GARDE lien: lecture du verdict impossible ($($_.Exception.Message)) -- demarrage refuse (fail-closed)"
        return 'UNKNOWN'
    }
    $ligne = ''
    foreach ($l in ($sortie -split "`r?`n")) {
        if ($l.Trim().Length -gt 0) { $ligne = $l.Trim(); break }
    }
    if (-not $ligne) {
        Log "GARDE lien: le verdict n'a rien rendu -- demarrage refuse (fail-closed)"
        return 'UNKNOWN'
    }
    return ($ligne -split '\s+')[0].ToUpperInvariant()
}

$verdict = Get-LinkVerdict
if ($verdict -ne 'UNBILLED') {
    Log "GARDE lien: verdict $verdict -- systemctl start NON lance (le service reste a l'arret)"
    if ($verdict -eq 'BILLED') { exit 3 }
    exit 4
}
Log "GARDE lien: verdict UNBILLED -- demarrage autorise"

# Garde anti-doublon : re-invoquer la tache ne doit pas empiler les holders.
$existing = Get-CimInstance Win32_Process -Filter "Name='wsl.exe'" |
    Where-Object { $_.CommandLine -match 'sleep infinity' -and $_.CommandLine -match $Distro }
if ($existing) {
    Log "holder deja vivant pid=$($existing.ProcessId) - start one-shot du service seulement"
    & $wsl -d $Distro -u root -- /bin/systemctl start $Service
    Log "systemctl start (one-shot) rc=$LASTEXITCODE"
    exit $LASTEXITCODE
}

$p = Start-Process -WindowStyle Hidden -PassThru -FilePath $wsl -ArgumentList @(
    '-d', $Distro, '-u', 'root', '--', '/bin/bash', '-c',
    "systemctl start $Service && exec sleep infinity"
)
Log "holder spawn pid=$($p.Id) (systemd start + sleep infinity) [distro=$Distro]"
Start-Sleep -Seconds 3
if ($p.HasExited) {
    Log "ERREUR: holder pid=$($p.Id) mort prematurément (exit=$($p.ExitCode))"
    exit 1
}
Log "holder pid=$($p.Id) vivant a t+3s"
exit 0
