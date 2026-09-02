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
$log = "$env:USERPROFILE\.coursia-runner\holder.log"
function Log($msg) { "$(Get-Date -Format o) $msg" | Add-Content -Encoding utf8 $log }

$wsl = "$env:WINDIR\System32\wsl.exe"

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
