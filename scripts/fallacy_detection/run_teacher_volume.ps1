# Wrapper du run volume tranche B #17578 -- lane myia-po-2027:CoursIA
# Detache par schtasks (survit a la session). Reprenable : checkpoint append-par-paire.
# La cle VLLM_API_KEY_MEDIUM est lue de master.env (gitignore) et N'EST JAMAIS ecrite ni echoee.
#
# Version commitee (Maintenance#126, trou n4) : les chemins absolus de la copie
# de travail deviennent des parametres ; la tache planifiee locale
# `CoursIA-po2027-teacher-volume` peut appeler ce fichier avec -MasterEnvPath
# pointant sur le .secrets du clone principal (un worktree ne porte pas .secrets).
#
# Historique des corrections (mesure du 2026-10-10) :
#  * L'etape `--split val` a ete RETIREE. val_fr etait deja complet (1629/1629) :
#    la passe ne generait rien mais reecrivait `report_val_fr.json` a chaque run,
#    donc churnait un fichier du scope revendique par `myia-po-2023:CoursIA`
#    (`.../data/teacher/**`) sans rien produire. Le scope de cette lane est
#    `test_fr.jsonl` + `report_test_fr.json`.
#  * Un PRE-FLIGHT a ete ajoute. Sans lui, un hub injoignable faisait bruler le
#    budget de retries (~70 s) et rendre un rc=1 indiscernable d'un defaut de
#    donnees -- 4 relances ont ete perdues ainsi.

param(
    [string]$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..')).Path,
    [string]$MasterEnvPath = '',
    [string]$VenvScripts = '',
    [string]$LogPath = '',
    [string]$HubHost = '192.168.0.47',
    [int]$HubPort = 5002,
    [string]$Split = 'test',
    [string]$Lang = 'fr',
    [int]$Limit = 0
)

if (-not $MasterEnvPath) { $MasterEnvPath = Join-Path $RepoRoot '.secrets\master.env' }
if (-not $VenvScripts)   { $VenvScripts = Join-Path $RepoRoot 'venv\Scripts' }
if (-not $LogPath)       { $LogPath = Join-Path $RepoRoot '.tmp\teacher_volume.log' }

$ErrorActionPreference = 'Continue'

$kv = @{}
Get-Content $MasterEnvPath -ErrorAction SilentlyContinue | ForEach-Object {
    if ($_ -match '^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*?)\s*$') { $kv[$Matches[1]] = $Matches[2] }
}
if (-not $kv['VLLM_API_KEY_MEDIUM']) {
    Add-Content $LogPath "[$(Get-Date -Format o)] FATAL: VLLM_API_KEY_MEDIUM absente de $MasterEnvPath"
    exit 1
}
$env:VLLM_API_KEY_MEDIUM = $kv['VLLM_API_KEY_MEDIUM']

# --- Pre-flight : le hub vit sur le LAN MyIA, cette machine est un portable. ---
$probe = New-Object System.Net.Sockets.TcpClient
try {
    $reachable = $probe.ConnectAsync($HubHost, $HubPort).Wait(5000)
} catch {
    $reachable = $false
} finally {
    $probe.Close()
}
if (-not $reachable) {
    $ipv4 = (Get-NetIPAddress -AddressFamily IPv4 |
             Where-Object { $_.IPAddress -notlike '127.*' -and $_.IPAddress -notlike '169.254.*' } |
             ForEach-Object { "$($_.IPAddress)/$($_.PrefixLength) [$($_.InterfaceAlias)]" }) -join ', '
    Add-Content $LogPath "[$(Get-Date -Format o)] FATAL: hub ${HubHost}:${HubPort} INJOIGNABLE -- generation NON lancee, aucun checkpoint touche."
    Add-Content $LogPath "[$(Get-Date -Format o)]   IPv4 actives : $ipv4"
    Add-Content $LogPath "[$(Get-Date -Format o)]   Attendu : une interface dans 192.168.0.x (LAN MyIA). Voir docs/reference/cluster-agents.md, regle de routage."
    exit 2
}
Add-Content $LogPath "[$(Get-Date -Format o)] pre-flight OK : hub ${HubHost}:${HubPort} joignable"

$env:PATH = "$VenvScripts;$env:PATH"
Set-Location (Join-Path $RepoRoot 'scripts')

Add-Content $LogPath "[$(Get-Date -Format o)] === ${Split}_${Lang} start (reprise depuis checkpoint) ==="
python -m fallacy_detection.generate_teacher_corpus --split $Split --lang $Lang --limit $Limit *>> $LogPath
Add-Content $LogPath "[$(Get-Date -Format o)] === ${Split}_${Lang} rc=$LASTEXITCODE === DONE ==="
