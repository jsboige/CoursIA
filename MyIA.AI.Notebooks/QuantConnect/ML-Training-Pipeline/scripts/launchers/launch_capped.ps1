<#
.SYNOPSIS
    Lance un entrainement CoursIA sous plafond memoire NATIF (Job Object Windows), exclusion N=1 et garde de charge de commit.

.DESCRIPTION
    Les entrainements CoursIA sur ai-01 ne sont pas des conteneurs : ce sont des
    processus Python natifs. Un plafond Docker `--memory` ne s'y applique pas.

    Ce lanceur passe par l'organe `scripts/ci/run_guarded.py`, qui pose sur le
    processus d'entrainement ET ses enfants :

      - un Job Object Windows `KILL_ON_JOB_CLOSE` (anti-orphelin : l'entrainement
        meurt avec son superviseur, jamais orphelin) ;
      - un plafond DUR de memoire commitee (`JOB_OBJECT_LIMIT_JOB_MEMORY`) : au
        dela, les allocations ECHOUENT au lieu de swapper sur l'hote ;
      - une garde d'admission sur la CHARGE DE COMMIT de la machine
        (`Win32_PerfFormattedData_PerfOS_Memory`), fail-CLOSED : une mesure
        illisible refuse aussi le demarrage ;
      - un verrou exclusif N=1 : un seul entrainement CoursIA par machine.

    Le defaut de production est 48 Go : c'est l'engagement pris aupres de la lane
    Maintenance d'ai-01 (issue #21661). La machine porte 190 Go de RAM ; sans
    plafond, un entrainement peut en retenir une part qui fait manquer de RAM a
    un service critique.

    Le lanceur demarre le superviseur DETACHE (comme les lanceurs historiques
    du dossier) : le superviseur reste vivant pendant toute la duree de
    l'entrainement, tient le verrou N=1 et le Job Object, et redige le bilan
    de fin (pic memoire, raison de l'arret) dans le journal. `-Wait` rend la
    main a la fin de l'entrainement.

.PARAMETER FilePath
    Programme a lancer (typiquement l'interpreteur Python de l'env conda).

.PARAMETER ArgumentList
    Arguments passes au programme.

.PARAMETER MemoryCapGiB
    Plafond de memoire du job, en GiB (defaut 48 -- engagement Maintenance).
    S'applique au processus et a ses enfants.

.PARAMETER MaxCommitChargePct
    Refuse le demarrage si la charge de commit de la machine depasse ce
    pourcentage (defaut 85). 0 desactive la garde.

.PARAMETER LogPath
    Journal de l'entrainement (sortie standard du programme ET rapport du
    superviseur).

.PARAMETER ErrPath
    Journal de la sortie d'erreur du programme.

.PARAMETER PidPath
    Fichier ou le superviseur ecrit le PID du processus d'entrainement.

.PARAMETER LockPath
    Verrou exclusif N=1. Un seul entrainement CoursIA par machine.

.PARAMETER PythonExe
    Interpreteur Python qui execute le superviseur. Doit avoir `psutil`.

.PARAMETER Wait
    Attendre la fin de l'entrainement (par defaut, le lanceur rend la main
    immediatement, comme les lanceurs historiques).

.EXAMPLE
    .\launch_capped.ps1 -FilePath C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe `
        -ArgumentList @("train_lstm.py", "--epochs", "100") `
        -LogPath D:\out\train.log -ErrPath D:\out\train.err -PidPath D:\out\PID.txt
#>
param(
    [Parameter(Mandatory = $true)][string]$FilePath,
    [string[]]$ArgumentList = @(),
    [double]$MemoryCapGiB = 48,
    [int]$MaxCommitChargePct = 85,
    [string]$LogPath,
    [string]$ErrPath,
    [string]$PidPath,
    [string]$LockPath = (Join-Path $env:LOCALAPPDATA "CoursIA\train-ai01.lock"),
    [string]$PythonExe = "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe",
    [switch]$Wait
)

$ErrorActionPreference = "Stop"

# --- Localisation de l'organe (racine du depot : 5 niveaux au-dessus) --------
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\..\..")).Path
$Guarded  = Join-Path $RepoRoot "scripts\ci\run_guarded.py"
if (-not (Test-Path $Guarded)) {
    throw "organe introuvable : $Guarded"
}
if (-not (Test-Path $PythonExe)) {
    throw "Python introuvable : $PythonExe"
}
if (-not $LogPath) { throw "-LogPath est obligatoire" }
if (-not $ErrPath) { throw "-ErrPath est obligatoire" }
if (-not $PidPath) { throw "-PidPath est obligatoire" }

foreach ($p in @($LogPath, $ErrPath, $PidPath)) {
    $dir = Split-Path -Parent $p
    if ($dir -and -not (Test-Path $dir)) { New-Item -ItemType Directory -Path $dir -Force | Out-Null }
}

# --- Arguments du superviseur ------------------------------------------------
$guardedArgs = @(
    $Guarded,
    "--limit-gib",           "$MemoryCapGiB",
    "--reserve-gib",         "4",
    "--job-memory-limit-gib", "$MemoryCapGiB",
    "--max-commit-charge-pct", "$MaxCommitChargePct",
    "--exclusive-lock",      $LockPath,
    "--pid-file",            $PidPath,
    "--log",                 $LogPath,
    "--stderr-file",         $ErrPath,
    "--",
    $FilePath
) + $ArgumentList

Write-Host "[CAP] superviseur      : $Guarded"
Write-Host "[CAP] plafond memoire  : $MemoryCapGiB GiB (processus + enfants, Job Object)"
Write-Host "[CAP] garde commit     : $MaxCommitChargePct % (fail-CLOSED)"
Write-Host "[CAP] exclusion N=1    : $LockPath"
Write-Host "[CAP] commande         : $FilePath $($ArgumentList -join ' ')"
Write-Host "[CAP] journal          : $LogPath (stdout + rapport) / $ErrPath (stderr)"

if ($Wait) {
    & $PythonExe @guardedArgs
    exit $LASTEXITCODE
}

# Start-Process joint les arguments avec des espaces SANS citer ceux qui en
# contiennent (PS 5.1) : on cite explicitement, sinon un chemin de travail
# contenant un espace est coupe en deux et la commande part avec des
# arguments fantomes.
$quotedArgs = $guardedArgs | ForEach-Object {
    if ($_ -match "\s" -and $_ -notmatch '^".*"$') { '"' + $_ + '"' } else { $_ }
}

$supOut = "$LogPath.supervisor.out"
$supErr = "$LogPath.supervisor.err"
$proc = Start-Process -FilePath $PythonExe -ArgumentList $quotedArgs -NoNewWindow -PassThru `
    -RedirectStandardOutput $supOut -RedirectStandardError $supErr

# Le PID du superviseur est note a part : c'est lui qu'on arrete, et le Job
# Object tue alors l'entrainement avec lui. Le PID de l'entrainement, lui, est
# ecrit par le superviseur dans -PidPath.
$supPidPath = "$PidPath.supervisor.txt"
$proc.Id | Out-File -FilePath $supPidPath -Encoding utf8

Write-Host "[CAP] superviseur lance : PID $($proc.Id) -> $supPidPath"
Write-Host "[CAP] l'entrainement demarre en detaché ; son PID sera ecrit dans $PidPath"
Write-Host "[CAP] arreter : Stop-Process -Id $($proc.Id) (le Job Object tue l'entrainement)"
