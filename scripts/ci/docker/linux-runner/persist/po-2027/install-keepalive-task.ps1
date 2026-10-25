<#
.SYNOPSIS
Re-arme le porteur WSL du leg coursia-runner de po-2027 apres un arret de la distro.

.DESCRIPTION
Mesure du 2026-10-24 sur cette machine : le porteur spawn par
hold-myia-po-2027.ps1 vit exactement aussi longtemps que la distro. Un
`wsl --shutdown` -- ce que fait Docker Desktop a chaque redemarrage -- tue le
porteur et la distro ensemble. La tache logon `Coursia-LinuxRunners` ne tire
qu'a l'ouverture de session : apres un shutdown, plus rien ne re-arme le
porteur, et WSL reape la distro des que le dernier client sort (mesure
fondatrice du 2026-09-02, cf persist/hold-runner.ps1).

Sequence mesuree le 2026-10-24 (boot -1 : 22:50:37 -> 23:54:02 CEST) :
Docker Desktop redemarre a 23:54:19, la distro meurt a 23:54:02, le porteur
pid 38780 meurt avec elle. docker.service et coursia-runner.service se
relevent seuls au boot suivant (4 slots de nouveau online en ~25 s), mais le
porteur reste absent : la distro est donc a nouveau reapee une fois le dernier
client sorti, sans autre signal qu'une disparition des slots sur GitHub.

Cette tache est le rattrapage : elle re-invoque le pont launch-runner.sh toutes
les N minutes. Le garde anti-doublon de hold-myia-po-2027.ps1 rend l'appel
idempotent (porteur vivant -> simple `systemctl start`).

Creation non elevee (tache utilisateur, Interactive/Limited) : aucune fenetre
UAC. La tache logon d'origine, elle, a ete creee en eleve et n'est pas modifiee
ici -- `Set-ScheduledTask` y rend 0x80070005, mesure le 2026-10-24.

.PARAMETER Apply
Ecrit la tache. Sans ce commutateur : dry-run, aucune ecriture.

.PARAMETER Minutes
Intervalle de repetition, en minutes (defaut 5).

.PARAMETER Bridge
Pont a invoquer (defaut : launch-runner.sh du depot, slots = -Slots).

.PARAMETER Slots
Nombre de slots passe au pont (defaut 4).

.EXAMPLE
powershell -NoProfile -ExecutionPolicy Bypass -File install-keepalive-task.ps1

.EXAMPLE
powershell -NoProfile -ExecutionPolicy Bypass -File install-keepalive-task.ps1 -Apply
#>
param(
    [switch]$Apply,
    [int]$Minutes = 5,
    [string]$Bridge = 'D:\dev\CoursIA\scripts\ci\docker\linux-runner\persist\launch-runner.sh',
    [int]$Slots = 4
)
$ErrorActionPreference = 'Stop'

$name = 'Coursia-LinuxRunners-Keep'
$bash = 'C:\Program Files\Git\bin\bash.exe'
# launch-runner.sh attend un chemin POSIX (il tourne sous bash.exe de Git).
$bridgePosix = $Bridge -replace '\\', '/' -replace '^([A-Za-z]):', '/$1'
$arguments = "-lc `"$bridgePosix $Slots`""

$action = New-ScheduledTaskAction -Execute $bash -Argument $arguments
$trigger = New-ScheduledTaskTrigger -Once -At (Get-Date).Date.AddMinutes(1) `
    -RepetitionInterval (New-TimeSpan -Minutes $Minutes) `
    -RepetitionDuration ([TimeSpan]::FromDays(3650))
$settings = New-ScheduledTaskSettingsSet -AllowStartIfOnBatteries `
    -DontStopIfGoingOnBatteries -StartWhenAvailable `
    -MultipleInstances IgnoreNew -ExecutionTimeLimit (New-TimeSpan -Minutes 10)
$description = "po-2027 coursia-runner : re-arme le porteur WSL toutes les $Minutes min (self-heal apres wsl --shutdown)"

function Write-KeepaliveTask {
    param($Action, $Trigger)
    if (Get-ScheduledTask -TaskName $name -ErrorAction SilentlyContinue) {
        Set-ScheduledTask -TaskName $name -Action $Action -Trigger $Trigger -Settings $settings | Out-Null
        "maj : tache existante mise a jour (idempotent)"
    } else {
        Register-ScheduledTask -TaskName $name -Action $Action -Trigger $Trigger `
            -Settings $settings -Description $description | Out-Null
        "creation : tache enregistree (non eleve)"
    }
}

"tache   : $name"
"action  : $bash $arguments"
"repet   : interval=$($trigger.Repetition.Interval) duration=$($trigger.Repetition.Duration)"

if (-not $Apply) {
    "DRY-RUN : aucune ecriture. Relancer avec -Apply pour installer."
    exit 0
}

try {
    Write-KeepaliveTask -Action $action -Trigger $trigger
} catch {
    # Certains hotes refusent un -RepetitionDuration de 3650 j sur un declencheur
    # Once : le rejet tombe au Register/Set-ScheduledTask, pas a la construction
    # du trigger. Repli : [TimeSpan]::MaxValue, qui vaut « indefiniment » pour le
    # planificateur (remarque Hermes, #22532 section 2).
    "repli   : duration 3650 j refusee -- $($_.Exception.Message)"
    $trigger = New-ScheduledTaskTrigger -Once -At (Get-Date).Date.AddMinutes(1) `
        -RepetitionInterval (New-TimeSpan -Minutes $Minutes) `
        -RepetitionDuration ([TimeSpan]::MaxValue)
    Write-KeepaliveTask -Action $action -Trigger $trigger
}

$task = Get-ScheduledTask -TaskName $name
"verifie : state=$($task.State) interval='$($task.Triggers[0].Repetition.Interval)' enabled=$($task.Triggers[0].Enabled)"
"next    : " + (Get-ScheduledTaskInfo -TaskName $name).NextRunTime
exit 0
