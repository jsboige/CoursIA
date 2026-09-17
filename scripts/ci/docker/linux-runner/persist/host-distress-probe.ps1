# Sonde de DETRESSE de l'hote Windows -- un echantillon, une ligne.
#
# Rend, separes par des espaces :
#   pagewrites  pagesout  disk_queue_max  disk_idle_pct_min  vmmem_commit_mb  mapped_mb
#
# TOUT est rendu en ENTIERS, et les deux tailles en Mo, pas en Go. Sous locale
# FR ce script rendait `91,7` -- virgule decimale -- que awk et l'arithmetique
# bash lisent comme `91`. Une taille arrondie au Go perdrait par ailleurs la
# resolution du critere `Mapped` (une eviction qdrant se voit bien avant 1 Go).
# Pas de separateur decimal = pas de dependance a la locale.
#
# Rend une ligne vide et sort 1 si la mesure est impossible : jamais un chiffre
# par defaut, jamais zero -- un zero fabrique est indiscernable d'une machine
# saine, et c'est precisement ce qui transforme un garde en decor.
#
# CE QUI EST MESURE, ET POURQUOI CES COMPTEURS-LA (arbitrage Maintenance
# 2026-09-07T22:59Z, apres le retrait de quatre seuils en une nuit) :
#
#   detresse reelle  -> PageWrites/s + PagesOutput/s SOUTENUS > 0, avec le
#                       disque qui souffre (file > 0 et temps d'inactivite qui
#                       s'effondre). Un compteur de NIVEAU ne dit rien.
#   cout d'un process-> Win32_Process.PageFileUsage (commit prive). Jamais le
#                       WorkingSet : Windows le rabote quand il pagine, donc
#                       l'instrument BAISSE quand le probleme s'aggrave.
#
# Compteurs ECARTES et la raison, pour qu'ils ne reviennent pas :
#   Available / FreePhysicalMemory  identiques (free + standby). Le standby
#                                   n'est de la marge que si personne ne le
#                                   reclame ; mesure ai-01 : 47,6 -> 91,6 Go
#                                   pendant que la ressource ne bougeait pas.
#   FreeAndZeroPageListBytes        Windows garde la free list basse PAR DESIGN.
#                                   1,7 Go avec zero lecture disque = machine
#                                   saine. Un plancher dessus est un faux rouge
#                                   permanent.
#   commit %                        « 78 etait mon invention » (Maintenance).
#   PageReads/s seul                un taux sans terme de contrainte : 293/s
#                                   avec latence 0 ms n'est pas une famine.
#   AvgDisksecPerRead / PerWrite    UInt32 EN SECONDES dans la classe formatee :
#                                   ils rendent 0 jusqu'a 1 s de latence.
#                                   Mesure ai-01 2026-09-07 23:42Z : 0 sur les
#                                   cinq disques. Un seuil a 5 ms dessus ne peut
#                                   PAS se declencher -- garde vert par
#                                   construction. On lit PercentIdleTime, qui a
#                                   la resolution (98-99 % a l'instant sain).

$ErrorActionPreference = 'Stop'
try {
    $m = Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory
    if (-not $m) { exit 1 }

    $d = @(Get-CimInstance Win32_PerfFormattedData_PerfDisk_PhysicalDisk |
           Where-Object { $_.Name -ne '_Total' })
    if ($d.Count -eq 0) { exit 1 }

    $queueMax   = ($d | Measure-Object -Property CurrentDiskQueueLength -Maximum).Maximum
    $idlePctMin = ($d | Measure-Object -Property PercentIdleTime -Minimum).Minimum

    # Commit PRIVE de la VM WSL, en Go. PageFileUsage est en Ko.
    $vm = @(Get-CimInstance Win32_Process | Where-Object { $_.Name -like 'vmmem*' })
    $vmCommitMb = if ($vm.Count -gt 0) {
        [int][math]::Round((($vm | Measure-Object -Property PageFileUsage -Sum).Sum) / 1KB)
    } else { -1 }

    # `Mapped` de la VM WSL, en Go : c'est le mmap qdrant. Une CHUTE = qdrant se
    # fait evincer, critere d'abandon donne par Maintenance. -1 = non mesurable
    # (wsl.exe absent ou distro non demarree) ; l'appelant traite -1 comme
    # « inconnu », jamais comme « zero ».
    #
    # `wsl.exe -e cat` puis filtrage cote PowerShell : PAS de `sh -c "awk ..."`.
    # Le motif awk traverse bash -> PowerShell -> wsl -> sh, et chaque etage
    # mange une couche de quoting : mesure du 2026-09-07T23:47Z, awk recevait
    # `{print` comme NOM DE FICHIER. Ne jamais faire transiter un motif par
    # quatre interpretes quand on peut faire transiter du texte.
    $mappedMb = -1
    $wsl = Get-Command wsl.exe -ErrorAction SilentlyContinue
    if ($wsl) {
        try {
            $meminfo = & wsl.exe -e cat /proc/meminfo 2>$null
            if ($LASTEXITCODE -eq 0) {
                $hit = $meminfo | Where-Object { $_ -match '^Mapped:\s+(\d+)\s+kB' } | Select-Object -First 1
                if ($hit -and $hit -match '^Mapped:\s+(\d+)\s+kB') {
                    $mappedMb = [int][math]::Round([double]$Matches[1] / 1KB)
                }
            }
        } catch { $mappedMb = -1 }
    }

    '{0} {1} {2} {3} {4} {5}' -f `
        [int]$m.PageWritesPersec, [int]$m.PagesOutputPersec,
        [int]$queueMax, [int]$idlePctMin, [int]$vmCommitMb, [int]$mappedMb
    exit 0
}
catch {
    exit 1
}
