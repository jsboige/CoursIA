<#
.SYNOPSIS
    Mutualise les checkouts Mathlib des projets Lean du depot via NTFS junctions.

.DESCRIPTION
    Issue #2611 : ~12 projets Lake embarquent chacun leur checkout Mathlib
    (~61 GB cumules). Ce script detecte les projets partageant EXACTEMENT le
    meme lake-manifest.json (toutes deps transitives, pas seulement mathlib)
    et le meme lean-toolchain, puis remplace leurs checkouts mathlib par des
    junctions NTFS vers un cache central `.mathlib-cache/<toolchain>-<rev8>/`.

    Precondition validee empiriquement (test 2026-06-10, social_choice_lean ->
    cooperative_games_lean) : les traces Lake sont stables au deplacement
    physique du checkout — build a travers la junction = pur replay
    (3327 jobs, 0 recompilation), A CONDITION que lake-manifest.json soit
    identique sur TOUS les packages transitifs et que le lean-toolchain soit
    identique. Le script refuse de grouper sinon.

    Les junctions NTFS ne requierent PAS d'elevation admin. La suppression
    d'une junction (`cmd /c rmdir`) ne supprime que le lien, jamais la cible.

.PARAMETER Mode
    Scan     : inventaire des projets, groupes mutualisables, economies estimees. Aucune modification.
    Apply    : cree le cache partage + junctions pour les groupes eligibles. Reversible (backups .bak-2611 + share-state.json).
    Rollback : restaure les checkouts physiques depuis les backups (lit share-state.json).

.PARAMETER Group
    (Apply/Rollback) Restreint aux groupes dont la cle contient cette chaine
    (ex: '1c1dadbc' = prefixe rev mathlib). Sans filtre, Apply traite TOUS les groupes eligibles.

.PARAMETER Build
    (Apply) Apres junction, lance `lake build` dans chaque projet membre.
    Si un build echoue, rollback automatique de CE membre (junction retiree, checkout physique restaure).

.PARAMETER RemoveBackups
    (Apply) Apres un build verifie SUCCESS pour un membre, supprime son backup
    `mathlib.bak-2611` (c'est la qu'on recupere l'espace disque). Sans ce flag,
    les backups restent en place et AUCUN espace n'est libere — c'est le mode sur.
    Requiert -Build.

.EXAMPLE
    pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan
    pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Apply -Group 1c1dadbc -Build
    pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Rollback -Group 1c1dadbc

.NOTES
    - Ne PAS lancer `lake update` dans un projet junctionne : cela muterait le
      checkout partage pour tous les membres du groupe. Mettre a jour =
      Rollback d'abord, update, puis re-Scan/Apply.
    - `.mathlib-cache/` est gitignore (artefact local, jamais committe).
    - Voir #2611 pour l'inventaire des groupes et le plan d'alignement des
      manifests (etape 2) qui elargira les groupes mutualisables.
#>
#Requires -Version 7.0
[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [ValidateSet('Scan', 'Apply', 'Rollback')]
    [string]$Mode,

    [string]$Group = '',

    [switch]$Build,

    [switch]$RemoveBackups
)

$ErrorActionPreference = 'Stop'

$RepoRoot = (& git rev-parse --show-toplevel 2>$null)
if (-not $RepoRoot) { throw "Pas dans un depot git." }
$RepoRoot = $RepoRoot -replace '/', '\'
$CacheRoot = Join-Path $RepoRoot '.mathlib-cache'
$BackupSuffix = '.bak-2611'

if ($RemoveBackups -and -not $Build) {
    throw "-RemoveBackups requiert -Build : on ne supprime un backup qu'apres un build verifie SUCCESS."
}

function Get-DirSizeGB([string]$Path) {
    if (-not (Test-Path $Path)) { return 0.0 }
    $sum = (Get-ChildItem -LiteralPath $Path -Recurse -File -Force -ErrorAction SilentlyContinue |
        Measure-Object Length -Sum).Sum
    if (-not $sum) { return 0.0 }
    return [Math]::Round($sum / 1GB, 2)
}

function Test-IsJunction([string]$Path) {
    if (-not (Test-Path -LiteralPath $Path)) { return $false }
    $item = Get-Item -LiteralPath $Path -Force
    return [bool]($item.Attributes -band [IO.FileAttributes]::ReparsePoint)
}

# --- Discovery : tous les projets Lake traques par git (lake-manifest.json) ---

function Get-LeanProjects {
    $manifests = & git -C $RepoRoot ls-files --cached --others --exclude-standard -- '*lake-manifest.json' |
        Where-Object { $_ -notmatch '\.lake/' }
    $projects = @()
    foreach ($rel in $manifests) {
        $manifestPath = Join-Path $RepoRoot ($rel -replace '/', '\')
        if (-not (Test-Path -LiteralPath $manifestPath)) { continue }
        $projDir = Split-Path $manifestPath -Parent
        try {
            $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
        } catch {
            Write-Warning "Manifest illisible, ignore : $rel"
            continue
        }
        $packages = @($manifest.packages)
        $mathlibPkg = $packages | Where-Object { $_.name -eq 'mathlib' }
        if (-not $mathlibPkg) { continue }  # projet core-only ou sans mathlib : rien a mutualiser

        $toolchainFile = Join-Path $projDir 'lean-toolchain'
        $toolchain = if (Test-Path -LiteralPath $toolchainFile) {
            (Get-Content -LiteralPath $toolchainFile -Raw).Trim()
        } else { '<missing>' }

        # Cle de groupe : toolchain + (name,rev) TRIES de TOUTES les deps transitives.
        # Precondition durcie du test 2026-06-10 : mathlib seul ne suffit pas,
        # le replay Lake exige l'identite de tout le graphe de packages.
        $pairs = $packages | Sort-Object name | ForEach-Object { "$($_.name)=$($_.rev)" }
        $groupKey = "$toolchain|$($pairs -join ';')"

        $mathlibDir = Join-Path $projDir '.lake\packages\mathlib'
        $projects += [pscustomobject]@{
            RelPath     = $rel -replace '/lake-manifest\.json$', ''
            ProjDir     = $projDir
            Toolchain   = $toolchain
            MathlibRev  = $mathlibPkg.rev
            GroupKey    = $groupKey
            MathlibDir  = $mathlibDir
            HasCheckout = (Test-Path -LiteralPath $mathlibDir)
            IsJunction  = (Test-IsJunction $mathlibDir)
        }
    }
    return $projects
}

function Get-GroupId([object]$Members) {
    $toolchainSafe = ($Members[0].Toolchain -replace '[^A-Za-z0-9.\-]', '_') -replace '^.*[:/]', ''
    $rev8 = $Members[0].MathlibRev.Substring(0, 8)
    return "$toolchainSafe-$rev8"
}

function Get-ShareStatePath([string]$GroupId) {
    return Join-Path (Join-Path $CacheRoot $GroupId) 'share-state.json'
}

# --- Scan ---

function Invoke-Scan {
    $projects = Get-LeanProjects
    if (-not $projects) { Write-Host "Aucun projet Lake avec mathlib trouve."; return }

    Write-Host "=== Projets Lake avec dependance mathlib ($($projects.Count)) ===`n"
    $groups = $projects | Group-Object GroupKey | Sort-Object Count -Descending
    $totalSavings = 0.0

    foreach ($g in $groups) {
        $members = @($g.Group)
        $groupId = Get-GroupId $members
        $shareable = $members.Count -ge 2
        $tag = if ($shareable) { 'MUTUALISABLE' } else { 'isole' }
        Write-Host "--- Groupe $groupId [$tag] : toolchain=$($members[0].Toolchain) mathlib=$($members[0].MathlibRev.Substring(0,8)) ---"

        $sizes = @{}
        foreach ($m in $members) {
            $status =
                if ($m.IsJunction) { 'JUNCTIONED' }
                elseif ($m.HasCheckout) {
                    $sz = Get-DirSizeGB $m.MathlibDir
                    $sizes[$m.RelPath] = $sz
                    "checkout physique ($sz GB)"
                }
                else { 'pas de checkout local' }
            Write-Host ("  {0,-70} {1}" -f $m.RelPath, $status)
        }
        if ($shareable -and $sizes.Count -ge 2) {
            $vals = @($sizes.Values | Sort-Object -Descending)
            $savings = [Math]::Round(($vals | Select-Object -Skip 1 | Measure-Object -Sum).Sum, 2)
            $totalSavings += $savings
            Write-Host "  => economie potentielle : $savings GB (garder le plus gros comme donneur)"
        }
        Write-Host ''
    }
    Write-Host "=== Economie totale potentielle (groupes en l'etat) : $([Math]::Round($totalSavings,2)) GB ==="
    Write-Host "Note : l'alignement des manifests (#2611 etape 2) peut elargir les groupes."
}

# --- Apply ---

function Remove-DirRobust([string]$Path) {
    # Remove-Item echoue sur les artefacts Mathlib (chemins > 260 chars) meme avec
    # le prefixe \\?\ (incident 2026-06-11, purge mathlib.bak-2611 de calibration_lean).
    # Fallback : robocopy /MIR depuis un dossier vide (gere les long paths nativement).
    if (-not (Test-Path -LiteralPath $Path)) { return }
    try { Remove-Item -LiteralPath $Path -Recurse -Force -ErrorAction Stop } catch {}
    if (Test-Path -LiteralPath $Path) {
        $empty = New-Item -ItemType Directory -Force -Path (Join-Path $env:TEMP "empty-2611")
        robocopy $empty.FullName $Path /MIR /NFL /NDL /NJH /NJS /NP /R:2 /W:1 | Out-Null
        cmd /c "rd /s /q `"$Path`"" 2>$null
        Remove-Item $empty.FullName -Force -ErrorAction SilentlyContinue
    }
    if (Test-Path -LiteralPath $Path) {
        throw "Suppression impossible : $Path"
    }
}

function Restore-Member([object]$Member) {
    # Retire la junction (lien seul) et restaure le backup physique si present.
    if (Test-IsJunction $Member.MathlibDir) {
        & cmd /c rmdir "$($Member.MathlibDir)"
    }
    $bak = "$($Member.MathlibDir)$BackupSuffix"
    if (Test-Path -LiteralPath $bak) {
        Move-Item -LiteralPath $bak -Destination $Member.MathlibDir
    }
}

function Invoke-Apply {
    $projects = Get-LeanProjects
    $groups = $projects | Group-Object GroupKey | Where-Object { $_.Count -ge 2 }
    if ($Group) {
        $groups = $groups | Where-Object {
            $gid = Get-GroupId @($_.Group)
            $gid -like "*$Group*" -or $_.Group[0].MathlibRev -like "$Group*"
        }
    }
    if (-not $groups) { Write-Host "Aucun groupe mutualisable ne correspond au filtre '$Group'."; return }

    foreach ($g in $groups) {
        $members = @($g.Group | Where-Object { -not $_.IsJunction })
        $alreadyDone = @($g.Group | Where-Object IsJunction)
        $groupId = Get-GroupId @($g.Group)
        $cacheDir = Join-Path $CacheRoot $groupId
        $cacheMathlib = Join-Path $cacheDir 'mathlib'

        Write-Host "`n=== Apply groupe $groupId ($($members.Count) a traiter, $($alreadyDone.Count) deja junctionne(s)) ==="

        # 1. Donneur : cache existant, sinon membre au plus gros .lake/build (traces les plus completes).
        $donorRelPath = $null
        if (-not (Test-Path -LiteralPath $cacheMathlib)) {
            $candidates = $members | Where-Object HasCheckout |
                Sort-Object { Get-DirSizeGB (Join-Path $_.MathlibDir '.lake\build') } -Descending
            if (-not $candidates) {
                Write-Warning "Groupe $groupId : aucun checkout physique a promouvoir en donneur, skip."
                continue
            }
            $donor = $candidates[0]
            $donorRelPath = $donor.RelPath
            Write-Host "Donneur : $($donor.RelPath) -> $cacheMathlib"
            New-Item -ItemType Directory -Force -Path $cacheDir | Out-Null
            Move-Item -LiteralPath $donor.MathlibDir -Destination $cacheMathlib
        } else {
            Write-Host "Cache existant reutilise : $cacheMathlib"
        }

        # 2. Junctions pour tous les membres (donneur inclus, son dossier vient d'etre deplace).
        # Les membres deja junctionnes sont re-traites aussi (re-enregistrement dans
        # share-state.json + re-verification -Build + liberation -RemoveBackups) : un
        # Apply interrompu entre la junction et la persistance de l'etat se repare en
        # relancant le meme Apply (incident 2026-06-11, abort PS5.1 sur utf8NoBOM).
        $statePath = Get-ShareStatePath $groupId
        $existing = if (Test-Path -LiteralPath $statePath) {
            @((Get-Content -LiteralPath $statePath -Raw | ConvertFrom-Json).members)
        } else { @() }
        $stateMembers = @()
        foreach ($m in @($g.Group)) {
            if ($m.IsJunction) {
                $hadBackup = Test-Path -LiteralPath "$($m.MathlibDir)$BackupSuffix"
                $prev = $existing | Where-Object { $_.relPath -eq $m.RelPath }
                $isDonor = [bool]($prev -and $prev.isDonor)
                Write-Host "  junction existante : $($m.RelPath) $(if ($hadBackup) { '(backup conserve)' })"
            } else {
                if (Test-Path -LiteralPath $m.MathlibDir) {
                    $bak = "$($m.MathlibDir)$BackupSuffix"
                    if (Test-Path -LiteralPath $bak) {
                        Write-Warning "$($m.RelPath) : backup deja present ($bak), skip ce membre."
                        continue
                    }
                    Move-Item -LiteralPath $m.MathlibDir -Destination $bak
                    $hadBackup = $true
                } else {
                    $hadBackup = $false
                }
                $parent = Split-Path $m.MathlibDir -Parent
                New-Item -ItemType Directory -Force -Path $parent | Out-Null
                New-Item -ItemType Junction -Path $m.MathlibDir -Target $cacheMathlib | Out-Null
                $isDonor = ($null -ne $donorRelPath -and $m.RelPath -eq $donorRelPath)
                Write-Host "  junction : $($m.RelPath) -> $groupId $(if ($hadBackup) { '(backup conserve)' })"
            }
            $stateMembers += [ordered]@{
                relPath    = $m.RelPath
                mathlibDir = $m.MathlibDir
                hadBackup  = $hadBackup
                isDonor    = $isDonor
            }

            # 3. Verification optionnelle : lake build a travers la junction.
            if ($Build) {
                Write-Host "  lake build $($m.RelPath) ..." -NoNewline
                Push-Location $m.ProjDir
                try {
                    $out = & lake build 2>&1
                    $ok = ($LASTEXITCODE -eq 0)
                } finally { Pop-Location }
                if ($ok) {
                    Write-Host " SUCCESS"
                    if ($RemoveBackups -and $hadBackup) {
                        Remove-DirRobust "$($m.MathlibDir)$BackupSuffix"
                        Write-Host "  backup supprime (espace recupere)."
                        ($stateMembers[-1]).hadBackup = $false
                    }
                } else {
                    Write-Host " FAILED — rollback de ce membre"
                    ($out | Select-Object -Last 15) | ForEach-Object { Write-Host "    $_" }
                    Restore-Member $m
                    # @(...) obligatoire : un pipeline a 0/1 element degraderait $stateMembers
                    # en $null/scalaire, et `+= [ordered]@{}` sur un dictionnaire fusionne les
                    # cles au lieu d'appender -> "Item has already been added: 'relPath'".
                    $stateMembers = @($stateMembers | Where-Object { $_.relPath -ne $m.RelPath })
                }
            }
        }

        # 4. Persistance de l'etat pour Rollback ($statePath/$existing charges avant la boucle).
        $merged = @($existing) + @($stateMembers) |
            Group-Object { $_.relPath } | ForEach-Object { $_.Group[-1] }
        [ordered]@{
            groupId   = $groupId
            toolchain = $g.Group[0].Toolchain
            mathlibRev = $g.Group[0].MathlibRev
            createdAt = (Get-Date -Format 'o')
            members   = @($merged)
        } | ConvertTo-Json -Depth 4 |
            Set-Content -LiteralPath $statePath -Encoding utf8NoBOM
        Write-Host "Etat persiste : $statePath"
    }
}

# --- Rollback ---

function Invoke-Rollback {
    if (-not (Test-Path -LiteralPath $CacheRoot)) { Write-Host "Pas de cache ($CacheRoot), rien a faire."; return }
    $stateFiles = Get-ChildItem -LiteralPath $CacheRoot -Recurse -Filter 'share-state.json'
    if ($Group) { $stateFiles = $stateFiles | Where-Object { $_.Directory.Name -like "*$Group*" } }
    if (-not $stateFiles) { Write-Host "Aucun share-state.json ne correspond au filtre '$Group'."; return }

    foreach ($sf in $stateFiles) {
        $state = Get-Content -LiteralPath $sf.FullName -Raw | ConvertFrom-Json
        Write-Host "`n=== Rollback groupe $($state.groupId) ==="
        $cacheMathlib = Join-Path $sf.Directory.FullName 'mathlib'
        $remaining = @()
        # Non-donneurs d'abord : le cache doit rester en place tant qu'un membre
        # sans backup pourrait devoir copier depuis lui. Le donneur en dernier :
        # son rollback DEPLACE le cache (qui est son checkout d'origine).
        $ordered = @($state.members | Where-Object { -not $_.isDonor }) + @($state.members | Where-Object isDonor)
        foreach ($m in $ordered) {
            $bak = "$($m.mathlibDir)$BackupSuffix"
            if (Test-IsJunction $m.mathlibDir) {
                & cmd /c rmdir "$($m.mathlibDir)"
                if ($m.isDonor) {
                    if (Test-Path -LiteralPath $cacheMathlib) {
                        Move-Item -LiteralPath $cacheMathlib -Destination $m.mathlibDir
                        Write-Host "  restaure (donneur, cache deplace) : $($m.relPath)"
                    } else {
                        Write-Warning "$($m.relPath) : donneur mais cache introuvable ($cacheMathlib)."
                        $remaining += $m
                    }
                } elseif ($m.hadBackup -and (Test-Path -LiteralPath $bak)) {
                    Move-Item -LiteralPath $bak -Destination $m.mathlibDir
                    Write-Host "  restaure (backup) : $($m.relPath)"
                } elseif (-not $m.hadBackup) {
                    Write-Host "  junction retiree (pas de checkout initial) : $($m.relPath)"
                } else {
                    Write-Warning "$($m.relPath) : backup attendu mais introuvable ($bak). Copier depuis le cache : Copy-Item '$cacheMathlib' '$($m.mathlibDir)' -Recurse"
                    $remaining += $m
                }
            } else {
                Write-Host "  deja physique : $($m.relPath)"
            }
        }
        if (-not $remaining) {
            Remove-Item -LiteralPath $sf.FullName
            if ((Test-Path -LiteralPath $cacheMathlib)) {
                Write-Host "Etat efface. Le cache mathlib reste sur disque (groupe applique sur cache pre-existant) : verifier avant suppression manuelle."
            } else {
                Remove-Item -LiteralPath $sf.Directory.FullName -Force -ErrorAction SilentlyContinue
                Write-Host "Etat efface, cache $($state.groupId) restitue au donneur."
            }
        }
    }
}

switch ($Mode) {
    'Scan'     { Invoke-Scan }
    'Apply'    { Invoke-Apply }
    'Rollback' { Invoke-Rollback }
}