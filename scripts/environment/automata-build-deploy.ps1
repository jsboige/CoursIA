# Automata Fork Build Script for CoursIA SymbolicAI Notebooks
#
# Builds the AutomataDotNet fork (which adds surface '&' / '~' regex operators and
# lifts the 21-char witness cap, #2979) and gathers the DLLs the SMT/Z3 notebook 06
# needs into the submodule's .deploy/ directory.
#
# Why this script exists:
#   The fork (github.com/MyIntelligenceAgency/Automata, branch
#   feature/net8-modernization-core) carries surface intersection/complement regex
#   syntax + uncapped witness generation that are NOT on any public AutomataDotNet
#   package (the upstream Microsoft.Automata is frozen ~2020 and was never net8.0).
#   Microsoft.Automata is pure-managed (no native libz3-style payload), so building
#   the single Automata.csproj (~6s) plus copying its one external managed dependency
#   (System.CodeDom) from the NuGet cache is all that the notebook #r path-loads need.
#
# Result: a fresh checkout with --recurse-submodules + .NET SDK can run notebook
#   06_Witness_Generation_Automata self-contained (no publish account, offline-friendly).
#
# Mirrors scripts/environment/z3-build-deploy.ps1 (Z3.Linq fork). See #2979 step 6.
# See: MyIA.AI.Notebooks/SymbolicAI/SMT/Z3/06_Witness_Generation_Automata.ipynb (cell 1)

param(
    # Path to the Automata submodule (auto-detected relative to this script).
    [string]$SubmoduleDir = (Resolve-Path (Join-Path $PSScriptRoot "..\..\MyIA.AI.Notebooks\SymbolicAI\SMT\Automata")),

    # Build configuration.
    [string]$Configuration = "Release",

    # Force rebuild even if .deploy/ already looks complete.
    [switch]$Force = $false
)

$ErrorActionPreference = "Stop"

Write-Host "=== Automata Fork Build for CoursIA SymbolicAI ===" -ForegroundColor Cyan
Write-Host ""

# --- locate submodule + csproj ---------------------------------------------------------
$submodule = (Resolve-Path $SubmoduleDir).Path
$csproj = Join-Path $submodule "src\Automata\Automata.csproj"
$deployDir = Join-Path $submodule ".deploy"

if (-not (Test-Path $csproj)) {
    Write-Host "ERROR: Automata.csproj not found at: $csproj" -ForegroundColor Red
    Write-Host "Did you clone with --recurse-submodules? Run:" -ForegroundColor Yellow
    Write-Host "  git submodule update --init --recursive" -ForegroundColor Gray
    exit 1
}

Write-Host "Submodule : $submodule" -ForegroundColor Gray
Write-Host "Project   : $csproj" -ForegroundColor Gray
Write-Host "Output    : $deployDir" -ForegroundColor Gray
Write-Host ""

# --- dotnet SDK precondition (installable everywhere, rule F) -------------------------
$dotnet = Get-Command dotnet -ErrorAction SilentlyContinue
if (-not $dotnet) {
    Write-Host "ERROR: dotnet SDK not found on PATH." -ForegroundColor Red
    Write-Host "Install .NET 8.0+ SDK from https://dotnet.microsoft.com/download" -ForegroundColor Yellow
    exit 1
}

# --- idempotency check -----------------------------------------------------------------
# .deploy/ is complete when both required DLLs are present.
$requiredDlls = @("Microsoft.Automata.dll", "System.CodeDom.dll")
$complete = $false
if ((Test-Path $deployDir) -and -not $Force) {
    $missing = $requiredDlls | Where-Object { -not (Test-Path (Join-Path $deployDir $_)) }
    if (-not $missing) {
        $complete = $true
    }
}
if ($complete) {
    Write-Host ".deploy/ already complete (2 DLLs present). Use -Force to rebuild." -ForegroundColor Green
    exit 0
}

# --- build the csproj ------------------------------------------------------------------
Write-Host "Building Automata fork ($Configuration)..." -ForegroundColor Cyan
& dotnet build $csproj -c $Configuration --nologo 2>&1 | ForEach-Object {
    if ($_ -match "error|Erreur") { Write-Host $_ -ForegroundColor Red }
    elseif ($_ -match "succeeded|réussi|->") { Write-Host $_ -ForegroundColor Gray }
}
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: dotnet build failed (exit $LASTEXITCODE)." -ForegroundColor Red
    exit $LASTEXITCODE
}

$buildOut = Join-Path $submodule "src\Automata\bin\$Configuration\net8.0"
$builtDll = Join-Path $buildOut "Microsoft.Automata.dll"
if (-not (Test-Path $builtDll)) {
    Write-Host "ERROR: build succeeded but Microsoft.Automata.dll not found at $buildOut" -ForegroundColor Red
    exit 1
}

# Sanity: confirm the fork core (CharSetSolver) is in the built DLL.
$bytes = [System.IO.File]::ReadAllText($builtDll, [System.Text.Encoding]::Latin1)
if ($bytes -notmatch "CharSetSolver") {
    Write-Host "WARNING: built Microsoft.Automata.dll lacks CharSetSolver — is the submodule at the fork commit?" -ForegroundColor Yellow
    Write-Host "  Expected commit 4a7b7f0 (MyIntelligenceAgency/Automata, surface &/~ + uncapped witness)." -ForegroundColor Gray
} else {
    Write-Host "  CharSetSolver present (fork core OK)." -ForegroundColor Green
}

# --- prepare .deploy/ ------------------------------------------------------------------
if (Test-Path $deployDir) { Remove-Item -Recurse -Force $deployDir }
New-Item -ItemType Directory -Path $deployDir -Force | Out-Null

# 1. the fork assembly from the local build output
Copy-Item $builtDll $deployDir -Force

# 2. managed dependency from the NuGet package cache.
#    System.CodeDom is the single external managed dependency (see deps.json). A
#    dotnet build of a library does not copy managed deps into bin/ (resolved at
#    runtime via deps.json), but #r path-loads in a notebook need it on disk.
$nugetRoot = Join-Path $env:USERPROFILE ".nuget\packages"
if (-not (Test-Path $nugetRoot)) {
    Write-Host "ERROR: NuGet package cache not found at $nugetRoot" -ForegroundColor Red
    Write-Host "  (run the build once to restore packages, or set NUGET_PACKAGES)" -ForegroundColor Yellow
    exit 1
}

$codeDom = Join-Path $nugetRoot "system.codedom\8.0.0\lib\net8.0\System.CodeDom.dll"
if (Test-Path $codeDom) {
    Copy-Item $codeDom (Join-Path $deployDir "System.CodeDom.dll") -Force
} else {
    Write-Host "ERROR: dependency not found in NuGet cache: $codeDom" -ForegroundColor Red
    Write-Host "  Run: dotnet restore $csproj  (then re-run this script)" -ForegroundColor Yellow
    exit 1
}

# --- verify ----------------------------------------------------------------------------
Write-Host ""
Write-Host "=== .deploy/ contents ===" -ForegroundColor Cyan
Get-ChildItem $deployDir -Filter "*.dll" | ForEach-Object {
    Write-Host ("  {0,-24} {1,8} KB" -f $_.Name, [int]($_.Length/1KB)) -ForegroundColor Gray
}

$missing = $requiredDlls | Where-Object { -not (Test-Path (Join-Path $deployDir $_)) }
if ($missing) {
    Write-Host ""
    Write-Host "FAILED: missing DLLs: $($missing -join ', ')" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "=== Automata fork build complete ===" -ForegroundColor Green
Write-Host ".deploy/ ready at: $deployDir" -ForegroundColor Cyan
Write-Host ""
Write-Host "Notebook 06 cell 1 should now resolve:" -ForegroundColor White
Write-Host '  #r "../Automata/.deploy/Microsoft.Automata.dll"' -ForegroundColor Gray
exit 0
