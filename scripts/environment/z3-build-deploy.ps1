# Z3.Linq Fork Build Script for CoursIA SymbolicAI Notebooks
#
# Builds the Z3.Linq wrapper fork (which adds int[][] / ExtractCollection /
# CollectionHandling support) and gathers all DLLs the SMT/Z3 notebooks need
# into the submodule's .deploy/ directory.
#
# Why this script exists:
#   The fork (github.com/MyIntelligenceAgency/Z3.Linq) carries int[][] array
#   support that is NOT on the public endjin NuGet package (Z3.Linq 2.0.1).
#   Publishing a forked NuGet is not an option (we are not the package-id
#   owner), so we build the thin wrapper locally. The native solver Microsoft.Z3
#   IS on public NuGet — only the thin LINQ wrapper is missing. This script
#   compiles ONLY the wrapper csproj (~1.5s), then copies Microsoft.Z3.dll +
#   ExpressionUtils.dll from the NuGet cache alongside it.
#
# Result: a fresh checkout with --recurse-submodules + .NET SDK can run every
# SMT/Z3 notebook self-contained (no publish account, offline-friendly).
#
# Decision: ai-01 [DECISION COORD] 2026-06-13, option (b) refined.
# See: MyIA.AI.Notebooks/SymbolicAI/SMT/Z3/04_Nested_Arrays_2D.ipynb (cell 1)

param(
    # Path to the Z3.Linq submodule (auto-detected relative to this script).
    [string]$SubmoduleDir = (Resolve-Path (Join-Path $PSScriptRoot "..\..\MyIA.AI.Notebooks\SymbolicAI\SMT\Z3.Linq")),

    # Build configuration.
    [string]$Configuration = "Release",

    # Force rebuild even if .deploy/ already looks complete.
    [switch]$Force = $false
)

$ErrorActionPreference = "Stop"

Write-Host "=== Z3.Linq Fork Build for CoursIA SymbolicAI ===" -ForegroundColor Cyan
Write-Host ""

# --- locate submodule + wrapper csproj -------------------------------------------------
$submodule = (Resolve-Path $SubmoduleDir).Path
$csproj = Join-Path $submodule "solutions\Z3.Linq\Z3.Linq.csproj"
$deployDir = Join-Path $submodule ".deploy"

if (-not (Test-Path $csproj)) {
    Write-Host "ERROR: Z3.Linq.csproj not found at: $csproj" -ForegroundColor Red
    Write-Host "Did you clone with --recurse-submodules? Run:" -ForegroundColor Yellow
    Write-Host "  git submodule update --init --recursive" -ForegroundColor Gray
    exit 1
}

Write-Host "Submodule : $submodule" -ForegroundColor Gray
Write-Host "Wrapper   : $csproj" -ForegroundColor Gray
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
# .deploy/ is complete when all 4 required DLLs are present.
$requiredDlls = @("Z3.Linq.dll", "Microsoft.Z3.dll", "libz3.dll", "ExpressionUtils.dll")
$complete = $false
if ((Test-Path $deployDir) -and -not $Force) {
    $missing = $requiredDlls | Where-Object { -not (Test-Path (Join-Path $deployDir $_)) }
    if (-not $missing) {
        $complete = $true
    }
}
if ($complete) {
    Write-Host ".deploy/ already complete (4 DLLs present). Use -Force to rebuild." -ForegroundColor Green
    exit 0
}

# --- build the wrapper csproj ----------------------------------------------------------
Write-Host "Building Z3.Linq wrapper ($Configuration)..." -ForegroundColor Cyan
& dotnet build $csproj -c $Configuration --nologo 2>&1 | ForEach-Object {
    if ($_ -match "error|Erreur") { Write-Host $_ -ForegroundColor Red }
    elseif ($_ -match "succeeded|réussi|->") { Write-Host $_ -ForegroundColor Gray }
}
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: dotnet build failed (exit $LASTEXITCODE)." -ForegroundColor Red
    exit $LASTEXITCODE
}

$buildOut = Join-Path $submodule "solutions\Z3.Linq\bin\$Configuration\net8.0"
$builtWrapper = Join-Path $buildOut "Z3.Linq.dll"
if (-not (Test-Path $builtWrapper)) {
    Write-Host "ERROR: build succeeded but Z3.Linq.dll not found at $builtOut" -ForegroundColor Red
    exit 1
}

# Sanity: confirm the fork feature (CollectionHandling) is in the built DLL.
$bytes = [System.IO.File]::ReadAllText($builtWrapper, [System.Text.Encoding]::Latin1)
if ($bytes -notmatch "CollectionHandling") {
    Write-Host "WARNING: built Z3.Linq.dll lacks CollectionHandling — is the submodule at the fork commit?" -ForegroundColor Yellow
    Write-Host "  Expected commit 096a6383 (MyIntelligenceAgency/Z3.Linq int[][] fork)." -ForegroundColor Gray
} else {
    Write-Host "  CollectionHandling present (fork feature OK)." -ForegroundColor Green
}

# --- prepare .deploy/ ------------------------------------------------------------------
if (Test-Path $deployDir) { Remove-Item -Recurse -Force $deployDir }
New-Item -ItemType Directory -Path $deployDir -Force | Out-Null

# 1. wrapper + native solver from the local build output
Copy-Item (Join-Path $buildOut "Z3.Linq.dll") $deployDir -Force
Copy-Item (Join-Path $buildOut "libz3.dll") $deployDir -Force

# 2. managed dependencies from the NuGet package cache.
#    Microsoft.Z3 + MiaPlaza.ExpressionUtils are netstandard2.0; dotnet build of a
#    library does not copy managed deps into bin/ (resolved at runtime via deps.json),
#    but #r path-loads in a notebook need them on disk. Pin via the package cache.
$nugetRoot = Join-Path $env:USERPROFILE ".nuget\packages"
if (-not (Test-Path $nugetRoot)) {
    Write-Host "ERROR: NuGet package cache not found at $nugetRoot" -ForegroundColor Red
    Write-Host "  (run the build once to restore packages, or set NUGET_PACKAGES)" -ForegroundColor Yellow
    exit 1
}

$z3Managed = Join-Path $nugetRoot "microsoft.z3\4.12.2\lib\netstandard2.0\Microsoft.Z3.dll"
$exprUtils = Join-Path $nugetRoot "miaplaza.expressionutils\1.2.0\lib\netstandard2.0\ExpressionUtils.dll"

foreach ($dep in @(@{Path=$z3Managed; Name="Microsoft.Z3.dll"}, @{Path=$exprUtils; Name="ExpressionUtils.dll"})) {
    if (Test-Path $dep.Path) {
        Copy-Item $dep.Path (Join-Path $deployDir $dep.Name) -Force
    } else {
        Write-Host "ERROR: dependency not found in NuGet cache: $($dep.Path)" -ForegroundColor Red
        Write-Host "  Run: dotnet restore $csproj  (then re-run this script)" -ForegroundColor Yellow
        exit 1
    }
}

# --- verify ----------------------------------------------------------------------------
Write-Host ""
Write-Host "=== .deploy/ contents ===" -ForegroundColor Cyan
Get-ChildItem $deployDir -Filter "*.dll" | ForEach-Object {
    Write-Host ("  {0,-22} {1,8} KB" -f $_.Name, [int]($_.Length/1KB)) -ForegroundColor Gray
}

$missing = $requiredDlls | Where-Object { -not (Test-Path (Join-Path $deployDir $_)) }
if ($missing) {
    Write-Host ""
    Write-Host "FAILED: missing DLLs: $($missing -join ', ')" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "=== Z3.Linq fork build complete ===" -ForegroundColor Green
Write-Host ".deploy/ ready at: $deployDir" -ForegroundColor Cyan
Write-Host ""
Write-Host "Notebook cell 1 should now resolve:" -ForegroundColor White
Write-Host '  #r "../Z3.Linq/.deploy/Microsoft.Z3.dll"' -ForegroundColor Gray
Write-Host '  #r "../Z3.Linq/.deploy/Z3.Linq.dll"' -ForegroundColor Gray
Write-Host '  #r "../Z3.Linq/.deploy/ExpressionUtils.dll"' -ForegroundColor Gray
exit 0
