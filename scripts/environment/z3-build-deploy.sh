#!/usr/bin/env bash
# Z3.Linq Fork Build Script for CoursIA SymbolicAI Notebooks (Linux/macOS)
#
# Cross-platform twin of z3-build-deploy.ps1. Builds the Z3.Linq wrapper fork
# (int[][] / ExtractCollection / CollectionHandling support) and gathers all
# DLLs the SMT/Z3 notebooks need into the submodule's .deploy/ directory.
#
# Why: the fork carries int[][] support absent from public endjin NuGet
# (Z3.Linq 2.0.1). Publishing a forked NuGet is not an option (not the
# package-id owner), so we build the thin wrapper locally. Native Microsoft.Z3
# IS on public NuGet — only the thin LINQ wrapper is missing. This compiles
# ONLY the wrapper csproj (~1.5s), then copies Microsoft.Z3.dll +
# ExpressionUtils.dll from the NuGet cache alongside it.
#
# Result: a fresh checkout with --recurse-submodules + .NET SDK runs every
# SMT/Z3 notebook self-contained.
#
# Decision: ai-01 [DECISION COORD] 2026-06-13, option (b) refined.
# See: MyIA.AI.Notebooks/SymbolicAI/SMT/Z3/04_Nested_Arrays_2D.ipynb (cell 1)

set -euo pipefail

# Resolve submodule dir relative to this script (3 levels up from scripts/environment/).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SUBMODULE_DIR="${1:-$SCRIPT_DIR/../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq}"
CONFIGURATION="${2:-Release}"
FORCE="${Z3_FORCE:-0}"

SUBMODULE_DIR="$(cd "$SUBMODULE_DIR" && pwd)"
CSPROJ="$SUBMODULE_DIR/solutions/Z3.Linq/Z3.Linq.csproj"
DEPLOY_DIR="$SUBMODULE_DIR/.deploy"

echo "=== Z3.Linq Fork Build for CoursIA SymbolicAI ==="
echo ""

# --- locate submodule + wrapper csproj -------------------------------------------------
if [[ ! -f "$CSPROJ" ]]; then
    echo "ERROR: Z3.Linq.csproj not found at: $CSPROJ"
    echo "Did you clone with --recurse-submodules? Run:"
    echo "  git submodule update --init --recursive"
    exit 1
fi
echo "Submodule : $SUBMODULE_DIR"
echo "Wrapper   : $CSPROJ"
echo "Output    : $DEPLOY_DIR"
echo ""

# --- dotnet SDK precondition (installable everywhere, rule F) -------------------------
if ! command -v dotnet >/dev/null 2>&1; then
    echo "ERROR: dotnet SDK not found on PATH."
    echo "Install .NET 8.0+ SDK from https://dotnet.microsoft.com/download"
    exit 1
fi

# --- idempotency check -----------------------------------------------------------------
required_dlls=("Z3.Linq.dll" "Microsoft.Z3.dll" "libz3.dll" "ExpressionUtils.dll")
if [[ -d "$DEPLOY_DIR" && "$FORCE" != "1" ]]; then
    missing=()
    for d in "${required_dlls[@]}"; do
        [[ -f "$DEPLOY_DIR/$d" ]] || missing+=("$d")
    done
    if [[ ${#missing[@]} -eq 0 ]]; then
        echo ".deploy/ already complete (4 DLLs present). Set Z3_FORCE=1 to rebuild."
        exit 0
    fi
fi

# --- build the wrapper csproj ----------------------------------------------------------
echo "Building Z3.Linq wrapper ($CONFIGURATION)..."
if ! dotnet build "$CSPROJ" -c "$CONFIGURATION" --nologo; then
    echo "ERROR: dotnet build failed."
    exit 1
fi

BUILD_OUT="$SUBMODULE_DIR/solutions/Z3.Linq/bin/$CONFIGURATION/net8.0"
BUILT_WRAPPER="$BUILD_OUT/Z3.Linq.dll"
if [[ ! -f "$BUILT_WRAPPER" ]]; then
    echo "ERROR: build succeeded but Z3.Linq.dll not found at $BUILD_OUT"
    exit 1
fi

# Sanity: confirm the fork feature (CollectionHandling) is in the built DLL.
if ! grep -qa "CollectionHandling" "$BUILT_WRAPPER"; then
    echo "WARNING: built Z3.Linq.dll lacks CollectionHandling — is the submodule at the fork commit?"
    echo "  Expected commit 096a6383 (MyIntelligenceAgency/Z3.Linq int[][] fork)."
else
    echo "  CollectionHandling present (fork feature OK)."
fi

# --- prepare .deploy/ ------------------------------------------------------------------
rm -rf "$DEPLOY_DIR"
mkdir -p "$DEPLOY_DIR"

# 1. wrapper + native solver from local build output
cp "$BUILD_OUT/Z3.Linq.dll" "$DEPLOY_DIR/"
cp "$BUILD_OUT/libz3.dll"   "$DEPLOY_DIR/"

# 2. managed dependencies from the NuGet package cache.
#    dotnet build of a library does not copy managed deps into bin/ (resolved at
#    runtime via deps.json), but #r path-loads in a notebook need them on disk.
NUGET_ROOT="${NUGET_PACKAGES:-$HOME/.nuget/packages}"
if [[ ! -d "$NUGET_ROOT" ]]; then
    echo "ERROR: NuGet package cache not found at $NUGET_ROOT"
    echo "  (run the build once to restore packages, or set NUGET_PACKAGES)"
    exit 1
fi

Z3_MANAGED="$NUGET_ROOT/microsoft.z3/4.12.2/lib/netstandard2.0/Microsoft.Z3.dll"
EXPR_UTILS="$NUGET_ROOT/miaplaza.expressionutils/1.2.0/lib/netstandard2.0/ExpressionUtils.dll"

for dep in "$Z3_MANAGED:Microsoft.Z3.dll" "$EXPR_UTILS:ExpressionUtils.dll"; do
    src="${dep%%:*}"; name="${dep##*:}"
    if [[ -f "$src" ]]; then
        cp "$src" "$DEPLOY_DIR/$name"
    else
        echo "ERROR: dependency not found in NuGet cache: $src"
        echo "  Run: dotnet restore $CSPROJ  (then re-run this script)"
        exit 1
    fi
done

# --- verify ----------------------------------------------------------------------------
echo ""
echo "=== .deploy/ contents ==="
for d in "${required_dlls[@]}"; do
    if [[ -f "$DEPLOY_DIR/$d" ]]; then
        size=$(( $(stat -f%z "$DEPLOY_DIR/$d" 2>/dev/null || stat -c%s "$DEPLOY_DIR/$d" 2>/dev/null) / 1024 ))
        printf "  %-22s %6d KB\n" "$d" "$size"
    else
        echo "FAILED: missing $d"; exit 1
    fi
done

echo ""
echo "=== Z3.Linq fork build complete ==="
echo ".deploy/ ready at: $DEPLOY_DIR"
echo ""
echo "Notebook cell 1 should now resolve:"
echo '  #r "../Z3.Linq/.deploy/Microsoft.Z3.dll"'
echo '  #r "../Z3.Linq/.deploy/Z3.Linq.dll"'
echo '  #r "../Z3.Linq/.deploy/ExpressionUtils.dll"'
exit 0
