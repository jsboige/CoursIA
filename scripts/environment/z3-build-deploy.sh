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
# SMT/Z3-Linq2Z3 notebook self-contained.
#
# Linux: the Microsoft.Z3 NuGet package ships native libz3 only for win-x64 and
# osx-x64, so the build output (and the .deploy/ committed in the fork) holds a
# Windows libz3.dll that Linux cannot load (DllNotFoundException 'libz3'). On
# Linux the script therefore also fetches libz3.so from the official z3-solver
# wheel of the SAME Z3 version as the Microsoft.Z3 package reference (#17654).
#
# Decision: ai-01 [DECISION COORD] 2026-06-13, option (b) refined.
# See: MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-Linq2Z3/05_Nested_Arrays_2D.ipynb (cell 1)

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
# Native solver per OS, and the Z3 version pinned by the wrapper csproj (the
# managed Microsoft.Z3.dll and the native library must come from the same release).
Z3_VERSION="$(sed -n 's/.*Include="Microsoft\.Z3" Version="\([0-9.]*\)".*/\1/p' "$CSPROJ" | head -1)"
if [[ -z "$Z3_VERSION" ]]; then
    echo "ERROR: Microsoft.Z3 PackageReference version not found in $CSPROJ"
    exit 1
fi
OS="$(uname -s)"
ARCH="$(uname -m)"
case "$OS" in
    Linux) NATIVE_LIB="libz3.so" ;;
    Darwin)
        NATIVE_LIB="libz3.dylib"
        case "$ARCH" in
            x86_64|arm64) ;;
            *) echo "ERROR: unsupported macOS architecture: $ARCH"; exit 1 ;;
        esac ;;
    *) NATIVE_LIB="libz3.dll" ;;
esac
required_dlls=("Z3.Linq.dll" "Microsoft.Z3.dll" "$NATIVE_LIB" "ExpressionUtils.dll")
if [[ -d "$DEPLOY_DIR" && "$FORCE" != "1" ]]; then
    missing=()
    for d in "${required_dlls[@]}"; do
        [[ -s "$DEPLOY_DIR/$d" ]] || missing+=("$d")
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
STAGE_DIR="$(mktemp -d "$SUBMODULE_DIR/.deploy-stage.XXXXXX")"
WHEEL_DIR=""
cleanup() {
    [[ -z "$STAGE_DIR" ]] || rm -rf "$STAGE_DIR"
    [[ -z "$WHEEL_DIR" ]] || rm -rf "$WHEEL_DIR"
}
trap cleanup EXIT

# 1. wrapper + native solver from local build output
cp "$BUILD_OUT/Z3.Linq.dll" "$STAGE_DIR/"
if [[ "$NATIVE_LIB" == "libz3.dll" ]]; then
    cp "$BUILD_OUT/libz3.dll" "$STAGE_DIR/"
fi

# 2. managed dependencies from the NuGet package cache.
#    dotnet build of a library does not copy managed deps into bin/ (resolved at
#    runtime via deps.json), but #r path-loads in a notebook need them on disk.
NUGET_ROOT="${NUGET_PACKAGES:-$HOME/.nuget/packages}"
if [[ ! -d "$NUGET_ROOT" ]]; then
    echo "ERROR: NuGet package cache not found at $NUGET_ROOT"
    echo "  (run the build once to restore packages, or set NUGET_PACKAGES)"
    exit 1
fi

Z3_MANAGED="$NUGET_ROOT/microsoft.z3/$Z3_VERSION/lib/netstandard2.0/Microsoft.Z3.dll"
EXPR_UTILS="$NUGET_ROOT/miaplaza.expressionutils/1.2.0/lib/netstandard2.0/ExpressionUtils.dll"

for dep in "$Z3_MANAGED:Microsoft.Z3.dll" "$EXPR_UTILS:ExpressionUtils.dll"; do
    src="${dep%%:*}"; name="${dep##*:}"
    if [[ -f "$src" ]]; then
        cp "$src" "$STAGE_DIR/$name"
    else
        echo "ERROR: dependency not found in NuGet cache: $src"
        echo "  Run: dotnet restore $CSPROJ  (then re-run this script)"
        exit 1
    fi
done

# 3. macOS x64 : bibliothèque native du même paquet NuGet que la DLL managée.
#    Microsoft.Z3 4.12.2 ne fournit pas ARM64 : utiliser la wheel correspondante.
if [[ "$OS" == "Darwin" && "$ARCH" == "x86_64" ]]; then
    Z3_NATIVE="$NUGET_ROOT/microsoft.z3/$Z3_VERSION/runtimes/osx-x64/native/libz3.dylib"
    if [[ ! -f "$Z3_NATIVE" ]]; then
        echo "ERROR: macOS x64 native dependency not found: $Z3_NATIVE"
        exit 1
    fi
    cp "$Z3_NATIVE" "$STAGE_DIR/libz3.dylib"
fi

# Linux et macOS ARM64 : bibliothèque native de la wheel z3-solver de même version
#    (le paquet NuGet Microsoft.Z3 ne fournit pas de natif linux-x64).
if [[ "$OS" == "Linux" || ( "$OS" == "Darwin" && "$ARCH" == "arm64" ) ]]; then
    WHEEL_DIR="$(mktemp -d)"
    if [[ "$OS" == "Linux" ]]; then
        WHEEL_PLATFORM="manylinux2014_$ARCH"
    else
        WHEEL_PLATFORM="macosx_11_0_arm64"
    fi
    echo "Fetching $NATIVE_LIB from z3-solver==$Z3_VERSION.0 ($WHEEL_PLATFORM)..."
    if ! python3 -m pip download "z3-solver==$Z3_VERSION.0" --no-deps --only-binary=:all: \
            --platform "$WHEEL_PLATFORM" -d "$WHEEL_DIR" -q; then
        echo "ERROR: could not download z3-solver==$Z3_VERSION.0 for $WHEEL_PLATFORM (python3 -m pip required)."
        exit 1
    fi
    python3 - "$WHEEL_DIR" "$STAGE_DIR/$NATIVE_LIB" "$NATIVE_LIB" <<'PY'
import glob
import sys
import zipfile

wheels = glob.glob(sys.argv[1] + "/z3_solver-*.whl")
if len(wheels) != 1:
    sys.exit("ERROR: expected exactly one z3-solver wheel")
with zipfile.ZipFile(wheels[0]) as zf:
    members = [n for n in zf.namelist() if n.endswith("/" + sys.argv[3])]
    if len(members) != 1:
        sys.exit("ERROR: expected exactly one native library in wheel")
    member = members[0]
    with open(sys.argv[2], "wb") as out:
        out.write(zf.read(member))
PY
fi

# --- verify ----------------------------------------------------------------------------
echo ""
echo "=== .deploy/ contents ==="
for d in "${required_dlls[@]}"; do
    if [[ -s "$STAGE_DIR/$d" ]]; then
        size=$(( $(stat -f%z "$STAGE_DIR/$d" 2>/dev/null || stat -c%s "$STAGE_DIR/$d" 2>/dev/null) / 1024 ))
        printf "  %-22s %6d KB\n" "$d" "$size"
    else
        echo "FAILED: missing $d"; exit 1
    fi
done

# Publier le répertoire vérifié ; conserver le précédent si le remplacement échoue.
BACKUP_DIR=""
if [[ -e "$DEPLOY_DIR" ]]; then
    BACKUP_DIR="$(mktemp -d "$SUBMODULE_DIR/.deploy-backup.XXXXXX")"
    rmdir "$BACKUP_DIR"
    mv "$DEPLOY_DIR" "$BACKUP_DIR"
fi
if ! mv "$STAGE_DIR" "$DEPLOY_DIR"; then
    if [[ -n "$BACKUP_DIR" ]]; then
        mv "$BACKUP_DIR" "$DEPLOY_DIR" || echo "ERROR: restore previous deployment from $BACKUP_DIR"
    fi
    echo "ERROR: could not publish deployment."
    exit 1
fi
STAGE_DIR=""
[[ -z "$BACKUP_DIR" ]] || rm -rf "$BACKUP_DIR"

echo ""
echo "=== Z3.Linq fork build complete ==="
echo ".deploy/ ready at: $DEPLOY_DIR"
echo ""
echo "Notebook cell 1 should now resolve:"
echo '  #r "../Z3.Linq/.deploy/Microsoft.Z3.dll"'
echo '  #r "../Z3.Linq/.deploy/Z3.Linq.dll"'
echo '  #r "../Z3.Linq/.deploy/ExpressionUtils.dll"'
exit 0
