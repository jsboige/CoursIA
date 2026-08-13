#!/usr/bin/env bash
# Automata Fork Build Script for CoursIA SymbolicAI Notebooks (Linux / macOS)
#
# Cross-platform twin of automata-build-deploy.ps1. Builds the AutomataDotNet fork
# (which adds surface '&' / '~' regex operators and lifts the 21-char witness cap,
# #2979) and gathers the DLLs the SMT/Z3 notebook 10 needs into the submodule's
# .deploy/ directory.
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
#   10_Witness_Generation_Automata self-contained (no publish account, offline-friendly).
#
# Usage: ./scripts/environment/automata-build-deploy.sh [submodule_dir] [Release|Debug] [--force]
#   submodule_dir  Path to the Automata submodule (auto-detected by default).
#   Configuration  Build configuration (default: Release).
#   --force        Rebuild even if .deploy/ already looks complete.
#
# Mirrors scripts/environment/z3-build-deploy.sh (Z3.Linq fork). See #2979 step 6.
# See: MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-Linq2Z3/10_Witness_Generation_Automata.ipynb (cell 1)

set -euo pipefail

# ---------------------------------------------------------------------------
# Colors (disabled when stdout is not a TTY)
# ---------------------------------------------------------------------------
if [[ -t 1 ]]; then
  C_GREEN=$'\033[32m'; C_YELLOW=$'\033[33m'; C_RED=$'\033[31m'
  C_CYAN=$'\033[36m'; C_GRAY=$'\033[90m'; C_RESET=$'\033[0m'
else
  C_GREEN=""; C_YELLOW=""; C_RED=""; C_CYAN=""; C_GRAY=""; C_RESET=""
fi

# ---------------------------------------------------------------------------
# Args: [SubmoduleDir] [Configuration] [--force]
# ---------------------------------------------------------------------------
FORCE=0
SUBMODULE_DIR=""
CONFIGURATION="Release"
for arg in "$@"; do
  case "$arg" in
    --force|-f) FORCE=1 ;;
    Release|Debug) CONFIGURATION="$arg" ;;
    -h|--help) sed -n '20,30p' "$0"; exit 0 ;;
    *) SUBMODULE_DIR="$arg" ;;
  esac
done

# Auto-detect submodule dir relative to this script (3 levels up from
# scripts/environment/), mirroring the .ps1 default.
if [[ -z "$SUBMODULE_DIR" ]]; then
  SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  SUBMODULE_DIR="$SCRIPT_DIR/../../MyIA.AI.Notebooks/SymbolicAI/SMT/Automata"
fi

printf '%s=== Automata Fork Build for CoursIA SymbolicAI ===%s\n' "$C_CYAN" "$C_RESET"

# --- locate submodule + csproj ---------------------------------------------------------
if [[ ! -d "$SUBMODULE_DIR" ]]; then
  printf '%sERROR: submodule dir not found: %s%s\n' "$C_RED" "$SUBMODULE_DIR" "$C_RESET"
  printf '  Did you clone with --recurse-submodules? Run:\n'
  printf '    git submodule update --init --recursive\n'
  exit 1
fi
SUBMODULE_DIR="$(cd "$SUBMODULE_DIR" && pwd)"
CSPROJ="$SUBMODULE_DIR/src/Automata/Automata.csproj"
DEPLOY_DIR="$SUBMODULE_DIR/.deploy"

if [[ ! -f "$CSPROJ" ]]; then
  printf '%sERROR: Automata.csproj not found at: %s%s\n' "$C_RED" "$CSPROJ" "$C_RESET"
  printf '  Did you clone with --recurse-submodules? Run:\n'
  printf '    git submodule update --init --recursive\n'
  exit 1
fi

printf '%sSubmodule : %s%s\n' "$C_GRAY" "$SUBMODULE_DIR" "$C_RESET"
printf '%sProject   : %s%s\n' "$C_GRAY" "$CSPROJ"        "$C_RESET"
printf '%sOutput    : %s%s\n' "$C_GRAY" "$DEPLOY_DIR"    "$C_RESET"

# --- dotnet SDK precondition (installable everywhere, rule F) -------------------------
if ! command -v dotnet >/dev/null 2>&1; then
  printf '%sERROR: dotnet SDK not found on PATH.%s\n' "$C_RED" "$C_RESET"
  printf '  Install .NET 8.0+ SDK from https://dotnet.microsoft.com/download\n'
  exit 1
fi

# --- idempotency check -----------------------------------------------------------------
# .deploy/ is complete when both required DLLs are present.
REQUIRED_DLLS=("Microsoft.Automata.dll" "System.CodeDom.dll")
if [[ -d "$DEPLOY_DIR" && $FORCE -eq 0 ]]; then
  missing=()
  for dll in "${REQUIRED_DLLS[@]}"; do
    [[ -f "$DEPLOY_DIR/$dll" ]] || missing+=("$dll")
  done
  if [[ ${#missing[@]} -eq 0 ]]; then
    printf '%s.deploy/ already complete (2 DLLs present). Use --force to rebuild.%s\n' "$C_GREEN" "$C_RESET"
    exit 0
  fi
fi

# --- build the csproj ------------------------------------------------------------------
printf '%sBuilding Automata fork (%s)...%s\n' "$C_CYAN" "$CONFIGURATION" "$C_RESET"
build_log="$(mktemp)"
if ! dotnet build "$CSPROJ" -c "$CONFIGURATION" --nologo >"$build_log" 2>&1; then
  printf '%sERROR: dotnet build failed.%s\n' "$C_RED" "$C_RESET"
  grep -iE "error|erreur" "$build_log" | sed 's/^/  /'
  rm -f "$build_log"
  exit 1
fi
# Surface the success / target lines (quiet otherwise).
grep -iE "succeeded|réussi|->" "$build_log" | sed "s/^/${C_GRAY}  /;s/$/${C_RESET}/" || true
rm -f "$build_log"

BUILD_OUT="$SUBMODULE_DIR/src/Automata/bin/$CONFIGURATION/net8.0"
BUILT_DLL="$BUILD_OUT/Microsoft.Automata.dll"
if [[ ! -f "$BUILT_DLL" ]]; then
  printf '%sERROR: build succeeded but Microsoft.Automata.dll not found at %s%s\n' "$C_RED" "$BUILD_OUT" "$C_RESET"
  exit 1
fi

# Sanity: confirm the fork core (CharSetSolver) is in the built DLL.
# (`grep -a` treats the binary as text; CharSetSolver is an ASCII symbol name.)
if ! grep -aq "CharSetSolver" "$BUILT_DLL"; then
  printf '%sWARNING: built Microsoft.Automata.dll lacks CharSetSolver — is the submodule at the fork commit?%s\n' "$C_YELLOW" "$C_RESET"
  printf '  Expected commit 4a7b7f0 (MyIntelligenceAgency/Automata, surface &/~ + uncapped witness).\n'
else
  printf '%s  CharSetSolver present (fork core OK).%s\n' "$C_GREEN" "$C_RESET"
fi

# --- prepare .deploy/ ------------------------------------------------------------------
rm -rf "$DEPLOY_DIR"
mkdir -p "$DEPLOY_DIR"

# 1. the fork assembly from the local build output
cp -f "$BUILT_DLL" "$DEPLOY_DIR/"

# 2. managed dependency from the NuGet package cache.
#    System.CodeDom is the single external managed dependency (see deps.json). A
#    dotnet build of a library does not copy managed deps into bin/ (resolved at
#    runtime via deps.json), but #r path-loads in a notebook need it on disk.
#    NuGet cache is cross-platform: $HOME/.nuget/packages (NUGET_PACKAGES overrides).
NUGET_ROOT="${NUGET_PACKAGES:-$HOME/.nuget/packages}"
if [[ ! -d "$NUGET_ROOT" ]]; then
  printf '%sERROR: NuGet package cache not found at %s%s\n' "$C_RED" "$NUGET_ROOT" "$C_RESET"
  printf '  (run the build once to restore packages, or set NUGET_PACKAGES)\n'
  exit 1
fi

CODEDOM="$NUGET_ROOT/system.codedom/8.0.0/lib/net8.0/System.CodeDom.dll"
if [[ -f "$CODEDOM" ]]; then
  cp -f "$CODEDOM" "$DEPLOY_DIR/System.CodeDom.dll"
else
  printf '%sERROR: dependency not found in NuGet cache: %s%s\n' "$C_RED" "$CODEDOM" "$C_RESET"
  printf '  Run: dotnet restore %s  (then re-run this script)\n' "$CSPROJ"
  exit 1
fi

# --- verify ----------------------------------------------------------------------------
printf '\n%s=== .deploy/ contents ===%s\n' "$C_CYAN" "$C_RESET"
for dll in "$DEPLOY_DIR"/*.dll; do
  [[ -f "$dll" ]] || continue
  size_kb=$(( $(stat -c %s "$dll" 2>/dev/null || stat -f %z "$dll") / 1024 ))
  printf '%s  %-24s %8s KB%s\n' "$C_GRAY" "$(basename "$dll")" "$size_kb" "$C_RESET"
done

missing=()
for dll in "${REQUIRED_DLLS[@]}"; do
  [[ -f "$DEPLOY_DIR/$dll" ]] || missing+=("$dll")
done
if [[ ${#missing[@]} -gt 0 ]]; then
  printf '\n%sFAILED: missing DLLs: %s%s\n' "$C_RED" "${missing[*]}" "$C_RESET"
  exit 1
fi

printf '\n%s=== Automata fork build complete ===%s\n' "$C_GREEN" "$C_RESET"
printf '%s.deploy/ ready at: %s%s\n' "$C_CYAN" "$DEPLOY_DIR" "$C_RESET"
printf '\nNotebook 10 cell 1 should now resolve:\n'
printf '  %s#r "../Automata/.deploy/Microsoft.Automata.dll"%s\n' "$C_GRAY" "$C_RESET"
exit 0
