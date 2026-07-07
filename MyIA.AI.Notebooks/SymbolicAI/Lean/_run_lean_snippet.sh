#!/bin/bash
# Helper: run a Lean snippet against a backing Lake project's cached Mathlib oleans.
# Used by Lean-13 Grothendieck notebook to display Mathlib excerpts via #check.
# Invoked from WSL.
#
# Usage: bash _run_lean_snippet.sh <lean_file>
# Env:   LEAN_BACKING_PROJECT (default: sensitivity_lean)
set -u
SNIPPET="${1:-}"
if [ -z "$SNIPPET" ]; then
  echo "Usage: $0 <lean_file>" >&2
  exit 2
fi

# Resolve backing project dynamically: search upward from script location
_script_dir="$(cd "$(dirname "$0")" && pwd)"
_default_project=""

# Walk up from script dir to find sensitivity_lean
_search="$_script_dir"
for _ in $(seq 1 12); do
  _candidate="$_search/sensitivity_lean"
  if [ -d "$_candidate" ] && [ -f "$_candidate/lakefile.lean" ]; then
    _default_project="$_candidate"
    break
  fi
  _search="$(dirname "$_search")"
  [ "$_search" = "/" ] && break
done

CW="${LEAN_BACKING_PROJECT:-${_default_project:-/mnt/c/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean}}"
cd "$CW" || exit 3

# Build LEAN_PATH from cached oleans (deps first, mathlib last)
PATHS=()
for pkg in batteries Qq aesop importGraph LeanSearchClient plausible proofwidgets Cli mathlib; do
  D="$CW/.lake/packages/$pkg/.lake/build/lib/lean"
  if [ -d "$D" ]; then
    PATHS+=("$D")
  fi
done
LP=$(IFS=:; echo "${PATHS[*]}")
export LEAN_PATH="$LP"

if [ -f ~/.elan/env ]; then
  source ~/.elan/env 2>/dev/null || true
fi

# Pinned toolchain from the backing project
LEAN_TOOLCHAIN_FILE="$CW/lean-toolchain"
if [ -f "$LEAN_TOOLCHAIN_FILE" ]; then
  LEAN_TOOLCHAIN=$(cat "$LEAN_TOOLCHAIN_FILE" | tr -d '\n\r ')
else
  LEAN_TOOLCHAIN="leanprover/lean4:v4.31.0-rc1"
fi

elan run "$LEAN_TOOLCHAIN" lean "$SNIPPET" 2>&1
