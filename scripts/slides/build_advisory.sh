#!/usr/bin/env bash
# Advisory Slidev build gate — discovery + denominator check + build.
#
# Issue #8817: the organ that was missing when 5/16 decks did not build for
# months. This script makes the inventory self-checking: a deck dir that the
# `slides.md` heuristic silently skips now fails LOUDLY, and every deck the PR
# touches is actually built.
#
# It is advisory by design: it never fails the job on a build break — that
# signal is the GitHub LABEL applied by the workflow (see criterion #5 of #8817:
# "le signal est le LABEL, jamais la conclusion du job"). The only thing this
# script fails hard on is a denominator mismatch (a tracked deck dir with zero
# discovered decks), because that is precisely the silent-skip failure mode.
#
# Usage:
#   build_advisory.sh check                 # inventory + denominator check (no build)
#   build_advisory.sh build --all           # build every discovered deck
#   build_advisory.sh build <deck>...       # build specific decks (repo-relative paths)
#
# Env:
#   SLIDES_DIR      slides workspace (default: slides)
#   SLIDEV_BIN      slidev invocation (default: npx --no-install slidev)
#
# Exit codes:
#   0  check passed / all requested decks built OK
#   1  denominator mismatch OR at least one build failed
#   2  usage error
set -euo pipefail

SLIDES_DIR="${SLIDES_DIR:-slides}"
SLIDEV_BIN="${SLIDEV_BIN:-npx --no-install slidev}"

# Top-level entries under slides/ that are NOT decks.
# Kept as an explicit allowlist-inverted list so a new deck dir is covered by
# default; a new non-deck dir must be added here (and the denominator check
# will remind you, since it would otherwise count it as an empty deck dir).
NON_DECK_DIRS="_assets _tools analysis node_modules node_modules.cache theme-ia101 themes"

is_non_deck() {
  local d="$1"
  local x
  for x in $NON_DECK_DIRS; do [ "$d" = "$x" ] && return 0; done
  return 1
}

# Deck dirs = top-level dirs under SLIDES_DIR that are actual decks.
deck_dirs() {
  local d name
  for d in "$SLIDES_DIR"/*/; do
    [ -d "$d" ] || continue
    d="${d%/}"
    name="$(basename "$d")"
    is_non_deck "$name" && continue
    echo "$name"
  done | sort
}

# Discover every deck file (repo-relative), one per line, sorted.
# A deck is `slides.md` or `deck-*.md`, NOT under an `archive/`/`analysis/`/
# `_assets/` subdir. The exclusion set mirrors the `case` in the canonical CI
# gate `.github/workflows/slides-build-advisory.yml` so this local tool and the
# gate agree on what is a deck — a deck author running `build_advisory.sh check`
# before pushing sees the same inventory the PR gate will compute
# (review nit #8868: the two had drifted — shell excluded only archive/).
discover_decks() {
  local d name dk
  for d in "$SLIDES_DIR"/*/; do
    [ -d "$d" ] || continue
    d="${d%/}"
    name="$(basename "$d")"
    is_non_deck "$name" && continue
    if [ -f "$d/slides.md" ]; then
      case "$d/slides.md" in */archive/*|*/analysis/*|*/_assets/*) continue ;; esac
      echo "$d/slides.md"
    fi
    for dk in "$d"/deck-*.md; do
      [ -f "$dk" ] || continue
      case "$dk" in
        */archive/*|*/analysis/*|*/_assets/*) continue ;;
      esac
      echo "$dk"
    done
  done | sort
}

check_denominator() {
  # Capture the deck list ONCE into an array and derive covered-dirs from it.
  # (A per-iteration `discover_decks | grep` re-globs every time and, under
  #  pipefail/errexit, can truncate the stream — an intermittent false
  #  negative that flagged a different dir each run. Single capture is
  #  deterministic.)
  local -a decks=() dirs=() empty=()
  local deck d deckdir covered=0
  while IFS= read -r deck; do decks+=("$deck"); done < <(discover_decks)
  while IFS= read -r d; do dirs+=("$d"); done < <(deck_dirs)
  local ndecks=${#decks[@]} ndirs=${#dirs[@]}

  # M=0 refusal (#8817 trap 1, cf CASE C): an empty discovery is the signature
  # of a mass rename or a broken glob — the check REFUSES to assert "all
  # covered" when there is nothing to cover. When N>0 the empty[] loop below
  # already fails; this guard closes the N==0 vacuous-truth hole (0/0 dirs) and
  # makes the M=0 failure explicit regardless of N.
  if [ "$ndecks" -eq 0 ]; then
    echo "=== Slidev deck inventory (#8817) ==="
    echo "Deck dirs tracked:   ${ndirs}"
    echo "Decks discovered:    0"
    echo
    echo "ERROR: ZERO decks discovered (M=0). This is the mass-rename / broken-"
    echo "discovery signature — the check refuses to assert coverage on an empty"
    echo "inventory. Restore a slides.md / deck-*.md, or set SLIDES_DIR correctly."
    return 1
  fi

  local -A covered_dirs=()
  for deck in "${decks[@]}"; do
    deckdir="${deck#"${SLIDES_DIR}"/}"   # <dir>/<file>
    deckdir="${deckdir%%/*}"             # <dir>
    covered_dirs["$deckdir"]=1
  done

  for d in "${dirs[@]}"; do
    if [ "${covered_dirs[$d]:-0}" = 1 ]; then
      covered=$((covered + 1))
    else
      empty+=("$d")
    fi
  done

  echo "=== Slidev deck inventory (#8817) ==="
  echo "Deck dirs tracked:   ${ndirs}"
  echo "Decks discovered:    ${ndecks}"
  echo "Dirs with >=1 deck:  ${covered} / ${ndirs}"

  if [ "${#empty[@]}" -gt 0 ]; then
    echo
    echo "ERROR: deck dir(s) with ZERO decks discovered (silent-skip risk):"
    printf '  - %s\n' "${empty[@]}"
    echo
    echo "Either add a slides.md / deck-*.md under the dir, or — if it is not a"
    echo "deck — add it to NON_DECK_DIRS in scripts/slides/build_advisory.sh."
    return 1
  fi
  echo "Denominator check: PASS (every tracked deck dir has >=1 deck)."
}

build_deck() {
  local deck="$1" rel out
  rel="${deck#${SLIDES_DIR}/}"          # path relative to slides/ (e.g. 01-introduction/slides.md)
  out="_advisory_dist/$(printf '%s' "$rel" | tr '/' '__')"

  # Rebuild after any markup crash: Rollup stops at the first crash, so a
  # green rebuild (not a single error lifted) is the only proof of repair
  # (#8817 pitfall #2).
  echo "--- Building: ${deck} ---"
  if ( cd "$SLIDES_DIR" && $SLIDEV_BIN build "$rel" --out "../${out}" --base "/${out}/" ) >/tmp/slidev_build.log 2>&1; then
    echo "OK:   ${deck}"
    return 0
  else
    echo "FAIL: ${deck}"
    echo "----- slidev build log (tail) -----"
    tail -n 40 /tmp/slidev_build.log || true
    echo "-----------------------------------"
    return 1
  fi
}

main() {
  local cmd="${1:-}"
  case "$cmd" in
    check)
      check_denominator
      ;;
    build)
      shift
      local -a targets=()
      if [ "${1:-}" = "--all" ]; then
        while IFS= read -r line; do targets+=("$line"); done < <(discover_decks)
      else
        targets=("$@")
      fi
      if [ "${#targets[@]}" -eq 0 ]; then
        echo "No decks to build (PR touches no deck file). Running denominator check only."
        check_denominator
        return $?
      fi
      check_denominator || return 1
      echo
      echo "Building ${#targets[@]} deck(s)..."
      local rc=0 deck
      for deck in "${targets[@]}"; do
        build_deck "$deck" || rc=1
      done
      echo
      if [ "$rc" -eq 0 ]; then
        echo "RESULT: all ${#targets[@]} deck(s) built OK."
      else
        echo "RESULT: at least one deck FAILED to build (advisory — see workflow label)."
      fi
      return "$rc"
      ;;
    *)
      echo "Usage: $0 {check|build [--all|<deck>...]}" >&2
      return 2
      ;;
  esac
}

main "$@"
