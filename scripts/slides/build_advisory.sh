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

# A deck dir is a top-level dir under SLIDES_DIR that is BOTH:
#  (1) NOT gitignored (a build output / local workdir present on disk but
#      ignored by git must not trip a false ERROR -- CASE 5 of #8926), and
#  (2) matching the NN/SN naming convention the gate uses (`^(S)?[0-9]`).
# This mirrors .github/workflows/slides-build-advisory.yml STRUCTURALLY: infra
# dirs (_assets, _tools, analysis, theme-ia101, themes, node_modules) do not
# match the convention and are excluded with no hand-maintained list to drift
# against the gate (#8926: the former NON_DECK_DIRS allowlist-inverted
# subtraction reproduced the pattern by hand and was guaranteed to diverge --
# the day an infra dir was added under slides/, the gate would keep ignoring
# it for free while this tool counted it as an empty deck dir -> false ERROR).
is_deck_dir() {
  local d="$1" name
  git check-ignore -q -- "$d" 2>/dev/null && return 1   # (1) git = authority on "ignored"
  name="$(basename "$d")"
  printf '%s' "$name" | grep -qE '^(S)?[0-9]'           # (2) gate convention (workflow L138)
}

# Deck dirs = top-level dirs under SLIDES_DIR matching the NN/SN convention
# (and not gitignored). Mirrors the gate's `slides/*/` + `^(S)?[0-9]` filter.
#
# Symmetric of trap 1 (#8929, cf gate workflow L138-155): a dir that does NOT
# match the convention but DOES carry a deck file is invisible to discovery
# -- a pre-flight `check` would pass green where the gate goes red. Because
# deck_dirs() feeds a process substitution (subshell), a probe side-effect set
# here could not reach the parent; the symmetric probe runs in check_denominator
# itself (where exit status is decided). deck_dirs() stays stdout-pure.
_warn_nonconvention_with_deck() {
  # Emit ERROR to stderr if $1 carries a deck; always returns 0 (set -e safe).
  local d="$1" dk has_deck=0
  [ -f "$d/slides.md" ] && has_deck=1
  for dk in "$d"/deck-*.md; do [ -f "$dk" ] && has_deck=1; done
  if [ "$has_deck" -eq 1 ]; then
    echo "ERROR: '$d' porte un deck (slides.md / deck-*.md) mais ne matche pas la" >&2
    echo "convention NN/SN -- invisible a la decouverte (symetrique du CASE A," >&2
    echo "cf gate workflow L138-155). Renommer le dir ou deplacer le deck." >&2
    return 1   # signals to the caller that a violation was found.
  fi
  return 0
}

deck_dirs() {
  local d
  for d in "$SLIDES_DIR"/*/; do
    [ -d "$d" ] || continue
    d="${d%/}"
    is_deck_dir "$d" || continue
    echo "$(basename "$d")"
  done | sort
}

# Discover every deck file (repo-relative), one per line, sorted.
# A deck is `slides.md` or `deck-*.md` directly under a convention deck dir.
# Like the gate (workflow L158-172), we glob the deck dir's direct children --
# there is no sub-path exclusion list because a top-level NN/SN dir's direct
# child cannot be under archive/analysis/_assets (those are peer infra dirs,
# already excluded by is_deck_dir). A deck author running `build_advisory.sh
# check` before pushing thus sees the same inventory the PR gate computes.
discover_decks() {
  local d dk
  for d in "$SLIDES_DIR"/*/; do
    [ -d "$d" ] || continue
    d="${d%/}"
    is_deck_dir "$d" || continue
    if [ -f "$d/slides.md" ]; then
      echo "$d/slides.md"
    fi
    for dk in "$d"/deck-*.md; do
      [ -f "$dk" ] || continue
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

  # Symmetric of trap 1 (#8929, cf gate workflow L138-155): a dir that does NOT
  # match the NN/SN convention but DOES carry a deck is invisible to discovery.
  # Ran in THIS parent (not in deck_dirs()'s subshell) so the finding can drive
  # the exit status. `if ... ; then rc=1; fi` is the set -e safe form (a bare
  # `[ ] && ` at end-of-list would abort the loop on the first infra dir).
  local symtrap=0 sdir
  for sdir in "$SLIDES_DIR"/*/; do
    [ -d "$sdir" ] || continue
    sdir="${sdir%/}"
    if is_deck_dir "$sdir"; then
      continue
    fi
    if ! _warn_nonconvention_with_deck "$sdir"; then
      symtrap=1
    fi
  done

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
    echo "deck — rename it so it does not match the NN/SN convention (the gate"
    echo "excludes non-convention dirs structurally; see is_deck_dir)."
    return 1
  fi
  if [ "$symtrap" -eq 1 ]; then
    # ERROR(s) already printed to stderr by _warn_nonconvention_with_deck.
    echo "Denominator check: FAIL (a non-convention dir carries a deck -> invisible to discovery, #8929)."
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
