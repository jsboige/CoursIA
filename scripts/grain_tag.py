#!/usr/bin/env python3
"""Shared `Grain:` tag extractor (variation-protocol §1, fix #9485).

THE single reader of the `Grain: <TIER>/<GENRE> -- lane <machine:workspace>`
tag, AND of the short-header trio `Quoi: / Preuve: / Perimetre:` introduced
by issue #9861 (one-line answers to "what does this PR change?", "what
attests it?", "what does it touch? -- and what is explicitly out of scope?").

Consumed by:

  - scripts/variation_light_cap.py  (G-VAR-2 organ, via import)
  - .github/workflows/variation-tag-guard.yml (CI guard, via CLI `--check-body`)

#9485 -- why this module exists. The guard (bash `grep '^Grain:'`) and the
organ (Python `Grain:\\s*`) were TWO divergent implementations, and BOTH
required the colon form. A body titled `## Grain` with the tag on the next
line matched NEITHER: 38% of the 2026-08-05 merges were invisible to the
G-VAR-2 cap (counted in no lane's numerator nor denominator). This module
unifies the two readers and tolerates the observed presentational variants,
WITHOUT tolerating the absence of substance: a body with no `<TIER>/<GENRE>`
anywhere still returns None (the guard keeps flagging `variation-tag-missing`).

Recognised forms (after markdown noise -- * ` # > -- is stripped):
    Grain: LIGHT/guard -- lane myia-po-2023:CoursIA       (canonical)
    **Grain:** LIGHT/guard - lane ...                     (bold)
    ## Grain\n\nLIGHT/guard ... lane ...                  (title + next line)
    `Grain` LIGHT/guard ...                               (no colon)
    **Grain** : DEEP/research-code -- ...                 (bold, space before :)
    lane declared elsewhere: `**Lane** : myia-...`        (extracted independently)

#9861 -- short-header trio (added in the same module, same source-of-truth
discipline). Each key is a single line, anywhere after the Grain tag:

    Quoi:       <one-line -- what the PR changes>
    Preuve:     <one-line -- command or run that attests it>
    Perimetre:  <one-line -- files/domain touched, and what is explicitly
                         out of scope>

Tolerant to bold (`**Quoi** :`), case, and extra whitespace. The trio is
**advisory** at first: the guard flags `variation-short-header-missing` only
when ALL THREE are absent (so existing PRs do not suddenly turn red the day
the convention is rolled out). Hardening to "1 absent = flag" is a separate
gate, after the convention has spread.

`parse_short_header` returns {quoi, preuve, perimetre} (each | None).
`parse_grain_tag` is unchanged (back-compat for the variation_light_cap organ).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# --- noise ------------------------------------------------------------------
#
# Markdown decoration that wraps or prefixes the tag in the wild. Stripped
# before matching so the regex sees a clean `Grain TIER/GENRE ... lane mw`.
# Two kinds of noise:
#
#   - **Inline decoration** (`*`, `` ` ``, `>`): stripped GLOBALLY. These are
#     visual wrappers around tokens -- `**Grain** : DEEP/lean` becomes
#     `Grain : DEEP/lean` after the strip, and the regex matches. Stripping
#     them globally is safe because they do not appear inside literal values
#     (a `#` in `#9861` is NOT decoration, it is a GitHub issue reference).
#
#   - **Line-leading title hashes** (`## Grain`, `### Grain`): stripped ONLY
#     on a line that begins with hash(es) followed by `Grain` (or any of the
#     short-header keys). This is what `## Grain` needs to read as `Grain` so
#     the next line can carry the tag. Stripping `#` GLOBALLY would BREAK
#     issue references (`#9861` -> `9861`) and the test suite caught it:
#     the short-header trio is supposed to capture `Quoi: fix for #9861`
#     verbatim, not `Quoi: fix for 9861`. The fix is to strip `#` only at
#     the start of a line that begins with one or more `#` followed by a
#     recognised key word -- see `_strip_title_hashes` below.
_NOISE = str.maketrans({"*": "", "`": "", ">": ""})

# Words that, when they appear at the start of a line after one or more `#`,
# justify stripping the title hashes. Anything else (an `#` mid-line, an
# `#` in `Quoi: fix #9861`) is preserved.
_TITLE_HASH_WORDS = ("Grain", "Quoi", "Preuve", "Perimetre", "Lane")
# Compiled once: `^#+\s*<word>\b` in multiline mode. The lookahead
# `(?=...)` does NOT consume the key word -- it only confirms the line
# looks like a title, then `_strip_title_hashes` cuts the line BEFORE
# the key word so the regex (`_GRAIN_FULL_RE` etc.) still sees it.
# Without the lookahead, `m.end()` would be AFTER the key word and the
# strip would delete the tag itself, breaking the title-form tests.
_TITLE_LINE_RE = re.compile(
    r"^[ \t]*#+\s*(?=" + "|".join(_TITLE_HASH_WORDS) + r")\b",
    re.IGNORECASE | re.MULTILINE,
)


def _strip_title_hashes(flat: str) -> str:
    """Strip line-leading `##` only on lines that begin with a recognised key.

    Splitting into lines is cheap and gives us byte-level control: a line
    that starts with `#` followed by `Grain` / `Quoi` / `Preuve` / `Perimetre`
    / `Lane` has its `#` chars removed (the KEY WORD IS PRESERVED -- the
    earlier prototype deleted the key too, which broke `## Grain` lookup
    for tests `test_title_form_hash_grain_next_line` / `_h3_grain`); every
    other line is kept intact, including `#` in the middle (issue references,
    code spans, etc.).
    """
    out_lines = []
    for line in flat.splitlines():
        m = _TITLE_LINE_RE.match(line)
        if m:
            # Drop ONLY the leading whitespace + `#` chars + whitespace
            # between them, KEEP the recognised key word. Concretely:
            # `## Grain` -> `Grain` ; `### Quoi: ...` -> `Quoi: ...`.
            # The `\s*` after the `#` group (in the regex) consumes the
            # leading whitespace before the key word; the key word itself
            # is matched but NOT consumed (lookahead via the alternation:
            # we use the END of the key word -- `m.end()` -- as the cut).
            # But the regex above consumes the whitespace before the key,
            # not the key itself. So `m.end()` is the position right after
            # the leading whitespace, which is exactly the start of the
            # key word -- exactly what we want to keep.
            out_lines.append(line[m.end():])
        else:
            out_lines.append(line)
    return "\n".join(out_lines)

# --- extraction -------------------------------------------------------------

# `Grain` then an OPTIONAL colon and any whitespace (incl. newlines), then
# TIER / GENRE. The `[:\\s]*` is the whole #9485 fix in one atom: it accepts
# `Grain:`, `Grain `, `Grain\\n\\n`, `Grain :` (space then colon). TIER is the
# alphabetic word before `/`; GENRE is the token after (letters, digits, _,-).
_GRAIN_FULL_RE = re.compile(
    r"Grain[:\s]*([A-Za-z]+)\s*/\s*([A-Za-z0-9_-]+)", re.IGNORECASE
)

# `lane` (case-insensitive), optional whitespace, optional colon, whitespace,
# then machine:workspace. Tolerates `lane:`, `lane :`, `lane ` (no colon),
# and `**Lane** :` (after `*` is stripped -> `Lane :`). The lane is structural
# (the worker's workspace) and may sit anywhere in the body -- extracted
# independently of the Grain line (#9485 point 4).
_LANE_RE = re.compile(
    r"lane\s*:?\s+([A-Za-z0-9._-]+:[A-Za-z0-9._-]+)", re.IGNORECASE
)

# `prev` (case-insensitive), optional colon, whitespace, then the SAME
# TIER/GENRE pair as the leading tag. The `prev:` field traces genre
# adjacency (variation-protocol.md §1) and carries a PR reference right
# after the genre (`prev: MED/refactor #1234 (c.42)`). #10093 -- GitHub
# parses a `prev:` whose GENRE is a closing keyword (`fix #1234`) as an
# auto-close instruction when the text lands in a commit message: a
# squash-merge of #10063 closed #10067 (unintended) this way. The 14
# canonical genres contain NO closing keyword, so a closing-keyword genre
# in `prev:` is ALWAYS a misuse (use `refactor`/`guard`/`tooling`).
_PREV_RE = re.compile(
    r"prev\s*:?\s*([A-Za-z]+)\s*/\s*([A-Za-z0-9_-]+)", re.IGNORECASE
)

# GitHub auto-close keywords (case-insensitive) -- the exact set GitHub
# recognises in commit messages + PR bodies + PR titles
# (https://docs.github.com/en/issues/tracking-your-work-with-issues/using-issues/linking-a-pull-request-to-an-issue).
# A `prev:` genre drawn from this set makes the `genre #N` tail an
# unintended close instruction. Source of truth for the close-keyword gate.
CLOSING_KEYWORDS = frozenset({
    "close", "closes", "closed",
    "fix", "fixes", "fixed",
    "resolve", "resolves", "resolved",
})


def find_prev_close_keywords(text: str | None) -> list[dict]:
    r"""Return `prev:` fields whose genre is a GitHub closing keyword (#10093).

    Scans any text (a PR body OR a commit message) for `prev: <TIER>/<genre>`
    where `<genre>` is one of the 9 GitHub auto-close keywords
    (`CLOSING_KEYWORDS`). Each hit is a `prev:` whose `genre #N` tail GitHub
    parses as a close instruction when the text lands in a commit message --
    the silent-PR-closure failure mode of #10093.

    The 14 canonical genres (variation-protocol.md §1) contain NO closing
    keyword, so a closing-keyword genre in `prev:` is ALWAYS a misuse: the
    worker meant `refactor`, `guard`, `tooling`, etc. -- never `fix`. This
    function does NOT flag a standalone ``Fixes #123`` (an intended close):
    it only flags the genre slot of a `prev:` field, where a closing word
    is structurally wrong, not intended.

    Same noise discipline as ``parse_grain_tag``: bold/backticks/blockquotes
    stripped, title hashes stripped on recognised key lines. Returns a list
    of ``{"tier", "genre"}`` dicts (one per offending `prev:` field, empty
    when the text is clean).
    """
    if not text:
        return []
    flat = _strip_title_hashes(text.translate(_NOISE))
    hits = []
    for m in _PREV_RE.finditer(flat):
        genre = m.group(2).lower()
        if genre in CLOSING_KEYWORDS:
            hits.append({"tier": m.group(1).upper(), "genre": genre})
    return hits


def parse_grain_tag(body: str | None) -> dict | None:
    """Extract {tier, genre, lane} from a PR body, form-tolerant.

    Returns None when no `Grain <TIER>/<GENRE>` can be read anywhere -- the
    signal that the guard must flag `variation-tag-missing`. `lane` is None
    when the body carries no `lane <machine:workspace>` token at all -- the
    signal that the guard must flag `variation-tag-lane-missing` (and the
    organ leaves the PR unattributed, never guessing a lane).
    """
    if not body:
        return None
    flat = _strip_title_hashes(body.translate(_NOISE))
    m = _GRAIN_FULL_RE.search(flat)
    if not m:
        return None
    lane_m = _LANE_RE.search(flat)
    return {
        "tier": m.group(1).upper(),
        "genre": m.group(2).lower(),
        "lane": lane_m.group(1) if lane_m else None,
    }


def extract_lane(body: str | None) -> str | None:
    """Extract the `<machine>:<workspace>` lane token from any text.

    Same reader as `parse_grain_tag` (the single lane extractor, #9485): shared
    by the Grain tag, the G-VAR-2 organ, and -- via `check_lane_claim` (#9774) --
    by the lane-claim guard. A `[CLAIMED] lane myia-po-2024:CoursIA -- ...`
    comment is not a Grain tag (it carries no `Grain TIER/GENRE`), so it cannot
    go through `parse_grain_tag`; this wrapper reuses the exact same compiled
    `_LANE_RE` so the two contexts never drift on what a lane token is.

    Returns the `machine:workspace` string, or None when the body carries no
    `lane <machine:workspace>` token.
    """
    if not body:
        return None
    flat = _strip_title_hashes(body.translate(_NOISE))
    m = _LANE_RE.search(flat)
    return m.group(1) if m else None


# --- short-header trio (#9861) ----------------------------------------------
#
# The convention (per #9861): just after the Grain tag, three one-line answers
# in this exact shape:
#
#     Quoi:       <one line -- what the PR changes>
#     Preuve:     <one line -- command or run that attests it>
#     Perimetre:  <one line -- files/domain touched + explicit out-of-scope>
#
# The detailed body below stays authorised and welcome (audit value) -- the
# goal is NOT to censor the argument, it is to guarantee the reviewer finds
# those three answers AT THE TOP, in three lines. The trio is advisory at
# rollout (issue spec: "rougit sur une PR dont le body n'a pas les trois
# cles"), so we flag `variation-short-header-missing` only when ALL THREE
# are absent -- existing PRs that have none of the three keys still pass,
# so the convention spreads without churn. Hardening to "1 absent = flag"
# is a separate decision, taken when the fleet has adopted the convention.
#
# Same noise discipline as `_GRAIN_FULL_RE` / `_LANE_RE`: bold (`**`), backticks
# (`` ` ``), title hashes (`#`), blockquotes (`>`) are stripped BEFORE matching.
# Tolerates `Quoi:`, `Quoi :`, `**Quoi** :`, `Quoi ` (no colon -- rare but seen
# in the wild; matches anything after the key word + at least one whitespace
# before the value).
_SHORT_HEADER_KEYS = ("Quoi", "Preuve", "Perimetre")

# One regex per key: word + optional colon + whitespace + captured value (rest
# of the line). Compiled once, reused. The value is captured non-greedily until
# the line end, which keeps the trio on a single line per key (#9861: "une
# ligne"). Multi-line values would need a different design; the issue rejects
# that explicitly ("juste apres le tag Grain: un en-tete court normalise").
_SHORT_HEADER_RES = {
    k: re.compile(rf"{k}\s*:?\s+(.+?)\s*$", re.IGNORECASE)
    for k in _SHORT_HEADER_KEYS
}


def parse_short_header(body: str | None) -> dict:
    """Extract the {Quoi, Preuve, Perimetre} short-header trio (#9861).

    Each key is independent: a body can carry one, two, or all three -- the
    caller decides what to do with the partial coverage. The CI guard
    (`check-short-header` job in `variation-tag-guard.yml`) flags a PR only
    when **all three are absent**, by design (existing PRs have none of the
    three and must not suddenly turn red).

    Each value is stripped of leading/trailing whitespace. The keys themselves
    are case-insensitive (matched after the noise strip, which lower-cases
    nothing but removes decoration). Returns {quoi, preuve, perimetre} with
    each entry `None` when the key is absent and the captured text otherwise.

    The body is treated as already-presented markdown: leading/trailing
    whitespace and the noise (bold, backticks, hashes, blockquotes) are
    handled by translating through `_NOISE` first, exactly like
    `parse_grain_tag`.
    """
    out: dict[str, str | None] = {k.lower(): None for k in _SHORT_HEADER_KEYS}
    if not body:
        return out
    flat = _strip_title_hashes(body.translate(_NOISE))
    # Scan line-by-line. A trio key on the same line as the Grain tag would
    # be a structural oddity; the convention in #9861 puts each on its own
    # line just after the Grain tag, and that is what we match. Multi-line
    # values are explicitly excluded by the spec ("une ligne -- ...").
    for line in flat.splitlines():
        line = line.strip()
        if not line:
            continue
        # Each key MUST be at the start of the line (after strip). Anchored
        # to prevent false positives where a body says e.g. "We discuss Quoi:
        # the convention here" mid-paragraph -- that is commentary, not a
        # canonical answer. The convention #9861 is "juste apres le tag Grain:
        # un en-tete court normalise" -- three lines, one key per line.
        for k in _SHORT_HEADER_KEYS:
            # Cheap prefix check before the regex: skips the regex engine
            # on every line that does not start with the key word.
            if not line.lower().startswith(k.lower()):
                continue
            m = _SHORT_HEADER_RES[k].search(line)
            if m:
                # First hit wins per key. If a body carries the key twice, the
                # first is the canonical answer; later mentions are commentary.
                if out[k.lower()] is None:
                    out[k.lower()] = m.group(1).strip()
    return out


# --- CLI (guard consumer) ---------------------------------------------------

# The §1 enumeration is the guard's business (which labels to pose), not the
# extractor's. The extractor reports WHAT it read; the guard decides if it is
# admissible. Kept here only so `--check-body` can emit a convenience flag for
# the bash, which would otherwise re-implement the case statement.
TIERS = ("DEEP", "MED", "LIGHT")
GENRES = (
    "lean", "qc", "training", "genai", "notebook-python", "notebook-dotnet",
    "docs", "guard", "refactor", "ledger", "readme", "test", "tooling",
    "research-code",
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Read a Grain tag from a PR body (shared extractor, #9485)."
    )
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--body", metavar="TEXT", help="the PR body inline")
    src.add_argument("--body-file", metavar="FILE", help="path to the PR body")
    args = p.parse_args(argv)

    body = args.body if args.body is not None else Path(args.body_file).read_text(
        encoding="utf-8"
    )
    g = parse_grain_tag(body)
    # Short-header trio (#9861) is parsed independently of the Grain tag: a
    # body can carry it (or part of it) even when the Grain tag is absent.
    # The guard reads both and applies separate labels.
    sh = parse_short_header(body)
    short_complete = all(sh[k] is not None for k in ("quoi", "preuve", "perimetre"))
    # `prev:` close-keyword scan (#10093): runs on the body the same way the
    # blocking job runs on commit messages. Reported as a field so the
    # advisory job can label without re-implementing the scan.
    prev_hits = find_prev_close_keywords(body)
    if g is None:
        # No TIER/GENRE anywhere: the one substance the protocol will not
        # relax. The guard poses `variation-tag-missing`. Short-header is
        # reported anyway (its own job consumes it).
        print(json.dumps({"present": False, "tier": None, "genre": None,
                          "lane": None, "tier_valid": False, "genre_valid": False,
                          "quoi": sh["quoi"], "preuve": sh["preuve"],
                          "perimetre": sh["perimetre"],
                          "short_header_complete": short_complete,
                          "prev_close_keyword_hits": prev_hits}))
        return 0
    tier_valid = g["tier"] in TIERS
    genre_valid = g["genre"] in GENRES
    print(json.dumps({
        "present": True,
        "tier": g["tier"],
        "genre": g["genre"],
        "lane": g["lane"],
        "tier_valid": tier_valid,
        "genre_valid": genre_valid,
        "quoi": sh["quoi"],
        "preuve": sh["preuve"],
        "perimetre": sh["perimetre"],
        "short_header_complete": short_complete,
        "prev_close_keyword_hits": prev_hits,
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
