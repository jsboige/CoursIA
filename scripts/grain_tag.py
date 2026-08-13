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

Tolerant to bold (`**Quoi** :`), case, and extra whitespace. c.10330 / PR
retired the `check-short-header` CI job that labelled `variation-short-header-missing`
on 69 % of PRs without the convention ever being promulgated in the harness
(#10330). The parser stays in place (pure function, no cost when no caller
invokes it); a future convention rollout would re-cable a job and pair it
with a harnais rule.

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

# Fallback lane token for claim comments that omit the `lane` keyword (#10395
# Variante 1). The repository has `scripts/check_lane_claim.py` parsers, and
# the historical dashboards had legitimate forms like
# `[CLAIMED] #9764 - myia-po-2025:CoursIA 2026-08-07T00:52Z`. Requiring the
# literal `lane` token made those claims invisible (counted as unattributed),
# and the reducer then blocked the author on its own issue. Per
# [variation-protocol.md](../../.claude/rules/variation-protocol.md), the
# decisive check is the SUBSTANCE: a `<machine>:<workspace>` token in the line
# carrying the marker IS a lane attribution.
#
# The fallback regex is intentionally stricter than `_LANE_RE` (no leading
# word-boundary bypass for arbitrary colon-pairs), and the caller MUST scope
# the search to the marker line -- URLs, time stamps and code tokens that
# happen to contain a colon are NOT lane IDs. Token shape: `myia-<slug>:<ws>`
# (lowercase, hyphens allowed) or any single-word `lower:Pascal` pair.
_LANE_FALLBACK_RE = re.compile(
    r"\b(myia-[A-Za-z0-9._-]+:[A-Za-z][A-Za-z0-9._-]*)\b"
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


# Matches `<closing-keyword> #N` in free prose (#10101). The keyword set is
# exactly `CLOSING_KEYWORDS` (the 9 GitHub auto-close words); the `#N` tail is
# what GitHub parses as an auto-close instruction when the text lands in a
# PR description or a commit message. The 9 flexions are anchored with a
# word boundary so `fixed` does not match inside `affixed`, and `\s+` allows
# any whitespace between the keyword and the `#`. The number is captured so
# the caller can resolve it: closing an ISSUE is intended
# (catalog-pr-hygiene HARD 4), closing a PR by keyword never is (one does not
# "resolve" a PR -- one merges or closes it explicitly). #10101.
CLOSE_KW_REF_RE = re.compile(
    r"\b(close[ds]?|fix(?:es|ed)?|resolv(?:e|es|ed))\s+#(\d+)\b",
    re.IGNORECASE,
)


def find_close_keyword_pr_refs(text: str | None) -> list[dict]:
    r"""Return ``<closing-keyword> #N`` references found in free prose (#10101).

    The complement of ``find_prev_close_keywords``: that one flags a closing
    keyword in the *genre slot of a `prev:` field* (structurally always wrong).
    This one flags a closing keyword followed by a number **anywhere in the
    text** -- the failure mode #10101 measures: PR #10094's own commit message
    carried a ``CLOSED <PR-number>`` line in prose, which a naive squash would
    have re-closed that PR (the same translation deliverable #10093 protects).

    Each hit is ``{"keyword": <lowercased>, "number": <int>, "span": <tuple>}``:
    the keyword (lowercased for the 9-flexion test), the referenced number
    (the caller resolves it PR-vs-issue), and the match span (so the verdict
    can cite the offending line). Returns an empty list when the text is clean
    or falsy.

    This function is a *finder*, not a *decider*: it does not know whether N is
    a PR or an issue (that needs an API call). The decision lives in the gate
    that calls it (`scripts/ci/pr_close_keyword_guard.py`), with the resolver
    injected so unit tests never touch the network.
    """
    if not text:
        return []
    hits = []
    for m in CLOSE_KW_REF_RE.finditer(text):
        hits.append({
            "keyword": m.group(1).lower(),
            "number": int(m.group(2)),
            "span": m.span(),
        })
    return hits


# Matches NON-closing references in free prose: the "safe syntax" of
# git-workflow.md (``See #N`` / ``Part of #N`` / ``Refs #N``) that links an
# issue without auto-closing it. These are the references an EPIC carries while
# several lanes work it concurrently (#1454, #1027, #3801) -- multi-lane by
# construction, which is why lane_claim_required blocks on CLOSING refs only and
# surfaces a conflict here as an ADVISORY label, never a block (#10223 Tache 4).
NON_CLOSING_REF_RE = re.compile(
    r"\b(see|part\s+of|refs?)\s+#(\d+)\b",
    re.IGNORECASE,
)


def find_non_closing_refs(text: str | None) -> list[dict]:
    r"""Return non-closing ``<keyword> #N`` references (See/Part of/Refs).

    The complement of ``find_close_keyword_pr_refs``: that one returns the
    references that auto-close an issue (the blocking discriminant of
    lane_claim_required). This one returns the references that merely LINK an
    issue -- an EPIC's ``See #N`` / ``Part of #N`` -- which are multi-lane by
    construction and must never block, but may still carry an advisory label
    when another lane holds a claim on them (#10223 Tache 4:
    ``lane-claim-conflict``).

    Same hit shape as ``find_close_keyword_pr_refs``:
    ``{"keyword": <lowercased>, "number": <int>, "span": <tuple>}``. Returns an
    empty list when the text is clean or falsy.
    """
    if not text:
        return []
    hits = []
    for m in NON_CLOSING_REF_RE.finditer(text):
        hits.append({
            "keyword": m.group(1).lower(),
            "number": int(m.group(2)),
            "span": m.span(),
        })
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


def extract_lane(body: str | None, marker_line: str | None = None) -> str | None:
    """Extract the `<machine>:<workspace>` lane token from any text.

    Same reader as `parse_grain_tag` (the single lane extractor, #9485): shared
    by the Grain tag, the G-VAR-2 organ, and -- via `check_lane_claim` (#9774) --
    by the lane-claim guard. A `[CLAIMED] lane myia-po-2024:CoursIA -- ...`
    comment is not a Grain tag (it carries no `Grain TIER/GENRE`), so it cannot
    go through `parse_grain_tag`; this wrapper reuses the exact same compiled
    `_LANE_RE` so the two contexts never drift on what a lane token is.

    `#10395 Variante 1` fallback: when `marker_line` is supplied (the line of
    the bracketed marker, stripped by the caller), and the primary `lane <x>`
    regex misses on the whole body, the function searches ONLY that line for
    a `<machine>:<workspace>` token matching `_LANE_FALLBACK_RE`. The marker
    line scope is what keeps URLs / time stamps / code tokens that contain
    colons from false-positiving -- the marker line is the human-stated intent
    of the claim, not arbitrary prose. Without `marker_line`, behaviour is
    unchanged (legacy callers like `parse_grain_tag` are unaffected).

    Returns the `machine:workspace` string, or None when no lane token is
    found.
    """
    if not body:
        return None
    flat = _strip_title_hashes(body.translate(_NOISE))
    m = _LANE_RE.search(flat)
    if m:
        return m.group(1)
    # Fallback for claim comments that omit the literal `lane` keyword (#10395
    # Variante 1). Restricted to the marker line by the caller -- see docstring.
    if marker_line is not None:
        flat_line = _strip_title_hashes(marker_line.translate(_NOISE))
        m2 = _LANE_FALLBACK_RE.search(flat_line)
        if m2:
            return m2.group(1)
    return None


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
# those three answers AT THE TOP, in three lines.
#
# c.10330 / PR retired the `check-short-header` CI job: the convention was
# voluntarily not promulgated (cf. issue title "pas une nouvelle regle") but
# the organ was cabled and labelled 69 % of PRs without ever discriminating
# anything. The function `parse_short_header` below stays in place as a pure
# parser -- available if a future harness rule ever adopts the convention.
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
    caller decides what to do with the partial coverage. c.10330 / PR retired
    the `check-short-header` CI job (#10330): the convention was not
    promulgated in the harness, so the label `variation-short-header-missing`
    flagged 69 % of PRs without ever discriminating anything. The function
    stays in place -- pure parser, no cost when no caller invokes it,
    available if the convention is one day promulgated.

    Two presentation forms are recognised (#10163 acceptance):

    - **Inline form** (#9861 reference) -- key + value on the SAME line:
        ``Quoi: fix the parser for #10163``
    - **Section form** (#10163 extension) -- key on its own line (optionally
      titled with `#`, optionally wrapped in `**`), value is the NEXT
      paragraph (lines until next blank-line break):
        ``## Quoi\\n\\nfix the parser for #10163\\n\\n## Context\\n...``

    Both forms tolerate the same noise discipline as `parse_grain_tag`: bold
    (``**``), backticks, title hashes (`#`), blockquotes (`>`) are stripped
    before matching. Each value is stripped of leading/trailing whitespace.
    Keys are case-insensitive. Returns {quoi, preuve, perimetre} with each
    entry `None` when the key is absent and the captured text otherwise.

    Mid-paragraph mentions like ``We discuss Quoi: the convention here`` are
    still rejected -- the key MUST be at the start of the line (after the
    noise strip), and in section form the value is the next PARAGRAPH, not
    the rest of the line.
    """
    out: dict[str, str | None] = {k.lower(): None for k in _SHORT_HEADER_KEYS}
    if not body:
        return out
    flat = _strip_title_hashes(body.translate(_NOISE))

    # Two-pass scan: first, the inline form (a key on a line that also has a
    # value -- captured by the same regex as #9861). Second, the section
    # form (key on its own line, value in the NEXT non-empty paragraph).
    # Pass 1 -- inline form.
    # The inline trio puts Quoi/Preuve/Perimetre on three CONSECUTIVE lines
    # inside ONE paragraph (joined by '\n', no blank line between them); we
    # iterate line-by-line and capture any key whose line yields an inline
    # match. The section-form pass 2 runs on paragraphs, not lines.
    for raw_line in flat.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        for k in _SHORT_HEADER_KEYS:
            if out[k.lower()] is not None:
                continue
            if not line.lower().startswith(k.lower()):
                continue
            m = _SHORT_HEADER_RES[k].search(line)
            if m:
                out[k.lower()] = m.group(1).strip()

    # Pass 2 -- section form. Walk paragraphs in order. A paragraph whose
    # FIRST line is a key (anchored, no inline value) takes the NEXT
    # non-empty paragraph as its value. We only fall back here for keys
    # still unfilled after pass 1 -- so a body that uses inline for Quoi
    # and section for Preuve still works (see
    # `test_short_header_section_form_mixed_inline_and_section`).
    paragraphs = flat.split("\n\n")
    for pi, para in enumerate(paragraphs):
        if not para.strip():
            continue
        first = para.splitlines()[0].strip()
        if not first:
            continue
        for k in _SHORT_HEADER_KEYS:
            if out[k.lower()] is not None:
                continue
            if not first.lower().startswith(k.lower()):
                continue
            # Already have inline value? pass 1 won.
            m = _SHORT_HEADER_RES[k].search(first)
            if m:
                continue
            # Section form: key alone on the line, value is the next
            # non-empty paragraph (any number of subsequent paragraphs,
            # skipping blanks -- matches the documented #10163 form where
            # the body has `## Key\n\nAnswer paragraph\n\n## NextKey\n...`).
            value_lines: list[str] = []
            for next_para in paragraphs[pi + 1:]:
                pstripped = next_para.strip()
                if not pstripped:
                    continue
                # Stop at a paragraph that itself starts with a known key
                # -- that paragraph belongs to the next key, not to ours.
                pfirst = pstripped.splitlines()[0].strip().lower()
                if any(pfirst.startswith(other.lower()) for other in _SHORT_HEADER_KEYS):
                    break
                value_lines.append(pstripped)
                # Take the first non-empty answer paragraph only.
                break
            if value_lines:
                out[k.lower()] = " ".join(
                    ln.strip() for ln in value_lines[0].splitlines() if ln.strip()
                )

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
