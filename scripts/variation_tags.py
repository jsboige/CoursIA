"""Shared Grain: tag extractor + conformity checker (variation-protocol §1).

The protocol (`<repo>/.claude/rules/variation-protocol.md`) makes the tag
`Grain: <TIER>/<GENRE>` a condition of merge; the rule names the form but
not the only one observed in the wild. Two readers need the same answer:

- `scripts/variation_light_cap.py` extracts {tier, lane} from PR bodies to
  count LIGHTs per lane (G-VAR-2 cap).
- `.github/workflows/variation-tag-guard.yml` extracts {tier, genre, lane}
  to label malformed tags and verify the GENRE is in the §1 enumeration.

Both readers MUST speak the same dialect of "what counts as a tag" -- a guard
and an organe that disagree silently is the worst failure mode: the cap is
applied to one slice of merges while the labels mark a different slice, and
neither tells the coordinator the truth. Issue #9485: 38 percent of merges
(13/34 on the 2026-08-05 lot) carried no readable tag simply because the
form is `## Grain\\nMED/tooling ... -- lane ...` instead of `Grain: ...`.

Substance > form. The 4 forms accepted here are all variations on the SAME
declaration:

    ## Grain
    MED/tooling (#8056 cost-honesty / under-declaration correction)
    -- lane myia-po-2023:CoursIA -- prev: MED/tooling #9457.

is a header-form `Grain` whose TIER/GENRE/LANE follow on subsequent lines --
logically identical to the original line-form `Grain: MED/tooling -- lane
myia-po-2023:CoursIA`. A body genuinely lacking TIER/GENRE remains
`variation-tag-missing` (the regulator returns None and the guard labels it);
the failures this module fixes are FORM (header, no-colon, decoration), not
SUBSTANCE.

PUBLIC API
----------

    extract_tag(body) -> {tier, genre, lane} | None
        Full-tag extraction for the cap organe. `tier` and `genre` are
        upper-cased / lowered strings; `lane` is the "<machine>:<workspace>"
        token, may be None.

    check_conformity(body) -> {ok, defects, grain}
        Used by the guard workflow. Returns a dict with `ok: bool` plus the
        list of defect class names (mirrors the workflow's existing label
        names: variation-tag-missing / variation-tag-malformed /
        variation-tag-genre-offlist / variation-tag-lane-missing) and the
        extracted `grain: {tier, genre, lane} | None`.

    GRAIN_GENRES
        The canonical §1 enumeration of accepted genres (lifted from the
        workflow so the two readers agree on the list).

    normalize_body(body) -> str
        Strip markdown noise that confuses extraction (phase 1 of the
        pipeline). Pure, no I/O.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Noise handling (mirrors the workflow's `tr -d '*`'` block, expanded for
# header markers `#` and blockquote markers `>` per #9485 constraint 3).

# Per-line leading-marker strip: header (`#`), blockquote (`>`), list bullet
# (`-` / `*` / `+`), plus any whitespace the author placed in front. Doing it
# line-by-line (NOT on the whole body) lets the line that opens `## Grain`
# collapse to `Grain` while later content (which may legitimately contain
# `*emphasis*` mid-line) is preserved for the asterisks/backticks pass.
_LEADING_MARKER_RE = re.compile(r"^[\s>\#\-\*\+]*")

# Inline noise: asterisks (bold, list bullet, horizontal rule) and backticks
# (inline code). Mirrors the workflow's `tr -d '*\`'` so the two stay in
# lockstep -- the cap organe flattens the same characters #8938.
_INLINE_NOISE = str.maketrans({"*": "", "`": ""})


def normalize_body(body: str) -> str:
    """Return `body` with markdown decoration that confuses tag extraction removed.

    Phase 1: per-line, strip leading markers (`#`, `>`, `-`, `*`, `+`,
    whitespace). Phase 2: per-body, strip inline asterisks and backticks
    (existing behavior, #8938). The result is a body whose tags look the
    same regardless of header level, blockquote, list bullet, or bold.
    """
    if not body:
        return ""
    out_lines = []
    for line in body.split("\n"):
        prefix = _LEADING_MARKER_RE.match(line)
        rest = line[prefix.end():] if prefix else line
        rest = rest.translate(_INLINE_NOISE).lstrip()
        out_lines.append(rest)
    return "\n".join(out_lines)


# ---------------------------------------------------------------------------
# The Grain: tag itself. After normalize_body the body looks like the three
# original line-forms (#8938) PLUS three new forms (#9485):
#
#   A. existing line-form ........... "Grain: DEEP/lean -- lane x:y"
#   B. existing line-form no-colon .. "Grain DEEP/lean -- lane x:y"  (still recognized)
#   C. header-form .................. "Grain\\nDEEP/lean -- lane x:y ..."
#   D. blockquote-form .............. "> Grain: DEEP/lean -- lane x:y"
#   E. bullet-form .................. "- Grain: DEEP/lean -- lane x:y"
#
# A, B, D, E collapse to A after normalize_body; C needs explicit recollation
# because the TIER/GENRE lives on the next line.

# The TIER/GENRE part of an inline Grain: tag. Captures the TIER word and the
# GENRE token (letters, digits, underscore, hyphen). Three separator shapes
# are accepted between the label `Grain` and the `<TIER>` word (#9485):
#
#   `Grain: DEEP/lean`              (colon adjacent, the canonical form)
#   `Grain DEEP/lean`               (no colon)
#   `Grain : DEEP/lean`             (bold + space-colon-space, observed #9477/#9479)
#
# The slash delimiter is required: a `<word>` followed by a slash followed
# by a `<token>` is the unambiguous signature of `TIER/GENRE`, and tolerating
# strings like `Grain heading` (which would match `Grain:?\s+heading` with a
# non-slash follow-on) keeps the regex honest.
_GRAIN_TIER_GENRE_RE = re.compile(
    r"Grain\s*:?\s+([A-Za-z]+)\s*/\s*([A-Za-z][A-Za-z0-9_-]*)"
)

# Lane token, anywhere in the body. The lane is STRUCTURAL (the worker's
# own workspace) and is never re-qualified -- it is always read from the
# body, even when a `grain-requalified:` label overrides the tier. After
# `normalize_body` strips the inline asterisks, the form observed in
# PR #9480 -- `**Lane** :` -- becomes `Lane :`, which the original
# `lane:?\s+` regex rejected because the SPACE between `Lane` and `:` is
# not tolerated (#9485 constraint 4). The widened regex accepts all
# three label/colon shapes observed in the wild:
#
#   `lane myia-ai-01:CoursIA`           (no colon at all)
#   `lane: myia-ai-01:CoursIA`          (colon adjacent)
#   `Lane : myia-ai-01:CoursIA`         (bold, space-colon-space)
#
# Search the WHOLE body (full-text) because constraint #4 explicitly allows
# the lane to live on a different line from the Tier block.
_LANE_RE = re.compile(
    r"lane\s*:?\s*([A-Za-z0-9._-]+:[A-Za-z0-9._-]+)",
    re.IGNORECASE,
)


def _find_inline_tag(flat: str) -> Optional[re.Match]:
    """Return the first regex match against `flat`, or None.

    `flat` is the result of `normalize_body(body)`. The regex matches the
    inline form `Grain: TIER/GENRE` (with optional colon, per #9485) -- the
    same match site is used both by inline-form bodies and by header-form
    bodies after explicit recollation.
    """
    return _GRAIN_TIER_GENRE_RE.search(flat)


# Lines that, AFTER `normalize_body`, are exactly `Grain` or `Grain:` (with
# optional trailing whitespace). The header form. We recollate the next
# non-empty lines that do not begin a new section, stripping the per-line
# markers ourselves so the recollation stops at the first line that is
# either empty OR a new header. The match is case-insensitive -- author
# may have written `## grain` in lowercase (observed #9477).
_HEADER_TAG_LINE_RE = re.compile(r"^Grain:?\s*$", re.IGNORECASE)

# A line whose UN-normalized form was a section header (i.e. starts with
# optional whitespace then one-or-more `#`). We detect this BEFORE applying
# the leading-marker strip so we can stop the recollation at the next
# section break -- otherwise the recollation would swallow the next header's
# content as if it belonged to `Grain`.
_NEXT_HEADER_RE = re.compile(r"^\s*#{1,6}\s")


def _recollapse_header_form(body: str) -> Optional[str]:
    """Locate a `## Grain` (or similar) header and recollate its content.

    The author wrote the Grain tag as a multi-line block, header-form:

        ## Grain
        MED/tooling (#8056 ...) -- lane myia-po-2023:CoursIA -- prev: ...

    After normalize_body each leading marker is gone, so the first line is
    just `Grain` (or `Grain:`). The recollation reads forward, skipping
    blank lines, until it hits either (a) the next raw header (line
    starting with `#`) or (b) the end of the body. The collected lines are
    joined into ONE string so the inline regex can match across them.

    Returns the recollated content, or None if no header-form tag was
    found. The match is case-insensitive.
    """
    lines = body.split("\n")
    for i, line in enumerate(lines):
        stripped = _LEADING_MARKER_RE.sub("", line).lstrip()
        # Match against the post-marker form -- but apply asterisk / backtick
        # stripping too, in case the header was `` ## `Grain` `` (observed
        # #9462). `_INLINE_NOISE` is a per-character table so we just call
        # `translate` again.
        stripped_clean = stripped.translate(_INLINE_NOISE).strip()
        if not _HEADER_TAG_LINE_RE.match(stripped_clean):
            continue
        # Found the Grain header. Recollate forward.
        block = []
        for j in range(i + 1, len(lines)):
            ln = lines[j]
            # Stop at the next section header (any level): a section break
            # means we have left the Grain block. The raw form starts with
            # optional whitespace then `#`, so we detect BEFORE any
            # normalization to be robust against later decoration.
            if _NEXT_HEADER_RE.match(ln):
                break
            stripped_ln = _LEADING_MARKER_RE.sub("", ln).lstrip()
            stripped_ln = stripped_ln.translate(_INLINE_NOISE).strip()
            if not stripped_ln:
                continue
            block.append(stripped_ln)
            # First non-empty content line is enough for the inline regex;
            # the GENRE/TIER are always on this line in the wild. Reading
            # more would risk swallowing the next paragraph. The TIER word
            # and the lane token both appear on the same line in EVERY
            # observed offender (#9458, #9477, #9479, ...).
            break
        if block:
            return " ".join(block)
        # Header-line empty / blank content after it: the tag is malformed.
        return None
    return None


# Public API --------------------------------------------------------------

def extract_tag(body: str) -> Optional[dict]:
    """Extract {tier, genre, lane} from `body`, full-text + separator-agnostic.

    Returns None when NO `Grain:` tag is found. `tier` is upper-cased
    (LIGHT/MED/DEEP) or None if only the TIER/GENRE was unreadable. `lane`
    is the "<machine>:<workspace>" string or None. The GENRE is lowercased
    to match the §1 enumeration convention.
    """
    if not body:
        return None
    # First try inline / decollated forms (A, B, D, E). If that fails, fall
    # back to explicit recollation for the header form (C).
    flat = normalize_body(body)
    m = _find_inline_tag(flat)
    inline_block: Optional[str] = None
    if not m:
        inline_block = _recollapse_header_form(body)
        if inline_block is not None:
            # Re-flatten the recollated block (some inline markers may be
            # preserved) so the regex sees the same shape as a real inline
            # form.
            m = _find_inline_tag(normalize_body(inline_block))
    if not m:
        return None
    lane_m = _LANE_RE.search(flat)  # whole body, not just the block
    return {
        "tier": m.group(1).upper(),
        "genre": m.group(2).lower(),
        "lane": lane_m.group(1) if lane_m else None,
    }


# ---------------------------------------------------------------------------
# §1 genre enumeration -- the 13 +1 GENREs currently canonized by
# variation-protocol §1, plus `tooling` and `research-code` admitted by the
# rule itself ("a genre observed often enough is a lacune of the enumeration,
# not a fault of the worker", workflow comment, c.61 / c.65).

GRAIN_GENRES = frozenset({
    "lean", "qc", "training", "genai",
    "notebook-python", "notebook-dotnet",
    "docs", "guard", "refactor", "ledger",
    "readme", "test",
    "tooling", "research-code",
})


def check_conformity(body: str) -> dict:
    """Return {ok, defects, grain} for the guard workflow.

    Defect class names mirror the existing workflow labels exactly so the
    guard's `note_defect` calls line up without translation:

      - "variation-tag-missing"        : no `Grain:` tag found at all
      - "variation-tag-malformed"      : TIER is unreadable or not in {DEEP, MED, LIGHT}
      - "variation-tag-genre-offlist"  : TIER readable but GENRE is not in §1
      - "variation-tag-lane-missing"   : tag present but no lane token

    `grain` is the raw extracted tag (or None). Consumers (the workflow,
    tests) can inspect it directly without re-parsing.
    """
    g = extract_tag(body or "")
    defects: list[str] = []

    if g is None:
        # No tag at all: the tag is missing. Substance check, not form --
        # only a body genuinely lacking TIER/GENRE lands here, NOT a body
        # whose form is just header / no-colon (those are now accepted).
        defects.append("variation-tag-missing")
        return {"ok": False, "defects": defects, "grain": None}

    if g.get("tier") not in ("DEEP", "MED", "LIGHT"):
        defects.append("variation-tag-malformed")
    else:
        # Only check GENRE if TIER is readable -- an unreadable TIER means
        # the parse is malformed and the GENRE check would be noise.
        if g.get("genre") not in GRAIN_GENRES:
            defects.append("variation-tag-genre-offlist")

    if not g.get("lane"):
        defects.append("variation-tag-lane-missing")

    return {"ok": not defects, "defects": defects, "grain": g}


# ---------------------------------------------------------------------------
# CLI used by the variation-tag-guard.yml workflow (`check-variation-tag`).
# The procedure: read the body from a file, run `check_conformity`, emit one
# JSON line on stdout that the shell can parse with `python3 -c ...`. Exit 0
# always (the guard is advisory; the workflow decides whether to label).
# Usage:
#     python3 scripts/variation_tags.py --body-file /tmp/pr_body.txt
#     python3 scripts/variation_tags.py --body '<body-as-string>'

def _cli(argv: list[str]) -> int:
    p = argparse.ArgumentParser(
        description="Conformity check for the variation-protocol Grain: tag."
    )
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--body", metavar="TEXT",
                     help="PR body to check (inline text)")
    src.add_argument("--body-file", metavar="FILE",
                     help="Path to a file holding the PR body (preferred for "
                          "shell pipelines: avoids quoting issues)")
    args = p.parse_args(argv)
    body = args.body if args.body is not None else Path(args.body_file).read_text(encoding="utf-8")
    print(json.dumps(check_conformity(body), ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
