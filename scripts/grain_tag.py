#!/usr/bin/env python3
"""Shared `Grain:` tag extractor (variation-protocol §1, fix #9485).

THE single reader of the `Grain: <TIER>/<GENRE> -- lane <machine:workspace>`
tag. Consumed by:

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

Returns {tier, genre, lane} | None. `tier` is upper-cased, `genre` lower-cased.
`lane` is the "<machine>:<workspace>" token or None -- extracted independently
of its position, but None when the body carries no `lane` token at all (a real
defect the guard reports as `variation-tag-lane-missing`; the organ then leaves
the PR unattributed, which is the correct arithmetic).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# --- noise ------------------------------------------------------------------

# Markdown decoration that wraps or prefixes the tag in the wild. Stripped
# before matching so the regex sees a clean `Grain TIER/GENRE ... lane mw`.
# Mirrors the organ's historical {*, `} and ADDS the title hashes (#, #9485)
# and the blockquote marker (>). Stripping `#` is what lets `## Grain` read
# as `Grain` and then match the next non-empty line via `\\s*` (newlines).
_NOISE = str.maketrans({"*": "", "`": "", "#": "", ">": ""})

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
    flat = body.translate(_NOISE)
    m = _GRAIN_FULL_RE.search(flat)
    if not m:
        return None
    lane_m = _LANE_RE.search(flat)
    return {
        "tier": m.group(1).upper(),
        "genre": m.group(2).lower(),
        "lane": lane_m.group(1) if lane_m else None,
    }


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
    if g is None:
        # No TIER/GENRE anywhere: the one substance the protocol will not
        # relax. The guard poses `variation-tag-missing`.
        print(json.dumps({"present": False, "tier": None, "genre": None,
                          "lane": None, "tier_valid": False, "genre_valid": False}))
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
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
