#!/usr/bin/env python3
r"""variation_adjacency_guard.py -- BLOCKING gate against consecutive LIGHT-genre grains (#11170).

## Why this exists

variation-protocol.md §2 (G-VAR-3) bans two consecutive grains of the same
LIGHT genre for a lane: `LIGHT/docs` following `LIGHT/docs` is monoculture,
the exact drift the protocol exists to stop. Until #11170 the ban had NO
organ -- `Check Grain tag conformity` verified the tag is well-formed,
`G-VAR-2 light cap` counted the daily budget, but NO job compared the genre
of the grain to that of its `prev:`. A tag perfectly conformant declaring
`LIGHT/docs -- prev: LIGHT/docs` passed every gate green.

Measured on the night of 2026-08-15/16: two identical-shaped grains, three
hours apart, got OPPOSITE verdicts from the same coordinator -- #11136
(`LIGHT/docs -- prev: LIGHT/docs 11134`) merged 00:30:56Z, #11167
(`LIGHT/docs -- prev: MED/docs 11069`) held ~03:00Z. The first was not
merged by complacency: nothing in the tooling posed the question.

## What it does

Reads the PR body, parses the Grain tag + its `prev:` field (both through
the SHARED extractor `scripts/grain_tag.py`, so this organ and the guard
never diverge on what a tag is), normalises both genres through the SAME
alias table as the G-VAR-2 organ (`variation_light_cap.canonicalize_genre`),
and compares:

  * **BLOCK** (exit 1) when `genre == prev_genre` AND the genre is in the
    LIGHT set `{guard, ledger, docs, readme, test}` -- the absolute ban of
    §2, no escape clause. The remediation is to pick a grain of ANOTHER
    genre, never to re-tag the same work.
  * **ADVISORY** (exit 0 + `adjacent: true`) when `genre == prev_genre` and
    the genre is outside the LIGHT set (a DEEP/MED domain-core genre). §2
    allows two consecutive there "si chacun est une substance genument
    distincte" -- a judgment not mechanisable, so the organ labels, never
    blocks. A Lean specialist chaining two distinct proofs must not blush.
  * **PASS** otherwise -- different genres, `prev: none (premier grain)`
    (the first-grain exemption, already parsed by `parse_prev`), or a
    `prev:` absent / unreadable (already covered by the `variation-tag-prev-
    absent` label and the tag-required job).

Emits a single JSON verdict on stdout:

    {"guard_pass": true|false, "blocking": true|false, "adjacent": bool,
     "genre": ..., "prev_genre": ..., "lane": ..., "reason": "..."}

Exit codes:
  0  -- pass, or advisory (DEEP/MED adjacency)
  1  -- LIGHT-genre adjacency (the PR is non-mergeable until the worker
       picks a grain of another genre)
  2  -- caller error (unreadable body file)

## Why BLOCKING (not advisory)

The advisory label is the failure mode #11170 measures: `Check Grain tag
conformity` has been posting labels all along and the LIGHT adjacency
crossed anyway, because a label does not stop a merge and the coordinator
read the green of a check that measures something else. The same shape as
`check-variation-tag-required` (#10045) and `check-prev-close-keyword-
required` (#10093): only a required check turning `PR gate` red before
merge makes the ban hold.

## Run locally

    python scripts/ci/variation_adjacency_guard.py --body-file body.txt
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Make the shared extractor + the G-VAR-2 alias table importable from anywhere
# in the repo (CI runs from the repo root; local devs may run from the script
# directory).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402
from variation_light_cap import LIGHT_GENRES, canonicalize_genre  # noqa: E402


def check(body: str | None) -> dict:
    """Return the adjacency verdict for a PR body.

    Pure function so unit tests pin each branch without going through the
    CLI. The verdict is:

      * `guard_pass: False, blocking: True`  -- LIGHT-genre adjacency (exit 1)
      * `guard_pass: True,  adjacent: True`  -- DEEP/MED adjacency (advisory)
      * `guard_pass: True,  adjacent: False` -- no adjacency, or not evaluable
        (missing tag / missing or exempt prev -- covered by other organs)
    """
    g = gt.parse_grain_tag(body)
    if g is None:
        return {
            "guard_pass": True, "blocking": False, "adjacent": False,
            "genre": None, "prev_genre": None, "lane": None,
            "reason": "no Grain tag in body (covered by check-variation-tag-required)",
        }
    pv = gt.parse_prev(body)
    if pv["exempt"]:
        return {
            "guard_pass": True, "blocking": False, "adjacent": False,
            "genre": g["genre"], "prev_genre": None, "lane": g["lane"],
            "reason": "prev: none (premier grain) -- no predecessor to compare",
        }
    if not pv["present"] or not pv["genre"]:
        return {
            "guard_pass": True, "blocking": False, "adjacent": False,
            "genre": g["genre"], "prev_genre": None, "lane": g["lane"],
            "reason": "prev: absent or unreadable (covered by variation-tag-prev-absent)",
        }

    # Normalise through the SAME alias table as the G-VAR-2 organ: without it,
    # `fix` vs `docs` on two grains of the same work would make the adjacency
    # invisible -- variation-protocol §1 warns that two invented labels suffice
    # to never trip the ban.
    genre = canonicalize_genre(g["genre"])
    prev_genre = canonicalize_genre(pv["genre"])
    lane = g["lane"]
    if genre is None or prev_genre is None:
        return {
            "guard_pass": True, "blocking": False, "adjacent": False,
            "genre": genre, "prev_genre": prev_genre, "lane": lane,
            "reason": "genre or prev-genre not normalisable -- adjacency not evaluable",
        }

    if genre != prev_genre:
        return {
            "guard_pass": True, "blocking": False, "adjacent": False,
            "genre": genre, "prev_genre": prev_genre, "lane": lane,
            "reason": f"genres differ ({genre} vs {prev_genre}) -- no adjacency",
        }

    # Same genre. The LIGHT set is the absolute ban of §2; a DEEP/MED
    # domain-core genre is the advisory judgment of §2.
    if genre in LIGHT_GENRES:
        return {
            "guard_pass": False, "blocking": True, "adjacent": True,
            "genre": genre, "prev_genre": prev_genre, "lane": lane,
            "reason": (
                f"G-VAR-3: {genre} succede a {prev_genre} -- deux grains LIGHT "
                f"consecutifs pour la lane {lane}. La regle est un ban absolu "
                f"(§2): piochez un grain d'UN AUTRE genre, ne retaguez pas "
                f"le meme travail (#11170)."
            ),
        }
    return {
        "guard_pass": True, "blocking": False, "adjacent": True,
        "genre": genre, "prev_genre": prev_genre, "lane": lane,
        "reason": (
            f"adjacence {genre}->{prev_genre} hors liste LIGHT : §2 l'autorise "
            f"si chaque grain est une substance genument distincte -- "
            f"jugement non mecanisable, signal advisory uniquement."
        ),
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--body-file", metavar="FILE", required=True,
                   help="path to the PR body")
    args = p.parse_args(argv)

    try:
        with open(args.body_file, encoding="utf-8") as f:
            body = f.read()
    except OSError as e:
        print(json.dumps({"guard_pass": False, "reason": f"caller error: {e}"}),
              file=sys.stderr)
        return 2

    verdict = check(body)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
