#!/usr/bin/env python3
r"""Detect TRIVIAL-DIFF: a META-genre PR whose whole diff is one mechanical instance.

#15740 -- the user's concern, verbatim (PR #15724, 2026-09-12T08:00:33Z):

    « Concern: encore une PR fine comme du papier à cigarette, ça n'est pas
    acceptable. Le geste pourrait comprendre une fournée au moins 10 fois plus
    grosse. Modifier le body de l'issue ET/OU mettre des garanties de CI sur
    le contrôle des diffs. Celui de cette PR pourrait clairement lever un
    warning par sa trivialité (en contre-exemple, une correction de 2 lignes
    d'un bug critique serait acceptable, mais ça n'est pas ce que montre le
    diff ici). »

The counter-example in the same sentence FORBIDS size as the principal
criterion: a 2-line critical-bug fix is small AND must pass. What the user
aimed at is TRIVIALITY -- a gesture one could mass-produce by scanning the
next instance. That litmus already exists in prose (variation-protocol §1):
« Pourrais-je en générer une douzaine en scannant l'instance suivante ? ».
This organ gives it a detector, for the first time. `variation_light_cap.py`
counts LIGHT already declared; it never judged whether a diff *is* trivial.

Signals -- a CONJUNCTION, and that is the whole design:

  1. genre_meta      declared genre is in the G-VAR-2 light-genre family
                     (docs/readme/guard/ledger/test -- imported from
                     variation_light_cap, single source). A real bug fix
                     carries tooling/notebook-python/qc/lean/... and NEVER
                     trips this leg: that is how the user's 2-line fix
                     escapes, without any exception mechanism.
  2. small_volume    additions+deletions <= TRIVIAL_CHANGED_LINES. Volume is
                     a SECONDARY signal (one leg of the conjunction), not the
                     criterion -- it separates the founder controls, which
                     carry the SAME tag LIGHT/docs:
                       #15630  1 file   +9/-0    (9 lines)   -> trivial
                       #15724  4 files  +18/-2   (20 lines)  -> trivial
                       #15737  26 files +737/-19 (756 lines) -> the requested
                                                                batch, passes
                     Anchor (guard-pool-widening discipline: anchor on the
                     founding instance, not on a round number): the bar sits
                     between the largest verdicté-trivial (20) and the
                     smallest approved batch (756). Geometric midpoint ~123;
                     bar = 100 (5x above the largest trivial, 7.6x under the
                     smallest batch).
  3. no_written_exception   the body carries no exception sentence. The
                     recognized form is #15719's (« exception seulement
                     résidu final mesuré »): a sweep down to its measured
                     last file is not a lazy PR, and the organ must not force
                     a lane to fabricate volume. When a sentence is found it
                     is QUOTED in the verdict -- the organ cites the phrase
                     that extinguishes it, so the reader can audit the match.

All three hold -> verdict `trivial` -> ::warning + label (advisory,
blocking=False). The user asked for « lever un warning », not a block.

Verdict states: `trivial` | `ok` | `unknown`. Unknown = no Grain tag (the
tag-required blocking guard owns that defect) or missing diff stats
(#14849: never decide on absent data). Unknown warns NOTHING.

Input:
  --pr-json <file>          CI mode: the payload of
                            gh pr view --json body,additions,deletions,changedFiles
  --body-file <f>           explicit mode (controls/tests): body text
  --stats <a,d,c>           explicit mode: additions,deletions,changed_files

Output: one JSON object on stdout (verdict + signals + disclosure). Exit 0
in every assessable state -- the organ is advisory; a crash is a bug, not a
verdict.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from grain_tag import parse_grain_tag  # noqa: E402
from variation_light_cap import LIGHT_GENRES  # noqa: E402

TRIVIAL_CHANGED_LINES = 100

# The exception form of #15719: « exception seulement résidu final mesuré ».
# Accent-stripped lowercase before matching (résidu -> residu, mesuré ->
# mesure). A line extinguishes when it names an exception/residue AND scopes
# it to a measured end (final/mesure/restant/dernier/seul) -- either half
# alone is prose, not a declared exception.
_EXCEPTION_LEXICAL = re.compile(r"\bexception|\bresidu|\bjustification")
_EXCEPTION_SCOPE = re.compile(r"\bfinal\b|\bmesur|\brestant|\bdernier\b|\bseul\b")


def _strip_accents_lower(line: str) -> str:
    decomposed = unicodedata.normalize("NFD", line)
    ascii_only = "".join(c for c in decomposed if not unicodedata.combining(c))
    return ascii_only.lower()


def find_written_exception(body: str | None) -> str | None:
    """Return the verbatim body line that declares an exception, else None.

    Only sentences of the #15719 form count: the loop keeps the ORIGINAL
    line (accents intact) for the verdict quote, matching happens on the
    normalized copy.
    """
    if not body:
        return None
    for raw_line in body.splitlines():
        if not raw_line.strip():
            continue
        flat = _strip_accents_lower(raw_line)
        if _EXCEPTION_LEXICAL.search(flat) and _EXCEPTION_SCOPE.search(flat):
            return raw_line.strip()
    return None


def assess(body: str | None, additions: int | None, deletions: int | None,
           changed_files: int | None) -> dict:
    """Render the triviality verdict. Never raises on assessable input."""
    tag = parse_grain_tag(body)
    if tag is None or tag.get("genre") is None:
        return {
            "verdict": "unknown",
            "reason": "pas de tag Grain lisible -- variation-tag-required garde ce defaut ; rien a mesurer ici.",
        }

    if additions is None or deletions is None:
        return {
            "verdict": "unknown",
            "reason": "stats de diff absentes -- jamais de verdict sur une absence de donnee (#14849).",
        }

    changed_lines = int(additions) + int(deletions)
    exception_line = find_written_exception(body)

    genre = tag.get("genre")
    signals = {
        "genre_meta": genre in LIGHT_GENRES,
        "small_volume": changed_lines <= TRIVIAL_CHANGED_LINES,
        "written_exception": exception_line,
    }

    trivial = (
        signals["genre_meta"]
        and signals["small_volume"]
        and exception_line is None
    )

    if trivial:
        reason = (
            f"genre {genre} dans la famille META ({'/'.join(sorted(LIGHT_GENRES))}) "
            f"+ diff de {changed_lines} lignes changees (<= {TRIVIAL_CHANGED_LINES}) "
            "+ aucune exception ecrite dans le body : le litmus de la trivialite "
            "(une douzaine d'instances scannees a la suite) est credible. "
            "Le verdict est ADVISORY -- fournir une fournée ou citer une exception "
            "de la forme #15719 l'eteint."
        )
    elif exception_line is not None and signals["genre_meta"] and signals["small_volume"]:
        reason = (
            f"exception ecrite reconnue (forme #15719), citee verbatim : « {exception_line} » "
            "-- le warning est eteint par cette phrase."
        )
    else:
        legs = []
        if not signals["genre_meta"]:
            legs.append(f"genre {genre} hors famille META")
        if not signals["small_volume"]:
            legs.append(f"diff de {changed_lines} lignes changees (> {TRIVIAL_CHANGED_LINES})")
        reason = "pas trivial : " + " ; ".join(legs) + "."

    return {
        "verdict": "trivial" if trivial else "ok",
        "signals": signals,
        "tier": tag.get("tier"),
        "genre": genre,
        "lane": tag.get("lane"),
        "changed_lines": changed_lines,
        "changed_files": changed_files,
        "bar": TRIVIAL_CHANGED_LINES,
        "reason": reason,
    }


def _parse_stats(raw: str) -> tuple[int | None, int | None, int | None]:
    try:
        a, d, c = (int(x) for x in raw.split(","))
        return a, d, c
    except (ValueError, TypeError):
        return None, None, None


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--pr-json", help="payload gh pr view --json body,additions,deletions,changedFiles")
    mode.add_argument("--body-file", help="body text file (mode controles/tests)")
    p.add_argument("--stats", help="additions,deletions,changed_files (avec --body-file)")
    args = p.parse_args(argv)

    if args.pr_json:
        try:
            payload = json.loads(Path(args.pr_json).read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            print(json.dumps({"verdict": "unknown", "reason": f"pr-json illisible : {exc}"}))
            return 0
        body = payload.get("body")
        additions = payload.get("additions")
        deletions = payload.get("deletions")
        files_field = payload.get("changedFiles")
        changed_files = len(files_field) if isinstance(files_field, list) else files_field
    else:
        body = Path(args.body_file).read_text(encoding="utf-8")
        additions, deletions, changed_files = _parse_stats(args.stats or "")

    verdict = assess(body, additions, deletions, changed_files)
    print(json.dumps(verdict, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
