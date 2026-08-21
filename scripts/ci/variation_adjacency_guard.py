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
import re
import sys
from pathlib import Path

# Make the shared extractor + the G-VAR-2 alias table importable from anywhere
# in the repo (CI runs from the repo root; local devs may run from the script
# directory).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402
from variation_light_cap import LIGHT_GENRES, canonicalize_genre  # noqa: E402


# --- G-VAR-3 override (#11708) --------------------------------------------
#
# variation-protocol section 3 already grants the coordinator a decision the
# gate could not hear: "Ne jamais tenir une LIGHT plus d'une journee [...]
# Passe 24 h : merger, ou fermer en nommant le remplacant", and "HOLD sans
# remplacement = echec coordinateur". Without an organ, that clause is
# unreachable: the job carries the `-required` suffix, so a correctly-blocked
# PR ages forever and the lane rewrites the same work elsewhere -- the exact
# harm the clause was written to prevent.
#
# The marker mirrors the lane-claim `[OVERRIDE]` of #10223: an arbitration the
# coordinator MAY make but MUST write. Two conditions make it non-vacuous:
#   * it is authored by a coordinator login (a worker cannot self-exempt);
#   * it NAMES the replacement genre the lane takes next, and that genre
#     DIFFERS from the blocked one -- otherwise the override would waive the
#     rule while promising to break it again.
COORDINATOR_LOGINS = frozenset({"myia-ai-01", "jsboige"})

_OVERRIDE_RE = re.compile(
    r"\[\s*G-?VAR-?3\s+OVERRIDE\s*\]"          # the marker
    r"(?:[^\n]*?lane\s+(?P<lane>[\w.-]+:[\w.-]+))?"  # optional lane echo
    r"[^\n]*?next\s*:\s*(?P<next>[A-Za-z][\w-]*)",   # mandatory replacement
    re.IGNORECASE,
)

# Bare marker, no `next:` requirement: lets parse_override tell "a coordinator
# marker was read but malformed" apart from "no marker read" (#12096) --
# "rien trouve" and "pas regarde" must never share a return value.
_MARKER_RE = re.compile(r"\[\s*G-?VAR-?3\s+OVERRIDE\s*\]", re.IGNORECASE)
_MARKER_LINE_RE = re.compile(
    r"^[^\n]*\[\s*G-?VAR-?3\s+OVERRIDE\s*\][^\n]*$", re.IGNORECASE | re.MULTILINE)
_NEXT_ANYWHERE_RE = re.compile(r"next\s*:", re.IGNORECASE)
_GENRE_SHAPE_RE = re.compile(r"next\s*:\s*(?P<next>\S+)", re.IGNORECASE)

OVERRIDE_EXPECTED_FORM = (
    "`[G-VAR-3 OVERRIDE] lane <machine:workspace> -- next: <genre>`, "
    "sur une seule ligne"
)


def parse_override(comments: list[dict] | None) -> dict | None:
    """Read a coordinator `[G-VAR-3 OVERRIDE] ... next: <genre>` marker.

    `comments` is a list of ``{"author", "body"}`` (the shape `gh pr view
    --json comments` returns, with `author` flattened to a login). Pure
    function: the caller does the network. Three states, never two (#12096):

      * ``None`` -- no coordinator marker read. Covers absent markers AND
        worker-authored ones: a lane cannot self-exempt, so a worker marker
        stays deliberately indistinguishable from absent (control C of
        #12096; the choice is documented here).
      * ``{"malformed": "<raison>", "author": ...}`` -- a COORDINATOR marker
        was read and REJECTED: ``next:`` missing, off the marker's line, or
        its value not a genre shape. The gate stays down -- a malformed
        override never waives it -- but `check` announces the rejection in
        the verdict so the coordinator gets feedback instead of a mute
        re-block (#11963).
      * well-formed dict -- ``author`` + ``lane`` + ``next_genre`` (kept
        verbatim when outside the enum, per the pass-through of section 1).
    """
    if not comments:
        return None
    for c in reversed(comments):
        login = (c.get("author") or "")
        if isinstance(login, dict):
            login = login.get("login") or ""
        if login not in COORDINATOR_LOGINS:
            continue
        body = c.get("body") or ""
        m = _OVERRIDE_RE.search(body)
        if m:
            return {
                "author": login,
                "lane": m.group("lane"),
                "next_genre": canonicalize_genre(m.group("next")) or m.group("next").lower(),
            }
        if _MARKER_RE.search(body):
            # Coordinator marker present but the full contract does not hold.
            # Name WHICH clause failed, in the priority order of #12096.
            line = _MARKER_LINE_RE.search(body)
            on_line = _GENRE_SHAPE_RE.search(line.group(0)) if line else None
            if on_line and not re.fullmatch(r"[A-Za-z][\w-]*", on_line.group("next")):
                reason = (f"`next: {on_line.group('next')}` -- valeur qui n'est pas "
                          f"un genre (forme attendue : une lettre puis lettres/"
                          f"chiffres/tirets)")
            elif _NEXT_ANYWHERE_RE.search(body):
                reason = "`next:` pas sur la meme ligne que le marqueur"
            else:
                reason = "`next:` manquant (aucun remplacant nomme)"
            return {"author": login, "lane": None, "malformed": reason}
    return None


def check(body: str | None, override: dict | None = None) -> dict:
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
        # The adjacency is real. Before failing, ask whether the coordinator
        # has exercised the 24h decision section 3 already grants (#11708).
        if override and override.get("next_genre") \
                and override["next_genre"] != genre:
            return {
                "guard_pass": True, "blocking": False, "adjacent": True,
                "genre": genre, "prev_genre": prev_genre, "lane": lane,
                "overridden": True,
                "override_author": override["author"],
                "override_next": override["next_genre"],
                "reason": (
                    f"G-VAR-3: adjacence {genre} apres {prev_genre} REELLE, "
                    f"mais levee par {override['author']} au titre de la "
                    f"clause 24h (section 3 : « merger, ou fermer en nommant "
                    f"le remplacant »). Prochain grain nomme pour la lane "
                    f"{lane} : {override['next_genre']}. Le travail ecrit "
                    f"n'est pas jete ; la lane change de genre au grain "
                    f"suivant."
                ),
            }
        hint = ""
        extra = {}
        if override and override.get("next_genre") == genre:
            hint = (
                f" Un marqueur d'override existe mais nomme `next: {genre}` "
                f"-- soit le genre meme qui bloque : une levee qui promet de "
                f"rejouer l'adjacence n'en est pas une, elle est ignoree."
            )
            extra["override_rejected"] = {
                "author": override["author"],
                "reason": f"next: {genre} -- le genre meme qui bloque",
            }
        elif override and override.get("malformed"):
            # #12096: "rejete" et "absent" ne doivent jamais partager une
            # valeur de retour. Le coordinateur qui a ecrit un marqueur
            # bancal voit le gate re-bloquer ET la raison -- pas un silence
            # qui se lit comme un arbitrage ignore.
            hint = (
                f" Un marqueur [G-VAR-3 OVERRIDE] de {override['author']} a "
                f"ete lu et rejete : {override['malformed']}. Forme attendue : "
                f"{OVERRIDE_EXPECTED_FORM}."
            )
            extra["override_rejected"] = {
                "author": override["author"],
                "reason": override["malformed"],
            }
        verdict = {
            "guard_pass": False, "blocking": True, "adjacent": True,
            "genre": genre, "prev_genre": prev_genre, "lane": lane,
            "overridden": False,
            "reason": (
                f"G-VAR-3: {genre} succede a {prev_genre} -- deux grains LIGHT "
                f"consecutifs pour la lane {lane}. La regle est un ban absolu "
                f"(§2): piochez un grain d'UN AUTRE genre, ne retaguez pas "
                f"le meme travail (#11170). Tenu > 24 h : le coordinateur "
                f"tranche par `[G-VAR-3 OVERRIDE] lane {lane} -- next: "
                f"<genre>` (section 3), il ne laisse pas vieillir.{hint}"
            ),
        }
        # `override_rejected` absent du verdict = "aucun marqueur de
        # coordinateur lu" -- jamais "pas regarde" (#12096, acceptance 5).
        verdict.update(extra)
        return verdict
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
    p.add_argument("--comments-file", metavar="FILE", default=None,
                   help="JSON list of {author, body} PR comments, scanned for "
                        "a coordinator [G-VAR-3 OVERRIDE] marker (#11708)")
    args = p.parse_args(argv)

    try:
        with open(args.body_file, encoding="utf-8") as f:
            body = f.read()
    except OSError as e:
        print(json.dumps({"guard_pass": False, "reason": f"caller error: {e}"}),
              file=sys.stderr)
        return 2

    override = None
    if args.comments_file:
        try:
            with open(args.comments_file, encoding="utf-8") as f:
                override = parse_override(json.load(f))
        except (OSError, ValueError) as e:
            print(json.dumps({"warning": f"comments unreadable: {e}"}),
                  file=sys.stderr)

    verdict = check(body, override=override)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
