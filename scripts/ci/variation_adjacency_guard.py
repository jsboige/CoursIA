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
and compares. Since #12095 the predecessor genre comes from the MERGED
sequence when the caller provides it (`--merged-prs-file`, resolved through
`resolve_merged_prev_genre`): the `prev:` field is frozen at PR-open time, so
a lane that merges grains while the PR sits open made the gate block PRs the
rule never aimed at (#11963 measured `prev: MED/guard #11841` exact at
redaction but followed by four merged grains -- the real predecessor was
`notebook-python`). The declared `prev:` keeps its documentary value
(exposed as `declared_prev_genre`) but is the source of truth ONLY when the
lane has no merged grain to consult (a first grain, or a fetch failure --
never a crash). The verdict reports which source it used in `prev_source`
(`merged-sequence` | `declared`). Comparing:

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
from variation_light_cap import (  # noqa: E402
    canonicalize_genre,
    genre_counts_light,
    genre_resolves,
)


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
#
# #13730 mirror of #13316: `jsboige` is the shared push identity of every
# lane, not a coordinator. Keeping it here turns the G-VAR-3 ban into a
# permission the lane can grant itself -- the exact opposite of the
# non-vacuity clause above. The other organ (`check_unaddressed_nits`,
# LIFT_OVERRIDE_LOGINS) was hardened by #13316 for the same reason; the
# adjacency guard was missed. Coordinator identity = `myia-ai-01` only.
COORDINATOR_LOGINS = frozenset({"myia-ai-01"})

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

# #13261: the comment-trigger job's entry gate matches any comment CONTAINING
# the marker string, so quoting the marker between backticks to DISCUSS it
# (e.g. explaining a check_unaddressed_nits false positive) arms the parse.
# Fenced blocks and inline code spans are stripped before matching: a marker
# inside code is discussion, not decision -- it grants nothing, rejects
# nothing, and never masks a real override.
#
# #13273: the stripper's notion of code must coincide with what GitHub
# RENDERS as code. Two deviations of opposite polarity, same root:
#   * sous-match (fail-closed): OVERRIDE_EXPECTED_FORM displays the marker
#     between backticks, so a coordinator recopying the recommended form
#     posts a span-wrapped marker that stripping erased -- a silent None,
#     the two-state collapse #12096 closed. A span whose ENTIRE content is
#     a well-formed override is now UNWRAPPED instead of erased.
#   * sur-match (fail-open): an UNCLOSED fence ran to the next ``` only, so
#     a marker after a dangling ``` stayed live while GitHub renders it as
#     code. An unclosed fence now extends to the end of the body.
_CODE_FENCE_RE = re.compile(r"```.*?```|```.*", re.DOTALL)
_CODE_SPAN_RE = re.compile(r"`([^`\n]*)`")


def _strip_code_spans(body: str) -> str:
    """Neutralize code surfaces the way GitHub renders them.

    Fenced blocks become a single space (a space, not the empty string, so
    stripping never glues the tokens on either side into a new match); an
    unclosed fence extends to the end of the body. An inline span whose
    entire content is a well-formed override is unwrapped to that content --
    everything else in a span is erased.
    """
    def _span(m: re.Match[str]) -> str:
        inner = m.group(1).strip()
        return inner if _OVERRIDE_RE.fullmatch(inner) else " "
    return _CODE_SPAN_RE.sub(_span, _CODE_FENCE_RE.sub(" ", body))

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
        re-block (#11963). Since #13261 this verdict is only reached when NO
        well-formed marker exists anywhere in the thread: a later prose
        mention by the same coordinator no longer revokes their earlier
        valid override, and a marker quoted inside code spans is stripped
        before matching (discussion is not decision).
      * well-formed dict -- ``author`` + ``lane`` + ``next_genre`` (kept
        verbatim when outside the enum, per the pass-through of section 1).
    """
    if not comments:
        return None
    fallback: dict | None = None
    for c in reversed(comments):
        login = (c.get("author") or "")
        if isinstance(login, dict):
            login = login.get("login") or ""
        if login not in COORDINATOR_LOGINS:
            continue
        body = _strip_code_spans(c.get("body") or "")
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
            # #13261: do NOT abandon the search here. A later prose mention
            # of the marker must not revoke a valid override posted earlier
            # in the thread -- remember the first (most recent) rejection as
            # the fallback and keep scanning older comments for a
            # well-formed marker. "Malformed" is only the verdict when NO
            # valid override exists anywhere in the thread.
            if fallback is None:
                fallback = {"author": login, "lane": None, "malformed": reason}
            continue
    return fallback


def resolve_merged_prev_genre(merged_prs: list[dict] | None, lane: str | None) -> tuple:
    """Return the lane's REAL predecessor: (canonical_genre, pr_number).

    G-VAR-3 adjacency is a property of the MERGED sequence of the lane, which
    moves while a PR sits open. The `prev:` field in the body is frozen at
    open time, so a PR acquires a false violation purely by aging -- issue
    #11963 measured a `prev: MED/guard #11841` that was exact at redaction
    (2026-08-20T08:27Z) but preceded by four grains merged since (#12025,
    #12022, #12059, #12063, the last being `LIGHT/notebook-python`): the
    declared field said `guard`, the real predecessor was `notebook-python`,
    and the gate blocked a PR the rule never aimed at. The same mechanism
    produces the symmetric false negative (a lane that merged the SAME genre
    while the PR sat open passes despite real adjacency).

    `merged_prs` is the list `gh pr list --state merged --json
    number,body,mergedAt` returns -- the same data source as
    variation_light_cap.py --replay. Each PR is attributed to a lane through
    the SAME extractor as the gate (`grain_tag.parse_grain_tag`), so this
    organ never diverges from the guard on what a tag is. Returns
    ``(genre, pr_number)`` for the most recent lane-attributed PR with a
    parseable Grain tag, or ``(None, None)`` when no such PR exists -- the
    caller then falls back to the declared `prev:` field (a lane with no
    merged grain has no merged sequence to consult). The genre is
    canonicalised so the comparison uses the SAME alias table as the gate.
    """
    if not merged_prs or not lane:
        return (None, None)
    lane_prs = []
    for pr in merged_prs:
        g = gt.parse_grain_tag(pr.get("body"))
        if g is None or g["lane"] != lane:
            continue
        genre = canonicalize_genre(g["genre"])
        if genre is None:
            continue
        lane_prs.append((pr.get("mergedAt") or "", pr.get("number"), genre))
    if not lane_prs:
        return (None, None)
    # Most recent first. `mergedAt` is ISO-8601, lexicographic == chronological.
    lane_prs.sort(key=lambda t: t[0], reverse=True)
    return (lane_prs[0][2], lane_prs[0][1])


def check(body: str | None, override: dict | None = None,
          merged_prev: tuple | None = None) -> dict:
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
    lane = g["lane"]
    declared_prev_genre = canonicalize_genre(pv["genre"])
    declared_prev_pr = pv["pr_number"]

    # Effective predecessor (#12095): the MERGED sequence is the source of
    # truth -- the adjacency is a property of what the lane actually merged,
    # not of what the author believed at open time. The declared `prev:` keeps
    # its documentary value (it says what the author believed) but stops being
    # the gate's authority. Fall back to the declared field when the lane has
    # no merged grain to consult (a first grain, or a lane that has never
    # merged).
    if merged_prev is not None and merged_prev[0] is not None:
        prev_genre = merged_prev[0]
        prev_pr = merged_prev[1]
        prev_source = "merged-sequence"
    else:
        prev_genre = declared_prev_genre
        prev_pr = declared_prev_pr
        prev_source = "declared"

    if genre is None or prev_genre is None:
        return {
            "guard_pass": True, "blocking": False, "adjacent": False,
            "genre": genre, "prev_genre": prev_genre, "lane": lane,
            "prev_source": prev_source,
            "declared_prev_genre": declared_prev_genre, "prev_pr": prev_pr,
            "reason": "genre or prev-genre not normalisable -- adjacency not evaluable",
        }

    src_note = ""
    if prev_source == "merged-sequence" and prev_pr:
        src_note = f" (predecesseur reel: #{prev_pr}, sequence mergee)"

    if genre != prev_genre:
        return {
            "guard_pass": True, "blocking": False, "adjacent": False,
            "genre": genre, "prev_genre": prev_genre, "lane": lane,
            "prev_source": prev_source,
            "declared_prev_genre": declared_prev_genre, "prev_pr": prev_pr,
            "reason": f"genres differ ({genre} vs {prev_genre}) -- no adjacency",
        }

    # Same genre. The LIGHT set is the absolute ban of §2; a DEEP/MED
    # domain-core genre is the advisory judgment of §2. The predicate is
    # the fail-CLOSED one of #13475 (`genre_counts_light`), TIER-AWARE
    # since the ai-01 reserve on #13585 (demande 2): an UNRESOLVED genre
    # (off the closed enumeration) counts LIGHT here too -- before, a
    # `LIGHT/zzz` twice in a row compared equal but escaped `LIGHT_GENRES`
    # membership, so the ban never fired on invented words. A grain whose
    # DECLARED tier is MED/DEEP does not requalify as LIGHT on a genre
    # word alone: the retag is asked (note GENRE-UNKNOWN below), the ban
    # is not applied.
    if genre_counts_light(genre, g.get("tier")):
        unknown_note = ""
        if not genre_resolves(genre):
            unknown_note = (
                f" GENRE-UNKNOWN: `{genre}` n est pas dans l enumeration "
                f"fermee (variation-protocol §1) -- retaguez avec un genre "
                f"canonique, le vocabulaire est ferme par intention."
            )
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
                "prev_source": prev_source,
                "declared_prev_genre": declared_prev_genre, "prev_pr": prev_pr,
                "reason": (
                    f"G-VAR-3: adjacence {genre} apres {prev_genre} REELLE, "
                    f"mais levee par {override['author']} au titre de la "
                    f"clause 24h (section 3 : « merger, ou fermer en nommant "
                    f"le remplacant »). Prochain grain nomme pour la lane "
                    f"{lane} : {override['next_genre']}. Le travail ecrit "
                    f"n'est pas jete ; la lane change de genre au grain "
                    f"suivant.{src_note}"
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
            "prev_source": prev_source,
            "declared_prev_genre": declared_prev_genre, "prev_pr": prev_pr,
            "reason": (
                f"G-VAR-3: {genre} succede a {prev_genre} -- deux grains LIGHT "
                f"consecutifs pour la lane {lane}. La regle est un ban absolu "
                f"(§2): piochez un grain d'UN AUTRE genre, ne retaguez pas "
                f"le meme travail (#11170). Tenu > 24 h : le coordinateur "
                f"tranche par `[G-VAR-3 OVERRIDE] lane {lane} -- next: "
                f"<genre>` (section 3), il ne laisse pas vieillir."
                f"{unknown_note}{hint}{src_note}"
            ),
        }
        # `override_rejected` absent du verdict = "aucun marqueur de
        # coordinateur lu" -- jamais "pas regarde" (#12096, acceptance 5).
        verdict.update(extra)
        return verdict
    return {
        "guard_pass": True, "blocking": False, "adjacent": True,
        "genre": genre, "prev_genre": prev_genre, "lane": lane,
        "prev_source": prev_source,
        "declared_prev_genre": declared_prev_genre, "prev_pr": prev_pr,
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
    p.add_argument("--merged-prs-file", metavar="FILE", default=None,
                   help="JSON list of merged PRs {number, body, mergedAt}, to "
                        "resolve the lane's real predecessor from the merged "
                        "sequence instead of the frozen `prev:` field (#12095). "
                        "Same data source as variation_light_cap.py --replay.")
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

    merged_prev = None
    merged_fallback_note = None
    if args.merged_prs_file:
        try:
            with open(args.merged_prs_file, encoding="utf-8") as f:
                merged_prs = json.load(f)
            g = gt.parse_grain_tag(body)
            merged_prev = resolve_merged_prev_genre(merged_prs, g["lane"] if g else None)
            if merged_prev[0] is None and merged_prs:
                # #12636: the merged window was fetched and is non-empty, but the
                # lane has no grain in it. The guard falls back to the declared
                # `prev:` -- that fallback must be VISIBLE, never silent (the
                # pre-#12095 silent fallback is exactly the defect fixed here,
                # and a window that misses the lane deserves a note, not a mute).
                merged_fallback_note = (
                    f"lane {g['lane'] if g else None} absente du window merge "
                    f"({len(merged_prs)} PRs) -- predecesseur resolu depuis le "
                    f"prev: declare (#12636)"
                )
        except (OSError, ValueError) as e:
            print(json.dumps({"warning": f"merged-prs unreadable: {e}"}),
                  file=sys.stderr)

    verdict = check(body, override=override, merged_prev=merged_prev)
    if merged_fallback_note:
        verdict = dict(verdict)
        verdict["prev_source"] = "declared"
        verdict["prev_fallback"] = merged_fallback_note
        verdict["reason"] = f"{verdict.get('reason', '')} {merged_fallback_note}".strip()
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
