#!/usr/bin/env python3
"""Lane-claim guard -- the "one command before you edit" of issue #9774.

#9774 (mandat user 2026-08-06) diagnosed why two lanes delivered #9764 twice:
the `[CLAIMED]` signal lived on the per-lane dashboard, which (a) does not cross
lanes, (b) is garbage-collected by auto-condensation, and (c) mixed local and
UTC timestamps -- a stamp `2026-08-07T00:52Z` that was actually 00:52 CEST
inverted the cross-lane claim order and nearly got the coordinator to entrench
the wrong priority. None of it was a discipline failure: both workers passed
their `gh pr list` guard, which only sees PUSHED work. The collision is born in
the "I decided to work on X" -> "I pushed" window, where the only signal is the
claim, and the claim was in a silo.

This tool operationalises the worker-side of the fix (the rule change itself
needs user sign-off; this is the mechanism that the rule will call):

  - **check** (default): before editing a file for a grain on issue #N, run
        check_lane_claim.py N --lane myia-po-2024:CoursIA
    It reads the issue comments, reconstructs the claim state per lane, and
    exits 1 if ANOTHER lane holds an active (unreleased) claim -- do not start,
    pick elsewhere. Exit 0 means the way is clear (optionally: your own lane
    already claimed, you are resuming).

  - **--stale-threshold HOURS** (check mode): treat OTHER lanes' claims older
    than HOURS as STALE -- the guard no longer blocks on them, it prints a
    `STALE_CLAIM <lane> <age>h` warning instead. This unblocks a lane when a
    prior claimer died (killed session, re-image, exhausted credit) without a
    release. Age is the server `createdAt`, never the body. The new claimant
    MUST still post its own `[CLAIMED]`; the stale claim is not a silent bypass.

  - **--claim "<intention>"**: post a `[CLAIMED] lane <machine:workspace>`
    comment. GitHub server-stamps it UTC -- the body carries NO timestamp, so
    Defaut 2 (local time wearing a `Z` suffix) is impossible by construction.

  - **--release [--note "..."]**: post a `[RELEASED]` comment, closing the
    active claim of this lane on the issue.

  - **--paths PATH [PATH ...]** (path mode, #9959): given one or more file
    paths/globs, list the OPEN PRs whose `files[]` intersect any of them and
    whose Grain tag names a DIFFERENT lane. Exit 2 with the colliding PRs
    printed by number + lane + intersection paths; exit 0 if the path is
    clear; exit 1 if `gh` itself fails. `--paths` complements -- it does not
    replace -- the issue-claim check above: the issue comment is still the
    authoritative claim record (single locus, server-stamped), `--paths`
    only adds the missing "is there already an OPEN PR on the same file?"
    leg of L898. The motivating incident (2026-08-08 R3D, #9955 / #8696) was
    two lanes of the SAME machine, only minutes apart, each having passed
    the issue-claim check -- there was no other-lane issue claim to trip on.

The authoritative timestamp is the comment's server `createdAt`, NEVER a stamp
written in the body. That is the whole of the Defaut-2 fix.

The lane token is read by `grain_tag.extract_lane` -- the SAME reader the Grain
tag and the G-VAR-2 organ use (#9485, single reader), so a claim comment and a
PR body never disagree on what a lane is.

Limitation (documented): claim state is comment-based. A merged PR that
references the issue is not auto-detected as a release -- the lane should
`--release` (or post `[DONE]`) when its PR lands. Detecting merges is a future
flag; the comment contract is the MVP.

Composite comments, the WRITTEN tie-break (#12624): a comment carrying
several markers is legal ONLY across lines -- each line-anchored marker is
its own event and the walk order applies ("dernier marqueur gagne": a
`[CLAIMED] lane X` followed on a LATER LINE by `[RELEASED] lane X` reduces
to released). A second marker on the SAME line as a head marker is NEVER an
event (the #10228 mid-prose protection must stand -- the claim template
itself carries a mid-line `[RELEASED]` citation), so a one-line "lift +
re-claim" repair comment enacts ONLY the head: the re-claim is silently
swallowed. That shape is flagged (`composite_single_line_markers`) and the
canonical repair gesture is documented in
.claude/rules/lane-claim-protocol.md: ONE comment per marker, a broken
marker is repaired by a NEW comment carrying only `[CLAIMED]`.

Exit codes: 0 ok / 1 blocked (other lane holds active issue claim) /
2 io-or-gh error (issue mode) OR cross-lane OPEN-PR collision (--paths mode).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

# Shared lane reader (#9485) -- see scripts/grain_tag.py.
from grain_tag import extract_lane, lane_marker_residues

# --- markers -----------------------------------------------------------------

# A comment is a claim EVENT only if it carries one of these bracketed markers.
# `[DONE]`/`[RELEASED]`/`[CANCELLED]`/`[ABANDONED]` close a claim; `[CLAIMED]`
# opens one; `[DELIVERED]` (#12320) closes a claim AND records the PR number
# that carries the substance -- the 3rd marker, distinct from `[RELEASED]`
# ("abandoned, reprenez") and `[DONE]` ("my work is in"): `[DELIVERED]` says
# "the substance is on a PR, verify its state before re-claiming". Closing
# semantics are identical to `[RELEASED]` for the reducer (it pops the lane
# from `state`); the `pr_ref` attribute on the event is the durable trace
# that downstream consumers can read. The future v2 conditional semantics
# ("`[DELIVERED]` blocks while PR is OPEN, lifts when PR is CLOSED-without-
# merge, locks permanently when PR is MERGED") is gated on coordinator
# sign-off and lives in a follow-up -- this v1 closes the WRITING GAP, not
# the CONDITIONAL GAP. Read on ISSUE comments (the claim registry per
# #9774), not on the dashboard. Case-insensitive, tolerates inner spaces.
# Line-anchored (`(?m)^...`): a marker only enacts a state change when it
# STARTS a line -- the convention of every `--claim`/`--release` post and every
# coordinator dispatch. A marker MENTIONED mid-sentence in prose is not an event.
# Closes the #10228 false-negative: ai-01's claim comment ended with the
# instructional sentence "Release with `[RELEASED]` when your PR lands" -- the
# unanchored regex took that mid-prose `[RELEASED]` as the final-intent close,
# neutralising the real `[CLAIMED]` and reporting the issue CLEAR while another
# lane held an active claim. `findall` still returns markers in order, so the
# legitimate "last marker wins" design (a `[CLAIMED]\n[DONE]` edit sequence on
# separate lines) is preserved -- only mid-line mentions are rejected.
# Decoration tolerance (#10906): issue comments are markdown-rendered, and
# agents legitimately post `**[CLAIMED] ...**`, `## [CLAIMED] ...`, `- [CLAIMED]
# ...`, `> [CLAIMED] ...` etc. The legacy `^[ \t]*\[` anchor voided every such
# marker (8 voided on 70 issues, including po-2024's [CLAIMED] on #10043 and
# po-2025's on #10038). The prefix group eats up to 6 leading `#>*+-` chars
# (headings / bullets / blockquotes / nested lists), then an optional `**`/`__`
# bold pair opener, then whitespace, then the bracket. A `[` NOT immediately at
# a decorator position (e.g. `- Prose with [CLAIMED] mid-line`) still does not
# match -- the mid-prose non-regression property is preserved.
# #12711 -- the decor class was ASCII-pure, so a leading non-ASCII decoration
# (`→` U+2192, `➡` U+27A1, `➜` U+279C, `»` U+00BB, `•` U+2022, `–` U+2013,
# `—` U+2014) voided the marker to BOTH regexes: the claim was never read (no
# block) and the bare-marker lint never flagged it (no WARN). Measured on
# #12465: `→DELIVERED #12465 ...` posted by po-2026 went unread, po-2027 then
# got CLEAR and delivered the same notebook 15 h later (#12512 / #12638).
# `_DECOR` is the shared, broadened decoration class for all four regexes.
_DECOR = r"(?:[#>*+\-→➡➜»•–—]{1,6}[ \t]*)*"
_MARKER_RE = re.compile(
    r"(?m)^[ \t]*" + _DECOR + r"(?:\*\*|__)?[ \t]*\[\s*(CLAIMED-AMEND|CLAIMED|RELEASED|CANCELLED|ABANDONED|DONE|OVERRIDE|DELIVERED)\s*\]",
    re.IGNORECASE,
)
# #13022 -- CLAIMED-AMEND is listed FIRST (longest first): the alternation
# would still backtrack to it after a bare `CLAIMED` fails at `\]`, but the
# explicit order keeps the intent readable. Measured on #11703: po-2027's
# `[CLAIMED-AMEND] ... -- paths: <8 globs>` (union of two scopes) was a no-op
# for this regex -- the organ kept crediting the earlier epic-wide-unmatched
# `[CLAIMED]` and the amendment existed only for human eyes. The fix makes
# CLAIMED-AMEND an OPEN action (see `_OPEN`): in the walk-order reducer, a
# later open event REPLACES the lane's earlier claim, so the amend comment
# carries the FULL corrected scope (union semantics -- same discipline as the
# pre-fix workaround of re-posting a canonical `[CLAIMED]` with the complete
# path list).
# #11239 -- malformed-marker lint. A claim line written WITHOUT the brackets
# (`CLAIMED #11222 -- ...`) is invisible to `_MARKER_RE` above: the organ
# reports `unattributed_markers: 0` and answers CLEAR to every other lane,
# while the writer believes their lock is posted. Measured 2026-08-16 on
# #11222: two lanes delivered the same fix seven minutes apart (#11230 /
# #11233). This regex is the WARN-side of that gap. Same decoration tolerance
# as `_MARKER_RE`, but the marker word must appear BARE (no `[`), and the line
# must carry a claim motif (`lane <machine:workspace>` or `#N`) so prose that
# merely MENTIONS a marker word is not flagged. Deliberately NOT a parser
# widening -- a malformed line must surface as a warning, never as a claim
# event. The motif tail is on the same line only (no `[\s\S]` cross-line).
_MALFORMED_MARKER_RE = re.compile(
    r"(?m)^[ \t]*" + _DECOR + r"(?:\*\*|__)?[ \t]*"
    r"(CLAIMED-AMEND|CLAIMED|RELEASED|CANCELLED|ABANDONED|DONE|OVERRIDE|DELIVERED)\b"
    r"[^\n]*(?:lane\s+\S+:\S+|#\d+)",
    re.IGNORECASE,
)
# #12624 -- quasi-marker lint (Defaut 1). `_MARKER_RE` requires the EXACT
# keyword alone in brackets; `_MALFORMED_MARKER_RE` requires the keyword BARE
# (no brackets). A bracketed line-head token that is ALMOST a keyword falls
# between the two and is invisible to both: measured 2026-08-22 on #12329,
# `[CLAGED] lane myia-po-2024:CoursIA-2 -- paths: ...` was never read, the
# organ answered CLEAR, and a second lane formalised the same four files
# nine hours later (#12343 / #12433, +375 lines of Lean). Two quasi shapes:
#   - "typo": the first word in brackets is at edit distance <= 2 of a known
#     keyword (`CLAGED` -> CLAIMED, `CLAMED` -> CLAIMED, `RELESED` -> RELEASED);
#   - "suffix": the first word IS a known keyword but the bracket carries
#     extra content (`[RELEASED claim-malformed]`) -- `_MARKER_RE`'s
#     `\[\s*KEYWORD\s*\]` rejects it, so the gesture enacts nothing.
# Same decoration tolerance as `_MARKER_RE`; same claim-motif gate as
# `_MALFORMED_MARKER_RE` (a `lane <tok>` / `#N` / `paths:` on the line) so
# prose that merely mentions an almost-word is not flagged. WARN-only by
# design: the quasi marker is SIGNALED, never auto-corrected and never
# enacted -- an auto-correction would guess intent where the writer must
# re-post the canonical form themselves.
_QUASI_MARKER_RE = re.compile(
    r"(?m)^[ \t]*" + _DECOR + r"(?:\*\*|__)?[ \t]*"
    r"\[([A-Za-z][A-Za-z_-]{2,})((?:[ \t][^\]\n]*)?)\]",
    re.IGNORECASE,
)
# #12624 -- the claim motif that gates BOTH quasi shapes. Same selectivity
# rationale as `_MALFORMED_MARKER_RE`'s tail: a bracketed almost-word on a
# line that carries no claim motif is prose, not a failed gesture.
_CLAIM_MOTIF_RE = re.compile(r"(?:lane\s+\S+:\S+|#\d+|paths?\s*:)", re.IGNORECASE)
# #12624 -- composite single-line detection (Defaut 2). A line-anchored head
# marker followed LATER ON THE SAME LINE by another exact bracketed keyword
# carrying a claim motif: the incident's repair comment was one single line
# `[RELEASED claim-malformed] ignore ... Re-claim ici : [CLAIMED] lane X --
# paths: ...`. Only the HEAD token is line-anchored, so only the head can be
# an event; the mid-line `[CLAIMED]` is deliberately NOT one (#10228
# mid-prose protection -- the claim template itself carries a mid-line
# `[RELEASED]`). The writer must learn that their re-claim was not read.
_MIDLINE_KEYWORD_RE = re.compile(
    r"\[\s*(CLAIMED|RELEASED|CANCELLED|ABANDONED|DONE|OVERRIDE|DELIVERED)\s*\]",
    re.IGNORECASE,
)
_KEYWORDS = ("CLAIMED", "RELEASED", "CANCELLED", "ABANDONED", "DONE", "OVERRIDE", "DELIVERED")


def _blank_keeping_shape(line: str) -> str:
    """Meme longueur, memes fins de ligne, tout le reste efface."""
    return "".join(c if c in "\r\n" else " " for c in line)


def _mask_fenced_blocks(body: str) -> str:
    """Blanchit les blocs de code fences -- ce que GitHub rend comme du CODE.

    Signale par po-2026 le 2026-08-20, mesure firsthand le meme jour : citer un
    marqueur VERBATIM dans un commentaire d'arbitrage le RESSUSCITE. Toutes les
    formes de citation en debut de ligne matchent `_MARKER_RE` -- blockquote,
    puce, gras, et le bloc fence, qui est precisement la forme canonique pour
    citer un marqueur mot pour mot. L'evenement est alors attribue a la lane
    nommee dans la citation, avec le `createdAt` du commentaire CITEUR, donc
    plus recent : l'arbitrage qui devait clore un claim le rouvre.

    Consequence mesuree : un `[OVERRIDE]` de ai-01 qui cite le `[CLAIMED]`
    qu'il arbitre reinstalle ce claim par-dessus son propre verdict.

    Le remede est le meme principe que le correctif YAML de #11881 quelques
    heures plus tot : scanner ce que le CONSOMMATEUR rend, pas les octets
    bruts. Un bloc fence est de la citation par construction -- GitHub ne
    l'interprete jamais comme un acte, l'organe non plus.

    Portee volontairement etroite -- les FENCES seulement :

    - le blockquote `> [CLAIMED]` et la puce `- [CLAIMED]` restent des
      marqueurs valides : #10906 les a explicitement rehabilites apres avoir
      mesure 8 marqueurs legitimes annules par l'ancre stricte. Les exclure
      ici rouvrirait ce faux negatif-la ;
    - le bloc indente a 4 espaces n'est pas masque : l'indentation appartient
      aussi aux listes imbriquees, ou les marqueurs sont legitimes.

    Une fence non refermee masque jusqu'a la fin -- c'est exactement ce que
    GitHub affiche, donc ce qu'un relecteur humain voit.

    La longueur est preservee caractere pour caractere : les offsets des
    matches restent valides sur le corps ORIGINAL, que `_line_for_match`
    continue de lire pour extraire la ligne verbatim.
    """
    out: list[str] = []
    fence: str | None = None
    for line in body.splitlines(keepends=True):
        stripped = line.lstrip()
        if fence is None:
            opener = None
            for ch in ("`", "~"):
                if stripped.startswith(ch * 3):
                    opener = ch * (len(stripped) - len(stripped.lstrip(ch)))
                    break
            if opener is None:
                out.append(line)
            else:
                fence = opener
                out.append(_blank_keeping_shape(line))
        else:
            out.append(_blank_keeping_shape(line))
            tail = stripped.rstrip()
            if tail.startswith(fence) and not tail.strip(fence[0]):
                fence = None
    return "".join(out)


# #13022 -- `[CLAIMED-AMEND]` is an OPEN action. Semantics (the one chosen for
# the fix): the amend comment REPLACES the lane's previous claim scope -- the
# walk-order reducer already does this for any later open event
# (`state[ev.lane] = ev`), so mapping CLAIMED-AMEND to "open" gives
# replace-previous-scope for free. The amend line must therefore carry the
# FULL corrected scope (a `paths:` union), exactly like the canonical
# re-[CLAIMED] workaround it supersedes. An amend WITHOUT a paths clause
# replaces the previous scope with EPIC-WIDE (legacy unscoped semantics) --
# deliberate, fail-CLOSED: an amendment that names no scope is not permissive.
_OPEN = {"CLAIMED", "CLAIMED-AMEND"}
_CLOSE = {"RELEASED", "CANCELLED", "ABANDONED", "DONE", "DELIVERED"}
# `[OVERRIDE] lane <machine:workspace>` (#10223): coordinator adjudication --
# GRANTS the claim to the named lane and CLOSES every other lane's claim in one
# gesture. Distinct from CLAIMED (grants to one) and RELEASED/DONE (closes one):
# override does both at once, which is the only mechanical trace of a
# coordinator merging against a held claim (the gap that let #10169 / #10161 be
# merged without a written adjudication). Additive: the existing markers keep
# their semantics, so no prior test changes.
#
# `paths:` clause (#10342 for [OVERRIDE], extended to [CLAIMED]/[RELEASED] by
# #10419): an optional path scope after the lane token. When present on an
# [OVERRIDE], the "close all others" effect is BOUND to the listed paths
# (fnmatch, comma-separated). When present on a [CLAIMED], the claim is SCOPED
# to those paths -- two lanes whose scoped claims do NOT intersect are free to
# work the same issue in parallel (the nominal pattern for multi-instance
# audits like #10382, one lane per notebook). Other lanes remain FREE on paths
# outside the scope. Syntax: `[CLAIMED] lane <machine:workspace> -- paths: g1, g2`.
# Without the clause, the marker is EPIC-WIDE (legacy semantics, preserved):
# an unscoped [CLAIMED] blocks every other lane, an unscoped [OVERRIDE] closes
# every other lane -- exactly as before #10342/#10419.
_OVERRIDE = {"OVERRIDE"}
# The token is OPTIONAL; the lane stays REQUIRED (an override without a named
# beneficiary is unattributed, per existing semantics). Capture groups:
# 1 = comma-separated path list (already stripped of surrounding spaces).
# Recognised on [CLAIMED], [RELEASED] (attached; the reducer treats release as
# a full lane-close, so the scope is informational there), [OVERRIDE], and
# [CLAIMED-AMEND] (#13022: the clause is the whole point of an amend -- it
# names the corrected/union scope that replaces the lane's previous claim).
# Same leading-decoration tolerance as `_MARKER_RE` (#10906). In practice the
# reducer feeds this regex the `_line_for_match` output (which starts at the
# `[`), so the legacy `^[ \t]*\[` anchor already worked -- the prefix group is
# defense-in-depth for direct calls on a full decorated marker line. The path
# list capture deliberately does NOT strip a trailing `**`/`__` (closing pair
# of a bold-wrapped claim): `paths: dir/**` is a legitimate recursive glob,
# indistinguishable from a closing decorator by suffix alone. Trailing `*` in
# fnmatch matches empty, so a captured `glob**` still matches `glob`.
_PATHS_CLAUSE_RE = re.compile(
    r"(?im)^[ \t]*" + _DECOR + r"(?:\*\*|__)?[ \t]*\[\s*(?:CLAIMED-AMEND|CLAIMED|RELEASED|OVERRIDE)\s*\][^\n]*?paths\s*:\s*([^\n]+?)\s*$"
)
# #12320 -- `[DELIVERED] lane <m:w> -- PR #N`. The PR reference is OPTIONAL on
# a DELIVERED marker (a DELIVERED without a PR is functionally equivalent to a
# RELEASED, but the vocabulary choice still records the writer's intent of
# "my work is in a PR I have the number for"). Captured as an integer (the
# first `#\d+` on the marker line), or None when absent. The `PR #` prefix is
# required (loose `\d+` would catch issue numbers and other integers) so the
# intent is unambiguous and the writer cannot accidentally invent a PR
# reference that the consumer will go fetch. The fetch itself (state of PR
# N) is left to consumers: the reducer stays pure.
_DELIVERED_PR_REF_RE = re.compile(
    r"(?im)\bPR\s*#(\d+)\b"
)
# #10958 -- the annotation suffix separator. Fleet claims append a trailing
# annotation after the glob list: `paths: a/** -- 2026-08-11T18:10Z` (body
# timestamp) or `paths: .../** — Phase 2 : ...` (prose rationale). The clause
# regex swallows it into the LAST glob, which then matches no tracked file and
# the claim silently ends up non-blocking (fail-open). The separator must be
# whitespace-delimited on BOTH sides so a `foo--bar.py` (internal dashes, no
# spaces) is never cut. Em/en dashes are included because fleet markers use
# both (` -- ` in timestamps, ` — ` in prose rationales).
_ANNOTATION_SUFFIX_RE = re.compile(r"\s+(?:--|—|–)\s+")
# #12052 -- the parenthetical annotation separator. Fleet markers sometimes
# append a prose parenthetical after the glob list (often a tranche or phase
# label): `paths: MyIA.AI.Notebooks/GenAI/** (Phase 2, tranche A)`. Without
# this separator, the parenthetical rides the LAST glob into `_split_paths_brace_aware`
# where the comma inside the parens splits it further -- yielding one or more
# GLOB-FREE fragments that fnmatch will never match (e.g. `tranche A)`), so
# the scoped claim silently ends up with a PARTIALLY-DEAD scope and is
# lifted to epic-wide by `_empty_scope_in` (fail-CLOSED, not fail-open -- a
# broken claim is not a permissive claim). The separator requires a SPACE
# before the opening paren so legitimate filename characters (e.g. a glob
# with a paren in it -- rare but possible) are not cut.
_PAREN_ANNOTATION_RE = re.compile(r" \(")
# #12072 -- off-marker scope declaration. `_PATHS_CLAUSE_RE` reads the `paths:`
# clause ONLY on the marker line (`[^\n]*?` forbids the newline): a clause
# written on its OWN line in a separate paragraph is read as None -> epic-wide,
# silently, while the declaring lane believes it scoped. This regex finds a
# scope-declaration-shaped line ANYWHERE in the body (line-start `paths:` /
# `Paths:` / `Path :`, case-insensitive, same decoration tolerance as the
# marker regexes) so the event can expose it and the lint can say so instead of
# staying silent. Used only as a SIGNAL (`scope_declared_off_marker`) -- the
# claim is NOT re-classified (see #12072: re-reading an off-marker prose line
# as the machine clause would make the scope depend on an heuristic).
_OFF_MARKER_SCOPE_RE = re.compile(
    r"(?im)^[ \t]*" + _DECOR + r"(?:\*\*|__)?[ \t]*paths?\s*:\s*([^\n]+?)\s*$"
)


class ClaimEvent(dict):
    """Typed-ish view over a parsed claim event.

    Keys: lane (str|None), action ("open"|"close"|"override"), marker (str upper),
    created_at (str ISO, server UTC), author (str|None), url (str|None),
    intent (str|None). `created_at` comes from the comment's server field, never
    from the body. `intent` is the marker line without the bracket prefix --
    the human-readable scope announcement that turns a BLOCKED verdict
    (otherwise opaque) into an actionable list of disjoint intentions (#10395
    Variante 2).
    """

    @property
    def lane(self) -> str | None:
        return self.get("lane")

    @property
    def is_open(self) -> bool:
        return self.get("action") == "open"

    @property
    def is_delivered(self) -> bool:
        """True on a `[DELIVERED]` marker (#12320).

        The reducer treats it like any other close marker (the lane is popped
        from `state`), but the predicate is the readable form for consumers
        that want to distinguish "abandoned" from "delivered to a PR". The
        `pr_ref` attribute (int | None) holds the captured PR number when
        the marker line carried `PR #N`; otherwise None.
        """
        return self.get("marker") == "DELIVERED"

    @property
    def pr_ref(self) -> int | None:
        """The PR number captured from a `[DELIVERED] … PR #N` marker (#12320).

        None on every non-DELIVERED marker, and on a DELIVERED marker whose
        line carried no `PR #N` (a legal but unreferenced close). Future v2
        conditional logic (PR OPEN = block, PR MERGED = lock) reads this
        field to drive its gate; v1 only surfaces it in the JSON summary.
        """
        return self.get("pr_ref")

    @property
    def is_override(self) -> bool:
        return self.get("action") == "override"

    @property
    def intent(self) -> str | None:
        """Marker-line body excerpt (#10395 Variante 2).

        The portion of the comment AFTER the bracketed marker, with leading
        punctuation / spaces stripped, capped at ~120 characters. The point
        is to give a BLOCKED message enough context to discriminate "two
        lanes working on disjoint notebooks of the same EPIC" (legitimate
        collision detection) from "two lanes working on the same file"
        (real collision). The marker is stripped so the excerpt reads
        naturally -- `lanes myia-po-2025:CoursIA-2 — taxonomy coverage
        analysis notebook` is the intent that justifies the claim.
        """
        return self.get("intent")

    @property
    def created_at(self) -> str | None:
        return self.get("created_at")

    @property
    def marker(self) -> str | None:
        return self.get("marker")

    @property
    def author(self) -> str | None:
        return self.get("author")

    @property
    def url(self) -> str | None:
        return self.get("url")

    @property
    def paths(self) -> list[str] | None:
        """Optional path scope (#10342 OVERRIDE, #10419 CLAIMED/RELEASED).

        None when the marker is epic-wide (no `paths:` clause). A non-None value
        on an [OVERRIDE] binds its "close all others" effect to the listed globs;
        on a [CLAIMED] it SCOPES the claim, so two lanes whose paths do NOT
        intersect (fnmatch, `_path_matches`) are free to work the same issue in
        parallel. The reducer preserves the full `paths` payload; the check
        filters `others` by scope intersection (`_filter_by_claim_scope`).
        """
        return self.get("paths")

    @property
    def scope_declared_off_marker(self) -> list[str]:
        """#12072 -- scope-declaration lines found OFF the marker line.

        Non-empty ONLY on an epic-wide event (`paths is None`) whose comment
        nevertheless contains a line-start `paths?` clause elsewhere (e.g. a
        `Paths: ...` paragraph under the `[CLAIMED]` line). The reducer could
        not read that clause (`_PATHS_CLAUSE_RE` is marker-line-anchored), so
        the claim reduced to EPIC-WIDE while the declaring lane believed it
        scoped. This field is a SIGNAL, not a re-classification: the claim is
        NOT lifted back to a scoped state (that would make the scope depend on
        a heuristic). Consumers (JSON summary, lint WARN) use it to say so
        explicitly instead of staying silent.
        """
        return self.get("scope_declared_off_marker") or []

    @property
    def unparseable_scope(self) -> list[str]:
        """Subset of `paths` that survived parse but still contain `{` or `}`.

        #10597 hardener: a lane that writes `paths: foo-{a,b-*.yaml`
        (unclosed brace) yields fnmatch-garbage on expansion. The safe read
        is to treat the claim as EPIC-WIDE (`conservateur: in case of doubt,
        block rather than let through`) -- `_run_check` reads this list and
        lifts the scope back to epic-wide when non-empty.
        """
        return self.get("unparseable_scope") or []

    @property
    def lane_scope_residue(self) -> list[str]:
        """Malformed-lane residues on the marker line (#12719).

        A bare date after the token (`myia-po-2023:CoursIA 2026-08-23`) or a
        trailing sentence period (`myia-po-2023:CoursIA.`). The lane regex
        fix makes both parse to the bare lane, so the claim is NOT blocked
        anymore; this witness lists the residue so the declaring lane can SEE
        its marker was malformed instead of the organ silently reinterpreting
        it. Report-only -- a malformed marker that parses is functional.
        """
        return self.get("lane_scope_residue") or []

    @property
    def empty_scope(self) -> list[str]:
        """Subset of `paths` matching ZERO tracked files in the repo (#10958).

        Unlike `unparseable_scope` (pure parse residue, computable without
        the repo), this witness requires a `git ls-files` walk, so it is
        attached at the CHECK layer (`_run_check`), not at parse. Empty when
        every glob locks at least one real file, or when the walk failed
        (best-effort: we cannot prove deadness, so we do not lift).
        """
        return self.get("empty_scope") or []


def _line_for_match(body: str, m: re.Match) -> str:
    """Return the verbatim source line carrying a marker match (marker included).

    Walks from the end of the match to the end of its line so the caller sees
    any trailing content (e.g. `[CLAIMED] #9764 - myia-po-2025:CoursIA`). This
    is the per-marker generalisation of the old `_last_marker_line`: the
    #10881 addendum fix reads EACH marker line, not just the last one.
    """
    tail = body[m.end():]
    nl = tail.find("\n")
    return (m.group(0) + (tail if nl == -1 else tail[:nl])).rstrip("\r")


def _intent_from_line(line: str | None) -> str | None:
    """Marker-line excerpt with the bracketed marker stripped (#10395 V2).

    The per-marker variant of the old `_extract_marker_intent`: strips the
    `[MARKER]` from a single line, trims leading punctuation, caps at 120
    chars. Returns None for a bare `[CLAIMED]` (nothing after the bracket).
    """
    if not line:
        return None
    text = _MARKER_RE.sub("", line, count=1)
    text = text.strip().lstrip(":—-•| ").strip()
    if not text:
        return None
    if len(text) > 120:
        text = text[:120].rstrip() + "…"
    return text


def _parse_claim_events(comment: dict) -> list[ClaimEvent]:
    """One ClaimEvent per bracketed marker line -- the #10881 reducer fix.

    A comment can LEGITIMATELY carry markers for several lanes: the natural
    shape of a coordinator arbitration is `[RELEASED] lane A` then
    `[CLAIMED] lane B -- paths: X`. The legacy single-event reader kept only
    the LAST marker (final intent): every marker of the comment was attributed
    to ONE lane (the first `lane <token>` in the whole body) with the LAST
    marker's paths clause, and intermediate `[RELEASED]`s were lost. Measured
    on #10678 2026-08-14 (ai-01's 07:30:08Z comment): po-2024:CoursIA-2 was
    credited with ai-01's gate-file scope while its own two notebooks were
    claimed by no one, and ai-01's epic-wide 07:06:23Z claim stayed active
    against every other lane.

    This function treats each marker line independently, with the lane ITS
    OWN LINE names (marker line first, whole body as fallback), its own
    paths clause, its own intent. `compute_active_claims` walks these events
    in order, so a comment can release one lane and open another, and a
    `[CLAIMED]\n[DONE]` sequence on separate lines still reduces to inactive
    (open then close). Per-marker fields keep the #10342/#10419 scope, the
    #10395 Variante-1 fallback and the #10597 hardener semantics.
    """
    body = comment.get("body") or ""
    author = (comment.get("author") or {}).get("login")
    created_at = comment.get("createdAt")
    url = comment.get("url")
    events: list[ClaimEvent] = []
    # Les blocs fences sont de la citation, jamais un acte (voir
    # `_mask_fenced_blocks`). Le masque preserve les longueurs, donc les
    # offsets restent valides sur `body` -- que `_line_for_match` relit.
    masked_body = _mask_fenced_blocks(body)
    # #12072 -- pre-computed off-marker scope declaration lines. `_PATHS_CLAUSE_RE`
    # only ever reads the marker's OWN line, so a `paths:`/`Paths:`/`Path :`
    # clause written on a separate line of the same comment is dead prose from
    # the reducer's point of view (epic-wide, silently). We scan the fenced-masked
    # body once and hand each event its own matching lines: the masked body
    # preserves offsets, so `_line_for_match` can still resolve verbatim text on
    # the real `body`. The clause regex is line-anchored to a line STARTING with
    # `paths?`, so it can never match the marker line itself (which starts with
    # the bracket after decoration) -- no overlap with the marker's own clause.
    off_marker_scope_lines = [
        _line_for_match(body, om).strip() for om in _OFF_MARKER_SCOPE_RE.finditer(masked_body)
    ]
    for m in _MARKER_RE.finditer(masked_body):
        marker = m.group(1).upper()
        line = _line_for_match(body, m)
        if marker in _OPEN:
            action = "open"
        elif marker in _OVERRIDE:
            action = "override"
        else:
            action = "close"
        paths = _extract_paths_clause(line) if line else None
        # #12320 -- [DELIVERED] carries an optional `PR #N` reference on the
        # same marker line. Parse it here so downstream consumers (the JSON
        # summary, future v2 conditional logic) can read the PR number without
        # re-walking the body. `pr_ref` is the integer number (e.g. 12271), or
        # None when absent or on a non-DELIVERED marker. The PR state itself
        # (OPEN/CLOSED/MERGED) is left to the consumer to fetch via `gh` --
        # the reducer stays pure and side-effect-free, by design.
        pr_ref = _extract_delivered_pr_ref(line) if marker == "DELIVERED" else None
        # Lane attribution per marker line: the marker's OWN line first, then
        # the whole body as fallback. The line-first order is the fix -- the
        # legacy whole-body search always picked the FIRST `lane <token>` of
        # the comment, mis-attributing every later marker to that lane.
        lane = extract_lane(line, marker_line=line)
        if lane is None:
            lane = extract_lane(body, marker_line=line)
        # #12719 -- malformed-lane witness (bare date / trailing period).
        # Report-only: the claim is attributed to the bare lane either way.
        lane_residue = lane_marker_residues(line)
        events.append(ClaimEvent(
            lane=lane,
            lane_scope_residue=lane_residue,
            action=action,
            marker=marker,
            created_at=created_at,
            author=author,
            url=url,
            paths=paths,
            # #12320 -- pr_ref is populated ONLY for DELIVERED markers (the
            # rest keep None). The summary exposes it so a consumer reading
            # "my_active_claim: false" can still surface the historical PR
            # reference for forensics, and so a v2 conditional reducer can
            # gate the close on the PR state.
            pr_ref=pr_ref,
            # #10597 hardener -- preserve the unparseable subset of the scope
            # (residual `{` or `}` after `_expand_brace_groups`). The reducer
            # and check layer use this to lift the claim back to EPIC-WIDE
            # when the scope cannot be matched by fnmatch. Without this field
            # an unclosed-brace scope would silently degrade to "non-blocking
            # accidental empty" -- the exact defect that motivated #10597.
            unparseable_scope=_unparseable_scope_in(paths) if paths else [],
            intent=_intent_from_line(line),
            # #12072 -- structured signal for a scope declared OFF the marker
            # line (line-start `paths?` elsewhere in the comment, e.g. a
            # `Paths: ...` paragraph below the `[CLAIMED]` line). The reducer
            # read `paths is None` -> the claim reduced to EPIC-WIDE while the
            # declaring lane believed it scoped. The field only exists when
            # the marker's OWN line carried no clause (a captured scope needs
            # no warning); the lint layer decides how loudly to say so.
            scope_declared_off_marker=off_marker_scope_lines if paths is None else [],
            # #11755: the body is needed downstream by `_lint_claim_events`
            # to mine for an inferred `Path:` clause when the marker has no
            # `paths:` field. Carrying it on the event (one extra reference)
            # avoids re-walking the comments list at lint time and keeps the
            # per-marker attribution accurate (a comment with N markers
            # yields N events all pointing at the same body).
            _body=body,
        ))
    return events


def parse_claim_event(comment: dict) -> ClaimEvent | None:
    """Classify one issue comment into a claim event, or None if not a marker.

    Legacy single-event view: the LAST bracketed marker of the comment is the
    final intent (backward-compatible with every existing caller and the
    Defaut-2 / lane / scope semantics). The full reader is `_parse_claim_events`
    -- one event per marker line (#10881 addendum), used by `_sort_events`; for
    a single-marker comment the two views are identical. The lane is read by
    `extract_lane`; None when the body carries no lane token (surfaced as
    "unattributed", never guessed). The timestamp is the comment's server
    `createdAt` -- the Defaut-2 fix: body stamps are not trusted.
    """
    events = _parse_claim_events(comment)
    return events[-1] if events else None


def _split_paths_brace_aware(raw: str) -> list[str]:
    """Split a comma-separated path list on commas OUTSIDE `{...}` groups.

    A scope like `search-{6,8,9}-*.yaml` uses commas as brace alternatives,
    not as list separators. A naive `raw.split(",")` fragments it into
    `["search-{6", "8", "9}-*.yaml"]` -- three invalid globs that `fnmatch`
    will never match, so the claim silently ends up EPIC-WIDE by accident
    (#10597). This splitter tracks brace depth and only splits on depth-0
    commas, keeping each brace group intact. Empty fragments from stray
    commas are dropped (`paths: a, , b` -> `["a", "b"]`).
    """
    parts: list[str] = []
    buf: list[str] = []
    depth = 0
    for ch in raw:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth = max(0, depth - 1)
        if ch == "," and depth == 0:
            parts.append("".join(buf).strip())
            buf = []
        else:
            buf.append(ch)
    parts.append("".join(buf).strip())
    return [p for p in parts if p]


def _expand_brace_groups(pattern: str) -> list[str]:
    """Expand a single `{a,b,c}` group into plain globs.

    fnmatch supports `*`, `?`, `[seq]`, `[!seq]` but NOT `{a,b}`. A pattern
    like `search-{6,8,9}-*.yaml` therefore matches nothing via fnmatch.
    This expands the FIRST brace group into sibling globs
    (`search-6-*.yaml`, `search-8-*.yaml`, `search-9-*.yaml`); nested
    groups would need recursion, but no scope in the fleet uses nesting.
    Patterns without braces are returned unchanged.
    """
    m = re.search(r"\{([^{}]*)\}", pattern)
    if not m:
        return [pattern]
    alts = [a for a in m.group(1).split(",") if a]
    if not alts:
        return [pattern]
    return [
        f"{pattern[:m.start()]}{alt}{pattern[m.end():]}" for alt in alts
    ]


def _extract_paths_clause(text: str | None) -> list[str] | None:
    """Parse the optional `paths: <comma-list>` clause from a marker line.

    Recognised on [CLAIMED], [RELEASED], [OVERRIDE], and [CLAIMED-AMEND]
    marker lines (#10342 introduced the clause for [OVERRIDE]; #10419
    extended it to [CLAIMED] and [RELEASED] so disjoint scoped claims no
    longer false-block each other on a multi-instance issue; #13022 added
    [CLAIMED-AMEND], where the clause names the replacement scope). Returns
    the trimmed path list, or None when the
    clause is absent -- the marker is then EPIC-WIDE (legacy semantics: an
    unscoped [CLAIMED] blocks every other lane, an unscoped [OVERRIDE] closes
    every other lane). Brace groups are expanded to sibling globs so that
    `paths: search-{6,8,9}-*.yaml` yields three matchable patterns instead of
    one silently-EPIC-WIDE accident (#10597).

    #10597 -- hardener: a scope containing UNCLOSED braces (e.g.
    `paths: foo-{a,b-*.yaml`) cannot be parsed to a matchable glob set.
    After expansion, any pattern still containing `{` or `}` is reported
    via `_unparseable_scope_in`; the caller MUST treat such a claim as
    EPIC-WIDE (conservateur: in case of doubt, block rather than let
    through). See `_run_check` for the integration.

    #10958 -- annotation suffix: a trailing ` -- <rest>` (or ` — <rest>`)
    after the glob list is TRUNCATED before the split. The clause regex
    captures to end of line, so `paths: a/** -- 2026-08-11T18:10Z` used to
    yield the single glob `a/** -- 2026-08-11T18:10Z` -- which matches no
    tracked file, so the scoped claim never blocked anyone (fail-open). The
    separator is whitespace-delimited on both sides, so an INTERNAL unspaced
    dash sequence (`foo--bar.py`) survives untouched; the truncation cuts at
    the FIRST separator, so glob content after it stays out regardless of
    how the annotation is punctuated.
    """
    m = _PATHS_CLAUSE_RE.search(text or "")
    if not m:
        return None
    raw = m.group(1)
    m_suffix = _ANNOTATION_SUFFIX_RE.search(raw)
    if m_suffix:
        raw = raw[:m_suffix.start()]
    # #12052 -- cut a trailing parenthetical annotation off the glob list.
    # Mirrors the `_ANNOTATION_SUFFIX_RE` discipline: a ` (` (space +
    # opening paren) introduces prose, not a glob. Cutting at the FIRST one
    # keeps the entire prose annotation (whatever's between the parens) out
    # of the split. An internal paren (no leading space) is left untouched
    # -- legitimate filename characters.
    m_paren = _PAREN_ANNOTATION_RE.search(raw)
    if m_paren:
        raw = raw[:m_paren.start()]
    parts = _split_paths_brace_aware(raw)
    expanded: list[str] = []
    for p in parts:
        for e in _expand_brace_groups(p):
            expanded.append(e)
    return expanded or None


def _extract_delivered_pr_ref(line: str | None) -> int | None:
    """Return the integer PR number from a `[DELIVERED] ... PR #N` line (#12320).

    `None` when the line carries no `PR #N` reference (a legal but
    unreferenced DELIVERED). The marker word must already have been
    matched (this helper is a pure extractor; it does NOT validate the
    marker itself). The `PR` prefix is required so a stray `#1234` in
    the body cannot be mistaken for a PR reference -- the writer must
    explicitly name `PR #N` for the close to record the linkage.
    """
    if not line:
        return None
    m = _DELIVERED_PR_REF_RE.search(line)
    return int(m.group(1)) if m else None


def _unparseable_scope_in(parts: list[str] | None) -> list[str]:
    """Return the subset of `parts` that look UNMATCHABLE: brace residue
    (`{` / `}`) OR a glob-free prose fragment (no `/`, no fnmatch meta).

    After `_extract_paths_clause` and `_expand_brace_groups`, any pattern
    residue containing braces is a SCOPE THAT FNMATCH WILL NEVER MATCH
    (fnmatch knows `*` `?` `[seq]` `[!seq]` -- not `{a,b}`). The safe
    read is to treat the claim as epic-wide (conservateur -- #10597
    acceptance #2). The list returned here is the witness, so the
    reducer and the JSON audit can surface it without re-parsing.

    #12052 -- a second class of unmatchable residue: PROSE WITHOUT SLASHES OR
    METACHARACTERS (e.g. `tranche A)` after a parenthetical annotation split).
    Such a fragment survives the brace-aware comma split because it carries no
    `{` and no `,` at depth 0, but fnmatch still will not match it (fnmatch
    uses the entire string as a glob; a bare word like `tranche` matches only
    files literally named `tranche`). Pre-#12052 the witness silently skipped
    these and the dead-glob hardener (`_empty_scope_in`) was the only line of
    defence -- but `_empty_scope_in` requires a `git ls-files` walk and
    surfaces the problem AFTER the lift has already fired. This witness
    surfaces the FRAGMENT in the JSON so the declaring lane can SEE the
    truncation was incomplete. Empty when the scope is fully parseable.
    Empty on `parts is None` (no clause -> epic-wide semantics handled by
    the caller).
    """
    if not parts:
        return []
    fnmatch_metas = set("*?[!")
    residue: list[str] = []
    for p in parts:
        if "{" in p or "}" in p:
            residue.append(p)
            continue
        # A glob contains at least one path separator OR one fnmatch meta.
        # A bare word without either is prose that fnmatch will treat as a
        # literal filename (matching only the literal string) -- on tracked
        # files this is effectively never the intent.
        if "/" not in p and not any(m in p for m in fnmatch_metas):
            residue.append(p)
    return residue


def _empty_scope_in(parts: list[str] | None,
                    tracked: list[str] | None) -> list[str]:
    """Return the subset of `parts` matching ZERO tracked files (#10958).

    The dead-glob witness: unlike `_unparseable_scope_in` (a parse residue),
    this requires the `git ls-files` walk, so the caller passes `tracked`
    (fetched once per check). Returns [] when `tracked` is None -- the walk
    failed (not a repo, git missing): we cannot prove deadness, so the
    fail-safe lift does NOT fire (best-effort, mirroring the lint). A
    NON-empty result means the glob locks nothing; `_filter_by_claim_scope`
    treats an ENTIRELY-dead scope as epic-wide (a broken claim is not a
    permissive claim).
    """
    if not parts or tracked is None:
        return []
    return [p for p in parts if not _glob_matches_tracked(p, tracked)]


def _claim_scope_effectively_epic_wide(ev: ClaimEvent) -> bool:
    """Return True if `ev`'s declared scope locks ZERO tracked files (#11098).

    Mirrors the #10958 fail-safe used by `_filter_by_claim_scope`: a claim
    whose `paths:` clause globs ALL fail to match any tracked file is broken,
    not permissive -- the safe hypothesis is that the lane meant something.
    An effectively-epic-wide claim intersects any override scope (epic-wide
    semantics), so the override closes it just like a plain `[CLAIMED]`
    without a `paths:` clause.

    The witness `empty_scope` is attached by `_run_check` after the tracked
    walk; reducer-direct callers (unit tests passing events straight in)
    carry no witness and the helper degrades to False -- no lift, no
    behaviour change for the unit-test paths. This is the read-side mirror
    of `_filter_by_claim_scope`'s caller-side lift (#10958 + #11098).
    """
    paths = ev.get("paths")
    if not paths:
        return False  # the no-`paths` branch is handled by the caller
    empty = ev.get("empty_scope")
    if empty is None:
        return False  # reducer-direct / no witness -> no lift
    return len(empty) >= len(paths)


def compute_active_claims(
    events: list[ClaimEvent],
    pr_states: dict[int, str] | None = None,
) -> tuple[dict, list[ClaimEvent]]:
    """Reduce a chronologically-ordered event list to active claims per lane.

    Returns `(active_by_lane, unattributed)`:
      - `active_by_lane`: {lane: ClaimEvent} for lanes whose LATEST event is an
        open (or the lane named by the latest override). Computed by walking
        events in order (caller sorts); later events overwrite earlier ones, a
        close removes the lane, and an **override** (#10223) grants the claim to
        its named lane while closing every other lane -- the only event type
        that touches more than one lane at once.
      - `unattributed`: events whose body carried a marker but no lane token --
        the tool surfaces them for manual verification, it does not guess.
        An override with no lane token is unattributed (an adjudication must
        name its beneficiary).
    """
    state: dict[str, ClaimEvent] = {}
    unattributed: list[ClaimEvent] = []
    for ev in events:
        if ev.lane is None:
            unattributed.append(ev)
            continue
        if ev.is_override:
            # Coordinator adjudication (#10223): grant to this lane. The
            # optional `paths:` clause (#10342, #10505) BOUNDS the "close
            # others" effect to the override's scope instead of closing every
            # other lane unconditionally. An unscoped override keeps the legacy
            # epic-wide semantics (closes all). A scoped override closes every
            # claim that does NOT survive its scope test -- the same test as
            # `_filter_by_claim_scope`: a claim is epic-wide (intersects any
            # override scope, hence closed) if it carries no `paths:` clause
            # OR every declared glob fails to match any tracked file (the
            # `empty_scope` witness attached by `_run_check`, #10958). A
            # scoped claim with at least one live glob stays scoped and is
            # closed iff its live paths intersect the override's. The symmetry
            # with `_filter_by_claim_scope` is deliberate: disjointness must
            # require BOTH sides to declare a LIVE scope, at the reducer just
            # as at the filter. (#11098 -- the reducer previously ignored
            # `empty_scope` entirely, leaving a clause-but-dead claim
            # uncloseable by any scoped override; the only escape was an
            # epic-wide override, which swept legitimate scoped claims of
            # sibling lanes along with the broken one.)
            # Later events (open/close) still apply on top in walk order.
            scope = ev.get("paths")
            if not scope:
                state = {ev.lane: ev}
            else:
                state = {
                    ln: e for ln, e in state.items()
                    if ln == ev.lane
                    or (
                        # scoped claim with at least one live glob AND
                        # disjoint from the override's scope -> keep.
                        # _scopes_intersect (not _path_matches_any): the
                        # operand order of the old read was inverted when the
                        # override's scope carried a joker, so a concrete
                        # claim it covered was never closed (#12656).
                        e.get("paths") is not None
                        and not _claim_scope_effectively_epic_wide(e)
                        and not _scopes_intersect(scope, e.get("paths") or [])
                    )
                }
                state[ev.lane] = ev
        elif ev.is_open:
            state[ev.lane] = ev
        elif ev.is_delivered:
            # #12386 -- v2 conditional gate. `is_delivered` already separated
            # `[DELIVERED]` from `[RELEASED]` (close markers in v1); v2 keeps
            # the close behaviour for two of the three branches (CLOSED /
            # lookup-failed) and re-marks the event as `open` for OPEN / MERGED.
            # `locked: True` on the MERGED branch is the cross-check the
            # #10223 `[OVERRIDE]` machinery can read to refuse a plain
            # re-claim (the override branch in `_run_check` honours it).
            v2_action = _resolve_delivered_v2(ev, pr_states)
            if v2_action == "open":
                state[ev.lane] = ev
            elif v2_action == "open_locked":
                ev["locked"] = True
                state[ev.lane] = ev
            else:  # "close" -- legacy v1 behaviour preserved on this branch
                state.pop(ev.lane, None)
        else:
            state.pop(ev.lane, None)
    return state, unattributed


# --- gh plumbing -------------------------------------------------------------

def _gh_issue_comments(issue: str) -> dict:
    """Fetch issue metadata + comments as JSON via `gh`. Raises on failure."""
    proc = subprocess.run(
        [
            "gh", "issue", "view", str(issue),
            # #12156 -- `labels` added so the umbrella classifier
            # (`_is_umbrella_issue`) can read the canonical `EPIC` label the
            # picker hydrates from. The label-route is the authoritative one;
            # the title-route stays a fallback for the historic pre-label
            # inventory.
            "--json", "number,title,labels,comments",
        ],
        # #12811 -- gh emits UTF-8; text=True alone decodes with the Windows
        # locale (cp1252), which raises UnicodeDecodeError on issue bodies
        # carrying bytes at cp1252-undefined positions (0x81/0x8D/0x8F/0x90/
        # 0x9D -- common in the UTF-8 of ICT symbols) and kills the guard.
        capture_output=True, text=True, shell=False,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh issue view {issue} failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )
    return json.loads(proc.stdout)


def _sort_events(payload: dict) -> list[ClaimEvent]:
    """Parse + chronologically sort claim events from a `gh issue view` payload.

    Uses `_parse_claim_events` -- one event per marker line (#10881) -- so a
    comment carrying markers for several lanes reduces correctly instead of
    collapsing to a single (mis-attributed) event. Events from the same comment
    share the server `createdAt`; the stable sort preserves their in-comment
    marker order, so the walk-order reducer sees `[CLAIMED] X\n[DONE] X` as
    open-then-close (final state inactive), exactly as before.
    """
    events = [
        ev
        for c in payload.get("comments", [])
        for ev in _parse_claim_events(c)
    ]
    # Server createdAt, ISO 8601 UTC -> lexicographic order == chronological.
    events.sort(key=lambda e: e.created_at or "")
    return events


# #12386 -- PR-state lookup for the `[DELIVERED]` v2 conditional reducer.
#
# A `[DELIVERED] lane X -- PR #N` carries a PR reference, and the v2 conditional
# gate binds the marker's effective action to the LIVE PR state:
#
#   - PR OPEN       -> DELIVERED is re-marked as `action: open` (the substance
#                      is in flight; the lane stays blocked). A second lane
#                      arriving at this issue MUST NOT re-claim -- this closes
#                      the 10 h 24 window measured on #12213 where the deliverer
#                      released the lock and another lane re-shipped the same work.
#   - PR MERGED      -> DELIVERED is re-marked as `action: open` AND the event
#                      carries `locked: True`. Re-claiming demands a written
#                      `[OVERRIDE]` from a coordinator; the substance has been
#                      accepted by main and the issue is considered resolved.
#   - PR CLOSED (not merged) -> legacy v1 behaviour: DELIVERED pops the lane.
#                      The attempt failed, the lane is free.
#
# The reducer was deliberately built without side effects (#12320 in the v1
# docstring: "the fetch itself (state of PR N) is left to consumers: the
# reducer stays pure"). v2 walks that line by passing an injected `pr_states`
# map (testability + opt-out) -- the default path reads from `gh` lazily, only
# for `[DELIVERED]` events that carry a `pr_ref`. Callers that already know the
# state (replay of an audit log, an offline test) can pass the map directly.
#
# Failures are surfaced as `pr_state: None` (the reducer falls back to legacy
# v1 close-on-DELIVERED). The previous v1 semantics are PRESERVED on a fetch
# failure -- an unreachable `gh` MUST NOT cause a `[DELIVERED]` to suddenly
# start blocking. The failure is visible in `delivered_claims_failed` so an
# operator can see which lookups were silently degraded.
#
# #13336 -- that fail-open is now scoped to TRANSIENT failures only. A gh
# schema break (`Unknown JSON field`) is PERMANENT: while it lasts, every
# lookup returns None and the v2 gate degenerates to v1 wholesale -- the
# exact silence that let #13216 be written twice (both lanes passed their
# guard, the signal was `null`). A permanent failure keeps the claim
# BLOCKING (fail-CLOSED, the organ's default posture); a network/auth
# hiccup keeps the documented fail-open.
_PR_STATE_CACHE: dict[int, tuple[str | None, str | None]] = {}
# value shape: (pr_state, error_message) where pr_state in
# {"OPEN","MERGED","CLOSED",None} and error_message is None on success.

# #13336 -- environmental failures (network, auth, gh binary absent) are
# transient: retryable, orthogonal to the claim protocol, and the documented
# fail-open applies. Everything else (schema break, non-JSON, unexpected
# payload, PR not found) is permanent for the lifetime of the process.
_TRANSIENT_ERROR_MARKERS = (
    "timed out", "timeout", "could not resolve host", "connection",
    "dial tcp", "temporary failure", "network", "rate limit",
    "http 429", "http 5", "502", "503", "504",
    "gh auth", "not logged in", "authentication required",
    "gh exec failed",
)


def _is_transient_error(err: str | None) -> bool:
    """#13336 -- True when a `_fetch_pr_state` error is environmental."""
    if not err:
        return False
    e = err.lower()
    return any(m in e for m in _TRANSIENT_ERROR_MARKERS)


def _fetch_pr_state(pr_ref: int) -> tuple[str | None, str | None]:
    """Return (pr_state, error) for a PR number, with a per-process cache.

    `pr_state` is one of:
      - "OPEN"    : the PR is still mergeable / not yet closed or merged
      - "CLOSED"  : closed WITHOUT being merged
      - "MERGED"  : closed AND merged (the substance reached main)
      - None      : the lookup failed (no network, gh error, PR not found)

    `error` is a short string on failure, None on success. The cache prevents
    repeated `gh pr view` calls when a single check visit processes several
    DELIVERED events on the same PR (rare but seen on audit issues with
    multiple deliveries from different lanes).

    The function is NOT called from the parser: parse_claim_event stays pure,
    per the #12320 contract. The reducer (`compute_active_claims`) is the only
    caller, and only for events that already have `pr_ref != None`.
    """
    if pr_ref in _PR_STATE_CACHE:
        return _PR_STATE_CACHE[pr_ref]
    try:
        proc = subprocess.run(
            [
                "gh", "pr", "view", str(pr_ref),
                "--json", "state,mergedAt",
            ],
            capture_output=True, text=True, shell=False,
            encoding="utf-8", errors="replace",  # #12811
        )
    except Exception as exc:  # pragma: no cover -- defensive
        result = (None, f"gh exec failed: {exc}")
        _PR_STATE_CACHE[pr_ref] = result
        return result
    if proc.returncode != 0:
        result = (None, f"gh pr view {pr_ref} exit {proc.returncode}: {proc.stderr.strip()[:200]}")
        _PR_STATE_CACHE[pr_ref] = result
        return result
    try:
        d = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        result = (None, f"gh pr view {pr_ref} non-JSON: {exc}")
        _PR_STATE_CACHE[pr_ref] = result
        return result
    # GH field model (#13336): `state` in {OPEN, CLOSED, MERGED}, `mergedAt`
    # is an ISO timestamp (null until merged). The bool field `merged` was
    # REMOVED from `gh pr view --json` (gh 2.83+): querying it exits 1 on the
    # WHOLE request, which made every lookup fail and silently reverted the
    # reducer to v1 (every [DELIVERED] released its claim, #13216 duplicated).
    # When `state == "MERGED"`, the reducer treats the substance as locked --
    # the PR reached main. A non-null `mergedAt` alone also locks, defence in
    # depth against a raced `state`.
    if d.get("mergedAt") is not None or d.get("state") == "MERGED":
        result = ("MERGED", None)
    elif d.get("state") == "CLOSED":
        result = ("CLOSED", None)
    elif d.get("state") == "OPEN":
        result = ("OPEN", None)
    else:
        result = (None, f"unexpected gh state payload: {d!r}")
    _PR_STATE_CACHE[pr_ref] = result
    return result


def _resolve_delivered_v2(
    ev: ClaimEvent,
    pr_states: dict[int, str] | None,
) -> str:
    """Compute the effective action for a `[DELIVERED]` event under the v2 semantics.

    Returns one of:
      - "open"          : the PR is OPEN; the substance is in flight; the lane
                          MUST stay blocked. Equivalent to re-marking the event
                          as a `[CLAIMED]`.
      - "open_locked"   : the PR is MERGED; the substance has been accepted;
                          the lane MUST stay blocked AND cannot be re-claimed
                          without a coordinator `[OVERRIDE]`.
      - "close"         : the PR is CLOSED without merge, OR the PR state could
                          not be resolved, OR the event carries no `pr_ref`.
                          Equivalent to legacy v1 behaviour (lane pops from state).

    Side effect (#12386, JSON summary): when a `pr_ref` is present, the resolved
    state is attached to the event as `ev["pr_state"]` so the JSON summary can
    surface it to consumers (the `delivered_claims_pr_states` map and the
    per-active-claim `pr_state` field both read this attribute). On a
    `pr_ref is None` event, no `pr_state` is attached -- the legacy v1 path
    is unchanged for unreferenced deliveries.

    `pr_states` is an optional injection map (testable): if supplied, the
    reducer does NOT call `gh`. If absent or the pr_ref is unknown to the map,
    the reducer calls `gh pr view` via `_fetch_pr_state`. The map and the live
    fetch are mutually exclusive -- a test that provides the map can run
    offline, an end-to-end test can omit it.
    """
    pr_ref = ev.get("pr_ref")
    if pr_ref is None:
        return "close"  # legacy: a DELIVERED without a PR ref is a close
    if pr_states is not None:
        st = pr_states.get(pr_ref)
        err = None
    else:
        st, err = _fetch_pr_state(pr_ref)
    # Attach the resolved state to the event for the JSON summary. On a None
    # state (lookup failed) we still attach None so the consumer sees that we
    # TRIED -- the absence of the key would otherwise be indistinguishable from
    # a non-DELIVERED event.
    ev["pr_state"] = st
    if st == "OPEN":
        return "open"
    if st == "MERGED":
        return "open_locked"
    if (st is None and pr_states is None
            and err is not None and not _is_transient_error(err)):
        # #13336 -- PERMANENT lookup failure (gh schema break, non-JSON
        # payload, PR not found): fail-CLOSED. Releasing the claim here is
        # what silently reverted v2 to v1 while the `merged` field was dead
        # (#13216: the same 49 lines written twice, both guards CLEAR).
        # The lane keeps its lock until a human or a working gh resolves it.
        ev["pr_state_error"] = err
        return "open"
    return "close"


def _post_comment(issue: str, body: str) -> None:
    """Post an issue comment via `gh issue comment --body-file`.

    A body file (not --body) avoids shell-escaping the marker / em-dash / quotes
    and keeps the posted text byte-exact. Written under the OS temp dir, not the
    worktree, so it never leaks into a commit (cf L677-L4 body-file discipline).
    """
    with tempfile.NamedTemporaryFile(
        "w", suffix=".md", delete=False, encoding="utf-8"
    ) as fh:
        fh.write(body)
        path = fh.name
    proc = subprocess.run(
        ["gh", "issue", "comment", str(issue), "--body-file", path],
        capture_output=True, text=True, shell=False,
        encoding="utf-8", errors="replace",  # #12811
    )
    Path(path).unlink(missing_ok=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh issue comment {issue} failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )


def _gh_open_prs_with_files() -> list[dict]:
    """Fetch all open PRs (number, title, headRefName, body, files) via `gh`.

    Used by `--paths` mode to intersect PR file lists with caller-provided
    patterns. Returns a list of dicts; each PR dict is {number, title,
    headRefName, body, files: [{path, ...}, ...], lane: str|None}. The `lane`
    key is filled by the caller -- `_run_check_paths` -- via the shared
    `extract_lane` reader, NOT here, so the lane-detection rule lives in
    exactly one place (#9485 single-reader discipline).

    Raises RuntimeError on `gh` failure so callers surface exit 2.
    """
    proc = subprocess.run(
        [
            "gh", "pr", "list", "--state", "open",
            "--json", "number,title,headRefName,body,files",
            "--limit", "200",
        ],
        # #12811 -- 200 PR bodies in one payload: a single non-cp1252 byte
        # anywhere kills the whole --paths mode on Windows.
        capture_output=True, text=True, shell=False,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh pr list --state open failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            f"gh pr list returned non-JSON (exit {proc.returncode}): {exc}"
        )


# #12386 v2 -- `_find_open_pr_for_issue_by_lane` returns the unique OPEN PR
# in `lane` whose body references `issue_number` (case insensitive
# `Closes #N` / `Fixes #N` / `Refs #N` / `See #N` / plain `#N`), OR `None`
# when no match (caller falls back to plain `[RELEASED]`).
#
# Why the helper is here and not in `main`: callers (`--release` smart
# branch) want ONE function that returns "the PR to bind", and we want
# the predicate (open + same-lane + references-the-issue) to live in
# exactly one place. The legacy `_gh_open_prs_with_files()` is reused
# because we already paginate 200 OPEN PRs (enough for typical work) and
# we already consume its body field elsewhere.
#
# Test injection: callers may pre-fetch the PRs once and pass `prs` to
# avoid double `gh pr list` round-trips in tests; otherwise we fetch
# here. The lane-tag reading uses the SHARED `extract_lane` helper --
# never a private regex -- so the rule stays single-sourced (#9485).
def _find_open_pr_for_issue_by_lane(
    issue_number: int,
    lane: str,
    prs: list[dict] | None = None,
) -> int | None:
    """Return the unique OPEN PR number in `lane` referencing `issue_number`.

    The matcher accepts any of: `Closes #N` / `Fixes #N` / `Refs #N` / `See
    #N` / `Resolves #N` / a bare `#N` token in the PR body. The
    `Refs #N` / `See #N` forms are the dispatch style (#10555) where a PR
    only partially closes an epic. The bare `#N` form covers PRs that
    mention the issue informally -- we keep it lenient because the
    `[DELIVERED]` marker is itself the binding attestation; the PR-body
    match just surfaces WHICH PR to record.
    """
    if prs is None:
        prs = _gh_open_prs_with_files()
    pat = re.compile(
        r"(?i)\b(?:closes|fixes|refs|see|resolves|part\s+of|part-of)\s*"
        + r"#(\d+)\b|\B#(\d+)\b"
    )
    matches: list[int] = []
    for pr in prs:
        body = (pr.get("body") or "")
        # Per #9485 single-reader: use the SAME `extract_lane` the rest
        # of the file uses. `extract_lane(body)` returns the first lane
        # token it finds, accepting both `lane myia-po-2023:CoursIA-2`
        # and `<!-- lane: ... -->` forms.
        pr_lane = extract_lane(body)
        if pr_lane != lane:
            continue
        for m in pat.finditer(body):
            captured = m.group(1) or m.group(2)
            if captured is None:
                continue
            try:
                if int(captured) == issue_number:
                    matches.append(int(pr["number"]))
                    break
            except (KeyError, ValueError, TypeError):
                continue
    if len(matches) == 0:
        return None
    if len(matches) > 1:
        # Multiple OPEN PRs in the same lane reference the issue -- the
        # caller has been racing themselves. We pick the lowest number
        # (deterministic, oldest PR wins) and emit a stderr warning so
        # the dashboard [DONE] can flag the ambiguity. We do NOT post
        # DELIVERED silently here: a misleading PR reference would
        # LOCK the wrong PR. Callers should fall back to plain
        # `[RELEASED]` in this case.
        print(
            f"WARN: {len(matches)} OPEN PRs in lane {lane} reference "
            f"#{issue_number}; refusing to pick one to bind to "
            f"[DELIVERED]. Use --release with --note 'delivered:#N' to "
            f"force a specific PR, or close/merge the others first.",
            file=sys.stderr,
        )
        return None
    return matches[0]


def _path_matches(path: str, patterns: list[str]) -> bool:
    """Return True if `path` matches any of the caller-provided patterns.

    Each pattern is a glob (fnmatch.fnmatch case-sensitive, `*` / `?` /
    `[abc]`); plain substrings without glob meta are also matched (covers
    the common dispatch form `path/to/file.py`). Symmetric with how GitHub
    UI's PR-files search treats "filter" input -- a worker who filters the
    web UI by filename and pastes the result here gets the same matches.

    Brace groups (`{a,b}`) are expanded first, so `--paths
    'sel/{6,8}-*.yaml'` behaves like the fs-shell glob a worker means
    (#10597) instead of silently matching nothing.

    The fnmatch patterns are anchored to the basename of the path AND to
    the full path, so a pattern like `*.lean` matches `knot_lean/Foo.lean`
    AND `Foo.lean` alone. This is the same convenience offered by the
    existing `grep`/git commands used in the cluster for "where does this
    file live" queries.
    """
    from fnmatch import fnmatch
    basename = path.rsplit("/", 1)[-1]
    for pat in patterns:
        for p in _expand_brace_groups(pat):
            if fnmatch(path, p) or fnmatch(basename, p):
                return True
    return False


def _compute_scope_intersection_paths(
    my_scope: list[str] | None,
    claim_scope: list[str] | None,
    tracked: list[str] | None,
    limit: int = 25,
) -> tuple[list[str], bool]:
    """Return paths matching BOTH the query scope and the claim's scope.

    #14187 -- a `blocked: true` on a wide `--paths` glob is BINARY today: the
    caller learns WHO blocks but not WHICH files are contested. The lane
    that owns the contested files is the one that wants to act; the others
    are free to write freely (their work does not intersect). Materialising
    the intersection per blocker lets the caller re-scope to lift the block
    without a dashboard round-trip.

    `my_scope` is the caller's `--paths` glob list (None = epic-wide =
    intersects all claim scopes). `claim_scope` is the active claim's
    declared `paths:` (None = epic-wide). `tracked` is the repo's
    git-ls-files output (None = no walk available; intersection becomes
    empty, fail-closed the same way `_filter_by_claim_scope` does on a
    missing tree).

    Returns `(paths, is_complete)`: the list of tracked files matching
    BOTH sides, and a boolean saying whether the list was TRUNCATED at
    `limit` (caller should warn on stderr so a lane knows it sees a
    sample, not the full intersection). Empty list means either side is
    empty in practice (no tracked files matched both) OR `tracked is
    None` (no walk possible). Epic-wide on either side = full
    intersection of the OTHER side against `tracked`.
    """
    if tracked is None:
        return [], False
    if not my_scope or not claim_scope:
        # Epic-wide on either side -> no scope intersection to enumerate.
        # The claim (or the caller) is wildcards-free, so the BLOCKED
        # verdict stays binary from the file-list perspective.
        return [], False
    matches: list[str] = []
    for path in tracked:
        if _path_matches(path, my_scope) and _path_matches(path, claim_scope):
            matches.append(path)
            if len(matches) > limit:
                return matches[:-1], True
    return matches, False


def _compute_free_paths(
    my_scope: list[str] | None,
    blocking_claims: dict[str, ClaimEvent],
    tracked: list[str] | None,
    limit: int = 25,
) -> tuple[list[str], bool]:
    """Return paths in `my_scope` that intersect NO active blocker claim.

    #14187 -- the dual of `_compute_scope_intersection_paths`: a lane that
    sees 3 blockers across 12 files in the scope needs to know which 9 are
    free, not just which 3 are locked. The list is the FILES THAT THE LANE
    CAN EDIT WITHOUT WAITING for any blocker to release or re-scope.

    `blocking_claims` is the post-filter `others` dict (already scoped to
    the caller's `my_scope` by `_filter_by_claim_scope`). Each claim's
    scope is checked; a path is "free" iff no claim's `_path_matches`
    says yes. Epic-wide claims (no `paths:`) make the entire `my_scope`
    non-free, so the function returns `([], False)` when any blocker is
    epic-wide -- the human verdict "all files blocked" is then exact, not
    a sample.
    """
    if tracked is None:
        return [], False
    if not my_scope:
        return [], False
    claim_scopes = [ev.get("paths") for ev in blocking_claims.values()]
    if any(scopes is None for scopes in claim_scopes):
        # Epic-wide blocker locks the whole `my_scope`.
        return [], False
    scoped_claims = [scopes for scopes in claim_scopes if scopes]
    # Empty blocker set after scope-filter -> the entire `my_scope` is
    # free. Walk the tracked files (constrained by `my_scope`) and
    # collect the matches. This is the disjoint case the lane-claim
    # guard relies on: rc=0 (clear), free_paths = the whole caller scope.
    if not scoped_claims:
        free: list[str] = []
        for path in tracked:
            if not _path_matches(path, my_scope):
                continue
            free.append(path)
            if len(free) > limit:
                return free[:-1], True
        return free, False
    free: list[str] = []
    for path in tracked:
        if not _path_matches(path, my_scope):
            continue
        if any(_path_matches(path, scopes) for scopes in scoped_claims):
            continue
        free.append(path)
        if len(free) > limit:
            return free[:-1], True
    return free, False


# --- formatted output --------------------------------------------------------

_CLAIM_BODY_TMPL = (
    "[CLAIMED] lane {lane} -- {intention}{paths_clause}\n\n"
    "(check_lane_claim #9774 -- server-stamped UTC; body timestamps are NOT "
    "authoritative. Release with `[RELEASED]` when your PR lands.)\n"
)
_RELEASE_BODY_TMPL = (
    "[RELEASED] lane {lane} -- {note}{paths_clause}\n"
)
# #12386 v2 -- `[DELIVERED]` carries an explicit PR reference. The `locked:
# True` reducer branch on `_fetch_pr_state(pr_ref) == "MERGED"` is the
# v2 gate; a plain `[RELEASED]` would only free the active_claims slot,
# losing the merged-link that powers the LOCKED verdict above. The
# `--release` flow in `main` chooses DELIVERED when (a) the caller has
# exactly one OPEN PR in their lane referencing the issue (body or
# refs/closes), and (b) the PR number parses; otherwise it falls back to
# RELEASED for backwards compat (caller can be releasing without an OPEN
# PR -- the "released" plain form still applies).
_DELIVERED_BODY_TMPL = (
    "[DELIVERED] lane {lane} -- PR #{pr_ref}{paths_clause}\n\n"
    "(#12386 v2: PR state-bound. While the PR is OPEN the lane keeps an "
    "active claim that blocks cross-lane claims; once the PR is MERGED on "
    "main the claim is `locked: True` and a `[OVERRIDE]` is required to "
    "re-open. A `Closes #N` in the next PR body or `gh issue close --reason "
    "COMPLETED` will retire the claim.)\n"
)


def _paths_clause(paths: list[str] | None) -> str:
    """Render a `paths:` scope clause for a claim/release marker (#11064).

    The reader (`_PATHS_CLAUSE_RE`) parses the clause at END OF LINE
    (`paths\\s*:\\s*([^\\n]+?)\\s*$`), so the clause is always the LAST element
    of the marker line. Empty when `paths` is None -- the marker stays
    epic-wide (legacy semantics, preserved). `--paths` provided on a posting
    path was previously DROPPED SILENTLY: the caller believed the claim was
    scoped while the organ read it epic-wide (maximally blocking). This
    function is the fix that makes the scope survive the round-trip.
    """
    if not paths:
        return ""
    return " -- paths: " + ", ".join(paths)


def _fmt_utc(iso: str | None) -> str:
    return (iso or "?").replace("T", " ").replace("Z", " UTC")


def _scope_zero_coverage_warning(
    scope: list[str] | None,
    repo_root: str | None = None,
) -> dict | None:
    """Return a warning dict if `scope` matches zero tracked files. None otherwise.

    #10597 bonus -- a lane declaring a scope that matches nothing is
    INDISTINGUISHABLE from a legitimately-empty scope (both read "the
    globs do not cover any file"). Without a positive control the lane
    never learns its lock is empty until the next round of arbitration.
    Walk the tracked files under `repo_root` (default: cwd) and return
    a structured warning when none match. Non-blocking by design: the
    gate is the structured claim, this is a usability hint.

    The walk is best-effort: when not in a git repo, or when the walk
    fails for any reason, return None. The warning is a polite nudge,
    not a structural guarantee.
    """
    if not scope:
        return None  # unscoped -> nothing to warn about
    if repo_root is None:
        repo_root = os.getcwd()
    try:
        proc = subprocess.run(
            ["git", "-C", repo_root, "ls-files"],
            capture_output=True, text=True, timeout=10,
            encoding="utf-8", errors="replace",  # #12811
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    tracked = [ln for ln in proc.stdout.splitlines() if ln]
    if not tracked:
        return None
    # Apply fnmatch (with brace expansion) per file. The first hit
    # short-circuits -- we only need to know "at least one file matches".
    for path in tracked:
        if _path_matches(path, scope):
            return None
    return {"scope": scope, "tracked_count": len(tracked)}


# --- #10881 lint: malformed paths: clauses -----------------------------------
# 2026-08-14 morning on #10678: four markers, all misread SILENTLY, two lanes
# blocked 1.5h. The lint fires on stderr when a marker is READ -- visible to
# any lane running the check, NEVER changing a verdict. Three checks:
#   1. marker without a `paths:` clause -> INFO naming the epic-wide effect
#      (the information that was missing in all four cases).
#   2. implausible glob (em-dash, colon-space, escaped comma, >120 chars) ->
#      WARN "glob suspect (prose avalée ?)" -- the prose-after-clause trap.
#   3. glob matching zero tracked files -> WARN "glob sans correspondance".
#      A dead glob is almost always a typo or prose. Best-effort: when the
#      git walk fails (not a repo), the no-match check silently skips.
# Selectivity is the acceptance's core ("la moitié qui compte"): a well-formed
# marker (`paths: a/b.lean, a/c.lean`, two existing files) produces NOTHING.

_IMPLAUSIBLE_SUBSTRINGS = ("—", "–", "\\,")


def _glob_implausible(glob: str) -> bool:
    """True when a `paths:` entry cannot plausibly be a repo path (prose)."""
    if len(glob) > 120:
        return True
    if any(s in glob for s in _IMPLAUSIBLE_SUBSTRINGS):
        return True
    if re.search(r":\s", glob):  # colon followed by whitespace = prose
        return True
    return False


def _git_tracked_files(repo_root: str | None = None) -> list[str] | None:
    """Best-effort `git ls-files` under repo_root (cwd default). None on failure.

    Mirrors the walk of `_scope_zero_coverage_warning` -- the one source of
    "which files does the repo track" for both callers.
    """
    if repo_root is None:
        repo_root = os.getcwd()
    try:
        proc = subprocess.run(
            ["git", "-C", repo_root, "ls-files"],
            capture_output=True, text=True, timeout=10,
            encoding="utf-8", errors="replace",  # #12811
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    tracked = [ln for ln in proc.stdout.splitlines() if ln]
    return tracked or None


def _glob_matches_tracked(glob: str, tracked: list[str]) -> bool:
    """True when at least one tracked file matches the glob (fnmatch, basename-or-full)."""
    for path in tracked:
        if _path_matches(path, [glob]):
            return True
    return False


# #13129 -- proximity suggestion for dead globs. When a declared glob matches
# ZERO tracked files AND the glob's basename exists UNIQUE elsewhere in the
# tracked tree, suggest the real path so the writer can fix the typo at the
# call site. The threshold prevents the false-positive on README.md /
# MANIFEST.md / __init__.py (basenames that legitimately appear hundreds of
# times). Returns None when the suggestion would be ambiguous or noise-prone.
_PROXIMITY_BASENAME_LIMIT = 5  # > N occurrences => basename is too generic.


def _suggest_path_correction(glob: str, tracked: list[str]) -> str | None:
    """Best-effort 'did you mean ... ?' suggestion for a dead glob (#13129).

    The glob's BASENAME must appear EXACTLY once in the tracked tree for a
    suggestion to be returned. Multiple matches = ambiguous (the writer must
    pick by intent, not by basename). Zero matches = no candidate (a brand
    new file -- the legitimate future case the warn was never meant to
    block, see #12740).

    The threshold (_PROXIMITY_BASENAME_LIMIT = 5) caps the suggestion at
    basenames that survive as legitimate identifiers: README.md, MANIFEST.md
    and __init__.py each have hundreds of occurrences across the repo and
    would mislead more often than they would help. A basename that appears
    between 1 and 5 times IS likely a typo (the writer meant one specific
    file and the regex did not pick the right one).
    """
    if not glob or "/" not in glob:
        return None
    basename = glob.rsplit("/", 1)[-1]
    if not basename or basename.startswith(".") and len(basename) <= 2:
        return None
    matches = [t for t in tracked if t.endswith("/" + basename)]
    if not matches or len(matches) > _PROXIMITY_BASENAME_LIMIT:
        return None
    if len(matches) == 1:
        return matches[0]
    # 2..5 matches: pick the one sharing the LONGEST prefix with the dead glob
    # (directory proximity beats basename uniqueness). Return it only when the
    # picked candidate is strictly closer than the runner-up.
    matches.sort(key=lambda t: -len(_common_prefix(glob, t)))
    best, second = matches[0], matches[1] if len(matches) > 1 else ""
    if _common_prefix(best, glob) > _common_prefix(second, glob):
        return best
    return None


def _common_prefix(a: str, b: str) -> str:
    n = 0
    for x, y in zip(a, b):
        if x != y:
            break
        n += 1
    return a[:n]


# #13129 motif B -- detect missing-comma in a glob. The mistake pattern is
# `paths: a.py b.py` where the writer forgot the comma; the parser treats
# the whole thing as ONE glob that matches nothing. We flag when a glob
# contains a SPACE and at least two SPACE-separated tokens each LOOK like a
# path (contain a `/` OR end with a tracked-file extension).
#
# #13486: SINGLE machinerie. The canonical implementation lives in
# `scripts/ci/emit_dead_scope_warnings.py` (the CI helper that emits
# `::notice::` annotations and the `dead_scope_suggestions` JSON line).
# This module DELEGATES -- the regex + heuristic are imported from there.
# Do not re-implement them here; if you need to change motif B detection,
# change the helper and re-export.
_PATHLIKE_TOKEN_RE = None  # back-compat alias (lazy-resolved on first call)


def _looks_like_missing_comma(glob: str) -> list[str] | None:
    """Delegate to the SINGLE motif-B machinerie (#13486).

    The canonical implementation lives in `emit_dead_scope_warnings.py`
    (`_missing_comma_tokens`). We import it lazily so `import check_lane_claim`
    does not require the helper to be on sys.path (the helper sits in
    `scripts/ci/`, imported only by the CI advisory job).
    """
    try:
        from scripts.ci.emit_dead_scope_warnings import _missing_comma_tokens  # type: ignore  # noqa: E501
    except Exception:
        try:
            # Fallback path when this module is invoked as `python -m scripts.check_lane_claim`
            from scripts.ci.emit_dead_scope_warnings import _missing_comma_tokens  # type: ignore  # noqa: E501,F811
        except Exception:
            return None
    return _missing_comma_tokens(glob)


_INFERRED_PATH_PATTERNS = (
    # French/English label keywords fleet uses to advertise intent in prose.
    # The patterns match the LABEL token followed by a colon and the path; the
    # path is captured (group 1) and stripped of trailing punctuation. The
    # regex is anchored at the start of the comment (`(?im)`) so a `Path:`
    # mentioned MID-sentence (the "discussion" form, not the "announcement"
    # form) does not feed the inference. The first hit wins -- the comment is
    # expected to name ONE path per label, the same way `--paths` takes one
    # file per argument. (#11755 acceptance #2.)
    re.compile(r"(?im)^\s*Path\s*:\s*([^\n]+?)\s*$"),
    re.compile(r"(?im)^\s*Paths\s*:\s*([^\n]+?)\s*$"),
    re.compile(r"(?im)^\s*Fichier\s*:\s*([^\n]+?)\s*$"),
    re.compile(r"(?im)^\s*Notebook\s*:\s*([^\n]+?)\s*$"),
    # Inline label form: `[CLAIMED] lane <...> — Path: GenAI/foo.ipynb`. The
    # marker line itself is allowed to carry the announcement -- the body of
    # the marker line is what feeds the reducer, so it is also where the
    # announcement lives in the #11112 corpus. The regex is line-anchored but
    # accepts any text before the label, so the marker decoration (`- **[`,
    # `> [`, `## [`) does not void the match.
    re.compile(r"(?im)^\s*.*?Path\s*:\s*([^\n]+?)\s*$"),
)


def _infer_paths_from_body(body: str | None) -> list[str]:
    """Best-effort extraction of a `paths:` clause from prose (#11755 Piste 2).

    A lane that writes `Path : MyIA.AI.Notebooks/...ipynb` in the BODY of its
    comment has the right intent but the wrong syntax: the organ reads the
    `paths:` MACHINE clause only, sees None, and promotes the claim to
    epic-wide silently. We mine the body for a plausible path and surface it
    on stderr as a SUGGESTION, never as a verdict: the lane keeps its
    epic-wide semantics and must reissue the claim with the explicit `paths:`
    clause to bind it. The mine is a hint, not a guess -- guessing a scope
    would be the mirror image of the current defect.

    Returns the list of unique inferred paths (empty list when none of the
    labels appear). Order is the body order so the first hit is the first
    advertised intent (the natural reading order).
    """
    if not body:
        return []
    seen: set[str] = set()
    out: list[str] = []
    for pat in _INFERRED_PATH_PATTERNS:
        for m in pat.finditer(body):
            raw = m.group(1).strip().rstrip(".,;:")
            if not raw or raw in seen:
                continue
            seen.add(raw)
            out.append(raw)
    return out


def _lint_claim_events(
    events: list[ClaimEvent],
    issue_number: int | None,
    repo_root: str | None = None,
    tracked: list[str] | None = None,
    active_claims: dict[str, ClaimEvent] | None = None,
    others_verdict: dict[str, ClaimEvent] | None = None,
    my_lane: str | None = None,
) -> None:
    """Emit WARN/INFO lines for malformed claim markers (#10881). Non-blocking.

    Runs on OPEN and OVERRIDE markers only: a close marker is always a full
    lane-close (its scope is informational, #10419), so an epic-wide release
    is semantically identical to a scoped one -- nothing to warn about. The
    lint only prints to stderr; verdicts are untouched. `tracked` lets a
    caller that already walked the repo (#10958 empty-scope witness) reuse
    the list instead of paying the walk twice.

    #11755: when an OPEN marker has no `paths:` clause AND its body advertises
    a plausible path via `Path:` / `Paths:` / `Fichier:` / `Notebook:`, the
    WARN echoes the inferred path AND the expected shape. The marker is NOT
    re-classified (legacy semantics preserved -- see #11755 Piste 1 rationale).
    The lane keeps its epic-wide read; the warning is a usability nudge to
    reissue with the explicit clause.

    #12072: distinct from the #11755 nudge, when the event carries the
    structured `scope_declared_off_marker` signal (a line-start `paths?`
    clause on a SEPARATE line of the comment), an explicit WARN names the
    faulty line and the expected marker-line syntax. Fires only on the
    signal -- an intentional epic-wide declaration (no off-marker clause)
    stays silent, so the lint never penalises a deliberate full-lane lock.

    #12327 (verdict qualifier): when `active_claims` and `others_verdict` are
    provided (caller has already reduced), each epic-wide marker is qualified
    by its EFFECTIVE state at the time of the verdict:
    - **superseded** by a later claim of the same lane (the marker exists as
      legacy noise, the active claim supersedes it -- print as hygiene debt,
      not as a blocker);
    - **hors scope declare** when the lane's claim does NOT intersect the
      verdict's `others` set (the claim was epic-wide in form but did not
      actually block the caller -- print as informational, never as `il bloque`);
    - **il bloque** ONLY when the lane IS in `others_verdict` (the claim is
      what the reducer actually kept against the caller).
    Without these args, the lint falls back to the legacy behaviour (every
    epic-wide marker prints `il bloque`), which is the bug #12327 names.
    """
    if tracked is None:
        tracked = _git_tracked_files(repo_root)
    # #11755: build a comment-body lookup keyed by the comment url so the lint
    # can mine the body of the marker line for an inferred `Path:` clause and
    # echo it on stderr next to the WARN. One walk per check is cheap, and the
    # lookup is bounded by the comments list (not the events list, which can
    # share a body across multiple marker lines -- one comment = many events).
    body_by_url: dict[str, str] = {}
    for ev in events:
        url = ev.get("url")
        if url and url not in body_by_url:
            # The event dict carries no body; pull it from the events we
            # already walked (events are built from `comment` dicts that have
            # both body and url -- see `_parse_claim_events`).
            pass  # the real source of bodies is `payload["comments"]` below
    for ev in events:
        if ev.get("action") not in ("open", "override"):
            continue
        if ev.paths is None:
            # #12072 -- the structured off-marker signal. Fires ONLY when the
            # comment declares a scope somewhere other than the marker line
            # (a `Paths:`/`path:`/`Path :` line in a separate paragraph): the
            # reducer could not read it, so the claim reduced to EPIC-WIDE
            # while the writer believed it scoped. Explicit intent stays
            # legitimate (no signal -> no noise); the claim is NOT re-scoped.
            off_marker = ev.scope_declared_off_marker
            if off_marker:
                print(
                    f"WARN: scope declare hors ligne de marqueur -- cette "
                    f"declaration n'est PAS lue (#12072) : "
                    f"{off_marker[0]!r} (lane {ev.lane or '?'}). "
                    f"La clause paths: doit etre SUR la ligne du marqueur : "
                    f"`[CLAIMED] lane <machine:workspace> -- paths: <g1>, <g2>`.",
                    file=sys.stderr,
                )
            inferred = _infer_paths_from_body(ev.get("_body"))
            inferred_str = (
                " ; chemin(s) inféré(s) du body : "
                + ", ".join(inferred)
                if inferred
                else ""
            )
            # #12327 -- qualify the epic-wide lint by the verdict the reducer
            # actually reached. Three buckets (others_verdict may be None when
            # the caller has not yet reduced -- legacy path keeps the old
            # `il bloque` wording for back-compat):
            ev_lane = ev.lane or "?"
            ev_active = active_claims.get(ev_lane) if active_claims else None
            in_others = (others_verdict is not None
                         and ev_lane in others_verdict)
            if (active_claims is not None
                    and ev_active is not None
                    and ev_active is not ev
                    and _event_is_active_for(ev, ev_active)):
                # The marker is shadowed by a later active claim of the SAME
                # lane -- superseded, sans effet. Hygiene debt: the lane should
                # [RELEASED] the old marker, but the organ never blocks on it.
                print(
                    f"INFO: marqueur {ev.marker} epic-wide SUPERSEDED "
                    f"(lane {ev_lane}) -- un claim actif ulterieur de la "
                    f"meme lane tient le verrou (scope: {ev_active.get('paths') or 'epic-wide'}). "
                    f"Sans effet sur le verdict. Hygiene: "
                    f"`[RELEASED]` l'ancien marqueur (cf. #12327).{inferred_str}",
                    file=sys.stderr,
                )
                continue
            if others_verdict is not None and not in_others and ev_lane != my_lane:
                # Epic-wide form, but the lane did NOT survive the reducer's
                # scope filter: either the lane re-posted a scoped claim, or
                # the caller declared `--paths` and the claim does not
                # intersect. The lint must NOT say `il bloque`.
                print(
                    f"INFO: marqueur {ev.marker} epic-wide (lane {ev_lane}) "
                    f"-- SANS effet sur #{issue_number} "
                    f"(claim de la lane filtre par scope ou re-poste depuis). "
                    f"Forme attendue : `[CLAIMED] lane <machine:workspace> "
                    f"-- paths: <g1>, <g2>` (cf. #11755).{inferred_str}",
                    file=sys.stderr,
                )
                continue
            # Legacy wording: the marker IS in `others_verdict` (real blocker)
            # OR the caller has not reduced yet (back-compat). Keep the
            # original `il bloque toutes les autres lanes` text.
            print(
                f"INFO: marqueur {ev.marker} epic-wide (pas de clause paths:) "
                f"-- il bloque toutes les autres lanes sur #{issue_number} "
                f"(lane {ev_lane}).{inferred_str} "
                f"Forme attendue : `[CLAIMED] lane <machine:workspace> "
                f"-- paths: <g1>, <g2>` (cf. #11755).",
                file=sys.stderr,
            )
            continue
        for g in ev.paths:
            if _glob_implausible(g):
                print(
                    f'WARN: glob suspect (prose avalée ?) : "{g}" '
                    f"(lane {ev.lane or '?'})",
                    file=sys.stderr,
                )
            if tracked is not None and not _glob_matches_tracked(g, tracked):
                print(
                    f'WARN: glob sans correspondance : "{g}" '
                    f"(lane {ev.lane or '?'})",
                    file=sys.stderr,
                )
                # #13129 motif B -- missing comma between paths. Fires when
                # the glob contains whitespace AND >=2 tokens each look path-
                # shaped. The classic typo is `paths: a.py b.py` which the
                # parser treats as a single glob that matches nothing.
                pathlike_tokens = _looks_like_missing_comma(g)
                if pathlike_tokens:
                    candidates = ", ".join(repr(t) for t in pathlike_tokens)
                    print(
                        f'WARN: glob ressemble a plusieurs chemins separes '
                        f"par ESPACE au lieu d'une virgule : {candidates}. "
                        f"Le parser n'a vu qu'un seul glob (motif B, #13129).",
                        file=sys.stderr,
                    )
                # #13129 motif A/C -- proximity suggestion. When the basename
                # of the dead glob exists UNIQUE elsewhere in the tree,
                # suggest the real path. Best-effort, non-blocking.
                elif (suggestion := _suggest_path_correction(g, tracked)) is not None:
                    print(
                        f"WARN: glob sans correspondance : \"{g}\" -- "
                        f"did you mean {suggestion!r} ? (basename unique, "
                        f"#13129 motif A/C)",
                        file=sys.stderr,
                    )


def _event_is_active_for(legacy: ClaimEvent, active: ClaimEvent) -> bool:
    """True when `active` is the live claim that supersedes `legacy`.

    Two markers from the SAME lane supersede each other when the active one
    was posted LATER (later `created_at`) OR carries a `paths:` clause (the
    legacy was epic-wide, the active is scoped -- the scoped form is more
    precise and replaces the legacy intent). If the active marker is OLDER
    than the legacy one, this is a sequence anomaly -- the legacy was
    INTENDED to supersede the active, and the active is itself legacy
    noise; in that case the caller wants the SHARED verdict to surface.
    """
    if active is None or active is legacy:
        return False
    # A scoped marker always supersedes an epic-wide one of the same lane.
    if active.get("paths") is not None and legacy.get("paths") is None:
        return True
    # Two markers of the same lane, both epic-wide: the LATER one wins.
    legacy_at = legacy.get("created_at")
    active_at = active.get("created_at")
    if legacy_at and active_at and active_at > legacy_at:
        return True
    return False


def _find_malformed_markers(payload: dict) -> list[dict]:
    """Bare-marker lines that look like claims but will never be read (#11239).

    `_parse_claim_events` keys off `_MARKER_RE`, which REQUIRES the brackets:
    a `CLAIMED #N -- lane ...` line written without them is invisible to the
    organ (`unattributed_markers: 0`, CLEAR to every other lane) yet the
    writer believes their lock is posted. Returns one dict per matching line
    (marker word, capped verbatim line, author, comment url). WARN-only by
    design: never changes a verdict, never touches `blocked` -- the lint
    exists to tell the writer they were not read, not to re-interpret their
    text as a claim.
    """
    found: list[dict] = []
    for c in payload.get("comments", []):
        body = c.get("body") or ""
        author = (c.get("author") or {}).get("login")
        # Meme raison que dans `_parse_claim_events` : une ligne citee dans un
        # bloc fence n'est pas une tentative de claim mal formee, c'est une
        # citation. La signaler enverrait son auteur corriger une prose saine.
        for m in _MALFORMED_MARKER_RE.finditer(_mask_fenced_blocks(body)):
            line = _line_for_match(body, m)
            found.append({
                "marker": m.group(1).upper(),
                "line": line if len(line) <= 160 else line[:160] + "…",
                "author": author,
                "url": c.get("url"),
            })
    return found


def _levenshtein(a: str, b: str) -> int:
    """Plain Levenshtein distance (small strings -- keyword-length inputs)."""
    if a == b:
        return 0
    if not a or not b:
        return len(a) + len(b)
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(
                prev[j] + 1,          # deletion
                cur[j - 1] + 1,       # insertion
                prev[j - 1] + (ca != cb),  # substitution
            ))
        prev = cur
    return prev[-1]


def _nearest_keyword(word: str) -> tuple[str | None, int]:
    """Return (nearest known keyword, distance) for an upper-cased token."""
    best: str | None = None
    best_d = 99
    for k in _KEYWORDS:
        d = _levenshtein(word, k)
        if d < best_d:
            best, best_d = k, d
    return best, best_d


def _find_suspected_typo_markers(payload: dict) -> list[dict]:
    """Bracketed line-head tokens that ALMOST form a marker (#12624 Defaut 1).

    Covers the gap between `_MARKER_RE` (exact keyword, alone in brackets)
    and `_MALFORMED_MARKER_RE` (bare keyword, no brackets): a bracketed
    `[CLAGED]` / `[RELEASED claim-malformed]` at line head is read by
    NEITHER, so the writer's gesture enacts nothing while they believe their
    lock is posted. WARN-only, never enacted, never auto-corrected -- the
    signal tells the writer to re-post the canonical form. Fenced blocks are
    masked (a quoted quasi marker is a citation, not a gesture).
    """
    found: list[dict] = []
    for c in payload.get("comments", []):
        body = c.get("body") or ""
        author = (c.get("author") or {}).get("login")
        for m in _QUASI_MARKER_RE.finditer(_mask_fenced_blocks(body)):
            word = m.group(1).upper()
            suffix = (m.group(2) or "").strip()
            if word in _KEYWORDS and not suffix:
                continue  # real marker -- `_MARKER_RE` already enacted it
            line = _line_for_match(body, m)
            if not _CLAIM_MOTIF_RE.search(line):
                continue  # prose mention, not a claim attempt (#11239 gate)
            if word in _KEYWORDS:
                kind, nearest = "suffix", word
            else:
                nearest, dist = _nearest_keyword(word)
                # len >= 4: a 3-letter token is within distance 2 of DONE for
                # almost any input -- the motif gate alone would not save us.
                if nearest is None or dist > 2 or len(word) < 4:
                    continue
                kind = "typo"
            found.append({
                "nearest": nearest,
                "token": m.group(1),
                "kind": kind,
                "line": line if len(line) <= 160 else line[:160] + "…",
                "author": author,
                "url": c.get("url"),
            })
    return found


def _find_single_line_composites(payload: dict) -> list[dict]:
    """Head marker + later exact keyword bracket on the SAME line (#12624 Defaut 2).

    The incident's repair comment was ONE line: `[RELEASED claim-malformed]
    ignore ... Re-claim ici : [CLAIMED] lane X -- paths: ...`. Only the head
    token is line-anchored, so the mid-line `[CLAIMED]` is NOT an event (by
    the #10228 mid-prose protection, which must stand -- the claim template
    itself carries a mid-line `[RELEASED]` citation). The net effect: the
    repair gesture enacted nothing, the re-claim never registered, and the
    lane worked uncovered. This lint names the line so the writer re-posts
    ONE COMMENT PER MARKER. Multi-LINE composites stay legal ("dernier
    marqueur gagne" -- walk order, documented in the module docstring); only
    the single-line shape is flagged, because only it silently swallows the
    second marker.
    """
    found: list[dict] = []
    for c in payload.get("comments", []):
        body = c.get("body") or ""
        author = (c.get("author") or {}).get("login")
        masked = _mask_fenced_blocks(body)
        for m in _QUASI_MARKER_RE.finditer(masked):
            line = _line_for_match(body, m)
            # masked preserves offsets, so m.end() is valid on `body`; the
            # remainder of the SAME line is what can carry a swallowed marker.
            tail = body[m.end():]
            nl = tail.find("\n")
            after_head = tail if nl == -1 else tail[:nl]
            for k in _MIDLINE_KEYWORD_RE.finditer(after_head):
                rest = after_head[k.end():]
                if _CLAIM_MOTIF_RE.search(rest):
                    found.append({
                        "head": m.group(1).upper(),
                        "swallowed": k.group(1).upper(),
                        "line": line if len(line) <= 160 else line[:160] + "…",
                        "author": author,
                        "url": c.get("url"),
                    })
                    break  # one signal per line is enough
    return found


def _warn_bare_integer_paths(paths: list[str]) -> list[str]:
    """Return the `--paths` entries that are bare integers (#10881 trap).

    `--paths` uses `nargs='+'` and swallows a TRAILING positional issue
    number: `--lane X --paths a b 10678` puts `"10678"` into the paths list,
    switches to path mode, and prints a reassuring CLEAR that measured
    nothing. A bare integer in the list is almost always that trap -- the
    correct form is `check_lane_claim.py 10678 --lane X --paths a b`
    (positional FIRST).
    """
    return [p for p in paths if p.isdigit()]


# --- modes -------------------------------------------------------------------

def _claim_age_hours(created_at: str | None, now: datetime) -> float | None:
    """Age of a claim in hours, from the server `createdAt` field.

    Returns None when `created_at` is missing or unparseable -- conservatively
    treated as NOT stale (we cannot prove an age, so we do not silently lift a
    block on a claim we cannot date). `now` is injected for testability.
    """
    if not created_at:
        return None
    parsed = _parse_iso_utc(created_at)
    if parsed is None:
        return None
    return (now - parsed).total_seconds() / 3600.0


def _is_umbrella_issue(payload: dict) -> bool:
    """Return True if `payload` describes an umbrella / EPIC-style issue (#12156).

    Mirrors `scripts/pick_idle_grain.py:130` so the two organs speak the same
    language: an issue is classified as an umbrella when (a) one of its labels
    is the literal string `EPIC` (case-sensitive -- that is the label the picker
    hydrates from `gh issue list --label EPIC`), OR (b) the title starts with
    `[EPIC` / `EPIC` after stripping the leading `[`. The label-route is the
    authoritative one; the title-route catches the historic pre-label inventory
    that the picker also accepts.

    Returns False on missing keys (defensive: the from-json path may carry a
    subset of fields). Never raises -- a malformed payload should degrade to
    the pre-#12156 behaviour (no umbrella flag) rather than crash.
    """
    try:
        labels = payload.get("labels") or []
        for lab in labels:
            name = lab.get("name") if isinstance(lab, dict) else None
            if isinstance(name, str) and name == "EPIC":
                return True
        title = payload.get("title") or ""
        upper = title.upper().lstrip("[")
        return upper.startswith("EPIC")
    except (AttributeError, TypeError):
        return False


def _parse_iso_utc(iso: str) -> datetime | None:
    """Parse a GitHub server `createdAt` (ISO 8601 UTC, trailing 'Z').

    Tolerates a fractional second component and an explicit +00:00 offset.
    Returns None on any parse failure rather than raising.
    """
    try:
        s = iso.strip()
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        dt = datetime.fromisoformat(s)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except (ValueError, TypeError):
        return None


def _run_check(payload: dict, my_lane: str, stale_threshold=None,
               now: datetime | None = None,
               my_paths: list[str] | None = None,
               pr_states: dict[int, str] | None = None) -> int:
    """Issue-claim check: exit 1 if another lane blocks, 0 if clear.

    Args:
        payload: `gh issue view --json ...` payload (or `from-json`).
        my_lane: caller lane `machine:workspace`.
        stale_threshold: optional hours; claims older than this DO NOT block
            (but a warning is printed, #9812). None = legacy epic-wide block.
        now: injected `datetime` for stale calc (testability).
        my_paths: optional list of files the caller intends to edit (#10342).
            Merged with the caller's OWN active-claim `paths:` clause (#10419)
            to form `my_scope`. An `[OVERRIDE]` or `[CLAIMED]` whose `paths:`
            clause does NOT intersect `my_scope` is treated as if it does not
            exist for the blocker test -- the claim only locks the paths it
            names. Without any declared scope (no `my_paths` AND no `paths:` on
            the caller's own claim), behaviour is unchanged: every other active
            claim blocks, regardless of its scope clause (we cannot prove
            disjointness, so we conservatively over-block).
    """
    events = _sort_events(payload)
    # One shared tracked-files walk feeds BOTH the #10881 lint and the
    # #10958 empty-scope witness (best-effort: None outside a git repo, in
    # which case both features degrade to their pre-#10958 behaviour).
    tracked = _git_tracked_files()
    # #11239 lint -- bare markers without brackets (invisible to the organ).
    # Same non-blocking spirit as the #10881 lint above: the writer learns at
    # the call site that their lock was never registered, instead of two lanes
    # discovering it via collision. Also mirrored into the JSON summary so a
    # coordinator's sweep can grep `malformed_markers` across issues.
    malformed = _find_malformed_markers(payload)
    for mm in malformed:
        who = f" by @{mm['author']}" if mm["author"] else ""
        print(
            f'WARN: marqueur sans crochets "{mm["marker"]}"{who} -- la forme '
            f'attendue est "[{mm["marker"]}]" ; sans crochets, l\'organe ne '
            f"le lit pas (unattributed_markers reste 0). {mm['line']}",
            file=sys.stderr,
        )
    # #12624 Defaut 1 -- quasi-marker lint (bracketed almost-keyword at line
    # head: `[CLAGED]`, `[RELEASED claim-malformed]`). Invisible to BOTH the
    # marker regex and the #11239 bare lint -- the gesture enacts nothing
    # while the writer believes their lock is posted. WARN-only.
    suspected = _find_suspected_typo_markers(payload)
    for s in suspected:
        who = f" by @{s['author']}" if s["author"] else ""
        if s["kind"] == "typo":
            why = f'"{s["token"]}" (distance <= 2 de {s["nearest"]})'
        else:
            why = f'"{s["token"]}..." ({s["nearest"]} + suffixe dans les crochets)'
        print(
            f"WARN: quasi-marqueur {why}{who} -- l'organe ne le lit PAS "
            f'(ni evenement, ni malformed_markers). Reposter la forme '
            f'canonique "[{s["nearest"]}] lane <machine:workspace>" dans un '
            f"commentaire neuf ; ne jamais corriger a la main le marqueur "
            f"existant (le createdAt serveur fait foi). {s['line']}",
            file=sys.stderr,
        )
    # #12624 Defaut 2 -- single-line composite lint. Only the HEAD token of
    # a line is line-anchored, so a second marker later on the SAME line is
    # never an event; the repair-gesture trap is the measured incident shape.
    composites = _find_single_line_composites(payload)
    for s in composites:
        who = f" by @{s['author']}" if s["author"] else ""
        print(
            f"WARN: marqueur compose sur une seule ligne{who} -- seul le "
            f'marqueur de TETE ({s["head"]}) est lu ; le [{s["swallowed"]}] '
            f"mid-line n'est PAS un evenement (protection mid-prose #10228). "
            f"Si l'intention etait un re-claim, il n'a PAS ete enregistre : "
            f"reposter UN commentaire par marqueur (cf. geste de reparation "
            f"#12624 dans .claude/rules/lane-claim-protocol.md). {s['line']}",
            file=sys.stderr,
        )
    # #10958 -- attach the dead-glob witness to every scoped event (own and
    # others): a glob that matches zero tracked files is surfaced in the
    # JSON (`empty_scope`) and, when it covers the WHOLE scope, lifts the
    # claim to epic-wide in `_filter_by_claim_scope` (fail-safe).
    if tracked is not None:
        for ev in events:
            if ev.get("paths"):
                ev["empty_scope"] = _empty_scope_in(ev["paths"], tracked)
    # #12740 -- dead-scope aggregate, lane-keyed, over ALL claim events.
    #
    # The #10881/#10958 witnesses surface a dead glob to a consumer that
    # reads them, but only for the ACTIVE claims (`active_claims.<lane>
    # .empty_scope`) and for the CALLER's own scope (`caller_empty_scope`).
    # A claim whose `paths:` glob is a typo and is then RELEASED/CLOSED leaves
    # the typo invisible to a JSON sweep -- the stderr WARN in
    # `_lint_claim_events` is the only channel, and it goes to STDERR, which
    # the CI gate, `pick_idle_grain` and the lane scripts do not consume.
    # That is exactly the fail-open #12740 names: a `[CLAIMED] -- paths:
    # scripts/notebook_tools/check_code_in_markdown.py` (real file:
    # detect_code_in_markdown_cells.py) claimed #12620, yet both lanes
    # worked the same real file -- the dead glob never surfaced in the JSON.
    #
    # Policy (chosen, #12740): SIGNAL, not re-block. We do NOT re-open the
    # #10958 fail-open: an ACTIVE claim whose entire scope is dead is STILL
    # lifted to epic-wide (a broken claim is not a permissive claim, and
    # lifting it back to scoped would re-create the #9764-style false CLEAR).
    # We ADD the signal -- a lane-keyed map of dead globs across every claim
    # event (open, override AND close) -- so a sweep can grep ONE key and a
    # released-claim typo still surfaces. A coordinator wanting full (a)
    # fail-CLOSED for the legitimate new-file case can address the semantic
    # deviation separately; the mechanism here is the visibility half.
    dead_scope_globs: dict[str, list[str]] = {}
    if tracked is not None:
        for ev in events:
            lane = ev.lane
            dead = ev.get("empty_scope") or []
            if not lane or not dead:
                continue
            bucket = dead_scope_globs.setdefault(lane, [])
            for g in dead:
                if g not in bucket:
                    bucket.append(g)
    active, unattributed = compute_active_claims(events, pr_states=pr_states)
    others = {ln: ev for ln, ev in active.items() if ln != my_lane}
    mine = active.get(my_lane)

    # #12345 / #12322 v2 -- the caller's CARRYING scope is computed EARLY
    # (before `query_scope` classification) so the classifier can read it.
    # `my_scope` = `--paths` merged with the caller's OWN active-claim
    # `paths:` clause (#10419). When `my_paths is None` AND the caller has
    # no own active claim with a `paths:` clause, `my_scope` is None -- the
    # caller declared no intent at all (legacy case, unchanged).
    mine_paths = mine.get("paths") if mine else None
    my_scope = list(dict.fromkeys((my_paths or []) + (mine_paths or []))) or None
    # Dead-glob witness on the CALLER side (mirror of `empty_scope` on the
    # claim side, #10958). `caller_empty_scope` lists the globs in `my_scope`
    # that match ZERO tracked files in the repo. Empty list when:
    # (a) `my_scope` is None (no declared scope -- legacy case),
    # (b) every glob in `my_scope` matches at least one tracked file,
    # (c) `tracked is None` (no git walk possible -- degrade silently).
    # The list is JSON-serialised in `caller_empty_scope` (#12345) so the
    # caller can see WHY a scope they thought is alive is being treated
    # as empty.
    caller_empty_scope = _empty_scope_in(my_scope, tracked) if tracked is not None else []
    # #12862 -- split the dead-scope verdict by CAUSE. A dead glob that is
    # SYNTACTICALLY VALID (survives `_unparseable_scope_in`: has a `/` or an
    # fnmatch metacharacter, braces closed) names files that do not exist
    # YET -- the expected state of a CREATION tranche (a notebook or lake to
    # be built). A dead glob that the parser flags as prose/fragment is a
    # typo and keeps the #12345 fail-CLOSED. Only the syntactically-valid
    # subset is eligible for the creation relaxation below.
    parse_residue = _unparseable_scope_in(my_scope)
    creation_scope_globs = ([g for g in caller_empty_scope
                             if g not in parse_residue]
                            if tracked is not None else [])

    # Override-scope filter (#10342): an `[OVERRIDE]` with a `paths:` clause
    # only locks lanes whose intended files intersect the scope. Without
    # `my_paths`, we conservatively treat every scoped override as blocking
    # (the caller's intent is unknown -- better to over-block than silently
    # merge a write that should have pinged a held lane). Note: `_filter_by_
    # claim_scope` already short-circuits when `my_scope` is entirely dead
    # (#10958 caller-side lift, line ~1614) so an entirely-dead MY scope
    # does not get to false-clear other lanes.
    others = _filter_by_claim_scope(others, my_paths, mine, tracked=tracked)

    # Stale-claim handling (#9812): a claim older than `stale_threshold` hours
    # (age from the server createdAt, NEVER the body) is treated as STALE -- it
    # no longer blocks, but a warning is printed and the new claimant MUST post
    # their own [CLAIMED] (this is not a silent bypass). Without the flag
    # (default None), behaviour is unchanged: every active claim blocks.
    stale_others: dict[str, ClaimEvent] = {}
    if stale_threshold is not None:
        now = now or datetime.now(timezone.utc)
        for ln, ev in others.items():
            age = _claim_age_hours(ev.created_at, now)
            if age is not None and age >= stale_threshold:
                stale_others[ln] = ev
        others = {ln: ev for ln, ev in others.items() if ln not in stale_others}
    else:
        # #12751 -- a zero of absence-of-measurement must not re-read as a
        # zero of absence-of-claim. Say the detection is OFF on stderr (the
        # JSON `stale_detection` field is set to "disabled" alongside).
        print("STALE_DETECTION disabled -- claims are NOT age-filtered "
              "(--no-stale or threshold None). Old claims still block.",
              file=sys.stderr)

    # #12327 -- lint qualifier runs AFTER the reducer: the epic-wide marker
    # lint can no longer say `il bloque toutes les autres lanes` for a
    # marker whose lane did not survive the scope filter or whose lane
    # re-posted a scoped claim since. We pass `active` (claim-per-lane) and
    # the FINAL `others` dict so the lint can bucket each epic-wide marker
    # into `superseded` / `sans effet` / `il bloque`.
    _lint_claim_events(
        events,
        payload.get("number"),
        tracked=tracked,
        active_claims=active,
        others_verdict=others,
        my_lane=my_lane,
    )

    # #12322 -- query_scope classifier (POST stale-filter, so the verdict
    # reflects the FINAL blocker set, not the pre-stale one). A call whose
    # CARRYING scope is empty (no `--paths` AND no `paths:` on the caller's
    # own claim) cannot prove disjointness from any FINAL blocker, so it
    # lands in `EPIC_WIDE_NO_PATHS_DECLARED`. #12345 v2: a call whose
    # declared scope is ENTIRELY dead (every glob matches zero tracked
    # files) is structurally indistinguishable from the no-scope case -- the
    # caller cannot prove disjointness because the claim they think they
    # made locks nothing. Same verdict (`EPIC_WIDE_NO_PATHS_DECLARED`),
    # same `exit 2`, plus a WARN stderr naming each dead glob so the caller
    # fixes the typo before re-running. The fail-CLOSED (the third property
    # of #12345's acceptance) lives at the verdict-emission point below --
    # a scope that is entirely dead does NOT clear to `exit 0`, it changes
    # verdict and acquires an explanation.
    if others and my_scope is None:
        query_scope = "EPIC_WIDE_NO_PATHS_DECLARED"
    elif caller_empty_scope and my_scope and len(caller_empty_scope) >= len(my_scope):
        # #12345 -- every glob in `my_scope` is dead: the caller declared a
        # scope they believe is alive, but it matches zero tracked files.
        # Cannot prove disjointness -> same verdict as the no-scope case.
        # #12862 -- UNLESS every dead glob is syntactically valid: then the
        # deadness is the EXPECTED state of a creation tranche, not a typo.
        # Such a scope stays `PATH_SCOPED`: it clears at exit 0 when no lane
        # blocks (the #12844 partition shape) and takes the normal BLOCKED
        # exit 1 when one does (the relaxation never opens a disputed
        # scope -- disjointness from a not-yet-existing tree is unprovable,
        # so any other active claim keeps blocking).
        if len(creation_scope_globs) == len(caller_empty_scope):
            query_scope = "PATH_SCOPED"
        else:
            query_scope = "EPIC_WIDE_NO_PATHS_DECLARED"
    else:
        query_scope = "PATH_SCOPED"

    # #12156 -- umbrella signal. Two booleans surface the diagnostic that
    # the body of #12156 asks to expose in `check_lane_claim.py`'s JSON:
    # (a) `is_umbrella` mirrors `pick_idle_grain.py:130` (label `EPIC` or
    #     title prefix `[EPIC`/`EPIC`), so a caller can know which urn an
    #     issue would have come from; (b) `epic_wide_on_umbrella` flags the
    #     pathology the body names -- an umbrella whose blocking claims
    #     are all epic-wide (no `paths:` or every glob dead per #10958 /
    #     #12072). The flag is True ONLY when an umbrella is held
    #     effectively-epic-wide by another lane AND the umbrella has no
    #     scoped claim; on a CLEAR issue or on a unit issue the flag stays
    #     False (the umbrella umbrellas nothing, or there is nothing to
    #     umbrella).
    is_umbrella = _is_umbrella_issue(payload)
    if is_umbrella and others:
        epic_wide_on_umbrella = all(
            (ev.get("paths") is None)
            or _claim_scope_effectively_epic_wide(ev)
            or bool(ev.scope_declared_off_marker)
            for ev in others.values()
        )
    else:
        epic_wide_on_umbrella = False

    # #14187 -- per-claim scope intersection with the caller's `--paths`.
    # Computed once on the FINAL `others` dict (post-stale-filter, post-
    # scope-filter) so the values surfaced in `active_claims` reflect the
    # verdict set, not a transient pre-filter state. Returns a list +
    # truncated-flag tuple so the JSON consumer knows if the list is a
    # sample (callers on a deep repo may hit the 25-entry cap).
    scope_intersections: dict[str, tuple[list[str], bool]] = {}
    for ln, ev in others.items():
        paths, truncated = _compute_scope_intersection_paths(
            my_scope, ev.get("paths"), tracked,
        )
        scope_intersections[ln] = (paths, truncated)
    # #14187 -- free-paths (dual of the intersection): the files in the
    # caller's `--paths` that intersect NO blocker claim. Surfaced when
    # the caller is scoped (`my_scope` non-empty). On a CLEAR verdict
    # (no blockers) the entire `my_scope` is free; on BLOCKED the helper
    # strips the intersect of each blocker. Epic-wide blockers make the
    # whole `my_scope` non-free (the helper returns `[]`); a single
    # epic-wide blocker on an umbrella sets `epic_wide_on_umbrella` so
    # the empty list is correct.
    free_paths: list[str] = []
    free_truncated = False
    if my_scope:
        free_paths, free_truncated = _compute_free_paths(
            my_scope, others, tracked,
        )

    summary = {
        "issue": payload.get("number"),
        "title": payload.get("title"),
        "my_lane": my_lane,
        "my_active_claim": bool(mine),
        "blocking_lanes": sorted(others),
        "stale_claims": sorted(stale_others) if stale_threshold is not None else None,
        # #12751 -- l'etat de la detection est nomme explicitement. "active" :
        # un seuil est pose, les claims plus vieux sont age-filtered (le
        # comportement par defaut, 48h). "disabled" : --no-stale / threshold
        # None -- rien n'est mesure du tout, un claim zombie de 415 h bloquerait
        # indefiniment. `stale_claims` vaut `null` quand disabled -- un zero
        # d'ABSENCE de mesure ne doit pas se relire comme un zero d'absence de
        # claim (avant, les deux rendaient `[]`).
        "stale_detection": "active" if stale_threshold is not None else "disabled",
        # #12156 -- umbrella classifier (`is_umbrella`) and the pathology it
        # describes (`epic_wide_on_umbrella`). Both default False: on a
        # unit-issue the umbrella flag stays False; on a CLEAR umbrella the
        # PATHOLOGY flag stays False too (the lock is empty, not held
        # wrong). The flags let a coordinator's sweep aggregate
        # `epic_wide_on_umbrella=True` across issues to count how many
        # umbrellas are stuck in the pattern #12156 names.
        "is_umbrella": is_umbrella,
        "epic_wide_on_umbrella": epic_wide_on_umbrella,
        "active_claims": {
            ln: {
                "claimed_at": ev.created_at,
                "by": ev.author,
                "marker": ev.marker,
                "url": ev.url,
                "paths": ev.get("paths"),
                # #14187 -- per-claim scope intersection with the caller's
                # `--paths`. Lets a lane see WHICH files a blocker claims
                # (and which it does NOT) without a dashboard round-trip.
                # Computed AFTER the stale + scope filters so the list
                # reflects the FINAL blocker set. `[]` when either side
                # is epic-wide (no glob scope to intersect) or when no
                # tracked file matched both (`tracked is None`).
                "scope_intersection_paths": (
                    scope_intersections.get(ln, ([], False))[0]
                    if isinstance(scope_intersections.get(ln), tuple)
                    else scope_intersections.get(ln, [])
                ),
                "scope_intersection_truncated": (
                    scope_intersections.get(ln, ([], False))[1]
                    if isinstance(scope_intersections.get(ln), tuple)
                    else False
                ),
                "scope_intersection_size": (
                    len(scope_intersections.get(ln, ([], False))[0])
                    if isinstance(scope_intersections.get(ln), tuple)
                    else (len(scope_intersections.get(ln, []))
                          if scope_intersections.get(ln) else 0)
                ),
                # #12320 -- PR reference on a `[DELIVERED]` marker. Surfaced
                # alongside the rest of the claim fields so a consumer that
                # reads "my_active_claim: false" can still pull the historical
                # PR for forensics, and so a v2 conditional reducer can drive
                # its gate on the live PR state. None on every non-DELIVERED
                # marker, and on a DELIVERED marker that did not name a PR.
                "pr_ref": ev.get("pr_ref"),
                # #12386 -- v2 conditional gate witness. Surfaces the live PR
                # state that the reducer used to bind the event's effective
                # action. None on a non-DELIVERED event, on a DELIVERED event
                # whose `pr_ref` is None, OR on a DELIVERED event whose PR
                # state could not be fetched (degraded to legacy v1 close).
                # Strings: "OPEN" (substance in flight), "MERGED" (locked),
                # "CLOSED" (attempt failed, lane free), or None (lookup-failed).
                "pr_state": ev.get("pr_state"),
                # #12386 -- locked witness for v2 MERGED branch. True ONLY on
                # an event the reducer re-marked as `open` because the PR is
                # MERGED: the substance reached main, the issue is resolved,
                # and re-claiming requires a coordinator `[OVERRIDE]`. None
                # on every other branch (legacy v1 close, OPEN, RELEASED,
                # etc.).
                "locked": ev.get("locked", False),
                # #10597 hardener -- surface the witness list of residual
                # `{`/`}` so a human reviewer can see WHY an unparseable claim
                # is being treated as epic-wide. The list may be empty (the
                # scope is fully parseable) or non-empty (the claim carries
                # patterns fnmatch cannot match).
                "unparseable_scope": ev.get("unparseable_scope") or [],
                # #12719 -- malformed-lane witness (bare date after the
                # token, trailing sentence period). The claim still parses to
                # the bare lane; the residue is surfaced so the declaring
                # lane sees its marker was malformed (report, not block).
                "lane_scope_residue": ev.get("lane_scope_residue") or [],
                # #10958 -- the dead-glob witness: globs of this claim that
                # match zero tracked files. Empty when every glob locks
                # something (or the walk was impossible). Non-empty means the
                # declaring lane should reissue the claim with valid globs;
                # when it covers the whole scope the claim is lifted to
                # epic-wide (a broken claim is not a permissive claim).
                "empty_scope": ev.get("empty_scope") or [],
                # #12072 -- the off-marker scope-declaration witness. Non-empty
                # ONLY on an epic-wide claim (`paths` is null) whose comment
                # still declares a `paths?` clause on a separate line (e.g. a
                # `Paths: ...` paragraph under the `[CLAIMED]` line). The
                # reducer could not read it (marker-line-anchored clause), so
                # the claim reduced to epic-wide while the writer believed it
                # scoped. Signal only -- never re-scopes the claim.
                "scope_declared_off_marker": ev.scope_declared_off_marker,
            }
            for ln, ev in sorted(active.items())
        },
        # #12320 -- `delivered_claims` is the forensic record of every lane
        # that CLOSED via `[DELIVERED]` on this issue. The reducer already
        # popped those lanes from `active_claims` (a DELIVERED closes), so
        # their history would otherwise be invisible to a lane that arrives
        # AFTER the close. Surfaced here so a `check` that returns
        # `my_active_claim: false` AND `blocking_lanes: []` still tells the
        # reader "another lane already delivered this, on PR #N -- verify
        # the PR state before you start work". v1 only exposes the captured
        # PR number; v2 (gated on coordinator sign-off) will look up the
        # LIVE PR state and add `pr_state: OPEN|CLOSED|MERGED`.
        "delivered_claims": sorted({
            ev.get("pr_ref")
            for ev in events
            if ev.marker == "DELIVERED" and ev.get("pr_ref")
        }),
        # #12386 -- v2 PR-state map for every historical `[DELIVERED]` close on
        # this issue. Keys = PR number, value = the LIVE state the reducer read
        # (`OPEN` / `MERGED` / `CLOSED`) or `None` when the lookup failed. A
        # consumer that needs to decide "should I re-claim?" looks up its
        # `delivered_claims` list here: any non-CLOSED value is information,
        # any CLOSED value is "free to re-claim" only if the original attempt
        # failed (no MERGED on the same number). The map is keyed by PR number
        # to match `delivered_claims`. An issue with NO deliveries has an
        # empty map.
        "delivered_claims_pr_states": {
            ev.get("pr_ref"): ev.get("pr_state")
            for ev in events
            if ev.marker == "DELIVERED" and ev.get("pr_ref") is not None
        },
        "unattributed_markers": len(unattributed),
        # #11239 -- bare-marker lines (no brackets) carrying a claim motif.
        # The organ does not read them (`_MARKER_RE` requires the brackets),
        # so they are invisible to `unattributed_markers` AND to the blocker
        # test; surfacing them here lets the writer and the coordinator see
        # the lock that never registered.
        "malformed_markers": len(malformed),
        "malformed_marker_lines": [m["line"] for m in malformed],
        # #12624 -- quasi-marker witnesses (Defaut 1). A bracketed line-head
        # token at edit distance <= 2 of a keyword (typo) or a keyword with a
        # suffix inside the brackets (`[RELEASED claim-malformed]`) is read
        # by neither the event parser nor the #11239 bare lint. Surfaced so
        # the writer learns their lock never registered.
        "suspected_typo_markers": len(suspected),
        "suspected_typo_marker_lines": [s["line"] for s in suspected],
        # #12624 -- single-line composite witnesses (Defaut 2). The head
        # marker is the only line-anchored event of its line; any second
        # bracketed keyword later on the same line is NOT an event. The
        # measured repair-trap shape (lift + re-claim in one line) shows up
        # here instead of silently swallowing the re-claim.
        "composite_single_line_markers": len(composites),
        "composite_single_line_marker_lines": [s["line"] for s in composites],
        "blocked": bool(others),
        # #14187 -- free-paths counter: files in the caller's `--paths`
        # that intersect NO blocker. A lane with `--paths 'knot_lean/**'`
        # blocked by 3 lanes whose scopes intersect 3 of 12 sub-files can
        # see `free_paths_size` and `intersection_summary` and decide
        # whether to re-scope (re-run with the 9 free files) or wait.
        # `free_paths` is the verbatim list (truncated at 25); the
        # truncated flag warns the caller it sees a sample.
        "free_paths": free_paths,
        "free_paths_size": len(free_paths),
        "free_paths_truncated": free_truncated,
        # #14187 -- human-readable one-liner, only when caller scoped.
        # Empty when epic-wide blocker(s) lock the whole scope (no list
        # to summarise) or when caller did not pass `--paths`. The string
        # surfaces the contested count and the free count together so a
        # reader can see at a glance whether the block is partial
        # (re-scope) or total (wait or release).
        "intersection_summary": (
            f"{sum(len(intersection[0]) for intersection in scope_intersections.values())} "
            f"fichiers bloques / {len(free_paths)} libres dans le scope"
            if (my_scope and not epic_wide_on_umbrella and not (others and all(
                ev.get("paths") is None or _claim_scope_effectively_epic_wide(ev)
                for ev in others.values()
            )))
            else ""
        ),
        # #12322 -- query_scope is the read-mode classifier for THIS call.
        # `EPIC_WIDE_NO_PATHS_DECLARED` means the caller did not pass `--paths`
        # AND did not post an active scoped claim, so we cannot prove
        # disjointness from any blocker. `PATH_SCOPED` covers everything else
        # (the caller is scoped one way or another). Co-rolled with the
        # `exit 2` verdict (vs `exit 1`) below -- the difference is the
        # actionable next step for the caller (re-run with `--paths` to lift
        # the over-block).
        "query_scope": query_scope,
        # #12345 -- dead-glob witness on the CALLER side (mirror of
        # `empty_scope` on the claim side, #10958). Lists the globs in
        # `my_scope` that match zero tracked files in the repo. Empty
        # when (a) caller declared no scope, (b) every glob is live, or
        # (c) `tracked` was None (no git walk possible). Non-empty means
        # the caller reissued with a typo'd path or a deleted file -- the
        # verdict below has already routed the call to `NOT_SCOPED` when
        # the dead globs cover the whole scope, otherwise the live globs
        # continue to carry the disjointness test.
        "caller_empty_scope": caller_empty_scope,
        # #12862 -- the syntactically-valid subset of `caller_empty_scope`
        # (dead globs that are not parse residue). Non-empty with an empty
        # `blocking_lanes` and `query_scope == PATH_SCOPED` = a creation
        # scope, expected to stay dead until the tranche lands.
        "creation_scope_globs": creation_scope_globs,
        # #12740 -- lane-keyed dead-glob map, aggregated over EVERY claim
        # event (not just active claims). Empty (`{}`) when no glob of any
        # claim matches zero tracked files, or when the tracked walk was
        # impossible (`tracked is None` -> cannot prove deadness). Unlike the
        # per-active-claim `empty_scope` (which disappears when a claim is
        # released) and the stderr WARN (unread by the CI gate / picker /
        # lane scripts), this key survives a release so a typo'd scope is
        # always visible to a JSON sweep. Non-blocking by design -- it only
        # reports; it does not change the verdict.
        "dead_scope_globs": dead_scope_globs,
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2))

    # #12345 -- SCOPE_DEAD_GLOB warning. When the caller declared a scope
    # whose globs include at least one dead glob, surface the witness list
    # on stderr so the caller fixes the typo at the call site instead of
    # re-running with the same broken path. Best-effort: when the file walk
    # failed (`tracked is None`), `caller_empty_scope` is empty by
    # construction -- we never false-WARN outside a git repo. The warning
    # is non-blocking on purpose: a PARTIALLY-dead scope still carries
    # disjointness on its live part (`_filter_by_claim_scope` uses `my_scope`
    # as-is); only an ENTIRELY-dead scope fails-CLOSED to `NOT_SCOPED` at
    # `exit 2` via the verdict block below.
    if caller_empty_scope:
        dead = ", ".join(repr(g) for g in caller_empty_scope)
        creation_note = (
            " Those are syntactically valid -- read as a CREATION scope "
            "(#12862): the paths are expected not to exist yet. The verdict "
            "below clears if no lane blocks."
            if creation_scope_globs else
            " Reissue with valid paths to lift this hint."
        )
        print(
            f"SCOPE_DEAD_GLOB: your declared scope contains globs that "
            f"match zero tracked files in this repo: {dead}. The live "
            f"globs (if any) continue to carry disjointness."
            + creation_note,
            file=sys.stderr,
        )

    # #10597 bonus -- SCOPE_ZERO_COVERAGE warning. When a lane declares a
    # SCOPED claim whose expanded globs do not match any tracked file in
    # the repo, the declaring lane gets a loud-but-non-blocking warning.
    # The motivation is the same as the positive control: a glob that
    # matches nothing is INDISTINGUISHABLE from a legitimately-empty
    # scope, so the lane learns at the call site that its declared lock
    # is empty and reissues with a valid glob. Best-effort: when the
    # file walk fails (e.g. not in a git repo), we skip silently -- the
    # warning is a usability hint, not a gate.
    if not others and not stale_others and mine is not None:
        warn = _scope_zero_coverage_warning(mine.get("paths"))
        if warn is not None:
            print(
                f"SCOPE_ZERO_COVERAGE: your declared claim scope "
                f"{warn['scope']!r} matches zero tracked files in the "
                f"repo. The claim is recorded, but the lock is empty -- "
                f"reissue with valid globs.",
                file=sys.stderr,
            )

    # Stale warnings -- non-blocking, but loud enough to prompt a fresh claim.
    for ln, ev in sorted(stale_others.items()):
        age = _claim_age_hours(ev.created_at, now)
        age_h = f"{age:.1f}" if age is not None else "?"
        print(
            f"STALE_CLAIM {ln} ({age_h}h >= {stale_threshold:g}h threshold) -- "
            f"reprise autorisee, poster un nouveau [CLAIMED].",
            file=sys.stderr,
        )

    # #13336 -- a DELIVERED whose PR state could not be resolved must be
    # NAMED in the verdict, whatever the verdict. Before this, the JSON
    # carried `delivered_claims_pr_states: {"N": null}` while the human line
    # still said `CLEAR:` -- the second lane on #13216 read CLEAR and
    # duplicated 49 lines that were already in an OPEN PR.
    unresolved_delivered = [
        (ev.get("lane") or "?", ev.get("pr_ref"), ev.get("pr_state_error"))
        for ev in events
        if ev.marker == "DELIVERED" and ev.get("pr_ref") is not None
        and ev.get("pr_state") is None
    ]

    # Human verdict after the JSON.
    if others:
        who = ", ".join(
            f"{ln} (@{_fmt_active(ev)})" for ln, ev in sorted(others.items())
        )
        # #10395 Variante 2: display the intentions side-by-side when the
        # comments carry them. A bare `BLOCKED` is not actionable on a
        # multi-lane EPIC where two lanes might be working on disjoint
        # notebooks -- surfacing the marker-line excerpts lets a coordinator
        # (or the worker themselves) read disjoint intent at a glance and
        # either narrow the claim's scope, post a `[RELEASED]`, or escalate.
        intent_lines: list[str] = []
        for ln, ev in sorted(others.items()):
            tag = f"  - {ln}: "
            excerpt = (ev.get("intent") if hasattr(ev, "get") else None) or "(no intent)"
            intent_lines.append(f"{tag}{excerpt}")
        intent_block = "\n".join(intent_lines)
        # #12322 -- distinct verdict for EPIC_WIDE_NO_PATHS_DECLARED. The
        # caller is asking without scoping themselves -- this is a
        # `non-scope question` showing up as a `block`, which is the trap
        # measured on #11112 (1 ESCALATION HIGH + 1 ASK HIGH in one day,
        # both from the user, both rooted in the same `exit 1 + blocker names
        # without the "re-scope to lift" hint). We keep `exit 1` semantics
        # for the genuine-scope case (PATH_SCOPED with blockers, including
        # the case where the caller narrowed their own scope and it still
        # intersects a blocker), and split out `exit 2` for the call whose
        # answer changes when the caller re-runs with `--paths`.
        if query_scope == "EPIC_WIDE_NO_PATHS_DECLARED":
            print(
                f"\nNOT_SCOPED: this call did not pass `--paths` so we cannot "
                f"prove disjointness on #{payload.get('number')}. The blockers "
                f"below may not actually conflict with the files you intend to "
                f"edit.\n"
                f"  Blocked-by (legacy `blocking_lanes` field, taken at face value): "
                f"{who}\n"
                f"  Claimed scopes (marker-line excerpts -- #10395 Variante 2):\n"
                f"{intent_block}\n"
                f"  ACTION: re-run with `--paths <glob1> --paths <glob2> ...` "
                f"matching the files you intend to edit. If your files intersect "
                f"the blockers' scopes the call returns BLOCKED at `exit 1` "
                f"(real conflict); if they are disjoint the call returns CLEAR "
                f"at `exit 0`. Exiting with `exit 2` (distinct from real "
                f"`exit 1` conflicts) so callers can branch on the verdict "
                f"without false-alarming on a scope-typo.",
                file=sys.stderr,
            )
            return 2
        print(
            f"\nBLOCKED: another lane holds an active claim on "
            f"#{payload.get('number')}: {who}.\n"
            f"Claimed scopes (marker-line excerpts -- #10395 Variante 2):\n"
            f"{intent_block}\n"
            # #14187 -- per-blocker intersection enumeration. On a wide
            # `--paths` glob the caller may see N blockers but only M
            # files are actually contested; surfacing the intersection
            # per blocker (with a truncation warning past 25 entries)
            # lets the caller re-scope to lift the block without a
            # dashboard round-trip.
            + (
                "\n".join(
                    f"  - {ln}: scope_intersection_paths = "
                    f"{paths if not truncated else paths + ['...(truncated)']}"
                    for ln, (paths, truncated) in scope_intersections.items()
                    if paths
                ) + "\n"
                if scope_intersections and any(p for p, _ in scope_intersections.values())
                else ""
            )
            + (
                f"\n  Scope intersection: "
                f"{sum(len(p) for p, _ in scope_intersections.values())} "
                f"fichier(s) conteste(s) sur l'ensemble du scope. "
                f"Fichiers libres du scope (hors blockers): "
                f"{free_paths[:10]}{'...' if len(free_paths) > 10 else ''}"
                f"{' (truncated at 25)' if free_truncated else ''}\n"
                if (free_paths or any(p for p, _ in scope_intersections.values()))
                else ""
            )
            + f"Do not start -- pick another grain, post a scope-narrowing "
              f"`[CLAIMED] paths: ...`, or wait for release.",
            file=sys.stderr,
        )
        # #12905 -- name the dead-scope lock. A blocker whose declared scope
        # is ENTIRELY dead (every glob matches zero tracked files) was lifted
        # to epic-wide by the #10958 fail-safe: it locks the WHOLE issue for
        # every lane, including callers whose live scope is provably disjoint
        # (#12905's reproduction on #12844: lane A live on the GT-17b
        # notebook, blocked by lane B reserving asymmetric_information_lean/**
        # before the path exists). The fail-closed verdict stays -- a dead
        # scope must not DE-unlock -- but the blocking text now NAMES the
        # mechanism: `WARN: glob sans correspondance` alone reads as "stale
        # worktree", not as "this claim locks the whole umbrella". Same shape
        # as the LOCKED (v2) sub-message below: explainer only, no exit-code
        # change.
        dead_scope_blockers = [
            ev for ev in others.values()
            if ev.get("paths") and _claim_scope_effectively_epic_wide(ev)
        ]
        if dead_scope_blockers:
            lines = []
            for ev in dead_scope_blockers:
                dead = ", ".join(
                    repr(g) for g in (ev.get("empty_scope") or ev.get("paths") or [])
                )
                ln = ev.get("lane") or "?"
                lines.append(
                    f"  - lane {ln} -- declared scope matches zero tracked "
                    f"files ({dead})"
                )
            print(
                f"\nDEAD-SCOPE LOCK (#12905): the blocker(s) above hold a "
                f"`paths:` scope that matches NO tracked file yet. By the "
                f"#10958 fail-safe such a claim is treated as EPIC-WIDE and "
                f"locks the whole issue #{payload.get('number')} for every "
                f"lane -- including yours, even when your scope is provably "
                f"disjoint (the nominal case of a lane reserving a path it "
                f"is about to create). The lock lifts when the blocking lane "
                f"re-issues its claim once the path exists, posts "
                f"`[RELEASED]`, or a coordinator writes an "
                f"`[OVERRIDE] lane <m:w>` comment (cf #10223).\n"
                + "\n".join(lines),
                file=sys.stderr,
            )
        # #12386 -- v2 LOCKED verdict. When the blocker is a `[DELIVERED]`
        # whose PR reached main (`locked: True`), a plain re-claim is NOT a
        # path forward -- the issue is resolved. We surface a tailored message
        # naming the merged PR and pointing at the `[OVERRIDE]` lane-comment
        # machinery as the only escape (cf #10223, marker semantics: a
        # coordinator `[OVERRIDE]` is the documented way to re-open a locked
        # claim). Without this branch, a lane arriving on a CLEAR-summary
        # would still see `blocking_lanes` empty AND the merged PR in
        # `delivered_claims_pr_states` -- the message naming the lock is what
        # closes the loop. We do NOT raise the exit code: 1 stays the
        # `BLOCKED` verdict for both branches; the message discriminates.
        locked_blockers = [
            ev for ev in others.values() if ev.get("locked")
        ]
        if locked_blockers:
            lines = []
            for ev in locked_blockers:
                pr = ev.get("pr_ref")
                ln = ev.get("lane") or "?"
                lines.append(f"  - lane {ln} -- PR #{pr} MERGED on main")
            print(
                f"\nLOCKED (v2): the issue is resolved on main by a MERGED "
                f"PR. A plain re-claim is not a path forward -- the substance "
                f"has reached `main` and the issue is considered done. The "
                f"only mechanical escape is a coordinator `[OVERRIDE] lane "
                f"<m:w>` comment on #{payload.get('number')} (cf #10223); "
                f"the writer lane that delivered the merge (or any other "
                f"lane) can also close the issue R5 (`Closes #N` in the next "
                f"PR body, or `gh issue close --reason COMPLETED`).\n"
                + "\n".join(lines),
                file=sys.stderr,
            )
        # #13336 -- fail-CLOSED witness: a lane blocked HERE because its
        # DELIVERED could not be resolved (permanent gh/schema error) must
        # see the CAUSE, not just the block. The exit code is unchanged (1
        # is BLOCKED); the message explains why a visible [DELIVERED] did
        # not release the lane.
        for ln, pr, why in unresolved_delivered:
            reason = f" ({why})" if why else ""
            print(
                f"WARN: le [DELIVERED] lane {ln} -- PR #{pr} n'a pas libere "
                f"la voie : etat de PR NON RESOLU, echec non transitoire"
                f"{reason}. Fail-CLOSED #13336 -- la lane garde son lock "
                f"jusqu'a resolution (gh/schema) ou arbitrage coordinateur.",
                file=sys.stderr,
            )
        return 1
    # #12345 -- fail-CLOSED on an entirely-dead scope, EVEN with no
    # blockers. Without this branch, a caller who typo'd every glob in
    # `--paths` would see CLEAR + `exit 0` on an issue no one else has
    # claimed, and the broken lock would authorise them to write anywhere.
    # The acceptance on #12345 names this explicitly: a scope that is
    # entirely dead "changes verdict and acquires an explanation; it
    # does not gain the authorisation to write." We route to the same
    # `NOT_SCOPED` + `exit 2` verdict the BLOCKED branch above emits,
    # minus the blocker names (there are none) -- the actionable next
    # step is the same: re-issue with valid globs.
    if query_scope == "EPIC_WIDE_NO_PATHS_DECLARED":
        dead = ", ".join(repr(g) for g in caller_empty_scope)
        print(
            f"\nNOT_SCOPED: this call's declared scope is entirely dead "
            f"on #{payload.get('number')}: every glob in `--paths` matches "
            f"zero tracked files ({dead}). The lock is empty -- the call "
            f"does NOT clear to `exit 0` because a broken scope is not a "
            f"permissive scope (#12345 fail-CLOSED). Re-run with valid "
            f"`--paths <glob>` matching the files you intend to edit; if "
            f"they intersect any blocker the call returns BLOCKED at "
            f"`exit 1`, otherwise CLEAR at `exit 0`. Exiting with `exit 2` "
            f"so callers can branch on the verdict without false-alarming "
            f"on a scope-typo.",
            file=sys.stderr,
        )
        return 2
    parts = []
    if mine:
        parts.append("resuming your own active claim")
    if stale_others:
        parts.append(f"{len(stale_others)} stale claim(s) bypassed")
    note = f" ({'; '.join(parts)})" if parts else ""
    print(f"\nCLEAR: no other lane claims #{payload.get('number')}{note}.")
    # #12862 -- the acceptance asks that one invocation surface BOTH the
    # dead-glob count AND the blocker set, so a CLEAR on a creation scope
    # can never be misread as a CLEAR on a live scope.
    if creation_scope_globs:
        print(
            f"  scope de creation : {len(creation_scope_globs)} glob(s) sans "
            f"correspondance sur les fichiers trackes, aucune lane bloquante "
            f"(blocking_lanes: []). Les chemins vises n'existent pas encore -- "
            f"etat attendu pour une tranche de creation (#12862)."
        )
    if unresolved_delivered:
        # #13336 -- CLEAR is not an all-clear when a delivery's PR could not
        # be resolved: the lane may still be holding an OPEN PR on this issue.
        for ln, pr, why in unresolved_delivered:
            reason = f" ({why})" if why else ""
            print(
                f"WARN: [DELIVERED] lane {ln} -- PR #{pr} non resolu{reason}: "
                f"l'etat vivant de la PR n'a pas pu etre lu, verifiez-la "
                f"avant de demarrer (#13336).",
                file=sys.stderr,
            )
    return 0


def _filter_by_claim_scope(
    others: dict[str, ClaimEvent],
    my_paths: list[str] | None,
    mine: ClaimEvent | None,
    tracked: list[str] | None = None,
) -> dict[str, ClaimEvent]:
    """Drop `others` lanes whose scoped claim does NOT intersect my scope.

    `my_scope` (#10419) = the caller's `--paths` intent MERGED with the
    `paths:` clause of the caller's OWN active claim (`mine`). When `my_scope`
    is empty (the caller declared no path intent at all), every other lane is
    kept -- we cannot prove disjointness, so we conservatively over-block
    (legacy behaviour, preserved).

    Per other lane:
      - No `paths:` clause (plain [CLAIMED], or epic-wide [OVERRIDE]) -> STAYS.
        Its epic-wide semantics predate the scope feature (#10342/#10419).
      - Has a `paths:` clause that INTERSECTS `my_scope` -> STAYS (real overlap).
      - Has a `paths:` clause DISJOINT from `my_scope` -> DROPPED (free). This
        is the #10419 fix: two lanes with disjoint scoped claims on the same
        multi-instance issue no longer false-block each other.
      - #10597 hardener: scope carries an `unparseable_scope` (residual `{` or
        `}` after brace expansion) -> STAYS. The read is conservative: an
        unparseable scope is fnmatch-garbage, so we cannot prove the lane's
        intent; better to over-block than to silently clear. The witness list
        is surfaced in the JSON summary under `unparseable_scopes` so the
        declaring lane sees the defect and reissues the claim with valid
        syntax.
      - #10958 fail-safe: scope is ENTIRELY dead (every glob matches zero
        tracked files, witness under `empty_scope`) -> STAYS, lifted to
        epic-wide. A claim whose scope matches nothing is not a permissive
        claim -- it is a BROKEN one (polluted suffix, typo'd path), and the
        safe hypothesis is that the lane meant something. A PARTIALLY dead
        scope (at least one live glob) stays scoped on its live part: the
        lock is real, the dead globs are surfaced in the JSON for the lane
        to fix. `tracked` None (no repo walk) -> no lift (cannot prove).

    The reducer `compute_active_claims` is untouched; this filter only prunes
    the `others` view. The active_claims summary keeps the full state, so the
    JSON output remains auditable.
    """
    mine_paths = (mine.get("paths") if mine else None) or []
    my_scope = list(dict.fromkeys((my_paths or []) + mine_paths)) or None
    if not my_scope:
        return others  # no declared scope -> cannot prove disjointness
    # #10958 fail-safe, caller side: an entirely-dead MY scope proves nothing
    # either. Dropping an other-lane claim as "disjoint" from globs that lock
    # no real file would be the same fail-open with the roles swapped, so the
    # caller keeps every other lane until its own scope is reissued clean.
    if tracked is not None and _empty_scope_in(my_scope, tracked) == my_scope:
        return others
    filtered: dict[str, ClaimEvent] = {}
    for ln, ev in others.items():
        scope = ev.get("paths")
        if not scope:
            filtered[ln] = ev  # epic-wide (plain CLAIMED or unscoped OVERRIDE)
            continue
        # #10597 hardener -- unparseable scope (residual braces) lifts the
        # claim back to epic-wide BEFORE we attempt the disjointness test.
        # fnmatch on residual `{`/`}` is guaranteed to miss every file, so
        # a "scoped disjoint" read here would silently clear the lane. The
        # witness list is surfaced via `ev.get("unparseable_scope")` for
        # the JSON audit (see _run_check summary).
        if ev.get("unparseable_scope"):
            filtered[ln] = ev  # lifted to epic-wide -- always blocking
            continue
        # #10958 fail-safe -- an ENTIRELY dead scope (every glob matches zero
        # tracked files) is a broken claim, not a permissive one: lifted to
        # epic-wide before the disjointness test, mirroring #10597. The
        # witness is `ev.get("empty_scope")` (attached by `_run_check` when
        # the walk succeeded); a missing/empty witness never lifts.
        empty = ev.get("empty_scope") or []
        if empty and len(empty) >= len(scope):
            filtered[ln] = ev  # lifted to epic-wide -- always blocking
            continue
        if _scopes_intersect(my_scope, scope, tracked):
            filtered[ln] = ev  # scopes intersect -> real collision
        # else: both scoped, disjoint -> free, drop from others
    return filtered


def _path_matches_any(paths: list[str], patterns: list[str]) -> bool:
    """Return True if any of `paths` matches any of `patterns` (fnmatch glob)."""
    for p in paths:
        if _path_matches(p, patterns):
            return True
    return False


def _glob_has_meta(glob: str) -> bool:
    """True if `glob` carries fnmatch meta (`*`, `?`, `[`) beyond literals."""
    return any(c in glob for c in "*?[")


def _literal_prefix(glob: str) -> str:
    """Leading run of literal (non-meta) characters in `glob`."""
    i = 0
    while i < len(glob) and glob[i] not in "*?[":
        i += 1
    return glob[:i]


def _prefixes_compatible(pa: str, pb: str) -> bool:
    """True if two literal prefixes can both prefix a single common string.

    ``''`` (a glob that opens on meta, e.g. ``**``) proves nothing, so it is
    compatible with anything. Two non-empty prefixes are compatible when they
    agree on every shared position -- they can then be extended to a common
    string, so we cannot cheaply prove disjointness.
    """
    if not pa or not pb:
        return True
    n = min(len(pa), len(pb))
    return pa[:n] == pb[:n]


def _glob_overlap(ga: str, gb: str) -> bool:
    """Conservative ``True`` if globs `ga` and `gb` MAY match a common string.

    Sound in the disjoint direction: if their literal prefixes conflict, no
    string matches both. Otherwise we cannot cheaply prove disjointness, so
    we report overlap (over-block). The fleet's globs are overwhelmingly
    ``*`` / ``?`` / literal (paths-scoped claims and ``--paths``); character
    classes are rare and only ever over-approximated here, which is the safe
    direction for a collision guard.
    """
    pa, pb = _literal_prefix(ga), _literal_prefix(gb)
    if pa and pb and not _prefixes_compatible(pa, pb):
        return False
    return True


def _scopes_intersect(
    a: list[str], b: list[str], tracked: list[str] | None = None
) -> bool:
    """True if path-scope `a` and path-scope `b` may cover a common file.

    This is the symmetric fix for the operand-order bug that #12656 exposed.
    The old read was ``_path_matches_any(my_scope, scope)`` -- it fed the
    CALLER's glob as the ``filename`` operand and the other lane's concrete
    path as the ``pattern``, so ``fnmatch("dir/**", "dir/file.md")`` is False
    and a joker caller was told CLEAR against a claim that demonstrably
    covered its target (fail-OPEN).

    With a `tracked` walk (the normal ``_run_check`` path and every
    check-level test) the test is EXACT: two scopes intersect iff some real
    tracked file matches both. Without it (`compute_active_claims`, which has
    no repo walk) we fall back to a conservative provable-disjoint test:
    concrete members of either side are matched against the other side's
    globs, then remaining glob-vs-glob pairs are decided by the literal
    prefix test of `_glob_overlap`. The fallback never wrongly reports
    "disjoint" (it over-blocks when unsure), which is the safe direction for
    a collision guard.
    """
    if not a or not b:
        return False
    if tracked is not None:
        for path in tracked:
            if _path_matches(path, a) and _path_matches(path, b):
                return True
        return False
    # no repo walk: concrete members of each side, matched against the other
    for side, other in ((a, b), (b, a)):
        for g in side:
            if not _glob_has_meta(g) and _path_matches(g, other):
                return True
    for ga in a:
        if not _glob_has_meta(ga):
            continue
        for gb in b:
            if not _glob_has_meta(gb):
                continue
            if _glob_overlap(ga, gb):
                return True
    return False


def _fmt_active(ev: ClaimEvent) -> str:
    return f"{ev.author or '?'}, {_fmt_utc(ev.created_at)}"


# --- path-mode (--paths, #9959) -----------------------------------------------
#
# Complements -- not replaces -- the issue-claim check. The motivating
# incident (R3D 2026-08-08) had two lanes of the SAME machine colliding on
# `knot_lean/Knots/Reidemeister.lean` minutes apart, each having passed the
# issue-claim check (the other lane's issue comment was posted AFTER each
# push but BEFORE the dispatch landed). The fix is the missing leg of L898:
# "does an OPEN PR on this machine already touch the same files?"
#
# Two lanes of a SAME machine MUST trip each other. The comparison key is
# the full `machine:workspace` string -- comparing on `machine` alone
# would miss this case by construction, which is exactly the bug.

class PathCollision:
    """One OPEN PR that intersects the caller's paths on a different lane."""

    def __init__(self, pr: dict, lane: str | None, files: list[str]) -> None:
        self.pr = pr
        self.number = pr.get("number")
        self.title = pr.get("title", "")
        self.headRefName = pr.get("headRefName", "")
        self.lane = lane
        self.files = files  # the PR files that intersect the patterns


def _run_check_paths(
    paths: list[str],
    my_lane: str,
    prs: list[dict] | None = None,
) -> int:
    """Path-mode guard: exit 2 on cross-lane OPEN-PR collision, 0 if clear.

    Args:
        paths: file paths/globs from the caller. Each PR file is matched
            against the list (fnmatch, basename-OR-full-path), and a PR
            counts as intersecting when at least one file matches.
        my_lane: caller's full lane token (e.g. "myia-po-2024:CoursIA-2").
        prs: pre-fetched list of OPEN PRs (testability seam); default None
            triggers a real `gh pr list` call via `_gh_open_prs_with_files`.

    Returns:
        0 if no other-lane PR intersects the paths,
        2 if at least one OPEN PR of another lane (or with an unreadable
          lane tag) intersects -- the calling worker MUST pick another
          grain or wait for that PR to merge/close,
        1 only on `gh` plumbing failure (raised RuntimeError is caught in
          `main` and turned into exit 1).

    Lane comparison is on the FULL `machine:workspace` string. Same
    machine + different workspace counts as a different lane (the
    motivating R3D incident). Same lane is reported as a non-issue
    ("your own PR is fine; it lands when it lands") even when the paths
    intersect, because the caller is resuming their own work.
    """
    if not paths:
        print("error: --paths requires at least one path/glob", file=sys.stderr)
        return 1
    if prs is None:
        try:
            prs = _gh_open_prs_with_files()
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    collisions: list[PathCollision] = []
    self_overlap: list[PathCollision] = []
    for pr in prs:
        pr_files = pr.get("files") or []
        if not pr_files:
            continue
        intersecting = [
            f.get("path", "") for f in pr_files
            if f.get("path") and _path_matches(f["path"], paths)
        ]
        if not intersecting:
            continue
        lane = extract_lane(pr.get("body") or "")
        coll = PathCollision(
            pr=pr, lane=lane, files=[p for p in intersecting if p],
        )
        # Three-way classification:
        #  - lane == my_lane             -> self_overlap (resuming own work)
        #  - lane is None (no Grain tag) -> collisions (cannot attribute;
        #                                    author is jsboige on every PR,
        #                                    so the tag is the only signal;
        #                                    absence = uncertainty, treated
        #                                    as a potential collision -- not
        #                                    silently ignored)
        #  - lane != my_lane (tagged)    -> collisions
        if lane == my_lane:
            self_overlap.append(coll)
        else:
            collisions.append(coll)

    def _serialise(c: PathCollision) -> dict:
        return {
            "number": c.number,
            "title": c.title,
            "headRefName": c.headRefName,
            "lane": c.lane,
            "files_intersecting": c.files,
        }

    summary = {
        "mode": "paths",
        "paths": list(paths),
        "my_lane": my_lane,
        "other_lane_collisions": [_serialise(c) for c in collisions],
        "self_overlap": [_serialise(c) for c in self_overlap],
        "untagged_prs": [
            _serialise(c) for c in collisions if c.lane is None
        ],
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2))

    if collisions:
        tagged = [c for c in collisions if c.lane is not None]
        untagged = [c for c in collisions if c.lane is None]
        msg = [
            f"\nBLOCKED: OPEN PR(s) of other lanes touch the requested paths.",
            "",
        ]
        for c in tagged:
            inter = ", ".join(c.files)
            msg.append(
                f"  - #{c.number} lane={c.lane} head={c.headRefName} "
                f"files=[{inter}] -- {c.title}"
            )
        for c in untagged:
            inter = ", ".join(c.files)
            msg.append(
                f"  - #{c.number} lane=UNREADABLE head={c.headRefName} "
                f"files=[{inter}] -- {c.title}\n"
                f"    (no `Grain:` lane tag in body; cannot attribute. "
                f"Treat as a potential collision: coordinate before pushing.)"
            )
        msg.append(
            "\nDo not start -- coordinate with the owner(s), or pick "
            "another grain that does not intersect the open PR(s)."
        )
        print("\n".join(msg), file=sys.stderr)
        return 2

    if self_overlap:
        own_numbers = ", ".join(f"#{c.number}" for c in self_overlap)
        print(
            f"\nCLEAR for paths {paths!r} -- you already have an OPEN PR on "
            f"the same paths ({own_numbers}). Resuming your own work is fine; "
            f"the path gate does not block your own lane.",
            file=sys.stderr,
        )
        return 0

    print(f"\nCLEAR: no OPEN PR of another lane touches {paths!r}.")
    return 0


def _run_open_prs_on(
    paths: list[str],
    prs: list[dict] | None = None,
) -> int:
    """List OPEN PRs touching `paths` across ALL lanes (no lane filter).

    #13595: the `--paths` guard filters its result by *lane* -- an OPEN PR of
    the caller's OWN lane reads as "your own PR is fine" and is dropped from
    the verdict. That is exactly the blind spot of case A (one machine, same
    lane, two worktrees, 74 s apart): there is only one lane, so the guard
    finds no *other*-lane collision and concludes CLEAR while two branches of
    the same lane are racing on the same files.

    This mode drops the lane filter entirely: it lists EVERY OPEN PR whose
    files intersect `paths`, whatever the lane -- INCLUDING the caller's own.
    It is NON-BLOCKING (returns 0 always): the signal is broad enough to
    produce legitimate false positives (two PRs on a large notebook), so the
    lane decides, it is never summarily refused (#13595 point 3).

    Returns:
        0 always (list mode). A `RuntimeError` from `gh` is surfaced by the
          caller as exit 1; this mode itself carries no collision verdict.
    """
    if not paths:
        print("error: --open-prs-on requires at least one path/glob",
              file=sys.stderr)
        return 1
    if prs is None:
        try:
            prs = _gh_open_prs_with_files()
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    hits: list[dict] = []
    for pr in prs:
        pr_files = pr.get("files") or []
        intersecting = [
            f.get("path", "") for f in pr_files
            if f.get("path") and _path_matches(f["path"], paths)
        ]
        if not intersecting:
            continue
        lane = extract_lane(pr.get("body") or "")
        hits.append({
            "number": pr.get("number"),
            "headRefName": pr.get("headRefName"),
            "lane": lane,
            "lane_readable": lane is not None,
            "files": intersecting,
            "title": pr.get("title"),
        })

    if hits:
        print(
            f"OPEN PRs on paths {paths!r} "
            f"(mode open-prs-on -- NO lane filter, non-blocking):"
        )
        for h in hits:
            lane = h["lane"] if h["lane_readable"] else "UNREADABLE"
            print(
                f"  #{h['number']} lane={lane} head={h['headRefName']} "
                f"files=[{', '.join(h['files'])}] -- {h['title']}"
            )
        print(
            "\nNote: your OWN lane appearing here is the case-A signal "
            "(same lane, two worktrees). Re-check before opening a branch, "
            "or confirm the other PR is resolved/separate before pushing.\n"
            "Re-query equivalent (the geste from #13595):"
        )
        print(
            "  gh pr list --state open --json number,headRefName,files "
            "--jq '.[] | select(.files[].path | test(\"<chemin>\")) "
            "| \"#\\(.number) \\(.headRefName)\"'"
        )
    else:
        print(f"NO open PR intersects paths {paths!r}. Path is free.")
    return 0


def main(argv: list[str] | None = None) -> int:
    # Windows FR : stdout d'un tube prend locale.getpreferredencoding() =
    # cp1252. Les verdicts de ce script contiennent des fleches (U+2192) et du
    # francais accentue -- une fleche n'existe PAS dans cp1252, donc le print
    # leve UnicodeEncodeError et le script sort en **exit 1**.
    #
    # C'est le pire mode de defaillance possible ici : lane-claim-protocol.md
    # prescrit d'appeler ce script AVANT d'editer, et un exit non-nul s'y lit
    # "claim d'une autre lane, ne pas commencer". Un plantage d'encodage se
    # deguisait donc en verrou, et faisait sauter un grain pourtant libre.
    #
    # Le parent (pick_idle_grain.py) passe PYTHONIOENCODING=utf-8, mais cela ne
    # couvre que SON chemin d'appel : l'invocation directe -- celle que la regle
    # prescrit -- restait exposee. On se protege donc ici, a la source.
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8", errors="replace")
    p = argparse.ArgumentParser(
        description=(
            "Lane-claim guard (#9774): check/post [CLAIMED] on an issue before "
            "editing. Defaut-2-safe: server UTC timestamps only."
        )
    )
    p.add_argument("issue", nargs="?", default=None,
                   help="issue number (or URL); optional when --paths is used "
                        "(--paths does not need an issue number, the dispatch "
                        "cote coordinateur calls it pre-claim to detect cross- "
                        "lane PR collisions on the same files)")
    p.add_argument("--lane", required=True,
                   help="your lane, e.g. myia-po-2024:CoursIA")
    p.add_argument("--from-json", metavar="FILE",
                   help="read `gh issue view` JSON from FILE (offline/test mode)")
    p.add_argument("--stale-threshold", type=float, metavar="HOURS", default=48.0,
                   help="treat OTHER lanes' claims older than HOURS as stale: "
                        "warn and do not block (age from server createdAt, never "
                        "the body). The new claimant must still post its own "
                        "[CLAIMED] -- this is not a silent bypass. Default 48 "
                        "(#12751): the canonical invocation now MEASURES. "
                        "`--no-stale` restores the legacy behaviour (every active "
                        "claim blocks).")
    p.add_argument("--no-stale", action="store_true", default=False,
                   help="#12751: disable staleness detection entirely (legacy "
                        "behaviour: every active claim blocks, nothing is "
                        "age-filtered). The detected state is reported as "
                        "`stale_detection: \"disabled\"`.")
    # #13057 -- repeated `--paths` occurrences form one union. argparse's
    # default `store` action kept only the LAST occurrence, so adding a disjoint
    # path could erase an earlier intersecting path and turn BLOCKED into CLEAR.
    # `extend` keeps a flat list across both accepted CLI forms:
    # `--paths a b` and `--paths a --paths b`.
    p.add_argument("--paths", metavar="PATH", nargs="+", action="extend",
                   default=None,
                   help="path-mode (#9959): one or more file paths/globs. "
                        "Repeated --paths occurrences are combined (#13057). "
                        "Exits 2 if any OPEN PR of a different lane (or with "
                        "an unreadable lane tag) has files[] intersecting. "
                        "Exits 0 if no collision, 1 on usage/`gh` failure. "
                        "Lane key is full `machine:workspace` (same-machine "
                        "different-workspace counts as different lane). "
                        "Complements the issue-claim check, does not replace. "
                        "When supplied TOGETHER with an issue number "
                        "(`check_lane_claim ISSUE --paths PATH ...`), the "
                        "scope is also applied to `[OVERRIDE]` markers that "
                        "carry a `paths:` clause (#10342): an override whose "
                        "scope does not intersect the caller's paths is "
                        "treated as if it did not exist for the blocker "
                        "decision. Without `--paths`, override scope is "
                        "ignored (legacy epic-wide behaviour, preserved).")
    p.add_argument("--open-prs-on", metavar="PATH", nargs="+", action="extend",
                   default=None,
                   help="list-mode (#13595): one or more file paths/globs. "
                        "List EVERY OPEN PR whose files[] intersect, "
                        "REGARDLESS of lane -- including the caller's own "
                        "(case A: same lane, two worktrees). NON-BLOCKING: "
                        "returns 0 always; the lane decides, it is never "
                        "refused. Use when a PATH may be raced by another "
                        "worktree of your own machine/lane, where the "
                        "lane-filtered `--paths` guard is structurally blind. "
                        "Mutually exclusive with `--paths`.")
    act = p.add_mutually_exclusive_group()
    act.add_argument("--claim", metavar="INTENTION",
                     help="post a [CLAIMED] comment for your lane. Runs the "
                          "issue-claim check FIRST and refuses to post when "
                          "another lane blocks (use --force only for "
                          "coordinator arbitration). A --paths scope is "
                          "rendered into the marker, never dropped (#11064).")
    act.add_argument("--release", nargs="?", const="", default=None,
                     metavar="NOTE", help="post a [RELEASED] comment")
    p.add_argument("--force", action="store_true",
                   help="post a [CLAIMED] even when the pre-claim check is "
                        "blocked (#11064). Coordinator arbitration only -- "
                        "the reading side still honours [OVERRIDE] markers.")
    args = p.parse_args(argv)
    # #12751 -- default is 48 (measuring). `--no-stale`/threshold=None restores
    # the legacy behaviour (every claim blocks, nothing age-filtered); the
    # disabled state is reported honestly as `stale_detection: "disabled"`.
    if args.no_stale:
        args.stale_threshold = None

    # #10881 -- `nargs='+'` on --paths swallows a TRAILING positional issue
    # number (`--lane X --paths a b 10678` puts "10678" into the paths list,
    # switches to path mode, and prints a reassuring CLEAR that measured
    # nothing). Warn loudly when a paths entry is a bare integer; the warning
    # is non-blocking (the caller may have meant a numeric path), but the
    # measured trap is precisely this shape.
    if args.paths is not None:
        for entry in _warn_bare_integer_paths(args.paths):
            print(
                f"WARN: --paths entry {entry!r} is a bare integer -- an issue "
                f"number swallowed by nargs='+' (#10881). Correct form: "
                f"`check_lane_claim.py {entry} --lane <lane> --paths ...` "
                f"(positional FIRST).",
                file=sys.stderr,
            )
    if args.open_prs_on is not None:
        for entry in _warn_bare_integer_paths(args.open_prs_on):
            print(
                f"WARN: --open-prs-on entry {entry!r} is a bare integer -- an "
                f"issue number swallowed by nargs='+' (#10881). Correct form: "
                f"`check_lane_claim.py {entry} --lane <lane> --open-prs-on ...` "
                f"(positional FIRST).",
                file=sys.stderr,
            )

    # #13595 -- `--open-prs-on` (list-mode) and `--paths` (guard-mode) are
    # mutually exclusive. The guard fires BEFORE either branch, else `--paths`
    # returns first and the caller never learns their `--open-prs-on` was
    # silently ignored.
    if args.open_prs_on is not None and args.paths is not None:
        print("error: --open-prs-on and --paths are mutually exclusive; "
              "run them separately", file=sys.stderr)
        return 1

    # Path-only mode (#9959) does NOT require an issue number -- it is the
    # missing leg of L898 dispatched pre-claim to detect cross-lane PR
    # collisions on the same files. We branch here when `--paths` is supplied
    # WITHOUT an issue; when both are present we go through the issue-claim
    # check with `my_paths` (the `--paths` are then used to scope-bind any
    # `[OVERRIDE]` markers, #10342).
    if args.paths is not None and args.issue is None:
        return _run_check_paths(args.paths, args.lane)

    # #13595 -- list-mode: no lane filter, non-blocking. `--open-prs-on` is
    # its own mode and does not require an issue number.
    if args.open_prs_on is not None:
        return _run_open_prs_on(args.open_prs_on)

    # Posting modes: short-circuit before any read. Both require an issue.
    if args.issue is None:
        print("error: an issue number is required (or use --paths PATH ...)",
              file=sys.stderr)
        return 1
    if args.claim is not None:
        # #11064: `--claim` must not short-circuit the check. The old path
        # posted FIRST (unchecked) and printed a reassuring "posted" line
        # while another lane held the claim -- the exact shape of the #11044
        # collision. Now: run the issue-claim check; a blocked issue REFUSES
        # to post (exit 1, nothing written). `--force` restores the old
        # bypass for coordinator arbitration (the reading side still honours
        # `[OVERRIDE]` markers).
        if not args.force:
            try:
                if args.from_json:
                    payload = json.loads(
                        Path(args.from_json).read_text(encoding="utf-8"))
                else:
                    payload = _gh_issue_comments(args.issue)
            except (RuntimeError, json.JSONDecodeError, OSError) as exc:
                print(f"error: {exc}", file=sys.stderr)
                return 2
            rc = _run_check(payload, args.lane,
                            stale_threshold=args.stale_threshold,
                            my_paths=args.paths)
            if rc != 0:
                print(f"BLOCKED: not posting [CLAIMED] on #{args.issue} "
                      f"-- another lane holds an active claim (the check "
                      f"above names it). Use --force only for coordinator "
                      f"arbitration.",
                      file=sys.stderr)
                return rc
        body = _CLAIM_BODY_TMPL.format(
            lane=args.lane, intention=args.claim,
            paths_clause=_paths_clause(args.paths),
        )
        try:
            _post_comment(args.issue, body)
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        scope = f" (paths: {', '.join(args.paths)})" if args.paths else ""
        print(f"posted [CLAIMED] lane {args.lane} on #{args.issue}{scope}")
        return 0
    if args.release is not None:
        # #12386 v2 -- smart DELIVERED-vs-RELEASED selection. A `[RELEASED]`
        # would only free the active_claims slot and lose the merged-link
        # that powers the LOCKED verdict above. When the caller has a single
        # OPEN PR in their lane referencing the issue, we post
        # `[DELIVERED] … -- PR #N` instead; the PR-state gate then stays
        # live until the PR reaches MERGED (`locked: True`).
        #
        # Smart-selection rules (the `--note` arg can override):
        #   1. `--note` literal starting with `delivered:#N` forces
        #      `[DELIVERED]` with that exact PR (escape hatch for the
        #      multi-PR ambiguity case).
        #   2. Else, `_find_open_pr_for_issue_by_lane` returns a single
        #      PR or None.
        #   3. Single match -> `[DELIVERED]` with that PR.
        #   4. None match -> `[RELEASED]` (back-compat: caller may be
        #      releasing without an OPEN PR referencing this issue).
        #   5. Multi-match -> `[RELEASED]` (the WARN has been emitted by
        #      the helper; the caller should disambiguate next cycle).
        note = args.release or "released"
        chosen_kind = "RELEASED"
        chosen_pr: int | None = None
        forced = note.lower().startswith("delivered:#")
        if forced:
            forced_str = note.split(":", 1)[1].strip()
            try:
                chosen_pr = int(forced_str.lstrip("#"))
                chosen_kind = "DELIVERED"
            except ValueError:
                print(
                    f"WARN: --note {note!r} starts with 'delivered:#' but "
                    f"cannot be parsed as an integer; falling back to "
                    f"[RELEASED].",
                    file=sys.stderr,
                )
                chosen_kind = "RELEASED"
                chosen_pr = None
        else:
            try:
                chosen_pr = _find_open_pr_for_issue_by_lane(
                    int(args.issue), args.lane,
                )
            except (RuntimeError, ValueError) as exc:
                # gh failure or non-integer issue -- degrade to RELEASED
                # rather than refusing the post (the comment is the
                # primary contract; the PR-binding is a nicety).
                print(
                    f"WARN: could not scan OPEN PRs to bind "
                    f"[DELIVERED]: {exc}. Falling back to [RELEASED].",
                    file=sys.stderr,
                )
                chosen_pr = None
            if chosen_pr is not None:
                chosen_kind = "DELIVERED"
        if chosen_kind == "DELIVERED":
            body = _DELIVERED_BODY_TMPL.format(
                lane=args.lane, pr_ref=chosen_pr,
                paths_clause=_paths_clause(args.paths),
            )
        else:
            body = _RELEASE_BODY_TMPL.format(
                lane=args.lane, note=note,
                paths_clause=_paths_clause(args.paths),
            )
        try:
            _post_comment(args.issue, body)
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        scope = f" (paths: {', '.join(args.paths)})" if args.paths else ""
        marker = "[DELIVERED]" if chosen_kind == "DELIVERED" else "[RELEASED]"
        print(f"posted {marker} lane {args.lane} on #{args.issue}{scope}")
        return 0

    # Check mode (default). `--paths` (when supplied with an issue) threads
    # through to `_run_check` as `my_paths` -- it scopes `[OVERRIDE]` blockers
    # by intersection. Posting modes already returned above, so `args.paths`
    # here is unambiguously the scope-binding form.
    try:
        if args.from_json:
            payload = json.loads(Path(args.from_json).read_text(encoding="utf-8"))
        else:
            payload = _gh_issue_comments(args.issue)
    except (RuntimeError, json.JSONDecodeError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return _run_check(
        payload,
        args.lane,
        stale_threshold=args.stale_threshold,
        my_paths=args.paths,
    )


if __name__ == "__main__":
    sys.exit(main())
