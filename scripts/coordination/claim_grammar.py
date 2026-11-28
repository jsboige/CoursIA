#!/usr/bin/env python3
"""Grammaire des marqueurs de claim + automate -- module pur (T4 de #26364).

Extraction fidele de `scripts/check_lane_claim.py` (phase 1, "construire a
cote") : le decoupage est byte-exact, recits d'incidents compris. Le contrat :

  - AUCUN reseau : ni `gh`, ni HTTP. La lecture groupee appartient a
    l'appelant (`scripts/coordination/gh_bulk.py`) ; les etats de PR se
    INJECTENT via `pr_states` (la voie paresseuse par `gh pr view` reste a la
    CLI, cf `_resolve_delivered_v2`).
  - git LOCAL seulement (`_git_tracked_files`), jamais le reseau.
  - Tant que la phase 2 (bascule) n'a pas eu lieu, `check_lane_claim.py`
    reste l'organe qui fait autorite : ce module est son egal byte-a-byte sur
    les memes entrees, et l'equivalence est PIREE par
    `scripts/tests/test_claim_grammar.py` sur un lot reel enregistre --
    si l'ancien fichier change sans que le module suive, le test rougit.

Deux divergences documentees (et pirees par test) :
  1. `_unwrap_trapped_body` : le chemin vers `scripts/ci` est recalcule car le
     module vit un niveau plus bas que l'original ;
  2. `_resolve_delivered_v2` : sans `pr_states` injecte, le module ne fetch
     PAS -- il fail-CLOSE (#13336) : temoin `pr_state_error` + "open", le
     verrou de la lane n'est PAS libere par un oubli d'injection. La CLI
     injecte toujours la carte.

Les numeros d'issue (#NNNNN) cites dans les commentaires renvoient aux
incidents fondateurs mesures dans l'original -- ils sont la pour ne pas les
redecouvrir.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

# Lecteur de lane partage (#9485) -- meme lecteur que l'original.
from grain_tag import extract_lane, lane_marker_residues  # noqa: E402


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
# #22445 -- [DELIVERED] honours the clause too. It is a CLOSE marker, but the
# v2 conditional reducer re-marks it as an ACTIVE OPEN claim while its PR is
# OPEN/MERGED (`_resolve_delivered_v2`), so the lane keeps occupying the
# issue: with the clause ignored, a lane that delivered a BOUNDED slice
# re-locked the whole umbrella as epic-wide -- the exact opposite of the
# protocol's advice to declare `paths:` and stop blocking siblings. On the
# CLOSED branch the event is popped and the scope stays informational, same as
# [RELEASED]. A dead glob still lifts the re-marked claim back to epic-wide
# (`empty_scope`, #10958), so this widening cannot fail open.
# Same leading-decoration tolerance as `_MARKER_RE` (#10906). In practice the
# reducer feeds this regex the `_line_for_match` output (which starts at the
# `[`), so the legacy `^[ \t]*\[` anchor already worked -- the prefix group is
# defense-in-depth for direct calls on a full decorated marker line. The path
# list capture deliberately does NOT strip a trailing `**`/`__` (closing pair
# of a bold-wrapped claim): `paths: dir/**` is a legitimate recursive glob,
# indistinguishable from a closing decorator by suffix alone. Trailing `*` in
# fnmatch matches empty, so a captured `glob**` still matches `glob`.
# #23720 (2026-10-31, lane myia-ai-01:CoursIA-2) -- la clause canonique est
# le SEGMENT FINAL de la ligne du marqueur (`-- paths: g1, g2`). Le motif
# ci-dessous lit donc la **derniere** occurrence du mot-cle sur la ligne :
# le quantificateur `[^\n]*` est désormais **greedy** (il etait non-greedy),
# de sorte que le moteur backtracke depuis la fin de ligne.
#
# Pourquoi : une lane qui ecrit "une clause `paths:` ..." dans le texte
# d'INTENTION de son marqueur detonait le parseur -- le mot-cle etait lu au
# premier endroit, la truncation d'annotation (` -- `) coupait le reste, et la
# portee rendue etait un jeton MORT ("`"), c'est-a-dire une claim epic-wide
# (fail-closed #10958/#11098) : la lane se verrouillait elle-meme sur
# l'issue entiere. Mesure sur `main` au tip `3c599591c2d2` :
#
#   '[CLAIMED] lane X -- une clause `paths:` (backticks) -- paths: a.py'
#     -> portee rendue : ["`"]      (avant #23720)
#     -> portee rendue : ["a.py"]   (apres #23720)
#
# Le lookbehind `(?<![`"'\w])` refuse une occurrence **encadree** (backtick,
# guillemet) ou precedee d'un caractere de mot : une mention en prose n'est
# pas une clause. Une occurrence en MARQUE (`**paths:**`) reste acceptee --
# la decoration n'est pas un mot.
_PATHS_CLAUSE_RE = re.compile(
    r"(?im)^[ \t]*" + _DECOR + r"(?:\*\*|__)?[ \t]*\[\s*(?:CLAIMED-AMEND|CLAIMED|RELEASED|DELIVERED|OVERRIDE)\s*\][^\n]*(?<![`\"'\w])paths\s*:\s*([^\n]+?)\s*$"
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


# #24824 -- la memo est trop petille (8192) pour le volume de corps d'une
# fenetre de claims : elle evictait et recalcule. Elargie pour tenir le
# working set ; le verdict est une fonction pure du corps.
@lru_cache(maxsize=65536)
def _unwrap_trapped_body(body: str) -> str:
    """Le corps REEL quand la publication a piege son propre payload (#19971).

    La classe de transport #16866/#17270 a une victime que l'organe ne voyait
    pas : quand le corps publie est l'objet `{"body": "..."}` COMPLET, le
    marqueur `[CLAIMED]` vit dans une VALEUR de chaine -- precede de
    `  "body": "`, ses sauts de ligne echappes en `\\n` litteraux. `_MARKER_RE`
    est ancre en debut de ligne (`(?m)^`) : il n'existe alors aucune ligne ou
    ancrer le marqueur, l'organe rend `CLEAR` et le lecteur croit le grain
    libre. Trois instances mesurees (#19727, #19796, #19915), dont deux grains
    reellement en cours de traitement (po-2024 sur #19727, po-2023 sur #19796).

    Ce n'est PAS un elargissement de `_MARKER_RE` : le contrat de l'organe
    reste cote EMISSION (`.claude/rules/gh-posting-hygiene.md`), la lecture
    DEFENSIVE du transport appartient a l'ENTREE. Le corps unwrape -- la
    valeur de la cle `body`, exactement ce que l'auteur a ecrit -- est celui
    que `_MARKER_RE` ET la clause `paths:` doivent lire ; sans lui, un claim
    scope reduit a epic-wide par accident.

    Organe-first : le predicat n'est pas re-ecrit ici, il est REUTILISE de
    `scripts/ci/check_gh_comment_traps.py::classify_payload_body` -- l'organe
    qui nomme deja ce payload `TRAPPED [json-payload]`. Un corps d'une autre
    forme traverse inchange (la fonction rend `None`, jamais une devinette).
    Import tardif et defensif : si le module est injoignable, le comportement
    d'avant ce correctif est preserve -- une exception ici ferait passer un
    blocage pour une absence, ce qui est precisement le defaut repare.
    """
    if not body:
        return body
    try:
        ci_dir = Path(__file__).resolve().parents[1] / "ci"  # T4: module un niveau plus bas
        if str(ci_dir) not in sys.path:
            sys.path.insert(0, str(ci_dir))
        from check_gh_comment_traps import classify_payload_body  # noqa: PLC0415
    except Exception:  # noqa: BLE001 -- organe optionnel : repli sur le corps brut
        return body
    inner = classify_payload_body(body)
    return inner if inner is not None else body


def _parse_claim_events(comment: dict,
                        tracked: list[str] | None = None) -> list[ClaimEvent]:
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
    # #19971 -- lecture defensive du transport AVANT tout parsing : un corps
    # publie sous forme de payload JSON est unwrape une fois, ici, et c'est le
    # corps REEL qui alimente `_MARKER_RE`, la clause `paths:` et `_body`.
    body = _unwrap_trapped_body(comment.get("body") or "")
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
            unparseable_scope=_unparseable_scope_in(paths, tracked) if paths else [],
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


def parse_claim_event(comment: dict,
                     tracked: list[str] | None = None) -> ClaimEvent | None:
    """Classify one issue comment into a claim event, or None if not a marker.

    Legacy single-event view: the LAST bracketed marker of the comment is the
    final intent (backward-compatible with every existing caller and the
    Defaut-2 / lane / scope semantics). The full reader is `_parse_claim_events`
    -- one event per marker line (#10881 addendum), used by `_sort_events`; for
    a single-marker comment the two views are identical. The lane is read by
    `extract_lane`; None when the body carries no lane token (surfaced as
    "unattributed", never guessed). The timestamp is the comment's server
    `createdAt` -- the Defaut-2 fix: body stamps are not trusted.

    `tracked` is forwarded to `_unparseable_scope_in` so a bare word that is
    a tracked filename at the repo root (#19435) is accepted as a valid glob.
    """
    events = _parse_claim_events(comment, tracked=tracked)
    return events[-1] if events else None


# #23720 -- les wrappers d'un jeton de chemin. Une lane qui ecrit son chemin
# entre backticks ou guillemets (`paths: \`a/b.py\``) produisait un glob qui
# ne matche AUCUN fichier suivi : la portee etait lue morte, donc la claim
# devenait epic-wide (fail-closed #10958/#11098) et verrouillait l'issue
# entiere au lieu du fichier vise. Le retrait des wrappers est fait ICI, a la
# lecture, ce qui repare aussi les claims DEJA poses -- aucune re-emission
# du claim n'est demandee a la lane.
_PATH_TOKEN_WRAPPERS = ("`", '"', "'")


def _normalize_path_token(token: str) -> str:
    r"""Strip the surrounding backticks/quotes of a declared path token.

    `paths: \`a/b.py\`` and `paths: a/b.py` must denote the SAME scope:
    otherwise the claim's scope and the caller's `--paths` are compared as
    two spellings of one path, and the comparison yields nothing.

    The wrappers are removed only when they are **paired** (`\\`a/b.py\\``,
    `"a/b.py"`, `'a/b.py'`), and the stripping repeats so a doubly-wrapped
    token (`\\`\\`a/b.py\\`\\``) is unwrapped too. A quote in the MIDDLE of a
    filename is left untouched -- only the edges are decoration.

    A token that carried nothing but wrappers normalises to the empty
    string; the caller drops it (a scope made only of decoration was dead
    before as well -- it simply said so more clearly).
    """
    t = token.strip()
    unwrapped = True
    while unwrapped and len(t) >= 2:
        unwrapped = False
        head, tail = t[0], t[-1]
        if head in _PATH_TOKEN_WRAPPERS and head == tail:
            t = t[1:-1].strip()
            unwrapped = True
    # Unbalanced leftovers (a single stray quote at one edge) are decoration
    # too -- `fnmatch` would never match them.
    return t.strip("`\"'").strip()


def _split_paths_brace_aware(raw: str) -> list[str]:
    """Split a comma-separated path list on commas OUTSIDE `{...}` groups.

    A scope like `search-{6,8,9}-*.yaml` uses commas as brace alternatives,
    not as list separators. A naive `raw.split(",")` fragments it into
    `["search-{6", "8", "9}-*.yaml"]` -- three invalid globs that `fnmatch`
    will never match, so the claim silently ends up EPIC-WIDE by accident
    (#10597). This splitter tracks brace depth and only splits on depth-0
    commas, keeping each brace group intact. Empty fragments from stray
    commas are dropped (`paths: a, , b` -> `["a", "b"]`).

    #23720 -- each fragment is then NORMALIZED (`_normalize_path_token`):
    the backticks/quotes a lane wrapped its path in are decoration, not part
    of the path. The normalization runs AFTER the brace-aware split, so a
    wrapped brace group (`` `search-{6,8,9}-*.yaml` ``) is first kept whole
    and then unwrapped -- it still expands into three matchable globs
    (#10597 preserved).
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
    return [t for t in (_normalize_path_token(p) for p in parts) if t]


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

    Recognised on [CLAIMED], [RELEASED], [DELIVERED], [OVERRIDE], and
    [CLAIMED-AMEND] marker lines (#10342 introduced the clause for [OVERRIDE];
    #10419 extended it to [CLAIMED] and [RELEASED] so disjoint scoped claims no
    longer false-block each other on a multi-instance issue; #13022 added
    [CLAIMED-AMEND], where the clause names the replacement scope; #22445 added
    [DELIVERED], whose v2 re-marking as an active claim while its PR is
    OPEN/MERGED otherwise re-locked the whole umbrella epic-wide -- a bounded
    delivery must not narrow back into a full-lane lock). Returns
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

    #23720 -- the clause is read from the LAST unquoted occurrence of the
    keyword on the marker line (see `_PATHS_CLAUSE_RE`), and each resulting
    token is NORMALIZED (`_normalize_path_token`): a path wrapped in
    backticks or quotes denotes the same scope as the bare path. Without
    both, a claim written in a natural sentence could end up with a DEAD
    scope -- and a dead scope is read as epic-wide, which locks the whole
    issue instead of the file the lane meant to hold.
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


def _unparseable_scope_in(parts: list[str] | None,
                           tracked: list[str] | None = None) -> list[str]:
    """Return the subset of `parts` that look UNMATCHABLE: brace residue
    (`{` / `}`) OR a glob-free prose fragment (no `/`, no fnmatch meta).

    After `_extract_paths_clause` and `_expand_brace_groups`, any pattern
    residue containing braces is a SCOPE THAT FNMATCH WILL NEVER MATCH
    (fnmatch knows `*` `?` `[seq]` `[!seq]` -- not `{a,b}`). The safe
    read is to treat the claim as epic-wide (conservateur -- #10597
    acceptance #2). The list returned here is the witness, so the
    reducer and the JSON audit can surface it without re-parsing.

    #12052 -- a second class of unparseable residue: PROSE WITHOUT SLASHES OR
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

    #19435 -- a THIRD class accepted: a bare word (no `/`, no fnmatch meta)
    that is the LITERAL NAME of a tracked file at the repo root (e.g.
    `_quarto.yml`, `Makefile`, `LICENSE`). The fnmatch semantics treat a
    bare word as a literal filename; if the word matches a tracked file,
    the glob is well-formed. The check accepts these when `tracked` is
    provided (caller has done a `git ls-files` walk); without `tracked`,
    the bare word is still residue (fail-CLOSED outside a git repo).
    Empty `parts` -> empty witness (caller semantics).
    """
    if not parts:
        return []
    fnmatch_metas = set("*?[!")
    tracked_set = set(tracked) if tracked else None
    residue: list[str] = []
    for p in parts:
        if "{" in p or "}" in p:
            residue.append(p)
            continue
        # A glob contains at least one path separator OR one fnmatch meta.
        # A bare word without either is prose that fnmatch will treat as a
        # literal filename (matching only the literal string). Two cases
        # are accepted as well-formed:
        #   1. the bare word is a TRACKED FILE at the repo root (#19435) --
        #      fnmatch will match it against the literal filename.
        #   2. (n/a) the glob is genuinely unmatchable: any other bare
        #      word is residue and lifts the claim to epic-wide (#12052).
        if "/" not in p and not any(m in p for m in fnmatch_metas):
            if tracked_set is not None and p in tracked_set:
                continue
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


def _sort_events(payload: dict,
                 tracked: list[str] | None = None) -> list[ClaimEvent]:
    """Parse + chronologically sort claim events from a `gh issue view` payload.

    Uses `_parse_claim_events` -- one event per marker line (#10881) -- so a
    comment carrying markers for several lanes reduces correctly instead of
    collapsing to a single (mis-attributed) event. Events from the same comment
    share the server `createdAt`; the stable sort preserves their in-comment
    marker order, so the walk-order reducer sees `[CLAIMED] X\n[DONE] X` as
    open-then-close (final state inactive), exactly as before.

    `tracked` is forwarded to each `_parse_claim_events` so a bare word that
    is a tracked filename at the repo root (#19435) is accepted as a valid
    glob. Without `tracked` (e.g. --from-json offline mode), the legacy
    fail-CLOSED behaviour holds: bare words remain residue.
    """
    events = [
        ev
        for c in payload.get("comments", [])
        for ev in _parse_claim_events(c, tracked=tracked)
    ]
    # Server createdAt, ISO 8601 UTC -> lexicographic order == chronological.
    events.sort(key=lambda e: e.created_at or "")
    return events

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
        # T4 (module pur) : aucun fetch ici -- la lecture groupee appartient a
        # l'appelant. Oubli d'injection => fail-CLOSED (#13336) : le temoin
        # pr_state_error est pose et l'evenement reste "open" -- un appelant
        # qui n'injecte pas ne libere pas le verrou d'une lane.
        st, err = None, "claim_grammar: pr_states non injecte (module pur, T4)"

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


@lru_cache(maxsize=8192)
def _compiled_path_pattern(pattern: str) -> re.Pattern[str]:
    """fnmatch regex for one raw pattern under the current platform rules."""
    from fnmatch import translate
    return re.compile(translate(os.path.normcase(pattern)))


@lru_cache(maxsize=65536)
def _normcase_path(path: str) -> str:
    return os.path.normcase(path)


@lru_cache(maxsize=262144)
def _path_matches_pair(path: str, pattern: str) -> bool:
    """Match one immutable (path, pattern) pair, memoized above.

    The glob is compiled to a regex by ``_compiled_path_pattern`` and matched
    with ``re.match`` against the ``os.path.normcase``-normalized FULL path
    AND against the normalized BASENAME, so ``*.lean`` matches both
    ``knot_lean/Foo.lean`` and a bare ``Foo.lean``. The verdict is a pure
    function of its two immutable ``str`` arguments, so the (bounded,
    ``maxsize=262144``) memo can never change it; the compiled-regex and
    normcase helpers are cached separately. Windows normcase and separator
    behavior are retained.
    """
    basename = path.rsplit("/", 1)[-1]
    regex = _compiled_path_pattern(pattern)
    return (regex.match(_normcase_path(path)) is not None
            or regex.match(_normcase_path(basename)) is not None)


@lru_cache(maxsize=8192)
def _expanded_path_pattern(pattern: str) -> tuple[str, ...]:
    """Brace expansion for one immutable caller pattern."""
    return tuple(_expand_brace_groups(pattern))


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
    return _path_matches_cached(path, tuple(patterns))


@lru_cache(maxsize=262144)
def _path_matches_cached(path: str, patterns: tuple[str, ...]) -> bool:
    """#24824 -- memoise le verdict par (chemin, motifs) : les deux sont
    invariants d'une issue a l'autre dans le batch, seule la liste suivie
    change (memoisee par racine). Fonction pure de ses deux arguments, donc
    la memoisation ne peut changer aucun verdict."""
    for pat in patterns:
        for p in _expanded_path_pattern(pat):
            if _path_matches_pair(path, p):
                return True
    return False


# #24824 -- memoise le croisement par (motifs, identite + generation de la
# liste suivie). La liste est l'objet _TrackedFiles memoise par racine dans
# _TRACKED_FILES_MEMO (jamais mute en place en production). La cle porte la
# generation _gen, que _TrackedFiles._invalidate() incrémente a chaque
# mutation : un resultat ne peut donc jamais etre servi stale contre une
# liste mutee (contrat test 3031/3040). On garde une reference FORTe vers la
# liste dans la valeur : son id() n'est pas reutilise tant que l'entree vit.
# Seules les listes _TrackedFiles sont memoisees ; une liste brute (mutable)
# ne l'est pas. Le bornage efface (re-calcule) : jamais un verdict faux.
_MATCHING_INDICES_MEMO: dict[tuple, tuple[object, frozenset[int]]] = {}

# #25913 (reponse a la reserve Hermes #4) -- double borne : en NOMBRE d'entrees
# (MAX) et en VOLUME (MAX_INDICES, somme des indices sur tous les frozensets).
# La borne en nombre seule laissait 1024 entrees pleines (chacune jusqu'a la
# liste suivie entiere, ~16k indices) tenir en memoire (~44 Mo de frozensets
# mesurés) ; la borne en indices cumulés plafonne le volume. _SIZE est le
# compteur correspondant, réinitialisé a chaque clear.
_MATCHING_INDICES_MEMO_MAX = 1024

_MATCHING_INDICES_MEMO_MAX_INDICES = 131072  # ~8 listes suivies completes

_MATCHING_INDICES_MEMO_SIZE = 0


def _matching_indices_store(
    key: tuple, tracked: object, indices: frozenset[int]
) -> None:
    """Insère dans ``_MATCHING_INDICES_MEMO`` sous double borne.

    #25913 (reponse a la reserve Hermes #4) : au-dela de la borne en nombre
    d'entrees, la borne en indices cumulés plafonne le volume de frozensets.
    A la limite, la memo entiere est effacée ; c'est une cache pure, l'effacement
    force un re-calcul mais ne change aucun verdict.
    """
    global _MATCHING_INDICES_MEMO_SIZE
    if (len(_MATCHING_INDICES_MEMO) >= _MATCHING_INDICES_MEMO_MAX
            or _MATCHING_INDICES_MEMO_SIZE + len(indices)
            > _MATCHING_INDICES_MEMO_MAX_INDICES):
        _MATCHING_INDICES_MEMO.clear()
        _MATCHING_INDICES_MEMO_SIZE = 0
    _MATCHING_INDICES_MEMO[key] = (tracked, indices)
    _MATCHING_INDICES_MEMO_SIZE += len(indices)


def _matching_tracked_indices(
    patterns: list[str], tracked: list[str]
) -> set[int]:
    """Indices des chemins suivis qui correspondent aux motifs.

    Cette forme en lot est utilisee par `_scopes_intersect`: les motifs
    sont developpes/normalises/compiles une fois par scope, puis chaque
    chemin est normalise une seule fois (par `_TrackedFiles`) et teste
    contre ces regex. La separation du basename se fait toujours sur le
    chemin brut, avant `normcase`, comme dans `fnmatch(path, pattern)` sous
    Windows.

    #24824 -- memoise par (motifs, identite de la liste suivie) : dans le
    batch, les memes perimetres sont recroises a chaque issue sur la meme
    liste suivie. La reference forte vers `tracked` rend l'`id()` stable,
    donc la memoisation ne change aucun verdict (fonction pure).
    """
    # #24824 -- la memo ne porte que sur les listes _TrackedFiles ; la cle
    # porte leur generation _gen, donc toute mutation force le re-calcule
    # (jamais un verdict stale). Une liste brute n'est pas memoisee.
    is_tf = isinstance(tracked, _TrackedFiles)
    if is_tf:
        key = (tuple(patterns), id(tracked), tracked._gen)
        hit = _MATCHING_INDICES_MEMO.get(key)
        if hit is not None:
            return set(hit[1])
    expanded = [p for pattern in patterns
                for p in _expanded_path_pattern(pattern)]
    regexes = [_compiled_path_pattern(p) for p in expanded]
    if not regexes:
        if is_tf:
            _matching_indices_store(key, tracked, frozenset())
        return set()
    pairs = _norm_pairs(tracked)
    result = {
        index for index, (path, basename) in enumerate(pairs)
        if any(rx.match(path) or rx.match(basename) for rx in regexes)
    }
    if is_tf:
        _matching_indices_store(key, tracked, frozenset(result))
    return result


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


class _TrackedFiles(list):
    """Liste des fichiers suivis, avec ses formes normalisees en cache.

    #22983 -- `normcase` etait appele deux fois par chemin compare, et le
    chemin etait compare a chaque glob : ~5,2 M appels pour 40 numeros.
    Les formes normalisees sont calculees ici, UNE FOIS par liste.
    """

    __slots__ = ("_norm", "_exact", "_bases", "_gen")

    def __init__(self, items):
        super().__init__(items)
        self._norm = None
        self._exact = None
        self._bases = None
        self._gen = 0

    def _invalidate(self):
        self._norm = self._exact = self._bases = None
        # #24824 -- toute mutation change la generation : la memo de
        # _matching_tracked_indices (clee sur _gen) ne sert donc jamais un
        # resultat stale contre une liste mutee (contrat test 3031/3040).
        self._gen += 1

    def __setitem__(self, key, value):
        super().__setitem__(key, value)
        self._invalidate()

    def __delitem__(self, key):
        super().__delitem__(key)
        self._invalidate()

    def append(self, item):
        super().append(item)
        self._invalidate()

    def extend(self, items):
        # An iterator can fail after partially extending the list.
        try:
            super().extend(items)
        finally:
            self._invalidate()

    def insert(self, index, item):
        super().insert(index, item)
        self._invalidate()

    def pop(self, index=-1):
        item = super().pop(index)
        self._invalidate()
        return item

    def remove(self, item):
        super().remove(item)
        self._invalidate()

    def clear(self):
        super().clear()
        self._invalidate()

    def reverse(self):
        super().reverse()
        self._invalidate()

    def sort(self, *args, **kwargs):
        try:
            super().sort(*args, **kwargs)
        finally:
            self._invalidate()

    def __iadd__(self, items):
        self.extend(items)
        return self

    def __imul__(self, count):
        super().__imul__(count)
        self._invalidate()
        return self

    @property
    def norm_pairs(self) -> list[tuple[str, str]]:
        """Paires (chemin normalise, nom de base normalise)."""
        if self._norm is None:
            self._norm = [
                (os.path.normcase(p), os.path.normcase(p.rsplit("/", 1)[-1]))
                for p in self
            ]
        return self._norm

    @property
    def exact_paths(self) -> set[str]:
        """Chemins normalises, pour la resolution O(1) des motifs litteraux."""
        if self._exact is None:
            self._exact = {npath for npath, _ in self.norm_pairs}
        return self._exact

    @property
    def exact_bases(self) -> set[str]:
        """Noms de base normalises, pour la resolution O(1) des litteraux."""
        if self._bases is None:
            self._bases = {nbase for _, nbase in self.norm_pairs}
        return self._bases


# #22983 -- memo de processus de la liste des fichiers suivis, par racine.
# Le batch de claims demande la liste pour CHAQUE issue ; sans memo, le
# `git ls-files` (~15 172 chemins) est relance par issue. Mesure du
# 2026-11-05 (profil sur `_run_check`) : apres l'optimisation du matching
# de globs, la lecture de la sortie des sous-processus representait 84 %
# du temps restant du check.
#
# Seuls les SUCCES sont memoisees : un echec (liste `None`) reste
# re-tente au check suivant et reste fail-CLOSED a chaque appel.
_TRACKED_FILES_MEMO: dict[str, list[str]] = {}


def _git_tracked_files(repo_root: str | None = None) -> list[str] | None:
    """Best-effort `git ls-files` under repo_root (cwd default). None on failure.

    Mirrors the walk of `_scope_zero_coverage_warning` -- the one source of
    "which files does the repo track" for both callers.

    #22983 -- le resultat reussi est memoise par racine de depot (le batch
    de claims relancait `git ls-files` sur les memes ~15 172 chemins pour
    chaque issue).
    """
    if repo_root is None:
        repo_root = os.getcwd()
    memo = _TRACKED_FILES_MEMO.get(repo_root)
    if memo is not None:
        return memo
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
    # #22983 -- les formes normalisees (chemin + nom de base) sont
    # attachees a la liste : elles ne dependent que de la liste, et la
    # liste est deja memoisee par racine. Le matching de globs les
    # reutilise au lieu de normaliser chaque chemin a chaque glob.
    tracked = _TrackedFiles(tracked)
    _TRACKED_FILES_MEMO[repo_root] = tracked
    return tracked


# #22983 -- les caracteres qui rendent un motif non litteral pour `fnmatch`
# (`*`, `?`, `[...]`). `{`/`}` sont exclus : les groupes d'accolades sont
# deployes par `_expand_brace_groups` AVANT ce test, donc un motif porte
# de `{` a ce stade est deja deploye en litteraux.
_GLOB_META = re.compile(r"[*?\[]")


def _norm_pairs(tracked) -> list[tuple[str, str]]:
    """Paires (chemin normalise, nom de base normalise) de la liste donnee."""
    if isinstance(tracked, _TrackedFiles):
        return tracked.norm_pairs
    return [(os.path.normcase(p), os.path.normcase(p.rsplit("/", 1)[-1]))
            for p in tracked]


# #24824 -- memo par (charge, identite + generation de la liste suivie) pour
# les fonctions pures de (charge, tracked). `tracked` est l'objet
# _TrackedFiles memoise par racine (_TRACKED_FILES_MEMO), jamais mute en
# place en production ; la cle porte _gen, que _TrackedFiles._invalidate()
# incremente a chaque mutation, donc un resultat ne peut jamais etre servi
# stale contre une liste mutee (contrat test 3031/3040). Reference FORTe vers
# la liste dans la valeur : son id() n'est pas reutilise tant que l'entree
# vit. Une liste brute (mutable) n'est jamais memoisee ; le bornage efface
# (re-calcule). Jamais un verdict faux.
_MISS = object()


class _TrackedScopedMemo:
    """Memo bornee des fonctions pures de (charge, liste suivie)."""

    __slots__ = ("_d", "_max")

    def __init__(self, maxsize: int) -> None:
        self._d: dict = {}
        self._max = maxsize

    def get(self, payload, tracked):
        if isinstance(tracked, _TrackedFiles):
            hit = self._d.get((payload, id(tracked), tracked._gen), _MISS)
            if hit is not _MISS:
                return hit[1]
        return _MISS

    def put(self, payload, tracked, value) -> None:
        if not isinstance(tracked, _TrackedFiles):
            return
        if len(self._d) >= self._max:
            self._d.clear()
        self._d[(payload, id(tracked), tracked._gen)] = (tracked, value)


_GLOB_TRACKED_MEMO = _TrackedScopedMemo(16384)

_CORRECTION_MEMO = _TrackedScopedMemo(16384)


def _glob_matches_tracked(glob: str, tracked: list[str]) -> bool:
    """True when at least one tracked file matches the glob (fnmatch, basename-or-full).

    #22983 -- le motif est compile UNE FOIS par glob, et non une fois par
    chemin compare. Mesure du 2026-11-05 (profil sur `_run_check`) : le
    check d'un issue coutait 0,94 s, dont 87 % dans ce matching --
    731 448 `normcase` et 365 352 `translate` pour trois checks, parce que
    `fnmatch.fnmatch` normalise et retranscrit le motif a chaque chemin.
    La correction compile le motif une fois et normalise le chemin une
    fois.

    **La semantique est inchangee** : `fnmatch.fnmatch(n, p)` vaut
    exactement `re.match(translate(normcase(p)), normcase(n))`, et le nom
    de base reste calcule sur le chemin BRUT separe par `/` -- le separer
    apres `normcase` serait faux sous Windows, ou `normcase` transforme
    les separateurs de chemin en antislash et le nom de base ne serait
    plus extrait.
    """
    cached = _GLOB_TRACKED_MEMO.get(glob, tracked)
    if cached is not _MISS:
        return cached
    result = _glob_matches_tracked_uncached(glob, tracked)
    _GLOB_TRACKED_MEMO.put(glob, tracked, result)
    return result


def _glob_matches_tracked_uncached(glob: str, tracked: list[str]) -> bool:
    """Corps de `_glob_matches_tracked`, sans memo (balayage par glob)."""
    from fnmatch import translate
    patterns = _expand_brace_groups(glob)
    if not patterns:
        return False

    # #22983 -- motif LITTERAL (aucun caractere special de `fnmatch`) :
    # resolution par table de hachage, sans balayer les chemins. Un
    # litteral n'a pas de caractere special, donc `fnmatch` le traite
    # comme une comparaison d'egalite -- sur le chemin complet OU sur le
    # nom de base, comme le matching general.
    if all(not _GLOB_META.search(p) for p in patterns):
        norm = [os.path.normcase(p) for p in patterns]
        if isinstance(tracked, _TrackedFiles):
            if any(p in tracked.exact_paths for p in norm):
                return True
            return any(p in tracked.exact_bases for p in norm)
        for path in tracked:
            npath = os.path.normcase(path)
            nbase = os.path.normcase(path.rsplit("/", 1)[-1])
            if npath in norm or nbase in norm:
                return True
        return False

    regexes = []
    for pat in patterns:
        regexes.append(re.compile(translate(os.path.normcase(pat))))
    for npath, nbase in _norm_pairs(tracked):
        for rx in regexes:
            if rx.match(npath) or rx.match(nbase):
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
    cached = _CORRECTION_MEMO.get(glob, tracked)
    if cached is not _MISS:
        return cached
    result = _suggest_path_correction_uncached(glob, tracked)
    _CORRECTION_MEMO.put(glob, tracked, result)
    return result


def _suggest_path_correction_uncached(glob: str, tracked: list[str]) -> str | None:
    """Corps de `_suggest_path_correction`, sans memo (balayage des chemins)."""
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

    #28669 (scoped liveness): the SCOPED branch below used to WARN on every
    dead glob of every open/override marker, including markers their lane has
    since superseded or released -- 90 of the 99 dead globs on the recorded
    batch (`scripts/tests/fixtures/claim_grammar/batch.json`, 14 issues) were
    carried by a marker that no longer holds anything. When `active_claims`
    is provided, a dead glob WARNs only when the marker IS its lane's active
    claim; the others are counted and restated as ONE `INFO:` line at the end
    of the function (observability: the organ says what it withheld). Without
    `active_claims` the branch is unchanged, exactly like #12327's fallback.
    A marker with no lane token cannot be proven inactive and keeps its WARN.
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
    # #28669 -- compteur des globs morts ETENDUS (marqueur non actif). Une
    # bride silencieuse doit se dire : l'organe nomme en une ligne ce qu'il
    # n'a pas signale, sinon la qualification ressemble a une reparation du
    # defaut qu'elle masque.
    silenced_dead_globs: dict[str, int] = {}
    silenced_superseded = 0
    silenced_released = 0
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
        # #28669 -- la branche SCOPEE n'avait aucune qualification de
        # vivacite : tout evenement open/override portant un glob mort
        # produisait son WARN, y compris un marqueur que sa lane a depuis
        # superseded ou libere. Le WARN ne parle que sur le claim ACTIF de sa
        # lane -- le seul cas ou l'auteur peut encore corriger sa clause, et
        # le seul ou le glob mort decrit un perimetre courant. Mesure sur le
        # lot enregistre (14 issues) : 90 des 99 globs morts portaient un
        # marqueur non actif. Sans `active_claims` (appelant qui n'a pas
        # reduit), la branche garde son comportement d'origine, comme la
        # branche epic-wide de #12327. Un marqueur SANS lane ne peut pas etre
        # prouve non actif : il garde son WARN.
        ev_lane = ev.lane or "?"
        ev_active = (active_claims.get(ev.lane)
                     if (active_claims is not None and ev.lane) else None)
        marker_is_live = (active_claims is None or ev.lane is None
                          or ev_active is ev)
        # #26657 -- les resolutions de scope de l'evenement (calculees par
        # l'appelant), indexees par glob mort.
        resolved_map = {note["glob"]: note
                        for note in (ev.get("scope_resolution") or [])}
        for g in ev.paths:
            if _glob_implausible(g):
                print(
                    f'WARN: glob suspect (prose avalée ?) : "{g}" '
                    f"(lane {ev.lane or '?'})",
                    file=sys.stderr,
                )
            # #26657 -- un glob RESOLU (PR ouverte, renommage, basename
            # unique) n'est pas un glob sans correspondance : le scope est
            # vivant, et le WARN desornerait une lane dont le perimetre est
            # correct. On le dit, on nomme la resolution.
            resolution = resolved_map.get(g)
            if resolution is not None:
                print(
                    f'INFO: glob resolu : "{g}" -> '
                    f'{", ".join(resolution["resolved_to"])} '
                    f'(lane {ev.lane or "?"}, {resolution["how"]}) -- '
                    f"l'organe resout ce perimetre ; le WARN porte sur le "
                    f"glob DECLARE, qui ne matche toujours rien (#26657).",
                    file=sys.stderr,
                )
            if tracked is not None and not _glob_matches_tracked(g, tracked):
                if not marker_is_live:
                    # #28669 -- marqueur superseded ou libere : le glob mort
                    # ne decrit plus aucun perimetre courant. On compte pour
                    # le dire en une ligne a la fin, on ne WARN pas.
                    silenced_dead_globs[ev_lane] = (
                        silenced_dead_globs.get(ev_lane, 0) + 1)
                    if ev_active is None:
                        silenced_released += 1
                    else:
                        silenced_superseded += 1
                    continue
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
    # #28669 -- restitution de la bride. Le WARN ne parle plus sur un
    # marqueur non actif, mais l'organe ne se tait pas : il dit combien de
    # globs morts il a etendus, sur quelles lanes, et pourquoi. Un lecteur
    # qui voit disparaitre 90 WARN doit pouvoir verifier que rien n'est
    # cache ; un marqueur superseded reste une dette d'hygiene
    # (`[RELEASED]` l'ancien), pas une alerte de perimetre.
    if silenced_dead_globs:
        total_silenced = sum(silenced_dead_globs.values())
        detail = ", ".join(
            f"{lane}: {n}" for lane, n in sorted(silenced_dead_globs.items())
        )
        print(
            f"INFO: {total_silenced} glob(s) mort(s) porte(s) par des "
            f"marqueurs NON ACTIFS, non signale(s) "
            f"({silenced_superseded} superseded, {silenced_released} sans "
            f"claim actif) -- le WARN ne parle que sur le claim actif de sa "
            f"lane (#28669). Par lane : {detail}.",
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
      - #21431: a scope that is entirely dead BUT is a CREATION scope (the
        files it names do not exist yet, in a directory that DOES exist) is
        not broken -- it is a tranche in progress. The tracked tree cannot
        decide a disjointness question about a file it does not contain,
        so the two scopes are compared BY PATTERN. The same relaxation
        applies to the caller's own scope (an entirely-dead creation scope
        no longer keeps every other lane) and to the other lane's scope (a
        creation scope is not lifted to epic-wide). A scope whose directory
        does not exist stays a typo and keeps the #10958 fail-CLOSED.

    The reducer `compute_active_claims` is untouched; this filter only prunes
    the `others` view. The active_claims summary keeps the full state, so the
    JSON output remains auditable.
    """
    mine_paths = ((mine.get("live_paths") or mine.get("paths"))
                  if mine else None) or []
    my_scope = list(dict.fromkeys((my_paths or []) + mine_paths)) or None
    if not my_scope:
        return others  # no declared scope -> cannot prove disjointness
    # #10958 fail-safe, caller side: an entirely-dead MY scope proves nothing
    # either. Dropping an other-lane claim as "disjoint" from globs that lock
    # no real file would be the same fail-open with the roles swapped, so the
    # caller keeps every other lane until its own scope is reissued clean.
    # #21431 -- UNLESS the scope is a CREATION scope: the files it names do
    # not exist yet (a new detector, a new notebook) and the tracked tree is
    # blind to them. There the disjointness IS provable -- by comparing the
    # patterns, which is what `_scopes_intersect` does for a creation scope.
    # A scope whose directory does not exist is a typo, not a creation: it
    # keeps the fail-CLOSED.
    if tracked is not None and _empty_scope_in(my_scope, tracked) == my_scope:
        if not _scope_is_creation(my_scope, tracked):
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
        # #26657 -- le scope VIVANT de la lane est son scope RESOLU : c'est
        # lui que la claim verrouille, et c'est lui que l'intersection
        # mesure. Le temoin `empty_scope` a ete calcule sur cette meme
        # liste, donc la comparaison se fait sur elle.
        live = ev.get("live_paths") or scope
        if empty and len(empty) >= len(live):
            # #10958 fail-safe -- an ENTIRELY dead scope (every glob matches
            # zero tracked files) is a broken claim, not a permissive one:
            # lifted to epic-wide before the disjointness test, mirroring
            # #10597. The witness is `ev.get("empty_scope")` (attached by
            # `_run_check` when the walk succeeded); a missing/empty witness
            # never lifts.
            # #21431 -- a CREATION scope is not a broken claim: the files it
            # names will exist. It is compared BY PATTERN with the caller's
            # scope, like any other scoped claim. A scope whose directory
            # does not exist keeps the lift (a typo, not a creation).
            if not _scope_is_creation(live, tracked):
                filtered[ln] = ev  # lifted to epic-wide -- always blocking
                continue
        if _scopes_intersect(my_scope, live, tracked):
            filtered[ln] = ev  # scopes intersect -> real collision
        # else: both scoped, disjoint -> free, drop from others
    return filtered


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


def _tracked_dirs(tracked: list[str] | None) -> set[str]:
    """The set of directories that hold at least one tracked file.

    Derived from the same walk `_empty_scope_in` uses -- no second `git`
    call. The ancestors of every tracked path are the directories that
    exist on disk.
    """
    dirs: set[str] = set()
    for path in tracked or []:
        parts = path.split("/")
        for i in range(1, len(parts)):
            dirs.add("/".join(parts[:i]))
    return dirs


def _glob_parent_dir(glob: str) -> str:
    """The literal parent directory of a glob.

    The literal prefix of the glob (up to the first fnmatch meta) is the
    part of the path that is certain; its directory is the directory the
    glob lives in. A glob with no directory (`newfile.py`) lives at the
    repository root, whose parent is the empty string (always existing).
    """
    prefix = _literal_prefix(glob)
    if "/" not in prefix:
        return ""
    return prefix.rsplit("/", 1)[0]


def _glob_carries_prose(glob: str) -> bool:
    """True when a scope element carries PROSE instead of a path pattern.

    #27162 -- the claim grammar splits the `paths:` clause on its annotation
    separators (` -- `, ` — `, ` (...)`). A glob that STILL carries whitespace
    after that split is a FRAGMENT of a mis-split clause, not a path: the
    measured case is a coordinator claim that glued its rationale to the glob
    (`MyIA.AI.Notebooks/Sudoku/** ; claim pose au dispatch par le
    coordinateur`).

    Such a scope matches zero tracked file. The #21431 creation relaxation
    then read it as "a file to be created in an existing directory" -- the
    parent directory of the polluted glob DOES exist, so the tracked tree
    could not decide the disjointness question, the scope was compared BY
    PATTERN, the pattern missed the caller's path, and the lane was dropped
    from the blockers: a fail-open (measured case #27139).

    The creation relaxation therefore REFUSES a scope that carries prose: a
    creation scope names a path, and a path with a rationale glued to it is a
    broken claim -- which keeps the #10958 epic-wide lift (fail-CLOSED).
    """
    return any(ch.isspace() for ch in glob) or ";" in glob


def _scope_is_creation(scope: list[str] | None,
                       tracked: list[str] | None) -> bool:
    """True when every glob of `scope` names a file to be CREATED.

    #21431 -- a scope whose files do not exist YET is not a broken claim
    (the #10958 fail-safe reading): it is the normal state of a creation
    tranche (a new detector, a new notebook). The tracked tree cannot
    decide a disjointness question about a file it does not contain -- it
    would read "disjoint" for every creation scope -- so the two scopes
    are compared BY PATTERN instead (`_scopes_may_overlap_by_pattern`).

    Three conditions per glob, all required:
      (a) it matches ZERO tracked file -- it does not exist yet;
      (b) it is syntactically valid (`_unparseable_scope_in` says nothing)
          -- a prose residue is a typo, not a path;
      (c) its literal parent directory EXISTS in the tracked tree -- the
          file is a new file in a real directory. A path whose directory
          does not exist (`scripts/nowhere/typo.py`) is a typo: the
          #10958 fail-CLOSED stays, because the lane that wrote it meant
          something else. This is the discriminator the issue leaves to
          the implementation, and it is the one that keeps every existing
          fail-safe test green.
      (d) it does not carry PROSE (#27162) -- a glob with a rationale glued
          to it is a broken claim, not a file to be created. Without this
          condition the polluted glob of the measured case reads as a
          creation scope (its parent directory exists), is compared BY
          PATTERN, misses the caller's path and is dropped: the fail-open
          of #27139.
    """
    if not scope or tracked is None:
        return False
    dirs = _tracked_dirs(tracked)
    for glob in scope:
        if _glob_matches_tracked(glob, tracked):
            return False          # (a) the file already exists
        if _unparseable_scope_in([glob], tracked):
            return False          # (b) prose residue -- a typo
        if _glob_carries_prose(glob):
            return False          # (d) prose glued to the glob -- a typo
        parent = _glob_parent_dir(glob)
        if parent and parent not in dirs:
            return False          # (c) the directory does not exist -- a typo
    return True


def _scopes_may_overlap_by_pattern(a: list[str], b: list[str]) -> bool:
    """True if two path scopes MAY cover a common file, compared BY PATTERN.

    #21431 -- the pattern-wise reading of a scope: a glob is a glob, and
    two scopes overlap when one of them can match a string the other can
    also match. The concrete members of each side are matched against the
    other side's globs -- fnmatch in BOTH directions, because the loop
    walks both sides: the concrete path against the other side's glob,
    and (on the other turn) the other side's concrete path against this
    side's glob. The remaining glob-vs-glob pairs are decided by the
    conservative literal-prefix test of `_glob_overlap`, which over-blocks
    when unsure (the safe direction for a collision guard).

    This is the test the tracked walk cannot make for a creation scope: a
    file that does not exist yet is matched by no tracked file, so the
    walk would read "disjoint" for a scope whose whole point is to create
    that file.
    """
    if not a or not b:
        return False
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

    #21431 -- the walk is exact for the scopes that live on disk, but BLIND
    to a creation scope: a file that does not exist yet is matched by no
    tracked file, so the walk reads "disjoint" for a scope whose whole point
    is to create that file. When either side is a creation scope, the two
    scopes are compared BY PATTERN instead -- the same proof, on the
    patterns rather than on the tree.
    """
    if not a or not b:
        return False
    if tracked is not None:
        if (_matching_tracked_indices(a, tracked)
                & _matching_tracked_indices(b, tracked)):
            return True
        if _scope_is_creation(a, tracked) or _scope_is_creation(b, tracked):
            return _scopes_may_overlap_by_pattern(a, b)
        return False
    # no repo walk: concrete members of each side, matched against the other
    return _scopes_may_overlap_by_pattern(a, b)

