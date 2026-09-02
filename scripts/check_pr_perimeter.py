#!/usr/bin/env python3
"""check_pr_perimeter.py -- perimeter truth-source for PR reviews (#11268).

Why this exists
---------------
On PR #11227 (merged ``4f5354f25``) the Hermes review asserted:

    « Périmètre : 2 fichiers twins uniquement, aucune autre modification. »

The effective file list (``gh pr view 11227 --json files``) had **3** files,
one of them ``.github/workflows/lean-knot.yml`` moving ``sorry-baseline:
"16" -> "14"``. The change itself was good (it ratchets a reduction down),
but the *class* of defect is not: a reviewer who certifies "nothing else"
without reading the file list would let the same review pass over a
**loosened** baseline -- and a loosened gate never goes red, that is its
entire effect. A perimeter assertion not derived from the effective file
list is a null instrument: "nothing else found" and "did not look" render
the same sentence.

What it does (issue #11268 acceptance 1-3)
------------------------------------------
1. Enumerates the effective file list of a PR (``gh pr view --json files``).
2. Names every ``.github/workflows/**`` file in a dedicated section -- that
   surface changes what CI applies to every subsequent PR, so it is always
   called out, even when the change is benign.
3. Detects baseline / threshold / ratchet moves in the diff and reports
   their direction. ``sorry-baseline`` (lower = tighter) and
   ``DENSITY_THRESHOLD`` (higher = tighter) get an automatic verdict;
   other numeric keys matching the generic pattern are reported with
   ``DIRECTION-A-QUALIFIER`` for the reviewer to judge. A removal of a
   baseline line counts as LOOSEN (gate gone), an addition as TIGHTEN.
4. ``--assert "<review sentence>"`` confronts a draft perimeter assertion
   with the effective list: a claimed file count that mismatches, or an
   exclusivity claim ("uniquement", "only", ...) that does not name a
   touched workflow, FAILS (exit 1). This is the non-regression property:
   a review claiming "2 files only" over a 3-file PR with a workflow can
   no longer be produced unnoticed.
5. ``--scan-thread`` (the wiring into the review path, acceptance 4): fetches
   the PR body + top-level reviews and confronts EVERY perimeter assertion
   found there with the effective list. Wired by
   ``.github/workflows/perimeter-review-guard.yml`` on ``pull_request`` +
   ``pull_request_review`` -- the moment such a review is submitted or
   edited, the check re-runs on the same head and goes red on a false
   assertion, so the PR cannot stand merged with one. Baseline moves are
   reported with direction but do not block in this mode (the reviewer
   applies #11268-3 on unjustified loosening; the output names the move).
6. (#13637) The API's file list is base-tip -> head, so a branch that merged
   ``main`` gets ``main``'s own changes attributed to it (measured on #13601:
   04-7 showed ``+2708/-2708`` although the PR did not touch it). Files the
   head already agrees with main on are subtracted from the effective list
   and reported separately ("dont M charriés d'une base vieille de X") --
   the perimeter is the PR's OWN contribution. ``is_pr_own_file`` exposes the
   predicate for the collision checks that re-implement it by hand.

Exit codes
----------
0 = perimeter reported, assertion (if any) consistent, no unjustified
    loosening detected.
1 = assertion mismatch, unnamed workflow under an exclusivity claim, or a
   LOOSEN move without ``--baseline-justified`` (the reviewer must either
   write the justification in the PR or post CHANGES_REQUESTED).
2 = gh/API error (missing PR, network...). Never silently pass: a perimeter
   check that succeeds when it could not look is the original defect again.

Usage
-----
    python scripts/check_pr_perimeter.py 11334
    python scripts/check_pr_perimeter.py 11227 --assert "2 fichiers twins uniquement"
    python scripts/check_pr_perimeter.py <PR#> --scan-thread
    python scripts/check_pr_perimeter.py <PR#> --baseline-justified "accepted debt, see #N"

The pure core (assertion checking, baseline parsing, perimeter extraction) is
unit-tested without network in ``scripts/tests/test_check_pr_perimeter.py``;
the gh wiring is exercised on real PRs (see the PR that introduced this file).
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
import unicodedata
from dataclasses import dataclass, field
from typing import Optional

WORKFLOW_PREFIX = ".github/workflows/"

# Keys whose direction is known by construction. value: "lower" means a lower
# number is tighter (sorry-baseline: accepting MORE sorries = looser);
# "higher" means a higher number is tighter (a density floor).
KNOWN_BASELINE_KEYS: dict[str, str] = {
    "sorry-baseline": "lower",
    "DENSITY_THRESHOLD": "higher",
}

# Generic safety net: any other line that looks like a tunable gate knob and
# carries a number is reported for the reviewer to qualify by hand. NB: no
# leading \b on the alternatives — `_cap` sits mid-word (`parallel_cap:`) and
# `_` is itself a word char, so a leading boundary can never match there.
GENERIC_KNOB = re.compile(r"(?i)(baseline|threshold|ratchet|_cap\b|\bcap\b)")

# Assertion vocabulary: file-count claims and exclusivity markers.
COUNT_CLAIM = re.compile(r"\b(\d+)\s*(?:fichiers?|files?)\b", re.IGNORECASE)
# #13440: the boundary `\b` stops the match at "fichier" when the body writes
# the plural parenthetically ("25 fichier(s) verifies") -- without skipping
# the "(s)" hump, every downstream tail window (incidental qualifier,
# negated-diff tail, reference verb) is blind on this form.
PLURAL_PAREN = re.compile(r"^\s*\(s\)\s*")
# #11985 rule 1 extension (CLOSED LIST -- never expand to unknown vocabulary):
# a body can declare its perimeter in words ("trois fichiers", "five files").
# The authorial declaration is the same shape; we just spell-check the
# spelled-out number too. French and English cardinals 1-10. Beyond that
# range we fail loud (false-negative default -- the next body with "onze
# fichiers" / "eleven files" will be caught by a reviewer and the mapping
# expanded). Closed list = false-negative cost is bounded and visible.
#
# #13535 accord de langue : le cardinal et le nom doivent concorder. Le
# singulier anglais "file" est aussi un mot francais courant (« file
# d'attente ») : sans accord, un corps francais qui parle d'une file de CI
# produisait le bigramme « une file », lu comme <cardinal> <noun> = 1 fichier,
# et le garde bloquant sur-accusait une phrase sans rapport (#13499 : « le
# meme verdict sur une file qui avance et sur une file figee » -> FAIL
# pretendu 1 fichier, liste effective 2). Croisement FR-cardinal + EN-nom
# n'a aucune forme legitime : on exige la meme langue des deux cotes. Le
# chiffre (COUNT_CLAIM) reste langue-neutre. Residu assume : « six » est
# cardinal des deux langues, donc « six files d'attente » (FR) matche quand
# meme la lecture EN -- borne par la rarece de la forme.
COUNT_WORDS_FR = {
    "un": 1, "une": 1, "deux": 2, "trois": 3, "quatre": 4, "cinq": 5,
    "six": 6, "sept": 7, "huit": 8, "neuf": 9, "dix": 10,
}
COUNT_WORDS_EN = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
}
COUNT_WORDS = {**COUNT_WORDS_FR, **COUNT_WORDS_EN}
# Triggers pre-compiles : (mot, valeur, regex) -- FR cardinal + fichiers?,
# EN cardinal + files?. Les trois sites consommateurs (_word_form_count,
# extraction, body_declares_effective_count) partagent cette meme definition.
WORD_FORM_TRIGGERS = tuple(
    (word, n, re.compile(rf"\b{re.escape(word)}\s+fichiers?\b", re.IGNORECASE))
    for word, n in COUNT_WORDS_FR.items()
) + tuple(
    (word, n, re.compile(rf"\b{re.escape(word)}\s+files?\b", re.IGNORECASE))
    for word, n in COUNT_WORDS_EN.items()
)
EXCLUSIVITY_MARKERS = (
    "uniquement",
    "seulement",
    "aucune autre",
    "only",
    "nothing else",
    "no other",
)

# "only" as an exclusivity marker must be a STANDALONE word. Technical
# compounds -- "read-only", "append-only", "metadata-only" -- carry "only"
# as a compound modifier (lecture seule), not a perimeter quantifier, and a
# plain substring match trips criterion #11268-2 on prose about permissions.
# Measured on #11654: the Hermes line "Sinon LGTM sur le périmètre — aucun
# secret, permissions read-only inchangées." was flagged as an exclusivity
# assertion because "only" sat inside "read-only" while "périmètre" supplied
# the strong scope word. The French markers need no such guard: no hyphenated
# compound carries "seulement"/"uniquement".
_ONLY_STANDALONE = re.compile(r"(?<![-\w])only\b", re.IGNORECASE)
_SUBSTRING_MARKERS = ("uniquement", "seulement", "aucune autre",
                      "nothing else", "no other")


# A marker under NEGATION asserts the opposite of exclusivity. "pas seulement
# les requis" / "not only the required ones" claims UNIVERSALITY -- it widens
# the set, it does not restrict it. A plain substring match reads the marker
# and fires criterion #11268-2 on prose that says the reverse. Measured on
# #12547: the body line "Le gate attend tous les checks non-advisory, pas
# seulement les requis" -- an explicit universality claim about CI semantics,
# nothing to do with the PR perimeter -- was flagged as an exclusivity
# assertion and turned the required PR gate red. Same failure shape as the
# "read-only" compound (#11654) above: the marker is present, its force is
# not. Negators are matched as whole words immediately before the marker
# (optionally through "pas" in "non pas uniquement").
_NEGATORS = ("pas", "non", "ni", "not", "never", "jamais")
_NEG_PREFIX = re.compile(
    r"(?:" + "|".join(_NEGATORS) + r")(?:\s+(?:pas|plus))?\s+$",
    re.IGNORECASE,
)


def _marker_is_negated(low: str, start: int) -> bool:
    """True when the marker at `start` is preceded by a negator word."""
    return bool(_NEG_PREFIX.search(low[:start]))


def _has_exclusivity(low: str) -> bool:
    """Exclusivity check shared by extraction and assertion checking.

    `low` is the lowercased line. French/phrase markers are substring-matched;
    "only" requires word boundaries AND no hyphen/word char before it. A
    marker carrying a negator ("pas seulement", "not only") is skipped: it
    asserts universality, which is the opposite of a perimeter restriction.
    """
    for m in _SUBSTRING_MARKERS:
        pos = low.find(m)
        while pos != -1:
            if not _marker_is_negated(low, pos):
                return True
            pos = low.find(m, pos + 1)
    for hit in _ONLY_STANDALONE.finditer(low):
        if not _marker_is_negated(low, hit.start()):
            return True
    return False


@dataclass
class BaselineMove:
    file: str
    key: str
    old: Optional[int]
    new: Optional[int]
    direction: str  # TIGHTEN | LOOSEN | DIRECTION-A-QUALIFIER

    def render(self) -> str:
        rng = f"{self.old} -> {self.new}" if (self.old is not None and self.new is not None) else (
            f"{self.old} -> (absent)" if self.old is not None else f"(absent) -> {self.new}"
        )
        return f"  {self.file}: {self.key} = {rng}  [{self.direction}]"


@dataclass
class Report:
    files: list[dict] = field(default_factory=list)
    moves: list[BaselineMove] = field(default_factory=list)
    problems: list[str] = field(default_factory=list)
    # #13637: files the API attributes to the PR but that main itself changed
    # and the branch merged -- NOT the PR's own work. They are subtracted from
    # `files` (the effective perimeter) and named separately so a cardinal that
    # changes is explained, not silently masked.
    carried: Optional["CarriedNote"] = None


@dataclass
class CarriedNote:
    """#13637: partition of the API file list between the PR's own contribution
    and files carried from a stale main the branch merged.

    ``propres`` is what the PR actually changes; ``charries`` is what the API
    reports but the head already agrees with main on. ``base_age_hours`` is the
    age of the branch's divergence point from main (stale-base indicator, None
    when unresolvable).
    """

    propres: list[dict] = field(default_factory=list)
    charries: list[dict] = field(default_factory=list)
    base_age_hours: Optional[int] = None


def partition_propres(files: list[dict], carried_paths: set[str]) -> tuple[list[dict], list[dict]]:
    """#13637: partition ``files`` (the API list) into the PR's own contributions
    and the carried files. Pure -- ``carried_paths`` is the set of paths already
    classified by the caller (``_classify_carried``). Order-preserving: a
    rounding of the perimeter reorders nothing, so diff-reading reviewers keep
    their anchors.
    """
    propres: list[dict] = []
    charries: list[dict] = []
    for f in files:
        (charries if f.get("path") in carried_paths else propres).append(f)
    return propres, charries


def extract_baseline_moves(diff_text: str) -> list[BaselineMove]:
    """Parse a unified diff into baseline moves.

    Works per-file section (``diff --git a/X b/Y`` header), pairing removed
    and added lines that carry the same key. Kept deliberately line-based:
    baseline knobs are single-line assignments in both yml and py.
    """
    moves: list[BaselineMove] = []
    current_file = ""
    per_file: dict[str, dict[str, list[int]]] = {}

    for line in diff_text.splitlines():
        m = re.match(r'^diff --git a/(.+?) b/(.+)$', line)
        if m:
            current_file = m.group(2)
            continue
        if line.startswith(("+++", "---")) or not line.startswith(("+", "-")):
            continue
        sign = "+" if line.startswith("+") else "-"
        content = line[1:]
        for key, _direction in KNOWN_BASELINE_KEYS.items():
            km = re.search(re.escape(key) + r'[^\d]*(\d+)', content)
            if not km:
                continue
            bucket = per_file.setdefault(current_file, {}).setdefault(key, [])
            bucket.append((sign, int(km.group(1))))
        # generic knob net (unknown direction), only for lines NOT already a known key
        if not any(k in content for k in KNOWN_BASELINE_KEYS) and GENERIC_KNOB.search(content):
            gm = re.search(r'(\d+)', content)
            if gm:
                bucket = per_file.setdefault(current_file, {}).setdefault(
                    f"(generic) ligne: {content.strip()[:70]}", []
                )
                bucket.append((sign, int(gm.group(1))))

    for file, keys in per_file.items():
        for key, entries in keys.items():
            removed = [v for s, v in entries if s == "-"]
            added = [v for s, v in entries if s == "+"]
            known = key in KNOWN_BASELINE_KEYS and not key.startswith("(generic)")
            if removed and added:
                old, new = removed[0], added[0]
                if not known:
                    direction = "DIRECTION-A-QUALIFIER"
                elif KNOWN_BASELINE_KEYS[key] == "lower":
                    direction = "TIGHTEN" if new < old else ("LOOSEN" if new > old else "NO-CHANGE")
                else:
                    direction = "TIGHTEN" if new > old else ("LOOSEN" if new < old else "NO-CHANGE")
                moves.append(BaselineMove(file, key, old, new, direction))
            elif removed and not added:
                # a baseline line deleted without replacement: the gate is gone
                moves.append(BaselineMove(file, key, removed[0], None, "LOOSEN" if known else "DIRECTION-A-QUALIFIER"))
            elif added and not removed:
                moves.append(BaselineMove(file, key, None, added[0], "TIGHTEN" if known else "DIRECTION-A-QUALIFIER"))
    return moves


def _fence_mask(text: str) -> str:
    """Blank every line inside a ``` or ~~~ fence (spaces, length preserved).

    Same exemption motif as _fence_line_indices (#11670/#11675, extraction
    level): a fence is a transcription, never the author's own claim. This
    mask covers the --assert path, where a reviewer confronts a WHOLE body
    against the file list: a fenced L898 proof containing "0 fichiers en
    commun" must not be misread as the author claiming a 0-file perimeter.
    When the fence PRECEDES the prose claim, search() stops at the fenced
    zero and the coincidence that let the #11675 founder body pass
    disappears (#11695).
    """
    masked_lines: list[str] = []
    in_fence = False
    for raw in text.splitlines(keepends=True):
        stripped = raw.strip()
        newline = "\n" if raw.endswith("\n") else ""
        if in_fence:
            masked_lines.append(" " * (len(raw) - len(newline)) + newline)
            if stripped.startswith("```") or stripped.startswith("~~~"):
                in_fence = False
        elif stripped.startswith("```") or stripped.startswith("~~~"):
            masked_lines.append(" " * (len(raw) - len(newline)) + newline)
            in_fence = True
        else:
            masked_lines.append(raw)
    return "".join(masked_lines)


# #12201 self-hosting : trois masques de citation pour la selection du claim.
# Un compte situe DANS une citation (« ... » guillemets, `...` inline code)
# est du discours rapporte -- le body cite la forme qu'il repare ou celle
# d'une autre PR, il ne la revendique pas. Un compte suivi d'un intervalle
# compact de noms ("12 fichiers `70.png`-`81.png`") designe une plage
# d'artefacts rendus, jamais le format revue "N fichiers : a, b, c" (un
# perimetre ne se declare jamais par borne d'intervalle). Apparies sur la
# meme ligne : un delimiteur non ferme ne masque rien (FN par defaut).
_GUILLEMET_SPAN = re.compile(r"«[^«»\n]*»")
_INLINE_CODE_SPAN = re.compile(r"(?<!`)`[^`\n]+`(?!`)")
_RANGE_ENUM_TAIL = re.compile(r"^\s*`[^`\n]+`\s*[-–—]\s*`[^`\n]+`")
# #13946 : un compte annote `(hors scope PR)` ou `(hors scope)` /
# `(hors perimetre)` sur la meme ligne est un constat empirique pour une
# tranche ulterieure, PAS le perimetre livre par la PR courante. Pattern
# documente dans le founder #13856 (« Tranche 3 (hors scope PR) : ... (28
# fichiers constatés) ») : l'auteur marque explicitement le compte comme
# hors scope PR et le predicat COUNT_CLAIM le selectionne quand meme comme
# le perimetre. On eteint la selection pour eviter le faux positif sans
# toucher au scope "fichiers touches" -- qui est la revendication
# perimetrique reelle (cf. test_out_of_scope_annotation_does_not_mask_real_perimeter).
_OUT_OF_SCOPE_LINE = re.compile(
    r"\(\s*(?:HORS|hors)\s+scope(?:\s+PR)?\s*\)|\(\s*(?:HORS|hors)\s+perimetre\s*\)|"
    r"\bprevisionnels?\b|\btranche\s+ulterieure\b",
    re.IGNORECASE,
)
# #12201 bootstrap : le body d'une PR qui modifie le garde lui-meme est un
# corpus diagnostique -- il cite obligatoirement des comptes d'exemple, des
# controles FN et les perimetres des PRs fondatrices. La confrontation
# d'egalite y est ECARTEE (pas assouplie) : l'exclusivite et les masques
# restent actifs, seul le test d'egalite compte/fichiers est saute.
GUARD_SELF_PATHS = frozenset({"scripts/check_pr_perimeter.py"})


def _count_in_citation(line: str, m: re.Match) -> bool:
    """True when the count match `m` sits inside a same-line citation span
    (guillemets or inline code). Reported speech, not the author's claim."""
    return any(
        sp.start() <= m.start() and m.end() <= sp.end()
        for rx in (_GUILLEMET_SPAN, _INLINE_CODE_SPAN)
        for sp in rx.finditer(line)
    )


def _count_is_range_enum(line: str, m: re.Match) -> bool:
    """True when the count is immediately followed by a compact name range
    (`a.png`-`b.png`): an interval of rendered artifacts, not the review
    enumeration format (#12273 founder). The tail is clamped to the match's
    line -- the range shape is a same-line notation."""
    tail = line[m.end():]
    nl = tail.find("\n")
    return bool(_RANGE_ENUM_TAIL.match(tail if nl < 0 else tail[:nl]))


def _count_is_out_of_scope_annotation(body: str, m: re.Match) -> bool:
    """#13946 : True when the line containing the count also carries an
    explicit hors-scope annotation -- the count is a forecast for a later
    tranche, not this PR's perimeter. Founder: PR #13856 body wrote
    `Tranche 3 (hors scope PR) : ... (28 fichiers constatés, ...)`, marking
    the scope explicitly; the predictor still picked `28` as the perimeter
    and FAIL'd the PR even though the body also said `Fichiers touchés : 2`.
    Accepts the full body (not just the line) -- locate the line first, then
    pattern-match within it. Same shape as ``_count_in_citation``.
    """
    line_start = body.rfind("\n", 0, m.start()) + 1
    line_end = body.find("\n", m.end())
    if line_end < 0:
        line_end = len(body)
    line = body[line_start:line_end]
    return bool(_OUT_OF_SCOPE_LINE.search(line))


# #13946 fallback : enumeration verb « touche N » / « toucher N » /
# « touches N » (FR + EN) followed by an optional space + opening paren or
# end-of-line. Matches the FIRST occurrence; subsequent occurrences on later
# lines are irrelevant (the body has one perimeter). A faux-match on
# compound « re-touche » / « retouche » is avoided by requiring a word
# boundary before the verb.
_TOUCHE_N = re.compile(
    r"\b(?:touche|to[uû]che|toucher|touchez|touched|touches|touch)\s+(\d+)",
    re.IGNORECASE,
)


def _first_touche_n(body: str):
    """#13946 fallback : return a fake re.Match whose group(1) is the digit
    and whose start/end wrap the digit, when the body declares its
    perimeter via « touche N (...) ». Returns None when no such form
    exists. Used by ``check_assertion`` only when COUNT_CLAIM falls through
    after the hors-scope filter -- founder #13856 makes this the single
    case where the perimeter is asserted in prose, not via "N fichiers".
    """
    mm = _TOUCHE_N.search(body)
    if mm is None:
        return None
    digit_start = mm.start(1)
    digit_end = mm.end(1)

    class _DigitMatch:
        def __init__(self, s: int, e: int, n: str) -> None:
            self._s = s
            self._e = e
            self._n = n

        def group(self, idx: int = 0) -> str:
            if idx == 0:
                return self._n
            if idx == 1:
                return self._n
            raise IndexError(idx)

        def start(self, idx: int = 0) -> int:  # noqa: ARG002 -- mirror re.Match
            return self._s

        def end(self, idx: int = 0) -> int:  # noqa: ARG002 -- mirror re.Match
            return self._e

    return _DigitMatch(digit_start, digit_end, mm.group(1))


def check_assertion(
    files: list[dict], assertion: str, block: str = "", body_hint: str = ""
) -> list[str]:
    """Confront a perimeter assertion with the effective file list.

    Fence blocks (transcribed commands, L898 proof) are masked out of the
    scan (#11695). The final "non verifiable" guard therefore fires for a
    body composed only of fence transcriptions: no claim OUTSIDE fences
    means no verifiable author assertion, and such a body must not pass
    in silence.

    #12201: the claim is the first non-zero count that survives the SAME
    per-count filters as the candidates and the additive sum (exemptions,
    citations, ranges) -- selecting a count the filters exempt downstream
    confronts a number the guard itself declares non-authorial. And the
    body of a PR that modifies the guard itself is diagnostic corpus
    (bootstrap): its counts describe other PRs and the forms being fixed,
    so the equality confrontation is skipped entirely there.

    #13791: `block` is the assertion's enclosing paragraph BLOCK (prefix +
    line + contiguous lines below, see _paragraph_block). The additive
    enumeration (#12103) confronts the sum over the BLOCK when the
    single-line sum mismatches -- an enumeration spanning two bullets
    ("- 1 fichier modifie (...)" / "- 1 fichier de test modifie (...)",
    founder #13736) declares 1 + 1 = 2, and the verdict must not depend on
    where the author pressed Enter. Safe by the same #12103 construction: a
    FAIL becomes a PASS only when the block sum is exactly len(files).
    """
    problems: list[str] = []
    guard_self = any(f["path"] in GUARD_SELF_PATHS for f in files)
    # A zero count is never the perimeter. On a mixed line -- "0 fichier
    # catalogue, 2 fichiers touches" -- the claim under test is the non-zero
    # one; reading the first match confronts "0" with a file list that cannot
    # be empty, so the line could never pass whatever the PR contained. This
    # is the FINDING raised in review of #11730 (#11735): the fence mask fixed
    # WHERE we scan, this fixes WHICH count we scan for. Both are needed.
    # #12201: per-count EXEMPTIONS deliberately stay OUT of this selection
    # (#11985 rule 1: an exempt count like "1 fichier test adapte" is still
    # confronted, its mismatch downgraded at the ROUTING level). Only the
    # citation/range masks sit here -- a count inside « » or ` `, or followed
    # by a name range, is reported speech, not a claim at all.
    scan_target = _fence_mask(assertion)
    word_count = None if guard_self else _word_form_count(scan_target)
    count_claim = None
    if not guard_self:
        count_claim = next(
            (
                mm
                for mm in COUNT_CLAIM.finditer(scan_target)
                if int(mm.group(1)) != 0
                and not _count_in_citation(scan_target, mm)
                and not _count_is_range_enum(scan_target, mm)
                and not _count_is_out_of_scope_annotation(scan_target, mm)
            ),
            None,
        )
        # #13946 fallback : when no "N fichiers" form survives the
        # per-count filters (typically because the body disambiguates by
        # naming the forecast counts explicitly as hors-scope PR), look for
        # the enumeration pattern « touche N (...) » / « toucher N (...) »
        # / « touches N (...) » -- the author's positive assertion that
        # THIS PR touches N files, often followed by the file list in
        # parens. Founder #13856 body wrote « ... pas le périmètre livré
        # par cette PR qui en touche 2 (CLAUDE.md + _archive-convention.md). »
        # ; without this fallback the script reports "no count" after
        # filtering the hors-scope 28-fichiers forecast, but the body DID
        # declare its perimeter. Search order: ``block`` (the candidate's
        # enclosing paragraph -- usually sufficient), then ``body_hint``
        # (the whole PR body, used by ``--scan-thread`` when the perimeter
        # verb is in a different paragraph from the hors-scope forecast --
        # founder #13856). The verb shape is anchored enough that body-
        # wide search is safe (no overlap with the COUNT_CLAIM vocabulary).
        if count_claim is None:
            if block:
                count_claim = _first_touche_n(block)
            if count_claim is None and body_hint:
                count_claim = _first_touche_n(body_hint)
    if count_claim:
        claimed = int(count_claim.group(1))
        if claimed != len(files):
            # #12103: additive enumeration -- "1 fichier modifie, 1 fichier
            # ajoute" declares 1 + 1 = 2 files. The first non-zero count (1)
            # can never equal a 2-file PR; confront the SUM of the counts
            # that survive the per-count filters instead. Safe by
            # construction: a FAIL becomes a PASS only when the sum is
            # exactly len(files) -- never a new failure.
            # #13791: the sum spans the enclosing paragraph BLOCK when one
            # is given -- an additive enumeration lists downward as often as
            # sideways ("_additive_line_sum est line-scope, la somme additive
            # meurt au retour a la ligne", founder #13736). Per-count filters
            # stay per-LINE (each line is classified on its own surface).
            additive = _additive_line_sum(scan_target)
            if additive != len(files) and block:
                # the block already contains the candidate line -- replace,
                # never add (no double count).
                additive = sum(
                    _additive_line_sum(ln)
                    for ln in _fence_mask(block).splitlines()
                    if ln.strip()
                )
            if additive != len(files):
                problems.append(
                    f"l'assertion pretend {claimed} fichier(s), la liste effective en compte {len(files)} : "
                    + ", ".join(f["path"] for f in files)
                )
    elif word_count is not None and word_count != len(files):
        # #12092: word-form cardinal ("trois fichiers"). COUNT_WORDS exists
        # since #12024 and gates extract (the word form enters candidates)
        # but check_assertion only read COUNT_CLAIM (digits): the word line
        # reached the terminal "unverifiable" branch despite being a true
        # perimeter claim. Read the same closed list, same first-non-zero
        # rule. FR cardinals are unique 1-10 (no false twin like EN "six").
        # #13610: an indefinite-article word count whose edit-verb referent is
        # a NAMED file not in this PR is a descriptive mention of another
        # file (routing target, dependency, candidate not chosen) -- not the
        # PR's perimeter. Skip the red; the digit branch never produces this
        # shape so the guard sits here only.
        # #13791: an indefinite word-form opened by a discrimination verb
        # ("distinguer un fichier corrompu d'un fichier offensif") names the
        # objects of a comparison, not the perimeter (founder #13736 l.26).
        if _word_form_is_indef_non_pr_subject(scan_target, files):
            pass
        elif _word_form_is_measurement_object(scan_target):
            pass
        elif _word_form_is_measurement_result(scan_target, block):
            pass
        else:
            problems.append(
                f"l'assertion pretend {word_count} fichier(s), la liste effective en compte {len(files)} : "
                + ", ".join(f["path"] for f in files)
            )
    exclusive = _has_exclusivity(scan_target.lower())
    if exclusive:
        for f in files:
            if f["path"].startswith(WORKFLOW_PREFIX):
                base = f["path"].rsplit("/", 1)[-1]
                if base not in scan_target:
                    problems.append(
                        f"assertion d'exclusivite sans nommer le workflow touche {f['path']} "
                        "(critere #11268-2 : tout .github/workflows/** doit etre enumere nommement)"
                    )
    if not count_claim and word_count is None and not exclusive and not guard_self:
        problems.append(
            "assertion sans compte de fichiers ni marqueur d'exclusivite reconnaissable -- "
            "formulation non verifiable (ecrire par ex. 'N fichiers : a, b, c')"
        )
    return problems


# A file-count claim alone marks a perimeter assertion (the review template's
# ``**Fichiers:** N fichiers modifiés``). For the exclusivity-only branch, the
# line must ALSO carry a strong scope word: incidental prose like "pas
# seulement les PR" / "uniquement à la prochaine ---" / "aucune `---`
# ultérieure" (measured on #11632) must not be scanned, while a bare "Aucune
# autre modification." is a genuine perimeter assertion.
STRONG_SCOPE_WORDS = (
    "modification", "modif", "changement", "change", "périmètre",
    "perimetre", "perimeter", "scope",
)

# ---------------------------------------------------------------------------
# #11712 — incidental counts. The founding asymmetry: the count branch retained
# ANY "N fichiers" in prose, so an inventory ("22 fichiers MP3"), a scan scope
# ("grep ... sur 73 fichiers"), a cited threshold ("< 15 fichiers", the G.4
# rule itself) or a zero-attestation ("0 fichier machine-path") was confronted
# with len(files) and failed necessarily -- 11/120 PRs carried >= 2 distinct
# counts, making a red GUARANTEED regardless of the real perimeter. The fix
# follows #11648's path: detection is UNCHANGED (the line is still extracted,
# confronted and printed), only the consequence moves -- an incidental count is
# a SIGNAL, not a blocking problem. Do not "fix" a false positive by narrowing
# extract_perimeter_assertions: that would also silence the printed report.
#
# FN safety is structural: every rule below first requires the line to carry
# NO strong scope word and NO diffstat neighborhood (+N/-N, insertions,
# deletions, lignes) -- the two shapes the corpus identifies as genuine
# assertions (40 diffstat lines and 30 scope-word lines, all preserved).
# ---------------------------------------------------------------------------
# A count whose referent is a KIND of artifact or a REMAINDER, not "the files
# this PR changes". Closed list measured on the 120-PR corpus; unknown
# qualifiers stay authorial (a false negative does not signal itself, so the
# default must fail loud).
#
# #13471 : les chaines accentuees sont NFD-strippees avant match (voir
# `_count_has_incidental_qualifier`). Les entrees canoniques sont stockees
# telles quelles pour la lisibilite de la liste (un mainteneur voit 'vérifié'
# et comprend), mais le predicat compare les deux cotes apres strip --
# donc 'verifié' (hybride 1er e nu / dernier accentué), 'vérifié', 'verifie',
# 'verifies' collapsent sur la meme cle 'verifie'.
INCIDENTAL_QUALIFIERS = frozenset({
    "mp3", "wav", "mathlib", "machine-path", "fr", "en", "scratch",
    "restants", "restant", "reste", "restants,", "nouveau", "nouveaux",
    "nouvelle", "nouvelles", "varies", "variés", "synthetiques",
    "synthétiques", "scripts", "cache", "generes", "générés", "produits",
    "produites", "sources", "source",
    # #11985 formes 3-4: artifact kinds and scan inventories.
    "audio", "distinct", "distincts", "distinctes", "non-notebook",
    # #13440 -- participes de RESULTAT DE CONTROLE : ce qu'un controle a
    # couvert, jamais ce que le diff touche (un claim de perimetre s'ecrit
    # avec des verbes de modification, qui restent bloquants via
    # _has_strong_scope et hors liste). Formes mesurees sur main :
    # "25 fichier(s) verifies sans BOM", "18 fichiers testes sans erreur",
    # "Controle encodage : 25 fichier(s) conformes".
    # FN DELIBERE : "restaures"/"restaurés" (campagne accents #2876) et
    # "re-executes"/"re-exécutés" (tranches MGS) restent HORS liste -- dans
    # ce depot ces formes SONT des perimetres.
    "verifies", "vérifiés", "verifie", "vérifié",
    "testes", "testés", "teste", "testé",
    "conformes", "conforme",
    "scannes", "scannés", "scanne", "scanné",
    "analyses", "analysés", "analyse", "analysé",
    "audites", "audités", "audite", "audité",
    "examines", "examinés", "examine", "examiné",    # #12718 (classe #11985 forme 4): "N fichiers neufs/neuve/neuf" -- the
    # French "new" adjective in its noun-collocated form -- is a NEW-FILES
    # descriptor, never the whole-PR perimeter. The equality confrontation
    # would read "2 fichiers neufs : file1 + file2" as "the PR changes 2
    # files" when it actually adds 2 new ones among 5 changed. Same family
    # as "nouveau/nouveaux/nouvelle/nouvelles" above; the masculine/feminine
    # singular/plural variants were missing.
    "neuf", "neuve", "neufs",})
# ---------------------------------------------------------------------------
# #13610 -- article indefini en position d'objet d'un verbe d'action dont le
# sujet N'est PAS la PR. Founder case PR #13539 l.43 :
# « generaliser demanderait d'editer un fichier deja porteur de deux PRs
# ouvertes de la meme lane (#13496, #13499) » -- « un fichier » y designe
# `pick_idle_grain.py` (un fichier que la PR ne touche pas, cite pour
# justifier un non-geste de routage), et le guard tirait 1 fichier(s) face a
# une liste de 3, rougissant un check requis sur une PR saine. Meme classe
# symetrique que les fondateurs #11985 forme 5/6 : un referent descriptif,
# pas une assertion de perimetre.
#
# Discriminant : « (un|une|des) (fichier|files)(s) » OUVERT par un verbe
# d'action EDIT + un nom de FICHIER NOMMÉ sur la meme ligne ET ce nom n'est
# PAS dans `files`. Si le referent reste anonyme (« editer un fichier »),
# le cas est ambigu et le garde CONSERVE le rouge (FN safety par defaut,
# coherent avec le pattern fondateur du script).
# ---------------------------------------------------------------------------
_INDEF_ARTICLE = re.compile(r"\b(?:un|une|des)\s+(?:fichiers?|files?)\b", re.IGNORECASE)
_EDIT_VERB = re.compile(
    r"\b(?:editer|modifier|toucher|ouvrir|créer|creer|ajouter|changer|mettre\s+à\s+jour|mettre\s+a\s+jour|update|edit|modify|touch|open|create|add|change)\b",
    re.IGNORECASE,
)
# A named file as it would appear in a body: backticked path, bare basename
# (.py/.cs/.yml/.json/.md/.ipynb/.sh), or a known scripts/<x>.py shape.
_NAMED_FILE_BODY = re.compile(
    r"(?:`([^`]+\.[A-Za-z0-9]+)`|"  # backticked: `pick_idle_grain.py`
    r"\b([\w./-]+\.(?:py|cs|yml|yaml|json|md|ipynb|ts|js|sh|toml|cfg|ini))\b)"  # bare basename
)
# A cited threshold ("< 15 fichiers", ">= 10 fichiers") quotes a rule, it does
# not claim a perimeter.
COMPARISON_PREFIX = re.compile(r"[<>=≤≥]\s*$")
# A count governed by a locative/scan preposition ("sur les 2 fichiers",
# "across N files") is the SCOPE of a check or a tool run, not the perimeter
# -- unless the same line carries a diffstat, where "sur 2 fichiers" names
# what the diffstat measured (a true assertion: "+307 lignes / −0 sur 2
# fichiers").
LOCATIVE_PREP = re.compile(
    r"\b(?:sur|dans|across|on)\s+(?:les\s+|le\s+|la\s+|the\s+)?\d+\s*"
    r"(?:fichiers?|files?|touches)\b",
    re.IGNORECASE,
)
# A count qualifying files as NOT changed ("91 fichiers inchanges", "2 fichiers
# non modifies", "73 files unchanged") is the NEGATION of a diff -- the author
# is reporting what the diff does NOT touch, which the guard cannot confront
# with the effective file list (which lists what the diff DOES touch). Issue
# #11800: the founder body of #11775 l.31 ("91 fichiers inchanges sur 2
# touches -- scope delta confirme") was blocked by the COUNT_CLAIM regex
# matching "91 fichiers" before the negation word was parsed. Fix: exempt the
# negated-diff shape syntactically. The negated-diff attestation is a property
# of the specific count that carries the negation word, NOT of the whole line
# -- otherwise a "5 fichiers modifies, 91 fichiers inchanges" line would have
# its blocking 5-files count swept under the negated-diff umbrella of 91.
NEGATED_DIFF_TAIL = re.compile(
    r"^\s*(?:inchang[eé]s?|non[\s-]+modifi[eé]s?|non[\s-]+touch[eé]s?"
    r"|intacts?|untouched|unchanged|unmodified)\b",
    re.IGNORECASE,
)
# ---------------------------------------------------------------------------
# #11985 -- counts that describe ANOTHER OBJECT than the PR's head. Measured
# on the 20/08 corpus: 7 of 9 perimeter-red PRs were false positives, and the
# founding asymmetry is that the guard's EQUALITY confrontation (claimed ==
# len(files)) can never validate these shapes -- it confronts a sub-sum, an
# inventory, a past revision or a rejected alternative. Same path as #11712:
# detection UNCHANGED (the line is still extracted and printed), only the
# consequence moves.
# ---------------------------------------------------------------------------
# Forme 5, past self-description: an imparfait + a commit SHA or a #PR ref on
# the same line describe a SUPERSEDED version of the PR. The diffstat in that
# line measures the old commit, not the head -- so this rule overrides the
# diffstat guard (#11790: "couvrait 160 fichiers / +31502/-80470", real PR = 1
# file). The imparfait is closed-list: genuine perimeter assertions are in the
# present tense.
PAST_REFERENCE = re.compile(
    r"\b(?:couvrait|contenait|comprenait|comportait|touchait)\b", re.IGNORECASE
)
HASH_OR_PR_REF = re.compile(r"\b[0-9a-f]{7,40}\b|#\d+")
# Forme 6, counterfactual: the count describes the PR that was NOT written.
# The marker must sit BEFORE the first count -- "3 fichiers plutot que 15"
# keeps its authorial 3. Measured on #11963: "> 1 PR composite (15 fichiers /
# >3000 lignes)".
COUNTERFACTUAL_MARKER = re.compile(
    r"(?:au lieu de|plut[oô]t que|plut[oô]t d'|contrefactuel|\bcomposite\b)",
    re.IGNORECASE,
)
# Forme 1, enumeration component: "X.py (...) + N fichiers de tests" -- the
# body enumerates 1 + 2 = 3 (exact), the guard reads the sub-sum 2 and can
# never validate it (#11935). Requires a NAMED file before the "+ N fichiers
# de tests" tail: the shape is an enumeration of components, not a total.
ENUMERATION_TAIL = re.compile(
    r"\+\s*\d+\s*fichiers?\s+de\s+tests?\b", re.IGNORECASE
)
NAMED_FILE = re.compile(
    r"\b[\w.-]+\.(?:py|cs|yml|yaml|json|md|ipynb|ts|js|sh|toml|cfg|ini)\b",
    re.IGNORECASE,
)
# Forme 4, scan result: a "N hits" antecedent before the count ("Apres : 1
# hit / 1 fichier") counts what the detector FOUND, not what the PR modifies
# (#11966 l.42).
HIT_ANTECEDENT = re.compile(r"\b\d+\s*hits?\b", re.IGNORECASE)
# Forme 4b, measurement antecedent: a "lake 70 fichiers" / "corpus 12 fichiers"
# / "count_code_sorry.py ... 70 fichiers" / "scan ... N fichiers" shape --
# the count is the OUTPUT of an EXTERNAL measurement tool, not the PR
# perimeter (#12184, founder case #12181 l.26 "lake de 70 modules, 1 sorry
# reel distinct"). Same family as HIT_ANTECEDENT / LOCATIVE_PREP: bad
# surface, not bad count -- the body reports what the tool measured on some
# corpus (a Lean lake, a registry, a scan target), never what the diff
# touches.
#
# Closed-list antecedent vocabulary: external measurement tools named in the
# corpus (lake, corpus, registry, count_code_sorry.py, scan, mesure,
# mesures, count_code_sorry, check_*). Extension is gated by the FN-control
# of #11985: a new vocabulary term needs to be measured against #11956 /
# #12065 (real perimeter assertions that must remain blocking). A bare
# antecedent is intentionally WEAK: it must sit within a small window before
# the count AND the count must remain excluded by the FN-safety guards in
# _count_is_incidental (no scope word, no diffstat neighborhood). The
# founder case is the asphalt.
#
# #13791: grep / git grep / rg added to the closed list -- grep is THE most
# common measurement verb in this repo's PR bodies ("2.9 est le seul
# notebook torch de 02-ML-Cours (grep : 1 fichier)", founder #13782), and
# without it the guard read a corpus count as a perimeter declaration.
# FN-control measured on the six verdict PRs of #13791: #11956/#12065/
# #13557/#13685 carry no grep-antecedent line that flips (their blocking
# counts sit on diffstat/scope-word lines, which stay blocking before this
# exemption is even consulted).
#
# The pattern matches the antecedent ALONE (no count baked in); the count
# exemption is per-match and uses line[:m.end()] to allow the antecedent to
# sit anywhere in the run-up to the count (the per-match exemption already
# anchors the count at m.start/end).
MEASUREMENT_ANTECEDENT = re.compile(
    r"\b(?:lake\s+(?:de\s+|of\s+)?|"
    r"corpus(?:\s+(?:de|of))?|"
    r"count_code_sorry(?:\.py)?|"
    r"scan(?:\s+(?:sur|of|on))?|"
    r"mesures?(?:\s+(?:sur|of|on))?|"
    r"(?:git\s+)?grep(?:\s+(?:sur|of|on|:|--?rn?))?|"
    r"rg(?:\s+(?:sur|of|on|:))?|"
    r"registry|registre(?:\s+(?:de|of))?|"
    r"check_(?:unaddressed_nits|pr_perimeter|perimeter))\b",
    re.IGNORECASE,
)
# Forme 4c, snapshot avant/apres: "avant (main) : <composant> — N fichiers" /
# "apres (branche) : N fichiers" -- a before/after baseline of a MEASURED
# quantity (a Lean lake's SIZE), never the PR's perimeter (#12718). Same family
# as MEASUREMENT_ANTECEDENT: bad surface, not bad count. The signal is the
# snapshot keyword adjacent to a branch-state label -- "avant (main)", "apres
# (branche)" -- which appears only in baseline-comparison prose. FN-safety is
# structural: a line carrying a strong scope word or a diffstat neighborhood
# returns blocking in _count_is_incidental BEFORE this exemption is consulted,
# so "Perimetre : avant 2 fichiers, apres 5 fichiers" stays blocking.
SNAPSHOT_ANTECEDENT = re.compile(
    r"\b(?:avant|après|apres|before|after|baseline)\b"
    r"[^a-z0-9_]*\(?\b(?:main|branche|branch|master)\b\)?",
    re.IGNORECASE,
)
# Forme 5, compte-antecedent parenthetique: "<N> <unites> (<M> fichiers)" --
# le compte entre parentheses qualifie la PROVENANCE du nombre qui precede
# ("32 prescriptions avant (2 fichiers) -> 32 apres"), jamais le perimetre de
# la PR (#12057). Meme famille que HIT_ANTECEDENT: mauvaise surface, pas
# mauvais compte.
#
# L'antecedent NUMERIQUE est ce qui borne l'exemption. Sans lui, la simple
# presence de parentheses suffirait et "Perimetre (2 fichiers)" -- une vraie
# assertion -- passerait. C'est le controle positif de #12057.
PAREN_ANTECEDENT_NUM = re.compile(r"\d")
# Forme 6, verbe de reference: "N fichiers pointent ici / referencent / citent"
# -- le compte porte sur des REFERENTS ENTRANTS, qui par construction ne sont
# pas dans le diff. Compter les liens entrants est EXIGE par le protocole de
# fusion arrete en #12051; le garde ne peut pas punir la mesure que le
# protocole rend obligatoire (#12057).
REFERENCE_VERB_TAIL = re.compile(
    r"^\s*(?:pointent|pointe|r[ée]f[ée]rencent|r[ée]f[ée]rence|citent|cite|"
    r"renvoient|renvoie|mentionnent|mentionne|link|links|reference|references)\b",
    re.IGNORECASE,
)
# Formes 2-4, two-word qualifier window: artifact kinds and enumeration tails
# are often compound ("fichiers audio generes", "fichiers de tests", "fichier
# test adapte") -- the closed list matches the first OR second word after the
# count, or their pair.
# "de tests"/"de test" deliberately ABSENT: the enumeration form 1 requires
# the "+ N fichiers de tests" tail AND a named file on the line
# (ENUMERATION_TAIL + NAMED_FILE below). A bare pair would make
# "2 fichiers de tests modifies" incidental with no named-file guard (#11985
# FN control).
INCIDENTAL_QUALIFIER_PAIRS = frozenset({
    "audio generes", "audio générés",
    "test adapte", "test adapté",
})
DIFFSTAT_NEIGHBORHOOD = re.compile(
    r"\+\d+\s*/\s*[-−]?\d+|insertions?|deletions?|\blignes?\b|\blines?\b",
    re.IGNORECASE,
)


def _has_strong_scope(low: str) -> bool:
    # Whole-word match -- "change" must not fire on "inchanges" (#11800 FN
    # vector: the negated-diff count's tail is "inchanges" / "non modifies"
    # etc., which carries "change" as a substring of "inchanges" via the
    # plain `in` test, blocking the per-match NEGATED_DIFF_TAIL exemption).
    # The 8 STRONG_SCOPE_WORDS are all standalone vocabulary in French/English;
    # a regex boundary costs nothing and removes a class of false positives.
    # #12718: "scope" as a hyphenated compound ("in-scope", "out-of-scope") is
    # an adjective describing scope-inclusion, never a perimeter-count label --
    # a hyphen-negative lookbehind keeps such a line incidental while
    # "scope = perimetre PR" and "Périmètre : N fichiers modifiés" still block.
    # All non-"scope" words keep the plain \b...\b boundary ("modif" must not
    # misfire; "périmètre" is a standalone label).
    for w in STRONG_SCOPE_WORDS:
        if w == "scope":
            if re.search(r"(?<![-\w])scope(?![-\w])", low):
                return True
        elif re.search(rf"\b{re.escape(w)}\b", low, re.IGNORECASE):
            return True
    return False


def _strip_accents(s: str) -> str:
    """#13471: NFD decompose + drop combining marks. Both sides of the
    incidental-qualifier match are run through this so accent variants
    ('verifié' hybride, 'vérifié', 'verifie') collapse to the same key.
    Couvre les variantes futures sans nouvelle tranche de liste -- c'est
    precisement la serie de tranches que ce depot cherche a eviter."""
    return "".join(
        ch for ch in unicodedata.normalize("NFD", s)
        if unicodedata.category(ch) != "Mn"
    )


# #13471: pre-normalized lookup set for incidental qualifier match. We normalize
# INCIDENTAL_QUALIFIERS once at module load (frozen set of NFD-stripped lower
# tokens) rather than normalizing per-call -- the set is small (~80 entries)
# and the predicate runs O(matches_per_line).
_INCIDENTAL_QUALIFIERS_NFD = frozenset(_strip_accents(w).lower() for w in INCIDENTAL_QUALIFIERS)
_INCIDENTAL_QUALIFIER_PAIRS_NFD = frozenset(
    _strip_accents(p).lower() for p in INCIDENTAL_QUALIFIER_PAIRS
)


def _count_has_incidental_qualifier(line: str, m: re.Match) -> bool:
    """#12718: true when the COUNT match `m` is immediately followed by an
    `INCIDENTAL_QUALIFIERS` word (or a qualified two-word pair). A count so
    qualified is a sub-claim ("N fichiers neufs : ... (330 lignes)"), not the
    whole-PR perimeter -- and, unlike an antecedent exemption, it overrides a
    diffstat neighbor on the same line. Extracted from _count_is_exempt so the
    two callers (per-count exemption, incidental override) share one predicate.

    #13471 (2 residus) :
      - Accent variants : les deux cotes du match passent par NFD-strip, donc
        'verifié' (hybride, premier e nu / dernier accentue) est reconnu au
        meme titre que 'vérifié' / 'verifie' / 'verifies' (formes deja
        listees). Une nouvelle variante accidentee future sera couverte sans
        nouvelle tranche.
      - 2 mots en OR : le predicat matche si le PREMIER OU le SECOND des deux
        premiers mots est dans `INCIDENTAL_QUALIFIERS`. La condition pre-
        existante (1er mot OU paire exacte `INCIDENTAL_QUALIFIER_PAIRS`)
        attrapait 'audio generes' mais pas 'puis conformes' -- le 2eme mot
        'conformes' est dans `INCIDENTAL_QUALIFIERS` mais le 1er ('puis')
        ne l'est pas, donc le predicat rendait False. Apres le fix, le
        second mot incident est lu comme un standalone."""
    # #13440: le pluriel parenthetique "(s)" est neutralise avant lecture du
    # qualificatif ("fichier(s) verifies" doit lire "verifies").
    after = PLURAL_PAREN.sub(" ", line[m.end():], count=1)
    # Le pattern lit **au plus** les 2 premiers mots ; au-dela, les
    # separateurs (parentheses ouvrantes, backticks, slash) ferment le
    # token. C'est le pattern d'origine (conservé) -- le predicat ne doit
    # **pas** traverser les delimiteurs vers des mots eloignes
    # (anti-regression : '- 1 fichier modifie (`scripts/.../foo.py`, +1/-1)'
    # matchait 'modifie' puis voyait 'scripts' comme 2eme mot, mais 'scripts'
    # EST dans la liste ; il faut rester aveugle derriere la parenthese).
    _WORD_RE = re.compile(
        r"\s+([\wàâäéèêëîïôöùûüçÀÂÄÉÈÊËÎÏÔÖÙÛÜÇ-]+)"
        r"(?:\s+([\wàâäéèêëîïôöùûüçÀÂÄÉÈÊËÎÏÔÖÙÛÜÇ-]+))?"
    )
    mw = _WORD_RE.match(after)
    if not mw:
        return False
    first_nfd = _strip_accents(mw.group(1)).lower()
    if first_nfd in _INCIDENTAL_QUALIFIERS_NFD:
        return True
    if mw.group(2):
        # Paire exacte (close-list, formes specifiques type 'audio generes').
        pair_nfd = f"{first_nfd} {_strip_accents(mw.group(2)).lower()}"
        if pair_nfd in _INCIDENTAL_QUALIFIER_PAIRS_NFD:
            return True
        # #13471 Résidu 2 : 2 mots en OR. Le 2eme mot seul est incident
        # ('puis conformes' -- 'conformes' est dans la liste single-word mais
        # 'puis' ne l'est pas).
        second_nfd = _strip_accents(mw.group(2)).lower()
        if second_nfd in _INCIDENTAL_QUALIFIERS_NFD:
            return True
    return False


def _count_is_exempt(line: str, m: re.Match, ante_context: str = "") -> bool:
    """True when the specific COUNT match `m` on `line` is exempted by the
    per-count filters (zero, threshold citation, locative scan scope,
    negated-diff tail, scan antecedent, reference verb, parenthesized
    antecedent, incidental qualifier). Shared by _count_is_incidental and
    _additive_line_sum (#12103).

    #13335: `ante_context` is the enclosing markdown paragraph above `line`
    (contiguous non-empty lines, blank line = boundary). ONLY the
    MEASUREMENT_ANTECEDENT branch consults it: a soft-wrapped body puts the
    tool antecedent ("Un scan recursif rendait 54 / en accusant 5 fichiers")
    on the line above the count, and a same-line window would amputate the
    exemption of the very thing it looks for -- the verdict would depend on
    where the author pressed Enter, not on what the body asserts. Every other
    branch stays line-scoped: the issue's controls C/D (founder perimeter
    assertion, bare authorial count) carry no measurement antecedent anywhere
    in their paragraph and remain blocking."""
    claimed = int(m.group(1))
    if claimed == 0:
        return True
    before = line[: m.start()].rstrip()
    if COMPARISON_PREFIX.search(before):
        return True
    if LOCATIVE_PREP.search(line):
        return True
    after = PLURAL_PAREN.sub(" ", line[m.end():], count=1)
    if NEGATED_DIFF_TAIL.match(after):
        return True
    if HIT_ANTECEDENT.search(line[: m.start()]):
        return True
    ante_scope = f"{ante_context}\n{line[: m.end()]}" if ante_context else line[: m.end()]
    if MEASUREMENT_ANTECEDENT.search(ante_scope):
        return True
    if SNAPSHOT_ANTECEDENT.search(line[: m.start()]):
        return True
    if REFERENCE_VERB_TAIL.match(after):
        return True
    if (before.endswith("(") and after.lstrip().startswith(")")
            and PAREN_ANTECEDENT_NUM.search(before[:-1])):
        return True
    if _count_has_incidental_qualifier(line, m):
        return True
    return False


def _word_form_is_indef_non_pr_subject(text: str, files: list[dict]) -> bool:
    """#13610: True when a word-form count in `text` is an indefinite
    article (« un/une/des fichier(s) ») opened by an edit-verb whose NAMED
    referent is NOT in `files`. The phrase describes an OTHER file (a
    routing target, a dependency, a candidate not chosen) and is not the
    PR's perimeter.

    FN safety: when the referent is anonymous (« editer un fichier » with
    no named file), the function returns False -- the ambiguous shape
    stays blocking, coherent with the script's founder pattern (default
    fails loud; new vocabulary is gated by a measurement, not an
    intuition). Founder case PR #13539 l.43 :
    « generaliser demanderait d'editer un fichier deja porteur de deux PRs
    ouvertes de la meme lane (#13496, #13499) » -- here "un fichier"
    designates `pick_idle_grain.py` (a file the PR does not touch), and
    the guard drew 1 vs 3, blocking a healthy PR.

    Hook: called from `check_assertion` on the `word_count` branch only.
    The digit branch (COUNT_CLAIM) cannot produce the indefinite-article
    shape and so does not need this guard.
    """
    low = text.lower()
    m = _INDEF_ARTICLE.search(low)
    if m is None:
        return False
    start = m.start()
    window_before = text[max(0, start - 80):start]
    if not _EDIT_VERB.search(window_before):
        return False
    paths_in_files = {f["path"] for f in files}
    paths_in_files_basenames = {p.rsplit("/", 1)[-1] for p in paths_in_files}
    named = _NAMED_FILE_BODY.findall(text)
    named_flat = [n[0] or n[1] for n in named if n[0] or n[1]]
    if not named_flat:
        return False
    return any(
        n not in paths_in_files and n not in paths_in_files_basenames
        for n in named_flat
    )


# #13791 -- indefinite word-form count opened by a DISCRIMINATION verb. The
# founder line (#13736 l.26): "le script echoue sur un faux positif
# (l'instrument ne peut pas distinguer un fichier corrompu d'un fichier
# offensif)" -- the word-form trigger read "un fichier" as a 1-file perimeter
# claim against a 2-file list, while the phrase names the OBJECTS OF A
# COMPARISON the body is making about the instrument. Same family as
# #11985 forme 4b (bad surface, not bad count) and #13610 (indefinite
# article + governing verb). Closed verb list; FN-safety mirrors
# _word_form_is_indef_non_pr_subject: same 80-char window before the article,
# and a genuine word-form perimeter claim ("un fichier modifie : X.py")
# never follows a discrimination verb -- the residual risk ("on distingue un
# fichier modifie") is the deliberate closed-list trade, measured against
# the #13791 control PRs (none of #11956/#12065/#13557/#13685 carries a
# discrimination verb before a word-form count).
_DISCRIMINATION_VERB = re.compile(
    r"\b(?:distinguer|diff[ée]rencier|discriminer|contraster|opposer|"
    r"s[ée]parer|comparer)\b",
    re.IGNORECASE,
)


def _word_form_is_measurement_object(text: str) -> bool:
    """#13791: True when a word-form count's indefinite article ("un fichier")
    sits within 80 chars AFTER a discrimination verb -- the phrase names the
    objects of a comparison (diagnostic prose about what an instrument
    distinguishes), not the PR's perimeter."""
    m = _INDEF_ARTICLE.search(text.lower())
    if m is None:
        return False
    return bool(_DISCRIMINATION_VERB.search(text[max(0, m.start() - 80):m.start()]))


_MEASUREMENT_RESULT = re.compile(
    r"\b(?:\d+|aucun(?:e)?)\s+(?:occurrences?|hits?|r[ée]sultats?|matches?)\b",
    re.IGNORECASE,
)
_DEFINITE_WORD_FORM = re.compile(
    r"\b(?:sur|dans)\s+(?:les|ces)\s+[*_]*"
    r"(?:deux|trois|quatre|cinq|six|sept|huit|neuf|dix)\s+fichiers?\b",
    re.IGNORECASE,
)


def _word_form_is_measurement_result(text: str, block: str = "") -> bool:
    """True when a definite word-form count is the corpus of a measured result.

    The result may sit on the same line or immediately above it in the same
    paragraph block (soft-wrap invariant). A strong scope word keeps genuine
    perimeter assertions blocking even when they also mention zero results.
    """
    surface = block or text
    if _has_strong_scope(surface.lower()):
        return False
    count = _DEFINITE_WORD_FORM.search(surface)
    if count is None:
        return False
    result = list(_MEASUREMENT_RESULT.finditer(surface, 0, count.start()))
    return bool(result)


def _additive_line_sum(line: str) -> int:
    """#12103: sum of the line's COUNT_CLAIM values that survive the per-count
    filters. An additive enumeration -- "1 fichier modifie, 1 fichier ajoute" --
    declares N + M files; the guard must confront the SUM, not the first
    non-zero count. A count exempted by the filters (zero, negated-diff tail,
    locative scope, ...) never joins the sum. #12201: a count inside a
    citation span or followed by a name range is reported speech, not an
    additive term -- same skip as the claim selection, so the two paths
    read the same body the same way."""
    return sum(
        int(m.group(1))
        for m in COUNT_CLAIM.finditer(line)
        if not _count_is_exempt(line, m)
        and not _count_in_citation(line, m)
        and not _count_is_range_enum(line, m)
        and not _count_is_out_of_scope_annotation(line, m)
    )


def _word_form_count(text: str) -> int | None:
    """#12092: first spelled-out cardinal followed by its language-agreeing
    noun (closed list COUNT_WORDS, FR/EN 1-10 ; #13535 : FR cardinal +
    fichiers?, EN cardinal + files?). None when the line carries no word-form
    count -- mirror of COUNT_CLAIM for the word shape. Reuses the exact
    trigger list of extract_perimeter_assertions so both halves
    of the organ agree on what a word count is."""
    low = text.lower()
    for _word, n, trig in WORD_FORM_TRIGGERS:
        if trig.search(low):
            return n
    return None


def _count_is_incidental(line: str, ante_context: str = "") -> bool:
    """True when every count on the line denotes something other than the PR's
    file list. Caller-facing guarantee: a line with a scope word or a diffstat
    neighborhood is NEVER incidental via the qualifier/locative rules (FN
    safety, #11712 acceptance). Four shapes override even those guards, because
    they can never be validated by the guard's EQUALITY confrontation anyway:
    a zero count (a PR never has 0 files), a comparison-prefixed count
    ("< 15 fichiers" cites a threshold), and -- #11985 -- a count describing
    ANOTHER object than the head (a table row, a superseded revision, a
    rejected alternative, an enumeration sub-sum). #13335: `ante_context`
    (paragraph prefix) feeds only the MEASUREMENT_ANTECEDENT exemption -- see
    _count_is_exempt."""
    low = line.lower()
    # #11985 forme 4 (table case): a markdown table row is a report structure
    # (the tube separates the qualifier from its number -- no cell pairing is
    # a perimeter claim). Extraction already skips rows; this pins the
    # classification for any direct caller.
    if line.lstrip().startswith("|"):
        return True
    matches = list(COUNT_CLAIM.finditer(line))
    if not matches:
        return False
    first = matches[0]
    first_before = line[: first.start()].rstrip()
    if int(first.group(1)) == 0 or COMPARISON_PREFIX.search(first_before):
        return True
    # #11985 formes 5/6/1 -- the count describes another object than the head:
    # its diffstat and scope words belong to that object, so these rules sit
    # BEFORE the guards below.
    if PAST_REFERENCE.search(low) and HASH_OR_PR_REF.search(line):
        return True  # superseded revision: "couvrait 160 fichiers" (#11790)
    marker = COUNTERFACTUAL_MARKER.search(low)
    if marker and first.start() > marker.start():
        return True  # rejected alternative: "1 PR composite (15 fichiers)" (#11963)
    if ENUMERATION_TAIL.search(line) and NAMED_FILE.search(line):
        return True  # enumeration sub-sum: "X.py + 2 fichiers de tests" (#11935)
    if _has_strong_scope(low):
        return False
    if DIFFSTAT_NEIGHBORHOOD.search(line):
        # A qualifier-exempt count ("N fichiers neufs : file (330 lignes)")
        # overrides the diffstat guard -- the "lignes" is a per-file size and
        # the qualifier marks a sub-claim, not the whole-PR perimeter. An
        # antecedent-exemption (locative "sur 2 fichiers", measurement parent,
        # snapshot) does NOT override: "+307 lignes / −0 sur 2 fichiers" names
        # what the diffstat measured (#11935 FN control stays blocking).
        if all(_count_has_incidental_qualifier(line, m) for m in matches):
            return True
        return False
    for m in matches:
        if not _count_is_exempt(line, m, ante_context):
            return False  # this count looks authorial -> the line stays blocking
    return True


def _exclusivity_marker_in_parens(line: str) -> bool:
    """True when every exclusivity marker on the line sits inside a
    parenthetical group. #11616 forme B: "(SL-8/SL-9 only, scope minimal)"
    co-presents 'only' and 'scope' by lexical coincidence -- a phase plan,
    not a perimeter assertion. Outside parens, "Aucune autre modification."
    and "N fichiers X uniquement" remain authorial (measured on the corpus:
    no genuine exclusivity-only assertion carries its marker in parens)."""
    low = line.lower()
    open_paren = False
    outside_hits = 0
    i = 0
    while i < len(line):
        ch = line[i]
        if ch == "(":
            open_paren = True
        elif ch == ")":
            open_paren = False
        else:
            for marker in EXCLUSIVITY_MARKERS:
                if low.startswith(marker, i) and not open_paren:
                    outside_hits += 1
        i += 1
    # every marker inside parens <=> no marker outside
    return outside_hits == 0 and any(low.find(mk) >= 0 for mk in EXCLUSIVITY_MARKERS)


def _is_incidental_assertion(text: str, ante_context: str = "") -> bool:
    """#11712: kept in candidates (found + printed), excluded from blocking.
    #13335: `ante_context` (enclosing paragraph, see _count_is_exempt) makes
    the measurement-antecedent exemption wrap-invariant."""
    if COUNT_CLAIM.search(text):
        return _count_is_incidental(text, ante_context)
    if _has_exclusivity(text.lower()):
        return _exclusivity_marker_in_parens(text)
    return False


def _quote_spans(line: str) -> list[tuple[int, int]]:
    """Char spans of quoted speech on a single line (« ... » and " ... ").

    A trigger that sits inside a quotation is REPORTED SPEECH -- the author
    quoting someone else's assertion (an incident writeup, an anti-FP test
    description) -- not the author's own claim. Spans are intra-line: a quote
    opened but not closed on the line counts to end of line.
    """
    spans: list[tuple[int, int]] = []
    for open_c, close_c in (("«", "»"), ('"', '"')):
        start = 0
        while True:
            i = line.find(open_c, start)
            if i < 0:
                break
            j = line.find(close_c, i + 1)
            if j < 0:
                spans.append((i, len(line)))
                break
            spans.append((i, j + 1))
            start = j + 1
    return spans


def _trigger_quoted(line: str, pos: int, length: int) -> bool:
    return any(a <= pos and pos + length <= b for a, b in _quote_spans(line))


def _codespan_spans(line: str) -> list[tuple[int, int]]:
    """Char spans of inline code on a single line (`` `...` ``, ````...````).

    A trigger that sits inside a backtick code-span is CITED content -- the
    author using code formatting to *show* an example (or to escape a
    technical word), not making their own assertion. Same class as quoted
    speech (see _quote_spans): the marker carries intent to be displayed,
    not claimed.

    CommonMark rules: `` `code` `` is a single-backtick span;
    `` ``code with ` inside`` `` is the double-backtick variant. We handle
    both, plus the case where a longer backtick run opens but no matching
    closer appears on the line -- the span then runs to end of line
    (CommonMark behaviour for unterminated inline code, and what GitHub
    renders).

    Measured on #12024 body v3 -- a 6-line snippet "(\\`trois fichiers\\` /
    \\`five files\\`)" flagged 4 lines as `trois fichiers` / `five files`
    candidates even though backticks clearly showed them as examples. The
    pre-fix extractor had no code-span awareness; the founder case here
    is "citer un exemple en l'écrivant comme du code n'est pas en faire
    une assertion".
    """
    spans: list[tuple[int, int]] = []
    i = 0
    while i < len(line):
        if line[i] != "`":
            i += 1
            continue
        n = 0
        while i + n < len(line) and line[i + n] == "`":
            n += 1
        close_pat = "`" * n
        j = line.find(close_pat, i + n)
        if j < 0:
            spans.append((i, len(line)))
            break
        spans.append((i, j + n))
        i = j + n
    return spans


def _trigger_in_codespan(line: str, pos: int, length: int) -> bool:
    return any(a <= pos and pos + length <= b for a, b in _codespan_spans(line))


def _trigger_in_quoted_or_codespan(line: str, pos: int, length: int) -> bool:
    return _trigger_quoted(line, pos, length) or _trigger_in_codespan(line, pos, length)


def _counts_all_quoted_or_codespan(line: str) -> bool:
    """Every numeric COUNT_CLAIM on the line sits inside a quotation OR a code-span.

    Wraps the original _counts_all_quoted with code-span awareness: a count
    cited as `` `trois fichiers` `` (the founder case on #12024 body v3) is
    displayed, not claimed. A line that only carries quoted / code-spanned
    counts is not a perimeter assertion.
    """
    return all(
        _trigger_in_quoted_or_codespan(line, m.start(), m.end() - m.start())
        for m in COUNT_CLAIM.finditer(line)
    )


def _counts_all_quoted(line: str) -> bool:
    """Every file-count claim on the line sits inside a quotation."""
    return all(
        _trigger_quoted(line, m.start(), m.end() - m.start())
        for m in COUNT_CLAIM.finditer(line)
    )


def _markers_all_quoted(line: str) -> bool:
    """Every exclusivity marker on the line sits inside a quotation."""
    low = line.lower()
    for marker in EXCLUSIVITY_MARKERS:
        start = 0
        while True:
            i = low.find(marker, start)
            if i < 0:
                break
            if not _trigger_quoted(line, i, len(marker)):
                return False
            start = i + len(marker)
    return True


def _fence_line_indices(text: str) -> tuple[set[int], int | None]:
    """Return (in_fence_indices, orphan_opener_line).

    The set contains the 0-based indices of lines that sit INSIDE a markdown
    fence. The int is the 0-based index of the orphan opener line -- the
    delimiter that was opened but never closed, so the fence runs to EOF --
    and None when every fence is closed (#11723). In CommonMark terms the
    fence running to EOF is the correct rendering behaviour (and what GitHub
    does), but it has a perverse downstream consequence: every line after
    the orphan opener is excluded from the scan, and the gate becomes a
    silent no-op for the rest of the body. Localizing the opener lets
    `--scan-thread` distinguish "no candidates found" from "no candidates
    read" AND point the author at the exact line to close, which is exactly
    the false-negative shape #11678's founder case measured.

    Mirrors the existing _quote_spans exemption idea: a fence is transcription,
    never an author's own claim. Workers document their L898 cross-lane
    verification in fences (command output verbatim), and that transcription
    carries file counts ("0 fichiers en commun") that would otherwise be
    mis-extracted as authorial perimeter assertions. Issue #11670 founder
    case: PR #11664 body contains L898 proof in a fenced block; the line
    "0 fichiers en commun avec les autres PR" sits inside the fence without
    the fence delimiters on the line itself, so the line-level scanner used
    by `--scan-thread` would otherwise surface it. The check is line-based
    and O(n) once per text.

    Fence delimiters are lines starting with three or more backticks OR
    three or more tildes. The closing delimiter matches either family.
    Delimiter lines themselves are NOT in the returned set (only the lines
    they enclose).
    """
    indices: set[int] = set()
    in_fence = False
    orphan_opener: int | None = None
    for idx, raw_line in enumerate(text.splitlines()):
        stripped = raw_line.lstrip()
        # A closing delimiter closes the fence BEFORE we record this line:
        # the delimiter itself is not part of the fenced body.
        if in_fence and (stripped.startswith("`" * 3) or stripped.startswith("~" * 3)):
            in_fence = False
            orphan_opener = None
            continue
        if not in_fence:
            # Open the fence on the next iteration.
            if (stripped.startswith("`" * 3) and len(stripped) >= 3) or (
                stripped.startswith("~" * 3) and len(stripped) >= 3
            ):
                in_fence = True
                orphan_opener = idx
            continue
        # We're inside a fence (opening was on a previous line, no closing on
        # this one). Add this line to the set.
        indices.add(idx)
    return indices, orphan_opener


def _paragraph_prefix(text: str, idx: int) -> str:
    """#13335: the markdown paragraph ABOVE line `idx` -- contiguous non-empty
    lines joined by newlines, read top-down. A blank line is a paragraph
    boundary (the acceptance's explicit cut: without it the window would climb
    the whole body and a stray "scan" three pages up would exempt everything).
    A fence delimiter line is also a boundary: a fenced block is transcription,
    never part of a prose paragraph (#11670 rationale)."""
    lines = text.splitlines()
    out: list[str] = []
    j = idx - 1
    while j >= 0:
        stripped = lines[j].strip()
        if not stripped:
            break  # blank line: paragraph boundary
        if stripped.startswith("`" * 3) or stripped.startswith("~" * 3):
            break  # fence delimiter: transcription boundary
        out.append(stripped)
        j -= 1
    return "\n".join(reversed(out))


def _paragraph_block(text: str, idx: int) -> str:
    """#13791: the markdown paragraph CONTAINING line `idx` -- the prefix of
    `_paragraph_prefix` PLUS the line PLUS the contiguous non-empty lines
    below it. Same boundaries (blank line, fence delimiter): a block is the
    maximal run of prose lines an author would read as one unit, which is the
    unit an additive enumeration spans ("- 1 fichier modifie (...)" /
    "- 1 fichier de test modifie (...)" on two bullets, founder #13736). The
    #13335 prefix alone could not see the lines BELOW the candidate -- and an
    additive enumeration lists downward."""
    lines = text.splitlines()
    if not 0 <= idx < len(lines):
        return ""
    low, hi = idx, idx
    while low - 1 >= 0:
        s = lines[low - 1].strip()
        if not s or s.startswith("`" * 3) or s.startswith("~" * 3):
            break
        low -= 1
    while hi + 1 < len(lines):
        s = lines[hi + 1].strip()
        if not s or s.startswith("`" * 3) or s.startswith("~" * 3):
            break
        hi += 1
    return "\n".join(l.strip() for l in lines[low:hi + 1])


def _extract_line_candidates(text: str) -> list[tuple[int, str]]:
    """Index-carrying core of extract_perimeter_assertions: returns
    (line_index, stripped_line) pairs so callers can re-attach body context
    (#13335 paragraph prefix) without re-parsing."""
    fence_indices, _unterminated = _fence_line_indices(text)
    candidates: list[tuple[int, str]] = []
    for idx, raw_line in enumerate(text.splitlines()):
        if idx in fence_indices:
            continue  # Issue #11670 founder case: L898 transcription, not an authorial claim
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith("|"):
            continue  # markdown table row: report structure, not an assertion
        low = line.lower()
        if COUNT_CLAIM.search(line):
            if _counts_all_quoted_or_codespan(line):
                continue  # citing a count (reported speech / code example), not claiming it
            candidates.append((idx, line))
            continue
        # #12024 / #11985 word-form extension: a body can declare its
        # perimeter with a spelled-out cardinal ("trois fichiers",
        # "five files"). Without this branch, the word form never enters
        # the candidate list and body_declares_effective_count is never
        # set for word-only declarations. Closed list FR/EN cardinals
        # 1-10 (see COUNT_WORDS rationale at line ~98).
        word_triggers = [
            (m, word)
            for word, _n, trig in WORD_FORM_TRIGGERS
            for m in trig.finditer(line)
        ]
        if word_triggers:
            # Same exclusion as numeric form: a word-form count cited inside
            # a code-span (`` `trois fichiers` ``) is an example, not an
            # authorial perimeter declaration. Founder case #12024: body v3
            # listed two illustrative examples between backticks, the
            # perimeter-review-guard flagged them as unverifiable assertions.
            # An all-in-codespan word-form pattern is reported display.
            if all(
                _trigger_in_quoted_or_codespan(line, m.start(), m.end() - m.start())
                for m, _ in word_triggers
            ):
                continue
            candidates.append((idx, line))
            continue
        if _has_exclusivity(low) and any(w in low for w in STRONG_SCOPE_WORDS):
            if _markers_all_quoted(line):
                continue  # quoting an exclusivity claim, not making one
            candidates.append((idx, line))
    return candidates


def extract_perimeter_assertions_with_context(text: str) -> list[tuple[str, str]]:
    """#13335: candidates paired with their enclosing paragraph prefix, for
    wrap-invariant classification. Same candidate set as
    extract_perimeter_assertions -- only the context differs."""
    return [
        (line, _paragraph_prefix(text, idx))
        for idx, line in _extract_line_candidates(text)
    ]


def extract_perimeter_assertions_with_block(text: str) -> list[tuple[str, str, str]]:
    """#13791: candidates paired with (paragraph prefix, enclosing paragraph
    BLOCK). The block extends the #13335 prefix to the lines BELOW the
    candidate -- the unit an additive enumeration ("- 1 fichier modifie" /
    "- 1 fichier de test modifie" on two bullets, founder #13736) spans.
    Same candidate set; only the carried context differs."""
    return [
        (line, _paragraph_prefix(text, idx), _paragraph_block(text, idx))
        for idx, line in _extract_line_candidates(text)
    ]


def extract_perimeter_assertions(text: str) -> list[str]:
    """Pull candidate perimeter assertions from review/PR prose.

    Line-based by design: perimeter statements sit on their own line (the
    report template's ``**Fichiers:** N fichiers modifiés``, the founding
    ``**Périmètre** : 2 fichiers twins uniquement, aucune autre
    modification.``). A line is a candidate when it carries a file-count
    claim, or an exclusivity marker AND a strong scope word. Lines with
    neither are not perimeter assertions and are skipped.

    Two citation shapes are skipped (measured on this tool's own PR #11635,
    dogfooded 2026-08-18 -- its evidence table quotes the founding sentence
    and the guard flagged its own PR against its own 4-file list):

    1. **Markdown table rows** (lines starting with ``|``): tables are
       report/summary structures (evidence matrices, status boards); a
       perimeter assertion is prose. The review template's line is a bullet,
       not a cell.
    2. **Candidacy fully quoted**: the trigger that made the line a
       candidate (count claim, or exclusivity markers) sits inside
       ``« ... »`` / ``" ... "`` -- the line quotes someone else's
       assertion instead of making one. One unquoted trigger keeps the line
       live.

    A ``#N`` backlink in the line is NOT an exemption: the founding #11227
    Hermes sentence carries an inline issue ref (#2874) in the same line and
    must stay caught -- a backlink exemption would also be a trivial
    evasion.
    """
    # #13335: core moved to _extract_line_candidates (index-carrying) so the
    # paragraph context can be attached without changing this public shape.
    return [line for _, line in _extract_line_candidates(text)]


def _check_unterminated_fence(text: str) -> bool:
    """Return True iff a fence was opened but never closed before EOF.

    CommonMark renders an unterminated fence to EOF, which is correct
    behaviour at the rendering layer. Downstream of the perimeter scan, it
    is a silent-no-op: every line after the orphan opener is excluded from
    candidacy, and the gate becomes a no-op for the rest of the body. Issue
    #11678 makes this distinction visible: "no candidates found" is no
    longer indistinguishable from "no candidates read". This wraps
    `_fence_line_indices` and discards the index set AND the opener line
    (#11723), keeping the boolean for callers that only need "is there an
    orphan" -- callers that need to localize it read `_fence_line_indices`
    directly.
    """
    _, unterminated = _fence_line_indices(text)
    return unterminated is not None


def _format_signal_explanation(candidates: list[Candidate]) -> str:
    """#11796: the trailing explanation of a SIGNAL block must match the
    composition of the candidates. The original wording printed "assertion
    d'un tiers : a lever par son auteur" UNCONDITIONALLY -- which is wrong
    when every signal is an INCIDENTAL count from the AUTHOR's own body
    (PRs #11786 / #11775): the author cannot "lever" their own incidental
    count, the count is what it is.

    Three shapes:

    - body+incidental only -> the author wrote it, but the count is not a
      perimeter claim (LOCATIVE_PREP, threshold, zero, etc.). Nothing to
      lever; the reviewer notes it.
    - thread only -> a reviewer/bot posted a false perimeter claim. The
      reviewer is the only one who can correct their own review.
    - mixed -> both shapes, each cited with its actual reason.

    FN safety: this function only formats; it does not change which
    candidates are blocking (that's `Candidate.blocking`). A candidate that
    is `blocking=True` never enters `signals` in `main()` -- so by
    construction, every candidate here is either body+incidental or thread.
    """
    has_body_incidental = any(
        c.source == "body" for c in candidates
    )
    has_thread = any(c.source == "thread" for c in candidates)

    if has_body_incidental and not has_thread:
        return (
            "Compte(s) INCIDENTAL du body de l'auteur (inventaire, scan scope, "
            "seuil cite, attestation de zero -- #11712) : pas une assertion "
            "de perimetre. Le reviewer qui merge le considere. Ne tient "
            "pas la PR."
        )
    if has_thread and not has_body_incidental:
        return (
            "Assertion d'un tiers (reviewer ou bot) non editable par "
            "l'auteur : a lever par son auteur (poster une assertion "
            "corrigee). Ne tient pas la PR."
        )
    # Mixed: name both shapes with their actual reason.
    return (
        "Mix : compte(s) INCIDENTAL du body de l'auteur (ci-dessus, pas "
        "une assertion de perimetre) + assertion(s) d'un tiers (a lever "
        "par leur auteur). Ne tient pas la PR."
    )


def _render_carried_note(carried: Optional[CarriedNote]) -> list[str]:
    """#13637 step 1+3: explain the subtracted carried files and surface the
    stale-base signal. A cardinal that changes must say WHY, not move silently
    -- otherwise the defect is displaced, not closed. The stale-base note is
    free signal: API count − propre count is a more direct stale-base indicator
    than `base-stale-14d`."""
    if carried is None or not carried.charries:
        return []
    m = len(carried.charries)
    age = carried.base_age_hours
    if age is not None:
        age_txt = f"~{age} h" if age < 48 else f"~{age // 24} j"
        note = f"  — dont {m} charrié(s) d'une base vieille de {age_txt}, non compté(s)"
    else:
        note = f"  — dont {m} charrié(s) de main, non compté(s)"
    lines = [note]
    lines.append(
        "  — charrié(s) de main (la tête est déjà d'accord avec main, la PR ne les "
        "modifie pas) : " + ", ".join(f["path"] for f in carried.charries)
    )
    lines.append(
        "  -> STALE-BASE : l'écart liste API − périmètre propre ("
        f"{m}) signale une base en retard sur un main actif ; la liste effective "
        "ci-dessus ne compte que les fichiers que la PR modifie réellement."
    )
    return lines


def format_report(report: Report, assertion: Optional[str], carried: Optional[CarriedNote] = None) -> str:
    # Default to the field the report carries; an explicit override lets callers
    # display a partition they computed themselves (e.g. in tests).
    if carried is None:
        carried = report.carried
    lines = []
    head = f"Périmètre effectif : {len(report.files)} fichier(s)"
    lines.append(head)
    lines.extend(_render_carried_note(carried))
    for f in sorted(report.files, key=lambda x: x["path"]):
        lines.append(f"  {f.get('additions', '?')}+/{f.get('deletions', '?')}-  {f['path']}")
    wf = [f for f in report.files if f["path"].startswith(WORKFLOW_PREFIX)]
    lines.append("")
    if wf:
        lines.append("WORKFLOWS CI TOUCHÉS (s'appliquent à toutes les PRs suivantes) :")
        for f in wf:
            lines.append(f"  - {f['path']}")
    else:
        lines.append("Workflows CI touchés : aucun.")
    lines.append("")
    if report.moves:
        lines.append("MOUVEMENTS DE BASELINE / SEUIL :")
        lines.extend(m.render() for m in report.moves)
    else:
        lines.append("Mouvements de baseline/seuil : aucun.")
    if assertion:
        lines.append("")
        lines.append(f"Assertion confrontée : « {assertion} »")
        if report.problems:
            lines.append("ÉCARTS :")
            lines.extend(f"  !! {p}" for p in report.problems)
        else:
            lines.append("Assertion cohérente avec la liste effective.")
    return "\n".join(lines)


def _run_gh(args: list[str]) -> str:
    gh = shutil.which("gh")
    if not gh:
        print("gh introuvable", file=sys.stderr)
        sys.exit(2)
    proc = subprocess.run([gh, *args], capture_output=True, text=True, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        print(f"gh error: {proc.stderr.strip()[:400]}", file=sys.stderr)
        sys.exit(2)
    return proc.stdout


def _normalize_rest_files(items: list[dict]) -> list[dict]:
    """Map REST pulls/files items onto the ``path``/``additions``/``deletions``
    shape the rest of the guard reads (``gh pr view --json files`` field names)."""
    return [
        {
            "path": it.get("filename"),
            "additions": it.get("additions"),
            "deletions": it.get("deletions"),
        }
        for it in (items or [])
    ]


def _branch_ref_exists(ref: str) -> bool:
    """True when ``ref`` (e.g. ``origin/main``) resolves locally."""
    proc = subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", ref],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    return proc.returncode == 0


def _pr_head_sha(pr: int) -> Optional[str]:
    try:
        return json.loads(_run_gh(["pr", "view", str(pr), "--json", "headRefOid"]))["headRefOid"]
    except SystemExit:
        return None


def _pr_base_ref(pr: int) -> Optional[str]:
    try:
        return json.loads(_run_gh(["pr", "view", str(pr), "--json", "baseRefName"]))["baseRefName"]
    except SystemExit:
        return None


def _resolve_base_pair(pr: int) -> tuple[Optional[str], Optional[str]]:
    """Return (head_sha, base_ref) or (None, None). ``base_ref`` is the local
    ``origin/<baseRefName>``, fetched if the checkout lacks it (a PR runner
    checks out the merge ref but may not have the base branch fetched)."""
    head = _pr_head_sha(pr)
    base = _pr_base_ref(pr)
    if not head or not base:
        return None, None
    ref = f"origin/{base}"
    if not _branch_ref_exists(ref):
        subprocess.run(
            ["git", "fetch", "origin", base],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
        )
        if not _branch_ref_exists(ref):
            return None, None
    return head, ref


def _base_age_hours(base_ref: str, head: str) -> Optional[int]:
    """Age in whole hours of the branch's divergence point from main (the
    merge-base date). None when unresolvable -- the carried note then omits the
    age rather than inventing one."""
    mb = subprocess.run(
        ["git", "merge-base", base_ref, head],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if mb.returncode != 0 or not mb.stdout.strip():
        return None
    d = subprocess.run(
        ["git", "show", "-s", "--format=%ct", mb.stdout.strip()],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if d.returncode != 0 or not d.stdout.strip():
        return None
    try:
        ts = int(d.stdout.strip())
    except ValueError:
        return None
    return max(0, (int(time.time()) - ts)) // 3600


def _classify_carried(pr: int, files: list[dict]) -> CarriedNote:
    """#13637: partition ``files`` (the API list) into the PR's own contribution
    and the carried files.

    GitHub's ``/pulls/N/files`` diffs the base tip -> head, so a branch that
    merged ``main`` has ``main``'s own changes attributed to it (#13601: 04-7
    showed as ``+2708/-2708`` although the PR did not touch it). A file is the
    PR's OWN work iff the head differs from main on it; ``git diff
    origin/<base> <head> -- p`` empty => carried.

    Fail-safe: on any resolution failure (base ref unfetchable, head unknown,
    git error) returns an empty ``charries`` -- no file is ever wrongly
    excluded, the fallback is the pre-fix behaviour.
    """
    if not files:
        return CarriedNote(propres=files, charries=[], base_age_hours=None)
    head, base_ref = _resolve_base_pair(pr)
    if not head:
        return CarriedNote(propres=files, charries=[], base_age_hours=None)
    api_paths = sorted({f["path"] for f in files if f.get("path")})
    if not api_paths:
        return CarriedNote(propres=files, charries=[], base_age_hours=None)
    proc = subprocess.run(
        ["git", "diff", "--name-only", base_ref, head, "--"] + api_paths,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return CarriedNote(propres=files, charries=[], base_age_hours=None)
    changed = set(proc.stdout.splitlines())
    carried = set(api_paths) - changed
    propres, charries = partition_propres(files, carried)
    return CarriedNote(
        propres=propres, charries=charries, base_age_hours=_base_age_hours(base_ref, head)
    )


def is_pr_own_file(pr: int, path: str, head: Optional[str] = None, base_ref: str = "origin/main") -> Optional[bool]:
    """#13637 step 2: the exposed callable predicate.

    True when ``path`` is the PR's OWN contribution (the head differs from main
    on it); False when carried (the head already agrees with main -- main
    changed it and the branch merged it); None when the predicate cannot be
    resolved. This is what collision checks re-implement by hand on
    ``--json files`` today; call this instead.
    """
    if head is None:
        head = _pr_head_sha(pr)
    if head is None:
        return None
    if not _branch_ref_exists(base_ref):
        refreshed = _resolve_base_pair(pr)
        if parsed := refreshed[1]:
            base_ref = parsed
        else:
            return None
    proc = subprocess.run(
        ["git", "diff", "--quiet", base_ref, head, "--", path],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode == 1:
        return True
    if proc.returncode == 0:
        return False
    return None


def fetch_report(pr: int) -> Report:
    # ``gh pr view --json files`` caps at 100 entries (single page), so the
    # guard used to confront bodies against a TRUNCATED list on >100-file PRs:
    # #13357 carries 148 real files, the capped list read 100, and the honest
    # body count failed against the truncation -- an unwinnable guard. The
    # REST endpoint paginates; ``--paginate`` without ``-q`` merges the pages
    # into one JSON array (same pattern as candidate_delivered.py, #10488).
    repo = json.loads(
        _run_gh(["repo", "view", "--json", "nameWithOwner"])
    )["nameWithOwner"]
    items = json.loads(_run_gh([
        "api", f"repos/{repo}/pulls/{pr}/files", "--paginate",
    ]))
    files = _normalize_rest_files(items)
    # #13637: subtract files carried from a stale main the branch merged. The
    # effective perimeter is the PR's OWN contribution. A cardinal that changes
    # is explained in the rendered output (see _render_carried_note), not
    # silently masked.
    carried = _classify_carried(pr, files)
    if carried.charries:
        files = carried.propres
    diff = _run_gh(["pr", "diff", str(pr)])
    return Report(files=files, moves=extract_baseline_moves(diff), carried=carried)


def fetch_review_thread(pr: int) -> list[dict]:
    """PR body + top-level review bodies -- the surfaces that carry perimeter assertions.

    Inline review comments are deliberately not scanned (v1): the perimeter
    statement lives in the review body or the PR body. ``gh pr view --json
    reviews`` returns the review objects with body/state/author.

    Each item carries ``source`` -- "body" or "thread" -- which decides whether
    a false assertion BLOCKS or merely SIGNALS (#11648-b2), and ``ts`` so that
    an author's later assertion can supersede their earlier one (#11648-b1).
    """
    meta = json.loads(
        _run_gh(["pr", "view", str(pr), "--json", "body,reviews,author"])
    )
    pr_author = (meta.get("author") or {}).get("login", "pr-author")
    items: list[dict] = [{
        "kind": "PR body",
        "author": pr_author,
        "body": meta.get("body") or "",
        "source": "body",
        "ts": "",
    }]
    for rv in meta.get("reviews") or []:
        items.append({
            "kind": f"review ({rv.get('state')})",
            "author": rv.get("author", {}).get("login", "?"),
            "body": rv.get("body") or "",
            "source": "thread",
            "ts": rv.get("submittedAt") or "",
        })
    return items


def _first_confrontable_count(text: str) -> Optional[int]:
    """The count `check_assertion` would confront for this text: the first
    non-zero file-count claim outside fences (None when there is none)."""
    scan_target = _fence_mask(text)
    mm = next(
        (m for m in COUNT_CLAIM.finditer(scan_target) if int(m.group(1)) != 0),
        None,
    )
    return int(mm.group(1)) if mm else None


# A count-mismatch problem starts with this prefix (the wording is ours, in
# check_assertion). Used by the #11985 body-level downgrade to reclassify ONLY
# count mismatches -- exclusivity violations (#11268-2) and unverifiable
# wordings keep their blocking force in every case.
COUNT_MISMATCH_PREFIX = "l'assertion pretend"


def is_downgradable_mismatch(cand: "Candidate", problem: str) -> bool:
    """#11985 regle 1: a blocking count-mismatch from a body that ALSO
    declares the effective count elsewhere is reclassified to SIGNAL. The
    rule never disarms: it fires only on count mismatches (never on the
    #11268-2 workflow criterion) and only when a DECLARATIVE candidate of the
    same body states the effective count -- an incidental scan scope carrying
    the right number by coincidence does not validate a wrong header."""
    return (
        cand.blocking
        and cand.body_declares_effective_count
        and problem.startswith(COUNT_MISMATCH_PREFIX)
    )


@dataclass
class Candidate:
    """One perimeter assertion, with what decides its consequence."""

    text: str
    kind: str
    author: str
    source: str  # "body" (author-controlled -> blocking) | "thread" (signal)
    ts: str = ""
    # #11985 regle 1: True when the SAME body carries another, DECLARATIVE
    # candidate whose count EQUALS the effective file count. The body then
    # asserts its perimeter correctly somewhere; its other count mismatches
    # (atomicity arguments, produced artifacts, scan residues) are reclassified
    # from blocking to signal by the caller. Filled by `select_candidates`
    # when given `n_files`; the `blocking` property below is untouched.
    body_declares_effective_count: bool = False
    # #13335: enclosing paragraph prefix (see _paragraph_prefix), filled by
    # select_candidates from the full body text. Feeds only the
    # MEASUREMENT_ANTECEDENT exemption -- wrap-invariance of the verdict.
    context: str = ""
    # #13791: enclosing paragraph BLOCK (see _paragraph_block) -- prefix +
    # line + the contiguous lines below. Feeds only the additive-enumeration
    # confrontation in check_assertion: an enumeration spanning two bullets
    # sums across the block, not the single line.
    block: str = ""
    # #13946: the full body text -- the hors-scope forecast line and the
    # positive perimeter declaration can sit in DIFFERENT paragraphs (the
    # forecast annotates « (hors scope PR) », the perimeter names
    # « touche N » elsewhere), and the block is then useless for the
    # cross-paragraph scan. Filled by select_candidates when given
    # ``n_files``; consumed only by the ``_first_touche_n`` fallback
    # inside check_assertion.
    body_text: str = ""

    @property
    def blocking(self) -> bool:
        """Only the PR body blocks.

        #11648-b2: a gate blocks on what its target can fix. The PR author owns
        the body and can edit it -- and since #11654 an edit re-triggers the
        workflow, so the green is reachable. A third-party review is NOT
        editable by the author, and a COMMENTED review cannot even be
        dismissed (dismissal applies to APPROVED/CHANGES_REQUESTED only), so
        blocking there leaves no lever at all -- measured on #11642 and #11646.

        #11712: an INCIDENTAL count from the body does not block either --
        inventory ("22 fichiers MP3"), scan scope ("grep ... sur 73 fichiers"),
        cited threshold ("< 15 fichiers") or zero-attestation ("0 fichier
        machine-path"). It stays extracted, confronted and printed as a
        SIGNAL; only the exit code moved (the #11648 path). 11/120 PRs
        carried >= 2 distinct counts, making a red guaranteed regardless
        of the real perimeter.
        """
        return self.source == "body" and not _is_incidental_assertion(
            self.text, self.context
        )


def select_candidates(
    items: list[dict], n_files: Optional[int] = None
) -> tuple[list[Candidate], int | None]:
    """Extract assertions, keeping only each thread author's LAST ones.

    #11648-b1 (supersession). The founding measurement: on #11646 the guard
    confronted three assertions, two of which their own author had already
    corrected -- ai-01 said "5 fichiers" at 14:29 then "7" (correct) at 14:48,
    and the stale one still held the PR red. An author who corrects themselves
    must extinguish their own red; that is the one lever that acts only on
    oneself, so it is safe to grant.

    "Last" means the most recent review of that author which actually carries
    an assertion -- a later review that says nothing about the perimeter is
    silence, not a retraction. The PR body is never superseded: there is only
    one of it, and it is always the current text.

    Returns (candidates, orphan_opener_line). The latter is the 0-based line
    index of the FIRST body-scanning-order body that had a fence opened but
    never closed before EOF (None when every body is clean) -- the
    silent-no-op shape #11678 measured on #11675/serde, localized per #11723.
    The flag does NOT change the gate's verdict (CommonMark-fence-to-EOF is
    correct rendering); it makes the false-negative shadow visible to the
    reviewer AND actionable (the author is told which line to close).

    #11985 regle 1: when `n_files` is given, each body's candidates get
    `body_declares_effective_count` set iff a DECLARATIVE (non-incidental)
    candidate of that same body states the effective count. The body then
    asserts its perimeter correctly somewhere, and the caller reclassifies
    that body's other count mismatches as signals.
    """
    body_items = [i for i in items if i.get("source") != "thread"]
    thread_items = [i for i in items if i.get("source") == "thread"]

    out: list[Candidate] = []
    orphan_opener: int | None = None
    for item in body_items:
        body = item["body"]
        if orphan_opener is None:
            _, opener = _fence_line_indices(body)
            if opener is not None:
                orphan_opener = opener
        body_candidates = [
            Candidate(
                text, item["kind"], item["author"], "body",
                context=ctx, block=blk, body_text=body,
            )
            for text, ctx, blk in extract_perimeter_assertions_with_block(body)
        ]
        if n_files is not None and any(
            not _is_incidental_assertion(c.text, c.context)
            and _first_confrontable_count(c.text) == n_files
            for c in body_candidates
        ):
            for c in body_candidates:
                c.body_declares_effective_count = True
        # #11985 / #12024 rule 1 word-form extension: a body can declare its
        # perimeter with a spelled-out cardinal ("trois fichiers", "five
        # files"). The numeric scan above misses this entirely (false
        # negative: a PR body that says "Trois fichiers (+184/-3)" never
        # gets body_declares_effective_count set). Mirror the numeric check
        # for COUNT_WORDS (closed list FR/EN cardinals 1-10 -- see line ~98
        # rationale).
        if n_files is not None and not any(
            c.body_declares_effective_count for c in body_candidates
        ):
            for word, n, pat in WORD_FORM_TRIGGERS:
                if n != n_files:
                    continue
                if any(
                    not _is_incidental_assertion(c.text, c.context)
                    and pat.search(c.text)
                    for c in body_candidates
                ):
                    for c in body_candidates:
                        c.body_declares_effective_count = True
                    break
        out.extend(body_candidates)

    # Per thread author, keep the latest assertion-carrying review.
    latest: dict[str, tuple[str, int, dict, list[str]]] = {}
    for pos, item in enumerate(thread_items):
        body = item["body"]
        found = extract_perimeter_assertions(body)
        if not found:
            continue
        author = item["author"]
        key = (item.get("ts") or "", pos)
        if author not in latest or key > (latest[author][0], latest[author][1]):
            latest[author] = (key[0], key[1], item, found)

    for author in sorted(latest):
        _, _, item, found = latest[author]
        for text in found:
            out.append(
                Candidate(text, item["kind"], author, "thread", item.get("ts") or "")
            )
    return out, orphan_opener


def main() -> int:
    ap = argparse.ArgumentParser(description="Perimeter truth-source for PR reviews (#11268)")
    ap.add_argument("pr", type=int, help="PR number")
    ap.add_argument("--assert", dest="assertion", help="draft perimeter assertion to confront")
    ap.add_argument(
        "--scan-thread",
        action="store_true",
        help="scan the PR body + top-level reviews for perimeter assertions and "
             "confront each with the effective file list (the wiring that makes "
             "a false assertion -- #11227's '2 fichiers twins uniquement' -- "
             "impossible to leave unblocked, #11268-4). Baseline moves are "
             "reported with direction but do NOT block here: the output names "
             "them and the reviewer applies CHANGES_REQUESTED on unjustified "
             "loosening.",
    )
    ap.add_argument(
        "--baseline-justified",
        dest="justified",
        help="written justification accepting a LOOSEN move (else exit 1)",
    )
    args = ap.parse_args()

    report = fetch_report(args.pr)
    if args.assertion:
        report.problems.extend(check_assertion(report.files, args.assertion))
    signals: list[str] = []
    orphan_opener: int | None = None
    if args.scan_thread:
        candidates, body_orphan = select_candidates(
            fetch_review_thread(args.pr), n_files=len(report.files)
        )
        if body_orphan is not None:
            orphan_opener = body_orphan
        for cand in candidates:
            # #13946: pass the candidate's full body text as ``body_hint``
            # so the « touche N » fallback can search across paragraphs --
            # the perimeter declaration often sits in a SEPARATE paragraph
            # from the hors-scope forecast the body uses to disambiguate.
            # The fallback is only consulted when COUNT_CLAIM + word-form
            # fall through after the hors-scope filter.
            for p in check_assertion(
                report.files, cand.text, block=cand.block, body_hint=cand.body_text
            ):
                line = f"[{cand.kind} / {cand.author}] {p}"
                # Every catch stays visible either way -- the detector is not
                # disarmed, only its consequence is placed where it can be
                # acted on (#11648). #11985 regle 1: a count mismatch from a
                # body that declares the effective count elsewhere is a
                # signal, not a block -- the body asserts its perimeter
                # correctly; the mismatched count denotes another object
                # (atomicity argument, produced artifact, scan residue).
                if cand.blocking and not is_downgradable_mismatch(cand, p):
                    report.problems.append(line)
                else:
                    signals.append(line)

    blocking = list(report.problems)
    if not args.justified and not args.scan_thread:
        for m in report.moves:
            if m.direction == "LOOSEN":
                blocking.append(
                    f"desserrement de {m.key} ({m.old} -> {m.new}) sans --baseline-justified "
                    "=> CHANGES_REQUESTED sauf justification ecrite dans la PR (#11268-3)"
                )

    print(format_report(report, args.assertion))
    if signals:
        print("")
        print("SIGNAL (non bloquant -- assertion d'un tiers non editable par l'auteur,")
        print("        ou compte INCIDENTAL du body : inventaire, perimetre de scan,")
        print("        seuil cite, attestation de zero -- #11712) :")
        for sg in signals:
            print(f"  ~~ {sg}")
        # #11796: the trailing explanation must match the composition of the
        # signals. All body+incidental -> "not a perimeter claim, just a
        # note"; all thread -> "tier to correct"; mixed -> both. The old
        # blanket phrase was wrong for the all-body case (#11786 / #11775).
        print(f"  -> {_format_signal_explanation(candidates)}")
    if orphan_opener is not None:
        # #11678: the body scanned had an unterminated fence. CommonMark
        # renders it to EOF (correct behaviour, what GitHub does), but the
        # downstream perimeter scan sees an empty second half. Emit a
        # non-blocking notice so the reviewer can ask the author to close
        # the fence or split the body. A scan with 0 candidates and an
        # unterminated fence is a different shape from a scan with 0
        # candidates and a clean read -- the former is suspect, the latter
        # is just clean. #11723: the notice names the orphan opener's line
        # (1-based for the human reading the PR body in a browser/editor) --
        # a signal that does not localize gets watched, not acted on.
        print("")
        print(f"UNFINISHED_FENCE: orphan opener at line {orphan_opener + 1} (1-based)")
        print("  -> le body de la PR contient une fence ``` ou ~~~ non fermee,")
        print(f"     ouverte a la ligne {orphan_opener + 1} et jamais fermee.")
        print("     CommonMark la rend jusqu'en fin de body, ce qui est correct ;")
        print("     mais le scan de perimetre a ignore toutes les lignes qu'elle")
        print("     enferme. Demander a l'auteur de fermer la fence (ou de la")
        print("     supprimer) avant de considerer la PR comme scannee.")
    if blocking:
        print("")
        print("VERDICT: FAIL")
        for b in blocking:
            print(f"  !! {b}")
        return 1
    print("")
    print("VERDICT: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
