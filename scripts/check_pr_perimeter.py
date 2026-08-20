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


def _has_exclusivity(low: str) -> bool:
    """Exclusivity check shared by extraction and assertion checking.

    `low` is the lowercased line. French/phrase markers are substring-matched;
    "only" requires word boundaries AND no hyphen/word char before it.
    """
    return (any(m in low for m in _SUBSTRING_MARKERS)
            or bool(_ONLY_STANDALONE.search(low)))


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


def check_assertion(files: list[dict], assertion: str) -> list[str]:
    """Confront a perimeter assertion with the effective file list.

    Fence blocks (transcribed commands, L898 proof) are masked out of the
    scan (#11695). The final "non verifiable" guard therefore fires for a
    body composed only of fence transcriptions: no claim OUTSIDE fences
    means no verifiable author assertion, and such a body must not pass
    in silence.
    """
    problems: list[str] = []
    # A zero count is never the perimeter. On a mixed line -- "0 fichier
    # catalogue, 2 fichiers touches" -- the claim under test is the non-zero
    # one; reading the first match confronts "0" with a file list that cannot
    # be empty, so the line could never pass whatever the PR contained. This
    # is the FINDING raised in review of #11730 (#11735): the fence mask fixed
    # WHERE we scan, this fixes WHICH count we scan for. Both are needed.
    scan_target = _fence_mask(assertion)
    count_claim = next(
        (mm for mm in COUNT_CLAIM.finditer(scan_target) if int(mm.group(1)) != 0),
        None,
    )
    if count_claim:
        claimed = int(count_claim.group(1))
        if claimed != len(files):
            problems.append(
                f"l'assertion pretend {claimed} fichier(s), la liste effective en compte {len(files)} : "
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
    if not count_claim and not exclusive:
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
INCIDENTAL_QUALIFIERS = frozenset({
    "mp3", "wav", "mathlib", "machine-path", "fr", "en", "scratch",
    "restants", "restant", "reste", "restants,", "nouveau", "nouveaux",
    "nouvelle", "nouvelles", "varies", "variés", "synthetiques",
    "synthétiques", "scripts", "cache", "generes", "générés", "produits",
    "produites", "sources", "source",
})
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
    return any(
        re.search(rf"\b{re.escape(w)}\b", low, re.IGNORECASE)
        for w in STRONG_SCOPE_WORDS
    )


def _count_is_incidental(line: str) -> bool:
    """True when every count on the line denotes something other than the PR's
    file list. Caller-facing guarantee: a line with a scope word or a diffstat
    neighborhood is NEVER incidental via the qualifier/locative rules (FN
    safety, #11712 acceptance). Two shapes override even those guards, because
    they can never be validated by the guard's EQUALITY confrontation anyway:
    a zero count (a PR never has 0 files) and a comparison-prefixed count
    ("< 15 fichiers" cites a threshold; the guard confronts claimed ==
    len(files), which "<" is not)."""
    low = line.lower()
    matches = list(COUNT_CLAIM.finditer(line))
    if not matches:
        return False
    first = matches[0]
    first_before = line[: first.start()].rstrip()
    if int(first.group(1)) == 0 or COMPARISON_PREFIX.search(first_before):
        return True
    if _has_strong_scope(low) or DIFFSTAT_NEIGHBORHOOD.search(line):
        return False
    for m in matches:
        claimed = int(m.group(1))
        if claimed == 0:
            continue  # "0 fichier X" is a scrub/absence attestation
        before = line[: m.start()].rstrip()
        if COMPARISON_PREFIX.search(before):
            continue  # "< N fichiers" cites a threshold
        if LOCATIVE_PREP.search(line):
            continue  # scan scope: "grep ... sur N fichiers"
        # #11800: per-count negation tail-check. The match's tail is the
        # segment immediately after the count -- if it starts with a
        # negation word, this specific count is an attestation of
        # unchanged files, not a perimeter claim. Scope is per-COUNT so
        # that a line like "5 fichiers modifies, 91 fichiers inchanges"
        # keeps its blocking 5-files count (the "modifies" tail is not a
        # negation word).
        after = line[m.end():]
        if NEGATED_DIFF_TAIL.match(after):
            continue
        mw = re.match(r"\s+([\wàâäéèêëîïôöùûüçÀÂÄÉÈÊËÎÏÔÖÙÛÜÇ-]+)", after)
        if mw and mw.group(1).lower() in INCIDENTAL_QUALIFIERS:
            continue  # "N fichiers MP3/scratch/restants/..." -- kind or remainder
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


def _is_incidental_assertion(text: str) -> bool:
    """#11712: kept in candidates (found + printed), excluded from blocking."""
    if COUNT_CLAIM.search(text):
        return _count_is_incidental(text)
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
    fence_indices, _unterminated = _fence_line_indices(text)
    candidates: list[str] = []
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
            if _counts_all_quoted(line):
                continue  # quoting a count (reported speech), not claiming it
            candidates.append(line)
            continue
        if _has_exclusivity(low) and any(w in low for w in STRONG_SCOPE_WORDS):
            if _markers_all_quoted(line):
                continue  # quoting an exclusivity claim, not making it
            candidates.append(line)
    return candidates


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


def format_report(report: Report, assertion: Optional[str]) -> str:
    lines = []
    lines.append(f"Périmètre effectif : {len(report.files)} fichier(s)")
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
    proc = subprocess.run([gh, *args], capture_output=True, text=True)
    if proc.returncode != 0:
        print(f"gh error: {proc.stderr.strip()[:400]}", file=sys.stderr)
        sys.exit(2)
    return proc.stdout


def fetch_report(pr: int) -> Report:
    files_json = _run_gh(["pr", "view", str(pr), "--json", "files"])
    files = json.loads(files_json)["files"]
    diff = _run_gh(["pr", "diff", str(pr)])
    return Report(files=files, moves=extract_baseline_moves(diff))


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


@dataclass
class Candidate:
    """One perimeter assertion, with what decides its consequence."""

    text: str
    kind: str
    author: str
    source: str  # "body" (author-controlled -> blocking) | "thread" (signal)
    ts: str = ""

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
        return self.source == "body" and not _is_incidental_assertion(self.text)


def select_candidates(items: list[dict]) -> tuple[list[Candidate], int | None]:
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
        for text in extract_perimeter_assertions(body):
            out.append(Candidate(text, item["kind"], item["author"], "body"))

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
        candidates, body_orphan = select_candidates(fetch_review_thread(args.pr))
        if body_orphan is not None:
            orphan_opener = body_orphan
        for cand in candidates:
            for p in check_assertion(report.files, cand.text):
                line = f"[{cand.kind} / {cand.author}] {p}"
                # Every catch stays visible either way -- the detector is not
                # disarmed, only its consequence is placed where it can be
                # acted on (#11648).
                if cand.blocking:
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
