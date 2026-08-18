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


def check_assertion(files: list[dict], assertion: str) -> list[str]:
    """Confront a perimeter assertion with the effective file list."""
    problems: list[str] = []
    count_claim = COUNT_CLAIM.search(assertion)
    if count_claim:
        claimed = int(count_claim.group(1))
        if claimed != len(files):
            problems.append(
                f"l'assertion pretend {claimed} fichier(s), la liste effective en compte {len(files)} : "
                + ", ".join(f["path"] for f in files)
            )
    exclusive = any(marker in assertion.lower() for marker in EXCLUSIVITY_MARKERS)
    if exclusive:
        for f in files:
            if f["path"].startswith(WORKFLOW_PREFIX):
                base = f["path"].rsplit("/", 1)[-1]
                if base not in assertion:
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
    candidates: list[str] = []
    for line in text.splitlines():
        line = line.strip()
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
        if any(m in low for m in EXCLUSIVITY_MARKERS) and any(w in low for w in STRONG_SCOPE_WORDS):
            if _markers_all_quoted(line):
                continue  # quoting an exclusivity claim, not making it
            candidates.append(line)
    return candidates


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
    """
    meta = json.loads(_run_gh(["pr", "view", str(pr), "--json", "body,reviews"]))
    items: list[dict] = [{"kind": "PR body", "author": "pr-author", "body": meta.get("body") or ""}]
    for rv in meta.get("reviews") or []:
        items.append({
            "kind": f"review ({rv.get('state')})",
            "author": rv.get("author", {}).get("login", "?"),
            "body": rv.get("body") or "",
        })
    return items


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
    if args.scan_thread:
        for item in fetch_review_thread(args.pr):
            for cand in extract_perimeter_assertions(item["body"]):
                for p in check_assertion(report.files, cand):
                    report.problems.append(f"[{item['kind']} / {item['author']}] {p}")

    blocking = list(report.problems)
    if not args.justified and not args.scan_thread:
        for m in report.moves:
            if m.direction == "LOOSEN":
                blocking.append(
                    f"desserrement de {m.key} ({m.old} -> {m.new}) sans --baseline-justified "
                    "=> CHANGES_REQUESTED sauf justification ecrite dans la PR (#11268-3)"
                )

    print(format_report(report, args.assertion))
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
