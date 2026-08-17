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
    python scripts/check_pr_perimeter.py <PR#> --baseline-justified "accepted debt, see #N"

The pure core (assertion checking, baseline parsing) is unit-tested without
network in ``scripts/tests/test_check_pr_perimeter.py``; the gh wiring is
exercised on real PRs (see the PR that introduced this file).
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


def main() -> int:
    ap = argparse.ArgumentParser(description="Perimeter truth-source for PR reviews (#11268)")
    ap.add_argument("pr", type=int, help="PR number")
    ap.add_argument("--assert", dest="assertion", help="draft perimeter assertion to confront")
    ap.add_argument(
        "--baseline-justified",
        dest="justified",
        help="written justification accepting a LOOSEN move (else exit 1)",
    )
    args = ap.parse_args()

    report = fetch_report(args.pr)
    if args.assertion:
        report.problems.extend(check_assertion(report.files, args.assertion))

    blocking = list(report.problems)
    if not args.justified:
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
