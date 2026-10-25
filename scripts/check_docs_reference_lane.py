#!/usr/bin/env python3
"""Verify the perennial-reference lane convention -- issue #14623 (sens perenne).

This is the mirror of ``check_docs_transients_lane.py`` for the *perennial*
direction: the living reference documents under ``docs/`` (outside the transient
lane and the archive) that must carry the marking

    > REFERENCE — vivante — dernière révision <date>

The issue's defect 2 was that, at a glance, one could not tell whether a file
was a dated report (transient) or a living reference (perennial); a marking that
nothing checks is a declaration, so this organ is the measurable half. Convention
and rationale: ``docs/transients/README.md`` (section "Sens perenne").

Two directions are checked:

  integrity   every perennial document that CARRIES the header in header
              position must have ``<date>`` agree with ``git log -1 --format=%cs``
              of the file itself -- the date is read from git history, never
              recopied. A mismatch means the document was revised after the
              header was written without refreshing it (stale) or the date was
              fabricated. A failing ``git log`` is a finding (``GIT_LOG_FAILED``),
              never a silent pass.
  coverage    a monotone ratchet: the number of perennial documents carrying the
              header must not drop below ``--baseline`` (default the first wave
              of 9, ``docs/notebook-metadata/``). Coverage may only grow; it is
              deliberately NOT required to be 100% on day one, so the lane is
              adopted wave by wave and the floor is raised as waves land.

Header matching tolerates the dash variant (em dash, en dash, hyphen) and the
accent variants (derni[èe]re / r[ée]vision) a writer may produce; what it enforces
is the marker, the ``vivante`` qualifier, and the date. Only header position
counts, so a document may quote the convention in its body without tripping the
organ.

Verdicts:
    CONFORME   both directions hold (exit 0)
    VIOLATION  at least one finding (exit 1)

Usage:
    python scripts/check_docs_reference_lane.py
    python scripts/check_docs_reference_lane.py --json
    python scripts/check_docs_reference_lane.py --baseline 9
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

TRANSIENTS_REL = Path("docs") / "transients"
ARCHIVE_REL = Path("docs") / "archive"

# Default coverage floor = first wave (docs/notebook-metadata/, 9 documents).
# Raise it as perenne waves land; it is a monotone floor, never a target.
DEFAULT_BASELINE = 9

# "> REFERENCE -- 2026-10-25 -- vivante -- derniere revision <date>"
# (marker + "vivante" + "derniere revision" + trailing date; dash and accent
# variants tolerated)
REF_HEADER_RE = re.compile(
    r"^>\s*REFERENCE\s*[—–-]\s*vivante\s*[—–-]\s*"
    r"derni[èe]re\s+r[eé]vision\s+(?P<date>\d{4}-\d{2}-\d{2})\s*$",
    re.IGNORECASE,
)

# How many leading non-empty lines count as "header position".
HEADER_WINDOW = 5


def _is_generated(path: Path) -> bool:
    """Generated artefacts (catalogs) are not hand-maintained references."""
    name = path.name.lower()
    return "generated" in name or name.startswith("course_catalog")


def _header_lines(path: Path, window: int = HEADER_WINDOW) -> list[str]:
    """First ``window`` non-empty stripped lines of ``path`` (best effort)."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    return lines[:window]


def _header_match(lines: list[str]) -> re.Match | None:
    for line in lines:
        match = REF_HEADER_RE.match(line)
        if match:
            return match
    return None


def _git_last_commit_date(root: Path, relpath: str) -> str | None:
    """Last commit short-date (YYYY-MM-DD) touching ``relpath``, or None."""
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "log", "-1", "--format=%cs", "--", relpath],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )
    except (subprocess.CalledProcessError, OSError):
        return None
    return out.stdout.strip() or None


def _perenne_docs(root: Path) -> list[Path]:
    """All perennial reference docs under docs/ (sorted, stable)."""
    docs_dir = root / "docs"
    if not docs_dir.is_dir():
        return []
    out: list[Path] = []
    for path in sorted(docs_dir.rglob("*.md")):
        rel = path.relative_to(root)
        parts = rel.parts  # ("docs", <subdir>, ...)
        if len(parts) > 1 and parts[1] in ("transients", "archive"):
            continue
        if _is_generated(path):
            continue
        out.append(path)
    return out


def scan_perenne(root: Path, baseline: int) -> tuple[list[dict], dict]:
    """Check both directions over the perennial reference docs."""
    findings: list[dict] = []
    covered = 0
    docs = _perenne_docs(root)
    total = len(docs)
    for path in docs:
        rel = path.relative_to(root)
        rel_str = str(rel).replace("\\", "/")
        match = _header_match(_header_lines(path))
        if match is None:
            continue  # not (yet) covered: counts against coverage, no integrity check
        covered += 1
        last = _git_last_commit_date(root, rel_str)
        if last is None:
            findings.append(
                {
                    "file": rel_str,
                    "reason": "GIT_LOG_FAILED: ne peut pas lire git log -1 du fichier",
                }
            )
        elif last != match.group("date"):
            findings.append(
                {
                    "file": rel_str,
                    "reason": "STALE_DATE: en-tete {} != derniere revision {} "
                    "(a rafraichir)".format(match.group("date"), last),
                }
            )
    if covered < baseline:
        findings.append(
            {
                "file": "docs/**",
                "reason": "COVERAGE_BELOW_FLOOR: {}/{} docs perennes balises, "
                "plancher {}".format(covered, total, baseline),
            }
        )
    stats = {"perenne_total": total, "perenne_covered": covered, "baseline": baseline}
    return findings, stats


def run(root: Path = REPO_ROOT, baseline: int = DEFAULT_BASELINE) -> dict:
    root = Path(root).resolve()
    findings, stats = scan_perenne(root, baseline)
    return {
        "verdict": "VIOLATION" if findings else "CONFORME",
        "root": str(root),
        "perenne_total": stats["perenne_total"],
        "perenne_covered": stats["perenne_covered"],
        "baseline": stats["baseline"],
        "findings": findings,
    }


def format_report(report: dict) -> str:
    lines = [
        "Lane perenne docs/ (sens reference vivante) -- #14623",
        "  balises     : {perenne_covered}/{perenne_total} doc(s) perenne(s), "
        "plancher {baseline}".format(**report),
    ]
    if report["findings"]:
        lines.append("")
        lines.append("  VIOLATION -- {n} finding(s)".format(n=len(report["findings"])))
        for finding in report["findings"]:
            lines.append("    - {file}".format(**finding))
            lines.append("      {reason}".format(**finding))
    else:
        lines.append("")
        lines.append("  CONFORME -- les 2 sens du contrat tiennent")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verifie la convention de la lane perenne docs/ (#14623, sens reference)."
    )
    parser.add_argument(
        "--root",
        default=str(REPO_ROOT),
        help="racine du depot (defaut : racine deduite du script)",
    )
    parser.add_argument(
        "--baseline",
        type=int,
        default=DEFAULT_BASELINE,
        help=(
            "plancher de couverture : nombre minimal de docs perennes balises "
            "(defaut {} = premiere vague)".format(DEFAULT_BASELINE)
        ),
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    report = run(root=args.root, baseline=args.baseline)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(format_report(report))
    return 1 if report["findings"] else 0


if __name__ == "__main__":
    sys.exit(main())
