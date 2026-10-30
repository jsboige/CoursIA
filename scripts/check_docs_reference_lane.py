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

The organ runs in TWO modes (review of #22527, squash-merge convention):

  tree mode   (default, no ``--base``): marker presence + coverage floor over
              the whole perennial set. Dates are deliberately NOT compared:
              on this repository the merge is a squash whose committer date is
              the merge time (#22216: last branch commit 05:57Z, squash %cs
              10:32Z), so ``git log -1 --format=%cs`` of a merged doc is the
              merge time, not the date its content was last revised -- a
              tree-wide date equality would redden ``main`` and every PR at
              each merge crossing a UTC day. The tree is judged only on what
              survives a squash: the marker and the floor.

  PR mode     (``--base <ref>``): dates ARE compared, but only for the docs the
              PR itself modifies, and against each doc's own last commit on the
              branch -- the one place where ``git log -1 --format=%cs`` still
              reads a content date. A mismatch means the document was revised
              without refreshing its header (``STALE_DATE``); a failing git
              call is a finding (``GIT_LOG_FAILED`` / ``GIT_DIFF_FAILED``),
              never a silent pass. Run it from the PR HEAD checkout, not the
              merge ref: on the merge ref every touched doc's last commit is
              the merge commit, dated at CI time.

  coverage    (both modes) a monotone ratchet over the whole perennial set: the
              number of documents carrying the header must not drop below
              ``--baseline`` (default 25 = wave 1 ``docs/notebook-metadata/``
              9 + wave 3 ``docs/genai/`` 16). Coverage may only grow; it is
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
    python scripts/check_docs_reference_lane.py                     # tree mode
    python scripts/check_docs_reference_lane.py --base origin/main  # PR mode
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

# Default coverage floor = wave 1 (docs/notebook-metadata/, 9 documents)
# + wave 2 (docs/qc/, 8 documents, hors qc-strategies-status chaud par PRs)
# + wave 3 (docs/genai/, 16 documents). Raise it as perenne waves land;
# it is a monotone floor, never a target.
DEFAULT_BASELINE = 33

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


def _git(root: Path, *args: str) -> str:
    """Run git in ``root``; raises CalledProcessError/OSError on failure."""
    proc = subprocess.run(
        ["git", "-C", str(root), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return proc.stdout


def _git_last_commit_date(root: Path, relpath: str) -> str | None:
    """Last commit short-date (YYYY-MM-DD) touching ``relpath``, or None."""
    try:
        out = _git(root, "log", "-1", "--format=%cs", "--", relpath)
    except (subprocess.CalledProcessError, OSError):
        return None
    return out.strip() or None


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


def _changed_docs(root: Path, base: str) -> set[str] | None:
    """Docs under docs/ changed between ``base`` and HEAD (repo-relative,
    forward slashes), or None when git cannot answer (fail-closed)."""
    try:
        out = _git(root, "diff", "--name-only", f"{base}...HEAD", "--", "docs/")
    except (subprocess.CalledProcessError, OSError):
        return None
    return {line.strip().replace("\\", "/") for line in out.splitlines() if line.strip()}


def scan_perenne(
    root: Path, baseline: int, base: str | None = None
) -> tuple[list[dict], dict]:
    """Check the coverage direction always, and the date direction only in
    PR mode (``base`` given), only for the docs the PR itself modifies."""
    findings: list[dict] = []
    covered = 0
    date_checked = 0
    docs = _perenne_docs(root)
    total = len(docs)

    touched: set[str] | None
    if base is None:
        touched = None  # tree mode: no date comparison at all
    else:
        touched = _changed_docs(root, base)
        if touched is None:
            findings.append(
                {
                    "file": "docs/**",
                    "reason": "GIT_DIFF_FAILED: ne peut pas lire git diff "
                    "{base}...HEAD -- docs/".format(base=base),
                }
            )

    for path in docs:
        rel = path.relative_to(root)
        rel_str = str(rel).replace("\\", "/")
        match = _header_match(_header_lines(path))
        if match is None:
            continue  # not (yet) covered: counts against coverage, no integrity check
        covered += 1
        if touched is None or rel_str not in touched:
            continue  # date judged only for the docs this PR modifies
        date_checked += 1
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
    stats = {
        "perenne_total": total,
        "perenne_covered": covered,
        "baseline": baseline,
        "mode": "tree" if base is None else "pr",
        "base": base,
        "date_checked": date_checked,
    }
    return findings, stats


def run(
    root: Path = REPO_ROOT,
    baseline: int = DEFAULT_BASELINE,
    base: str | None = None,
) -> dict:
    root = Path(root).resolve()
    findings, stats = scan_perenne(root, baseline, base=base)
    report = dict(stats)
    report.update(
        {
            "verdict": "VIOLATION" if findings else "CONFORME",
            "root": str(root),
            "findings": findings,
        }
    )
    return report


def format_report(report: dict) -> str:
    mode = "PR (base {base}, {date_checked} doc(s) date-verifie(s))".format(**report) \
        if report["mode"] == "pr" else "arbre (marqueur + plancher)"
    lines = [
        "Lane perenne docs/ (sens reference vivante) -- #14623",
        "  mode        : {m}".format(m=mode),
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
        lines.append("  CONFORME -- le contrat de la lane tient dans ce mode")
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
    parser.add_argument(
        "--base",
        default=None,
        metavar="REF",
        help=(
            "mode PR : ne verifier les dates que des docs modifies entre REF et "
            "HEAD, contre leur propre dernier commit. Defaut (absent) : mode "
            "arbre, marqueur + plancher seulement (survit au squash-merge)."
        ),
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    report = run(root=args.root, baseline=args.baseline, base=args.base)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(format_report(report))
    return 1 if report["findings"] else 0


if __name__ == "__main__":
    sys.exit(main())
