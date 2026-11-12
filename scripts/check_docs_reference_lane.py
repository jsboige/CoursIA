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
              PR ITSELF modifies -- its OWN commits, against the PR's base:
              ``git log <base>..HEAD --no-merges --name-only -- docs/``. A
              mismatch means the document was revised without refreshing its
              header (``STALE_DATE``); a failing git call is a finding
              (``GIT_LOG_FAILED``), never a silent pass. Run it from the PR
              HEAD checkout, not the merge ref: on the merge ref every touched
              doc's last commit is the merge commit, dated at CI time.

              ``GIT_LOG_FAILED`` **replaces** the ``GIT_DIFF_FAILED`` code this
              organ used to publish on the same path: the touched-doc list is
              now read by ``git log``, so it is a failing ``git log`` that is
              reported. The published finding code changes with it -- a
              consumer filtering on ``GIT_DIFF_FAILED`` would stop seeing it.
              The sibling organ ``check_docs_transients_lane.py`` reads a
              ``git diff`` of its own and keeps publishing its own
              ``GIT_DIFF_FAILED``.

              Two properties of that range are load-bearing:

              - the range is measured against the **PR's base**, not against
                ``origin/main``: on a STACKED PR, ``origin/main..HEAD`` also
                contains the commits of the base branch, and the false positive
                of #24482 would survive the fix;
              - ``--no-merges`` and ``--first-parent``: an ``update-branch``
                or a ``git merge origin/main`` must not turn the docs that
                ``main`` modified into docs the PR modified -- neither the
                merge commit itself nor the ordinary commits it brings in.

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
# + wave 3 (docs/genai/, 16 documents)
# + wave 4 (docs/reference/, 70 documents, hors scripts-reference chaud par
# #25433, STABLE_SNAPSHOT et quant-prose-census dates-par-signature).
# Raise it as perenne waves land; it is a monotone floor, never a target.
DEFAULT_BASELINE = 102

# "> REFERENCE — vivante — dernière révision 2026-10-31"
# (marker, then "vivante", then "derniere revision" with its trailing date --
# the fields are separated by dashes; em dash, en dash, hyphen and accent
# variants all tolerated)
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


def _pr_own_commits(root: Path, base: str) -> list[tuple[str, list[str]]] | None:
    """The PR's OWN commits: (committer date, docs touched), most recent first.

    The range is ``base..HEAD``, the merges are excluded, and only the FIRST
    parent chain is walked. Three properties are load-bearing, and the first
    two were false positives before (arbitration of the coordinator,
    2026-11-04):

      - the range is measured against the **PR's base**, not ``origin/main``:
        on a stacked PR, ``origin/main..HEAD`` also contains the commits of
        the base branch, and the false positive of #24482 (a doc the PR never
        touched, reddened because the BASE branch had touched it) would
        survive the fix;
      - ``--no-merges``: an ``update-branch`` or a ``git merge origin/main``
        must not make the docs that ``main`` modified look like the PR's;
      - ``--first-parent``: the commits that an update-branch merge BRINGS IN
        are not merge commits -- they are ordinary commits that became
        reachable from the PR's head. Without this flag they stay in the
        range, and the false positive of #24482 survives the two fixes above:
        on that PR, the only source of ``docs/genai/decision-models.md`` in
        the range was main's squash commit ``3903e1c5`` (dated 2026-11-04,
        header 2026-11-03), reached through the merge.

    Returns ``None`` when git cannot answer -- the caller turns that into a
    finding (fail-closed), never into a silent pass.
    """
    try:
        out = _git(root, "log", f"{base}..HEAD", "--no-merges", "--first-parent",
                   "--format=@@@%H %cs", "--name-only", "--", "docs/")
    except (subprocess.CalledProcessError, OSError):
        return None
    commits: list[tuple[str, list[str]]] = []
    date: str | None = None
    files: list[str] = []
    for line in out.splitlines():
        if line.startswith("@@@"):
            if date is not None:
                commits.append((date, files))
            parts = line[3:].split()
            date = parts[1] if len(parts) > 1 else None
            files = []
        elif line.strip() and date is not None:
            files.append(line.strip().replace("\\", "/"))
    if date is not None:
        commits.append((date, files))
    return commits


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
    forward slashes), or None when git cannot answer (fail-closed).

    Kept for the callers that need the DIFF; the date check itself no longer
    reads it -- the PR's own commits are the only thing that decides which
    docs the PR is answerable for (see ``_pr_own_commits``).
    """
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
    date_of: dict[str, str] = {}
    if base is None:
        touched = None  # tree mode: no date comparison at all
    else:
        commits = _pr_own_commits(root, base)
        if commits is None:
            findings.append(
                {
                    "file": "docs/**",
                    "reason": "GIT_LOG_FAILED: ne peut pas lire git log "
                    "{base}..HEAD --no-merges --name-only -- docs/".format(base=base),
                }
            )
            touched = set()
        else:
            # The PR's OWN commits decide both WHICH docs it is answerable
            # for and WHEN it revised them. A doc that only the base branch
            # or main touched is not the PR's business -- that finding
            # belongs to the PR that made the change.
            touched = set()
            for commit_date, files in commits:  # most recent first
                for name in files:
                    if name not in date_of:
                        date_of[name] = commit_date
                    touched.add(name)

    for path in docs:
        rel = path.relative_to(root)
        rel_str = str(rel).replace("\\", "/")
        match = _header_match(_header_lines(path))
        if match is None:
            continue  # not (yet) covered: counts against coverage, no integrity check
        covered += 1
        if touched is None or rel_str not in touched:
            continue  # date judged only for the docs this PR modifies
        last = date_of.get(rel_str)
        if last is None:
            continue  # the PR's own commits never touched it: not its revision
        date_checked += 1
        if last != match.group("date"):
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
            "mode PR : ne verifier que les docs modifies par les commits PROPRES "
            "de la PR -- git log REF..HEAD --no-merges --name-only -- docs/ -- "
            "REF est la base de la PR (sur une PR empilee, la branche de base, "
            "PAS origin/main). Defaut (absent) : mode arbre, marqueur + plancher "
            "seulement (survit au squash-merge)."
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
