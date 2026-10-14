#!/usr/bin/env python3
"""Verify the transient-reports lane convention (docs/transients/) -- issue #14623.

The lane holds transient documents -- dated reports, audits, state snapshots --
that carry proof value at their production date but do not belong to the
perennial tree. Its contract is a marking; a marking that nothing checks is a
declaration, so this organ is the measurable half. Convention and rationale:
``docs/transients/README.md``.

Two directions are always checked, a third when ``--base`` is given:

  inside the lane   every ``*.md`` but the lane README is dated
                    (``YYYY-MM-DD-slug.md``) and carries the frozen header
                    ``> RAPPORT - <date> - <perimetre> - fige`` among the first
                    lines, with a date agreeing with the filename;
  outside the lane  no file under ``docs/`` (outside ``docs/archive/`` and the
                    lane itself) carries that header in header position -- a
                    transient parked in the perennial tree is the exact drift
                    the lane exists to surface;
  archive entry     (``--base <ref>`` only, tranche 2 of #14623) no file is
                    CREATED under ``docs/archive/`` in the ``<ref>...HEAD``
                    diff carrying the transient signature (dated filename or
                    frozen header). The archive is stock to absorb, not a
                    destination; renames INTO it are reclassifications and stay
                    permitted. A failing ``git diff`` is itself a finding
                    (``GIT_DIFF_FAILED``), never a silent pass.

Header matching tolerates the dash variant (em dash, en dash, hyphen) and the
accent variant (fige/fige-with-accent) a writer may produce; what it enforces is
the marker, the date, and their agreement. Only header position counts outside
the lane, so a perennial document may quote the convention without tripping the
organ.

Verdicts:
    CONFORME   both directions hold (exit 0)
    VIOLATION  at least one finding (exit 1)

Usage:
    python scripts/check_docs_transients_lane.py
    python scripts/check_docs_transients_lane.py --json
    python scripts/check_docs_transients_lane.py --root . --lane-dir docs/transients
    python scripts/check_docs_transients_lane.py --base origin/main
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

LANE_REL = Path("docs") / "transients"
ARCHIVE_REL = Path("docs") / "archive"
LANE_README = "README.md"

# "> RAPPORT -- 2026-09-29 -- audited scope -- fige"
HEADER_RE = re.compile(
    r"^>\s*RAPPORT\s*[—–-]\s*"
    r"(?P<date>\d{4}-\d{2}-\d{2})\s*[—–-]\s*"
    r"(?P<scope>.+?)\s*[—–-]\s*fig[eé]\s*$",
    re.IGNORECASE,
)

DATE_PREFIX_RE = re.compile(r"^(?P<date>\d{4}-\d{2}-\d{2})-(?P<slug>.+)\.md$")

# How many leading non-empty lines count as "header position".
HEADER_WINDOW = 5


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
        match = HEADER_RE.match(line)
        if match:
            return match
    return None


def scan_lane(lane_dir: Path) -> list[dict]:
    findings: list[dict] = []
    if not lane_dir.is_dir():
        findings.append(
            {
                "file": str(lane_dir),
                "reason": "LANE_MISSING: le repertoire de la lane n'existe pas",
            }
        )
        return findings

    for path in sorted(lane_dir.glob("*.md")):
        if path.name == LANE_README:
            continue
        name = DATE_PREFIX_RE.match(path.name)
        if not name:
            findings.append(
                {
                    "file": str(path),
                    "reason": "NO_DATE_PREFIX: nom attendu <YYYY-MM-DD>-<slug>.md",
                }
            )
            continue
        match = _header_match(_header_lines(path))
        if not match:
            findings.append(
                {
                    "file": str(path),
                    "reason": (
                        "NO_HEADER: en-tete gele absent des "
                        f"{HEADER_WINDOW} premieres lignes "
                        "(attendu : '> RAPPORT - <date> - <perimetre> - fige')"
                    ),
                }
            )
            continue
        if match.group("date") != name.group("date"):
            findings.append(
                {
                    "file": str(path),
                    "reason": (
                        "DATE_MISMATCH: nom date {name_date}, en-tete date "
                        "{header_date}".format(
                            name_date=name.group("date"),
                            header_date=match.group("date"),
                        )
                    ),
                }
            )
    return findings


def scan_outside(root: Path, lane_dir: Path, archive_dir: Path) -> tuple[list[dict], int]:
    findings: list[dict] = []
    scanned = 0
    docs_dir = root / "docs"
    if not docs_dir.is_dir():
        return findings, scanned

    for path in sorted(docs_dir.rglob("*.md")):
        if lane_dir in path.parents or archive_dir in path.parents:
            continue
        scanned += 1
        if _header_match(_header_lines(path)):
            findings.append(
                {
                    "file": str(path),
                    "reason": (
                        "STRAY_REPORT_HEADER: en-tete de rapport transiente "
                        "en tete de document hors de la lane "
                        "(destination : docs/transients/, ou distillation vers le "
                        "document perenne)"
                    ),
                }
            )
    return findings, scanned


def _git_archive_entries(root: Path, base: str) -> list[tuple[str, str, str]] | None:
    """(status, src, dst) of every docs/archive change in ``base...HEAD``.

    Rename detection is ON so a move into the archive shows as ``Rxx`` (a
    reclassification, permitted) while a creation shows as ``A`` (the gesture
    the entry ban targets). Returns ``None`` when git itself fails -- the
    caller turns that into a finding rather than a silent pass.
    """
    try:
        proc = subprocess.run(
            [
                "git",
                "-C",
                str(root),
                "diff",
                "-M",
                "--name-status",
                f"{base}...HEAD",
                "--",
                "docs/archive",
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=60,
        )
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    entries: list[tuple[str, str, str]] = []
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        status, dst = parts[0], parts[-1]
        src = parts[1] if len(parts) >= 3 else ""
        entries.append((status, src, dst))
    return entries


def scan_archive_additions(
    root: Path, entries: list[tuple[str, str, str]] | None
) -> list[dict]:
    """Flag dated-report CREATIONS under docs/archive/ (tranche 2, #14623).

    ``A`` entries carrying the transient signature (dated filename or frozen
    header in header position) are findings; ``R`` renames are reclassifications
    and pass, as do creations without the signature (an ``INDEX.md`` refresh,
    for instance). ``None`` entries mean git failed: that is a finding too.
    """
    if entries is None:
        return [
            {
                "file": "docs/archive (diff)",
                "reason": (
                    "GIT_DIFF_FAILED: le git diff sous-jacent a echoue -- "
                    "le controle d'entree d'archive n'a pas pu etre execute, "
                    "ce n'est pas un acquittement"
                ),
            }
        ]
    findings: list[dict] = []
    for status, _src, dst in entries:
        if not status.startswith("A"):
            continue
        dated_name = DATE_PREFIX_RE.match(Path(dst).name) is not None
        frozen_header = _header_match(_header_lines(root / dst)) is not None
        if dated_name or frozen_header:
            findings.append(
                {
                    "file": dst,
                    "reason": (
                        "ARCHIVE_NEW_REPORT: creation d'un rapport date sous "
                        "docs/archive/ -- l'archive est un stock a resorber, "
                        "pas une destination ; un rapport date neuf vit dans "
                        "docs/transients/ (nom <YYYY-MM-DD>-<slug>.md + "
                        "en-tete gele). Deplacer un document EXISTANT vers "
                        "l'archive reste permis (reclasse, rename)"
                    ),
                }
            )
    return findings


def run(
    root: Path = REPO_ROOT, lane_dir: Path | None = None, base: str | None = None
) -> dict:
    root = Path(root).resolve()
    lane_dir = Path(lane_dir) if lane_dir else root / LANE_REL
    lane_dir = lane_dir.resolve()
    archive_dir = (root / ARCHIVE_REL).resolve()

    lane_findings = scan_lane(lane_dir)
    outside_findings, scanned = scan_outside(root, lane_dir, archive_dir)
    if base is not None:
        archive_entries = _git_archive_entries(root, base)
        archive_findings = scan_archive_additions(root, archive_entries)
    else:
        archive_entries = None
        archive_findings = []
    findings = lane_findings + outside_findings + archive_findings
    lane_files = (
        len([p for p in lane_dir.glob("*.md") if p.name != LANE_README])
        if lane_dir.is_dir()
        else 0
    )
    return {
        "verdict": "VIOLATION" if findings else "CONFORME",
        "root": str(root),
        "lane_dir": str(lane_dir),
        "lane_files": lane_files,
        "outside_scanned": scanned,
        "archive_base": base,
        "archive_entries": None if archive_entries is None else len(archive_entries),
        "findings": findings,
    }


def format_report(report: dict) -> str:
    lines = [
        "Lane transiente docs/transients/ -- #14623",
        "  lane        : {lane_dir} ({lane_files} rapport(s))".format(**report),
        "  hors lane   : {outside_scanned} fichier(s) 'docs/**/*.md' scanne(s) "
        "(hors archive/, hors lane)".format(**report),
    ]
    if report.get("archive_base"):
        entries = report.get("archive_entries")
        entries_txt = (
            "git diff en echec" if entries is None else f"{entries} entree(s) du diff"
        )
        lines.append(
            "  archive     : base {archive_base}, {e}".format(
                e=entries_txt, **report
            )
        )
    if report["findings"]:
        lines.append("")
        lines.append("  VIOLATION -- {n} finding(s)".format(n=len(report["findings"])))
        for finding in report["findings"]:
            lines.append("    - {file}".format(**finding))
            lines.append("      {reason}".format(**finding))
    else:
        lines.append("")
        senses = 3 if report.get("archive_base") else 2
        lines.append(f"  CONFORME -- les {senses} sens du contrat tiennent")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verifie la convention de la lane transiente docs/transients/ (#14623)."
    )
    parser.add_argument(
        "--root",
        default=str(REPO_ROOT),
        help="racine du depot (defaut : racine deduite du script)",
    )
    parser.add_argument(
        "--lane-dir",
        default=None,
        help="repertoire de la lane (defaut : <root>/docs/transients)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument(
        "--base",
        default=None,
        help=(
            "ref de base du diff (ex. origin/main) : ajoute le controle "
            "d'entree d'archive -- aucune creation de rapport date sous "
            "docs/archive/ dans <base>...HEAD"
        ),
    )
    args = parser.parse_args(argv)

    report = run(root=args.root, lane_dir=args.lane_dir, base=args.base)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(format_report(report))
    return 1 if report["findings"] else 0


if __name__ == "__main__":
    sys.exit(main())