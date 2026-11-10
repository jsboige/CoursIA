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
  distillation      (``--distillation`` / ``--strict-distillation`` only) a
                    report is distilled when a PERENNIAL document cites it.
                    Citations from the navigation surfaces (``_quarto.yml``,
                    ``docs/README.md``) do not count: they prove the report is
                    reachable, not that its conclusion was absorbed. The
                    undated slug a report carried before entering the lane
                    counts too -- a perennial written earlier cites that name.
                    Advisory by default; ``--strict-distillation`` turns a
                    missing citation into a finding.

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


# --- distillation -- the lane's own contract (4th direction, #14623) --------
#
# The lane README is explicit: "Un rapport ne s'accumule pas. Quand sa conclusion
# est durable, elle est distillee dans le document perenne qui la porte [...], et
# ce document CITE le rapport. [...] La lane est un transit, pas un stock."
# Nothing measured that half, so the lane could quietly become the stock it
# exists to avoid. A citation from a navigation surface proves the report is
# reachable, not that its conclusion was absorbed -- those do not count.

NAVIGATION_SURFACES = frozenset({"_quarto.yml", "docs/README.md"})


def _undated_slug(filename: str) -> str | None:
    """``2026-08-10-variation-genre-census.md`` -> ``variation-genre-census``.

    A perennial document written before the report entered the lane cites the
    name it carried in the perennial tree. Matching only the dated basename
    reports such a report as undistilled, which is false -- measured on
    ``scripts/variation_light_cap.py`` citing ``variation-genre-census.md``.
    """
    match = DATE_PREFIX_RE.match(filename)
    return match.group("slug") if match else None


def _git_citations(root: Path, needles: set[str]) -> dict[str, set[str]] | None:
    """``needle -> files citing it``, outside the lane and outside the archive.

    ``git grep`` rather than a filesystem walk: a perennial home lives outside
    ``docs/`` as often as inside it (rules, workflows, scripts, notebooks), and
    reading the whole tree to answer that would cost more than the answer is
    worth. ``None`` means git could not answer -- never a silent pass.
    """
    citations: dict[str, set[str]] = {}
    for needle in sorted(needles):
        try:
            proc = subprocess.run(
                [
                    "git",
                    "-C",
                    str(root),
                    "grep",
                    "-l",
                    "-F",
                    "-e",
                    needle,
                    "--",
                    ":!docs/transients",
                    ":!docs/archive",
                ],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=120,
            )
        except OSError:
            return None
        if proc.returncode not in (0, 1):  # 1 = no match, not a failure
            return None
        citations[needle] = {
            line.strip() for line in proc.stdout.splitlines() if line.strip()
        }
    return citations


def scan_distillation(
    lane_dir: Path, citations: dict[str, set[str]] | None
) -> tuple[dict, list[dict]]:
    """Which lane reports a perennial document actually cites."""
    reports = (
        sorted(p.name for p in lane_dir.glob("*.md") if p.name != LANE_README)
        if lane_dir.is_dir()
        else []
    )
    if citations is None:
        return (
            {
                "reports": len(reports),
                "distilled": 0,
                "index_only": [],
                "measured": False,
            },
            [
                {
                    "file": str(lane_dir),
                    "reason": (
                        "DISTILLATION_UNMEASURABLE: git n'a pas pu repondre -- "
                        "le sens distillation n'a pas ete execute, ce n'est pas "
                        "un acquittement"
                    ),
                }
            ],
        )

    distilled: list[str] = []
    index_only: list[str] = []
    findings: list[dict] = []
    for name in reports:
        needles = {name}
        slug = _undated_slug(name)
        if slug:
            needles.add(slug)
        hits: set[str] = set()
        for needle in needles:
            hits |= citations.get(needle, set())
        perennial = sorted(hit for hit in hits if hit not in NAVIGATION_SURFACES)
        if perennial:
            distilled.append(name)
            continue
        index_only.append(name)
        navigation = sorted(hit for hit in hits if hit in NAVIGATION_SURFACES)
        where = (
            f"seulement une entree de navigation ({', '.join(navigation)})"
            if navigation
            else "cite nulle part hors de la lane"
        )
        findings.append(
            {
                "file": str(lane_dir / name),
                "reason": (
                    "DISTILLATION_MISSING: aucun document perenne ne cite ce "
                    f"rapport -- {where}. La lane est un transit, pas un stock : "
                    "distiller la conclusion durable dans le document qui la "
                    "porte et l'y citer, ou retirer le rapport avec preuve de "
                    "preservation"
                ),
            }
        )
    return (
        {
            "reports": len(reports),
            "distilled": len(distilled),
            "index_only": index_only,
            "measured": True,
        },
        findings,
    )


def run(
    root: Path = REPO_ROOT,
    lane_dir: Path | None = None,
    base: str | None = None,
    distillation: bool = False,
    strict_distillation: bool = False,
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
    distillation_summary = None
    distillation_findings: list[dict] = []
    if (distillation or strict_distillation) and lane_dir.is_dir():
        needles: set[str] = set()
        for path in lane_dir.glob("*.md"):
            if path.name == LANE_README:
                continue
            needles.add(path.name)
            slug = _undated_slug(path.name)
            if slug:
                needles.add(slug)
        distillation_summary, distillation_findings = scan_distillation(
            lane_dir, _git_citations(root, needles)
        )

    findings = lane_findings + outside_findings + archive_findings
    if strict_distillation:
        findings = findings + distillation_findings
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
        "distillation": distillation_summary,
        "distillation_findings": distillation_findings,
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
    summary = report.get("distillation")
    if summary:
        if not summary["measured"]:
            lines.append("  distillation: NON MESUREE (git n'a pas repondu)")
        else:
            lines.append(
                "  distillation: {d}/{n} distille(s) par un document perenne, "
                "{i} sans".format(
                    d=summary["distilled"],
                    n=summary["reports"],
                    i=len(summary["index_only"]),
                )
            )
            for name in summary["index_only"]:
                lines.append(f"    . {name}")

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
    parser.add_argument(
        "--distillation",
        action="store_true",
        help=(
            "quatrieme sens (mesure, non bloquant) : chaque rapport de la lane "
            "est-il cite par un document perenne -- hors surfaces de navigation "
            "(_quarto.yml, docs/README.md) et hors docs/archive/"
        ),
    )
    parser.add_argument(
        "--strict-distillation",
        action="store_true",
        help=(
            "impose le sens distillation : un rapport de la lane sans citation "
            "perenne fait passer le verdict a VIOLATION (exit 1)"
        ),
    )
    args = parser.parse_args(argv)

    report = run(
        root=args.root,
        lane_dir=args.lane_dir,
        base=args.base,
        distillation=args.distillation,
        strict_distillation=args.strict_distillation,
    )
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(format_report(report))
    return 1 if report["findings"] else 0


if __name__ == "__main__":
    sys.exit(main())