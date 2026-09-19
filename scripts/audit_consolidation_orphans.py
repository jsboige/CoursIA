#!/usr/bin/env python3
"""Consolidation-orphans audit -- the ORGAN for issue #16473 (acceptance 1).

User mandate (2026-09-17, verbatim excerpt from the Epic body): the open-issue
pool grows, consolidation debt is paid poorly, and part of the stock ADDS
entropy instead of absorbing it. The Epic therefore asks for an audit that
LISTS the orphan issues (not attached to any consolidation chaperone) BY AXIS
(A-F), each with the PROOF of what was searched -- "un tri, pas un verdict".

Attachment semantics (a TRIAGE, deliberately generous -- a human arbitrates):

  - ``body``            the issue's own body cites ``#<chaperone>``;
  - ``chaperone_body``  a chaperone's body cites ``#<issue>``;
  - ``chaperone_comment`` a comment on a chaperone cites ``#<issue>``;
  - ``issue_comment``   (``--deep`` only) a comment on the issue cites
                        ``#<chaperone>``.

A bare ``#N`` mention counts as attachment here even when the prose around it
is negative ("ne pas dupliquer #5081") -- the report surfaces the line, the
reader decides. This is the opposite failure mode of a verdict tool: a false
"attached" costs a glance, a false "orphan" costs a duplicate grain.

Chaperones (from the Epic body): #5081 (notebook canon), #4362 (Lean lakes),
#13737 (structural, 30 perimeters), #9535 (cleanup), #16473 (this umbrella).

ADVISORY by default (same posture as orphan_branch_scan.py): exit 0 whatever
the orphan count; the payload is the report. ``--fail-on-orphans`` exists for
a future ratchet wire, NOT for this delivery.

Usage::

    python scripts/audit_consolidation_orphans.py --fetch             # gh live
    python scripts/audit_consolidation_orphans.py --fetch --deep      # + per-issue comments
    python scripts/audit_consolidation_orphans.py --input state.json  # offline
    ... --format md|json [--out report.md] [--fail-on-orphans]

``--input`` expects ``{"issues": [{"number", "title", "body"}, ...],
"chaperones": {"5081": {"body": "...", "comments": [{"body": "..."}]}}}``
(comments optional). The pure core (attachment proofs, axis classification,
report rendering) is network-free and unit-tested in
scripts/tests/test_audit_consolidation_orphans.py; only ``--fetch`` talks to
GitHub via ``gh``.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from typing import Any

CHAPERONES = (5081, 4362, 13737, 9535, 16473)

AXIS_LABELS = {
    "A": "Renumeration / parcours notebooks",
    "B": "Doublons / twins / consolidation notebooks",
    "C": "Lakes Lean",
    "D": "Scripts sprawl & doublons CLI",
    "E": "Doc sprawl & catalogue",
    "F": "Fraicheur des bodies d'Epic",
}

# Deliberately narrow patterns: a wrong axis is noise, an unclassified orphan
# is still listed. Multi-word anchors beat bare keywords ("lean" alone would
# swallow every notebook issue; "cli" alone every tooling one).
AXIS_PATTERNS: dict[str, list[re.Pattern[str]]] = {
    "A": [
        re.compile(r"renum", re.IGNORECASE),
        re.compile(r"renommage|renommer|rename", re.IGNORECASE),
        re.compile(r"num[ée]rotation|numeration|renumber", re.IGNORECASE),
        re.compile(r"accr[ée]tion|accretion", re.IGNORECASE),
        re.compile(r"suffixe (noyau|kernel)|noyau canonique", re.IGNORECASE),
        re.compile(r"nomenclature", re.IGNORECASE),
        re.compile(r"casse .*(lien|catalogue|catalog)", re.IGNORECASE),
    ],
    "B": [
        re.compile(r"doublon|doublons", re.IGNORECASE),
        re.compile(r"jumeau|jumelle|jumeaux", re.IGNORECASE),
        re.compile(r"\btwins?\b|\btwin_", re.IGNORECASE),
        re.compile(r"duplicat|duplicate", re.IGNORECASE),
        re.compile(r"solution_leak|check_twin|duplicate_notebook|link_label", re.IGNORECASE),
    ],
    "C": [
        re.compile(r"\blakes?\b", re.IGNORECASE),
        re.compile(r"mathlib", re.IGNORECASE),
        re.compile(r"junction", re.IGNORECASE),
        re.compile(r"find_lake_root|lake build|lakefile", re.IGNORECASE),
    ],
    "D": [
        re.compile(r"scripts? .*(sprawl|consolidat|obsol[èe]te|doublon)", re.IGNORECASE),
        re.compile(r"one[- ]shots?", re.IGNORECASE),
        re.compile(r"infralink", re.IGNORECASE),
        re.compile(r"kill[-_]mcp", re.IGNORECASE),
        re.compile(r"command sprawl", re.IGNORECASE),
    ],
    "E": [
        re.compile(r"\bdocs?\b .*(sprawl|consolidat|hygiene|hygi[èe]ne)", re.IGNORECASE),
        re.compile(r"readme", re.IGNORECASE),
        re.compile(r"catalogue|catalog\b", re.IGNORECASE),
        re.compile(r"changelog", re.IGNORECASE),
        re.compile(r"rebrand", re.IGNORECASE),
        re.compile(r"\.planning\b", re.IGNORECASE),
        re.compile(r"markdown files|fichiers markdown", re.IGNORECASE),
    ],
    "F": [
        re.compile(r"epic", re.IGNORECASE),
        re.compile(r"staleness|stale body|body p[ée]rim[ée]", re.IGNORECASE),
    ],
}


def mention_lines(text: str, number: int) -> list[str]:
    """Lines of ``text`` citing ``#<number>`` (word-bounded: #1647 != #16473)."""
    if not text:
        return []
    pattern = re.compile(rf"#{number}\b")
    return [line.strip() for line in text.splitlines() if pattern.search(line)]


def attachment_proofs(
    issue: dict[str, Any],
    chaperones: dict[int, dict[str, Any]],
    issue_comments: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    """All attachment proofs found for one issue against the chaperones."""
    proofs: list[dict[str, Any]] = []
    number = issue["number"]
    for chap in CHAPERONES:
        for line in mention_lines(issue.get("body") or "", chap):
            proofs.append({"type": "body", "chaperone": chap, "lines": [line]})
        detail = chaperones.get(chap)
        if not detail:
            continue
        for line in mention_lines(detail.get("body") or "", number):
            proofs.append({"type": "chaperone_body", "chaperone": chap, "lines": [line]})
        for comment in detail.get("comments") or []:
            for line in mention_lines(comment.get("body") or "", number):
                proofs.append({"type": "chaperone_comment", "chaperone": chap, "lines": [line]})
    if issue_comments is not None:
        for comment in issue_comments:
            for chap in CHAPERONES:
                for line in mention_lines(comment.get("body") or "", chap):
                    proofs.append({"type": "issue_comment", "chaperone": chap, "lines": [line]})
    return proofs


def classify_axes(title: str, body: str) -> list[str]:
    """Axes A-F matched by title+body, in A-F order. Empty list = UNCLASSIFIED."""
    haystack = f"{title}\n{body or ''}"
    return [
        axis
        for axis in sorted(AXIS_PATTERNS)
        if any(pat.search(haystack) for pat in AXIS_PATTERNS[axis])
    ]


def audit(
    issues: list[dict[str, Any]],
    chaperones: dict[int, dict[str, Any]],
    issues_comments: dict[int, list[dict[str, Any]]] | None = None,
) -> dict[str, Any]:
    """Pure core: tri of open issues into attached / orphaned-by-axis."""
    chaperone_numbers = {i["number"] for i in issues} & set(CHAPERONES)
    attached: list[dict[str, Any]] = []
    orphans: list[dict[str, Any]] = []
    for issue in issues:
        number = issue["number"]
        if number in CHAPERONES:
            continue
        comments = (issues_comments or {}).get(number)
        proofs = attachment_proofs(issue, chaperones, comments)
        if proofs:
            attached.append({
                "number": number,
                "title": issue.get("title") or "",
                "proofs": [
                    {"type": p["type"], "chaperone": p["chaperone"], "line": p["lines"][0]}
                    for p in proofs
                ],
            })
            continue
        absence = ["body: 0 citation des chaperons (#%s)" % " #".join(map(str, CHAPERONES))]
        if issues_comments is not None:
            absence.append("comments: 0 citation des chaperons (--deep)")
        orphans.append({
            "number": number,
            "title": issue.get("title") or "",
            "axes": classify_axes(issue.get("title") or "", issue.get("body") or ""),
            "absence": absence,
        })
    by_axis: dict[str, list[dict[str, Any]]] = {axis: [] for axis in AXIS_LABELS}
    by_axis["UNCLASSIFIED"] = []
    for orphan in orphans:
        if orphan["axes"]:
            for axis in orphan["axes"]:
                by_axis[axis].append(orphan)
        else:
            by_axis["UNCLASSIFIED"].append(orphan)
    return {
        "chaperones": list(CHAPERONES),
        "scanned": len(issues) - len(chaperone_numbers),
        "attached": len(attached),
        "orphans": len(orphans),
        "deep": issues_comments is not None,
        "attached_details": attached,
        "orphans_by_axis": by_axis,
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Audit consolidation-orphans (#16473, acceptance 1)",
        "",
        "Chaperons : %s" % " ".join(f"#{c}" for c in report["chaperones"]),
        f"Issues ouvertes scannées : {report['scanned']} ; rattachées : {report['attached']} ; orphelines : {report['orphans']}"
        + (" (scan --deep : commentaires inclus)" if report["deep"] else " (bodies seulement, lancer --deep pour les commentaires)"),
        "",
        "Un tri, pas un verdict : chaque ligne orpheline liste la preuve de ce qui a été cherché. L'arbitrage de rattachement (acceptance 2) reste humain.",
        "",
    ]
    for axis in [*AXIS_LABELS, "UNCLASSIFIED"]:
        entries = report["orphans_by_axis"][axis]
        if not entries:
            continue
        label = AXIS_LABELS[axis] if axis in AXIS_LABELS else "Hors périmètre consolidation apparent"
        lines.append(f"## Axe {axis} — {label} ({len(entries)})")
        lines.append("")
        lines.append("| Issue | Titre | Preuve d'absence |")
        lines.append("|---|---|---|")
        for orphan in sorted(entries, key=lambda o: o["number"]):
            absence = " ; ".join(orphan["absence"])
            lines.append(f"| #{orphan['number']} | {orphan['title'][:90]} | {absence} |")
        lines.append("")
    return "\n".join(lines)


def _gh_json(repo: str, args: list[str]) -> Any:
    result = subprocess.run(
        ["gh", *args, "--repo", repo],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if result.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} failed (rc={result.returncode}): {result.stderr.strip()}")
    return json.loads(result.stdout) if result.stdout.strip() else None


def fetch_state(repo: str, limit: int, deep: bool) -> dict[str, Any]:
    """Collect live state: open issues + chaperone bodies/comments (+ per-issue comments with --deep)."""
    issues = _gh_json(repo, ["issue", "list", "--state", "open", "--limit", str(limit),
                             "--json", "number,title,body"]) or []
    chaperones: dict[int, dict[str, Any]] = {}
    for chap in CHAPERONES:
        detail = _gh_json(repo, ["issue", "view", str(chap), "--json", "body,comments"]) or {}
        chaperones[chap] = detail
    issues_comments: dict[int, list[dict[str, Any]]] | None = None
    if deep:
        issues_comments = {}
        for issue in issues:
            number = issue["number"]
            detail = _gh_json(repo, ["issue", "view", str(number), "--json", "comments"]) or {}
            issues_comments[number] = detail.get("comments") or []
    return {"issues": issues, "chaperones": {str(k): v for k, v in chaperones.items()},
            "issues_comments": {str(k): v for k, v in (issues_comments or {}).items()},
            "deep": deep}


def load_input(path: str) -> tuple[list[dict[str, Any]], dict[int, dict[str, Any]], dict[int, list[dict[str, Any]]] | None]:
    with open(path, encoding="utf-8") as handle:
        state = json.load(handle)
    issues = state.get("issues") or []
    raw_chap = state.get("chaperones") or {}
    chaperones = {int(k): v for k, v in raw_chap.items()}
    raw_comments = state.get("issues_comments")
    issues_comments = None
    if raw_comments:
        issues_comments = {int(k): v for k, v in raw_comments.items()}
    return issues, chaperones, issues_comments


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--fetch", action="store_true", help="collect live state via gh")
    source.add_argument("--input", metavar="FILE", help="offline JSON state (see module docstring)")
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--limit", type=int, default=400)
    parser.add_argument("--deep", action="store_true", help="also scan comments on open issues (N+5 gh calls)")
    parser.add_argument("--format", choices=("md", "json"), default="md")
    parser.add_argument("--out", help="write the report to FILE instead of stdout")
    parser.add_argument("--fail-on-orphans", action="store_true",
                        help="exit 1 when orphans > 0 (future ratchet wire; NOT the delivery posture)")
    args = parser.parse_args(argv)

    if args.fetch:
        state = fetch_state(args.repo, args.limit, args.deep)
        issues = state["issues"]
        chaperones = {int(k): v for k, v in state["chaperones"].items()}
        issues_comments = None
        if state["issues_comments"]:
            issues_comments = {int(k): v for k, v in state["issues_comments"].items()}
    else:
        issues, chaperones, issues_comments = load_input(args.input)

    report = audit(issues, chaperones, issues_comments)
    rendered = json.dumps(report, ensure_ascii=False, indent=2) if args.format == "json" else render_markdown(report)
    if args.out:
        with open(args.out, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(rendered)
        print(f"report written to {args.out}", file=sys.stderr)
    else:
        print(rendered)
    if args.fail_on_orphans and report["orphans"] > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
