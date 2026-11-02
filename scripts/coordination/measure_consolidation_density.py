#!/usr/bin/env python3
"""Mesure l'acceptance 4 de #16473 : densite DEEP/CONTENU avant/apres.

Un service suit la definition de ``belt_service_balance.py`` (#18832) : une
issue distincte referencee par une PR mergee via ``closingIssuesReferences``.
Les PRs qui ne font que citer une issue avec ``See`` ou ``Part of`` ne sont pas
dans le denominateur : la mesure ne pretend donc pas couvrir toute la production.

L'ancre par defaut est l'ouverture reelle de #16473 (2026-09-16T23:48:48Z).
La fenetre est semi-ouverte [debut, fin), ce qui evite de compter deux fois une
PR mergée exactement a la frontiere. Les tags sont lus par ``grain_tag`` et
``effective_tier`` ; les axes B/C par ``classify_axes``. Aucun de ces lecteurs
n'est reimplemente ici.

Usage :
    python scripts/coordination/measure_consolidation_density.py
    python scripts/coordination/measure_consolidation_density.py --json-out result.json
    python scripts/coordination/measure_consolidation_density.py --replay fixture.json

Le replay accepte ``{"before": [...], "after": [...], "issues": [...]}``.
La sortie est advisory : 0 pour une mesure complete, 2 pour une panne ou une
donnee tronquee. Une fenetre sans service rend INCONCLUSIVE, jamais 100 %.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

UTC = timezone.utc

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from audit_consolidation_orphans import classify_axes
from grain_tag import parse_grain_tag
from pick_idle_grain import CONTENU
from variation_light_cap import effective_tier, label_names

DEFAULT_ANCHOR = "2026-09-16T23:48:48Z"
PR_FIELDS = "number,title,body,mergedAt,labels,closingIssuesReferences"


def parse_iso(value: str) -> datetime:
    """Parse an ISO timestamp and require an explicit timezone."""
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None:
        raise ValueError(f"timestamp sans fuseau : {value!r}")
    return parsed.astimezone(UTC)


def iso_z(value: datetime) -> str:
    return value.astimezone(UTC).isoformat().replace("+00:00", "Z")


def issue_refs(pr: dict[str, Any]) -> list[dict[str, Any]]:
    refs = pr.get("closingIssuesReferences") or []
    if isinstance(refs, dict):
        return list(refs.get("nodes") or [])
    return list(refs)


def run_json(argv: list[str], *, stdin: str | None = None) -> Any:
    proc = subprocess.run(
        argv,
        input=stdin,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
        check=False,
    )
    if proc.returncode:
        raise RuntimeError(f"commande en echec ({proc.returncode}) : {argv!r}\n{proc.stderr[:500]}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"JSON illisible depuis {argv!r}: {exc}") from exc


def fetch_merged_prs(repo: str, start: datetime, end: datetime) -> list[dict[str, Any]]:
    """Fetch one window and fail rather than silently accepting a 1000-hit cap."""
    query = f"merged:{iso_z(start)}..{iso_z(end)}"
    prs = run_json([
        "gh", "pr", "list", "--repo", repo, "--state", "merged",
        "--search", query, "--limit", "1000", "--json", PR_FIELDS,
    ])
    if len(prs) >= 1000:
        raise RuntimeError(f"fenetre tronquee a 1000 PRs : {query}; la decouper avant de mesurer")
    selected = []
    for pr in prs:
        merged_at = pr.get("mergedAt")
        if merged_at and start <= parse_iso(merged_at) < end:
            selected.append(pr)
    return selected


def fetch_issues(repo: str, prs: list[dict[str, Any]]) -> dict[int, dict[str, Any]]:
    """Resolve referenced issue IDs in GraphQL batches, including full bodies."""
    ids = sorted({ref["id"] for pr in prs for ref in issue_refs(pr) if ref.get("id")})
    if not ids:
        return {}
    issues: dict[int, dict[str, Any]] = {}
    query = """query($ids: [ID!]!) {
      nodes(ids: $ids) {
        __typename
        ... on Issue { id number title body createdAt closedAt }
      }
    }"""
    for offset in range(0, len(ids), 50):
        batch = ids[offset:offset + 50]
        payload = run_json(
            ["gh", "api", "graphql", "--input", "-"],
            stdin=json.dumps({"query": query, "variables": {"ids": batch}}),
        )
        if payload.get("errors"):
            raise RuntimeError(f"GraphQL issues : {payload['errors']}")
        nodes = (payload.get("data") or {}).get("nodes") or []
        for node in nodes:
            if not node:
                continue
            if node.get("__typename") != "Issue" or not node.get("number"):
                raise RuntimeError(f"reference inattendue dans la mesure : {node!r}")
            issues[int(node["number"])] = node
        if len([node for node in nodes if node]) != len(batch):
            raise RuntimeError("une issue referencee n'est plus lisible ; mesure refusee plutot que partielle")
    return issues


def measure_window(
    prs: list[dict[str, Any]], issues: dict[int, dict[str, Any]],
    start: datetime, end: datetime,
) -> dict[str, Any]:
    """Aggregate distinct served issues, using the earliest merged service."""
    earliest: dict[int, tuple[datetime, dict[str, Any]]] = {}
    duplicates = 0
    linked_prs: set[int] = set()
    window_prs = []
    for pr in prs:
        merged_at = pr.get("mergedAt")
        if not merged_at:
            continue
        stamp = parse_iso(merged_at)
        if not start <= stamp < end:
            continue
        window_prs.append(pr)
        if issue_refs(pr):
            linked_prs.add(pr.get("number"))
        for ref in issue_refs(pr):
            number = ref.get("number")
            if not number:
                continue
            number = int(number)
            if number in earliest:
                duplicates += 1
            if number not in earliest or stamp < earliest[number][0]:
                earliest[number] = (stamp, pr)

    services = []
    for number, (stamp, pr) in sorted(earliest.items()):
        body = pr.get("body") or ""
        tag = parse_grain_tag(body)
        tier = effective_tier(body, label_names(pr))
        genre = tag.get("genre") if tag else None
        issue = issues.get(number, {})
        axes = classify_axes(issue.get("title") or "", issue.get("body") or "") if issue else []
        deep_content = tier == "DEEP" and genre in CONTENU
        services.append({
            "issue": number,
            "pr": pr.get("number"),
            "mergedAt": iso_z(stamp),
            "tier": tier,
            "genre": genre,
            "axes": axes,
            "deep_content": deep_content,
            "deep_axis_bc": deep_content and bool({"B", "C"} & set(axes)),
            "issue_metadata": bool(issue),
        })

    linked_prs.discard(None)
    total = len(services)
    deep = sum(service["deep_content"] for service in services)
    deep_bc = sum(service["deep_axis_bc"] for service in services)
    missing = [service["issue"] for service in services if not service["issue_metadata"]]
    return {
        "start": iso_z(start),
        "end": iso_z(end),
        "merged_prs": len(window_prs),
        "prs_with_closing_link": len(linked_prs),
        "unlinked_prs": len(prs) - len(linked_prs),
        "services": total,
        "duplicate_issue_links": duplicates,
        "deep_content": deep,
        "deep_content_density": deep / total if total else None,
        "deep_axis_bc": deep_bc,
        "deep_axis_bc_density": deep_bc / total if total else None,
        "tagged_services": sum(service["tier"] is not None for service in services),
        "missing_issue_metadata": missing,
        "deep_by_genre": dict(sorted(Counter(
            service["genre"] for service in services if service["deep_content"]
        ).items())),
        "deep_axis_bc_examples": [
            {"issue": service["issue"], "pr": service["pr"], "genre": service["genre"], "axes": service["axes"]}
            for service in services if service["deep_axis_bc"]
        ],
        "service_details": services,
    }


def compare(before: dict[str, Any], after: dict[str, Any]) -> dict[str, Any]:
    if not before["services"] or not after["services"]:
        verdict = "INCONCLUSIVE"
        delta = None
        bc_delta = None
    else:
        delta = after["deep_content_density"] - before["deep_content_density"]
        bc_delta = after["deep_axis_bc_density"] - before["deep_axis_bc_density"]
        verdict = "INCREASE" if delta > 0 else "NOT_INCREASED"
    return {
        "acceptance": "#16473 acceptance 4",
        "definition": "issues distinctes via closingIssuesReferences ; tier effectif DEEP et genre CONTENU",
        "coverage_limit": "les citations See/Part of sans closingIssuesReferences sont hors denominateur",
        "before": before,
        "after": after,
        "deep_content_delta_points": delta * 100 if delta is not None else None,
        "deep_axis_bc_delta_points": bc_delta * 100 if bc_delta is not None else None,
        "verdict": verdict,
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Densite DEEP/CONTENU — #16473 acceptance 4",
        "",
        (
            "Un service = une issue distincte reliee a une PR mergee par `closingIssuesReferences` (definition #18832). "
            "Le tier effectif est `DEEP` et le genre appartient a `CONTENU`."
        ),
        "",
        "| Fenetre | PRs mergees | Services distincts | DEEP/CONTENU | Densite | dont axes B/C |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for key, label in (("before", "7 jours avant"), ("after", "7 jours apres")):
        row = report[key]
        density = "N/A" if row["deep_content_density"] is None else f"{100 * row['deep_content_density']:.1f} %"
        lines.append(
            f"| {label} ({row['start']} → {row['end']}) | {row['merged_prs']} | "
            f"{row['services']} | {row['deep_content']} | {density} | {row['deep_axis_bc']} |"
        )
    delta = report["deep_content_delta_points"]
    bc_delta = report["deep_axis_bc_delta_points"]
    lines.extend([
        "",
        f"**Verdict : {report['verdict']}**" + (f" — variation {delta:+.1f} points." if delta is not None else " — une fenetre est vide."),
        "",
        (
            "Axes B/C parmi les DEEP/CONTENU : "
            + (f"variation de proportion {bc_delta:+.1f} points." if bc_delta is not None else "non mesurable (fenetre vide).")
        ),
        "",
        f"Portee : {report['coverage_limit']}. La mesure etablit une variation de proportion, pas une causalite attribuable a #16473.",
        "Les issues sans metadonnee ne sont pas devinees ; leur nombre figure dans le JSON (`missing_issue_metadata`).",
        "",
    ])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=(
        "Mesure l'acceptance 4 de #16473 : densite DEEP/CONTENU avant/apres."
    ))
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--anchor", default=DEFAULT_ANCHOR, help="ouverture de l'EPIC, ISO avec fuseau")
    parser.add_argument("--days", type=int, default=7)
    parser.add_argument("--replay", type=Path, help="fixture JSON au lieu de gh")
    parser.add_argument("--out", type=Path, help="rapport markdown (sinon stdout)")
    parser.add_argument("--json-out", type=Path, help="preuve complete, details par service inclus")
    args = parser.parse_args(argv)
    try:
        anchor = parse_iso(args.anchor)
        if args.days <= 0:
            raise ValueError("--days doit etre positif")
        before_start = anchor - timedelta(days=args.days)
        after_end = anchor + timedelta(days=args.days)
        if args.replay:
            data = json.loads(args.replay.read_text(encoding="utf-8"))
            before_prs, after_prs = data["before"], data["after"]
            issues = {int(issue["number"]): issue for issue in data.get("issues", [])}
        else:
            before_prs = fetch_merged_prs(args.repo, before_start, anchor)
            after_prs = fetch_merged_prs(args.repo, anchor, after_end)
            issues = fetch_issues(args.repo, before_prs + after_prs)
        before = measure_window(before_prs, issues, before_start, anchor)
        after = measure_window(after_prs, issues, anchor, after_end)
        report = compare(before, after)
        markdown = render_markdown(report)
        if args.out:
            args.out.write_text(markdown, encoding="utf-8")
        else:
            print(markdown)
        if args.json_out:
            args.json_out.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        return 0
    except (OSError, ValueError, KeyError, RuntimeError, json.JSONDecodeError) as exc:
        print(f"UNKNOWN — mesure non produite : {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
