#!/usr/bin/env python3
"""Audit des filtres de chemin sur les workflows GitHub Actions.

Genere un rapport JSON + Markdown sur la couverture `pull_request.paths` /
`pull_request.paths-ignore` des workflows sous `.github/workflows/`. Detecte
les workflows sans filtre, classe par categorie (gate requis / advisory /
non-require), et signale les ajouts recents comme regression potentielle.

Issue de reference : #10600 (74 workflows, 0 filtre -> partiellement faux ;
62/72 ont deja un filtre paths/paths-ignore sur main a l'instant).

Sortie :
- JSON : `docs/audit/workflow-path-filters/audit-<sha>.json` (complet)
- Markdown : `docs/audit/workflow-path-filters/audit-<sha>.md` (resume humain)
- Last-known : `docs/audit/workflow-path-filters/latest.json` (le plus recent)

Usage :
    python scripts/notebook_tools/audit_workflow_path_filters.py --audit-dir docs/audit/workflow-path-filters
    python scripts/notebook_tools/audit_workflow_path_filters.py --check-regression <previous.json>
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any

import yaml


# Workflows dont le declenchement non-filtre est DELIBERE (gates requis par
# construction ou advisories bon marche qui doivent voir chaque PR).
# Cette liste est OPT-IN : ajouter un nom ici uniquement apres audit
# (cf. issue #10600 et discussion lane-claim-protocol).
REQUIRED_UNFILTERED_WORKFLOWS: set[str] = {
    # Gates PR (protection de branche)
    "pr-gate.yml",
    "lane-claim-guard.yml",
    "variation-tag-guard.yml",
    "variation-light-genre.yml",
    "translation-guard.yml",
    # catalog-pr-guard.yml retire par #11012 : le workflow n'a jamais tourne sur
    # une PR (0 run pull_request), c'est catalog-drift.yml qui tient la ligne.
    # Secret scan (doit voir chaque PR)
    "secret-scan.yml",
    # Regression guard (doit voir chaque PR)
    "regression-guard.yml",
    # Advisories bon marche
    "repo-size-advisory.yml",
    "stale-base-warning.yml",
}


def _parse_on_key(data: dict[str, Any]) -> dict[str, Any] | None:
    """Recupere le bloc `on:` d'un workflow YAML.

    PyYAML normalise la cle `on` en `True` (cle booleenne). On essaie
    les deux conventions.
    """
    on = data.get(True)
    if isinstance(on, dict):
        return on
    on = data.get("on")
    if isinstance(on, dict):
        return on
    return None


def _classify_unfiltered(name: str) -> str:
    """Classifie un workflow unfiltered en 'required' ou 'optional'."""
    if name in REQUIRED_UNFILTERED_WORKFLOWS:
        return "required"
    return "optional"  # nouveau, non audite -> a investiguer


def _parse_paths(pr_config: dict[str, Any] | list[Any] | None) -> list[str]:
    """Extrait la liste paths/paths-ignore depuis la config pull_request."""
    if pr_config is None or not isinstance(pr_config, dict):
        return []
    paths = pr_config.get("paths") or []
    paths_ignore = pr_config.get("paths-ignore") or []
    if isinstance(paths, str):
        paths = [paths]
    if isinstance(paths_ignore, str):
        paths_ignore = [paths_ignore]
    return list(paths) + [f"!{p}" for p in paths_ignore]


def audit_workflows(workflows_dir: Path) -> dict[str, Any]:
    """Parcourt `.github/workflows/*.yml` et retourne l'audit complet.

    Returns:
        dict avec :
          - workflows : liste de {name, has_pr_trigger, has_filter,
            paths_count, paths_list, classification}
          - summary : totaux filtered/unfiltered/no-pr-trigger/required-unfiltered
    """
    workflows: list[dict[str, Any]] = []

    for fname in sorted(workflows_dir.iterdir()):
        if fname.suffix not in (".yml", ".yaml"):
            continue

        try:
            content = fname.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            workflows.append(
                {
                    "name": fname.name,
                    "has_pr_trigger": False,
                    "has_filter": False,
                    "paths_count": 0,
                    "paths_list": [],
                    "classification": "unreadable",
                    "error": "cannot read file",
                }
            )
            continue

        try:
            data = yaml.safe_load(content)
        except yaml.YAMLError as e:
            workflows.append(
                {
                    "name": fname.name,
                    "has_pr_trigger": False,
                    "has_filter": False,
                    "paths_count": 0,
                    "paths_list": [],
                    "classification": "unreadable",
                    "error": f"yaml error: {e}",
                }
            )
            continue

        if not isinstance(data, dict):
            continue

        on = _parse_on_key(data)
        pr = on.get("pull_request") if on else None

        if pr is None:
            workflows.append(
                {
                    "name": fname.name,
                    "has_pr_trigger": False,
                    "has_filter": False,
                    "paths_count": 0,
                    "paths_list": [],
                    "classification": "no_pr_trigger",
                }
            )
            continue

        # pr can be None (= all PRs), dict with filter, dict without filter,
        # or a list of dicts (multiple PR triggers).
        if isinstance(pr, list):
            paths_combined: list[str] = []
            for entry in pr:
                if isinstance(entry, dict):
                    paths_combined.extend(_parse_paths(entry))
            has_filter = len(paths_combined) > 0
            paths_list = paths_combined
        elif isinstance(pr, dict):
            paths_list = _parse_paths(pr)
            has_filter = len(paths_list) > 0
        else:
            # pr is None or scalar -> all PRs, no filter
            has_filter = False
            paths_list = []

        workflows.append(
            {
                "name": fname.name,
                "has_pr_trigger": True,
                "has_filter": has_filter,
                "paths_count": len(paths_list),
                "paths_list": paths_list,
                "classification": (
                    "filtered"
                    if has_filter
                    else _classify_unfiltered(fname.name)
                ),
            }
        )

    summary = {
        "total": len(workflows),
        "with_pr_trigger": sum(1 for w in workflows if w["has_pr_trigger"]),
        "filtered": sum(
            1 for w in workflows if w["has_pr_trigger"] and w["has_filter"]
        ),
        "unfiltered": sum(
            1
            for w in workflows
            if w["has_pr_trigger"] and not w["has_filter"]
        ),
        "unfiltered_required": sum(
            1
            for w in workflows
            if w["has_pr_trigger"]
            and not w["has_filter"]
            and w["classification"] == "required"
        ),
        "unfiltered_optional": sum(
            1
            for w in workflows
            if w["has_pr_trigger"]
            and not w["has_filter"]
            and w["classification"] == "optional"
        ),
        "no_pr_trigger": sum(1 for w in workflows if not w["has_pr_trigger"]),
    }

    return {
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "workflows_dir": str(workflows_dir),
        "summary": summary,
        "workflows": workflows,
    }


def check_regression(
    current: dict[str, Any], previous: dict[str, Any]
) -> list[dict[str, Any]]:
    """Detecte les ajouts recents sans filtre par rapport a un audit anterieur.

    Returns:
        liste de {name, reason} pour chaque regression detectee.
    """
    previous_filtered = {
        w["name"] for w in previous["workflows"] if w["has_pr_trigger"]
    }
    current_unfiltered = {
        w["name"]
        for w in current["workflows"]
        if w["has_pr_trigger"] and not w["has_filter"]
    }

    regressions: list[dict[str, Any]] = []
    # Nouveaux workflows sans filtre (ni dans la liste required)
    for name in current_unfiltered:
        if name not in previous_filtered and name not in REQUIRED_UNFILTERED_WORKFLOWS:
            regressions.append(
                {
                    "name": name,
                    "reason": "newly_added_unfiltered_optional",
                    "explanation": (
                        f"{name} added since previous audit without paths/paths-ignore filter "
                        f"and not in REQUIRED_UNFILTERED_WORKFLOWS whitelist"
                    ),
                }
            )
    # Workflows qui ont perdu leur filtre
    current_filtered = {
        w["name"]
        for w in current["workflows"]
        if w["has_pr_trigger"] and w["has_filter"]
    }
    for name in previous_filtered:
        if (
            name in current_unfiltered
            and name in REQUIRED_UNFILTERED_WORKFLOWS
        ):
            # Was filtered, now unfiltered-required -> check if was in required list
            # actually this means someone REMOVED the filter from a workflow that
            # wasn't on the whitelist originally. Skip if it's currently required.
            continue
        if name in current_unfiltered and name not in REQUIRED_UNFILTERED_WORKFLOWS:
            # Was filtered, now unfiltered-optional -> filter removed!
            previous_filter_status = next(
                (
                    w
                    for w in previous["workflows"]
                    if w["name"] == name
                ),
                None,
            )
            if previous_filter_status and previous_filter_status.get("has_filter"):
                regressions.append(
                    {
                        "name": name,
                        "reason": "filter_removed",
                        "explanation": (
                            f"{name} previously had a filter but filter was removed "
                            f"(now in unfiltered-optional)"
                        ),
                    }
                )
    return regressions


def write_markdown(audit: dict[str, Any], path: Path) -> None:
    """Ecrit un resume Markdown pour revue humaine."""
    s = audit["summary"]
    lines = [
        f"# Audit workflow path-filters",
        f"",
        f"**Generated** : {audit['generated_at']}",
        f"**Workflows dir** : `{audit['workflows_dir']}`",
        f"",
        f"## Summary",
        f"",
        f"| Metrique | Valeur |",
        f"|---|---|",
        f"| Total workflows | {s['total']} |",
        f"| Avec `pull_request` trigger | {s['with_pr_trigger']} |",
        f"| **Avec filtre paths/paths-ignore** | **{s['filtered']}** |",
        f"| Sans filtre | {s['unfiltered']} |",
        f"| - dont required (gates/advisories) | {s['unfiltered_required']} |",
        f"| - dont optional (a investiguer) | {s['unfiltered_optional']} |",
        f"| Sans `pull_request` trigger | {s['no_pr_trigger']} |",
        f"",
        f"## Sans filtre `paths`/`paths-ignore`",
        f"",
    ]

    unfiltered_required = [
        w for w in audit["workflows"] if w["classification"] == "required"
    ]
    unfiltered_optional = [
        w for w in audit["workflows"] if w["classification"] == "optional"
    ]

    if unfiltered_required:
        lines.extend(
            [
                f"### Required (gates/advisories - non-concerne par l'audit)",
                f"",
            ]
        )
        for w in unfiltered_required:
            lines.append(f"- `{w['name']}`")
        lines.append("")

    if unfiltered_optional:
        lines.extend(
            [
                f"### Optional (a investiguer - devrait avoir un filtre)",
                f"",
            ]
        )
        for w in unfiltered_optional:
            lines.append(f"- `{w['name']}`")
        lines.append("")

    lines.extend(
        [
            f"## Avec filtre `paths`/`paths-ignore`",
            f"",
            f"| Workflow | paths_count |",
            f"|---|---|",
        ]
    )
    for w in audit["workflows"]:
        if w["classification"] == "filtered":
            lines.append(f"| `{w['name']}` | {w['paths_count']} |")
    lines.append("")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--workflows-dir",
        default=".github/workflows",
        help="Repertoire des workflows GitHub Actions (default: .github/workflows)",
    )
    parser.add_argument(
        "--audit-dir",
        default="docs/audit/workflow-path-filters",
        help="Repertoire de sortie pour les rapports (default: docs/audit/workflow-path-filters)",
    )
    parser.add_argument(
        "--check-regression",
        metavar="PREVIOUS_JSON",
        help="Verifie les regressions contre un audit anterieur (chemin JSON)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Mode silencieux (sortie console minimale)",
    )

    args = parser.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[2]
    workflows_dir = repo_root / args.workflows_dir
    audit_dir = repo_root / args.audit_dir

    if not workflows_dir.is_dir():
        print(f"ERROR: workflows dir not found: {workflows_dir}", file=sys.stderr)
        return 1

    audit = audit_workflows(workflows_dir)

    # Hash SHA-256 du contenu audit pour nommage deterministe
    audit_json = json.dumps(audit, sort_keys=True)
    sha = hashlib.sha256(audit_json.encode("utf-8")).hexdigest()[:12]
    timestamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    json_path = audit_dir / f"audit-{timestamp}-{sha}.json"
    md_path = audit_dir / f"audit-{timestamp}-{sha}.md"
    latest_json = audit_dir / "latest.json"
    latest_md = audit_dir / "latest.md"

    audit_dir.mkdir(parents=True, exist_ok=True)
    json_path.write_text(
        json.dumps(audit, indent=2, sort_keys=True), encoding="utf-8"
    )
    write_markdown(audit, md_path)
    latest_json.write_text(
        json.dumps(audit, indent=2, sort_keys=True), encoding="utf-8"
    )
    latest_md.write_text(md_path.read_text(encoding="utf-8"), encoding="utf-8")

    s = audit["summary"]
    if not args.quiet:
        print(f"Audit completed: {s['with_pr_trigger']} PR-triggered workflows")
        print(f"  Filtered: {s['filtered']}")
        print(f"  Unfiltered: {s['unfiltered']} (required: {s['unfiltered_required']}, optional: {s['unfiltered_optional']})")
        print(f"  Reports:")
        print(f"    JSON: {json_path}")
        print(f"    MD:   {md_path}")
        print(f"    Latest: {latest_json}, {latest_md}")

    # Regression check
    rc = 0
    if args.check_regression:
        prev_path = Path(args.check_regression)
        if not prev_path.is_file():
            print(
                f"ERROR: previous audit file not found: {prev_path}",
                file=sys.stderr,
            )
            return 1
        previous = json.loads(prev_path.read_text(encoding="utf-8"))
        regressions = check_regression(audit, previous)
        if regressions:
            rc = 1
            print(f"\nREGRESSIONS DETECTED: {len(regressions)}", file=sys.stderr)
            for reg in regressions:
                print(
                    f"  - [{reg['reason']}] {reg['explanation']}",
                    file=sys.stderr,
                )
        else:
            if not args.quiet:
                print("\nNo regressions detected vs previous audit.")

    return rc


if __name__ == "__main__":
    sys.exit(main())
