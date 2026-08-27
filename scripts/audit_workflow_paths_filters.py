#!/usr/bin/env python3
"""Audit inventory: workflow paths-filter coverage + estimated fan-out per PR type.

Issue #10600 (cause structurelle du merge bottleneck) : 74 workflows se
declenchent sur chaque PR, 0 filtre de chemin. Avant d'ajouter des ``paths:``
(risque : check requis absent -> PR BLOCKED pour toujours), il faut un
inventaire reproductible qui distingue :

  * workflows SANS paths: (fan-out garanti) ;
  * workflows AVEC paths: (fan-out conditionnel au diff) ;
  * workflows avec paths ET label-posing (risque #8822) ;
  * workflows REQUIS vs ADVISORY (seul le PR gate est requis sur main, verifie
    via l'API de protection de branche) ;
  * fan-out estime par type de PR : markdown-only, notebook-only, scripts-only,
    workflows-only, mixed (la mesure est calculee, pas rejouee).

Sortie : JSON sur stdout (--json) ou tableau Markdown (defaut). Le rapport est
concivable pour etre pose en commentaire d'issue ou integre dans une PR de
documentation.

Acceptance #10600 (cette tranche livre l'instrument, pas le filtre) :

  * inventaire exhaustif des workflows ``.github/workflows/*.yml`` ;
  * distinction SANS / AVEC paths ;
  * distinction REQUIRED / ADVISORY (depuis la protection de branche, via
    l'API, fallback a une liste statique si l'API est inaccessible) ;
  * fan-out estime par type de PR via les paths des workflows ;
  * exit 0 en mode audit (lecture seule) ; exit 1 uniquement si --strict
    detecte un workflow REQUIS sans paths.

Usage :
  python scripts/audit_workflow_paths_filters.py
  python scripts/audit_workflow_paths_filters.py --json
  python scripts/audit_workflow_paths_filters.py --strict
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable

import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS_DIR = REPO_ROOT / ".github" / "workflows"

# Fallback static list of required checks (protection de branche). Used when the
# GitHub API is unreachable (CI sandbox). The source of truth is the API; the
# list is updated when the protection changes.
REQUIRED_CHECKS_FALLBACK = {"PR gate"}


def has_pull_request_trigger(workflow: dict) -> bool:
    on = workflow.get(True, workflow.get("on", {}))
    if not isinstance(on, dict):
        return False
    return "pull_request" in on or "pull_request_review" in on


def get_pull_request_paths(workflow: dict) -> list[str] | None:
    """Return the ``paths`` filter under ``pull_request``, or None if absent."""
    on = workflow.get(True, workflow.get("on", {}))
    if not isinstance(on, dict):
        return None
    pr = on.get("pull_request")
    if not isinstance(pr, dict):
        return None
    paths = pr.get("paths")
    if isinstance(paths, list):
        return paths
    return None


def get_workflow_pulls_label(workflow: dict) -> bool:
    """Detect label-posing in the workflow script source (heuristic)."""
    # Read raw file to scan ``gh pr edit --add-label`` and ``gh label``.
    path = workflow.get("__file__")
    if not path:
        return False
    try:
        text = Path(path).read_text(encoding="utf-8")
    except OSError:
        return False
    return bool(
        re.search(r"gh\s+pr\s+edit[^&|;\n]*--add-label", text)
        or re.search(r"gh\s+label\s+create\b", text)
    )


def list_required_checks_via_api(repo_root: Path) -> set[str] | None:
    """Best-effort fetch of branch protection required checks via gh CLI."""
    try:
        result = subprocess.run(
            ["gh", "api", "repos/jsboige/CoursIA/branches/main/protection"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=15,
            encoding="utf-8", errors="replace",
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    try:
        data = json.loads(result.stdout)
    except json.JSONDecodeError:
        return None
    ctx = data.get("required_status_checks", {}) or {}
    contexts = ctx.get("contexts", [])
    return set(contexts) if isinstance(contexts, list) else set()


def inventory_workflows() -> list[dict]:
    rows: list[dict] = []
    for wf_path in sorted(WORKFLOWS_DIR.glob("*.yml")):
        try:
            with wf_path.open(encoding="utf-8") as fh:
                wf = yaml.safe_load(fh) or {}
        except yaml.YAMLError as exc:
            rows.append(
                {
                    "file": str(wf_path.relative_to(REPO_ROOT)),
                    "name": wf_path.stem,
                    "yaml_error": str(exc).splitlines()[0],
                }
            )
            continue
        wf["__file__"] = str(wf_path)
        name = wf.get("name") or wf_path.stem
        pulls = has_pull_request_trigger(wf)
        paths = get_pull_request_paths(wf) if pulls else None
        labels = get_workflow_pulls_label(wf) if pulls else False
        rows.append(
            {
                "file": str(wf_path.relative_to(REPO_ROOT)),
                "name": name,
                "has_pull_request": pulls,
                "paths": paths,
                "labels_posed": labels,
            }
        )
    return rows


# Mapping: PR-type -> set of paths the PR touches. Used to estimate fan-out
# by intersecting with each workflow's paths filter.
PR_TYPE_TOUCHES = {
    "markdown-only": ["**/*.md"],
    "notebook-only": ["**/*.ipynb"],
    "scripts-only": ["scripts/**"],
    "workflows-only": [".github/workflows/**", ".github/actions/**"],
    "docs-only": ["docs/**"],
}


def estimate_fanout(row: dict, pr_paths: Iterable[str]) -> bool:
    """Return True if this workflow would trigger for the given PR paths."""
    paths = row.get("paths")
    if paths is None:
        return bool(row.get("has_pull_request"))
    return any(fnmatch(p, pat) for pat in paths for p in pr_paths)


# Local fnmatch to avoid pulling in ``fnmatch`` heavy semantics
import fnmatch as _fnmatch  # noqa: E402


def fnmatch(path: str, pattern: str) -> bool:
    return _fnmatch.fnmatch(path, pattern)


def estimate_fanout_for_type(row: dict, pr_type: str) -> bool:
    if pr_type not in PR_TYPE_TOUCHES:
        return False
    paths = row.get("paths")
    if paths is None:
        return bool(row.get("has_pull_request"))
    touched = PR_TYPE_TOUCHES[pr_type]
    return any(_fnmatch.fnmatch(p, pat) for pat in paths for p in touched)


def render_markdown(rows: list[dict], required: set[str] | None) -> str:
    out: list[str] = []
    out.append("# Audit workflow paths-filters (issue #10600)")
    out.append("")
    n_total = len(rows)
    n_pulls = sum(1 for r in rows if r.get("has_pull_request"))
    n_paths = sum(1 for r in rows if r.get("paths"))
    n_labels = sum(1 for r in rows if r.get("labels_posed"))
    n_required = sum(
        1
        for r in rows
        if r.get("has_pull_request") and required and r.get("name") in required
    )
    out.append(f"Total workflows: **{n_total}** | pull_request: **{n_pulls}** | avec paths: **{n_paths}** | label-posing: **{n_labels}** | required: **{n_required}**")
    out.append("")
    if required is None:
        out.append(
            "_API de protection de branche injoignable -- fallback sur la liste statique._"
        )
        out.append("")
    out.append("| Workflow | pull_request | paths | label-posing |")
    out.append("|----------|--------------|-------|--------------|")
    for r in rows:
        if not r.get("has_pull_request"):
            continue
        paths_repr = ", ".join(r.get("paths") or ["(none)"])[:80]
        labels_repr = "oui" if r.get("labels_posed") else "non"
        out.append(
            f"| `{r['file']}` | oui | {paths_repr or '(none)'} | {labels_repr} |"
        )
    out.append("")
    out.append("## Fan-out estime par type de PR")
    out.append("")
    out.append("| Type de PR | Workflows declenches | Reduction vs SANS paths |")
    out.append("|------------|---------------------|--------------------------|")
    for pr_type in PR_TYPE_TOUCHES:
        n = sum(1 for r in rows if r.get("has_pull_request") and estimate_fanout_for_type(r, pr_type))
        out.append(f"| {pr_type} | **{n}** | reduction vs total pulls |")
    out.append("")
    return "\n".join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="JSON on stdout")
    parser.add_argument("--strict", action="store_true", help="exit 1 si un REQUIS n'a pas de paths")
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help="Chemin du rapport (defaut stdout). Le rapport est toujours ecrit, --json change juste le format.",
    )
    args = parser.parse_args()

    rows = inventory_workflows()
    required = list_required_checks_via_api(REPO_ROOT) or REQUIRED_CHECKS_FALLBACK
    api_reachable = list_required_checks_via_api(REPO_ROOT) is not None

    payload = {
        "issue": 10600,
        "workflows_total": len(rows),
        "workflows_pull_request": sum(1 for r in rows if r.get("has_pull_request")),
        "workflows_with_paths": sum(1 for r in rows if r.get("paths")),
        "workflows_label_posing": sum(1 for r in rows if r.get("labels_posed")),
        "required_checks": sorted(required) if required else [],
        "required_checks_source": "api" if api_reachable else "fallback_static",
        "fanout_estimated_per_pr_type": {
            t: sum(
                1
                for r in rows
                if r.get("has_pull_request") and estimate_fanout_for_type(r, t)
            )
            for t in PR_TYPE_TOUCHES
        },
        "rows": rows,
    }

    if args.json:
        text = json.dumps(payload, indent=2, ensure_ascii=False)
    else:
        text = render_markdown(rows, required)

    if args.report:
        args.report.write_text(text, encoding="utf-8")
        print(f"Report written: {args.report}", file=sys.stderr)
    else:
        print(text)

    if args.strict:
        # PR gate is intentionally pathless: a required check that filters by
        # path becomes pending-forever on PRs that don't touch the path, and
        # per #10600 criterion 2 the absence of `paths:` on PR gate is a
        # DESIGN choice, not a violation. See `.github/workflows/pr-gate.yml`
        # header for the rationale. Other required checks should NOT be
        # pathless — flag them.
        violations = [
            r
            for r in rows
            if r.get("has_pull_request")
            and r.get("paths") is None
            and r.get("name") in required
            and r.get("name") != "PR gate"
        ]
        if violations:
            print(
                f"\n# STRICT: {len(violations)} workflow(s) REQUIS sans paths:",
                file=sys.stderr,
            )
            for v in violations:
                print(f"  - {v['file']} (name: {v['name']})", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())