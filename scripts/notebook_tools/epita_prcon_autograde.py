#!/usr/bin/env python3
"""EPITA PrCon 2026 auto-grade script.

Queries the student repository via GitHub API and generates a structured
grading report per group (E4, H1, H2, J1, I2).

Grading criteria (collegial, 4 x 0-10, sum/2 = /20):
    1. Qualite de la presentation (0-10)
    2. Qualite theorique (0-10)
    3. Qualite technique (0-10)
    4. Organisation (0-10)

Auto-graded dimensions (from repo analysis):
    - Code presence and quality (Python files, notebooks, solver usage)
    - Git activity (commits, PRs, last activity date, contributor count)
    - File structure completeness (README, code, notebook, demo, slides)
    - CP solver usage (OR-Tools CP-SAT, SAT, or equivalent)

Usage:
    # Full report (all groups)
    python epita_prcon_autograde.py

    # JSON output
    python epita_prcon_autograde.py --json

    # Single group
    python epita_prcon_autograde.py --group H2

    # Custom repo
    python epita_prcon_autograde.py --repo owner/repo --token $GITHUB_TOKEN
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_DEFAULT = "jsboigeEpita/2026-Epita-Programmation-par-Contraintes"
GROUPS = ["E4", "H1", "H2", "J1", "I2"]

# Map group ID to actual folder name in the repo
GROUP_FOLDERS = {
    "E4": "E4-Evariste_BALVAY",
    "H1": "groupe-H1-Composition_Musicale_Assistée_par_Contraintes",
    "H2": "procedural-gen",
    "J1": "Groupe-J1-Allocation-multicritere-de-candidats",
    "I2": "I2-ANGLES-DEGUEST-HIEGEL",
}

# Size bonus/malus per grading matrix
SIZE_BONUS = {"E4": 3, "H1": 0, "H2": 3, "J1": 0, "I2": 0}

# Soutenance dates
SOUTENANCE_DATES = {
    "E4": "2026-05-18",
    "H1": "2026-05-18",
    "H2": "2026-05-22",
    "J1": "2026-05-22",
    "I2": "2026-05-22",
}


def _gh_api(endpoint: str, token: str | None = None) -> dict | list:
    """Call GitHub API via gh CLI or direct HTTP."""
    cmd = ["gh", "api", endpoint]
    if token:
        cmd = ["gh", "api", "--header", f"Authorization: token {token}", endpoint]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    if result.returncode != 0:
        return {}
    return json.loads(result.stdout)


def get_repo_tree(repo: str, token: str | None = None) -> list[dict]:
    """Get full repository tree via Git Trees API."""
    data = _gh_api(f"repos/{repo}/git/trees/main?recursive=1", token)
    return data.get("tree", [])


def get_commits(repo: str, path: str, token: str | None = None) -> list[dict]:
    """Get commits for a specific path."""
    data = _gh_api(f"repos/{repo}/commits?path={path}&per_page=20", token)
    if isinstance(data, list):
        return data
    return []


def get_prs(repo: str, token: str | None = None) -> list[dict]:
    """Get all merged PRs."""
    data = _gh_api(f"repos/{repo}/pulls?state=closed&per_page=50", token)
    if isinstance(data, list):
        return [pr for pr in data if pr.get("merged_at")]
    return []


def get_file_content(repo: str, path: str, token: str | None = None) -> str:
    """Get raw file content."""
    cmd = ["gh", "api", f"repos/{repo}/contents/{path}", "--jq", ".content"]
    if token:
        cmd = ["gh", "api", "--header", f"Authorization: token {token}",
               f"repos/{repo}/contents/{path}", "--jq", ".content"]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=15)
    if result.returncode != 0:
        return ""
    import base64
    try:
        return base64.b64decode(result.stdout.strip()).decode("utf-8", errors="replace")
    except Exception:
        return ""


def analyze_group(
    group: str,
    tree: list[dict],
    commits_by_path: dict[str, list[dict]],
    merged_prs: list[dict],
    repo: str,
    token: str | None = None,
) -> dict:
    """Analyze a single group's repository state and compute auto-grade metrics."""
    folder = GROUP_FOLDERS.get(group, group)
    group_prefix = f"{folder}/"
    group_files = [
        f for f in tree
        if f["path"].startswith(group_prefix) and f["type"] == "blob"
    ]
    # Also include files directly in the folder root (no subpath)
    root_file = [
        f for f in tree
        if f["path"] == folder and f["type"] == "blob"
    ]
    group_files.extend(root_file)

    # Classify files
    python_files = [f for f in group_files if f["path"].endswith(".py")]
    notebook_files = [f for f in group_files if f["path"].endswith(".ipynb")]
    readme_files = [f for f in group_files if "README" in f["path"].upper()]
    json_files = [f for f in group_files if f["path"].endswith(".json")]
    other_files = [
        f for f in group_files
        if f["path"] not in {x["path"] for x in python_files + notebook_files + readme_files + json_files}
    ]

    # README analysis
    readme_size = sum(f.get("size", 0) for f in readme_files)
    readme_content = ""
    if readme_files:
        readme_content = get_file_content(repo, readme_files[0]["path"], token)

    readme_indicators = {
        "has_formulation": any(
            kw in readme_content.lower()
            for kw in ["variable", "constraint", "objective", "contrainte", "objectif"]
        ),
        "has_cp_modeling": any(
            kw in readme_content.lower()
            for kw in ["cp-sat", "cpsat", "or-tools", "ortools", "constraint programming",
                        "bin packing", "satisfaction", "propagation"]
        ),
        "has_baselines": any(
            kw in readme_content.lower()
            for kw in ["baseline", "benchmark", "comparison", "random", "brute"]
        ),
        "has_metrics": any(
            kw in readme_content.lower()
            for kw in ["metric", "performance", "result", "accuracy", "sharpe", "time"]
        ),
        "line_count": readme_content.count("\n") if readme_content else 0,
    }

    # Python file analysis
    py_has_solver = False
    py_has_cpsat = False
    total_py_lines = 0
    for pf in python_files:
        content = get_file_content(repo, pf["path"], token)
        total_py_lines += content.count("\n")
        lower = content.lower()
        if any(kw in lower for kw in ["cp_model", "cpmodel", "cpsat", "cp-sat", "ortools",
                                       "solver", "constraint", "sat solver"]):
            py_has_solver = True
        if any(kw in lower for kw in ["cp_model", "newboolvar", "newintvar", "addconstraint",
                                       "add(self.", "model.add"]):
            py_has_cpsat = True

    # Git activity — use only this group's commits
    all_commits = commits_by_path.get(group, [])

    # Deduplicate by SHA
    seen_shas = set()
    unique_commits = []
    for c in all_commits:
        sha = c.get("sha", "")
        if sha not in seen_shas:
            seen_shas.add(sha)
            unique_commits.append(c)

    commit_count = len(unique_commits)
    contributors = set()
    last_activity = None
    for c in unique_commits:
        author = c.get("author", {}) or {}
        if author.get("login"):
            contributors.add(author["login"])
        date_str = c.get("commit", {}).get("committer", {}).get("date", "")
        if date_str:
            try:
                dt = datetime.fromisoformat(date_str.replace("Z", "+00:00"))
                if last_activity is None or dt > last_activity:
                    last_activity = dt
            except ValueError:
                pass

    # Filter PRs for this group — match by folder name or group ID
    group_prs = [
        pr for pr in merged_prs
        if folder in (pr.get("title", "") or "")
        or group in (pr.get("title", "") or "")
        or folder in (pr.get("body", "") or "")
        or group in (pr.get("body", "") or "")
    ]

    # Days since last activity
    days_inactive = 0
    if last_activity:
        now = datetime.now(timezone.utc)
        days_inactive = (now - last_activity).days

    # --- Scoring (auto-gradable dimensions only) ---
    # Theoretical quality (0-10) — based on README depth and CP modeling
    theoretical_score = 0
    if readme_indicators["has_formulation"]:
        theoretical_score += 2
    if readme_indicators["has_cp_modeling"]:
        theoretical_score += 2
    if readme_indicators["has_baselines"]:
        theoretical_score += 1
    if readme_indicators["has_metrics"]:
        theoretical_score += 1
    if readme_indicators["line_count"] > 50:
        theoretical_score += 2
    if readme_indicators["line_count"] > 100:
        theoretical_score += 1
    if py_has_solver:
        theoretical_score += 1
    theoretical_score = min(theoretical_score, 10)

    # Technical quality (0-10) — code, notebook, solver usage
    technical_score = 0
    if python_files:
        technical_score += 2
    if notebook_files:
        technical_score += 2
    if py_has_cpsat:
        technical_score += 3
    elif py_has_solver:
        technical_score += 1
    if total_py_lines > 100:
        technical_score += 1
    if total_py_lines > 300:
        technical_score += 1
    if len(group_files) > 3:
        technical_score += 1
    technical_score = min(technical_score, 10)

    # Organisation (0-10) — git activity, PRs, contributors, recency
    org_score = 0
    if commit_count >= 1:
        org_score += 1
    if commit_count >= 3:
        org_score += 1
    if commit_count >= 5:
        org_score += 1
    if len(contributors) > 1:
        org_score += 2
    if days_inactive < 7:
        org_score += 2
    elif days_inactive < 14:
        org_score += 1
    if group_prs:
        org_score += 1
    if readme_files:
        org_score += 1
    if len(group_files) > 5:
        org_score += 1
    org_score = min(org_score, 10)

    # Presentation cannot be auto-graded (requires soutenance)
    presentation_score = None  # To be filled during soutenance

    # Estimated raw score (excluding presentation)
    estimated_partial = theoretical_score + technical_score + org_score
    estimated_max = estimated_partial + 10  # +10 if presentation is perfect
    estimated_min = estimated_partial + 0   # +0 if presentation is worst

    size_adj = SIZE_BONUS.get(group, 0)

    return {
        "group": group,
        "files": {
            "total": len(group_files),
            "python": len(python_files),
            "notebooks": len(notebook_files),
            "readme": len(readme_files),
            "json": len(json_files),
            "other": len(other_files),
            "total_py_lines": total_py_lines,
        },
        "readme_analysis": readme_indicators,
        "code_analysis": {
            "has_solver_import": py_has_solver,
            "has_cpsat_model": py_has_cpsat,
            "python_file_paths": [f["path"] for f in python_files],
            "notebook_paths": [f["path"] for f in notebook_files],
        },
        "git_activity": {
            "commit_count": commit_count,
            "contributors": sorted(contributors),
            "last_activity": last_activity.isoformat() if last_activity else None,
            "days_inactive": days_inactive,
            "merged_prs": len(group_prs),
        },
        "soutenance_date": SOUTENANCE_DATES.get(group, "unknown"),
        "scores": {
            "presentation": presentation_score,
            "theoretical": theoretical_score,
            "technical": technical_score,
            "organisation": org_score,
        },
        "size_bonus": size_adj,
        "estimated_range": {
            "min": max(0, (estimated_min + size_adj) / 2),
            "max": min(20, (estimated_max + size_adj) / 2),
        },
        "notes": _generate_notes(group, python_files, notebook_files, py_has_cpsat,
                                 py_has_solver, commit_count, days_inactive, readme_indicators),
    }


def _generate_notes(
    group: str,
    python_files: list,
    notebook_files: list,
    has_cpsat: bool,
    has_solver: bool,
    commits: int,
    days_inactive: int,
    readme_indicators: dict,
) -> list[str]:
    """Generate qualitative notes for the report."""
    notes = []

    if not python_files and not notebook_files:
        notes.append("CRITICAL: No code or notebook in repository")
    elif not python_files:
        notes.append("WARNING: No Python files found")
    elif not notebook_files:
        notes.append("INFO: No Jupyter notebooks found")

    if has_cpsat:
        notes.append("GOOD: CP-SAT model detected in code")
    elif has_solver:
        notes.append("OK: Solver import detected but no full CP-SAT model")
    elif python_files:
        notes.append("WARNING: Python code present but no CP solver usage detected")

    if commits <= 1:
        notes.append(f"WARNING: Only {commits} commit(s) — minimal git activity")
    if days_inactive > 14:
        notes.append(f"WARNING: {days_inactive} days since last activity")
    elif days_inactive > 7:
        notes.append(f"INFO: {days_inactive} days since last activity")

    if readme_indicators["line_count"] > 100:
        notes.append("GOOD: Detailed README (>100 lines)")
    elif readme_indicators["line_count"] > 50:
        notes.append("OK: README with some content")
    elif readme_indicators["line_count"] == 0:
        notes.append("CRITICAL: No README found")

    # Group-specific notes
    if group == "J1" and not has_cpsat:
        notes.append("CRITICAL: Web app without CP solver — course misalignment")
    if group in ("E4", "H1") and not python_files:
        notes.append("RISK: Excellent README but zero code — verify local dev during soutenance")
    if group == "I2" and commits <= 1:
        notes.append("RISK: Scaffolding only — verify original contributions during soutenance")

    return notes


def generate_report(
    repo: str = REPO_DEFAULT,
    token: str | None = None,
    groups: list[str] | None = None,
) -> dict:
    """Generate full grading report for all groups."""
    target_groups = groups or GROUPS

    print(f"Fetching repository tree for {repo}...")
    tree = get_repo_tree(repo, token)
    if not tree:
        print("ERROR: Could not fetch repository tree. Check gh auth status.", file=sys.stderr)
        return {"error": "repo_tree_fetch_failed", "groups": {}}

    print(f"Found {len(tree)} entries in repository.")

    # Fetch PRs
    merged_prs = get_prs(repo, token)
    print(f"Found {len(merged_prs)} merged PRs.")

    # Fetch commits per group
    commits_by_path: dict[str, list[dict]] = {}
    for group in target_groups:
        folder = GROUP_FOLDERS.get(group, group)
        print(f"Fetching commits for group {group} ({folder})...")
        commits = get_commits(repo, folder, token)
        commits_by_path[group] = commits

    # Analyze each group
    results = {}
    for group in target_groups:
        print(f"Analyzing group {group}...")
        results[group] = analyze_group(
            group, tree, commits_by_path, merged_prs, repo, token
        )

    return {
        "repo": repo,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "groups": results,
    }


def print_summary(report: dict) -> None:
    """Print human-readable summary table."""
    groups = report.get("groups", {})
    if not groups:
        print("No group data available.")
        return

    print("\n" + "=" * 90)
    print(f"EPITA PrCon 2026 — Auto-Grade Report")
    print(f"Repository: {report.get('repo', 'unknown')}")
    print(f"Generated: {report.get('generated_at', 'unknown')}")
    print("=" * 90)

    for group_id in GROUPS:
        g = groups.get(group_id)
        if not g:
            continue

        scores = g["scores"]
        files = g["files"]
        git = g["git_activity"]
        adj = g["size_bonus"]

        print(f"\n--- Group {group_id} (soutenance: {g['soutenance_date']}) ---")
        print(f"  Files: {files['total']} total "
              f"({files['python']} .py, {files['notebooks']} .ipynb, "
              f"{files['readme']} README)")
        print(f"  Code:  {files['total_py_lines']} Python lines, "
              f"solver={'YES' if g['code_analysis']['has_cpsat_model'] else 'no'}, "
              f"CP-SAT={'YES' if g['code_analysis']['has_cpsat_model'] else 'no'}")
        print(f"  Git:   {git['commit_count']} commits, "
              f"{len(git['contributors'])} contributors, "
              f"{git['days_inactive']}d inactive")
        print(f"  Scores: theory={scores['theoretical']}/10  "
              f"tech={scores['technical']}/10  "
              f"org={scores['organisation']}/10  "
              f"presentation=PENDING")
        print(f"  Size bonus: {adj:+d}")
        est = g["estimated_range"]
        print(f"  Estimated range: {est['min']:.1f} — {est['max']:.1f} /20")

        if g["notes"]:
            print("  Notes:")
            for note in g["notes"]:
                print(f"    - {note}")

    # Summary table
    print("\n" + "=" * 90)
    print("Summary Table")
    print("-" * 90)
    print(f"{'Group':<6} {'Theory':>8} {'Tech':>6} {'Org':>5} {'Pres':>6} "
          f"{'Size':>5} {'Min':>6} {'Max':>6} {'Key Issue':<30}")
    print("-" * 90)

    for group_id in GROUPS:
        g = groups.get(group_id)
        if not g:
            continue
        s = g["scores"]
        key_issue = ""
        for note in g["notes"]:
            if note.startswith("CRITICAL") or note.startswith("WARNING"):
                key_issue = note.split(": ", 1)[-1][:28]
                break
        print(f"{group_id:<6} {s['theoretical']:>8} {s['technical']:>6} "
              f"{s['organisation']:>5} {'?':>6} {g['size_bonus']:>+5} "
              f"{g['estimated_range']['min']:>6.1f} "
              f"{g['estimated_range']['max']:>6.1f} {key_issue:<30}")

    print("=" * 90)


def main():
    parser = argparse.ArgumentParser(
        description="EPITA PrCon 2026 auto-grade script"
    )
    parser.add_argument("--repo", default=REPO_DEFAULT, help="GitHub repository (owner/repo)")
    parser.add_argument("--token", help="GitHub API token (or use gh auth)")
    parser.add_argument("--group", help="Analyze single group (e.g. H2)")
    parser.add_argument("--json", action="store_true", help="Output JSON only")
    parser.add_argument("--output", help="Output file path (default: stdout)")
    args = parser.parse_args()

    groups = [args.group] if args.group else None

    report = generate_report(repo=args.repo, token=args.token, groups=groups)

    if args.json:
        output = json.dumps(report, indent=2, default=str)
        if args.output:
            Path(args.output).write_text(output, encoding="utf-8")
            print(f"JSON report saved to {args.output}")
        else:
            print(output)
    else:
        print_summary(report)
        if args.output:
            output = json.dumps(report, indent=2, default=str)
            Path(args.output).write_text(output, encoding="utf-8")
            print(f"\nFull JSON data saved to {args.output}")


if __name__ == "__main__":
    main()
