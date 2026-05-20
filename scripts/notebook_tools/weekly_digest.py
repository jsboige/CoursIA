#!/usr/bin/env python3
"""Generate weekly status digest for CoursIA repository.

Collects git activity metrics over the past week and produces a structured
summary: PRs merged, notebooks modified, series touched, top contributors.

Usage:
    python weekly_digest.py                    # Current week
    python weekly_digest.py --since 2026-05-01 # Custom start date
    python weekly_digest.py --days 14          # Last 14 days
    python weekly_digest.py --json             # JSON output
    python weekly_digest.py --markdown         # Markdown table output
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def _git(args: list[str]) -> str:
    """Run a git command and return stdout."""
    result = subprocess.run(
        ["git"] + args, capture_output=True, text=True,
        cwd=str(REPO_ROOT), timeout=30,
    )
    return result.stdout.strip()


def get_merged_prs(since: str, until: str | None = None) -> list[dict]:
    """Get merged PRs via gh CLI."""
    cmd = ["gh", "pr", "list", "--state", "merged", "--limit", "100",
           "--json", "number,title,mergedAt,author,additions,deletions,files"]
    result = subprocess.run(cmd, capture_output=True, text=True,
                           cwd=str(REPO_ROOT), timeout=30)
    if result.returncode != 0:
        return []

    prs = json.loads(result.stdout) if result.stdout else []

    # Filter by date
    since_dt = datetime.fromisoformat(since).replace(tzinfo=timezone.utc)
    until_dt = datetime.fromisoformat(until).replace(tzinfo=timezone.utc) if until else datetime.now(timezone.utc)

    filtered = []
    for pr in prs:
        merged_at = pr.get("mergedAt", "")
        if not merged_at:
            continue
        try:
            dt = datetime.fromisoformat(merged_at.replace("Z", "+00:00"))
            if since_dt <= dt <= until_dt:
                filtered.append(pr)
        except ValueError:
            continue

    return filtered


def get_commit_stats(since: str) -> dict:
    """Get commit statistics since a date."""
    # Total commits
    log = _git(["log", "--oneline", f"--since={since}"])
    commits = [l for l in log.split("\n") if l.strip()] if log else []
    total = len(commits)

    # Files changed
    diffstat = _git(["diff", "--stat", f"--since={since}", "HEAD"])
    # This doesn't work well with --since on diff. Use log --stat instead.
    logstat = _git(["log", "--format=", "--name-only", f"--since={since}"])
    files = set()
    for line in logstat.split("\n"):
        line = line.strip()
        if line:
            files.add(line)

    # Contributors
    shortlog = _git(["shortlog", "-sn", f"--since={since}"])
    contributors = []
    for line in shortlog.split("\n"):
        if line.strip():
            parts = line.strip().split("\t", 1)
            if len(parts) == 2:
                contributors.append({"commits": int(parts[0]), "author": parts[1]})

    return {
        "total_commits": total,
        "files_changed": len(files),
        "contributors": contributors,
    }


def classify_notebook_changes(files: set[str]) -> dict:
    """Classify changed files by series."""
    notebook_series = {}
    other_files = {"python": 0, "csharp": 0, "docs": 0, "config": 0, "other": 0}

    for f in files:
        if f.startswith("MyIA.AI.Notebooks/"):
            parts = f.replace(chr(92), "/").split("/")
            if len(parts) >= 2:
                series = parts[1]
            else:
                series = "root"
            notebook_series.setdefault(series, []).append(f)
        elif f.endswith(".py"):
            other_files["python"] += 1
        elif f.endswith(".cs"):
            other_files["csharp"] += 1
        elif f.endswith(".md") or f.endswith(".txt"):
            other_files["docs"] += 1
        elif f.endswith(".json") or f.endswith(".yml") or f.endswith(".yaml"):
            other_files["config"] += 1
        else:
            other_files["other"] += 1

    # Count notebooks vs other files per series
    series_stats = {}
    for series, sfiles in notebook_series.items():
        nbs = [f for f in sfiles if f.endswith(".ipynb")]
        series_stats[series] = {
            "files": len(sfiles),
            "notebooks": len(nbs),
            "notebook_names": [Path(f).stem for f in nbs[:5]],
        }

    return {"series": series_stats, "other": other_files}


def generate_digest(since: str, until: str | None = None) -> dict:
    """Generate full weekly digest."""
    until_str = until or datetime.now(timezone.utc).isoformat()

    # Commit stats
    commit_stats = get_commit_stats(since)

    # PRs merged
    prs = get_merged_prs(since, until_str)

    # Classify file changes
    file_classification = classify_notebook_changes(
        set(commit_stats.get("files_list", []))
    )

    # Get file list from git log
    logstat = _git(["log", "--format=", "--name-only", f"--since={since}"])
    files_changed = set()
    for line in logstat.split("\n"):
        line = line.strip()
        if line:
            files_changed.add(line)
    file_classification = classify_notebook_changes(files_changed)

    return {
        "period": {"since": since, "until": until_str},
        "commits": {
            "total": commit_stats["total_commits"],
            "contributors": commit_stats["contributors"],
        },
        "prs_merged": len(prs),
        "pr_details": [
            {
                "number": pr["number"],
                "title": pr["title"],
                "author": pr.get("author", {}).get("login", "unknown"),
                "additions": pr.get("additions", 0),
                "deletions": pr.get("deletions", 0),
                "files": len(pr.get("files", [])),
            }
            for pr in prs
        ],
        "files_changed": len(files_changed),
        "series_breakdown": file_classification["series"],
        "other_files": file_classification["other"],
    }


def print_markdown(digest: dict) -> None:
    """Print markdown-formatted digest."""
    period = digest["period"]
    commits = digest["commits"]

    print(f"# Weekly Digest: {period['since']} → {period['until'][:10]}")
    print()
    print(f"## Overview")
    print(f"- **Commits**: {commits['total']}")
    print(f"- **PRs merged**: {digest['prs_merged']}")
    print(f"- **Files changed**: {digest['files_changed']}")
    print(f"- **Contributors**: {len(commits['contributors'])}")
    print()

    if commits["contributors"]:
        print("### Top Contributors")
        print("| Author | Commits |")
        print("|--------|---------|")
        for c in commits["contributors"][:10]:
            print(f"| {c['author']} | {c['commits']} |")
        print()

    if digest["pr_details"]:
        print("### Merged PRs")
        print("| # | Title | Author | +/− |")
        print("|---|-------|--------|------|")
        for pr in digest["pr_details"]:
            title = pr["title"][:60] + ("..." if len(pr["title"]) > 60 else "")
            print(f"| #{pr['number']} | {title} | {pr['author']} | +{pr['additions']}/-{pr['deletions']} |")
        print()

    if digest["series_breakdown"]:
        print("### Series Activity")
        print("| Series | Files | Notebooks |")
        print("|--------|-------|-----------|")
        for series, stats in sorted(digest["series_breakdown"].items(),
                                     key=lambda x: -x[1]["files"]):
            nb_names = ", ".join(stats["notebook_names"][:3])
            if len(stats["notebook_names"]) > 3:
                nb_names += f" (+{len(stats['notebook_names']) - 3})"
            print(f"| {series} | {stats['files']} | {stats['notebooks']} ({nb_names}) |")
        print()

    print("### Non-Notebook Changes")
    other = digest["other_files"]
    print(f"- Python scripts: {other['python']}")
    print(f"- C# files: {other['csharp']}")
    print(f"- Documentation: {other['docs']}")
    print(f"- Config: {other['config']}")
    print(f"- Other: {other['other']}")


def main():
    parser = argparse.ArgumentParser(
        description="Generate weekly status digest for CoursIA"
    )
    parser.add_argument("--since", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--days", type=int, default=7, help="Days to cover (default: 7)")
    parser.add_argument("--until", help="End date (YYYY-MM-DD)")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--markdown", action="store_true", help="Markdown output (default)")
    args = parser.parse_args()

    if args.since:
        since = args.since
    else:
        since_date = datetime.now(timezone.utc) - timedelta(days=args.days)
        since = since_date.strftime("%Y-%m-%d")

    until = args.until

    digest = generate_digest(since, until)

    if args.json:
        print(json.dumps(digest, indent=2, default=str))
    else:
        print_markdown(digest)


if __name__ == "__main__":
    main()
