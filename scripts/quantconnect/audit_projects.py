#!/usr/bin/env python3
"""QuantConnect Cloud Projects Audit Script (Issue #558).

Generates a markdown report classifying all QC Cloud projects as
ALIVE / DEAD / SUPERSEDED / TEST and proposes deletion candidates.

Usage:
    # From MCP output (recommended):
    python audit_projects.py --from-json projects.json -o AUDIT_QC_CLOUD.md

    # With catalog enrichment (backtest data from prior audit):
    python audit_projects.py --from-json projects.json --catalog catalog.json -o AUDIT_QC_CLOUD.md

    # Dry run (report only, no deletions):
    python audit_projects.py --from-json projects.json --dry-run

Input JSON format: QC MCP list_projects() output:
    {"projects": [{"projectId": int, "name": str, ...}], ...}

Catalog JSON format (optional enrichment):
    {"projects": [{"projectId": int, "name": str, "backtest_count": int,
                   "best_sharpe": float, "best_cagr": str, "best_maxdd": str,
                   "status": str}]}

Classification rules:
    ALIVE      - Has backtests with positive Sharpe, or active by convention
    SUPERSEDED - Newer version exists (e.g. -v2 suffix, Framework_ prefix)
    DEAD       - 0 backtests AND stale, or structurally broken
    TEST       - Explicitly named test/validation/experimental
"""

import argparse
import json
import sys
from collections import defaultdict
from datetime import datetime, timedelta
from pathlib import Path


# Classification thresholds
STALE_DAYS = 30  # Days without modification to be considered stale
MIN_SHARPE = -0.5  # Below this = structurally broken


def load_projects(json_path: str) -> list[dict]:
    """Load project list from MCP JSON output."""
    try:
        with open(json_path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"ERROR: File not found: {json_path}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON in {json_path}: {e}", file=sys.stderr)
        sys.exit(1)
    return data.get("projects", [])


def load_catalog(catalog_path: str) -> dict[int, dict]:
    """Load catalog enrichment data keyed by project ID."""
    try:
        with open(catalog_path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"ERROR: Catalog not found: {catalog_path}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON in catalog {catalog_path}: {e}", file=sys.stderr)
        sys.exit(1)
    catalog = {}
    for entry in data.get("projects", []):
        pid = entry.get("projectId", 0)
        catalog[pid] = entry
    return catalog


def get_catalog_sharpe(catalog: dict[int, dict] | None, pid: int) -> float | None:
    """Get best Sharpe from catalog for a project."""
    if not catalog or pid not in catalog:
        return None
    return catalog[pid].get("best_sharpe")


def get_catalog_bt_count(catalog: dict[int, dict] | None, pid: int) -> int | None:
    """Get backtest count from catalog for a project."""
    if not catalog or pid not in catalog:
        return None
    return catalog[pid].get("backtest_count")


def classify_project(
    project: dict,
    name_index: dict[str, dict],
    catalog: dict[int, dict] | None = None,
) -> tuple[str, str]:
    """Classify a project. Returns (category, reason).

    Categories: ALIVE, SUPERSEDED, DEAD, TEST
    """
    name = project.get("name", "")
    pid = project.get("projectId", 0)
    modified = project.get("modified", "")
    created = project.get("created", "")
    org_id = project.get("organizationId", "")

    # 1. TEST category — explicit naming
    test_patterns = ["-Validation", "-Staging", "-Sandbox"]
    if any(p in name for p in test_patterns):
        return "TEST", "Name contains test/validation pattern"

    # ESGF validation projects
    if "ESGF-" in name and "Validation" in name:
        return "TEST", "ESGF validation project"

    # 2. SUPERSEDED detection
    superseded_pairs = [
        ("RiskParity", "RiskParity-v2"),
        ("DualMomentum", "DualMomentumNoTLT"),
    ]
    for old_name, new_name in superseded_pairs:
        if name == old_name and new_name in name_index:
            return "SUPERSEDED", f"Superseded by {new_name}"

    # Researcher projects superseded by Framework/Cloud versions
    if name.endswith("-Researcher"):
        base_name = name.replace("-Researcher", "")
        # Check if a Framework/Cloud version exists
        framework_name = f"Framework_{base_name}"
        cloud_name = f"Cloud-{base_name}"
        if framework_name in name_index or cloud_name in name_index:
            # But researcher may still have good backtests — check catalog
            sharpe = get_catalog_sharpe(catalog, pid)
            bt_count = get_catalog_bt_count(catalog, pid)
            bt_info = f", Sharpe {sharpe:.3f}" if sharpe else ""
            bt_info += f", {bt_count} BTs" if bt_count else ""
            return "SUPERSEDED", f"Researcher superseded by Framework/Cloud{bt_info}"
        # Researcher without replacement — classify by catalog data
        sharpe = get_catalog_sharpe(catalog, pid)
        bt_count = get_catalog_bt_count(catalog, pid)
        if bt_count is not None and bt_count > 0:
            if sharpe is not None and sharpe > MIN_SHARPE:
                return "ALIVE", f"Active Researcher, Sharpe {sharpe:.3f}, {bt_count} BTs"
            elif sharpe is not None:
                return "ALIVE", f"Researcher, negative Sharpe {sharpe:.3f}, {bt_count} BTs"

    # HandsOn duplicates
    if "HandsOn-Ex19-FinBERT" == name and "HandsOn-Ex19-FinBERT-Sentiment" in name_index:
        return "SUPERSEDED", "Duplicate of HandsOn-Ex19-FinBERT-Sentiment (renamed)"
    if "HandsOn-Ex16-LLM-Tiingo-News" == name and "HandsOn-Ex16-LLM-Summarization" in name_index:
        return "SUPERSEDED", "Superseded by HandsOn-Ex16-LLM-Summarization"

    # 3. Check catalog enrichment data (backtests + Sharpe)
    sharpe = get_catalog_sharpe(catalog, pid)
    bt_count = get_catalog_bt_count(catalog, pid)

    if bt_count is not None:
        if bt_count == 0:
            # No backtests — check freshness
            if created:
                try:
                    created_dt = datetime.fromisoformat(created.replace("Z", "+00:00"))
                    age_days = (datetime.now(created_dt.tzinfo) - created_dt).days
                    if age_days < 7:
                        return "ALIVE", "Fresh project (< 7 days old), no backtests yet"
                except (ValueError, TypeError):
                    pass
            # Check if it's a Framework/Cloud/ML naming (might be in development)
            dev_patterns = ["Framework_", "Cloud-", "ESGF-Framework"]
            if any(name.startswith(p) for p in dev_patterns):
                return "ALIVE", "Framework project, no backtests yet"
            return "DEAD", "No backtests"
        else:
            # Has backtests — classify by Sharpe
            if sharpe is not None:
                if sharpe >= 0:
                    return "ALIVE", f"Sharpe {sharpe:.3f}, {bt_count} BTs"
                elif sharpe > MIN_SHARPE:
                    return "ALIVE", f"Negative Sharpe {sharpe:.3f} ({bt_count} BTs, structural)"
                else:
                    # Extremely negative Sharpe
                    # But projects with many backtests (active iteration) are ALIVE with warning
                    if bt_count >= 5:
                        return "ALIVE", f"Sharpe {sharpe:.3f} ({bt_count} BTs, structural issue)"
                    return "DEAD", f"Sharpe {sharpe:.3f} ({bt_count} BTs, structurally broken)"
            else:
                # Has BTs but no Sharpe data (null stats)
                return "ALIVE", f"{bt_count} BTs (Sharpe unavailable)"

    # 4. Fallback: name-based classification
    active_patterns = ["Alpha", "Composite", "Framework", "Cloud-", "ML-",
                       "HandsOn-Ex", "DQN", "LSTM", "Transformer"]
    if any(name.startswith(p) or p in name for p in active_patterns):
        return "ALIVE", "Active by naming convention"

    # 5. Check modification date
    if modified:
        try:
            mod_dt = datetime.fromisoformat(modified.replace("Z", "+00:00"))
            age_days = (datetime.now(mod_dt.tzinfo) - mod_dt).days
            if age_days < STALE_DAYS:
                return "ALIVE", f"Recently modified ({age_days}d ago)"
            return "DEAD", f"Stale ({age_days}d since last modification)"
        except (ValueError, TypeError):
            pass

    return "DEAD", "No activity indicators"


def get_org_name(org_id: str) -> str:
    """Map org ID to name."""
    if org_id.startswith("d600793e"):
        return "Personal"
    elif org_id.startswith("94aa4bcb"):
        return "ESGF"
    return f"Unknown ({org_id[:8]})"


def generate_report(
    projects: list[dict],
    catalog: dict[int, dict] | None = None,
) -> str:
    """Generate markdown audit report."""
    now = datetime.now().strftime("%Y-%m-%d %H:%M")
    categories = defaultdict(list)
    reasons = {}
    name_index = {p.get("name", ""): p for p in projects}

    for proj in projects:
        cat, reason = classify_project(proj, name_index, catalog)
        categories[cat].append(proj)
        reasons[proj.get("projectId")] = (cat, reason)

    # Sort each category by name
    for cat in categories:
        categories[cat].sort(key=lambda p: p.get("name", ""))

    lines = [
        f"# QuantConnect Cloud Projects Audit",
        f"",
        f"**Generated**: {now} | **Source**: Issue #558",
        f"**Total**: {len(projects)} projects",
        f"",
        f"## Summary",
        f"",
        f"| Category | Count |",
        f"|----------|-------|",
    ]
    for cat in ["ALIVE", "SUPERSEDED", "TEST", "DEAD"]:
        count = len(categories.get(cat, []))
        lines.append(f"| {cat} | {count} |")

    lines.extend([
        f"",
        f"## Classification Legend",
        f"",
        f"- **ALIVE** — Active project with backtests (positive or negative Sharpe)",
        f"- **SUPERSEDED** — Newer version exists, original can be archived",
        f"- **TEST** — Validation/experimental project",
        f"- **DEAD** — No backtests and stale, or structurally broken",
        f"",
    ])

    # Detailed tables per org
    orgs = defaultdict(list)
    for proj in projects:
        org_name = get_org_name(proj.get("organizationId", ""))
        orgs[org_name].append(proj)

    for org_name in sorted(orgs.keys()):
        lines.extend([
            f"## {org_name} Organization ({len(orgs[org_name])} projects)",
            f"",
            f"| Project ID | Name | Category | Reason |",
            f"|-----------|------|----------|--------|",
        ])
        for proj in orgs[org_name]:
            pid = proj.get("projectId", "?")
            name = proj.get("name", "?")
            cat, reason = reasons.get(pid, ("UNKNOWN", ""))
            lines.append(f"| {pid} | {name} | {cat} | {reason} |")
        lines.append("")

    # Deletion candidates
    dead_projects = categories.get("DEAD", [])
    superseded_projects = categories.get("SUPERSEDED", [])
    deletion_candidates = dead_projects + superseded_projects

    if deletion_candidates:
        lines.extend([
            f"## Deletion Candidates ({len(deletion_candidates)})",
            f"",
            f"**WARNING**: Do NOT delete without user validation.",
            f"",
            f"| Project ID | Name | Category | Action |",
            f"|-----------|------|----------|--------|",
        ])
        for proj in deletion_candidates:
            pid = proj.get("projectId", "?")
            name = proj.get("name", "?")
            cat, reason = reasons.get(pid, ("", ""))
            action = "Archive" if cat == "SUPERSEDED" else "Delete candidate"
            lines.append(f"| {pid} | {name} | {cat} | {action} |")
        lines.append("")

    # Recommendations
    lines.extend([
        f"## Recommendations",
        f"",
        f"1. **Immediate**: Delete confirmed DEAD projects with 0 backtests",
        f"2. **Short-term**: Archive SUPERSEDED Researcher projects (code preserved in repo)",
        f"3. **Medium-term**: Fix broken HandsOn exercises (Ex10, Ex17) or mark as DRAFT",
        f"4. **Ongoing**: Run this script weekly to track project health",
        f"",
        f"## Reproduce",
        f"",
        f"```bash",
        f"# Export projects from QC MCP",
        f"# list_projects() -> save to projects.json",
        f"",
        f"# Generate report (with catalog enrichment):",
        f"python scripts/quantconnect/audit_projects.py --from-json projects.json --catalog catalog.json -o AUDIT.md",
        f"",
        f"# Without catalog (staleness-based classification only):",
        f"python scripts/quantconnect/audit_projects.py --from-json projects.json -o AUDIT.md",
        f"```",
    ])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="QC Cloud Projects Audit")
    parser.add_argument("--from-json", required=True, help="Path to projects JSON from MCP")
    parser.add_argument("--catalog", help="Path to catalog enrichment JSON (backtest data)")
    parser.add_argument("-o", "--output", help="Output markdown file path")
    parser.add_argument("--dry-run", action="store_true", help="Report only, no changes")
    parser.add_argument("--verbose", action="store_true", help="Verbose output")
    args = parser.parse_args()

    projects = load_projects(args.from_json)
    if not projects:
        print(f"ERROR: No projects found in {args.from_json}", file=sys.stderr)
        sys.exit(1)

    catalog = None
    if args.catalog:
        catalog = load_catalog(args.catalog)

    report = generate_report(projects, catalog)

    if args.output:
        Path(args.output).write_text(report, encoding="utf-8")
        print(f"Report written to {args.output}")

        # Print summary (reuse classification from generate_report)
        name_index = {p.get("name", ""): p for p in projects}
        cats = defaultdict(int)
        for proj in projects:
            cat, _ = classify_project(proj, name_index, catalog)
            cats[cat] += 1
        print(f"\nClassification: {dict(cats)}")
    else:
        print(report)


if __name__ == "__main__":
    main()
