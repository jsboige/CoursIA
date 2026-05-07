#!/usr/bin/env python3
"""Per-family validation dispatcher for CoursIA notebooks.

Reads matrix.yml for family-specific configs, scans notebooks, runs
structure/content validation, and produces a summary report.

Usage:
    python dispatch.py --family Search            # Validate one family
    python dispatch.py --family Search --quick     # Structure only, no content
    python dispatch.py --all                       # All families
    python dispatch.py --all --quick               # Quick scan all
    python dispatch.py --all --json                # JSON output
    python dispatch.py --summary                   # Summary table only

Output:
    Per-family pass/fail/warn counts + maturity distribution + BROKEN list.
"""

import argparse
import json
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
MATRIX_PATH = Path(__file__).resolve().parent / "matrix.yml"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

sys.path.insert(0, str(SCRIPTS_DIR / "notebook_tools"))
sys.path.insert(0, str(SCRIPTS_DIR))

from notebook_tools import NotebookValidator, discover_notebooks


def load_matrix() -> dict:
    """Load validation matrix from matrix.yml."""
    with open(MATRIX_PATH, encoding="utf-8") as f:
        return yaml.safe_load(f)


def get_family_notebooks(family_name: str, family_config: dict) -> list[Path]:
    """Discover notebooks for a given family."""
    rel_path = family_config.get("path", f"MyIA.AI.Notebooks/{family_name}")
    abs_path = REPO_ROOT / rel_path
    if not abs_path.exists():
        return []
    return sorted(abs_path.rglob("*.ipynb"))


def validate_family(
    family_name: str,
    family_config: dict,
    quick: bool = False,
) -> dict:
    """Run validation on a single family.

    Returns dict with:
        name, total, pass, warn, fail, skip, errors_list,
        maturity_counts, status_counts, duration_s
    """
    import time

    t0 = time.time()
    notebooks = get_family_notebooks(family_name, family_config)
    acceptance = family_config.get("acceptance", {})
    require_outputs = acceptance.get("outputs_present", True)
    require_zero_errors = acceptance.get("zero_errors", True)

    results = {
        "name": family_name,
        "total": len(notebooks),
        "pass": 0,
        "warn": 0,
        "fail": 0,
        "skip": 0,
        "broken": [],
        "maturity": {"PRODUCTION": 0, "BETA": 0, "ALPHA": 0, "DRAFT": 0},
        "status": {"READY": 0, "DEMO": 0, "RESEARCH": 0, "BROKEN": 0},
    }

    for nb_path in notebooks:
        if ".ipynb_checkpoints" in str(nb_path):
            continue

        validator = NotebookValidator(nb_path)
        struct = validator.validate_structure()

        if not struct.valid_json:
            results["fail"] += 1
            results["broken"].append({
                "path": str(nb_path.relative_to(REPO_ROOT)),
                "reason": "Invalid JSON",
            })
            continue

        issues = []
        if not quick:
            issues = validator.validate_content()

        has_errors = struct.cells_with_errors > 0
        has_outputs = struct.cells_with_output > 0
        has_code = struct.code_cells > 0

        if has_errors and require_zero_errors:
            results["fail"] += 1
            error_names = _extract_error_names(nb_path)
            results["broken"].append({
                "path": str(nb_path.relative_to(REPO_ROOT)),
                "reason": f"errors: {', '.join(error_names[:3])}",
            })
            results["status"]["BROKEN"] += 1
        elif has_code and not has_outputs and require_outputs:
            results["warn"] += 1
            results["status"]["BROKEN"] += 1
        elif quick:
            results["pass"] += 1
            results["status"]["READY"] += 1
        else:
            severity = _worst_severity(issues)
            if severity == "error":
                results["fail"] += 1
            elif severity == "warning":
                results["warn"] += 1
            else:
                results["pass"] += 1
            results["status"]["READY"] += 1

        maturity = _classify_maturity(struct, issues)
        results["maturity"][maturity] += 1

    results["duration_s"] = round(time.time() - t0, 1)
    return results


def _extract_error_names(nb_path: Path) -> list[str]:
    """Extract error names from notebook outputs."""
    import json as _json
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = _json.load(f)
    except Exception:
        return ["ParseError"]

    names = []
    for cell in nb.get("cells", []):
        for out in cell.get("outputs", []):
            if out.get("output_type") == "error":
                names.append(out.get("ename", "Unknown"))
    return names or ["Unknown"]


def _worst_severity(issues: list) -> str:
    """Return worst severity from issue list."""
    for sev in ("error", "warning"):
        if any(i.issue_type == sev for i in issues):
            return sev
    return "ok"


def _classify_maturity(struct, issues) -> str:
    """Quick maturity classification from validation result."""
    if not struct.has_cells or struct.code_cells == 0:
        return "DRAFT"
    if not struct.valid_json:
        return "DRAFT"

    has_outputs = struct.cells_with_output > 0
    all_outputs = struct.cells_with_output == struct.code_cells and struct.code_cells > 0
    has_md = struct.markdown_cells > 0

    if not has_outputs:
        return "DRAFT"
    if not all_outputs:
        return "ALPHA"
    if not has_md:
        return "DRAFT"
    if struct.cells_with_errors > 0:
        return "ALPHA"
    if all_outputs and has_md and len(issues) <= 2:
        return "PRODUCTION"
    return "BETA"


def print_report(all_results: list[dict], json_output: bool = False):
    """Print validation report."""
    if json_output:
        print(json.dumps(all_results, indent=2, ensure_ascii=False))
        return

    total_nb = sum(r["total"] for r in all_results)
    total_pass = sum(r["pass"] for r in all_results)
    total_warn = sum(r["warn"] for r in all_results)
    total_fail = sum(r["fail"] for r in all_results)
    total_skip = sum(r["skip"] for r in all_results)

    print(f"\n{'=' * 72}")
    print(f"VALIDATION REPORT — {total_nb} notebooks, {len(all_results)} families")
    print(f"{'=' * 72}\n")

    print(f"{'Family':<16} {'Total':>5} {'PASS':>5} {'WARN':>5} {'FAIL':>5} {'Time':>6}")
    print("-" * 50)
    for r in all_results:
        print(
            f"{r['name']:<16} {r['total']:>5} {r['pass']:>5} "
            f"{r['warn']:>5} {r['fail']:>5} {r['duration_s']:>5.1f}s"
        )
    print("-" * 50)
    print(
        f"{'TOTAL':<16} {total_nb:>5} {total_pass:>5} "
        f"{total_warn:>5} {total_fail:>5}"
    )

    print(f"\n--- Maturity Distribution ---")
    print(f"{'Family':<16} {'PROD':>5} {'BETA':>5} {'ALPHA':>5} {'DRAFT':>5}")
    print("-" * 44)
    for r in all_results:
        m = r["maturity"]
        print(f"{r['name']:<16} {m['PRODUCTION']:>5} {m['BETA']:>5} {m['ALPHA']:>5} {m['DRAFT']:>5}")

    total_m = {"PRODUCTION": 0, "BETA": 0, "ALPHA": 0, "DRAFT": 0}
    for r in all_results:
        for k in total_m:
            total_m[k] += r["maturity"][k]
    print("-" * 44)
    print(f"{'TOTAL':<16} {total_m['PRODUCTION']:>5} {total_m['BETA']:>5} {total_m['ALPHA']:>5} {total_m['DRAFT']:>5}")

    broken = []
    for r in all_results:
        broken.extend(r["broken"])
    if broken:
        print(f"\n--- BROKEN ({len(broken)}) ---")
        for b in broken:
            print(f"  {b['path']}: {b['reason']}")


def main():
    parser = argparse.ArgumentParser(description="Per-family validation dispatcher")
    parser.add_argument("--family", help="Validate a single family")
    parser.add_argument("--all", action="store_true", help="Validate all families")
    parser.add_argument("--quick", action="store_true", help="Structure check only")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--summary", action="store_true", help="Summary table only")
    args = parser.parse_args()

    matrix = load_matrix()
    families = matrix.get("families", {})

    if args.family:
        if args.family not in families:
            print(f"Unknown family: {args.family}")
            print(f"Available: {', '.join(families.keys())}")
            sys.exit(1)
        targets = {args.family: families[args.family]}
    elif args.all:
        targets = families
    else:
        parser.print_help()
        sys.exit(1)

    all_results = []
    for name, config in targets.items():
        print(f"Validating {name}...", end=" ", flush=True)
        result = validate_family(name, config, quick=args.quick)
        status = "OK" if result["fail"] == 0 else f"{result['fail']} FAIL"
        print(f"{result['total']} notebooks, {status} ({result['duration_s']}s)")
        all_results.append(result)

    print_report(all_results, json_output=args.json)


if __name__ == "__main__":
    main()
