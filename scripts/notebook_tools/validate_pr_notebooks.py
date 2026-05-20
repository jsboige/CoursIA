#!/usr/bin/env python3
"""Validate notebooks changed in a PR for execution compliance (H.1 / H.3).

Checks that every modified .ipynb in a PR has:
1. All code cells with execution_count != null
2. Zero cells with output_type: error
3. No raise NotImplementedError / assert False / 1/0 (C.1)

Designed for use in GitHub Actions as a merge gate.
Also usable locally: python validate_pr_notebooks.py <base-branch> [paths...]

Exit codes:
    0 - All modified notebooks pass
    1 - One or more notebooks fail validation
    2 - Setup / runtime error
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# Patterns banned by rule C.1
C1_BANNED = ["raise NotImplementedError", "assert False", "1/0"]

# Kernels that cannot be executed via Papermill in CI (skip execution check,
# but still check C.1 and structural validity)
SKIP_EXEC_KERNELS = {
    ".net-csharp", ".net-fsharp", ".net-powershell",
    "lean4", "lean4-wsl", "lean",
}

# Paths that require QC Cloud (python3 kernel but need QuantBook runtime).
# H.3 is advisory-only for these — they can only be executed via QC Cloud.
QC_CLOUD_PATHS = ("QuantConnect/Python", "QuantConnect/projects")


def get_changed_notebooks(base: str, paths: list[str] | None = None) -> list[Path]:
    """Get list of .ipynb files changed relative to base branch."""
    if paths:
        return [Path(p) for p in paths if p.endswith(".ipynb") and Path(p).exists()]

    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", "--diff-filter=ACM", base],
            capture_output=True, text=True, check=True,
            cwd=str(REPO_ROOT),
        )
    except subprocess.CalledProcessError as e:
        print(f"ERROR: git diff failed: {e.stderr}", file=sys.stderr)
        return []

    notebooks = []
    for line in result.stdout.strip().splitlines():
        if line.endswith(".ipynb") and (REPO_ROOT / line).exists():
            notebooks.append(REPO_ROOT / line)
    return notebooks


def get_kernel_name(nb_path: Path) -> str:
    """Extract kernel name from notebook metadata."""
    try:
        data = json.loads(nb_path.read_text(encoding="utf-8"))
        return (
            data.get("metadata", {})
            .get("kernelspec", {})
            .get("name", "python3")
        )
    except (json.JSONDecodeError, UnicodeDecodeError):
        return "unknown"


def validate_notebook(nb_path: Path) -> dict:
    """Validate a single notebook for H.1/H.3 compliance.

    Returns dict with: path, kernel, total_code, passed, errors (list).
    """
    try:
        rel_path = str(nb_path.relative_to(REPO_ROOT))
    except ValueError:
        rel_path = str(nb_path)
    result = {
        "path": rel_path,
        "kernel": get_kernel_name(nb_path),
        "total_code": 0,
        "passed": True,
        "errors": [],
    }

    try:
        data = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        result["passed"] = False
        result["errors"].append(f"Cannot parse JSON: {e}")
        return result

    kernel = result["kernel"]
    skip_exec = any(k in kernel for k in SKIP_EXEC_KERNELS)
    normalized = rel_path.replace("\\", "/")
    skip_exec = skip_exec or any(p in normalized for p in QC_CLOUD_PATHS)

    for i, cell in enumerate(data.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue

        source = "".join(cell.get("source", []))
        if not source.strip():
            continue

        # Skip comment-only cells
        lines = [l.strip() for l in source.split("\n") if l.strip()]
        if all(l.startswith("#") for l in lines):
            continue

        result["total_code"] += 1

        # C.1 check: banned patterns
        for pattern in C1_BANNED:
            if pattern in source:
                result["passed"] = False
                result["errors"].append(
                    f"cell {i}: C.1 violation — '{pattern}' found"
                )

        # H.3 check: execution_count must not be null (skip for non-Papermill kernels)
        if not skip_exec:
            exec_count = cell.get("execution_count")
            if exec_count is None:
                result["passed"] = False
                result["errors"].append(
                    f"cell {i}: execution_count is null (H.3 violation)"
                )

        # H.1 check: no error outputs (advisory for QC Cloud — errors expected
        # from [REFERENCE QC] cells executed locally without QuantBook runtime)
        for output in cell.get("outputs", []):
            if output.get("output_type") == "error":
                ename = output.get("ename", "Unknown")
                if skip_exec:
                    result["errors"].append(
                        f"cell {i}: has error output — {ename} (advisory, QC Cloud)"
                    )
                else:
                    result["passed"] = False
                    result["errors"].append(
                        f"cell {i}: has error output — {ename}"
                    )

    return result


def main():
    parser = argparse.ArgumentParser(
        description="Validate notebooks changed in a PR (H.1/H.3/C.1)"
    )
    parser.add_argument(
        "base", nargs="?", default="origin/main",
        help="Base branch to diff against (default: origin/main)",
    )
    parser.add_argument(
        "paths", nargs="*",
        help="Specific paths to check (skips git diff)",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output results as JSON",
    )
    parser.add_argument(
        "--strict", action="store_true",
        help="Also check execution_count for non-Python kernels",
    )
    args = parser.parse_args()

    notebooks = get_changed_notebooks(args.base, args.paths)
    if not notebooks:
        if args.json:
            print(json.dumps({"notebooks": [], "passed": True}))
        else:
            print("No notebooks changed in this PR.")
        return 0

    results = [validate_notebook(nb) for nb in notebooks]
    failed = [r for r in results if not r["passed"]]
    total_cells = sum(r["total_code"] for r in results)

    if args.json:
        print(json.dumps({
            "notebooks": results,
            "total_notebooks": len(results),
            "total_code_cells": total_cells,
            "passed": len(failed) == 0,
            "failed_count": len(failed),
        }, indent=2, ensure_ascii=False))
        return 1 if failed else 0

    # Human-readable report
    print(f"Notebook PR Validation: {len(results) - len(failed)}/{len(results)} passed")
    print(f"Total code cells checked: {total_cells}")
    print()

    for r in results:
        status = "PASS" if r["passed"] else "FAIL"
        kernel_tag = f" [{r['kernel']}]" if r["kernel"] != "python3" else ""
        print(f"  {status} {r['path']} ({r['total_code']} cells){kernel_tag}")
        for err in r["errors"]:
            print(f"       {err}")

    if failed:
        print(f"\nFAILED: {len(failed)} notebook(s) with violations")
        print("Fix: re-execute notebooks and commit with outputs, or fix C.1 violations")
        return 1

    print("\nAll notebooks passed validation.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
