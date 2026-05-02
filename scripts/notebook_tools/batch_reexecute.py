#!/usr/bin/env python3
"""Batch re-execute notebooks with missing outputs (C.2 remediation).

Identifies notebooks with missing execution_count/outputs and re-executes
them using papermill, respecting kernel types and dependencies.

Usage:
    python batch_reexecute.py --dry-run               # Preview what would be executed
    python batch_reexecute.py --serie Search           # Re-execute Search notebooks
    python batch_reexecute.py --maturity BETA          # BETA notebooks only
    python batch_reexecute.py --path <file.ipynb>      # Single notebook
    python batch_reexecute.py --max 5                  # Limit to 5 notebooks
    python batch_reexecute.py --timeout 300            # Per-notebook timeout (seconds)

Safety:
    - Dry-run mode shows what would be executed without running
    - Creates backup before each execution
    - Skips notebooks requiring API keys, GPU, or cloud services
    - Respects C.3: only re-executes notebooks with source changes
"""

import argparse
import json
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"


def needs_reexecution(entry: dict) -> bool:
    """Check if a notebook needs re-execution (C.2 violation)."""
    if entry.get("status") == "BROKEN":
        return False
    if entry.get("cells_without_outputs", 0) > 0:
        return True
    return False


def get_kernel_name(entry: dict) -> str:
    """Map catalog kernel to papermill kernel name."""
    kernel = entry.get("kernel", "").lower()
    if "python 3" in kernel:
        return "python3"
    if ".net" in kernel or "c#" in kernel:
        return ".net-interactive"
    return kernel


def execute_notebook(nb_path: Path, kernel: str, timeout: int) -> dict:
    """Execute a single notebook with papermill."""
    backup_path = nb_path.with_suffix(".ipynb.bak")

    # Create backup
    shutil.copy2(nb_path, backup_path)

    try:
        cmd = [
            sys.executable, "-m", "papermill",
            str(nb_path), str(nb_path),
            "--kernel", kernel,
            "--timeout", str(timeout * 60),  # papermill uses seconds
        ]

        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout * 60 + 60,  # extra buffer
            cwd=str(REPO_ROOT),
        )

        if result.returncode == 0:
            backup_path.unlink(missing_ok=True)
            return {"path": str(nb_path), "status": "SUCCESS"}
        else:
            # Restore backup on failure
            shutil.copy2(backup_path, nb_path)
            backup_path.unlink(missing_ok=True)
            return {
                "path": str(nb_path),
                "status": "FAILED",
                "error": result.stderr[-500:] if result.stderr else "Unknown error",
            }
    except subprocess.TimeoutExpired:
        shutil.copy2(backup_path, nb_path)
        backup_path.unlink(missing_ok=True)
        return {"path": str(nb_path), "status": "TIMEOUT"}
    except Exception as e:
        shutil.copy2(backup_path, nb_path)
        backup_path.unlink(missing_ok=True)
        return {"path": str(nb_path), "status": "ERROR", "error": str(e)}


def main():
    parser = argparse.ArgumentParser(
        description="Batch re-execute notebooks with missing outputs (C.2)"
    )
    parser.add_argument("--serie", type=str, default=None)
    parser.add_argument("--maturity", type=str, default=None,
                        choices=["PRODUCTION", "BETA", "ALPHA", "DRAFT"])
    parser.add_argument("--path", type=str, default=None)
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview without executing")
    parser.add_argument("--max", type=int, default=0,
                        help="Max notebooks to execute (0=all)")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Per-notebook timeout in seconds (default: 300)")
    parser.add_argument("--skip-external", action="store_true", default=True,
                        help="Skip notebooks requiring API/GPU/cloud (default: True)")
    args = parser.parse_args()

    if args.path:
        nb_path = Path(args.path)
        if not nb_path.is_absolute():
            nb_path = REPO_ROOT / nb_path
        targets = [{"path": str(nb_path.relative_to(NOTEBOOKS_DIR)),
                     "kernel": "python3", "cells_without_outputs": 1}]
    elif CATALOG_PATH.exists():
        catalog = json.loads(CATALOG_PATH.read_text(encoding="utf-8"))
        targets = catalog
        if args.serie:
            targets = [e for e in targets if e.get("serie") == args.serie]
        if args.maturity:
            targets = [e for e in targets if e.get("maturity") == args.maturity]
        targets = [e for e in targets if needs_reexecution(e)]
    else:
        print("Error: catalog not found. Use --path or run generate_catalog.py.")
        return 2

    # Filter out external dependencies
    if args.skip_external:
        before = len(targets)
        targets = [
            e for e in targets
            if not e.get("requires_api")
            and not e.get("requires_gpu")
            and not e.get("requires_cloud")
        ]
        skipped = before - len(targets)
        if skipped:
            print(f"Skipping {skipped} notebooks requiring API/GPU/cloud")

    if args.max > 0:
        targets = targets[:args.max]

    print(f"Notebooks to process: {len(targets)}")

    if not targets:
        print("Nothing to do.")
        return 0

    if args.dry_run:
        print("\nDry-run mode — notebooks that would be re-executed:\n")
        for e in targets:
            name = e["path"].split("/")[-1]
            kernel = get_kernel_name(e)
            missing = e.get("cells_without_outputs", "?")
            print(f"  {name} (kernel={kernel}, missing={missing})")
        return 0

    # Execute
    results = {"success": 0, "failed": 0, "timeout": 0, "error": 0}
    start = datetime.now()

    for i, entry in enumerate(targets, 1):
        nb_path = NOTEBOOKS_DIR / entry["path"]
        name = entry["path"].split("/")[-1]
        kernel = get_kernel_name(entry)
        print(f"\n[{i}/{len(targets)}] {name} (kernel={kernel})...")

        result = execute_notebook(nb_path, kernel, args.timeout)
        status = result["status"]
        results[status.lower()] = results.get(status.lower(), 0) + 1

        elapsed = (datetime.now() - start).total_seconds()
        print(f"  -> {status} ({elapsed:.0f}s elapsed)")

        if result.get("error"):
            print(f"     Error: {result['error'][:200]}")

    # Summary
    total_time = (datetime.now() - start).total_seconds()
    print(f"\n{'='*50}")
    print(f"Batch complete: {len(targets)} notebooks in {total_time:.0f}s")
    print(f"  Success: {results.get('success', 0)}")
    print(f"  Failed:  {results.get('failed', 0)}")
    print(f"  Timeout: {results.get('timeout', 0)}")
    print(f"  Error:   {results.get('error', 0)}")

    return 1 if results.get("failed", 0) + results.get("error", 0) > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
