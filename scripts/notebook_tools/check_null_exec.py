#!/usr/bin/env python3
"""H.3 pre-commit hook: refuse un-executed notebooks at commit time.

Scans .ipynb files for code cells with ``execution_count == null`` AND empty
``outputs`` -- a C.2/H.3 violation (a committed notebook must prove it ran).
Exits 1 if any such cell is found, 0 otherwise.

A null ``execution_count`` is TOLERATED (not a violation) exactly where local
execution is also impossible or unsafe, reusing the canonical predicates from
``validate_pr_notebooks.py`` (single source of truth -- no divergence):

  - lean kernels (``ALLOW_NULL_EXEC_COUNT_KERNELS``: lean4 / lean4-wsl / lean),
  - QC Cloud notebooks (``_is_qc_cloud``: QC path fast-path, ``qc_reference``
    metadata flag, or a cell instantiating ``QuantBook()`` -- the QuantBook
    runtime exists on no worker machine),
  - PII-governed notebooks (``metadata.pii_no_output: true`` -- e.g.
    GradeBook.ipynb, where empty outputs are the compliant state; running it
    locally would leak student PII, #8830).

.NET Interactive is deliberately NOT tolerated: ``dotnet-interactive`` runs on
every worker, so a committed .NET cell MUST carry a real execution_count (cf.
the Tweety-3 incident, PRs #5194/#5199/#5202 merged at null+empty).

Usage -- pre-commit (``pass_filenames: true``):
    python scripts/notebook_tools/check_null_exec.py <staged.ipynb> [...]

Standalone:
    python scripts/notebook_tools/check_null_exec.py --all     # whole-repo scan
    python scripts/notebook_tools/check_null_exec.py --check   # CI parity (exit 1)

See #9888 (inert pre-commit harness) and
docs/reference/regles-validation-detail.md (H.3 -- "verification pre-commit
obligatoire").
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Reuse the canonical predicates so this hook never diverges from the CI/PR
# gate (validate_pr_notebooks.py). Same package -> direct import.
from validate_pr_notebooks import (  # noqa: E402
    ALLOW_NULL_EXEC_COUNT_KERNELS,
    PII_NO_OUTPUT_KEY,
    REPO_ROOT,
    _is_qc_cloud,
    get_kernel_name,
)

__all__ = ["scan_notebook", "main"]


def _code_cells(data: dict) -> list[tuple[int, dict]]:
    """Yield (index, cell) for code cells in notebook JSON ``data``."""
    out = []
    for i, cell in enumerate(data.get("cells", [])):
        if cell.get("cell_type") == "code":
            out.append((i, cell))
    return out


def _is_null_unexecuted(cell: dict) -> bool:
    """True if a code cell has execution_count == null AND empty outputs.

    This is the precise C.2/H.3 violation: the cell never ran (no count) and
    produced nothing (no outputs). A cell with outputs but a null count, or a
    count but empty outputs, is not this violation (handled elsewhere).
    """
    if cell.get("execution_count") is not None:
        return False
    outputs = cell.get("outputs", [])
    return not outputs


def scan_notebook(nb_path: Path) -> list[str]:
    """Return a list of violation messages for ``nb_path`` (empty if clean).

    A notebook is clean if every code cell has a non-null execution_count, OR
    its kernel/runtime makes local execution impossible (lean / QC Cloud).
    """
    try:
        data = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as exc:
        # Unparseable notebook: report as a violation (the worker should see it
        # before commit), but do not crash the hook.
        return [f"{nb_path}: cannot parse ({exc.__class__.__name__})"]

    kernel = get_kernel_name(nb_path)
    try:
        rel_path = str(nb_path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        rel_path = str(nb_path)

    # Tolerated-null runtimes: local execution is also impossible or unsafe, so
    # a null count is not worker negligence. Three declared carve-outs, matching
    # validate_pr_notebooks.py exactly (allow_null_exec_count predicate):
    #   - lean kernels (rendering subtleties, local install not universal),
    #   - QC Cloud notebooks (QuantBook runtime on no worker machine),
    #   - PII-governed notebooks (metadata.pii_no_output: true -- e.g.
    #     GradeBook.ipynb, whose empty outputs are the COMPLIANT state: running
    #     it locally would leak student PII to a public repo, #8830).
    if any(k in kernel for k in ALLOW_NULL_EXEC_COUNT_KERNELS):
        return []
    if _is_qc_cloud(rel_path, data):
        return []
    if data.get("metadata", {}).get(PII_NO_OUTPUT_KEY) is True:
        return []

    violations: list[str] = []
    for idx, cell in _code_cells(data):
        if _is_null_unexecuted(cell):
            violations.append(
                f"{rel_path}: cell {idx} code "
                f"(kernel={kernel}) execution_count=null + outputs=[] "
                f"-- H.3 violation (execute the cell before commit)"
            )
    return violations


def _collect_targets(args: argparse.Namespace) -> list[Path]:
    """Resolve the list of notebooks to scan from CLI args."""
    if args.all or args.check:
        root = Path(__file__).resolve().parents[2]
        return sorted(root.rglob("*.ipynb"))
    paths = [Path(p) for p in args.files]
    # Filter to .ipynb that exist (pre-commit may pass deleted files).
    return [p for p in paths if p.suffix == ".ipynb" and p.exists()]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="H.3 pre-commit hook: refuse un-executed notebooks."
    )
    parser.add_argument(
        "files",
        nargs="*",
        help="Notebook paths to check (pre-commit passes staged files).",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Scan every .ipynb in the repo (standalone audit).",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="CI parity mode: whole-repo scan, exit 1 if any violation.",
    )
    args = parser.parse_args(argv)

    targets = _collect_targets(args)
    if not targets:
        return 0

    all_violations: list[str] = []
    for nb_path in targets:
        all_violations.extend(scan_notebook(nb_path))

    if all_violations:
        print(
            f"H.3 pre-commit: {len(all_violations)} un-executed cell(s) "
            f"refused (execution_count=null + outputs=[]):",
            file=sys.stderr,
        )
        for v in all_violations:
            print(f"  - {v}", file=sys.stderr)
        print(
            "Re-execute the notebook locally and re-stage, or (QC Cloud / "
            "lean) the notebook is auto-tolerated -- check the kernel.",
            file=sys.stderr,
        )
        return 1

    scanned = len(targets)
    print(f"H.3 pre-commit: {scanned} notebook(s) OK (no null+empty code cell).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
