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

# Shared C.1 detector (#1505): digit-bounded regex, comment/docstring-aware.
# Both this CI gate and notebook_lint.py consume the same scanner so the two
# C.1 checkers can never diverge again (the old substring match here flagged
# dates like "21/02/2022" because "1/0" is a substring of "1/02").
sys.path.insert(0, str(Path(__file__).resolve().parent))
from notebook_lint import scan_c1_source

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# Kernels that cannot be Papermill-executed in CI. The CI re-exec gate is
# advisory for these (no kernel to re-run), but C.1 + structural validity are
# still enforced. NOTE: "CI can't re-run" is NOT the same as "outputs may be
# empty" — see ALLOW_NULL_EXEC_COUNT_KERNELS for that finer distinction (#5214).
SKIP_EXEC_KERNELS = {
    ".net-csharp", ".net-fsharp", ".net-powershell",
    "lean4", "lean4-wsl", "lean",
}

# Where a NULL execution_count is genuinely tolerated (#5214): the reviewer
# CANNOT execute the notebook locally either. Two cases:
#  - QC Cloud needs the QuantBook runtime (nowhere on a worker machine).
#  - Lean is kept advisory for now (its own rendering subtleties via
#    lean4_jupyter/alectryon, and #5214 scopes the change to .NET).
# .NET Interactive is EXCLUDED on purpose: dotnet-interactive runs on every
# worker machine (the 6 older Tweety ports — Dung, Aspic, 2b, 2c — are
# committed with real execution_count + outputs as proof), so a committed
# .NET cell MUST prove local execution (execution_count != null). The
# incident: PRs #5194/#5199/#5202 (Tweety-3 C#) were merged with notebooks at
# execution_count:null + outputs:[] — a C.2 violation the old advisory let
# through because it fused "CI skip" with "outputs may be empty".
ALLOW_NULL_EXEC_COUNT_KERNELS = {"lean4", "lean4-wsl", "lean"}

# Paths that require QC Cloud (python3 kernel but need QuantBook runtime).
# H.3 is advisory-only for these — they can only be executed via QC Cloud.
QC_CLOUD_PATHS = ("QuantConnect/Python", "QuantConnect/projects")

# Kernels that render errors as TEXT, not as output_type=="error" (#5151).
# Lean via lean4_jupyter/alectryon embeds the compiler's own message severity
# in the cell output (text/plain + text/html). A `severity: error` message is
# an unambiguous toolchain error (failed import, unknown identifier, unsolved
# goals, ...) that the output_type=="error" check misses entirely — a whole
# Lean notebook can be red (every cell ❌) while CI stays green, because the
# alectryon renderer never emits a Jupyter error output. We anchor on the
# toolchain-emitted severity string, so notebook *prose* that merely discusses
# errors does not trip it (verified: 0 false positives on clean Lean
# notebooks). A cell tagged "raises-exception" (the standard Jupyter/nbval
# marker for an intentionally-erroring teaching cell) is exempt.
TEXT_RENDERED_ERROR_SIGNATURES = ('"severity": "error"', '"severity":"error"')


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


def _output_text(output: dict) -> str:
    """Concatenate the textual payload of an output so text-rendered errors
    (Lean/alectryon) can be scanned. Covers display_data / execute_result
    (text/plain + text/html) and stream outputs."""
    parts = []
    otype = output.get("output_type")
    if otype in ("display_data", "execute_result"):
        data = output.get("data", {})
        for mime in ("text/plain", "text/html"):
            v = data.get(mime, "")
            parts.append("".join(v) if isinstance(v, list) else str(v))
    elif otype == "stream":
        t = output.get("text", "")
        parts.append("".join(t) if isinstance(t, list) else str(t))
    return " ".join(parts)


def _is_qc_cloud(rel_path: str, data: dict) -> bool:
    """Whether a notebook can ONLY be executed via QC Cloud (so a null
    execution_count is tolerated everywhere — CI AND local). True if the path
    is under a QC Cloud directory OR the notebook is explicitly flagged as a
    QC reference template (metadata.qc_reference=True, content-aware unification
    with regression_scan.py:261 / #3776)."""
    normalized = rel_path.replace("\\", "/")
    if any(p in normalized for p in QC_CLOUD_PATHS):
        return True
    return data.get("metadata", {}).get("qc_reference") is True


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
    # "CI cannot Papermill-execute this kernel" — the CI re-exec gate is
    # advisory, and H.1 error outputs are advisory (expected without the
    # kernel/runtime). Covers .NET, Lean, QC Cloud, qc_reference templates.
    qc_cloud = _is_qc_cloud(rel_path, data)
    ci_reexec_skipped = any(k in kernel for k in SKIP_EXEC_KERNELS) or qc_cloud
    # "A null execution_count is tolerated" — STRICTER than ci_reexec_skipped.
    # Only where local execution is ALSO impossible (QC Cloud needs QuantBook;
    # Lean kept advisory for now — own rendering subtleties, out of #5214).
    # .NET Interactive runs locally (dotnet-interactive on every worker) → a
    # committed .NET cell MUST carry execution_count != null = EXEC_PROVED
    # (#5214: "CI skip .NET" != "outputs may be empty"). The Tweety-3 cluster
    # (#5194/#5199/#5202) was merged at execution_count:null + outputs:[].
    allow_null_exec_count = (
        any(k in kernel for k in ALLOW_NULL_EXEC_COUNT_KERNELS) or qc_cloud
    )
    saw_null_exec = False  # for the forensic verdict (H.5)

    for i, cell in enumerate(data.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue

        source = "".join(cell.get("source", []))
        if not source.strip():
            continue

        # Skip comment-only cells. Comment syntax is kernel-dependent: in Lean,
        # '#check' / '#eval' / '#print' / '#reduce' are COMMANDS (comments are
        # '--'), so the Python-centric '#' heuristic would wrongly skip real
        # Lean command cells — and with them any error output they carry
        # (#5151: the failing '#print axioms' / '#check' cells were skipped;
        # the notebook was only caught by its failing 'import' cell).
        comment_prefix = "--" if "lean" in kernel else "#"
        lines = [l.strip() for l in source.split("\n") if l.strip()]
        if all(l.startswith(comment_prefix) for l in lines):
            continue

        result["total_code"] += 1

        # C.1 check: forbidden patterns via the shared digit-bounded,
        # comment/docstring-aware scanner (#1505 — no more date false positives)
        for _line, desc in scan_c1_source(source):
            result["passed"] = False
            result["errors"].append(
                f"cell {i}: C.1 violation — '{desc}' found"
            )

        # H.3 check: execution_count must not be null. Advisory ONLY where local
        # execution is impossible too (QC Cloud / Lean — allow_null_exec_count).
        # .NET Interactive executes locally, so a null execution_count is a C.2
        # violation (commit proof of local execution); "CI skip" is not a
        # license to ship empty outputs (#5214).
        if not allow_null_exec_count:
            exec_count = cell.get("execution_count")
            if exec_count is None:
                saw_null_exec = True
                result["passed"] = False
                result["errors"].append(
                    f"cell {i}: execution_count is null "
                    f"(H.3/C.2 violation — {kernel} executes locally; "
                    f"commit execution proof, See #5214)"
                )

        # H.1 check: no error outputs. Two rendering paths:
        #  (a) output_type == "error" — Python/IPython, .NET Interactive.
        #      Advisory for QC Cloud reference cells (errors expected without
        #      the QuantBook runtime).
        #  (b) text-rendered errors — Lean (lean4_jupyter/alectryon) embeds the
        #      compiler's `severity: error` in text output and NEVER emits
        #      output_type=error, so (a) misses it (incident #5151: notebook
        #      red top-to-bottom, CI green). These are ALWAYS blocking: a Lean
        #      compile error is never "expected", and QC notebooks are Python,
        #      so there is no overlap with the QC-advisory carve-out. Opt out
        #      per-cell with the "raises-exception" tag for intentional demos.
        cell_tags = cell.get("metadata", {}).get("tags", []) or []
        raises_ok = "raises-exception" in cell_tags
        for output in cell.get("outputs", []):
            if output.get("output_type") == "error":
                ename = output.get("ename", "Unknown")
                if ci_reexec_skipped:
                    result["errors"].append(
                        f"cell {i}: has error output — {ename} (advisory, QC Cloud)"
                    )
                else:
                    result["passed"] = False
                    result["errors"].append(
                        f"cell {i}: has error output — {ename}"
                    )
            elif not raises_ok and any(
                sig in _output_text(output)
                for sig in TEXT_RENDERED_ERROR_SIGNATURES
            ):
                result["passed"] = False
                result["errors"].append(
                    f"cell {i}: Lean toolchain error in output "
                    f"(severity:error — failed compile/import/proof)"
                )
                break  # one report per cell is enough

    # Forensic verdict (H.5): EXEC_PROVED / STRUCTURAL_ONLY / ADVISORY_NON_EXEC.
    # Distinguishes "real outputs present" from "structural-only / advisory" so
    # reviewers and bots apply CHANGES_REQUESTED on the second (#5214).
    if allow_null_exec_count:
        result["forensic_verdict"] = "ADVISORY_NON_EXEC"
    elif saw_null_exec:
        result["forensic_verdict"] = "STRUCTURAL_ONLY"
    else:
        result["forensic_verdict"] = "EXEC_PROVED"

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
