#!/usr/bin/env python3
"""Diagnose BROKEN notebooks and categorize root causes.

Reads COURSE_CATALOG.generated.json and opens each BROKEN notebook to
extract error messages, then classifies root causes.

Usage:
    python diagnose_broken.py                       # Full diagnostic
    python diagnose_broken.py --serie Sudoku        # Filter by serie
    python diagnose_broken.py --summary              # Summary only (no per-notebook details)
    python diagnose_broken.py --json                 # JSON output for scripts

Root cause categories:
    MISSING_DEP     — ImportError / ModuleNotFoundError
    KERNEL_ERROR    — .NET / Lean kernel not available locally
    API_KEY         — API key required but not configured
    RUNTIME_ERROR   — General Python/runtime error
    NO_OUTPUTS      — No outputs at all (never executed)
    TEMPLATE        — Template file, not a real notebook
    UNKNOWN         — Error type not classified
"""

import argparse
import json
import re
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

# Error classification patterns (order matters — first match wins)
ERROR_PATTERNS = [
    (r"ImportError|ModuleNotFoundError", "MISSING_DEP"),
    (r"No module named", "MISSING_DEP"),
    (r"cannot import name", "MISSING_DEP"),
    (r"OSError.*cannot load library|DLL load failed", "MISSING_DEP"),
    (r".*kernel.*not found|No such kernel|Kernel not available", "KERNEL_ERROR"),
    (r".*interactive.*not supported|C# kernel", "KERNEL_ERROR"),
    (r"api_key|API_KEY|OPENAI_API|ANTHROPIC_API|HUGGINGFACE|OpenAIError|The api_key client option", "API_KEY"),
    (r"401|403|Unauthorized|Authentication", "API_KEY"),
    (r"FileNotFoundError|No such file or directory", "RUNTIME_ERROR"),
    (r"TypeError|ValueError|AttributeError|KeyError|IndexError", "RUNTIME_ERROR"),
    (r"SyntaxError|IndentationError", "RUNTIME_ERROR"),
    (r"ZeroDivisionError|OverflowError", "RUNTIME_ERROR"),
    (r"TimeoutError|timeout|timed out", "RUNTIME_ERROR"),
    (r"CUDA|out of memory|OOM", "RUNTIME_ERROR"),
    (r"ConnectionError|ConnectionRefused", "RUNTIME_ERROR"),
    (r"compilation error", "KERNEL_ERROR"),
    (r"System\..*Exception", "KERNEL_ERROR"),
    (r"FileNotFoundException", "RUNTIME_ERROR"),
    (r"NameError.*is not defined", "RUNTIME_ERROR"),
]


def classify_error(ename: str, traceback: str) -> str:
    """Classify an error by its name and traceback."""
    text = f"{ename}\n{traceback}"
    for pattern, category in ERROR_PATTERNS:
        if re.search(pattern, text, re.IGNORECASE):
            return category
    return "UNKNOWN"


def extract_errors(notebook: dict) -> list[dict]:
    """Extract error details from notebook cells."""
    errors = []
    for cell in notebook.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for output in cell.get("outputs", []):
            if output.get("output_type") == "error":
                ename = output.get("ename", "Unknown")
                evalue = output.get("evalue", "")
                traceback = "\n".join(output.get("traceback", []))
                errors.append({
                    "ename": ename,
                    "evalue": evalue,
                    "traceback": traceback,
                })
    return errors


def is_template(entry: dict) -> bool:
    """Check if notebook is a template file."""
    name = entry["path"].lower()
    return "template" in name or "squelette" in name


def diagnose_notebook(entry: dict) -> dict:
    """Diagnose a single BROKEN notebook."""
    nb_path = NOTEBOOKS_DIR / entry["path"]

    if is_template(entry):
        return {
            "path": entry["path"],
            "serie": entry["serie"],
            "root_cause": "TEMPLATE",
            "errors": [],
        }

    if not nb_path.exists():
        return {
            "path": entry["path"],
            "serie": entry["serie"],
            "root_cause": "FILE_MISSING",
            "errors": [],
        }

    try:
        notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return {
            "path": entry["path"],
            "serie": entry["serie"],
            "root_cause": "CORRUPT",
            "errors": [],
        }

    errors = extract_errors(notebook)

    if not errors and entry["cells_with_outputs"] == 0:
        root_cause = "NO_OUTPUTS"
    elif errors:
        # Classify ALL errors, prefer API_KEY over MISSING_DEP when both present
        # (many ML notebooks first fail on langchain import, then reveal api_key issue)
        all_causes = []
        for err in errors:
            text = f"{err['ename']}\n{err['evalue']}\n{err['traceback']}"
            cause = "UNKNOWN"
            for pattern, category in ERROR_PATTERNS:
                if re.search(pattern, text, re.IGNORECASE):
                    cause = category
                    break
            all_causes.append(cause)

        # Prefer API_KEY over MISSING_DEP if both present
        if "API_KEY" in all_causes:
            root_cause = "API_KEY"
        else:
            root_cause = all_causes[0]
    else:
        root_cause = "UNKNOWN"

    return {
        "path": entry["path"],
        "serie": entry["serie"],
        "kernel": entry.get("kernel", "unknown"),
        "root_cause": root_cause,
        "num_errors": len(errors),
        "errors": [
            {"ename": e["ename"], "evalue": e["evalue"][:200]}
            for e in errors[:3]
        ],
    }


def generate_report(results: list[dict], summary_only: bool = False) -> str:
    """Generate human-readable report."""
    lines = ["# BROKEN Notebooks Diagnostic", ""]

    # Summary by root cause
    cause_counts = Counter(r["root_cause"] for r in results)
    cause_order = [
        "NO_OUTPUTS", "MISSING_DEP", "KERNEL_ERROR", "API_KEY",
        "RUNTIME_ERROR", "TEMPLATE", "FILE_MISSING", "CORRUPT", "UNKNOWN",
    ]

    lines.extend([
        "## Summary by Root Cause",
        "",
        "| Root Cause | Count |",
        "|------------|-------|",
    ])
    for cause in cause_order:
        if cause in cause_counts:
            lines.append(f"| {cause} | {cause_counts[cause]} |")
    for cause in sorted(cause_counts):
        if cause not in cause_order:
            lines.append(f"| {cause} | {cause_counts[cause]} |")
    lines.append(f"| **TOTAL** | **{len(results)}** |")
    lines.append("")

    # Summary by serie
    serie_causes = {}
    for r in results:
        s = r["serie"]
        serie_causes.setdefault(s, Counter())[r["root_cause"]] += 1

    lines.extend([
        "## Summary by Serie",
        "",
        "| Serie | Total | Root Causes |",
        "|-------|-------|-------------|",
    ])
    for serie in sorted(serie_causes):
        causes = serie_causes[serie]
        total = sum(causes.values())
        cause_str = ", ".join(f"{c}:{n}" for c, n in causes.most_common())
        lines.append(f"| {serie} | {total} | {cause_str} |")
    lines.append("")

    if not summary_only:
        # Per-notebook details
        by_cause = {}
        for r in results:
            by_cause.setdefault(r["root_cause"], []).append(r)

        for cause in cause_order:
            if cause not in by_cause:
                continue
            items = by_cause[cause]
            lines.extend([
                f"## {cause} ({len(items)} notebooks)",
                "",
                "| Serie | Notebook | Errors | Detail |",
                "|-------|----------|--------|--------|",
            ])
            for r in items:
                name = r["path"].split("/")[-1]
                num_err = r.get("num_errors", 0)
                detail = ""
                if r.get("errors"):
                    e = r["errors"][0]
                    detail = f"{e['ename']}: {e['evalue'][:60]}"
                lines.append(
                    f"| {r['serie']} | {name[:50]} | {num_err} | {detail} |"
                )
            lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Diagnose BROKEN notebooks and categorize root causes"
    )
    parser.add_argument(
        "--serie", type=str, default=None,
        help="Filter by serie",
    )
    parser.add_argument(
        "--summary", action="store_true",
        help="Summary only (no per-notebook details)",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output JSON for scripts",
    )
    parser.add_argument(
        "--output", type=str, default=None,
        help="Output file path (default: stdout)",
    )
    args = parser.parse_args()

    if not CATALOG_PATH.exists():
        print(f"Error: {CATALOG_PATH} not found. Run generate_catalog.py first.")
        return

    catalog = json.loads(CATALOG_PATH.read_text(encoding="utf-8"))

    broken = [
        e for e in catalog
        if e.get("status") == "BROKEN"
        and (args.serie is None or e.get("serie") == args.serie)
    ]

    results = [diagnose_notebook(e) for e in broken]

    if args.json:
        output = json.dumps(results, indent=2, ensure_ascii=False)
    else:
        output = generate_report(results, summary_only=args.summary)

    if args.output:
        Path(args.output).write_text(output, encoding="utf-8")
        print(f"Written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
