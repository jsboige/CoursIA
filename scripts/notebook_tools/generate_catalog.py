#!/usr/bin/env python3
"""Generate a comprehensive catalog of all notebooks in CoursIA.

Extends count_notebooks_by_series.py with per-notebook metadata:
path, title, serie, sous-serie, kernel, status, deps, requirements.

Output:
    COURSE_CATALOG.generated.json  — machine-readable
    COURSE_CATALOG.generated.md    — human-readable summary

Usage:
    python generate_catalog.py                      # Generate both files
    python generate_catalog.py --json-only           # JSON only
    python generate_catalog.py --series GenAI        # Single series
    python generate_catalog.py --check               # Report status summary
    python generate_catalog.py --status BROKEN       # Filter by status

Status heuristics (B-2 from #623):
    READY     — outputs present, 0 errors
    DEMO      — outputs present, requires API/GPU/cloud
    RESEARCH  — research/archive/examples path
    BROKEN    — errors in outputs (non-pedagogical)
"""

import argparse
import json
import re
import sys
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_ALWAYS = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "ESGF", "examples"}

SERIES_ORDER = [
    "GenAI", "Search", "ML", "SymbolicAI", "QuantConnect",
    "GameTheory", "Sudoku", "Probas", "IIT", "RL", "EPF",
]

# Keywords indicating special requirements
API_KEYWORDS = {"openai", "anthropic", "api_key", "API_KEY", "bearer", "endpoint"}
GPU_KEYWORDS = {"cuda", "gpu", "torch.device", "ComfyUI", "VRAM"}
CLOUD_KEYWORDS = {"QuantBook", "quantconnect", "qc-api", "lean-cli"}
WSL_KEYWORDS = {"wsl", "WSL"}


def detect_kernel(notebook: dict) -> str:
    """Extract kernel display name from notebook metadata."""
    ks = notebook.get("metadata", {}).get("kernelspec", {})
    return ks.get("display_name", ks.get("name", "unknown"))


def extract_title(notebook: dict) -> str:
    """Extract title from first markdown heading."""
    for cell in notebook.get("cells", []):
        if cell["cell_type"] == "markdown":
            src = "".join(cell.get("source", []))
            for line in src.split("\n"):
                line = line.strip()
                if line.startswith("#"):
                    return line.lstrip("#").strip()
    return ""


def detect_requirements(notebook: dict) -> dict:
    """Detect API/GPU/cloud/WSL requirements from notebook source."""
    all_source = ""
    for cell in notebook.get("cells", []):
        if cell["cell_type"] == "code":
            all_source += "".join(cell.get("source", [])) + "\n"

    return {
        "requires_api": any(kw in all_source for kw in API_KEYWORDS),
        "requires_gpu": any(kw in all_source for kw in GPU_KEYWORDS),
        "requires_cloud": any(kw in all_source for kw in CLOUD_KEYWORDS),
        "requires_wsl": any(kw in all_source for kw in WSL_KEYWORDS),
    }


def check_errors(outputs: list) -> list[str]:
    """Check for error outputs in a code cell's output list."""
    errors = []
    for out in outputs:
        if out.get("output_type") == "error":
            errors.append(out.get("ename", "UnknownError"))
    return errors


def determine_status(
    nb_path: Path,
    notebook: dict,
    code_cells: list,
    requirements: dict,
    pedagogical: bool,
) -> str:
    """Determine notebook status using heuristics.

    READY     — outputs present, no errors
    DEMO      — outputs present, requires external services
    RESEARCH  — in research/archive/examples path
    BROKEN    — errors in outputs
    """
    rel_path = str(nb_path.relative_to(NOTEBOOKS_DIR))

    # Research/archive path → RESEARCH
    if not pedagogical:
        return "RESEARCH"

    # Check for errors in outputs
    all_errors = []
    for cell in code_cells:
        all_errors.extend(check_errors(cell.get("outputs", [])))

    has_outputs = any(cell.get("outputs") for cell in code_cells)

    # Errors present in outputs → BROKEN
    if all_errors:
        return "BROKEN"

    # No outputs but requires cloud/api → DEMO (not locally executable)
    if not has_outputs and code_cells:
        if (requirements["requires_api"] or requirements["requires_gpu"]
                or requirements["requires_cloud"]):
            return "DEMO"
        return "BROKEN"

    # Has outputs, check external requirements
    if (requirements["requires_api"] or requirements["requires_gpu"]
            or requirements["requires_cloud"]):
        return "DEMO"

    return "READY"


def count_todos(notebook: dict) -> int:
    """Count # TODO markers across all code cells."""
    count = 0
    for cell in notebook.get("cells", []):
        if cell["cell_type"] == "code":
            src = "".join(cell.get("source", []))
            count += src.upper().count("# TODO")
    return count


def has_markdown_intro_conclusion(cells: list) -> tuple[bool, bool]:
    """Check if notebook has intro (first md cell with heading) and conclusion markers."""
    md_cells = [c for c in cells if c["cell_type"] == "markdown"]
    if not md_cells:
        return False, False

    first_src = "".join(md_cells[0].get("source", [])).lower()
    has_intro = any(kw in first_src for kw in ["introduction", "objectif", "overview", "prérequis", "contexte"])

    last_src = "".join(md_cells[-1].get("source", [])).lower()
    has_conclusion = any(
        kw in last_src for kw in ["conclusion", "résumé", "summary", "pour aller plus loin", "next steps"]
    )
    return has_intro, has_conclusion


def classify_maturity(
    notebook: dict,
    code_cells: list,
    kernel: str,
) -> str:
    """Classify notebook maturity level.

    Heuristics (B-2 from #656):
        PRODUCTION — kernel defined, all outputs, <3 TODO, intro+conclusion, structured
        BETA       — outputs present, <5 TODO, markdown structure
        ALPHA      — partial outputs OR 5-10 TODO
        DRAFT      — no outputs OR >10 TODO OR no markdown cells
    """
    cells = notebook.get("cells", [])
    md_cells = [c for c in cells if c["cell_type"] == "markdown"]
    todo_count = count_todos(notebook)
    has_intro, has_conclusion = has_markdown_intro_conclusion(cells)

    total_code = len(code_cells)
    code_with_outputs = sum(1 for c in code_cells if c.get("outputs"))
    all_have_outputs = total_code > 0 and code_with_outputs == total_code
    has_outputs = code_with_outputs > 0

    # No markdown at all → DRAFT
    if not md_cells:
        return "DRAFT"

    # No outputs on any code cell → DRAFT
    if total_code > 0 and not has_outputs:
        return "DRAFT"

    # >10 TODO → DRAFT
    if todo_count > 10:
        return "DRAFT"

    # 5-10 TODO or partial outputs → ALPHA
    if 5 <= todo_count <= 10:
        return "ALPHA"
    if total_code > 0 and not all_have_outputs:
        return "ALPHA"

    # BETA: outputs present, <5 TODO, has some markdown structure
    kernel_defined = kernel and kernel != "unknown"
    has_structure = has_intro or has_conclusion or len(md_cells) >= 3

    if has_outputs and todo_count < 5 and has_structure:
        # PRODUCTION: stricter requirements
        if kernel_defined and all_have_outputs and todo_count < 3 and has_intro and has_conclusion:
            return "PRODUCTION"
        return "BETA"

    return "ALPHA"


def analyze_notebook(nb_path: Path, pedagogical: bool) -> dict | None:
    """Analyze a single notebook and return its catalog entry."""
    try:
        notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None

    cells = notebook.get("cells", [])
    code_cells = [c for c in cells if c["cell_type"] == "code"]
    rel = nb_path.relative_to(NOTEBOOKS_DIR)
    parts = rel.parts

    # Determine serie and sous-serie
    serie = parts[0] if parts else ""
    sous_serie = parts[1] if len(parts) > 2 else ""

    title = extract_title(notebook)
    kernel = detect_kernel(notebook)
    requirements = detect_requirements(notebook)
    status = determine_status(nb_path, notebook, code_cells, requirements, pedagogical)
    maturity = classify_maturity(notebook, code_cells, kernel)

    code_with_outputs = sum(1 for c in code_cells if c.get("outputs"))
    code_without_outputs = len(code_cells) - code_with_outputs
    md_cells = sum(1 for c in cells if c["cell_type"] == "markdown")

    return {
        "path": str(rel).replace("\\", "/"),
        "title": title or nb_path.stem,
        "serie": serie,
        "sous_serie": sous_serie,
        "kernel": kernel,
        "status": status,
        "maturity": maturity,
        "cells_total": len(cells),
        "cells_code": len(code_cells),
        "cells_markdown": md_cells,
        "cells_with_outputs": code_with_outputs,
        "cells_without_outputs": code_without_outputs,
        "requires_api": requirements["requires_api"],
        "requires_gpu": requirements["requires_gpu"],
        "requires_cloud": requirements["requires_cloud"],
        "requires_wsl": requirements["requires_wsl"],
        "executable_locally": (
            not requirements["requires_api"]
            and not requirements["requires_gpu"]
            and not requirements["requires_cloud"]
            and not requirements["requires_wsl"]
        ),
    }


def scan_all_notebooks(
    pedagogical: bool = True,
    series_filter: str | None = None,
) -> list[dict]:
    """Scan all notebooks and return catalog entries."""
    entries = []
    dirs = sorted(NOTEBOOKS_DIR.iterdir()) if not series_filter else [
        NOTEBOOKS_DIR / series_filter
    ]

    for series_dir in dirs:
        if not series_dir.is_dir():
            continue
        if series_dir.name in EXCLUDE_ALWAYS or series_dir.name.startswith("."):
            continue

        for nb_path in sorted(series_dir.rglob("*.ipynb")):
            parts = nb_path.relative_to(series_dir).parts
            if any(exc in part for part in parts for exc in EXCLUDE_ALWAYS):
                continue
            if pedagogical and any(
                exc in str(nb_path.relative_to(series_dir))
                for exc in EXCLUDE_PEDAGOGICAL
            ):
                continue

            entry = analyze_notebook(nb_path, pedagogical)
            if entry:
                entries.append(entry)

    return entries


def generate_markdown_report(entries: list[dict]) -> str:
    """Generate a human-readable markdown summary."""
    by_serie = {}
    status_counts = {}
    for e in entries:
        s = e["serie"]
        by_serie.setdefault(s, []).append(e)
        status_counts[e["status"]] = status_counts.get(e["status"], 0) + 1

    lines = [
        f"# CoursIA Notebook Catalog",
        f"",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        f"Total notebooks: {len(entries)}",
        f"",
        f"## Status Summary",
        f"",
    ]
    for status in ["READY", "DEMO", "RESEARCH", "BROKEN"]:
        count = status_counts.get(status, 0)
        lines.append(f"- **{status}**: {count}")

    # Maturity summary
    maturity_counts = {}
    for e in entries:
        maturity_counts[e.get("maturity", "UNKNOWN")] = (
            maturity_counts.get(e.get("maturity", "UNKNOWN"), 0) + 1
        )
    lines.extend(["", "## Maturity Summary", ""])
    for maturity in ["PRODUCTION", "BETA", "ALPHA", "DRAFT"]:
        count = maturity_counts.get(maturity, 0)
        lines.append(f"- **{maturity}**: {count}")

    lines.extend(["", "## By Series", ""])
    for serie in SERIES_ORDER:
        if serie not in by_serie:
            continue
        items = by_serie[serie]
        statuses = {}
        for e in items:
            statuses[e["status"]] = statuses.get(e["status"], 0) + 1
        status_str = ", ".join(
            f"{s}:{c}" for s, c in sorted(statuses.items())
        )
        maturities = {}
        for e in items:
            maturities[e.get("maturity", "UNKNOWN")] = (
                maturities.get(e.get("maturity", "UNKNOWN"), 0) + 1
            )
        mat_str = ", ".join(
            f"{m}:{c}" for m, c in sorted(maturities.items())
        )
        lines.append(f"### {serie} ({len(items)} notebooks) — {status_str} | {mat_str}")
        lines.append("")
        lines.append(f"| # | Notebook | Kernel | Status | Maturity |")
        lines.append(f"|---|----------|--------|--------|----------|")
        for i, e in enumerate(items, 1):
            name = e["title"][:50]
            kernel = e["kernel"][:30]
            maturity = e.get("maturity", "UNKNOWN")
            lines.append(f"| {i} | {name} | {kernel} | {e['status']} | {maturity} |")
        lines.append("")

    # Requirements summary
    req_counts = {
        "API": sum(1 for e in entries if e["requires_api"]),
        "GPU": sum(1 for e in entries if e["requires_gpu"]),
        "Cloud": sum(1 for e in entries if e["requires_cloud"]),
        "WSL": sum(1 for e in entries if e["requires_wsl"]),
        "Local": sum(1 for e in entries if e["executable_locally"]),
    }
    lines.extend(["", "## Requirements", ""])
    for req, count in req_counts.items():
        lines.append(f"- **{req}**: {count} notebooks")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate CoursIA notebook catalog"
    )
    parser.add_argument(
        "--json-only", action="store_true",
        help="Output JSON only (no markdown)",
    )
    parser.add_argument(
        "--md-only", action="store_true",
        help="Output markdown only (no JSON)",
    )
    parser.add_argument(
        "--series", type=str, default=None,
        help="Scan only a specific series",
    )
    parser.add_argument(
        "--check", action="store_true",
        help="Print status summary and exit",
    )
    parser.add_argument(
        "--status", type=str, default=None,
        choices=["READY", "DEMO", "RESEARCH", "BROKEN"],
        help="Filter entries by status",
    )
    parser.add_argument(
        "--maturity", type=str, default=None,
        choices=["PRODUCTION", "BETA", "ALPHA", "DRAFT"],
        help="Filter entries by maturity level",
    )
    parser.add_argument(
        "--all", action="store_true",
        help="Include research, examples, and archive notebooks",
    )
    parser.add_argument(
        "--output-dir", type=str, default=str(REPO_ROOT),
        help="Output directory for generated files",
    )
    args = parser.parse_args()

    pedagogical = not args.all
    entries = scan_all_notebooks(pedagogical=pedagogical, series_filter=args.series)

    if args.status:
        entries = [e for e in entries if e["status"] == args.status]

    if args.maturity:
        entries = [e for e in entries if e.get("maturity") == args.maturity]

    if args.check:
        status_counts = {}
        maturity_counts = {}
        for e in entries:
            status_counts[e["status"]] = status_counts.get(e["status"], 0) + 1
            m = e.get("maturity", "UNKNOWN")
            maturity_counts[m] = maturity_counts.get(m, 0) + 1
        print(f"\nCatalog Status Summary ({len(entries)} notebooks)")
        print("=" * 40)
        for status in ["READY", "DEMO", "RESEARCH", "BROKEN"]:
            count = status_counts.get(status, 0)
            print(f"  {status:<12} {count:>4}")
        print("-" * 40)
        for maturity in ["PRODUCTION", "BETA", "ALPHA", "DRAFT"]:
            count = maturity_counts.get(maturity, 0)
            print(f"  {maturity:<12} {count:>4}")
        print("=" * 40)
        print(f"  {'TOTAL':<12} {len(entries):>4}")
        return

    out_dir = Path(args.output_dir)

    if not args.md_only:
        json_path = out_dir / "COURSE_CATALOG.generated.json"
        json_path.write_text(
            json.dumps(entries, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"JSON: {json_path} ({len(entries)} entries)")

    if not args.json_only:
        md_path = out_dir / "COURSE_CATALOG.generated.md"
        report = generate_markdown_report(entries)
        md_path.write_text(report, encoding="utf-8")
        print(f"MD:  {md_path}")


if __name__ == "__main__":
    main()
