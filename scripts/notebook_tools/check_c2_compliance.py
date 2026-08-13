#!/usr/bin/env python3
"""Check C.2 compliance: all code cells must have execution_count and outputs.

Rule C.2: Notebooks committed WITH outputs. Every executable code cell must have
execution_count: <int> and coherent outputs. Modification of a code cell = full
re-execution before commit.

Usage:
    python check_c2_compliance.py                       # Check all pedagogical notebooks
    python check_c2_compliance.py --maturity PRODUCTION  # PRODUCTION notebooks only
    python check_c2_compliance.py --serie Search         # Single serie
    python check_c2_compliance.py --path <file.ipynb>    # Single notebook
    python check_c2_compliance.py --fix                  # Show fix suggestions
    python check_c2_compliance.py --json                 # JSON output

Exit codes:
    0 — All checked notebooks compliant
    1 — Violations found
    2 — Error (catalog not found, etc.)
"""

import argparse
import json
import sys
from pathlib import Path

# Same declared PII carve-out as the PR gate — imported, never re-spelled, so
# the two scanners cannot drift apart on the key name. A notebook whose outputs
# would embed student rosters/e-mails/marks is COMPLIANT while empty; honouring
# the flag in only one of the two scanners would leave the other still telling
# an agent to go and execute it. See validate_pr_notebooks.PII_NO_OUTPUT_KEY.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from validate_pr_notebooks import PII_NO_OUTPUT_KEY

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_ALWAYS = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "partner-course", "examples"}


def check_notebook(nb_path: Path) -> dict:
    """Check a single notebook for C.2 compliance.

    Returns dict with:
        path, total_code, violations (list of cell indices + reasons)
    """
    try:
        notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        return {
            "path": str(nb_path),
            "total_code": 0,
            "violations": [{"error": f"Cannot parse: {e}"}],
        }

    violations = []
    code_idx = 0
    # Declared PII notebook: emptiness IS the compliant state, and conversely a
    # committed output is the violation to report (symmetric, like the PR gate).
    pii_no_output = (
        notebook.get("metadata", {}).get(PII_NO_OUTPUT_KEY) is True
    )

    for i, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        code_idx += 1

        source = "".join(cell.get("source", []))
        # Skip empty code cells
        if not source.strip():
            continue

        # Skip cells that are only markdown-like comments. Both Python `#` and
        # C-family `//` (C#/.NET Interactive, JS, Java) are recognised — a `.net
        # -csharp` cell whose body is all `//` comments is a non-executable
        # transition/explanation cell, the C# mirror of a Python `#`-comment-only
        # cell, and must be skipped on the same grounds (C.2 targets executable
        # code cells, not prose). Harmonised with notebook_lint.scan_c1_source
        # and audit_c1_c3.py (cf #5261 C-family comment-awareness).
        lines = [l.strip() for l in source.split("\n") if l.strip()]
        if all(l.startswith(("#", "//")) for l in lines):
            continue

        # Check execution_count
        exec_count = cell.get("execution_count")
        outputs = cell.get("outputs", [])

        if pii_no_output:
            if outputs:
                violations.append({
                    "cell_index": i,
                    "code_cell": code_idx,
                    "reason": (
                        f"metadata.{PII_NO_OUTPUT_KEY} declared but output "
                        f"committed — personal data may be in git history"
                    ),
                    "source_preview": source[:80].replace("\n", " "),
                })
            continue

        # Skip "[REFERENCE QC]" / "Code a copier" / "non executable" cells
        # in BOTH branches (missing exec_count AND no outputs): they exist
        # as pedagogical reference material, not to run.
        if any(marker in source for marker in
               ("[REFERENCE QC]", "Code a copier", "non executable")):
            continue

        # Skip papermill parameter cells in BOTH branches: papermill injects
        # values via API at execution time, the cell intentionally produces
        # no output. Both GenAI convention ("# Parametres Papermill -
        # JAMAIS modifier ce commentaire" + BATCH_MODE) and qc-strategies
        # convention ("# Parameters" / "# Parametres notebook paper").
        if any(marker in source for marker in
               ("Parametres Papermill", "JAMAIS modifier", "# Parameters",
                "BATCH_MODE =", "notebook_mode =")):
            continue

        if exec_count is None:
            violations.append({
                "cell_index": i,
                "code_cell": code_idx,
                "reason": "missing execution_count",
                "source_preview": source[:80].replace("\n", " "),
            })
        elif not outputs and source.strip():
            # Code cell with execution_count but no outputs. Only flag if the
            # cell SHOULD produce output (top-level print/display/figure call,
            # expression statement, or function with `return`); pedagogical
            # stubs (def/class/C#-declaration) are not violations.
            # Papermill and REFERENCE-QC cells are skipped upstream (single
            # guard, covers both branches).
            stripped = source.strip()

            # Skip pure import statements (no output expected by design).
            is_import = stripped.startswith(("import ", "from "))

            # Detect if this cell's top-level statement should produce output.
            # "Top-level" = first non-comment, non-empty line; we inspect that
            # line plus any expression statement appearing after a comment block.
            #
            # An "expression that produces output" in Jupyter is:
            #   - a function call: foo(), obj.method(), etc.
            #   - a top-level expression: value, df.head(), ...
            # Function/class definitions (def/class) without `return` are stubs.
            lines = [
                l for l in source.split("\n")
                if l.strip() and not l.strip().startswith(("#", "//"))
            ]
            first_meaningful = lines[0] if lines else ""
            is_function_def = first_meaningful.startswith("def ")
            is_class_def = first_meaningful.startswith("class ")

            # Skip top-level C# / .NET Interactive declarations: `using …;`,
            # `namespace …`, `public enum …`, `public class …` (already covered
            # by `is_class_def` but `enum`/`struct`/`record` are not), and the
            # `#r "nuget: …"` package references. These are top-of-file
            # boilerplate that the kernel consumes without producing output.
            is_csharp_declaration = first_meaningful.startswith(
                ("using ", "namespace ", "public ", "private ", "internal ",
                 "protected ", "@", "#r ", "static ", "var ", "const ",
                 "[", "//", "/// ", "/*")
            ) or first_meaningful.startswith("enum ") or first_meaningful.startswith("struct ")

            # A function definition with `return` is not a stub — the function
            # was meant to be called and produce a value. Skip only the no-
            # return variant (stub).
            is_function_stub = is_function_def and "return " not in source

            # Detect output-producing top-level expression. A top-level call
            # (`foo()`, `obj.bar()`, `df.head()`) or top-level `print/display`
            # call is what triggers Jupyter's auto-output. Only column-0
            # (non-indented) occurrences count: a `print(` nested inside a
            # def/class body produces no output until the function is called
            # (PRINT_IN_DEF_FP — 73 cells flagged pre-fix were pure function
            # definitions whose body happened to call print).
            output_keywords = ("print(", "display(", "plt.", "fig", "IPython.")
            toplevel_source = "\n".join(
                line for line in source.split("\n")
                if line and not line[0].isspace()
            )
            has_output_call = any(kw in toplevel_source for kw in output_keywords)
            # `return` outside a function = a Jupyter cell that should output
            # something — but typically `return` only appears inside a `def`,
            # so this is mostly a smoke-check.
            has_top_level_return = "\nreturn " in ("\n" + source) or source.startswith("return ")

            # Top-level expression statement (not assignment): Jupyter prints
            # the value. Detected by looking at first meaningful line — if
            # it's NOT a `def`/`class`/assignment/import/C#-decl, it's an
            # expression.
            is_expression_statement = (
                bool(first_meaningful)
                and not is_function_def
                and not is_class_def
                and "=" not in first_meaningful.split("#")[0]  # not an assignment
                and not first_meaningful.startswith(("import ", "from ", "if ", "for ", "while ", "with ", "try:", "return ", "yield ", "raise ", "pass", "del ", "using ", "namespace ", "public ", "private ", "internal ", "protected ", "@", "#r ", "static ", "var ", "const ", "[", "enum ", "struct "))
            )

            expects_output = (
                has_output_call
                or has_top_level_return
                or is_expression_statement
            )

            # Skip legitimate no-output cells (C.1 stubs + C# declarations).
            skip = (
                is_import
                or is_function_stub
                or is_class_def
                or is_csharp_declaration
            )

            if expects_output and not skip:
                violations.append({
                    "cell_index": i,
                    "code_cell": code_idx,
                    "reason": "execution_count set but no outputs",
                    "source_preview": source[:80].replace("\n", " "),
                })

    return {
        "path": str(nb_path),
        "total_code": code_idx,
        "violations": violations,
    }


def get_target_notebooks(args) -> list[Path]:
    """Get list of notebooks to check based on args."""
    if args.path:
        p = Path(args.path)
        if not p.is_absolute():
            p = REPO_ROOT / p
        return [p] if p.exists() else []

    if not CATALOG_PATH.exists() or args.no_catalog:
        # Fallback: scan all notebooks
        targets = []
        for nb_path in sorted(NOTEBOOKS_DIR.rglob("*.ipynb")):
            parts = nb_path.relative_to(NOTEBOOKS_DIR).parts
            if any(exc in part for part in parts for exc in EXCLUDE_ALWAYS):
                continue
            if any(exc in str(nb_path) for exc in EXCLUDE_PEDAGOGICAL):
                continue
            targets.append(nb_path)
        return targets

    catalog = json.loads(CATALOG_PATH.read_text(encoding="utf-8"))

    entries = catalog
    if args.serie:
        entries = [e for e in entries if e.get("serie") == args.serie]
    if args.maturity:
        entries = [e for e in entries if e.get("maturity") == args.maturity]
    if args.exclude_broken:
        entries = [e for e in entries if e.get("status") != "BROKEN"]

    # ``e.get("path")`` guards a malformed/partial catalog entry that omits
    # the ``path`` key (schema drift, manual edit): the sibling filters above
    # already use ``.get()`` defensively, but the raw ``e["path"]`` access
    # below would raise KeyError and abort the whole scan. Skip such entries
    # instead of crashing — same missing-key unification as catalog_coverage
    # (#7473). ``path`` is the primary key of the generated catalog, so this
    # is unreachable via ``generate_catalog.py`` today, but defensive parity
    # with the filters is the right contract for a partial/manual catalog.
    return [
        NOTEBOOKS_DIR / e["path"]
        for e in entries
        if e.get("path") and (NOTEBOOKS_DIR / e["path"]).exists()
    ]


def main():
    parser = argparse.ArgumentParser(
        description="Check C.2 compliance: all code cells have execution_count and outputs"
    )
    parser.add_argument("--serie", type=str, default=None, help="Check single serie")
    parser.add_argument("--maturity", type=str, default=None,
                        choices=["PRODUCTION", "BETA", "ALPHA", "DRAFT"],
                        help="Filter by maturity level")
    parser.add_argument("--path", type=str, default=None,
                        help="Check a single notebook file")
    parser.add_argument("--exclude-broken", action="store_true",
                        help="Skip BROKEN notebooks")
    parser.add_argument("--no-catalog", action="store_true",
                        help="Scan filesystem instead of catalog")
    parser.add_argument("--fix", action="store_true",
                        help="Show fix suggestions for violations")
    parser.add_argument("--json", action="store_true",
                        help="JSON output for scripts")
    args = parser.parse_args()

    targets = get_target_notebooks(args)
    if not targets:
        print("No notebooks to check.")
        return 0

    results = [check_notebook(p) for p in targets]
    violations = [r for r in results if r["violations"]]

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
        return 1 if violations else 0

    # Human-readable report
    total = len(results)
    compliant = total - len(violations)
    total_violations = sum(len(r["violations"]) for r in violations)

    print(f"C.2 Compliance Check: {compliant}/{total} notebooks compliant")
    if not violations:
        print("All clear!")
        return 0

    print(f"\nViolations: {total_violations} cells in {len(violations)} notebooks\n")

    for r in violations:
        rel = Path(r["path"]).relative_to(REPO_ROOT) if REPO_ROOT in Path(r["path"]).parents else r["path"]
        print(f"  {rel} ({len(r['violations'])} violations):")
        for v in r["violations"]:
            if "error" in v:
                print(f"    ERROR: {v['error']}")
            else:
                preview = v.get("source_preview", "")[:60]
                print(f"    cell #{v['code_cell']}: {v['reason']}")
                if args.fix:
                    print(f"      -> Re-execute cell or full notebook")

    print(f"\nSummary: {compliant}/{total} compliant, {len(violations)} with issues")
    return 1


if __name__ == "__main__":
    sys.exit(main())
