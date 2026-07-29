#!/usr/bin/env python3
"""Repo-wide C.1 + C.3 audit for pedagogical notebooks.

Scans all .ipynb files under MyIA.AI.Notebooks/ and reports:
  C.1 violations: raise NotImplementedError, assert False, 1/0
  C.3 violations: output-only changes (outputs changed without source change)

C.3 comes in two granularities. The default (working tree, whole notebook)
flags a file whose diff touches no source at all. `--base/--head` compares two
refs cell by cell and flags the case that actually reaches a merge gate: a PR
edits one cell, re-runs the whole notebook, and commits fresh outputs for the
cells it never touched.

Usage:
    python audit_c1_c3.py                       # Full scan
    python audit_c1_c3.py --family GenAI        # Single family
    python audit_c1_c3.py --check c1            # C.1 only
    python audit_c1_c3.py --json                # JSON output
    python audit_c1_c3.py --summary             # Summary per family only
    python audit_c1_c3.py --base main --head HEAD   # Per-cell C.3 on a branch

Exit codes:
    0 — No violations
    1 — Violations found
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_DIRS = {
    ".ipynb_checkpoints", ".git", "__pycache__", "obj", "bin",
    "_output", "research", "archive", "partner-course", "examples",
    ".venv", "node_modules",
}

C1_PATTERNS = [
    (re.compile(r"raise\s+NotImplementedError"), "raise NotImplementedError"),
    (re.compile(r"assert\s+False"), "assert False"),
    # Negative lookahead excludes digit (21/0, 1/07), slash (1/0/0 reward-list
    # delimiters) AND dot (decimal fractions 1/0.5, 1/0.25, 0.1/0.5 are NOT
    # ZeroDivision — the auditor over-matched these, cf FP on ICT-7
    # `echelle caracteristique 1/0.5`). Lookbehind keeps excluding digit/slash/hyphen.
    (re.compile(r"(?<![\d/\-])1\s*/\s*0(?![\d/.])"), "1/0"),
]


def _is_in_docstring(line: str, in_doc: bool) -> tuple:
    was = in_doc
    for q in ('"""', "'''"):
        if line.count(q) % 2 == 1:
            in_doc = not in_doc
    return in_doc, was != in_doc or was


def find_notebooks(family: str | None = None) -> list[Path]:
    """Discover all pedagogical notebooks."""
    notebooks = []
    root = NOTEBOOKS_DIR / family if family else NOTEBOOKS_DIR
    if not root.exists():
        return []
    for p in root.rglob("*.ipynb"):
        # #8858-class guard: ``root.rglob`` yields ABSOLUTE paths, so
        # filtering on ``p.parts`` (absolute components) would match the
        # repo's own parent if it sits under an EXCLUDE_DIRS-name dir (e.g.
        # a checkout cloned at ``archive/repo/``). That matches EVERY path
        # and silences the whole scan — worse than a false positive for a
        # C.1 compliance gate. Filter on the path RELATIVE to ``root``
        # (the in-repo SKIP_DIRS semantics), with a fallback to ``p.parts``
        # when ``p`` is not under ``root``.
        try:
            rel_parts = p.relative_to(root).parts
        except ValueError:
            rel_parts = p.parts
        if any(part in EXCLUDE_DIRS for part in rel_parts):
            continue
        notebooks.append(p)
    return sorted(notebooks)


def check_c1(nb_path: Path) -> list[dict]:
    """Check C.1: no intentional errors."""
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return []

    violations = []
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        source = "".join(cell.get("source", []))
        in_doc = False
        for line in source.split("\n"):
            # Skip full-line comments (Python '#' or C-family '//', e.g. C#).
            stripped = line.lstrip()
            if stripped.startswith("#") or stripped.startswith("//"):
                continue
            # Strip inline comments before checking patterns (both '#' and '//').
            code_part = re.split(r"#|//", line, maxsplit=1)[0].rstrip()
            in_doc, inside = _is_in_docstring(line, in_doc)
            if inside:
                continue
            for pattern, desc in C1_PATTERNS:
                if pattern.search(code_part):
                    violations.append({
                        "cell": i,
                        "pattern": desc,
                        "line": line.strip()[:80],
                    })
    return violations


def check_c3(nb_path: Path) -> list[dict]:
    """Check C.3: detect output-only changes (outputs changed, source unchanged).

    Compares HEAD vs last commit that changed the notebook's source cells.
    If only outputs differ (no source changes), flags as C.3 violation.
    """
    rel = nb_path.relative_to(REPO_ROOT)
    try:
        diff = subprocess.run(
            ["git", "diff", "HEAD", "--", str(rel)],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
            timeout=10,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return []

    if not diff.stdout:
        return []

    lines = diff.stdout.split("\n")
    source_changes = 0
    output_changes = 0
    in_source = False
    in_output = False

    for line in lines:
        if line.startswith("@@"):
            in_source = False
            in_output = False
            continue
        if '"source"' in line:
            in_source = True
            in_output = False
        elif '"outputs"' in line or '"execution_count"' in line:
            in_output = True
            in_source = False

        if not line.startswith("+") and not line.startswith("-"):
            continue
        if line.startswith("+++ ") or line.startswith("--- "):
            continue

        if in_source:
            source_changes += 1
        elif in_output:
            output_changes += 1

    if output_changes > 0 and source_changes == 0:
        return [{"reason": "output-only changes in working tree (no source change)"}]
    return []


def _cells_at_ref(rel: str, ref: str) -> list[tuple[int, dict]] | None:
    """Load a notebook's code cells at a given git ref, with their notebook index.

    The index is the position in `nb["cells"]`, not the code-cell ordinal, so a
    reported cell can be found by opening the notebook. Markdown cells carry no
    outputs and are skipped.

    Returns None when the notebook does not exist at that ref (added by the
    diff under audit), which is not a C.3 violation.
    """
    try:
        blob = subprocess.run(
            ["git", "show", f"{ref}:{rel}"],
            capture_output=True, cwd=str(REPO_ROOT), timeout=20,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return None
    if blob.returncode != 0 or not blob.stdout:
        return None
    try:
        nb = json.loads(blob.stdout.decode("utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None
    return [(i, c) for i, c in enumerate(nb.get("cells", []))
            if c.get("cell_type") == "code"]


def _outputs_signature(cell: dict) -> tuple[int, int, str]:
    """(output count, error-output count, concatenated text) for one cell.

    Error outputs are counted separately because gaining one is the signature
    of a re-execution that ran against a broken or absent service.
    """
    outs = cell.get("outputs", [])
    n_err = 0
    text_parts = []
    for out in outs:
        kind = out.get("output_type")
        if kind == "error":
            n_err += 1
            text_parts.append(f"{out.get('ename', '')}: {out.get('evalue', '')}")
        elif kind == "stream":
            text_parts.append("".join(out.get("text", [])))
        elif "data" in out:
            text_parts.append(str(out["data"].get("text/plain", "")))
    return len(outs), n_err, "".join(text_parts)


def check_c3_scope(rel: str, base_ref: str, head_ref: str) -> list[dict]:
    """Per-cell C.3: flag cells re-executed although their source is unchanged.

    `check_c3` is whole-notebook: a single modified cell suppresses every flag
    for the rest of the file. That is the case a PR hits in practice — it edits
    one cell, re-runs the notebook, and commits fresh outputs for cells it never
    touched. Under C.3 those outputs should not be staged.

    Cells are matched by source hash (occurrence-aware, so two cells sharing the
    same source stay distinct). A cell whose source is byte-identical across the
    two refs but whose outputs differ is reported.

    Both labels are C.3 violations; they describe what happened, not how bad it
    is. OUTPUTS-LOST means the re-execution dropped outputs or gained error
    outputs. OUTPUTS-REPLACED means the content differs without shrinking — do
    not read it as benign: a run that fails loudly can *grow* the output count
    with logged failures, which is how the worst cells of PR #8615 presented
    (14->31 and 16->37 outputs, every added line an exception trace emitted
    through `logging` rather than as an `error` output).
    """
    base_cells = _cells_at_ref(rel, base_ref)
    head_cells = _cells_at_ref(rel, head_ref)
    if base_cells is None or head_cells is None:
        return []

    base_by_hash: dict[str, list[dict]] = defaultdict(list)
    for _, cell in base_cells:
        digest = hashlib.md5("".join(cell.get("source", [])).encode("utf-8")).hexdigest()
        base_by_hash[digest].append(cell)

    seen: dict[str, int] = defaultdict(int)
    violations = []
    for idx, cell in head_cells:
        source = "".join(cell.get("source", []))
        digest = hashlib.md5(source.encode("utf-8")).hexdigest()
        occurrence = seen[digest]
        seen[digest] += 1
        candidates = base_by_hash.get(digest, [])
        if occurrence >= len(candidates):
            continue  # source is new or modified in this diff — C.3 does not apply
        before = candidates[occurrence]

        n_before, err_before, text_before = _outputs_signature(before)
        n_after, err_after, text_after = _outputs_signature(cell)
        if (n_before, text_before) == (n_after, text_after):
            continue

        lost = n_after < n_before or err_after > err_before
        violations.append({
            "cell_index": idx,
            "severity": "OUTPUTS-LOST" if lost else "OUTPUTS-REPLACED",
            "outputs_before": n_before,
            "outputs_after": n_after,
            "errors_before": err_before,
            "errors_after": err_after,
            "source_head": source.strip().split("\n")[0][:70],
            "reason": "outputs re-executed although source is unchanged vs base",
        })
    return violations


def changed_notebooks(base_ref: str, head_ref: str) -> list[str]:
    """Notebook paths modified between two refs, repo-relative, posix separators."""
    try:
        diff = subprocess.run(
            ["git", "diff", "--name-only", f"{base_ref}...{head_ref}"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=30,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return []
    if diff.returncode != 0:
        return []
    return [p for p in diff.stdout.split("\n") if p.strip().endswith(".ipynb")]


def get_family(nb_path: Path) -> str:
    """Extract family name from path relative to NOTEBOOKS_DIR."""
    try:
        rel = nb_path.relative_to(NOTEBOOKS_DIR)
        return rel.parts[0] if rel.parts else "unknown"
    except ValueError:
        return "unknown"


def run_scope_audit(base_ref: str, head_ref: str, as_json: bool = False) -> int:
    """Per-cell C.3 audit over every notebook changed between two refs."""
    notebooks = changed_notebooks(base_ref, head_ref)
    if not notebooks:
        print(f"No notebook changed between {base_ref} and {head_ref}.")
        return 0

    results = []
    for rel in notebooks:
        violations = check_c3_scope(rel, base_ref, head_ref)
        if violations:
            results.append({"path": rel, "violations": violations})

    if as_json:
        print(json.dumps({"base": base_ref, "head": head_ref,
                          "notebooks_changed": len(notebooks),
                          "violations": results}, indent=2, ensure_ascii=False))
        return 1 if results else 0

    print(f"C.3 scope audit ({base_ref}...{head_ref}): "
          f"{len(notebooks) - len(results)}/{len(notebooks)} notebooks clean")
    for entry in results:
        lost = [v for v in entry["violations"] if v["severity"] == "OUTPUTS-LOST"]
        print(f"\n  {entry['path']}")
        print(f"    {len(entry['violations'])} cell(s) re-executed with unchanged source"
              f" — {len(lost)} lost outputs")
        for v in entry["violations"]:
            print(f"    [{v['severity']:<16}] cell {v['cell_index']:<3} "
                  f"outputs {v['outputs_before']}->{v['outputs_after']} "
                  f"errors {v['errors_before']}->{v['errors_after']}  {v['source_head']}")
    if results:
        print("\nUnder C.3 these outputs should not be staged: the PR does not modify "
              "these cells' source, so they did not have to be re-executed.")
    return 1 if results else 0


def main():
    parser = argparse.ArgumentParser(description="Repo-wide C.1 + C.3 audit")
    parser.add_argument("--family", type=str, default=None, help="Audit single family")
    parser.add_argument("--check", type=str, default="c1,c3",
                        help="Checks: c1, c3 (default: c1,c3)")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--summary", action="store_true", help="Summary per family only")
    parser.add_argument("--base", type=str, default=None,
                        help="Base ref for per-cell C.3 scope audit (e.g. origin/main)")
    parser.add_argument("--head", type=str, default="HEAD",
                        help="Head ref for per-cell C.3 scope audit (default: HEAD)")
    args = parser.parse_args()

    if args.base:
        return run_scope_audit(args.base, args.head, as_json=args.json)

    checks = set(args.check.split(","))
    notebooks = find_notebooks(args.family)

    if not notebooks:
        print("No notebooks found.")
        return 0

    results = []
    families = defaultdict(lambda: {"total": 0, "c1": 0, "c3": 0, "violations": []})

    for nb in notebooks:
        family = get_family(nb)
        families[family]["total"] += 1

        entry = {"path": str(nb.relative_to(REPO_ROOT)), "family": family, "violations": []}

        if "c1" in checks:
            c1_v = check_c1(nb)
            if c1_v:
                entry["violations"].extend([{"check": "C1", **v} for v in c1_v])
                families[family]["c1"] += len(c1_v)

        if "c3" in checks:
            c3_v = check_c3(nb)
            if c3_v:
                entry["violations"].extend([{"check": "C3", **v} for v in c3_v])
                families[family]["c3"] += len(c3_v)

        if entry["violations"]:
            results.append(entry)
            families[family]["violations"].append(nb.name)

    if args.json:
        print(json.dumps({"total_notebooks": len(notebooks), "violations": results},
                         indent=2, ensure_ascii=False))
        return 1 if results else 0

    total_nb = len(notebooks)
    clean = total_nb - len(results)

    print(f"C.1/C.3 Audit: {clean}/{total_nb} notebooks pass")

    if args.summary:
        print(f"\n{'Family':<30} {'Total':>6} {'C.1':>6} {'C.3':>6}")
        print("-" * 52)
        for fam in sorted(families):
            d = families[fam]
            print(f"{fam:<30} {d['total']:>6} {d['c1']:>6} {d['c3']:>6}")
        print("-" * 52)
        total_c1 = sum(d["c1"] for d in families.values())
        total_c3 = sum(d["c3"] for d in families.values())
        print(f"{'TOTAL':<30} {total_nb:>6} {total_c1:>6} {total_c3:>6}")
        return 1 if results else 0

    if not results:
        print("All clear!")
        return 0

    total_v = sum(len(r["violations"]) for r in results)
    print(f"\n{total_v} violations in {len(results)} notebooks:\n")

    for r in results:
        print(f"  {r['path']} ({len(r['violations'])} issues):")
        for v in r["violations"][:5]:
            check = v.get("check", "?")
            if "pattern" in v:
                print(f"    [{check}] cell #{v['cell']}: {v['pattern']}")
            elif "reason" in v:
                print(f"    [{check}] {v['reason']}")

    return 1


if __name__ == "__main__":
    sys.exit(main())
