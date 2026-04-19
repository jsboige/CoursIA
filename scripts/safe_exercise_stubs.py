#!/usr/bin/env python3
"""
safe_exercise_stubs.py - Convert unsafe stubs to safe stubs across the whole repo.

Problem: cells with `raise NotImplementedError` fail papermill execution, which
led someone to fill exercises with full solutions to make CI pass. The correct
pattern is: stubs that DO NOT raise (so CI passes) AND do not expose solutions.

Transformation applied to every code cell:
1. Replace `raise NotImplementedError(...)` at any indent with `pass` at same
   indent. If the raise is at column 0 (top-level) it becomes a print marker.
2. Only for cells that received a `pass` replacement for a top-level raise:
   comment out trailing test/usage code from the point of the raise onwards so
   it does not fail.

This is idempotent. Cells without `raise NotImplementedError` are untouched.

Usage: python scripts/safe_exercise_stubs.py [--dry-run]
"""

import json
import re
import sys
from pathlib import Path

BASE = Path("d:/CoursIA/MyIA.AI.Notebooks")
DRY_RUN = "--dry-run" in sys.argv

SAFE_MARKER = "Exercice a completer - voir les indices ci-dessus"


def cell_source_str(c):
    src = c.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src


def transform_cell_source(src):
    """Return (new_src, changed) where changed is True iff transformation applied."""
    if "raise NotImplementedError" not in src:
        return src, False

    lines = src.split("\n")
    out = []
    changed = False
    # Detect if there's any top-level raise (column 0). If yes, we need to also
    # comment out lines after that raise that look like test/usage code.
    top_level_raise_line = -1
    for i, ln in enumerate(lines):
        if re.match(r"^raise NotImplementedError", ln):
            top_level_raise_line = i
            break

    i = 0
    while i < len(lines):
        ln = lines[i]
        # Match `raise NotImplementedError` optionally followed by args over
        # possibly multiple lines. Start marker:
        m = re.match(r"^(\s*)raise NotImplementedError\b(.*)$", ln)
        if m:
            indent = m.group(1)
            rest = m.group(2).strip()
            # If the raise spans multiple lines (opens `(` without close), skip
            # ahead until the closing paren to swallow the full statement.
            if rest.startswith("(") and rest.count("(") > rest.count(")"):
                # multi-line; skip continuation lines
                j = i + 1
                open_parens = rest.count("(") - rest.count(")")
                while j < len(lines) and open_parens > 0:
                    open_parens += lines[j].count("(") - lines[j].count(")")
                    j += 1
                # Replace all these lines with a single pass/marker
                if indent == "":
                    out.append(f'print("{SAFE_MARKER}")')
                else:
                    out.append(f"{indent}pass")
                i = j
                changed = True
                continue
            # single-line
            if indent == "":
                out.append(f'print("{SAFE_MARKER}")')
            else:
                out.append(f"{indent}pass")
            changed = True
            i += 1
            continue
        out.append(ln)
        i += 1

    # If there was a top-level raise, everything after it on the same "flat" level
    # may reference the missing logic. Safe approach: replace the rest of the
    # cell (from top_level_raise_line+1) with a commented block.
    if top_level_raise_line >= 0:
        # Comment trailing lines that are not blank/already-commented
        tail_start = top_level_raise_line + 1
        # Only comment if there is real code after the raise
        has_tail_code = any(
            ln.strip() and not ln.strip().startswith("#")
            for ln in lines[tail_start:]
        )
        if has_tail_code:
            new_out = out[:tail_start]
            new_out.append("")
            new_out.append("# --- Suite (decommentez apres avoir complete l'exercice) ---")
            for ln in lines[tail_start:]:
                stripped = ln.strip()
                if not stripped:
                    new_out.append(ln)
                elif stripped.startswith("#"):
                    new_out.append(ln)
                else:
                    new_out.append(f"# {ln}")
            out = new_out
            changed = True

    return "\n".join(out), changed


def process_notebook(nb_path):
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except Exception as e:
        print(f"  [ERROR] {nb_path}: {e}")
        return 0

    changed_cells = 0
    for c in nb.get("cells", []):
        if c.get("cell_type") != "code":
            continue
        src = cell_source_str(c)
        new_src, changed = transform_cell_source(src)
        if changed:
            c["source"] = new_src
            c["outputs"] = []
            c["execution_count"] = None
            changed_cells += 1

    if changed_cells and not DRY_RUN:
        with open(nb_path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write("\n")

    return changed_cells


def main():
    total_cells = 0
    total_files = 0
    for nb_path in sorted(BASE.rglob("*.ipynb")):
        if ".ipynb_checkpoints" in str(nb_path):
            continue
        # Skip "_output" notebooks (papermill outputs, regenerable)
        # Actually process them too since they're committed
        changed = process_notebook(nb_path)
        if changed:
            rel = nb_path.relative_to(BASE)
            print(f"  [{'DRY' if DRY_RUN else 'OK'}] {rel}: {changed} cells transformed")
            total_files += 1
            total_cells += changed

    print(f"\nTotal: {total_cells} cells transformed across {total_files} notebooks")


if __name__ == "__main__":
    main()
