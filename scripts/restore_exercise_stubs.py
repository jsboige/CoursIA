#!/usr/bin/env python3
"""
restore_exercise_stubs.py - Convert filled-in exercise cells back to safe stubs.

Root cause: commit 311d7577 filled exercise stubs with solutions to make papermill
execution pass. We want: stubs that DO NOT raise exceptions AND do not expose
solutions. Strategy:

- Take each exercise cell (detected by "Exercice" marker in previous markdown
  cell or in first lines of code) that currently contains a solution.
- Replace every method body (including top-level exercise block) with a safe
  stub: preserve the signature/docstring/hint comments, replace the actual
  implementation with `pass` (for methods) or `print("... a completer")` for
  top-level exercise blocks.
- Comment out any trailing test/usage code (lines that would exercise the stub
  and could fail). The student can uncomment them after implementing.

We drive this from the clean (pre-311d7577) commit 4052a436: we KEEP the
structure/docstring from clean but REMOVE `raise NotImplementedError` in favor
of `pass` / safe placeholders, and we comment trailing test code.
"""

import json
import re
import subprocess
from pathlib import Path

BASE = Path("d:/CoursIA")
CLEAN_COMMIT = "4052a436"

TARGETS = [
    "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-1-StateSpace.ipynb",
    "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-3-Informed.ipynb",
    "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-5-GeneticAlgorithms.ipynb",
    "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-6-AdversarialSearch.ipynb",
    "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-7-MCTS-And-Beyond.ipynb",
    "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-10-SymbolicAutomata.ipynb",
]


def cell_source(c):
    src = c.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src


def load_clean(rel_path):
    result = subprocess.run(
        ["git", "show", f"{CLEAN_COMMIT}:{rel_path}"],
        capture_output=True, text=True, encoding="utf-8",
    )
    if result.returncode != 0:
        return None
    return json.loads(result.stdout)


def transform_stub_source(clean_src):
    """Transform a clean stub cell source:
    - Replace `raise NotImplementedError(...)` at any indent with `pass` at same indent
    - If the last non-comment statement is a top-level `raise NotImplementedError`,
      replace with `print("Exercice a completer - voir indices ci-dessus")`
    - Leave test code untouched when the test does not call the stubs directly.
      To keep it safe, we comment lines after method defs that look like calls
      to the stubs (heuristic: any line starting a top-level call `foo(` or
      `obj = Class(`) gets a `# ` prefix.
    """
    lines = clean_src.split("\n")

    # Pass 1: replace `raise NotImplementedError` with `pass`
    replaced = []
    for ln in lines:
        # Handle `raise NotImplementedError` (with or without message)
        m = re.match(r"^(\s*)raise NotImplementedError(\(.*\))?\s*$", ln)
        if m:
            indent = m.group(1)
            if indent == "":
                # Top-level raise -> print message instead
                replaced.append(f'print("Exercice a completer - voir les indices ci-dessus")')
            else:
                replaced.append(f"{indent}pass")
        else:
            replaced.append(ln)

    return "\n".join(replaced)


def comment_trailing_test_code(src):
    """Comment out trailing test/usage code that would fail with stubs.
    Heuristic: find the LAST `def ` or `class ` line (considering methods inside
    classes too). Everything AFTER the end of that class/def block that is not
    a `print(...)` alone or a comment is considered test code and gets commented.

    Simpler heuristic that works well: find top-level lines (no indent) after
    the last `class X:` or `def foo():` definition block that reference names
    matching class/function names defined above. Comment those.

    To keep this robust and low-risk, we take a simpler approach:
    - Find the last non-empty top-level statement that is NOT `class`/`def`/
      `print`/`#`/string literal/import/assignment to simple constants.
    - If such a line calls a class or function defined above, comment it.

    Given complexity, we use an even simpler rule: comment out every trailing
    line (from the end backward) until we hit a `class` or `def` definition
    or an `import`/simple assignment/comment/print-only-literal line. All
    commented lines get a `# ` prefix; existing content stays readable.
    """
    lines = src.split("\n")
    n = len(lines)

    # Find index of last `class ` or `def ` at column 0
    last_class_def = -1
    for i in range(n - 1, -1, -1):
        ln = lines[i]
        if re.match(r"^(class|def)\s+\w+", ln):
            last_class_def = i
            break

    if last_class_def == -1:
        return src  # no class/def; don't touch

    # Find end of the last class/def block: first line at column 0 after it
    # that is NOT inside the block. We scan from last_class_def+1 forward.
    block_end = n
    for i in range(last_class_def + 1, n):
        ln = lines[i]
        if ln.strip() == "":
            continue
        # Line at column 0 means outside the block
        if not ln.startswith(" ") and not ln.startswith("\t"):
            block_end = i
            break

    if block_end >= n:
        return src  # no trailing code

    # Now comment out lines from block_end to end, but keep blank lines and
    # existing comments as-is; existing prints and simple assignments get
    # commented too. Exception: if a "print" is a lone message string, keep it.
    # Simplest: comment all non-empty non-comment lines with '# '.
    out = lines[:block_end]
    marker_added = False
    for i in range(block_end, n):
        ln = lines[i]
        stripped = ln.strip()
        if not stripped:
            out.append(ln)
            continue
        if stripped.startswith("#"):
            out.append(ln)
            continue
        # Skip simple "# --- section --- " style comments
        # Comment this line
        if not marker_added:
            out.append("")
            out.append("# --- Test (decommentez apres avoir complete l'exercice ci-dessus) ---")
            marker_added = True
        out.append(f"# {ln}")

    # Add a final marker print so papermill has a visible output
    if marker_added:
        out.append("")
        out.append('print("Exercice charge - completez le code puis decommentez les tests.")')

    return "\n".join(out)


def transform_cell(clean_src):
    s = transform_stub_source(clean_src)
    s = comment_trailing_test_code(s)
    return s


def build_stub_index(nb_clean):
    """Return dict {cell_id: transformed_source} for cells that contain stubs."""
    idx = {}
    for c in nb_clean.get("cells", []):
        if c.get("cell_type") != "code":
            continue
        src = cell_source(c)
        if "raise NotImplementedError" not in src:
            continue
        cid = c.get("id")
        if cid:
            idx[cid] = transform_cell(src)
    return idx


def restore_notebook(rel_path):
    nb_clean = load_clean(rel_path)
    if nb_clean is None:
        print(f"  [SKIP] Cannot read {rel_path} at {CLEAN_COMMIT}")
        return 0

    stubs = build_stub_index(nb_clean)
    if not stubs:
        print(f"  [SKIP] No stubs found in clean {rel_path}")
        return 0

    curr_path = BASE / rel_path
    with open(curr_path, encoding="utf-8") as f:
        nb_curr = json.load(f)

    restored = 0
    for c in nb_curr.get("cells", []):
        if c.get("cell_type") != "code":
            continue
        cid = c.get("id")
        if cid not in stubs:
            continue
        curr_src = cell_source(c)
        # Skip if already a safe stub (contains "Exercice a completer" marker)
        if "Exercice charge - completez le code" in curr_src:
            continue
        c["source"] = stubs[cid]
        c["outputs"] = []
        c["execution_count"] = None
        restored += 1

    if restored:
        with open(curr_path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(nb_curr, f, ensure_ascii=False, indent=1)
            f.write("\n")
        print(f"  [OK] {rel_path}: {restored} stubs restored")
    else:
        print(f"  [NOOP] {rel_path}: no cells needed restoration")
    return restored


def main():
    total = 0
    for nb in TARGETS:
        print(f"Processing {nb}")
        total += restore_notebook(nb)
    print(f"\nTotal stubs restored: {total}")


if __name__ == "__main__":
    main()
