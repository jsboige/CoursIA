"""Batch fix Sudoku series solution leaks — Issue #1205 Batch 3.

Strategy: Same as Batch 1 (Search) + Batch 2 (Probas/Infer).
For each HIGH leak detected by detect_solution_leaks.py:
- The markdown cell contains "Exercice N" header(s) but the following code cell
  contains a complete worked solution.
- Fix: relabel ALL occurrences of "Exercice/Exercise" -> "Exemple guide" in the
  markdown cell, including section headers like "## 8. Exercice" and individual
  exercise headers.
- Additional pass: relabel // EXERCICE comments in C# code cells and
  # EXERCICE comments in Python code cells.
"""

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NB_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

AFFECTED = {
    "Sudoku/Sudoku-1-Backtracking-Csharp.ipynb": [11],
    "Sudoku/Sudoku-10-ORTools-Csharp.ipynb": [24],
    "Sudoku/Sudoku-10-ORTools-Python.ipynb": [16],
    "Sudoku/Sudoku-11-Choco-Csharp.ipynb": [20],
    "Sudoku/Sudoku-12-Z3-Csharp.ipynb": [19, 21, 23, 25],
    "Sudoku/Sudoku-14-BDD-Csharp.ipynb": [32],
    "Sudoku/Sudoku-15-Infer-Csharp.ipynb": [35],
    "Sudoku/Sudoku-17-LLM-Python.ipynb": [26, 30],
    "Sudoku/Sudoku-18-Comparison-Python.ipynb": [46],
    "Sudoku/Sudoku-2-DancingLinks-Csharp.ipynb": [18],
    "Sudoku/Sudoku-2-DancingLinks-Python.ipynb": [25],
    "Sudoku/Sudoku-3-Genetic-Csharp.ipynb": [16],
    "Sudoku/Sudoku-4-SimulatedAnnealing-Csharp.ipynb": [34],
    "Sudoku/Sudoku-4-SimulatedAnnealing-Python.ipynb": [28, 30, 32],
    "Sudoku/Sudoku-7-Norvig-Csharp.ipynb": [28],
    "Sudoku/Sudoku-8-HumanStrategies-Python.ipynb": [31],
    "Sudoku/Sudoku-9-GraphColoring-Csharp.ipynb": [28],
    "Sudoku/Sudoku-9-GraphColoring-Python.ipynb": [19],
}

EXERCICE_LINE_RE = re.compile(
    r'^(#+[ \t]*(?:\d+[.:][ \t]*)?)(Exercice[s]?|Exercise[s]?)([ \t]*\d*[ \t]*[:.]?[ \t]*)([^\n]*)',
    re.MULTILINE | re.IGNORECASE,
)

EXERCICE_SECTION_RE = re.compile(
    r'^(#+[ \t]*(?:\d+[.:][ \t]*)?)(Exercice[s]?|Exercise[s]?)([ \t]*)',
    re.MULTILINE | re.IGNORECASE,
)

EXERCICE_CSHARP_COMMENT_RE = re.compile(
    r'^(//[ \t]*)(Exercice[s]?|Exercise[s]?)([ \t]*[:.]?[ \t]*)([^\n]*)',
    re.MULTILINE | re.IGNORECASE,
)

EXERCICE_PYTHON_COMMENT_RE = re.compile(
    r'^(#[ \t]*)(Exercice[s]?|Exercise[s]?)([ \t]*[:.]?[ \t]*)([^\n]*)',
    re.MULTILINE | re.IGNORECASE,
)


def find_markdown_header_cell(cells: list, code_cell_idx: int) -> int | None:
    """Find the markdown cell with Exercice header closest before a code cell."""
    for j in range(code_cell_idx - 1, max(code_cell_idx - 5, -1), -1):
        cell = cells[j]
        if cell.get('cell_type') != 'markdown':
            continue
        source = ''.join(cell.get('source', []))
        if EXERCICE_LINE_RE.search(source):
            return j
    return None


def fix_section_headers(nb: dict) -> int:
    """Fix remaining section-level Exercice headers."""
    fixed = 0
    for cell in nb['cells']:
        if cell.get('cell_type') != 'markdown':
            continue
        source_text = ''.join(cell.get('source', []))
        if not EXERCICE_SECTION_RE.search(source_text):
            continue
        new_source, count = EXERCICE_LINE_RE.subn(r'\1Exemple guide\3\4', source_text)
        if count == 0:
            continue
        new_lines = new_source.split('\n')
        cell['source'] = [line + '\n' for line in new_lines[:-1]]
        if new_lines[-1]:
            cell['source'].append(new_lines[-1])
        fixed += 1
    return fixed


def fix_code_cell_comments(nb: dict) -> int:
    """Relabel EXERCICE comments in code cells (C# // and Python #)."""
    fixed = 0
    for cell in nb['cells']:
        if cell.get('cell_type') != 'code':
            continue
        source_text = ''.join(cell.get('source', []))

        # Try C# style first
        new_source, count = EXERCICE_CSHARP_COMMENT_RE.subn(
            r'\1Exemple guide\3\4', source_text,
        )
        # Then Python style
        new_source, count2 = EXERCICE_PYTHON_COMMENT_RE.subn(
            r'\1Exemple guide\3\4', new_source,
        )
        count += count2
        if count == 0:
            continue
        new_lines = new_source.split('\n')
        cell['source'] = [line + '\n' for line in new_lines[:-1]]
        if new_lines[-1]:
            cell['source'].append(new_lines[-1])
        fixed += count
    return fixed


def fix_notebook(rel_path: str, code_cell_indices: list[int]) -> tuple[int, int]:
    """Fix one notebook. Returns (cells_fixed, cells_unchanged)."""
    nb_path = NB_ROOT / rel_path
    with open(nb_path, 'r', encoding='utf-8-sig') as f:
        nb = json.load(f)

    fixed = 0
    unchanged = 0
    cells_to_fix = set()

    for code_idx in code_cell_indices:
        md_idx = find_markdown_header_cell(nb['cells'], code_idx)
        if md_idx is None:
            print(f"  WARNING: no Exercice markdown header found before code cell {code_idx}")
            unchanged += 1
            continue
        cells_to_fix.add(md_idx)

    for cell_idx in sorted(cells_to_fix):
        cell = nb['cells'][cell_idx]
        source_text = ''.join(cell.get('source', []))

        new_source, count = EXERCICE_LINE_RE.subn(r'\1Exemple guide\3\4', source_text)

        if count == 0:
            print(f"  WARNING: cell {cell_idx} no Exercice header found")
            unchanged += 1
            continue

        new_lines = new_source.split('\n')
        cell['source'] = [line + '\n' for line in new_lines[:-1]]
        if new_lines[-1]:
            cell['source'].append(new_lines[-1])

        fixed += 1
        print(f"  Fixed markdown cell {cell_idx}: {count} occurrence(s) replaced")

    if fixed > 0:
        section_fixed = fix_section_headers(nb)
        if section_fixed > 0:
            print(f"  + {section_fixed} section header(s) fixed")
            fixed += section_fixed

        code_fixed = fix_code_cell_comments(nb)
        if code_fixed > 0:
            print(f"  + {code_fixed} code cell comment(s) fixed")
            fixed += code_fixed

        with open(nb_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)
            f.write('\n')

    return fixed, unchanged


def main():
    total_fixed = 0
    total_unchanged = 0

    for rel_path, cells in sorted(AFFECTED.items()):
        print(f"\n{rel_path} ({len(cells)} cells)...")
        f, u = fix_notebook(rel_path, cells)
        total_fixed += f
        total_unchanged += u

    print(f"\n{'='*60}")
    print(f"Total: {total_fixed} cells fixed, {total_unchanged} unchanged, "
          f"{len(AFFECTED)} notebooks processed")

    if total_unchanged > 0:
        print(f"WARNING: {total_unchanged} cells could not be fixed automatically")
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
