"""Batch fix Search series solution leaks — Issue #1205 Batch 1.

Strategy: For each HIGH leak detected by detect_solution_leaks.py:
- The markdown cell contains "Exercice N" header(s) but the following code cell
  contains a complete worked solution (often labeled "# Exemple resolu").
- Fix: relabel ALL occurrences of "Exercice/Exercise" -> "Exemple guide" in the
  markdown cell, including section headers like "## 7. Exercices" and individual
  exercise headers like "### Exercice 1 : ...".
- This preserves the pedagogical content while accurately labeling it as
  an instructor-provided example rather than a student exercise.
"""

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NB_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

# From detect_solution_leaks.py scan output (CODE cell indices)
AFFECTED = {
    "Search/Applications/CSP/App-1-NQueens.ipynb": [41, 45, 49],
    "Search/Applications/CSP/App-11-Picross.ipynb": [38, 42],
    "Search/Applications/CSP/App-15-SportsScheduling.ipynb": [33, 35, 37],
    "Search/Applications/CSP/App-16-Crossword-CSP.ipynb": [18, 20],
    "Search/Applications/CSP/App-2-GraphColoring.ipynb": [43, 47, 51],
    "Search/Applications/CSP/App-3-NurseScheduling.ipynb": [46, 50, 54],
    "Search/Applications/CSP/App-6-Minesweeper.ipynb": [46, 50],
    "Search/Applications/CSP/App-8-MiniZinc.ipynb": [41, 43, 45],
    "Search/Applications/Hybrid/App-13-TSP-Metaheuristics.ipynb": [26, 30, 36, 44],
    "Search/Applications/Hybrid/App-9-EdgeDetection.ipynb": [34],
    "Search/GeneticSharp-EdgeDetection.ipynb": [24, 26],
    "Search/Part1-Foundations/Search-10-SymbolicAutomata.ipynb": [75, 78, 81],
    "Search/Part1-Foundations/Search-11-Metaheuristics.ipynb": [36, 40],
    "Search/Part1-Foundations/Search-2-Uninformed.ipynb": [52, 55],
    "Search/Part1-Foundations/Search-3-Informed.ipynb": [52, 54, 58],
    "Search/Part1-Foundations/Search-7-MCTS-And-Beyond.ipynb": [25],
    "Search/Part1-Foundations/Search-8-DancingLinks.ipynb": [46],
    "Search/Part1-Foundations/Search-9-LinearProgramming.ipynb": [38, 40, 44],
    "Search/Part2-CSP/CSP-1-Fundamentals.ipynb": [71],
    "Search/Part2-CSP/CSP-2-Consistency.ipynb": [58, 60],
    "Search/Part2-CSP/CSP-4-Scheduling.ipynb": [26],
    "Search/Part2-CSP/CSP-5-Optimization.ipynb": [36, 38, 40, 42, 44, 46, 48, 50],
    "Search/Part2-CSP/CSP-6-Hybridization.ipynb": [24, 26, 36],
    "Search/Part2-CSP/CSP-7-Soft.ipynb": [27],
    "Search/Part2-CSP/CSP-8-Temporal.ipynb": [25, 29, 37],
    "Search/Part2-CSP/CSP-9-Distributed.ipynb": [28, 32, 40],
}

# Matches any line containing Exercice/Exercise (case-insensitive)
# Uses [^\n] instead of . and [ \t] instead of \s to prevent cross-line matching
EXERCICE_LINE_RE = re.compile(
    r'^(#+[ \t]*(?:\d+[.:][ \t]*)?)(Exercice[s]?|Exercise[s]?)([ \t]*\d*[ \t]*[:.]?[ \t]*)([^\n]*)',
    re.MULTILINE | re.IGNORECASE,
)


# Matches section-level headers like "## Exercices" or "## 7. Exercices"
EXERCICE_SECTION_RE = re.compile(
    r'^(#+[ \t]*(?:\d+[.:][ \t]*)?)(Exercice[s]?|Exercise[s]?)([ \t]*)',
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
    """Fix remaining section-level Exercice headers (e.g., '## Exercices').

    After targeted fixes, some section headers like '## 7. Exercices' remain
    because they are never the closest markdown cell before a reported code cell.
    This pass fixes ALL remaining markdown cells with Exercice headers.
    """
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


def fix_notebook(rel_path: str, code_cell_indices: list[int]) -> tuple[int, int]:
    """Fix one notebook. Returns (cells_fixed, cells_unchanged).

    For each code cell reported, find the preceding markdown cell and replace
    ALL occurrences of Exercice/Exercise with Exemple guide in that cell.
    """
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

        # Replace ALL occurrences of Exercice/Exercise with Exemple guide
        new_source, count = EXERCICE_LINE_RE.subn(r'\1Exemple guide\3\4', source_text)

        if count == 0:
            print(f"  WARNING: cell {cell_idx} no Exercice header found")
            unchanged += 1
            continue

        # Update source as list of lines (preserving format)
        new_lines = new_source.split('\n')
        cell['source'] = [line + '\n' for line in new_lines[:-1]]
        if new_lines[-1]:
            cell['source'].append(new_lines[-1])

        fixed += 1
        print(f"  Fixed markdown cell {cell_idx}: {count} occurrence(s) replaced")

    if fixed > 0:
        # Second pass: fix remaining section-level headers
        section_fixed = fix_section_headers(nb)
        if section_fixed > 0:
            print(f"  + {section_fixed} section header(s) fixed")
            fixed += section_fixed

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
