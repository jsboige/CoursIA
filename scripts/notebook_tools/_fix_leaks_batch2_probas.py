"""Batch fix Probas/Infer solution leaks — Issue #1205 Batch 2.

Strategy: Same as Batch 1 (Search series).
For each HIGH leak detected by detect_solution_leaks.py:
- The markdown cell contains "Exercice N" header(s) but the following code cell
  contains a complete worked solution.
- Fix: relabel ALL occurrences of "Exercice/Exercise" -> "Exemple guide" in the
  markdown cell, including section headers like "## 8. Exercice" and individual
  exercise headers.
"""

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NB_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

AFFECTED = {
    "Probas/Infer/Infer-1-Setup.ipynb": [28],
    "Probas/Infer/Infer-10-Crowdsourcing.ipynb": [39, 44],
    "Probas/Infer/Infer-11-Sequences.ipynb": [47, 56],
    "Probas/Infer/Infer-12-Recommenders.ipynb": [66, 73],
    "Probas/Infer/Infer-13-Debugging.ipynb": [34, 41],
    "Probas/Infer/Infer-14-Decision-Utility-Foundations.ipynb": [33, 36],
    "Probas/Infer/Infer-15-Decision-Utility-Money.ipynb": [36],
    "Probas/Infer/Infer-16-Decision-Multi-Attribute.ipynb": [35, 43],
    "Probas/Infer/Infer-17-Decision-Networks.ipynb": [42],
    "Probas/Infer/Infer-18-Decision-Value-Information.ipynb": [38],
    "Probas/Infer/Infer-19-Decision-Expert-Systems.ipynb": [36],
    "Probas/Infer/Infer-3-Factor-Graphs.ipynb": [38],
    "Probas/Infer/Infer-4-Bayesian-Networks.ipynb": [52],
    "Probas/Infer/Infer-5-Skills-IRT.ipynb": [57, 64, 66],
    "Probas/Infer/Infer-6-TrueSkill.ipynb": [47, 51],
    "Probas/Infer/Infer-7-Classification.ipynb": [43],
    "Probas/Infer/Infer-8-Model-Selection.ipynb": [41, 50],
    "Probas/Infer/Infer-9-Topic-Models.ipynb": [42, 47],
}

EXERCICE_LINE_RE = re.compile(
    r'^(#+[ \t]*(?:\d+[.:][ \t]*)?)(Exercice[s]?|Exercise[s]?)([ \t]*\d*[ \t]*[:.]?[ \t]*)([^\n]*)',
    re.MULTILINE | re.IGNORECASE,
)

EXERCICE_SECTION_RE = re.compile(
    r'^(#+[ \t]*(?:\d+[.:][ \t]*)?)(Exercice[s]?|Exercise[s]?)([ \t]*)',
    re.MULTILINE | re.IGNORECASE,
)

EXERCICE_CODE_COMMENT_RE = re.compile(
    r'^(//[ \t]*)(Exercice[s]?|Exercise[s]?)([ \t]*[:.]?[ \t]*)([^\n]*)',
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
    """Relabel EXERCICE comments in code cells (e.g., '// EXERCICE : Completez...')."""
    fixed = 0
    for cell in nb['cells']:
        if cell.get('cell_type') != 'code':
            continue
        source_text = ''.join(cell.get('source', []))
        new_source, count = EXERCICE_CODE_COMMENT_RE.subn(r'\1Exemple guide\3\4', source_text)
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
