#!/usr/bin/env python3
"""Audit solution leaks in pedagogical notebooks.

Detects 3 patterns per issue #362:
1. Function body leak: function defined under # Exercice N with >3 lines of logic
2. Commented-out solution leak: # comment blocks >3 lines with code/data
3. Pre-resolved cells: # Solution / # Exemple resolu with complete answers
"""

import json
import sys
import re
import glob
import os
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXERCICE_MARKERS = re.compile(
    r'#\s*(Exercice|TODO\s+etudiant|Etape)\s*\d*', re.IGNORECASE
)
EXERCICE_MD_MARKERS = re.compile(
    r'(##?\s*Exercice\s+\d+|###?\s*Exercice\s+\d+)', re.IGNORECASE
)
SOLUTION_MARKERS = re.compile(
    r'#\s*(Solution|Exemple\s+résolu|Réponse\s*:)'
    r'|#\s*(Solution|Exemple\s+resolu|Reponse\s*:)', re.IGNORECASE
)
EXAMPLE_RESOLU_MARKERS = re.compile(
    r'#\s*(Exemple\s+résolu|Exemple\s+resolu|Solution\s*[:-]?\s*$)', re.IGNORECASE
)


def get_cells_after_exercice_md(cells, start_idx):
    """Get code cells that follow a markdown exercice header."""
    code_cells = []
    for i in range(start_idx + 1, min(start_idx + 5, len(cells))):
        cell = cells[i]
        if cell['cell_type'] == 'markdown':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MD_MARKERS.search(src):
                break
            if src.strip().startswith('#'):
                break
        if cell['cell_type'] == 'code':
            code_cells.append((i, cell))
    return code_cells


def detect_function_body_leak(source_lines):
    """Pattern 1: Function with >3 lines of real logic under exercice."""
    leaks = []
    in_function = False
    func_name = ""
    logic_lines = 0
    func_start = 0
    current_indent = 0

    for lineno, line in enumerate(source_lines):
        stripped = line.strip()

        # Detect function definition
        func_match = re.match(r'def\s+(\w+)\s*\(', stripped)
        if func_match:
            if in_function and logic_lines > 3:
                leaks.append({
                    'type': 'function_body_leak',
                    'func_name': func_name,
                    'start_line': func_start + 1,
                    'logic_lines': logic_lines,
                    'severity': 'HIGH' if logic_lines > 5 else 'MEDIUM',
                })
            in_function = True
            func_name = func_match.group(1)
            logic_lines = 0
            func_start = lineno
            current_indent = len(line) - len(line.lstrip())
            continue

        if in_function:
            indent = len(line) - len(line.lstrip()) if stripped else current_indent + 4
            if stripped and indent > current_indent:
                # Skip stub patterns
                if stripped in ('pass', 'return None', 'return None  # TODO etudiant',
                                'print("Exercice a completer")', 'return 0', 'return ""',
                                'return []', 'return {}', 'return False', 'return True'):
                    logic_lines = 0
                    in_function = False
                    continue
                if stripped.startswith('#') or stripped.startswith('"""') or stripped.startswith("'''"):
                    continue
                if stripped.startswith('return ') and 'TODO' in stripped:
                    continue
                if stripped.startswith('return ') and stripped.endswith('None'):
                    continue
                logic_lines += 1

            # Function ended (dedent or blank line after logic)
            if stripped and indent <= current_indent and lineno > func_start + 1:
                if logic_lines > 3:
                    leaks.append({
                        'type': 'function_body_leak',
                        'func_name': func_name,
                        'start_line': func_start + 1,
                        'logic_lines': logic_lines,
                        'severity': 'HIGH' if logic_lines > 5 else 'MEDIUM',
                    })
                in_function = False
                logic_lines = 0

    # Check last function
    if in_function and logic_lines > 3:
        leaks.append({
            'type': 'function_body_leak',
            'func_name': func_name,
            'start_line': func_start + 1,
            'logic_lines': logic_lines,
            'severity': 'HIGH' if logic_lines > 5 else 'MEDIUM',
        })

    return leaks


def detect_commented_solution_leak(source_lines):
    """Pattern 2: Comment blocks >3 lines with code/data that constitute solution."""
    leaks = []
    comment_block = []
    block_start = 0

    for lineno, line in enumerate(source_lines):
        stripped = line.strip()
        if stripped.startswith('#') and not stripped.startswith('#!') and not stripped.startswith('# @'):
            # Check if comment looks like code
            content = stripped[1:].strip()
            if re.match(r'(prof|profil|expected|result|solution|answer|correct)\w*\s*[=:]', content, re.IGNORECASE):
                comment_block.append((lineno + 1, stripped))
            elif re.match(r'\w+\s*[=\[\(].*\)', content):
                comment_block.append((lineno + 1, stripped))
            elif re.match(r'(if|for|while|return|def|class)\s+', content):
                comment_block.append((lineno + 1, stripped))
        else:
            if len(comment_block) > 3:
                leaks.append({
                    'type': 'commented_solution_leak',
                    'start_line': comment_block[0][0],
                    'lines': len(comment_block),
                    'severity': 'MEDIUM',
                })
            comment_block = []

    if len(comment_block) > 3:
        leaks.append({
            'type': 'commented_solution_leak',
            'start_line': comment_block[0][0],
            'lines': len(comment_block),
            'severity': 'MEDIUM',
        })

    return leaks


def detect_preresolved_cells(cells):
    """Pattern 3: # Solution or # Exemple resolu cells with complete answers."""
    leaks = []
    for i, cell in enumerate(cells):
        if cell['cell_type'] != 'code':
            continue
        source = ''.join(cell.get('source', []))
        if SOLUTION_MARKERS.search(source.split('\n')[0] if source else ''):
            code_lines = [l for l in source.split('\n') if l.strip() and not l.strip().startswith('#')]
            if len(code_lines) > 3:
                leaks.append({
                    'type': 'preresolved_cell',
                    'cell_index': i,
                    'code_lines': len(code_lines),
                    'first_line': source.split('\n')[0][:80],
                    'severity': 'LOW',
                })
    return leaks


def audit_notebook(path):
    """Audit a single notebook for solution leaks."""
    try:
        nb = json.load(open(path, encoding='utf-8'))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return []

    cells = nb.get('cells', [])
    all_leaks = []

    # Track which cells are "exercise context"
    exercice_context = set()

    for i, cell in enumerate(cells):
        if cell['cell_type'] == 'markdown':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MD_MARKERS.search(src):
                exercice_context.add(i)
        elif cell['cell_type'] == 'code':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MARKERS.search(src.split('\n')[0] if src else ''):
                exercice_context.add(i)

    # Check code cells under exercice context for pattern 1 & 2
    for i in exercice_context:
        cell = cells[i]
        if cell['cell_type'] != 'code':
            continue
        source = ''.join(cell.get('source', []))
        lines = source.split('\n')

        # Skip cells that are legitimate demos (# Exemple resolu, # Solution)
        if EXAMPLE_RESOLU_MARKERS.search(lines[0] if lines else ''):
            continue

        # Pattern 1: function body leak
        body_leaks = detect_function_body_leak(lines)
        for leak in body_leaks:
            leak['cell_index'] = i
            leak['context'] = 'exercice_marker'
            all_leaks.append(leak)

        # Pattern 2: commented solution
        comment_leaks = detect_commented_solution_leak(lines)
        for leak in comment_leaks:
            leak['cell_index'] = i
            all_leaks.append(leak)

    # Also check code cells immediately after exercice markdown headers
    for i, cell in enumerate(cells):
        if cell['cell_type'] == 'markdown':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MD_MARKERS.search(src):
                following_code = get_cells_after_exercice_md(cells, i)
                for j, code_cell in following_code:
                    source = ''.join(code_cell.get('source', []))
                    lines = source.split('\n')
                    # Skip cells that are legitimate demos
                    if EXAMPLE_RESOLU_MARKERS.search(lines[0] if lines else ''):
                        continue
                    body_leaks = detect_function_body_leak(lines)
                    for leak in body_leaks:
                        leak['cell_index'] = j
                        leak['context'] = f'after_md_exercice_{i}'
                        all_leaks.append(leak)

    # Pattern 3: pre-resolved cells (all code cells)
    preresolved = detect_preresolved_cells(cells)
    all_leaks.extend(preresolved)

    return all_leaks


def main():
    notebooks = list(NOTEBOOKS_DIR.rglob('*.ipynb'))
    notebooks = [n for n in notebooks if '_output' not in n.name and '_executed' not in n.name
                 and '.ipynb_checkpoints' not in str(n)]

    print(f"Auditing {len(notebooks)} notebooks for solution leaks...")
    print()

    results = {}
    total_leaks = {'function_body_leak': 0, 'commented_solution_leak': 0, 'preresolved_cell': 0}

    for nb_path in sorted(notebooks):
        leaks = audit_notebook(nb_path)
        if leaks:
            rel_path = nb_path.relative_to(REPO_ROOT)
            results[str(rel_path)] = leaks
            for leak in leaks:
                total_leaks[leak['type']] = total_leaks.get(leak['type'], 0) + 1

    # Report
    print(f"## Audit Results: {len(results)} notebooks with leaks")
    print(f"Total: function_body_leak={total_leaks.get('function_body_leak', 0)}, "
          f"commented_solution_leak={total_leaks.get('commented_solution_leak', 0)}, "
          f"preresolved_cell={total_leaks.get('preresolved_cell', 0)}")
    print()

    # Sort by severity (HIGH first)
    for path, leaks in sorted(results.items()):
        high = [l for l in leaks if l.get('severity') == 'HIGH']
        medium = [l for l in leaks if l.get('severity') == 'MEDIUM']
        low = [l for l in leaks if l.get('severity') == 'LOW']

        if high or medium:
            print(f"### {path}")
            for leak in high + medium:
                leak_desc = f"  [{leak['severity']}] {leak['type']}"
                if 'func_name' in leak:
                    leak_desc += f" `{leak['func_name']}` ({leak['logic_lines']} logic lines)"
                elif 'lines' in leak:
                    leak_desc += f" ({leak['lines']} comment lines)"
                elif 'code_lines' in leak:
                    leak_desc += f" ({leak['code_lines']} code lines)"
                if 'cell_index' in leak:
                    leak_desc += f" cell {leak['cell_index']}"
                if 'start_line' in leak:
                    leak_desc += f" L{leak['start_line']}"
                print(leak_desc)
            print()

    # JSON output for further processing
    output = {
        'total_notebooks': len(notebooks),
        'notebooks_with_leaks': len(results),
        'leak_counts': total_leaks,
        'findings': {k: v for k, v in results.items()},
    }

    output_path = REPO_ROOT / 'audit_solution_leaks_results.json'
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False, default=str)

    print(f"Full results saved to {output_path}")


if __name__ == '__main__':
    main()
