#!/usr/bin/env python3
"""
Validate Python syntax in all Tweety notebook cells.
Reports syntax errors with line numbers and cell IDs.
"""

import ast
import json
import sys
from pathlib import Path
from typing import List, Tuple, Dict

# Notebooks to validate
TWEETY_NOTEBOOKS = [
    "Tweety-1-Setup.ipynb",
    "Tweety-2-Basic-Logics.ipynb",
    "Tweety-3-Advanced-Logics.ipynb",
    "Tweety-4-Belief-Revision.ipynb",
    "Tweety-5-Abstract-Argumentation.ipynb",
    "Tweety-6-Structured-Argumentation.ipynb",
    "Tweety-7-Advanced-Argumentation.ipynb",
    "Tweety-7a-Extended-Frameworks.ipynb",
    "Tweety-7b-Ranking-Probabilistic.ipynb",
]


def validate_python_syntax(code: str) -> Tuple[bool, str]:
    """
    Validate Python syntax using ast.parse.

    Returns:
        Tuple of (is_valid, error_message)
    """
    try:
        ast.parse(code)
        return True, ""
    except SyntaxError as e:
        return False, f"Line {e.lineno}: {e.msg}"


def validate_notebook(notebook_path: Path) -> List[Dict]:
    """
    Validate all code cells in a notebook.

    Returns:
        List of error dictionaries with cell info
    """
    errors = []

    if not notebook_path.exists():
        return [{"notebook": notebook_path.name, "error": "File not found"}]

    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
    except json.JSONDecodeError as e:
        return [{"notebook": notebook_path.name, "error": f"Invalid JSON: {e}"}]

    cells = nb.get('cells', [])

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue

        source = cell.get('source', [])
        if isinstance(source, list):
            code = ''.join(source)
        else:
            code = source

        # Skip empty cells
        if not code.strip():
            continue

        # Get cell ID if available
        cell_id = cell.get('id', f'cell_{i}')

        # Validate syntax
        is_valid, error_msg = validate_python_syntax(code)

        if not is_valid:
            errors.append({
                "notebook": notebook_path.name,
                "cell_index": i,
                "cell_id": cell_id,
                "error": error_msg,
                "first_line": code.split('\n')[0][:60] + "..." if len(code.split('\n')[0]) > 60 else code.split('\n')[0]
            })

    return errors


def main():
    """Main entry point."""
    # Find notebook directory
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent

    if not notebook_dir.exists():
        print(f"ERROR: Notebook directory not found: {notebook_dir}")
        return 1

    print(f"Validating notebooks in: {notebook_dir}")
    print("=" * 60)

    all_errors = []
    notebooks_checked = 0

    for nb_name in TWEETY_NOTEBOOKS:
        nb_path = notebook_dir / nb_name

        if not nb_path.exists():
            print(f"  SKIP: {nb_name} (not found)")
            continue

        errors = validate_notebook(nb_path)
        notebooks_checked += 1

        if errors:
            all_errors.extend(errors)
            print(f"  FAIL: {nb_name} - {len(errors)} error(s)")
            for err in errors:
                print(f"        Cell {err['cell_index']} ({err['cell_id']}): {err['error']}")
                print(f"        First line: {err['first_line']}")
        else:
            print(f"  OK:   {nb_name}")

    print("=" * 60)
    print(f"Checked {notebooks_checked} notebooks, {len(all_errors)} syntax errors found.")

    return 0 if not all_errors else 1


if __name__ == "__main__":
    sys.exit(main())
