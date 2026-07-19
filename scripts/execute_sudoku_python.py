#!/usr/bin/env python
"""
Execute all Python Sudoku notebooks with papermill.
Fixes common issues before execution.

Resolved issues vs. the original version:

- ``SUDOKU_DIR`` used to be hard-coded to ``d:/Dev/CoursIA/MyIA.AI.Notebooks/Sudoku``
  (a path that is specific to one Windows workstation and does not exist on
  other machines — including this repo's CI runners and fellow workers). The
  directory is now derived from ``__file__`` so the script works wherever it
  is checked out.

- ``PYTHON_NOTEBOOKS`` listed six stale names (``Sudoku-10-NeuralNetwork.ipynb``,
  ``Sudoku-Python-Backtracking.ipynb``, …) that no longer exist after the
  series rename. Sudoku notebooks were reshuffled into numbered ``*-Python.ipynb``
  pairs (e.g. ``Sudoku-16-NeuralNetwork-Python.ipynb``). The list is now
  discovered from the actual ``*-Python.ipynb`` files in :data:`SUDOKU_DIR` at
  call time, so renames in the series stay in sync without editing this file.

- The ``.view() -> .reshape()`` patch used to key off ``Sudoku-10-NeuralNetwork.ipynb``;
  the corresponding notebook is now ``Sudoku-16-NeuralNetwork-Python.ipynb``.
"""

import json
import subprocess
import sys
from pathlib import Path

# Repo-local Sudoku directory (portable across machines and CI).
# Previously hard-coded to "d:/Dev/CoursIA/MyIA.AI.Notebooks/Sudoku" which is
# specific to one Windows workstation. Resolve relative to this file so the
# script works on any checkout (CI, fellow workers, fresh clone).
REPO_ROOT = Path(__file__).resolve().parent.parent
SUDOKU_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "Sudoku"


def _discover_python_notebooks() -> list[str]:
    """Return basenames of every ``*-Python.ipynb`` in :data:`SUDOKU_DIR`.

    The Sudoku series currently exposes one notebook per algorithm/backtracking
    variant under ``*Python.ipynb``; the discovery keeps the script in sync if
    another algorithm is added (e.g. ``Sudoku-20-SAT-Python.ipynb``) without
    editing this file. The numeric prefix (``Sudoku-NN-``) sorts naturally
    because the index uses zero-padded numbers.
    """
    if not SUDOKU_DIR.is_dir():
        return []
    return sorted(p.name for p in SUDOKU_DIR.glob("*-Python.ipynb"))

def fix_view_to_reshape(notebook_path: Path):
    """Fix .view() -> .reshape() in train_model function for PyTorch 2.x compatibility."""
    print(f"Checking {notebook_path.name} for .view() issues...")

    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    modified = False

    for cell in nb.get('cells', []):
        if cell.get('cell_type') == 'code':
            source = cell.get('source', [])
            if isinstance(source, str):
                source = [source]

            # Check if cell contains the problematic pattern
            cell_text = ''.join(source)

            # Fix: output.view(-1, 9) -> output.reshape(-1, 9) when after permute
            if 'output.view(-1, 9)' in cell_text and 'permute' in cell_text:
                new_source = []
                for line in source:
                    if isinstance(line, str):
                        new_source.append(line.replace('output.view(-1, 9)', 'output.reshape(-1, 9)'))
                        new_source.append(line.replace('output.view(-1, 9),', 'output.reshape(-1, 9),'))
                    else:
                        new_source.append(line)
                cell['source'] = new_source
                modified = True
                print(f"  Fixed .view() -> .reshape() in train_model")

    if modified:
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, indent=1, ensure_ascii=False)
        print(f"  Saved fixed version")

    return modified

def execute_python_notebook(notebook_path: Path, timeout: int = 600):
    """Execute a Python notebook with papermill."""
    print(f"\nExecuting {notebook_path.name}...")

    result = subprocess.run(
        [sys.executable, '-m', 'papermill',
         str(notebook_path),
         str(notebook_path),
         '--kernel', 'python3'],
        capture_output=True,
        text=True,
        timeout=timeout
    )

    success = result.returncode == 0

    if not success:
        print(f"  ERROR: Execution failed")
        print(result.stdout[-500:] if len(result.stdout) > 500 else result.stdout)
        if result.stderr:
            print("STDERR:", result.stderr[-500:] if len(result.stderr) > 500 else result.stderr)

    return success

def main():
    print("="*70)
    print("PYTHON SUDOKU NOTEBOOKS EXECUTION")
    print("="*70)

    results = []
    failed = []

    for notebook_name in _discover_python_notebooks():
        notebook_path = SUDOKU_DIR / notebook_name

        if not notebook_path.exists():
            results.append({
                'name': notebook_name,
                'kernel': 'python3',
                'success': False,
                'error': 'File not found'
            })
            failed.append(notebook_name)
            continue

        # Fix known issues — the NN notebook was renamed during the series
        # re-numbering, but the .view() pattern only applies there.
        if "NeuralNetwork" in notebook_name:
            fix_view_to_reshape(notebook_path)

        # Execute
        try:
            success = execute_python_notebook(notebook_path)

            # Count cells and outputs
            with open(notebook_path) as f:
                nb = json.load(f)

            total_cells = len(nb.get('cells', []))
            code_cells = sum(1 for c in nb.get('cells', []) if c.get('cell_type') == 'code')
            cells_with_outputs = sum(
                1 for c in nb.get('cells', [])
                if c.get('cell_type') == 'code' and c.get('outputs')
            )

            results.append({
                'name': notebook_name,
                'kernel': 'python3',
                'success': success,
                'total_cells': total_cells,
                'code_cells': code_cells,
                'cells_with_outputs': cells_with_outputs,
                'error': None if success else 'Execution failed'
            })

            if not success:
                failed.append(notebook_name)

        except subprocess.TimeoutExpired:
            results.append({
                'name': notebook_name,
                'kernel': 'python3',
                'success': False,
                'error': f'Timeout after {timeout}s'
            })
            failed.append(notebook_name)

        except Exception as e:
            results.append({
                'name': notebook_name,
                'kernel': 'python3',
                'success': False,
                'error': str(e)
            })
            failed.append(notebook_name)

    # Print summary
    print("\n" + "="*70)
    print("EXECUTION SUMMARY - PYTHON NOTEBOOKS")
    print("="*70)

    print(f"\n{'Notebook':<35} {'Status':<8} {'Code':<5} {'Outputs':<8}")
    print("-" * 70)

    for r in results:
        status = "OK" if r['success'] else "ERROR"
        print(f"{r['name']:<35} {status:<8} {r.get('code_cells', 0):<5} {r.get('cells_with_outputs', 0):<8}")

    print("-" * 70)

    total_ok = sum(1 for r in results if r['success'])
    print(f"\nTotal: {len(results)} notebooks | OK: {total_ok} | FAILED: {len(failed)}")

    if failed:
        print(f"\nFailed notebooks:")
        for name in failed:
            print(f"  - {name}")

    return 0 if len(failed) == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
