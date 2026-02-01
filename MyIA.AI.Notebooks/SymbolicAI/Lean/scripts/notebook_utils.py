#!/usr/bin/env python3
"""
Notebook manipulation utilities for Lean scripts.

Provides shared functions for reading, writing, and manipulating
Jupyter notebook cells. Used by verification and maintenance scripts.

Usage:
    from notebook_utils import read_notebook, write_notebook, get_cell_source
"""

import json
from pathlib import Path
from typing import Dict, Any, List, Optional


def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON with proper encoding.

    Args:
        path: Path to the notebook file

    Returns:
        Notebook as a dictionary
    """
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)


def write_notebook(path: str, nb: Dict[str, Any]) -> None:
    """Write notebook JSON with consistent formatting.

    Args:
        path: Path to the notebook file
        nb: Notebook dictionary to write
    """
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')


def get_cell_source(cell: Dict[str, Any]) -> str:
    """Get cell source as a single string.

    Args:
        cell: Notebook cell dictionary

    Returns:
        Cell source as a single string
    """
    source = cell.get('source', [])
    return ''.join(source) if isinstance(source, list) else source


def set_cell_source(cell: Dict[str, Any], source: str) -> None:
    """Set cell source from string, preserving line structure.

    Args:
        cell: Notebook cell dictionary to modify
        source: New source content as a string
    """
    lines = source.split('\n')
    # Preserve newlines except for the last line
    cell['source'] = [line + '\n' for line in lines[:-1]]
    if lines[-1]:
        cell['source'].append(lines[-1])


def create_markdown_cell(source: str) -> Dict[str, Any]:
    """Create a new markdown cell with given content.

    Args:
        source: Markdown content

    Returns:
        New markdown cell dictionary
    """
    cell = {
        "cell_type": "markdown",
        "metadata": {},
        "source": []
    }
    set_cell_source(cell, source)
    return cell


def create_code_cell(source: str) -> Dict[str, Any]:
    """Create a new code cell with given content.

    Args:
        source: Code content

    Returns:
        New code cell dictionary
    """
    cell = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": []
    }
    set_cell_source(cell, source)
    return cell


def find_cell_by_content(cells: List[Dict], pattern: str) -> Optional[int]:
    """Find cell index containing pattern.

    Args:
        cells: List of notebook cells
        pattern: Text pattern to search for

    Returns:
        Cell index if found, None otherwise
    """
    for i, cell in enumerate(cells):
        if pattern in get_cell_source(cell):
            return i
    return None


def get_cell_type(cell: Dict[str, Any]) -> str:
    """Get cell type (markdown or code).

    Args:
        cell: Notebook cell dictionary

    Returns:
        Cell type string
    """
    return cell.get('cell_type', 'unknown')


def count_cells_by_type(nb: Dict[str, Any]) -> Dict[str, int]:
    """Count cells by type in a notebook.

    Args:
        nb: Notebook dictionary

    Returns:
        Dictionary with cell type counts
    """
    counts = {'markdown': 0, 'code': 0, 'raw': 0}
    for cell in nb.get('cells', []):
        cell_type = get_cell_type(cell)
        if cell_type in counts:
            counts[cell_type] += 1
    return counts


def insert_cell_after(nb: Dict[str, Any], index: int, cell: Dict[str, Any]) -> None:
    """Insert a cell after a given index.

    Args:
        nb: Notebook dictionary
        index: Index after which to insert
        cell: Cell to insert
    """
    nb['cells'].insert(index + 1, cell)


def remove_cell(nb: Dict[str, Any], index: int) -> Dict[str, Any]:
    """Remove a cell at a given index.

    Args:
        nb: Notebook dictionary
        index: Index of cell to remove

    Returns:
        Removed cell
    """
    return nb['cells'].pop(index)


def get_kernel_name(nb: Dict[str, Any]) -> Optional[str]:
    """Get kernel name from notebook metadata.

    Args:
        nb: Notebook dictionary

    Returns:
        Kernel name if found, None otherwise
    """
    metadata = nb.get('metadata', {})
    kernelspec = metadata.get('kernelspec', {})
    return kernelspec.get('name')


if __name__ == '__main__':
    # Simple test
    print("Notebook utilities module loaded successfully")
    print("Available functions:")
    print("  - read_notebook(path)")
    print("  - write_notebook(path, nb)")
    print("  - get_cell_source(cell)")
    print("  - set_cell_source(cell, source)")
    print("  - create_markdown_cell(source)")
    print("  - create_code_cell(source)")
    print("  - find_cell_by_content(cells, pattern)")
    print("  - count_cells_by_type(nb)")
    print("  - insert_cell_after(nb, index, cell)")
    print("  - remove_cell(nb, index)")
    print("  - get_kernel_name(nb)")
