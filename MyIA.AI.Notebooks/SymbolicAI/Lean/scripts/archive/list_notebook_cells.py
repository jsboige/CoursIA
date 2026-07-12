#!/usr/bin/env python3
"""
List cells in a Jupyter notebook with their indexes and IDs
"""

import json
import sys
from pathlib import Path

def list_cells(notebook_path):
    """List all cells with index, ID, and type"""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    print(f"\n{'='*80}")
    print(f"NOTEBOOK: {Path(notebook_path).name}")
    print(f"{'='*80}")
    print(f"Total cells: {len(nb['cells'])}\n")

    for i, cell in enumerate(nb['cells']):
        cell_type = cell['cell_type']
        cell_id = cell.get('id', 'N/A')

        # Get first line of content
        source = cell.get('source', [])
        if isinstance(source, list):
            first_line = source[0] if source else ""
        else:
            first_line = source

        first_line = first_line.strip()[:60]

        print(f"Cell {i:2d} | ID: {cell_id:15s} | Type: {cell_type:8s} | {first_line}")

    print(f"\n{'='*80}\n")

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python list_notebook_cells.py <notebook.ipynb>")
        sys.exit(1)

    list_cells(sys.argv[1])
