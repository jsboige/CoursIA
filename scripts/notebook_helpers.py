#!/usr/bin/env python3
"""
Notebook Helpers - Consolidated utilities for Jupyter notebook manipulation.

This module provides functions for:
- Reading/writing notebook JSON files
- Listing and inspecting cells
- Manipulating cell content
- Cell iteration patterns with objectives

Usage:
    from notebook_helpers import NotebookHelper, CellIterator

Example:
    helper = NotebookHelper("path/to/notebook.ipynb")
    helper.list_cells()
    helper.get_cell_source(5)
    helper.set_cell_source(5, "new code")
    helper.save()

For iterative cell correction with MCP tools:
    See CellIterator class and notebook-cell-iterator agent.
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Callable, Tuple
from dataclasses import dataclass, field
from datetime import datetime


@dataclass
class CellInfo:
    """Information about a notebook cell."""
    index: int
    cell_id: str
    cell_type: str  # 'code' or 'markdown'
    source: str
    first_line: str
    outputs: List[Dict] = field(default_factory=list)
    execution_count: Optional[int] = None
    has_error: bool = False
    error_message: Optional[str] = None


@dataclass
class IterationResult:
    """Result of a cell iteration attempt."""
    iteration: int
    success: bool
    cell_source: str
    output: Optional[str] = None
    error: Optional[str] = None
    objective_met: bool = False
    notes: str = ""


class NotebookHelper:
    """
    Helper class for reading, modifying, and writing Jupyter notebooks.

    Consolidates functionality from:
    - list_notebook_cells.py (cell listing)
    - fix_notebooks_execution.py (read/write/get/set source)
    - analyze_notebook_errors.py (error detection)
    """

    def __init__(self, notebook_path: str):
        """Initialize with notebook path."""
        self.path = Path(notebook_path)
        self.notebook: Dict[str, Any] = {}
        self._load()

    def _load(self) -> None:
        """Load notebook JSON from file."""
        with open(self.path, 'r', encoding='utf-8', newline='') as f:
            self.notebook = json.load(f)

    def save(self, path: Optional[str] = None) -> None:
        """Save notebook JSON to file with LF line endings."""
        save_path = Path(path) if path else self.path
        with open(save_path, 'w', encoding='utf-8', newline='\n') as f:
            json.dump(self.notebook, f, indent=1, ensure_ascii=False)
            f.write('\n')

    @property
    def cells(self) -> List[Dict]:
        """Get list of cells."""
        return self.notebook.get('cells', [])

    @property
    def cell_count(self) -> int:
        """Get number of cells."""
        return len(self.cells)

    def get_cell(self, index: int) -> Optional[Dict]:
        """Get cell by index."""
        if 0 <= index < len(self.cells):
            return self.cells[index]
        return None

    def get_cell_by_id(self, cell_id: str) -> Optional[Tuple[int, Dict]]:
        """Get cell by ID, returns (index, cell) or None."""
        for i, cell in enumerate(self.cells):
            if cell.get('id') == cell_id:
                return (i, cell)
        return None

    def get_cell_source(self, index: int) -> str:
        """Get cell source as string."""
        cell = self.get_cell(index)
        if not cell:
            return ""
        source = cell.get('source', [])
        return ''.join(source) if isinstance(source, list) else source

    def set_cell_source(self, index: int, source: str) -> bool:
        """Set cell source from string. Returns True if successful."""
        cell = self.get_cell(index)
        if not cell:
            return False
        lines = source.split('\n')
        cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])
        return True

    def get_cell_outputs(self, index: int) -> List[Dict]:
        """Get outputs for a code cell."""
        cell = self.get_cell(index)
        if not cell or cell.get('cell_type') != 'code':
            return []
        return cell.get('outputs', [])

    def get_cell_output_text(self, index: int) -> str:
        """Get combined text output from a code cell."""
        outputs = self.get_cell_outputs(index)
        text_parts = []

        for output in outputs:
            output_type = output.get('output_type', '')

            if output_type == 'stream':
                text = output.get('text', [])
                if isinstance(text, list):
                    text_parts.append(''.join(text))
                else:
                    text_parts.append(text)

            elif output_type == 'execute_result':
                data = output.get('data', {})
                if 'text/plain' in data:
                    text = data['text/plain']
                    if isinstance(text, list):
                        text_parts.append(''.join(text))
                    else:
                        text_parts.append(text)

            elif output_type == 'error':
                ename = output.get('ename', 'Error')
                evalue = output.get('evalue', '')
                text_parts.append(f"[{ename}] {evalue}")

        return '\n'.join(text_parts)

    def has_cell_error(self, index: int) -> Tuple[bool, Optional[str]]:
        """Check if cell has error output. Returns (has_error, error_message)."""
        outputs = self.get_cell_outputs(index)

        for output in outputs:
            if output.get('output_type') == 'error':
                ename = output.get('ename', 'Error')
                evalue = output.get('evalue', '')
                return (True, f"{ename}: {evalue}")

        return (False, None)

    def get_cell_info(self, index: int) -> Optional[CellInfo]:
        """Get detailed information about a cell."""
        cell = self.get_cell(index)
        if not cell:
            return None

        source = self.get_cell_source(index)
        first_line = source.split('\n')[0][:60] if source else ""
        has_error, error_msg = self.has_cell_error(index)

        return CellInfo(
            index=index,
            cell_id=cell.get('id', 'N/A'),
            cell_type=cell.get('cell_type', 'unknown'),
            source=source,
            first_line=first_line,
            outputs=self.get_cell_outputs(index),
            execution_count=cell.get('execution_count'),
            has_error=has_error,
            error_message=error_msg
        )

    def list_cells(self, show_source: bool = False) -> List[CellInfo]:
        """List all cells with their information."""
        cells_info = []
        for i in range(self.cell_count):
            info = self.get_cell_info(i)
            if info:
                cells_info.append(info)
        return cells_info

    def print_cells(self, show_source: bool = False) -> None:
        """Print cell listing to console."""
        print(f"\n{'='*80}")
        print(f"NOTEBOOK: {self.path.name}")
        print(f"{'='*80}")
        print(f"Total cells: {self.cell_count}\n")

        for info in self.list_cells():
            error_marker = " [ERROR]" if info.has_error else ""
            print(f"Cell {info.index:2d} | ID: {info.cell_id:15s} | "
                  f"Type: {info.cell_type:8s} | {info.first_line}{error_marker}")
            if show_source:
                print(f"    Source: {info.source[:100]}...")

        print(f"\n{'='*80}\n")

    def find_code_cells(self) -> List[int]:
        """Return indices of all code cells."""
        return [i for i, cell in enumerate(self.cells)
                if cell.get('cell_type') == 'code']

    def find_markdown_cells(self) -> List[int]:
        """Return indices of all markdown cells."""
        return [i for i, cell in enumerate(self.cells)
                if cell.get('cell_type') == 'markdown']

    def find_consecutive_code_cells(self) -> List[Tuple[int, int]]:
        """Find pairs of consecutive code cells (no markdown between them)."""
        pairs = []
        code_cells = self.find_code_cells()

        for i in range(len(code_cells) - 1):
            idx1, idx2 = code_cells[i], code_cells[i + 1]
            if idx2 == idx1 + 1:  # Directly consecutive
                pairs.append((idx1, idx2))

        return pairs

    def find_cells_with_pattern(self, pattern: str, cell_type: Optional[str] = None) -> List[int]:
        """Find cells containing a regex pattern."""
        matches = []
        regex = re.compile(pattern, re.IGNORECASE)

        for i, cell in enumerate(self.cells):
            if cell_type and cell.get('cell_type') != cell_type:
                continue
            source = self.get_cell_source(i)
            if regex.search(source):
                matches.append(i)

        return matches

    def find_cells_with_errors(self) -> List[int]:
        """Find all cells that have error outputs."""
        return [i for i in self.find_code_cells() if self.has_cell_error(i)[0]]

    def insert_cell(self, index: int, cell_type: str, source: str) -> str:
        """Insert a new cell at index. Returns the new cell ID."""
        import uuid
        cell_id = str(uuid.uuid4())[:8]

        lines = source.split('\n')
        source_list = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])

        new_cell = {
            "cell_type": cell_type,
            "id": cell_id,
            "metadata": {},
            "source": source_list
        }

        if cell_type == 'code':
            new_cell["outputs"] = []
            new_cell["execution_count"] = None

        self.cells.insert(index, new_cell)
        return cell_id

    def delete_cell(self, index: int) -> bool:
        """Delete cell at index. Returns True if successful."""
        if 0 <= index < len(self.cells):
            del self.cells[index]
            return True
        return False

    def replace_in_source(self, index: int, old: str, new: str,
                          replace_all: bool = False) -> int:
        """Replace text in cell source. Returns number of replacements."""
        source = self.get_cell_source(index)
        if replace_all:
            new_source = source.replace(old, new)
            count = source.count(old)
        else:
            new_source = source.replace(old, new, 1)
            count = 1 if old in source else 0

        if count > 0:
            self.set_cell_source(index, new_source)
        return count


class CellIterator:
    """
    Iterator for cell correction with objectives.

    This class provides a pattern for iteratively correcting a cell
    until an objective is met or max iterations are reached.

    Usage with MCP tools:
        iterator = CellIterator(
            notebook_path="path/to/notebook.ipynb",
            cell_index=5,
            objective="Output should contain 'SUCCESS'",
            max_iterations=5
        )

        # In a loop with MCP execution:
        while not iterator.is_complete:
            # Execute cell via MCP
            output = execute_cell_via_mcp(iterator.cell_index)

            # Check if objective is met
            result = iterator.evaluate(output)

            if not result.objective_met:
                # Generate correction (via LLM or rules)
                new_code = generate_correction(result.cell_source, result.error)
                iterator.apply_correction(new_code)
    """

    def __init__(
        self,
        notebook_path: str,
        cell_index: int,
        objective: str,
        max_iterations: int = 5,
        objective_checker: Optional[Callable[[str, str], bool]] = None
    ):
        """
        Initialize the cell iterator.

        Args:
            notebook_path: Path to the notebook
            cell_index: Index of the cell to iterate on
            objective: Description of the objective to achieve
            max_iterations: Maximum number of correction attempts
            objective_checker: Optional function(output, objective) -> bool
        """
        self.helper = NotebookHelper(notebook_path)
        self.cell_index = cell_index
        self.objective = objective
        self.max_iterations = max_iterations
        self.objective_checker = objective_checker or self._default_checker

        self.iteration = 0
        self.history: List[IterationResult] = []
        self.is_complete = False
        self.success = False

    def _default_checker(self, output: str, objective: str) -> bool:
        """Default objective checker: look for keywords in output."""
        # Check for common success indicators
        success_keywords = ['success', 'passed', 'complete', 'done', 'ok']
        error_keywords = ['error', 'failed', 'exception', 'traceback']

        output_lower = output.lower()

        # If output contains error keywords, not successful
        if any(kw in output_lower for kw in error_keywords):
            return False

        # Check if objective text appears in output
        if objective.lower() in output_lower:
            return True

        # Check for success keywords
        if any(kw in output_lower for kw in success_keywords):
            return True

        return False

    @property
    def current_source(self) -> str:
        """Get current cell source."""
        return self.helper.get_cell_source(self.cell_index)

    def evaluate(self, output: str, error: Optional[str] = None) -> IterationResult:
        """
        Evaluate the result of executing the current cell.

        Args:
            output: The output from cell execution
            error: Any error message from execution

        Returns:
            IterationResult with evaluation details
        """
        self.iteration += 1

        # Check for errors
        has_error = error is not None or self.helper.has_cell_error(self.cell_index)[0]

        # Check if objective is met
        objective_met = False
        if not has_error:
            objective_met = self.objective_checker(output, self.objective)

        result = IterationResult(
            iteration=self.iteration,
            success=not has_error,
            cell_source=self.current_source,
            output=output,
            error=error,
            objective_met=objective_met,
            notes=f"Iteration {self.iteration}/{self.max_iterations}"
        )

        self.history.append(result)

        # Update completion status
        if objective_met:
            self.is_complete = True
            self.success = True
        elif self.iteration >= self.max_iterations:
            self.is_complete = True
            self.success = False

        return result

    def apply_correction(self, new_source: str) -> None:
        """Apply a correction to the cell source."""
        self.helper.set_cell_source(self.cell_index, new_source)

    def save(self) -> None:
        """Save the notebook with corrections."""
        self.helper.save()

    def get_summary(self) -> Dict[str, Any]:
        """Get summary of the iteration process."""
        return {
            "notebook": str(self.helper.path),
            "cell_index": self.cell_index,
            "objective": self.objective,
            "iterations": self.iteration,
            "max_iterations": self.max_iterations,
            "success": self.success,
            "is_complete": self.is_complete,
            "history": [
                {
                    "iteration": r.iteration,
                    "success": r.success,
                    "objective_met": r.objective_met,
                    "error": r.error[:100] if r.error else None
                }
                for r in self.history
            ]
        }


# ============================================================================
# Utility functions for common operations
# ============================================================================

def read_notebook(path: str) -> Dict[str, Any]:
    """Read notebook JSON from file."""
    helper = NotebookHelper(path)
    return helper.notebook


def write_notebook(path: str, notebook: Dict[str, Any]) -> None:
    """Write notebook JSON to file."""
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)
        f.write('\n')


def list_notebook_cells(path: str, verbose: bool = False) -> None:
    """Print cell listing for a notebook."""
    helper = NotebookHelper(path)
    helper.print_cells(show_source=verbose)


def find_cells_needing_markdown(path: str) -> Dict[str, List]:
    """Find cells that might need pedagogical markdown."""
    helper = NotebookHelper(path)

    return {
        "consecutive_code_cells": helper.find_consecutive_code_cells(),
        "cells_with_errors": helper.find_cells_with_errors(),
        "code_cells_without_output": [
            i for i in helper.find_code_cells()
            if not helper.get_cell_outputs(i)
        ]
    }


# ============================================================================
# CLI interface
# ============================================================================

if __name__ == '__main__':
    import sys
    import argparse

    parser = argparse.ArgumentParser(
        description='Notebook helper utilities',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python notebook_helpers.py list notebook.ipynb
    python notebook_helpers.py list notebook.ipynb --verbose
    python notebook_helpers.py analyze notebook.ipynb
    python notebook_helpers.py get-source notebook.ipynb 5
    python notebook_helpers.py get-output notebook.ipynb 5
        """
    )

    subparsers = parser.add_subparsers(dest='command', help='Command to run')

    # list command
    list_parser = subparsers.add_parser('list', help='List cells in notebook')
    list_parser.add_argument('notebook', help='Path to notebook')
    list_parser.add_argument('--verbose', '-v', action='store_true',
                            help='Show cell source preview')

    # analyze command
    analyze_parser = subparsers.add_parser('analyze', help='Analyze notebook structure')
    analyze_parser.add_argument('notebook', help='Path to notebook')

    # get-source command
    source_parser = subparsers.add_parser('get-source', help='Get cell source')
    source_parser.add_argument('notebook', help='Path to notebook')
    source_parser.add_argument('cell_index', type=int, help='Cell index')

    # get-output command
    output_parser = subparsers.add_parser('get-output', help='Get cell output')
    output_parser.add_argument('notebook', help='Path to notebook')
    output_parser.add_argument('cell_index', type=int, help='Cell index')

    args = parser.parse_args()

    if args.command == 'list':
        list_notebook_cells(args.notebook, verbose=args.verbose)

    elif args.command == 'analyze':
        helper = NotebookHelper(args.notebook)
        print(f"\n{'='*60}")
        print(f"ANALYSIS: {helper.path.name}")
        print(f"{'='*60}")
        print(f"Total cells: {helper.cell_count}")
        print(f"Code cells: {len(helper.find_code_cells())}")
        print(f"Markdown cells: {len(helper.find_markdown_cells())}")
        print(f"Cells with errors: {len(helper.find_cells_with_errors())}")

        consecutive = helper.find_consecutive_code_cells()
        if consecutive:
            print(f"\nConsecutive code cells (need markdown):")
            for idx1, idx2 in consecutive:
                print(f"  Cells {idx1} and {idx2}")

        errors = helper.find_cells_with_errors()
        if errors:
            print(f"\nCells with errors:")
            for idx in errors:
                _, msg = helper.has_cell_error(idx)
                print(f"  Cell {idx}: {msg[:80]}")

    elif args.command == 'get-source':
        helper = NotebookHelper(args.notebook)
        source = helper.get_cell_source(args.cell_index)
        print(source)

    elif args.command == 'get-output':
        helper = NotebookHelper(args.notebook)
        output = helper.get_cell_output_text(args.cell_index)
        print(output if output else "(no output)")

    else:
        parser.print_help()
