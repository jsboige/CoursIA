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

    # ========================================================================
    # ENRICHMENT VALIDATION METHODS
    # ========================================================================

    def get_cell_sequence(self, start: int, end: int = None,
                          max_preview: int = 60) -> List[Dict[str, Any]]:
        """
        Get a compact sequence view of cells in a range.

        Perfect for agents to validate their insertions by checking
        the cell sequence around a modified area.

        Args:
            start: Starting cell index (inclusive)
            end: Ending cell index (inclusive). If None, returns just start cell.
            max_preview: Max characters for source preview

        Returns:
            List of dicts with: index, cell_id, type, preview, has_output
        """
        if end is None:
            end = start

        # Clamp to valid range
        start = max(0, start)
        end = min(end, self.cell_count - 1)

        sequence = []
        for i in range(start, end + 1):
            cell = self.get_cell(i)
            if not cell:
                continue

            source = self.get_cell_source(i)
            first_line = source.split('\n')[0][:max_preview] if source else ""

            # Clean up the preview
            preview = first_line.strip()
            if len(first_line) == max_preview:
                preview += "..."

            cell_info = {
                'index': i,
                'cell_id': cell.get('id', 'N/A'),
                'type': cell.get('cell_type', 'unknown'),
                'preview': preview,
            }

            if cell.get('cell_type') == 'code':
                cell_info['has_output'] = bool(cell.get('outputs', []))

            sequence.append(cell_info)

        return sequence

    def print_cell_sequence(self, start: int, end: int = None) -> str:
        """
        Print a formatted cell sequence for easy visual inspection.

        Returns:
            Formatted string showing the cell sequence
        """
        sequence = self.get_cell_sequence(start, end)
        lines = []

        for cell in sequence:
            type_marker = "[MD]" if cell['type'] == 'markdown' else "[CODE]"
            output_marker = ""
            if cell['type'] == 'code':
                output_marker = " (output)" if cell.get('has_output') else " (no output)"

            lines.append(
                f"  {cell['index']:2d}: {type_marker:6s} {cell['cell_id']:10s} | {cell['preview']}{output_marker}"
            )

        return "\n".join(lines)

    def validate_enrichment_context(self, code_cell_index: int) -> Dict[str, Any]:
        """
        Validate the enrichment context around a code cell.

        Checks if a code cell has:
        - An introduction/explanation BEFORE it (or is first in section)
        - An interpretation/analysis AFTER it (if it produces output)

        Args:
            code_cell_index: Index of the code cell to check

        Returns:
            Dict with:
                valid: bool - True if structure is correct
                has_intro_before: bool - Markdown exists before
                has_interpretation_after: bool - Markdown exists after
                prev_cell: Optional[Dict] - Info about previous cell
                next_cell: Optional[Dict] - Info about next cell
                suggestion: str - What to fix if invalid
        """
        result = {
            'valid': True,
            'code_cell_index': code_cell_index,
            'has_intro_before': False,
            'has_interpretation_after': False,
            'prev_cell': None,
            'next_cell': None,
            'suggestion': ''
        }

        cell = self.get_cell(code_cell_index)
        if not cell or cell.get('cell_type') != 'code':
            result['valid'] = False
            result['suggestion'] = f"Cell {code_cell_index} is not a code cell"
            return result

        # Check previous cell
        if code_cell_index > 0:
            prev = self.get_cell(code_cell_index - 1)
            if prev:
                prev_source = self.get_cell_source(code_cell_index - 1)
                result['prev_cell'] = {
                    'index': code_cell_index - 1,
                    'type': prev.get('cell_type'),
                    'preview': prev_source.split('\n')[0][:60] if prev_source else ""
                }
                if prev.get('cell_type') == 'markdown':
                    result['has_intro_before'] = True

        # Check next cell
        if code_cell_index < self.cell_count - 1:
            next_cell = self.get_cell(code_cell_index + 1)
            if next_cell:
                next_source = self.get_cell_source(code_cell_index + 1)
                result['next_cell'] = {
                    'index': code_cell_index + 1,
                    'type': next_cell.get('cell_type'),
                    'preview': next_source.split('\n')[0][:60] if next_source else ""
                }
                if next_cell.get('cell_type') == 'markdown':
                    result['has_interpretation_after'] = True

        # Determine if structure is valid
        code_source = self.get_cell_source(code_cell_index)
        has_output = bool(cell.get('outputs', []))

        # A code cell with significant output should have interpretation after
        if has_output and not result['has_interpretation_after']:
            result['valid'] = False
            result['suggestion'] = f"Insert interpretation AFTER cell {code_cell_index} (using cell_id='{cell.get('id')}')"

        # Check for consecutive code cells
        if not result['has_intro_before'] and result['prev_cell']:
            if result['prev_cell']['type'] == 'code':
                result['valid'] = False
                result['suggestion'] = f"Insert explanation BEFORE cell {code_cell_index} (after cell {code_cell_index - 1})"

        return result

    def find_cells_needing_enrichment(self) -> List[Dict[str, Any]]:
        """
        Find all code cells that need enrichment (interpretation after output).

        Returns:
            List of dicts describing cells that need attention
        """
        needs_enrichment = []

        for i in range(self.cell_count):
            cell = self.get_cell(i)
            if not cell or cell.get('cell_type') != 'code':
                continue

            # Skip empty cells
            source = self.get_cell_source(i)
            if not source.strip():
                continue

            # Check context
            context = self.validate_enrichment_context(i)
            if not context['valid']:
                needs_enrichment.append({
                    'cell_index': i,
                    'cell_id': cell.get('id'),
                    'first_line': source.split('\n')[0][:50],
                    'has_output': bool(cell.get('outputs', [])),
                    'issue': context['suggestion']
                })

        return needs_enrichment

    def get_insertion_plan(self) -> List[Dict[str, Any]]:
        """
        Generate a plan for enriching the notebook.

        Returns a list of insertions to make, in REVERSE ORDER
        (so indices stay valid during insertion from bottom to top).

        Each item has:
            insert_after_index: cell index to insert after
            insert_after_id: cell_id (if available, else None)
            content_type: 'interpretation' or 'introduction'
            code_preview: preview of the code cell
            insert_position: human-readable position description
        """
        plan = []

        for i in range(self.cell_count):
            cell = self.get_cell(i)
            if not cell or cell.get('cell_type') != 'code':
                continue

            source = self.get_cell_source(i)
            if not source.strip():
                continue

            has_output = bool(cell.get('outputs', []))
            cell_id = cell.get('id')

            # Check if needs interpretation after (code with output but no markdown after)
            if has_output and i < self.cell_count - 1:
                next_cell = self.get_cell(i + 1)
                if next_cell and next_cell.get('cell_type') == 'code':
                    plan.append({
                        'insert_after_index': i,
                        'insert_after_id': cell_id,
                        'content_type': 'interpretation',
                        'code_preview': source.split('\n')[0][:50],
                        'insert_position': f"After cell {i} (code)"
                    })

        # REVERSE the plan so insertions don't shift indices
        plan.reverse()

        return plan

    def print_enrichment_plan(self) -> str:
        """
        Print a human-readable enrichment plan.

        Format designed for agent consumption: shows exactly what to do.
        """
        plan = self.get_insertion_plan()
        if not plan:
            return "No enrichment needed - all code cells have markdown after them."

        lines = [
            "ENRICHMENT PLAN (execute in this order - bottom to top):",
            "=" * 60
        ]

        for item in plan:
            lines.append(f"\n{item['content_type'].upper()}:")
            lines.append(f"  Insert AFTER cell index {item['insert_after_index']}")
            if item['insert_after_id']:
                lines.append(f"  Cell ID: {item['insert_after_id']}")
            lines.append(f"  Code: {item['code_preview']}...")
            lines.append(f"  Action: Add markdown interpretation of this code's output")

        return "\n".join(lines)


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
# Execution classes and functions
# ============================================================================

@dataclass
class ExecutionResult:
    """Result of notebook/cell execution."""
    success: bool
    cell_index: Optional[int] = None
    output: str = ""
    error: Optional[str] = None
    duration: float = 0.0
    kernel: str = "unknown"


@dataclass
class NotebookExecutionResult:
    """Result of full notebook execution."""
    success: bool
    notebook_path: str
    output_path: Optional[str] = None
    kernel: str = "unknown"
    total_cells: int = 0
    executed_cells: int = 0
    failed_cells: int = 0
    duration: float = 0.0
    cell_results: List[ExecutionResult] = field(default_factory=list)
    errors: List[str] = field(default_factory=list)

    @property
    def success_rate(self) -> float:
        if self.executed_cells == 0:
            return 0.0
        return ((self.executed_cells - self.failed_cells) / self.executed_cells) * 100


class NotebookExecutor:
    """
    Executor for running notebooks with various backends.

    Supports:
    - jupyter_client for cell-by-cell execution
    - papermill for full notebook execution
    - Auto-detection of kernel type (python3, .net-csharp, lean4, etc.)

    Consolidated from:
    - verify_lean.py (execute_notebook_cell_by_cell)
    - papermill-coursia/core/executor.py (PapermillExecutor)
    - verify_notebooks.py (execute_python_notebook)
    """

    # Known kernel mappings
    KERNEL_PATTERNS = {
        'python': 'python3',
        'python3': 'python3',
        '.net-csharp': '.net-csharp',
        '.net-fsharp': '.net-fsharp',
        'csharp': '.net-csharp',
        'fsharp': '.net-fsharp',
        'lean4': 'lean4',
        'lean': 'lean4',
    }

    def __init__(self, timeout: int = 300, verbose: bool = False):
        """
        Initialize the executor.

        Args:
            timeout: Default timeout in seconds for execution
            verbose: Whether to print progress messages
        """
        self.timeout = timeout
        self.verbose = verbose
        self._jupyter_client = None

    def detect_kernel(self, notebook_path: str) -> str:
        """
        Detect the appropriate kernel for a notebook.

        Args:
            notebook_path: Path to the notebook

        Returns:
            Kernel name (e.g., 'python3', '.net-csharp', 'lean4')
        """
        try:
            helper = NotebookHelper(notebook_path)
            metadata = helper.notebook.get('metadata', {})
            kernel_spec = metadata.get('kernelspec', {})
            kernel_name = kernel_spec.get('name', '').lower()
            language = kernel_spec.get('language', '').lower()

            # Check kernel name directly
            if kernel_name in self.KERNEL_PATTERNS:
                return self.KERNEL_PATTERNS[kernel_name]

            # Check language
            if 'python' in language:
                return 'python3'
            elif language in ['c#', 'csharp']:
                return '.net-csharp'
            elif language in ['f#', 'fsharp']:
                return '.net-fsharp'
            elif 'lean' in language:
                return 'lean4'

            # Check for .NET magic commands in cells
            for cell in helper.cells:
                if cell.get('cell_type') == 'code':
                    source = ''.join(cell.get('source', []))
                    if '#!import' in source or '#!csharp' in source:
                        return '.net-csharp'
                    if '#!fsharp' in source:
                        return '.net-fsharp'

            return 'python3'  # Default

        except Exception as e:
            if self.verbose:
                print(f"Warning: Could not detect kernel: {e}")
            return 'python3'

    def execute_cell(
        self,
        notebook_path: str,
        cell_index: int,
        kernel_name: Optional[str] = None,
        timeout: Optional[int] = None
    ) -> ExecutionResult:
        """
        Execute a single cell using jupyter_client.

        Args:
            notebook_path: Path to the notebook
            cell_index: Index of the cell to execute
            kernel_name: Kernel to use (auto-detected if None)
            timeout: Timeout in seconds (uses default if None)

        Returns:
            ExecutionResult with output and status
        """
        import time
        start_time = time.time()

        try:
            import jupyter_client
        except ImportError:
            return ExecutionResult(
                success=False,
                cell_index=cell_index,
                error="jupyter_client not installed. Run: pip install jupyter-client",
                duration=time.time() - start_time
            )

        kernel_name = kernel_name or self.detect_kernel(notebook_path)
        timeout = timeout or self.timeout

        helper = NotebookHelper(notebook_path)
        cell = helper.get_cell(cell_index)

        if not cell:
            return ExecutionResult(
                success=False,
                cell_index=cell_index,
                error=f"Cell {cell_index} not found",
                kernel=kernel_name,
                duration=time.time() - start_time
            )

        if cell.get('cell_type') != 'code':
            return ExecutionResult(
                success=True,
                cell_index=cell_index,
                output="Skipped (non-code cell)",
                kernel=kernel_name,
                duration=time.time() - start_time
            )

        source = helper.get_cell_source(cell_index)
        if not source.strip():
            return ExecutionResult(
                success=True,
                cell_index=cell_index,
                output="Skipped (empty cell)",
                kernel=kernel_name,
                duration=time.time() - start_time
            )

        # Start kernel if not already running
        try:
            km = jupyter_client.KernelManager(kernel_name=kernel_name)
            km.start_kernel()
            kc = km.client()
            kc.start_channels()
            kc.wait_for_ready(timeout=30)
        except Exception as e:
            return ExecutionResult(
                success=False,
                cell_index=cell_index,
                error=f"Failed to start {kernel_name} kernel: {e}",
                kernel=kernel_name,
                duration=time.time() - start_time
            )

        try:
            # Set working directory
            nb_dir = str(Path(notebook_path).parent)
            if kernel_name == 'python3':
                kc.execute(f"import os; os.chdir(r'{nb_dir}')")
            elif '.net' in kernel_name:
                kc.execute(f'System.IO.Directory.SetCurrentDirectory(@"{nb_dir}")')

            # Wait for wd setup
            self._wait_for_idle(kc, timeout=10)

            # Execute the cell
            kc.execute(source)

            # Collect outputs
            outputs = []
            errors = []

            while True:
                try:
                    msg = kc.get_iopub_msg(timeout=timeout)
                    msg_type = msg['msg_type']
                    content = msg.get('content', {})

                    if msg_type == 'stream':
                        outputs.append(content.get('text', ''))
                    elif msg_type == 'execute_result':
                        data = content.get('data', {})
                        outputs.append(data.get('text/plain', str(data)))
                    elif msg_type == 'error':
                        ename = content.get('ename', 'Error')
                        evalue = content.get('evalue', '')
                        errors.append(f"{ename}: {evalue}")
                    elif msg_type == 'status' and content.get('execution_state') == 'idle':
                        break
                except Exception:
                    break

            output_text = '\n'.join(outputs)
            error_text = '\n'.join(errors) if errors else None

            return ExecutionResult(
                success=len(errors) == 0,
                cell_index=cell_index,
                output=output_text,
                error=error_text,
                kernel=kernel_name,
                duration=time.time() - start_time
            )

        finally:
            try:
                kc.stop_channels()
                km.shutdown_kernel(now=True)
            except:
                pass

    def _wait_for_idle(self, kc, timeout: int = 10) -> None:
        """Wait for kernel to become idle."""
        while True:
            try:
                msg = kc.get_iopub_msg(timeout=timeout)
                if msg['msg_type'] == 'status' and msg['content']['execution_state'] == 'idle':
                    break
            except:
                break

    def execute_notebook_cell_by_cell(
        self,
        notebook_path: str,
        kernel_name: Optional[str] = None,
        timeout_per_cell: int = 60,
        stop_on_error: bool = False
    ) -> NotebookExecutionResult:
        """
        Execute all cells in a notebook sequentially.

        Args:
            notebook_path: Path to the notebook
            kernel_name: Kernel to use (auto-detected if None)
            timeout_per_cell: Timeout per cell in seconds
            stop_on_error: Whether to stop on first error

        Returns:
            NotebookExecutionResult with all cell results
        """
        import time
        start_time = time.time()

        try:
            import jupyter_client
        except ImportError:
            return NotebookExecutionResult(
                success=False,
                notebook_path=notebook_path,
                errors=["jupyter_client not installed"]
            )

        kernel_name = kernel_name or self.detect_kernel(notebook_path)
        helper = NotebookHelper(notebook_path)

        result = NotebookExecutionResult(
            success=True,
            notebook_path=notebook_path,
            kernel=kernel_name,
            total_cells=helper.cell_count
        )

        # Start kernel
        try:
            km = jupyter_client.KernelManager(kernel_name=kernel_name)
            km.start_kernel()
            kc = km.client()
            kc.start_channels()
            kc.wait_for_ready(timeout=30)
        except Exception as e:
            result.success = False
            result.errors.append(f"Failed to start {kernel_name} kernel: {e}")
            result.duration = time.time() - start_time
            return result

        try:
            # Set working directory
            nb_dir = str(Path(notebook_path).parent)
            if kernel_name == 'python3':
                kc.execute(f"import os; os.chdir(r'{nb_dir}')")
            elif '.net' in kernel_name:
                kc.execute(f'System.IO.Directory.SetCurrentDirectory(@"{nb_dir}")')
            self._wait_for_idle(kc, timeout=10)

            # Execute each cell
            for i, cell in enumerate(helper.cells):
                if cell.get('cell_type') != 'code':
                    continue

                source = helper.get_cell_source(i)
                if not source.strip():
                    continue

                if self.verbose:
                    print(f"  Cell {i}: ", end="", flush=True)

                cell_start = time.time()
                outputs = []
                errors = []

                try:
                    kc.execute(source)

                    while True:
                        try:
                            msg = kc.get_iopub_msg(timeout=timeout_per_cell)
                            msg_type = msg['msg_type']
                            content = msg.get('content', {})

                            if msg_type == 'stream':
                                outputs.append(content.get('text', ''))
                            elif msg_type == 'execute_result':
                                data = content.get('data', {})
                                outputs.append(data.get('text/plain', ''))
                            elif msg_type == 'error':
                                ename = content.get('ename', 'Error')
                                evalue = content.get('evalue', '')
                                errors.append(f"{ename}: {evalue}")
                            elif msg_type == 'status' and content.get('execution_state') == 'idle':
                                break
                        except Exception as e:
                            if 'timeout' in str(e).lower():
                                errors.append(f"Timeout after {timeout_per_cell}s")
                            break

                except Exception as e:
                    errors.append(str(e))

                cell_result = ExecutionResult(
                    success=len(errors) == 0,
                    cell_index=i,
                    output='\n'.join(outputs),
                    error='\n'.join(errors) if errors else None,
                    kernel=kernel_name,
                    duration=time.time() - cell_start
                )

                result.cell_results.append(cell_result)
                result.executed_cells += 1

                if cell_result.success:
                    if self.verbose:
                        print("OK")
                else:
                    result.failed_cells += 1
                    result.errors.append(f"Cell {i}: {cell_result.error}")
                    if self.verbose:
                        print(f"FAILED: {cell_result.error[:50] if cell_result.error else 'unknown'}")
                    if stop_on_error:
                        break

            result.success = result.failed_cells == 0
            result.duration = time.time() - start_time

        finally:
            try:
                kc.stop_channels()
                km.shutdown_kernel(now=True)
            except:
                pass

        return result

    def execute_with_papermill(
        self,
        notebook_path: str,
        output_path: Optional[str] = None,
        parameters: Optional[Dict[str, Any]] = None,
        kernel_name: Optional[str] = None,
        timeout: Optional[int] = None
    ) -> NotebookExecutionResult:
        """
        Execute a notebook using Papermill (subprocess).

        Args:
            notebook_path: Path to the notebook
            output_path: Path for output notebook (auto-generated if None)
            parameters: Parameters to inject
            kernel_name: Kernel to use (auto-detected if None)
            timeout: Timeout in seconds

        Returns:
            NotebookExecutionResult
        """
        import subprocess
        import time
        import sys

        start_time = time.time()
        kernel_name = kernel_name or self.detect_kernel(notebook_path)
        timeout = timeout or self.timeout

        nb_path = Path(notebook_path)
        if output_path is None:
            output_path = str(nb_path.parent / f"{nb_path.stem}_output{nb_path.suffix}")

        cmd = [
            sys.executable, '-m', 'papermill',
            str(notebook_path),
            str(output_path),
            '--kernel', kernel_name
        ]

        # Add parameters
        if parameters:
            for key, value in parameters.items():
                cmd.extend(['-p', str(key), str(value)])

        result = NotebookExecutionResult(
            success=False,
            notebook_path=notebook_path,
            output_path=output_path,
            kernel=kernel_name
        )

        try:
            if self.verbose:
                print(f"Executing with Papermill (kernel={kernel_name})...")

            proc_result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout,
                cwd=str(nb_path.parent)
            )

            result.duration = time.time() - start_time

            if proc_result.returncode == 0:
                result.success = True
                if self.verbose:
                    print(f"Success in {result.duration:.1f}s")
            else:
                result.errors.append(proc_result.stderr[-500:] if proc_result.stderr else "Unknown error")
                if self.verbose:
                    print(f"Failed: {result.errors[-1][:100]}")

        except subprocess.TimeoutExpired:
            result.duration = timeout
            result.errors.append(f"Timeout after {timeout}s")
            if self.verbose:
                print(f"Timeout after {timeout}s")

        except Exception as e:
            result.duration = time.time() - start_time
            result.errors.append(str(e))
            if self.verbose:
                print(f"Error: {e}")

        return result


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

    # sequence command - NEW for enrichment validation
    seq_parser = subparsers.add_parser('sequence', help='Show cell sequence around an index')
    seq_parser.add_argument('notebook', help='Path to notebook')
    seq_parser.add_argument('start', type=int, help='Start cell index')
    seq_parser.add_argument('end', type=int, nargs='?', default=None, help='End cell index (optional)')

    # validate-context command - NEW for enrichment validation
    ctx_parser = subparsers.add_parser('validate-context', help='Validate enrichment context around a code cell')
    ctx_parser.add_argument('notebook', help='Path to notebook')
    ctx_parser.add_argument('cell_index', type=int, help='Code cell index to validate')

    # enrichment-plan command - NEW
    plan_parser = subparsers.add_parser('enrichment-plan', help='Show cells needing enrichment')
    plan_parser.add_argument('notebook', help='Path to notebook')
    plan_parser.add_argument('--json', action='store_true', help='Output as JSON')

    # execute command
    exec_parser = subparsers.add_parser('execute', help='Execute notebook')
    exec_parser.add_argument('notebook', help='Path to notebook')
    exec_parser.add_argument('--cell', type=int, default=None,
                             help='Execute only this cell index')
    exec_parser.add_argument('--kernel', default=None,
                             help='Kernel to use (auto-detect if not specified)')
    exec_parser.add_argument('--timeout', type=int, default=300,
                             help='Timeout in seconds (default: 300)')
    exec_parser.add_argument('--papermill', action='store_true',
                             help='Use Papermill instead of cell-by-cell')
    exec_parser.add_argument('--verbose', '-v', action='store_true',
                             help='Verbose output')

    # detect-kernel command
    kernel_parser = subparsers.add_parser('detect-kernel', help='Detect notebook kernel')
    kernel_parser.add_argument('notebook', help='Path to notebook')

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

    elif args.command == 'sequence':
        helper = NotebookHelper(args.notebook)
        end = args.end if args.end is not None else args.start + 4
        print(f"\nCell sequence [{args.start}-{end}] in {helper.path.name}:")
        print(helper.print_cell_sequence(args.start, end))
        print()

    elif args.command == 'validate-context':
        helper = NotebookHelper(args.notebook)
        result = helper.validate_enrichment_context(args.cell_index)
        print(f"\nEnrichment context for cell {args.cell_index}:")
        print(f"  Valid: {result['valid']}")
        print(f"  Has intro before: {result['has_intro_before']}")
        print(f"  Has interpretation after: {result['has_interpretation_after']}")
        if result['prev_cell']:
            print(f"  Previous cell: [{result['prev_cell']['type']}] {result['prev_cell']['preview'][:40]}")
        if result['next_cell']:
            print(f"  Next cell: [{result['next_cell']['type']}] {result['next_cell']['preview'][:40]}")
        if result['suggestion']:
            print(f"  Suggestion: {result['suggestion']}")
        print()

    elif args.command == 'enrichment-plan':
        helper = NotebookHelper(args.notebook)
        if args.json:
            plan = helper.get_insertion_plan()
            print(json.dumps(plan, indent=2))
        else:
            print(f"\n{helper.path.name}")
            print(helper.print_enrichment_plan())
        print()

    elif args.command == 'execute':
        executor = NotebookExecutor(timeout=args.timeout, verbose=args.verbose)

        if args.cell is not None:
            # Execute single cell
            result = executor.execute_cell(
                args.notebook,
                args.cell,
                kernel_name=args.kernel
            )
            print(f"\nCell {result.cell_index}:")
            print(f"  Success: {result.success}")
            print(f"  Kernel: {result.kernel}")
            print(f"  Duration: {result.duration:.2f}s")
            if result.output:
                print(f"  Output: {result.output[:500]}")
            if result.error:
                print(f"  Error: {result.error}")
        elif args.papermill:
            # Execute with Papermill
            result = executor.execute_with_papermill(
                args.notebook,
                kernel_name=args.kernel
            )
            print(f"\nNotebook: {result.notebook_path}")
            print(f"  Success: {result.success}")
            print(f"  Kernel: {result.kernel}")
            print(f"  Duration: {result.duration:.2f}s")
            if result.output_path:
                print(f"  Output: {result.output_path}")
            if result.errors:
                print(f"  Errors: {result.errors}")
        else:
            # Execute cell by cell
            result = executor.execute_notebook_cell_by_cell(
                args.notebook,
                kernel_name=args.kernel,
                timeout_per_cell=min(args.timeout, 60)
            )
            print(f"\nNotebook: {result.notebook_path}")
            print(f"  Success: {result.success}")
            print(f"  Kernel: {result.kernel}")
            print(f"  Cells: {result.executed_cells}/{result.total_cells}")
            print(f"  Failed: {result.failed_cells}")
            print(f"  Success rate: {result.success_rate:.1f}%")
            print(f"  Duration: {result.duration:.2f}s")
            if result.errors:
                print(f"  Errors:")
                for err in result.errors[:5]:
                    print(f"    - {err[:100]}")

    elif args.command == 'detect-kernel':
        executor = NotebookExecutor()
        kernel = executor.detect_kernel(args.notebook)
        print(f"Detected kernel: {kernel}")

    else:
        parser.print_help()
