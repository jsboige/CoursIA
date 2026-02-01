#!/usr/bin/env python3
"""
Consolidated Notebook Utilities for Lean notebooks.

Commands:
    list        - List cells with indexes and types
    format      - Fix markdown formatting (blank lines)
    info        - Show notebook summary info
    get-source  - Get source of a specific cell
    get-output  - Get output of a specific cell

Usage:
    python notebook_utils.py list <notebook.ipynb>
    python notebook_utils.py format <notebook.ipynb> [--dry-run]
    python notebook_utils.py info <notebook.ipynb>
    python notebook_utils.py get-source <notebook.ipynb> <cell_index>
    python notebook_utils.py get-output <notebook.ipynb> <cell_index>
"""

import json
import re
import sys
import argparse
from pathlib import Path
from typing import List, Dict, Any, Optional


# =============================================================================
# Notebook Helper Class
# =============================================================================

class NotebookHelper:
    """Helper class for reading and manipulating Jupyter notebooks."""

    def __init__(self, notebook_path: str):
        self.path = Path(notebook_path)
        with open(self.path, 'r', encoding='utf-8') as f:
            self.notebook = json.load(f)
        self.cells = self.notebook.get('cells', [])

    @property
    def cell_count(self) -> int:
        return len(self.cells)

    def get_cell(self, index: int) -> Optional[Dict]:
        """Get cell at index."""
        if 0 <= index < len(self.cells):
            return self.cells[index]
        return None

    def get_cell_source(self, index: int) -> str:
        """Get cell source as string."""
        cell = self.get_cell(index)
        if not cell:
            return ""
        source = cell.get('source', [])
        return ''.join(source) if isinstance(source, list) else source

    def get_cell_output_text(self, index: int) -> str:
        """Get text output from a cell."""
        cell = self.get_cell(index)
        if not cell or cell.get('cell_type') != 'code':
            return ""

        outputs = cell.get('outputs', [])
        texts = []
        for out in outputs:
            if out.get('output_type') == 'stream':
                texts.append(out.get('text', ''))
            elif out.get('output_type') == 'execute_result':
                data = out.get('data', {})
                if 'text/plain' in data:
                    texts.append(data['text/plain'])

        return ''.join(t if isinstance(t, str) else ''.join(t) for t in texts)

    def save(self):
        """Save notebook back to file."""
        with open(self.path, 'w', encoding='utf-8') as f:
            json.dump(self.notebook, f, ensure_ascii=False, indent=1)


# =============================================================================
# Markdown Formatting
# =============================================================================

class MarkdownFormatter:
    """Applies systematic formatting rules to markdown source arrays."""

    def format_source(self, source: List[str]) -> List[str]:
        """Apply all formatting rules to a source array."""
        if not source:
            return source

        text = ''.join(source)
        lines = text.split('\n')
        formatted_lines = self._apply_rules(lines)
        return self._to_jupyter_source(formatted_lines)

    def _apply_rules(self, lines: List[str]) -> List[str]:
        """Apply all formatting rules."""
        lines = self._explode_compressed_lines(lines)
        result = []

        for i, line in enumerate(lines):
            if i > 0 and result and not self._is_blank(result[-1]):
                if self._needs_blank_before(line, i, lines):
                    result.append('')

            result.append(line)

            if i < len(lines) - 1:
                next_line = lines[i + 1]
                if not self._is_blank(next_line):
                    if self._needs_blank_after(line, next_line):
                        result.append('')

        return self._collapse_blanks(result)

    def _explode_compressed_lines(self, lines: List[str]) -> List[str]:
        """Explode lines that have multiple logical lines compressed together."""
        result = []
        for line in lines:
            # Pattern: "--- ##" or "--- #" (horizontal rule followed by heading)
            if re.search(r'---\s+(#{1,4})\s+', line):
                parts = re.split(r'(\s+---\s+|\s---\s+|---\s+)', line)
                for part in parts:
                    part = part.strip()
                    if part and part != '---':
                        if part.startswith('---'):
                            result.append('---')
                            result.append(part[3:].strip())
                        else:
                            result.append(part)
                    elif part == '---':
                        result.append('---')
                continue

            result.append(line)

        return result

    def _needs_blank_before(self, line: str, index: int, all_lines: List[str]) -> bool:
        """Check if blank line needed before this line."""
        if re.match(r'^```', line):
            prev = all_lines[index - 1]
            if not re.match(r'^#+\s+', prev) and prev.strip():
                return True

        if re.match(r'^---\s*$', line):
            return True

        if re.match(r'^##\s+[^#]', line) and index > 0:
            prev = all_lines[index - 1]
            if prev.strip() and not re.match(r'^\*\*Navigation\*\*', prev):
                return True

        return False

    def _needs_blank_after(self, line: str, next_line: str) -> bool:
        """Check if blank line needed after this line."""
        if re.match(r'^#{2,4}\s+', line):
            return True

        if re.match(r'^```\s*$', line) and line.strip() == '```':
            return True

        if re.match(r'^---\s*$', line):
            return True

        return False

    def _is_blank(self, line: str) -> bool:
        return not line.strip()

    def _collapse_blanks(self, lines: List[str]) -> List[str]:
        """Collapse multiple consecutive blank lines."""
        result = []
        prev_blank = False
        for line in lines:
            is_blank = self._is_blank(line)
            if is_blank and prev_blank:
                continue
            result.append(line)
            prev_blank = is_blank
        return result

    def _to_jupyter_source(self, lines: List[str]) -> List[str]:
        """Convert lines back to Jupyter source format."""
        if not lines:
            return []
        result = []
        for i, line in enumerate(lines):
            if i < len(lines) - 1:
                result.append(line + '\n')
            else:
                result.append(line + '\n' if line else line)
        return result


# =============================================================================
# Commands
# =============================================================================

def cmd_list(notebook_path: str, verbose: bool = False):
    """List all cells with index, ID, and type."""
    helper = NotebookHelper(notebook_path)

    print(f"\n{'='*80}")
    print(f"NOTEBOOK: {helper.path.name}")
    print(f"{'='*80}")
    print(f"Total cells: {helper.cell_count}\n")

    code_cells = 0
    markdown_cells = 0

    for i, cell in enumerate(helper.cells):
        cell_type = cell['cell_type']
        cell_id = cell.get('id', 'N/A')[:12]

        if cell_type == 'code':
            code_cells += 1
        else:
            markdown_cells += 1

        source = helper.get_cell_source(i)
        first_line = source.split('\n')[0].strip()[:55]

        type_marker = 'C' if cell_type == 'code' else 'M'
        print(f"[{i:2d}] {type_marker} | {cell_id:12s} | {first_line}")

    print(f"\n{'='*80}")
    print(f"Summary: {code_cells} code cells, {markdown_cells} markdown cells")
    print(f"{'='*80}\n")


def cmd_format(notebook_path: str, dry_run: bool = False):
    """Format markdown cells with proper blank lines."""
    helper = NotebookHelper(notebook_path)
    formatter = MarkdownFormatter()

    print(f"\nProcessing: {helper.path.name}")

    cells_modified = 0
    blank_lines_added = 0

    for i, cell in enumerate(helper.cells):
        if cell['cell_type'] != 'markdown' or not cell['source']:
            continue

        original = cell['source']
        formatted = formatter.format_source(original)

        if formatted != original:
            if not dry_run:
                cell['source'] = formatted
            cells_modified += 1

            orig_blanks = sum(1 for line in original if not ''.join([line]).strip())
            new_blanks = sum(1 for line in formatted if not ''.join([line]).strip())
            added = new_blanks - orig_blanks
            blank_lines_added += added

            print(f"  Cell {i:2d}: +{added} blank lines")

    if not dry_run and cells_modified > 0:
        helper.save()

    mode = " (dry-run)" if dry_run else ""
    print(f"  Total: {cells_modified} cells modified, {blank_lines_added} blank lines added{mode}")


def cmd_info(notebook_path: str):
    """Show notebook summary info."""
    helper = NotebookHelper(notebook_path)

    code_cells = sum(1 for c in helper.cells if c['cell_type'] == 'code')
    markdown_cells = sum(1 for c in helper.cells if c['cell_type'] == 'markdown')

    metadata = helper.notebook.get('metadata', {})
    kernel_spec = metadata.get('kernelspec', {})
    kernel_name = kernel_spec.get('name', 'unknown')
    language = kernel_spec.get('language', 'unknown')

    print(f"\n{'='*60}")
    print(f"NOTEBOOK INFO: {helper.path.name}")
    print(f"{'='*60}")
    print(f"Total cells:    {helper.cell_count}")
    print(f"  Code cells:   {code_cells}")
    print(f"  Markdown:     {markdown_cells}")
    print(f"Kernel:         {kernel_name}")
    print(f"Language:       {language}")
    print(f"File size:      {helper.path.stat().st_size:,} bytes")
    print(f"{'='*60}\n")


def cmd_get_source(notebook_path: str, cell_index: int):
    """Get source of a specific cell."""
    helper = NotebookHelper(notebook_path)
    source = helper.get_cell_source(cell_index)
    if source:
        print(source)
    else:
        print(f"Cell {cell_index} not found or empty")


def cmd_get_output(notebook_path: str, cell_index: int):
    """Get output of a specific cell."""
    helper = NotebookHelper(notebook_path)
    output = helper.get_cell_output_text(cell_index)
    if output:
        print(output)
    else:
        print(f"(no output)")


# =============================================================================
# Main
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Notebook utilities for Lean notebooks',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    subparsers = parser.add_subparsers(dest='command', help='Command to run')

    # list command
    list_parser = subparsers.add_parser('list', help='List cells')
    list_parser.add_argument('notebook', help='Notebook path')
    list_parser.add_argument('-v', '--verbose', action='store_true')

    # format command
    format_parser = subparsers.add_parser('format', help='Format markdown')
    format_parser.add_argument('notebook', help='Notebook path')
    format_parser.add_argument('--dry-run', action='store_true', help='Show changes without applying')

    # info command
    info_parser = subparsers.add_parser('info', help='Show notebook info')
    info_parser.add_argument('notebook', help='Notebook path')

    # get-source command
    source_parser = subparsers.add_parser('get-source', help='Get cell source')
    source_parser.add_argument('notebook', help='Notebook path')
    source_parser.add_argument('cell_index', type=int, help='Cell index')

    # get-output command
    output_parser = subparsers.add_parser('get-output', help='Get cell output')
    output_parser.add_argument('notebook', help='Notebook path')
    output_parser.add_argument('cell_index', type=int, help='Cell index')

    args = parser.parse_args()

    if args.command == 'list':
        cmd_list(args.notebook, getattr(args, 'verbose', False))
    elif args.command == 'format':
        cmd_format(args.notebook, args.dry_run)
    elif args.command == 'info':
        cmd_info(args.notebook)
    elif args.command == 'get-source':
        cmd_get_source(args.notebook, args.cell_index)
    elif args.command == 'get-output':
        cmd_get_output(args.notebook, args.cell_index)
    else:
        parser.print_help()


if __name__ == '__main__':
    main()
