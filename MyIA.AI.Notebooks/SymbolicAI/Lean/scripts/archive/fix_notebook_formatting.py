#!/usr/bin/env python3
"""
Systematic Notebook Markdown Formatting Fixer

Fixes markdown formatting by adding proper blank lines according to rules.
"""

import json
import re
from pathlib import Path
from typing import List
import argparse

class MarkdownFormatter:
    """Applies systematic formatting rules to markdown source arrays."""

    def format_source(self, source: List[str]) -> List[str]:
        """Apply all formatting rules to a source array."""
        if not source:
            return source

        # Convert to lines
        text = ''.join(source)
        lines = text.split('\n')

        # Apply formatting rules
        formatted_lines = self._apply_rules(lines)

        # Convert back to Jupyter format
        return self._to_jupyter_source(formatted_lines)

    def _apply_rules(self, lines: List[str]) -> List[str]:
        """Apply all formatting rules."""
        # First, explode compressed lines (e.g., "--- ## Title" → ["---", "## Title"])
        lines = self._explode_compressed_lines(lines)

        result = []

        for i, line in enumerate(lines):
            # Check if blank needed BEFORE this line
            if i > 0 and result and not self._is_blank(result[-1]):
                if self._needs_blank_before(line, i, lines):
                    result.append('')

            # Add current line
            result.append(line)

            # Check if blank needed AFTER this line
            if i < len(lines) - 1:
                next_line = lines[i + 1]
                if not self._is_blank(next_line):
                    if self._needs_blank_after(line, next_line):
                        result.append('')

        # Collapse multiple blanks
        return self._collapse_blanks(result)

    def _explode_compressed_lines(self, lines: List[str]) -> List[str]:
        """Explode lines that have multiple logical lines compressed together."""
        result = []
        for line in lines:
            # Pattern 1: "--- ##" or "--- #" (horizontal rule followed by heading)
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

            # Pattern 2: "## Title Text" followed by more headings (no line break)
            # Split on heading markers that aren't at the start
            if re.search(r'\S\s+(#{2,4})\s+', line):
                parts = []
                current = ""
                i = 0
                while i < len(line):
                    # Check if we're at a heading marker in the middle
                    if i > 0 and line[i:i+2] in ['##', '###', '####'] and line[i-1].isspace():
                        if current.strip():
                            parts.append(current.strip())
                        current = ""
                    current += line[i]
                    i += 1
                if current.strip():
                    parts.append(current.strip())
                result.extend(parts)
                continue

            # No compression detected, keep as is
            result.append(line)

        return result

    def _needs_blank_before(self, line: str, index: int, all_lines: List[str]) -> bool:
        """Check if blank line needed before this line."""
        # Before code blocks (unless after heading)
        if re.match(r'^```', line):
            prev = all_lines[index - 1]
            if not re.match(r'^#+\s+', prev) and prev.strip():
                return True

        # Before horizontal rules
        if re.match(r'^---\s*$', line):
            return True

        # Before main section headings
        if re.match(r'^##\s+[^#]', line) and index > 0:
            prev = all_lines[index - 1]
            if prev.strip() and not re.match(r'^\*\*Navigation\*\*', prev):
                return True

        return False

    def _needs_blank_after(self, line: str, next_line: str) -> bool:
        """Check if blank line needed after this line."""
        # After all headings
        if re.match(r'^#{2,4}\s+', line):
            return True

        # After closing code blocks
        if re.match(r'^```\s*$', line) and line.strip() == '```':
            return True

        # After horizontal rules
        if re.match(r'^---\s*$', line):
            return True

        return False

    def _is_blank(self, line: str) -> bool:
        """Check if line is blank."""
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


class NotebookFormatter:
    """Formats all markdown cells in a Jupyter notebook."""

    def __init__(self, debug: bool = False):
        self.debug = debug
        self.formatter = MarkdownFormatter()

    def format_notebook(self, notebook_path: Path):
        """Format all markdown cells in notebook."""
        print(f"\nProcessing: {notebook_path.name}")

        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)

        cells_modified = 0
        blank_lines_added = 0

        for i, cell in enumerate(nb['cells']):
            if cell['cell_type'] != 'markdown' or not cell['source']:
                continue

            original = cell['source']
            formatted = self.formatter.format_source(original)

            if formatted != original:
                cell['source'] = formatted
                cells_modified += 1

                orig_blanks = sum(1 for line in original if not line.strip())
                new_blanks = sum(1 for line in formatted if not line.strip())
                added = new_blanks - orig_blanks
                blank_lines_added += added

                print(f"  Cell {i:2d}: +{added} blank lines")

        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)

        print(f"  Total: {cells_modified} cells modified, {blank_lines_added} blank lines added")
        return cells_modified, blank_lines_added


def main():
    parser = argparse.ArgumentParser(description='Fix markdown formatting in Jupyter notebooks')
    parser.add_argument('notebooks', nargs='+', help='Notebook file(s) to format')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')

    args = parser.parse_args()

    formatter = NotebookFormatter(debug=args.debug)

    print("="*80)
    print("NOTEBOOK MARKDOWN FORMATTING FIXER")
    print("="*80)

    total_cells = 0
    total_blanks = 0

    for notebook_file in args.notebooks:
        path = Path(notebook_file)
        if path.exists():
            cells, blanks = formatter.format_notebook(path)
            total_cells += cells
            total_blanks += blanks
        else:
            print(f"ERROR: File not found: {path}")

    print(f"\n{'='*80}")
    print(f"✅ SUMMARY")
    print(f"{'='*80}")
    print(f"Total notebooks processed: {len(args.notebooks)}")
    print(f"Total cells modified: {total_cells}")
    print(f"Total blank lines added: {total_blanks}")
    print(f"{'='*80}\n")


if __name__ == '__main__':
    main()
