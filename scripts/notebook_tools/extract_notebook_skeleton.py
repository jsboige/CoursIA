#!/usr/bin/env python3
"""
Extract notebook skeleton for README generation.

Extracts structure information from notebooks including:
- Title, sections, subsections
- Cell counts and types
- Code cell previews (first/last lines)
- Output summaries

Usage:
    python extract_notebook_skeleton.py [path] [options]

Arguments:
    path: Directory or notebook file to analyze

Options:
    --output: Output format (json, markdown, summary)
    --depth: Maximum heading depth to extract (default: 3)
    --code-preview: Include code cell previews
    --recursive: Scan subdirectories
    --exclude: Patterns to exclude (comma-separated)

Examples:
    python extract_notebook_skeleton.py MyIA.AI.Notebooks/Probas/Infer
    python extract_notebook_skeleton.py MyIA.AI.Notebooks/GameTheory --output markdown
    python extract_notebook_skeleton.py . --recursive --exclude archive,test
"""

import argparse
import json
import os
import re
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field, asdict


@dataclass
class CellInfo:
    """Information about a notebook cell."""
    cell_type: str
    index: int
    preview: str = ""
    line_count: int = 0
    has_output: bool = False
    output_type: Optional[str] = None


@dataclass
class SectionInfo:
    """Information about a markdown section."""
    level: int
    title: str
    cell_index: int


@dataclass
class NotebookSkeleton:
    """Complete skeleton of a notebook."""
    path: str
    name: str
    title: Optional[str] = None
    kernel: str = "unknown"
    total_cells: int = 0
    markdown_cells: int = 0
    code_cells: int = 0
    cells_with_output: int = 0
    sections: List[SectionInfo] = field(default_factory=list)
    code_previews: List[CellInfo] = field(default_factory=list)
    estimated_duration: Optional[int] = None  # minutes

    def to_dict(self) -> Dict:
        """Convert to dictionary for JSON serialization."""
        return {
            'path': self.path,
            'name': self.name,
            'title': self.title,
            'kernel': self.kernel,
            'total_cells': self.total_cells,
            'markdown_cells': self.markdown_cells,
            'code_cells': self.code_cells,
            'cells_with_output': self.cells_with_output,
            'sections': [{'level': s.level, 'title': s.title, 'cell_index': s.cell_index}
                        for s in self.sections],
            'code_previews': [asdict(c) for c in self.code_previews],
            'estimated_duration': self.estimated_duration
        }


def extract_cell_preview(source: str, max_lines: int = 3, max_chars: int = 150) -> str:
    """Extract a preview from cell source."""
    lines = source.split('\n')

    # Filter out magic commands and empty lines for preview
    preview_lines = []
    for line in lines:
        line_stripped = line.strip()
        if line_stripped and not line_stripped.startswith('#!') and not line_stripped.startswith('%'):
            preview_lines.append(line_stripped)
        if len(preview_lines) >= max_lines:
            break

    preview = ' '.join(preview_lines)[:max_chars]
    if len(preview) == max_chars:
        preview = preview.rsplit(' ', 1)[0] + '...'
    return preview


def detect_kernel(nb_data: Dict) -> str:
    """Detect the kernel type from notebook metadata."""
    kernel_spec = nb_data.get('metadata', {}).get('kernelspec', {})
    kernel_name = kernel_spec.get('name', '').lower()
    language = kernel_spec.get('language', '').lower()
    display_name = kernel_spec.get('display_name', '')

    if 'python' in kernel_name or language == 'python':
        if 'wsl' in display_name.lower():
            return 'Python (WSL)'
        return 'Python'
    elif '.net' in kernel_name or language in ['c#', 'csharp']:
        return '.NET C#'
    elif 'fsharp' in kernel_name or language == 'f#':
        return '.NET F#'
    elif 'lean' in kernel_name or language == 'lean4':
        return 'Lean 4'

    # Check cell contents for .NET magic commands
    for cell in nb_data.get('cells', []):
        if cell.get('cell_type') == 'code':
            source = ''.join(cell.get('source', []))
            if '#!import' in source or '#!csharp' in source:
                return '.NET C#'

    return display_name or 'Unknown'


def extract_sections(cells: List[Dict], max_depth: int = 3) -> List[SectionInfo]:
    """Extract section headers from markdown cells."""
    sections = []

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'markdown':
            continue

        source = ''.join(cell.get('source', []))

        # Find all headings in this cell
        for line in source.split('\n'):
            match = re.match(r'^(#{1,6})\s+(.+)$', line.strip())
            if match:
                level = len(match.group(1))
                if level <= max_depth:
                    title = match.group(2).strip()
                    # Remove markdown formatting from title
                    title = re.sub(r'\*\*([^*]+)\*\*', r'\1', title)
                    title = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', title)
                    sections.append(SectionInfo(level=level, title=title, cell_index=i))

    return sections


def estimate_duration(nb_data: Dict) -> int:
    """Estimate reading/execution time in minutes."""
    cells = nb_data.get('cells', [])

    # Rough estimates: 30 sec per markdown cell, 1 min per code cell
    markdown_count = sum(1 for c in cells if c.get('cell_type') == 'markdown')
    code_count = sum(1 for c in cells if c.get('cell_type') == 'code')

    return (markdown_count * 0.5 + code_count * 1.0).__ceil__()


def analyze_notebook(notebook_path: Path, include_code_preview: bool = True,
                     max_depth: int = 3) -> NotebookSkeleton:
    """Analyze a notebook and extract its skeleton."""
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb_data = json.load(f)
    except Exception as e:
        return NotebookSkeleton(
            path=str(notebook_path),
            name=notebook_path.stem,
            title=f"[Error: {e}]"
        )

    cells = nb_data.get('cells', [])

    # Extract title (first H1 heading)
    title = None
    for cell in cells:
        if cell.get('cell_type') == 'markdown':
            source = ''.join(cell.get('source', []))
            match = re.search(r'^#\s+(.+)$', source, re.MULTILINE)
            if match:
                title = match.group(1).strip()
                break

    # Count cells and outputs
    markdown_cells = sum(1 for c in cells if c.get('cell_type') == 'markdown')
    code_cells = sum(1 for c in cells if c.get('cell_type') == 'code')
    cells_with_output = sum(1 for c in cells
                           if c.get('cell_type') == 'code' and c.get('outputs'))

    # Extract code previews
    code_previews = []
    if include_code_preview:
        for i, cell in enumerate(cells):
            if cell.get('cell_type') != 'code':
                continue

            source = ''.join(cell.get('source', []))
            if not source.strip():
                continue

            outputs = cell.get('outputs', [])
            output_type = None
            if outputs:
                first_output = outputs[0]
                output_type = first_output.get('output_type')

            code_previews.append(CellInfo(
                cell_type='code',
                index=i,
                preview=extract_cell_preview(source),
                line_count=len(source.split('\n')),
                has_output=bool(outputs),
                output_type=output_type
            ))

    return NotebookSkeleton(
        path=str(notebook_path),
        name=notebook_path.stem,
        title=title,
        kernel=detect_kernel(nb_data),
        total_cells=len(cells),
        markdown_cells=markdown_cells,
        code_cells=code_cells,
        cells_with_output=cells_with_output,
        sections=extract_sections(cells, max_depth),
        code_previews=code_previews[:20],  # Limit previews
        estimated_duration=estimate_duration(nb_data)
    )


def discover_notebooks(base_path: Path, recursive: bool = True,
                       exclude_patterns: List[str] = None) -> List[Path]:
    """Discover notebooks in a directory."""
    exclude_patterns = exclude_patterns or []
    exclude_patterns.extend(['.ipynb_checkpoints', '_output', 'archive'])

    notebooks = []

    if base_path.is_file() and base_path.suffix == '.ipynb':
        return [base_path]

    pattern = '**/*.ipynb' if recursive else '*.ipynb'

    for nb_path in sorted(base_path.glob(pattern)):
        # Check exclusions
        path_str = str(nb_path).lower()
        if any(excl.lower() in path_str for excl in exclude_patterns):
            continue
        notebooks.append(nb_path)

    return notebooks


def format_markdown_table(skeletons: List[NotebookSkeleton], base_path: Path) -> str:
    """Format skeletons as markdown tables for README."""
    lines = []

    # Group by directory
    by_dir = {}
    for skel in skeletons:
        nb_path = Path(skel.path)
        try:
            rel_path = nb_path.relative_to(base_path)
            parent = str(rel_path.parent) if rel_path.parent != Path('.') else 'root'
        except ValueError:
            parent = 'other'

        if parent not in by_dir:
            by_dir[parent] = []
        by_dir[parent].append(skel)

    for directory, notebooks in sorted(by_dir.items()):
        if directory != 'root':
            lines.append(f"\n### {directory}\n")

        lines.append("| # | Notebook | Kernel | Cellules | Duree | Sections principales |")
        lines.append("|---|----------|--------|----------|-------|---------------------|")

        for i, nb in enumerate(notebooks, 1):
            # Extract notebook number if present
            num_match = re.search(r'-(\d+)-', nb.name)
            num = num_match.group(1) if num_match else str(i)

            # Format sections
            main_sections = [s.title for s in nb.sections if s.level == 2][:3]
            sections_str = ', '.join(main_sections) if main_sections else '-'
            if len(sections_str) > 50:
                sections_str = sections_str[:47] + '...'

            duration = f"~{nb.estimated_duration} min" if nb.estimated_duration else '-'

            lines.append(
                f"| {num} | [{nb.name}]({nb.name}.ipynb) | {nb.kernel} | "
                f"{nb.total_cells} | {duration} | {sections_str} |"
            )

    return '\n'.join(lines)


def format_detailed_markdown(skeletons: List[NotebookSkeleton], base_path: Path) -> str:
    """Format detailed skeleton information as markdown."""
    lines = []

    for skel in skeletons:
        lines.append(f"\n## {skel.name}")
        if skel.title:
            lines.append(f"\n**{skel.title}**\n")

        lines.append(f"- **Kernel**: {skel.kernel}")
        lines.append(f"- **Cellules**: {skel.total_cells} (MD: {skel.markdown_cells}, Code: {skel.code_cells})")
        lines.append(f"- **Sorties**: {skel.cells_with_output}/{skel.code_cells} cellules avec output")
        if skel.estimated_duration:
            lines.append(f"- **Duree estimee**: ~{skel.estimated_duration} min")

        if skel.sections:
            lines.append("\n### Structure\n")
            for sec in skel.sections:
                indent = '  ' * (sec.level - 1)
                lines.append(f"{indent}- {sec.title}")

        if skel.code_previews:
            lines.append("\n### Cellules de code (extraits)\n")
            lines.append("| # | Lignes | Output | Preview |")
            lines.append("|---|--------|--------|---------|")
            for cp in skel.code_previews[:10]:
                output_status = cp.output_type or '-' if cp.has_output else 'None'
                preview = cp.preview.replace('|', '\\|')
                lines.append(f"| {cp.index} | {cp.line_count} | {output_status} | {preview} |")

    return '\n'.join(lines)


def format_summary(skeletons: List[NotebookSkeleton]) -> str:
    """Format a brief summary."""
    total_cells = sum(s.total_cells for s in skeletons)
    total_code = sum(s.code_cells for s in skeletons)
    total_md = sum(s.markdown_cells for s in skeletons)
    total_duration = sum(s.estimated_duration or 0 for s in skeletons)

    lines = [
        f"Notebooks: {len(skeletons)}",
        f"Cellules totales: {total_cells} (MD: {total_md}, Code: {total_code})",
        f"Duree estimee: ~{total_duration} min ({total_duration//60}h{total_duration%60:02d})",
        "",
        "Notebooks:"
    ]

    for skel in skeletons:
        sections_count = len([s for s in skel.sections if s.level == 2])
        lines.append(f"  - {skel.name}: {skel.total_cells} cells, {sections_count} sections")

    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(
        description='Extract notebook skeleton for README generation',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('path', nargs='?', default='.',
                        help='Directory or notebook to analyze')
    parser.add_argument('--output', '-o', choices=['json', 'markdown', 'detailed', 'summary'],
                        default='summary', help='Output format')
    parser.add_argument('--depth', '-d', type=int, default=3,
                        help='Maximum heading depth to extract')
    parser.add_argument('--code-preview', action='store_true',
                        help='Include code cell previews')
    parser.add_argument('--recursive', '-r', action='store_true',
                        help='Scan subdirectories')
    parser.add_argument('--exclude', '-e', type=str,
                        help='Patterns to exclude (comma-separated)')

    args = parser.parse_args()

    base_path = Path(args.path)
    if not base_path.exists():
        print(f"Error: Path not found: {base_path}")
        return 1

    exclude_patterns = args.exclude.split(',') if args.exclude else []

    # Discover and analyze notebooks
    notebooks = discover_notebooks(base_path, args.recursive, exclude_patterns)

    if not notebooks:
        print(f"No notebooks found in: {base_path}")
        return 1

    print(f"Analyzing {len(notebooks)} notebook(s)...", file=__import__('sys').stderr)

    skeletons = []
    for nb_path in notebooks:
        skel = analyze_notebook(nb_path, args.code_preview, args.depth)
        skeletons.append(skel)

    # Output
    if args.output == 'json':
        output = json.dumps([s.to_dict() for s in skeletons], indent=2, ensure_ascii=False)
    elif args.output == 'markdown':
        output = format_markdown_table(skeletons, base_path)
    elif args.output == 'detailed':
        output = format_detailed_markdown(skeletons, base_path)
    else:
        output = format_summary(skeletons)

    print(output)
    return 0


if __name__ == '__main__':
    import sys
    sys.exit(main())
