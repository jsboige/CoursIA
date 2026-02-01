#!/usr/bin/env python3
"""
Consolidated Notebook Tools for CoursIA

A comprehensive utility module for working with Jupyter notebooks across the repository.
Provides tools for validation, execution, skeleton extraction, and content analysis.

Usage as module:
    from notebook_tools import NotebookAnalyzer, NotebookValidator, NotebookExecutor

Usage as CLI:
    python notebook_tools.py validate [target] [--quick] [--verbose]
    python notebook_tools.py skeleton [path] [--output json|markdown|summary]
    python notebook_tools.py analyze [path] [--verbose]
    python notebook_tools.py check-env [family]
    python notebook_tools.py execute [target] [--cell-by-cell] [--timeout N]

Examples:
    python notebook_tools.py validate GameTheory --quick
    python notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown
    python notebook_tools.py analyze MyIA.AI.Notebooks/SymbolicAI/Tweety
    python notebook_tools.py check-env Lean
    python notebook_tools.py execute GameTheory --timeout 120 --verbose
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Union


# =============================================================================
# CONFIGURATION
# =============================================================================

# Notebook families configuration
NOTEBOOK_FAMILIES = {
    "Sudoku": {
        "path": "MyIA.AI.Notebooks/Sudoku",
        "kernel": "dotnet",
        "notes": "Uses #!import, requires cell-by-cell execution",
        "expected_notebooks": ["Sudoku-{}-*.ipynb".format(i) for i in range(10)]
    },
    "Search": {
        "path": "MyIA.AI.Notebooks/Search",
        "kernel": "mixed",
        "python": ["CSPs_Intro.ipynb", "Exploration_non_informee*.ipynb", "PyGad-*.ipynb"],
        "dotnet": ["GeneticSharp-*.ipynb", "Portfolio_*.ipynb"]
    },
    "SymbolicAI": {
        "path": "MyIA.AI.Notebooks/SymbolicAI",
        "kernel": "mixed",
        "exclude_subdirs": ["Argument_Analysis", "Lean", "Tweety"]
    },
    "Tweety": {
        "path": "MyIA.AI.Notebooks/SymbolicAI/Tweety",
        "kernel": "python",
        "notes": "Requires JDK 17+ (auto-download), JPype",
        "expected_notebooks": [f"Tweety-{i}-*.ipynb" for i in range(1, 10)]
    },
    "Lean": {
        "path": "MyIA.AI.Notebooks/SymbolicAI/Lean",
        "kernel": "lean4",
        "notes": "Requires lean4_jupyter kernel and elan",
        "expected_notebooks": [f"Lean-{i}-*.ipynb" for i in range(1, 10)]
    },
    "Argument_Analysis": {
        "path": "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis",
        "kernel": "python",
        "requires_env": True,
        "batch_mode": True
    },
    "GenAI": {
        "path": "MyIA.AI.Notebooks/GenAI",
        "kernel": "python",
        "requires_env": True,
        "notes": "Some notebooks require GPU"
    },
    "ML": {
        "path": "MyIA.AI.Notebooks/ML",
        "kernel": "dotnet"
    },
    "Probas": {
        "path": "MyIA.AI.Notebooks/Probas",
        "kernel": "dotnet",
        "subdir": "Infer"
    },
    "Infer": {
        "path": "MyIA.AI.Notebooks/Probas/Infer",
        "kernel": "dotnet",
        "expected_notebooks": [f"Infer-{i}-*.ipynb" for i in range(1, 21)]
    },
    "IIT": {
        "path": "MyIA.AI.Notebooks/IIT",
        "kernel": "python"
    },
    "EPF": {
        "path": "MyIA.AI.Notebooks/EPF",
        "kernel": "mixed"
    },
    "GameTheory": {
        "path": "MyIA.AI.Notebooks/GameTheory",
        "kernel": "python",
        "notes": "Uses nashpy, some notebooks have Lean proofs",
        "expected_notebooks": [f"GameTheory-{i}-*.ipynb" for i in range(1, 20)]
    }
}

# Notebooks to skip (interactive, broken, etc.)
SKIP_PATTERNS = [
    "UI_configuration.ipynb",
    "*_output.ipynb",
    "*_verified.ipynb",
    ".ipynb_checkpoints",
]


# =============================================================================
# ANSI COLORS
# =============================================================================

class Colors:
    """ANSI color codes for terminal output"""
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    MAGENTA = '\033[95m'
    BOLD = '\033[1m'
    END = '\033[0m'

    @classmethod
    def disable(cls):
        """Disable colors for non-terminal output"""
        cls.GREEN = cls.RED = cls.YELLOW = cls.BLUE = ''
        cls.CYAN = cls.MAGENTA = cls.BOLD = cls.END = ''


def print_ok(msg: str):
    print(f"{Colors.GREEN}[OK]{Colors.END} {msg}")


def print_error(msg: str):
    print(f"{Colors.RED}[X]{Colors.END} {msg}")


def print_warning(msg: str):
    print(f"{Colors.YELLOW}[!]{Colors.END} {msg}")


def print_info(msg: str):
    print(f"{Colors.CYAN}[i]{Colors.END} {msg}")


def print_section(title: str):
    print(f"\n{Colors.BOLD}{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.BLUE}{title:^60}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.BLUE}{'='*60}{Colors.END}\n")


# =============================================================================
# DATA CLASSES
# =============================================================================

@dataclass
class CellInfo:
    """Information about a notebook cell"""
    index: int
    cell_type: str
    preview: str = ""
    line_count: int = 0
    has_output: bool = False
    output_type: Optional[str] = None
    cell_id: Optional[str] = None


@dataclass
class SectionInfo:
    """Information about a markdown section"""
    level: int
    title: str
    cell_index: int


@dataclass
class ValidationIssue:
    """Issue found during validation"""
    issue_type: str  # 'error', 'warning', 'info'
    category: str    # 'structure', 'markdown', 'code', 'latex', etc.
    cell_index: int
    message: str


@dataclass
class NotebookSkeleton:
    """Complete skeleton of a notebook"""
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
    estimated_duration: Optional[int] = None

    def to_dict(self) -> Dict:
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


@dataclass
class NotebookValidation:
    """Result of notebook validation"""
    path: str
    name: str
    exists: bool = False
    valid_json: bool = False
    has_cells: bool = False
    has_metadata: bool = False
    kernel: str = "unknown"
    kernel_correct: bool = False
    markdown_cells: int = 0
    code_cells: int = 0
    total_cells: int = 0
    cells_with_output: int = 0
    cells_with_errors: int = 0
    issues: List[ValidationIssue] = field(default_factory=list)
    execution_time: float = 0.0

    @property
    def status(self) -> str:
        errors = [i for i in self.issues if i.issue_type == 'error']
        if not self.exists:
            return "MISSING"
        if not self.valid_json:
            return "INVALID"
        if errors:
            return "ERROR"
        if [i for i in self.issues if i.issue_type == 'warning']:
            return "WARNING"
        return "OK"

    @property
    def error_count(self) -> int:
        return len([i for i in self.issues if i.issue_type == 'error'])

    @property
    def warning_count(self) -> int:
        return len([i for i in self.issues if i.issue_type == 'warning'])


@dataclass
class EnvironmentCheck:
    """Result of environment check"""
    family: str
    ready: bool = False
    components: Dict[str, bool] = field(default_factory=dict)
    versions: Dict[str, str] = field(default_factory=dict)
    errors: List[str] = field(default_factory=list)


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def get_repo_root() -> Path:
    """Get the repository root directory"""
    # Try to find by looking for known markers
    current = Path(__file__).parent
    for _ in range(5):
        if (current / "CLAUDE.md").exists() or (current / "MyIA.AI.Notebooks").exists():
            return current
        current = current.parent
    return Path(__file__).parent.parent


def should_skip(path: Path) -> bool:
    """Check if a path should be skipped"""
    path_str = str(path)
    for pattern in SKIP_PATTERNS:
        if '*' in pattern:
            if pattern.replace('*', '') in path_str:
                return True
        else:
            if pattern in path_str:
                return True
    return False


def detect_kernel(nb_data: Dict) -> str:
    """Detect the kernel type from notebook metadata"""
    kernel_spec = nb_data.get('metadata', {}).get('kernelspec', {})
    kernel_name = kernel_spec.get('name', '').lower()
    language = kernel_spec.get('language', '').lower()
    display_name = kernel_spec.get('display_name', '')

    if 'python' in kernel_name or language == 'python':
        if 'wsl' in display_name.lower():
            return 'Python (WSL)'
        if 'gametheory' in display_name.lower():
            return 'Python (GameTheory WSL)'
        return 'Python'
    elif '.net' in kernel_name or language in ['c#', 'csharp']:
        return '.NET C#'
    elif 'fsharp' in kernel_name or language == 'f#':
        return '.NET F#'
    elif 'lean' in kernel_name or language == 'lean4':
        if 'wsl' in display_name.lower():
            return 'Lean 4 (WSL)'
        return 'Lean 4'

    # Check cell contents for .NET magic commands
    for cell in nb_data.get('cells', []):
        if cell.get('cell_type') == 'code':
            source = ''.join(cell.get('source', []))
            if '#!import' in source or '#!csharp' in source:
                return '.NET C#'

    return display_name or 'Unknown'


def extract_cell_preview(source: str, max_lines: int = 3, max_chars: int = 150) -> str:
    """Extract a preview from cell source"""
    lines = source.split('\n')

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


# =============================================================================
# NOTEBOOK ANALYZER
# =============================================================================

class NotebookAnalyzer:
    """Analyze notebook structure and content"""

    def __init__(self, notebook_path: Union[str, Path]):
        self.path = Path(notebook_path)
        self.nb_data: Optional[Dict] = None
        self._load()

    def _load(self):
        """Load notebook JSON"""
        if not self.path.exists():
            return

        try:
            with open(self.path, 'r', encoding='utf-8') as f:
                self.nb_data = json.load(f)
        except (json.JSONDecodeError, Exception):
            self.nb_data = None

    @property
    def is_valid(self) -> bool:
        return self.nb_data is not None

    @property
    def cells(self) -> List[Dict]:
        return self.nb_data.get('cells', []) if self.nb_data else []

    @property
    def kernel(self) -> str:
        return detect_kernel(self.nb_data) if self.nb_data else 'unknown'

    def get_skeleton(self, include_code_preview: bool = True, max_depth: int = 3) -> NotebookSkeleton:
        """Extract complete skeleton of the notebook"""
        if not self.nb_data:
            return NotebookSkeleton(
                path=str(self.path),
                name=self.path.stem,
                title="[Error: Could not load notebook]"
            )

        cells = self.cells

        # Extract title
        title = None
        for cell in cells:
            if cell.get('cell_type') == 'markdown':
                source = ''.join(cell.get('source', []))
                match = re.search(r'^#\s+(.+)$', source, re.MULTILINE)
                if match:
                    title = match.group(1).strip()
                    break

        # Count cells
        markdown_cells = sum(1 for c in cells if c.get('cell_type') == 'markdown')
        code_cells = sum(1 for c in cells if c.get('cell_type') == 'code')
        cells_with_output = sum(1 for c in cells
                               if c.get('cell_type') == 'code' and c.get('outputs'))

        # Extract sections
        sections = self._extract_sections(max_depth)

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
                    output_type = outputs[0].get('output_type')

                code_previews.append(CellInfo(
                    index=i,
                    cell_type='code',
                    preview=extract_cell_preview(source),
                    line_count=len(source.split('\n')),
                    has_output=bool(outputs),
                    output_type=output_type,
                    cell_id=cell.get('id')
                ))

        # Estimate duration
        estimated_duration = (markdown_cells * 0.5 + code_cells * 1.0).__ceil__()

        return NotebookSkeleton(
            path=str(self.path),
            name=self.path.stem,
            title=title,
            kernel=self.kernel,
            total_cells=len(cells),
            markdown_cells=markdown_cells,
            code_cells=code_cells,
            cells_with_output=cells_with_output,
            sections=sections,
            code_previews=code_previews[:20],
            estimated_duration=estimated_duration
        )

    def _extract_sections(self, max_depth: int = 3) -> List[SectionInfo]:
        """Extract section headers from markdown cells"""
        sections = []

        for i, cell in enumerate(self.cells):
            if cell.get('cell_type') != 'markdown':
                continue

            source = ''.join(cell.get('source', []))

            for line in source.split('\n'):
                match = re.match(r'^(#{1,6})\s+(.+)$', line.strip())
                if match:
                    level = len(match.group(1))
                    if level <= max_depth:
                        title = match.group(2).strip()
                        title = re.sub(r'\*\*([^*]+)\*\*', r'\1', title)
                        title = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', title)
                        sections.append(SectionInfo(level=level, title=title, cell_index=i))

        return sections

    def get_cell_outputs_analysis(self) -> Dict[str, Any]:
        """Analyze outputs of all cells"""
        results = {
            'total_cells': len(self.cells),
            'code_cells': 0,
            'cells_with_output': 0,
            'cells_with_errors': 0,
            'cells_without_output': 0,
            'errors': [],
            'cells': []
        }

        for i, cell in enumerate(self.cells):
            if cell.get('cell_type') != 'code':
                continue

            results['code_cells'] += 1
            source = ''.join(cell.get('source', []))
            outputs = cell.get('outputs', [])

            cell_info = {
                'index': i,
                'has_output': bool(outputs),
                'status': 'OK',
                'first_line': source.split('\n')[0][:60] if source else '(empty)',
            }

            if not outputs:
                results['cells_without_output'] += 1
                cell_info['status'] = 'NOT_EXECUTED' if source.strip() else 'EMPTY'
            else:
                results['cells_with_output'] += 1
                for output in outputs:
                    if output.get('output_type') == 'error':
                        results['cells_with_errors'] += 1
                        cell_info['status'] = 'ERROR'
                        results['errors'].append({
                            'cell_index': i,
                            'ename': output.get('ename', 'Error'),
                            'evalue': output.get('evalue', ''),
                        })
                        break

            results['cells'].append(cell_info)

        return results


# =============================================================================
# NOTEBOOK VALIDATOR
# =============================================================================

class NotebookValidator:
    """Validate notebook structure and content"""

    def __init__(self, notebook_path: Union[str, Path]):
        self.path = Path(notebook_path)
        self.analyzer = NotebookAnalyzer(notebook_path)

    def validate_structure(self) -> NotebookValidation:
        """Validate basic notebook structure"""
        validation = NotebookValidation(
            path=str(self.path),
            name=self.path.name
        )

        if not self.path.exists():
            return validation

        validation.exists = True

        if not self.analyzer.is_valid:
            validation.issues.append(ValidationIssue(
                issue_type='error',
                category='structure',
                cell_index=0,
                message='Invalid JSON format'
            ))
            return validation

        validation.valid_json = True
        nb = self.analyzer.nb_data

        # Check cells
        cells = nb.get('cells', [])
        if cells:
            validation.has_cells = True
            validation.total_cells = len(cells)

            for i, cell in enumerate(cells):
                cell_type = cell.get('cell_type', '')
                if cell_type == 'markdown':
                    validation.markdown_cells += 1
                elif cell_type == 'code':
                    validation.code_cells += 1
                    if cell.get('outputs'):
                        validation.cells_with_output += 1
                    for output in cell.get('outputs', []):
                        if output.get('output_type') == 'error':
                            validation.cells_with_errors += 1
                            break
        else:
            validation.issues.append(ValidationIssue(
                issue_type='error',
                category='structure',
                cell_index=0,
                message='No cells found in notebook'
            ))

        # Check metadata
        metadata = nb.get('metadata', {})
        if metadata:
            validation.has_metadata = True
            validation.kernel = self.analyzer.kernel
        else:
            validation.issues.append(ValidationIssue(
                issue_type='warning',
                category='structure',
                cell_index=0,
                message='No metadata found'
            ))

        return validation

    def validate_content(self, strict: bool = False) -> List[ValidationIssue]:
        """Validate markdown and code content quality"""
        issues = []

        if not self.analyzer.is_valid:
            return issues

        for i, cell in enumerate(self.analyzer.cells):
            cell_type = cell.get('cell_type', '')

            if cell_type == 'markdown':
                issues.extend(self._validate_markdown_cell(cell, i))
            elif cell_type == 'code':
                issues.extend(self._validate_code_cell(cell, i))

        # Check pedagogical flow
        issues.extend(self._validate_pedagogical_flow())

        return issues

    def _validate_markdown_cell(self, cell: Dict, index: int) -> List[ValidationIssue]:
        """Validate a markdown cell"""
        issues = []
        source = ''.join(cell.get('source', []))

        if not source.strip():
            issues.append(ValidationIssue(
                issue_type='warning',
                category='markdown',
                cell_index=index,
                message='Empty markdown cell'
            ))
            return issues

        # Check heading structure
        headings = re.findall(r'^(#{1,6})\s+(.+)$', source, re.MULTILINE)
        if headings:
            levels = [len(h[0]) for h in headings]
            for i in range(1, len(levels)):
                if levels[i] > levels[i-1] + 1:
                    issues.append(ValidationIssue(
                        issue_type='warning',
                        category='structure',
                        cell_index=index,
                        message=f'Heading level jump: {levels[i-1]} to {levels[i]}'
                    ))

        # Check LaTeX
        single_dollars = len(re.findall(r'(?<!\$)\$(?!\$)', source))
        if single_dollars % 2 != 0:
            issues.append(ValidationIssue(
                issue_type='error',
                category='latex',
                cell_index=index,
                message='Unbalanced $ signs in LaTeX'
            ))

        double_dollars = len(re.findall(r'\$\$', source))
        if double_dollars % 2 != 0:
            issues.append(ValidationIssue(
                issue_type='error',
                category='latex',
                cell_index=index,
                message='Unbalanced $$ signs in LaTeX'
            ))

        # Check links
        links = re.findall(r'\[([^\]]*)\]\(([^)]*)\)', source)
        for text, url in links:
            if not url or url.isspace():
                issues.append(ValidationIssue(
                    issue_type='warning',
                    category='links',
                    cell_index=index,
                    message=f'Empty URL for link: [{text}]'
                ))

        return issues

    def _validate_code_cell(self, cell: Dict, index: int) -> List[ValidationIssue]:
        """Validate a code cell"""
        issues = []
        source = ''.join(cell.get('source', []))
        outputs = cell.get('outputs', [])

        if not source.strip():
            return issues

        # Check for errors in outputs
        for output in outputs:
            if output.get('output_type') == 'error':
                ename = output.get('ename', 'Unknown')
                evalue = output.get('evalue', '')
                issues.append(ValidationIssue(
                    issue_type='error',
                    category='execution',
                    cell_index=index,
                    message=f'{ename}: {evalue[:100]}'
                ))

        return issues

    def _validate_pedagogical_flow(self) -> List[ValidationIssue]:
        """Validate pedagogical flow"""
        issues = []
        cells = self.analyzer.cells

        markdown_cells = [c for c in cells if c.get('cell_type') == 'markdown']
        code_cells = [c for c in cells if c.get('cell_type') == 'code']

        if not markdown_cells:
            issues.append(ValidationIssue(
                issue_type='warning',
                category='pedagogy',
                cell_index=0,
                message='Notebook has no markdown explanations'
            ))
            return issues

        # Check for title
        first_md = ''.join(markdown_cells[0].get('source', []))
        if not first_md.strip().startswith('#'):
            issues.append(ValidationIssue(
                issue_type='info',
                category='pedagogy',
                cell_index=0,
                message='Notebook should start with a title (# heading)'
            ))

        # Check code-to-markdown ratio
        if code_cells and markdown_cells:
            ratio = len(markdown_cells) / len(code_cells)
            if ratio < 0.3:
                issues.append(ValidationIssue(
                    issue_type='warning',
                    category='pedagogy',
                    cell_index=0,
                    message=f'Low explanation ratio ({ratio:.2f}). Consider adding more explanatory text.'
                ))

        # Check for consecutive code cells without markdown
        prev_was_code = False
        consecutive_count = 0
        for i, cell in enumerate(cells):
            if cell.get('cell_type') == 'code':
                if prev_was_code:
                    consecutive_count += 1
                    if consecutive_count >= 3:
                        issues.append(ValidationIssue(
                            issue_type='info',
                            category='pedagogy',
                            cell_index=i,
                            message=f'{consecutive_count + 1} consecutive code cells without explanation'
                        ))
                prev_was_code = True
            else:
                prev_was_code = False
                consecutive_count = 0

        return issues


# =============================================================================
# ENVIRONMENT CHECKER
# =============================================================================

class EnvironmentChecker:
    """Check environment for specific notebook families"""

    def __init__(self, family: str):
        self.family = family
        self.config = NOTEBOOK_FAMILIES.get(family, {})

    def check_command(self, cmd: str, name: str, version_flag: str = "--version") -> Tuple[bool, str]:
        """Check if a command is available"""
        import platform

        # On Linux/WSL, source .elan/env for Lean tools
        if platform.system() == "Linux" and cmd in ["elan", "lean", "lake", "repl"]:
            try:
                bash_cmd = f"source ~/.elan/env 2>/dev/null && {cmd} {version_flag}"
                result = subprocess.run(
                    ["bash", "-c", bash_cmd],
                    capture_output=True, text=True, timeout=10
                )
                if result.returncode == 0:
                    version = result.stdout.strip().split('\n')[0]
                    return True, version
            except Exception:
                pass

        path = shutil.which(cmd)
        if path:
            try:
                result = subprocess.run(
                    [cmd, version_flag],
                    capture_output=True, text=True, timeout=5
                )
                version = result.stdout.strip().split('\n')[0]
                return True, version
            except Exception:
                return True, "unknown"
        return False, ""

    def check_python_package(self, pkg_name: str, import_name: str = None) -> Tuple[bool, str]:
        """Check if a Python package is installed"""
        if import_name is None:
            import_name = pkg_name.replace("-", "_")

        try:
            mod = __import__(import_name)
            version = getattr(mod, "__version__", "unknown")
            return True, version
        except ImportError:
            return False, ""

    def check_jupyter_kernel(self, kernel_name: str) -> bool:
        """Check if a Jupyter kernel is registered"""
        try:
            result = subprocess.run(
                ["jupyter", "kernelspec", "list"],
                capture_output=True, text=True, timeout=10
            )
            return kernel_name.lower() in result.stdout.lower()
        except Exception:
            return False

    def check(self) -> EnvironmentCheck:
        """Run environment check for the family"""
        env = EnvironmentCheck(family=self.family)

        kernel_type = self.config.get('kernel', 'python')

        # Common checks
        python_ok, python_ver = self.check_command("python", "Python")
        env.components['python'] = python_ok
        if python_ok:
            env.versions['python'] = python_ver

        if kernel_type == 'python':
            env.components['python3_kernel'] = self.check_jupyter_kernel('python3')

        elif kernel_type == 'dotnet':
            dotnet_ok, dotnet_ver = self.check_command("dotnet", ".NET")
            env.components['dotnet'] = dotnet_ok
            if dotnet_ok:
                env.versions['dotnet'] = dotnet_ver
            env.components['dotnet_kernel'] = self.check_jupyter_kernel('.net-csharp')

        elif kernel_type == 'lean4':
            elan_ok, elan_ver = self.check_command("elan", "elan")
            lean_ok, lean_ver = self.check_command("lean", "Lean")
            env.components['elan'] = elan_ok
            env.components['lean'] = lean_ok
            if elan_ok:
                env.versions['elan'] = elan_ver
            if lean_ok:
                env.versions['lean'] = lean_ver
            env.components['lean4_kernel'] = self.check_jupyter_kernel('lean4')

            # Check lean4_jupyter package
            pkg_ok, pkg_ver = self.check_python_package("lean4-jupyter", "lean4_jupyter")
            env.components['lean4_jupyter'] = pkg_ok

        # Family-specific checks
        if self.family == 'Tweety':
            jpype_ok, jpype_ver = self.check_python_package("jpype1", "jpype")
            env.components['jpype'] = jpype_ok
            if jpype_ok:
                env.versions['jpype'] = jpype_ver

            # Check for JDK
            java_home = os.environ.get("JAVA_HOME", "")
            if java_home and Path(java_home).exists():
                env.components['jdk'] = True
                env.versions['jdk'] = "system"
            else:
                env.components['jdk'] = False
                env.errors.append("JAVA_HOME not set or JDK not found")

        elif self.family == 'GameTheory':
            nashpy_ok, nashpy_ver = self.check_python_package("nashpy")
            numpy_ok, numpy_ver = self.check_python_package("numpy")
            env.components['nashpy'] = nashpy_ok
            env.components['numpy'] = numpy_ok
            if nashpy_ok:
                env.versions['nashpy'] = nashpy_ver

        elif self.family in ['GenAI', 'Argument_Analysis']:
            openai_ok, _ = self.check_python_package("openai")
            env.components['openai'] = openai_ok

        # Determine overall readiness
        required = [v for k, v in env.components.items() if not k.endswith('_optional')]
        env.ready = all(required) if required else True

        return env


# =============================================================================
# NOTEBOOK EXECUTOR
# =============================================================================

@dataclass
class CellExecutionResult:
    """Result of executing a single cell"""
    index: int
    cell_type: str
    success: bool
    execution_time: float = 0.0
    output: str = ""
    error: Optional[str] = None


@dataclass
class NotebookExecutionResult:
    """Result of notebook execution"""
    path: str
    success: bool
    kernel: str
    total_cells: int = 0
    executed_cells: int = 0
    success_cells: int = 0
    error_cells: int = 0
    execution_time: float = 0.0
    message: str = ""
    cell_results: List[CellExecutionResult] = field(default_factory=list)


class NotebookExecutor:
    """Execute notebooks using Papermill or cell-by-cell"""

    def __init__(self, notebook_path: Union[str, Path]):
        self.path = Path(notebook_path)
        self.analyzer = NotebookAnalyzer(notebook_path)

    def detect_kernel_name(self) -> str:
        """Detect the appropriate kernel name for execution"""
        kernel = self.analyzer.kernel.lower()

        if 'python' in kernel:
            return 'python3'
        elif '.net' in kernel or 'csharp' in kernel:
            return '.net-csharp'
        elif 'fsharp' in kernel:
            return '.net-fsharp'
        elif 'lean' in kernel:
            return 'lean4'
        else:
            return 'python3'  # Default

    def execute_with_papermill(self, timeout: int = 300,
                                output_path: Optional[Path] = None,
                                batch_mode: bool = False) -> NotebookExecutionResult:
        """
        Execute notebook using Papermill.
        Returns NotebookExecutionResult with success/failure info.
        """
        kernel = self.detect_kernel_name()
        start_time = time.time()

        if output_path is None:
            output_path = self.path.parent / f"{self.path.stem}_output.ipynb"

        cmd = [
            sys.executable, "-m", "papermill",
            str(self.path),
            str(output_path),
            "--kernel", kernel,
            "--cwd", str(self.path.parent)
        ]

        if batch_mode:
            cmd.extend(["-p", "BATCH_MODE", "true"])

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout
            )

            execution_time = time.time() - start_time

            if result.returncode == 0:
                return NotebookExecutionResult(
                    path=str(self.path),
                    success=True,
                    kernel=kernel,
                    execution_time=execution_time,
                    message=f"SUCCESS (kernel={kernel})"
                )
            else:
                error_msg = result.stderr[-500:] if result.stderr else "Unknown error"
                return NotebookExecutionResult(
                    path=str(self.path),
                    success=False,
                    kernel=kernel,
                    execution_time=execution_time,
                    message=f"FAILED: {error_msg}"
                )

        except subprocess.TimeoutExpired:
            return NotebookExecutionResult(
                path=str(self.path),
                success=False,
                kernel=kernel,
                execution_time=timeout,
                message=f"TIMEOUT ({timeout}s)"
            )
        except Exception as e:
            return NotebookExecutionResult(
                path=str(self.path),
                success=False,
                kernel=kernel,
                execution_time=time.time() - start_time,
                message=f"ERROR: {e}"
            )

    def execute_cell_by_cell(self, timeout: int = 60,
                              verbose: bool = False) -> NotebookExecutionResult:
        """
        Execute notebook cell by cell using jupyter_client.
        Better for .NET notebooks with #!import or Lean notebooks.
        """
        try:
            import jupyter_client
        except ImportError:
            return NotebookExecutionResult(
                path=str(self.path),
                success=False,
                kernel="unknown",
                message="jupyter_client not installed: pip install jupyter_client"
            )

        if not self.analyzer.is_valid:
            return NotebookExecutionResult(
                path=str(self.path),
                success=False,
                kernel="unknown",
                message="Could not load notebook"
            )

        kernel_name = self.detect_kernel_name()
        cells = self.analyzer.cells
        cell_results = []
        start_time = time.time()

        # Start kernel
        try:
            km = jupyter_client.KernelManager(kernel_name=kernel_name)
            km.start_kernel(cwd=str(self.path.parent))
            kc = km.client()
            kc.start_channels()
            kc.wait_for_ready(timeout=60)
        except Exception as e:
            return NotebookExecutionResult(
                path=str(self.path),
                success=False,
                kernel=kernel_name,
                message=f"Failed to start {kernel_name} kernel: {e}"
            )

        try:
            # Set working directory for Python kernels
            if 'python' in kernel_name:
                wd_code = f"import os; os.chdir(r'{self.path.parent}')"
                kc.execute(wd_code)
                while True:
                    try:
                        msg = kc.get_iopub_msg(timeout=5)
                        if msg['msg_type'] == 'status' and msg['content']['execution_state'] == 'idle':
                            break
                    except:
                        break

            success_count = 0
            error_count = 0

            for i, cell in enumerate(cells):
                cell_type = cell.get('cell_type', 'unknown')
                source = ''.join(cell.get('source', []))

                if cell_type != 'code' or not source.strip():
                    cell_results.append(CellExecutionResult(
                        index=i,
                        cell_type=cell_type,
                        success=True,
                        output='skipped'
                    ))
                    continue

                cell_start = time.time()
                if verbose:
                    print(f"  Cell {i}: ", end="", flush=True)

                try:
                    msg_id = kc.execute(source)
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
                                errors.append(f"{content.get('ename', 'Error')}: {content.get('evalue', '')}")
                            elif msg_type == 'status' and content.get('execution_state') == 'idle':
                                break
                        except Exception as e:
                            if 'timeout' in str(e).lower():
                                errors.append(f"Timeout after {timeout}s")
                            break

                    output_text = '\n'.join(outputs)[:500]
                    error_text = '\n'.join(errors) if errors else None
                    cell_success = len(errors) == 0

                    cell_results.append(CellExecutionResult(
                        index=i,
                        cell_type=cell_type,
                        success=cell_success,
                        execution_time=time.time() - cell_start,
                        output=output_text,
                        error=error_text
                    ))

                    if cell_success:
                        success_count += 1
                        if verbose:
                            print("OK")
                    else:
                        error_count += 1
                        if verbose:
                            print(f"FAILED: {error_text[:80] if error_text else 'unknown'}")

                except Exception as e:
                    cell_results.append(CellExecutionResult(
                        index=i,
                        cell_type=cell_type,
                        success=False,
                        execution_time=time.time() - cell_start,
                        error=str(e)
                    ))
                    error_count += 1
                    if verbose:
                        print(f"ERROR: {e}")

            total_time = time.time() - start_time
            executed = sum(1 for r in cell_results if r.output != 'skipped')

            return NotebookExecutionResult(
                path=str(self.path),
                success=error_count == 0,
                kernel=kernel_name,
                total_cells=len(cells),
                executed_cells=executed,
                success_cells=success_count,
                error_cells=error_count,
                execution_time=total_time,
                message=f"Executed {executed} cells: {success_count} OK, {error_count} errors",
                cell_results=cell_results
            )

        finally:
            try:
                kc.stop_channels()
                km.shutdown_kernel(now=True)
            except:
                pass


# =============================================================================
# NOTEBOOK DISCOVERER
# =============================================================================

def discover_notebooks(target: str, repo_root: Path = None,
                       python_only: bool = False, dotnet_only: bool = False,
                       recursive: bool = True) -> List[Path]:
    """Discover notebooks based on target specification"""
    if repo_root is None:
        repo_root = get_repo_root()

    notebooks = []

    if target.endswith('.ipynb'):
        path = Path(target) if Path(target).is_absolute() else repo_root / target
        if path.exists():
            notebooks.append(path)
    elif target.lower() == 'all':
        for family_name, config in NOTEBOOK_FAMILIES.items():
            family_path = repo_root / config['path']
            if family_path.exists():
                for nb in family_path.rglob('*.ipynb') if recursive else family_path.glob('*.ipynb'):
                    if not should_skip(nb):
                        notebooks.append(nb)
    elif target in NOTEBOOK_FAMILIES:
        config = NOTEBOOK_FAMILIES[target]
        family_path = repo_root / config['path']
        if family_path.exists():
            for nb in family_path.rglob('*.ipynb') if recursive else family_path.glob('*.ipynb'):
                if not should_skip(nb):
                    exclude = config.get('exclude_subdirs', [])
                    if not any(ex in str(nb) for ex in exclude):
                        notebooks.append(nb)
    else:
        # Try as a path
        path = Path(target) if Path(target).is_absolute() else repo_root / target
        if path.exists():
            if path.is_file():
                notebooks.append(path)
            else:
                for nb in path.rglob('*.ipynb') if recursive else path.glob('*.ipynb'):
                    if not should_skip(nb):
                        notebooks.append(nb)

    # Filter by kernel type
    if python_only or dotnet_only:
        filtered = []
        for nb in notebooks:
            analyzer = NotebookAnalyzer(nb)
            kernel = analyzer.kernel.lower()
            if python_only and 'python' in kernel:
                filtered.append(nb)
            elif dotnet_only and ('.net' in kernel or 'dotnet' in kernel):
                filtered.append(nb)
        notebooks = filtered

    return sorted(set(notebooks))


# =============================================================================
# CLI COMMANDS
# =============================================================================

def cmd_validate(args):
    """Validate notebooks"""
    repo_root = get_repo_root()
    notebooks = discover_notebooks(
        args.target, repo_root,
        python_only=args.python_only,
        dotnet_only=args.dotnet_only
    )

    if not notebooks:
        print_error(f"No notebooks found for target: {args.target}")
        return 1

    print_info(f"Found {len(notebooks)} notebook(s) to validate")

    results = []
    for nb_path in notebooks:
        validator = NotebookValidator(nb_path)
        validation = validator.validate_structure()

        if not args.quick:
            content_issues = validator.validate_content()
            validation.issues.extend(content_issues)

        results.append(validation)

        status_icon = {'OK': '+', 'WARNING': '~', 'ERROR': '!', 'MISSING': 'x', 'INVALID': 'x'}
        icon = status_icon.get(validation.status, '?')

        if args.verbose or validation.status in ['ERROR', 'MISSING']:
            print(f"  [{icon}] {nb_path.name}: {validation.status} "
                  f"({validation.total_cells} cells, {validation.error_count} errors)")

            if args.verbose:
                for issue in validation.issues[:5]:
                    print(f"      [{issue.issue_type}] Cell {issue.cell_index}: {issue.message[:60]}")

    # Summary
    print_section("SUMMARY")
    ok_count = len([r for r in results if r.status == 'OK'])
    error_count = len([r for r in results if r.status == 'ERROR'])
    warning_count = len([r for r in results if r.status == 'WARNING'])

    print(f"  OK: {ok_count}")
    print(f"  Warnings: {warning_count}")
    print(f"  Errors: {error_count}")

    if args.json:
        print(json.dumps([{
            'path': r.path,
            'status': r.status,
            'issues': [asdict(i) for i in r.issues]
        } for r in results], indent=2))

    return 1 if error_count > 0 else 0


def cmd_skeleton(args):
    """Extract notebook skeletons"""
    repo_root = get_repo_root()
    notebooks = discover_notebooks(args.path, repo_root, recursive=args.recursive)

    if not notebooks:
        print_error(f"No notebooks found at: {args.path}")
        return 1

    skeletons = []
    for nb_path in notebooks:
        analyzer = NotebookAnalyzer(nb_path)
        skeleton = analyzer.get_skeleton(include_code_preview=args.code_preview)
        skeletons.append(skeleton)

    # Format output
    if args.output == 'json':
        print(json.dumps([s.to_dict() for s in skeletons], indent=2, ensure_ascii=False))
    elif args.output == 'markdown':
        print(_format_markdown_table(skeletons, Path(args.path)))
    else:
        print(_format_summary(skeletons))

    return 0


def _format_markdown_table(skeletons: List[NotebookSkeleton], base_path: Path) -> str:
    """Format skeletons as markdown table"""
    lines = ["| # | Notebook | Kernel | Cells | Duration | Main Sections |",
             "|---|----------|--------|-------|----------|---------------|"]

    for i, nb in enumerate(skeletons, 1):
        num_match = re.search(r'-(\d+)-', nb.name)
        num = num_match.group(1) if num_match else str(i)

        main_sections = [s.title for s in nb.sections if s.level == 2][:3]
        sections_str = ', '.join(main_sections) if main_sections else '-'
        if len(sections_str) > 40:
            sections_str = sections_str[:37] + '...'

        duration = f"~{nb.estimated_duration} min" if nb.estimated_duration else '-'

        lines.append(f"| {num} | [{nb.name}]({nb.name}.ipynb) | {nb.kernel} | "
                    f"{nb.total_cells} | {duration} | {sections_str} |")

    return '\n'.join(lines)


def _format_summary(skeletons: List[NotebookSkeleton]) -> str:
    """Format brief summary"""
    total_cells = sum(s.total_cells for s in skeletons)
    total_duration = sum(s.estimated_duration or 0 for s in skeletons)

    lines = [
        f"Notebooks: {len(skeletons)}",
        f"Total cells: {total_cells}",
        f"Estimated duration: ~{total_duration} min ({total_duration//60}h{total_duration%60:02d})",
        "",
        "Notebooks:"
    ]

    for skel in skeletons:
        sections_count = len([s for s in skel.sections if s.level == 2])
        lines.append(f"  - {skel.name}: {skel.total_cells} cells, {sections_count} sections")

    return '\n'.join(lines)


def cmd_analyze(args):
    """Analyze notebook outputs"""
    repo_root = get_repo_root()
    notebooks = discover_notebooks(args.path, repo_root)

    if not notebooks:
        print_error(f"No notebooks found at: {args.path}")
        return 1

    all_analyses = []
    for nb_path in notebooks:
        analyzer = NotebookAnalyzer(nb_path)
        analysis = analyzer.get_cell_outputs_analysis()
        analysis['notebook'] = nb_path.name
        all_analyses.append(analysis)

        status = "!" if analysis['cells_with_errors'] > 0 else (
            "~" if analysis['cells_without_output'] > 0 else "+"
        )
        print(f"  [{status}] {nb_path.name}: "
              f"{analysis['code_cells']} code, "
              f"{analysis['cells_with_output']} output, "
              f"{analysis['cells_with_errors']} errors")

        if args.verbose and analysis['errors']:
            for err in analysis['errors'][:3]:
                print(f"      [ERROR] Cell {err['cell_index']}: {err['ename']}: {err['evalue'][:50]}")

    if args.json:
        print(json.dumps(all_analyses, indent=2))

    return 0


def cmd_check_env(args):
    """Check environment for a notebook family"""
    family = args.family

    if family not in NOTEBOOK_FAMILIES:
        print_error(f"Unknown family: {family}")
        print(f"Available families: {', '.join(NOTEBOOK_FAMILIES.keys())}")
        return 1

    print_section(f"ENVIRONMENT CHECK: {family}")

    checker = EnvironmentChecker(family)
    result = checker.check()

    for component, status in result.components.items():
        version = result.versions.get(component, '')
        version_str = f" ({version})" if version else ""
        if status:
            print_ok(f"{component}{version_str}")
        else:
            print_error(f"{component}")

    for error in result.errors:
        print_warning(error)

    print()
    if result.ready:
        print_ok("Environment ready")
        return 0
    else:
        print_error("Environment not ready")
        return 1


def cmd_execute(args):
    """Execute notebooks"""
    repo_root = get_repo_root()
    notebooks = discover_notebooks(
        args.target, repo_root,
        python_only=args.python_only,
        dotnet_only=args.dotnet_only
    )

    if not notebooks:
        print_error(f"No notebooks found for target: {args.target}")
        return 1

    print_info(f"Found {len(notebooks)} notebook(s) to execute")

    results = []
    for nb_path in notebooks:
        executor = NotebookExecutor(nb_path)
        kernel = executor.detect_kernel_name()

        print(f"\n[{nb_path.name}] (kernel: {kernel})")

        if args.cell_by_cell:
            result = executor.execute_cell_by_cell(
                timeout=args.timeout,
                verbose=args.verbose
            )
        else:
            result = executor.execute_with_papermill(
                timeout=args.timeout,
                batch_mode=args.batch_mode
            )

        results.append(result)

        status_icon = '+' if result.success else '!'
        print(f"  [{status_icon}] {result.message}")

        if args.verbose and result.cell_results:
            errors = [r for r in result.cell_results if not r.success and r.error]
            if errors:
                for err in errors[:3]:
                    print(f"      Cell {err.index}: {err.error[:80]}")

    # Summary
    print_section("EXECUTION SUMMARY")
    success_count = len([r for r in results if r.success])
    error_count = len(results) - success_count
    total_time = sum(r.execution_time for r in results)

    print(f"  Success: {success_count}")
    print(f"  Failed: {error_count}")
    print(f"  Total time: {total_time:.1f}s")

    if args.json:
        print(json.dumps([{
            'path': r.path,
            'success': r.success,
            'kernel': r.kernel,
            'execution_time': r.execution_time,
            'message': r.message
        } for r in results], indent=2))

    return 1 if error_count > 0 else 0


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Consolidated Notebook Tools for CoursIA',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )

    subparsers = parser.add_subparsers(dest='command', help='Commands')

    # validate command
    p_validate = subparsers.add_parser('validate', help='Validate notebooks')
    p_validate.add_argument('target', nargs='?', default='all',
                           help='Notebook path, family name, or "all"')
    p_validate.add_argument('--quick', action='store_true',
                           help='Structure validation only')
    p_validate.add_argument('--python-only', action='store_true')
    p_validate.add_argument('--dotnet-only', action='store_true')
    p_validate.add_argument('--verbose', '-v', action='store_true')
    p_validate.add_argument('--json', action='store_true')

    # skeleton command
    p_skeleton = subparsers.add_parser('skeleton', help='Extract notebook skeletons')
    p_skeleton.add_argument('path', nargs='?', default='.',
                           help='Directory or notebook to analyze')
    p_skeleton.add_argument('--output', '-o', choices=['json', 'markdown', 'summary'],
                           default='summary')
    p_skeleton.add_argument('--recursive', '-r', action='store_true')
    p_skeleton.add_argument('--code-preview', action='store_true')

    # analyze command
    p_analyze = subparsers.add_parser('analyze', help='Analyze notebook outputs')
    p_analyze.add_argument('path', help='Directory or notebook to analyze')
    p_analyze.add_argument('--verbose', '-v', action='store_true')
    p_analyze.add_argument('--json', action='store_true')

    # check-env command
    p_env = subparsers.add_parser('check-env', help='Check environment for a family')
    p_env.add_argument('family', help='Notebook family name')

    # execute command
    p_execute = subparsers.add_parser('execute', help='Execute notebooks')
    p_execute.add_argument('target', nargs='?', default='all',
                          help='Notebook path, family name, or "all"')
    p_execute.add_argument('--cell-by-cell', action='store_true',
                          help='Execute cell by cell (for .NET/Lean notebooks)')
    p_execute.add_argument('--batch-mode', action='store_true',
                          help='Enable batch mode for interactive notebooks')
    p_execute.add_argument('--timeout', type=int, default=300,
                          help='Timeout per notebook/cell in seconds (default: 300)')
    p_execute.add_argument('--python-only', action='store_true')
    p_execute.add_argument('--dotnet-only', action='store_true')
    p_execute.add_argument('--verbose', '-v', action='store_true')
    p_execute.add_argument('--json', action='store_true')

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return 0

    commands = {
        'validate': cmd_validate,
        'skeleton': cmd_skeleton,
        'analyze': cmd_analyze,
        'check-env': cmd_check_env,
        'execute': cmd_execute,
    }

    return commands[args.command](args)


if __name__ == '__main__':
    sys.exit(main())
