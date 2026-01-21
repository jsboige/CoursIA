#!/usr/bin/env python3
"""
Notebook Verification Script for CoursIA

Usage:
    python verify_notebooks.py [target] [options]

Arguments:
    target: Notebook path, family name, or "all"

Options:
    --quick: Structure validation only (no execution)
    --fix: Attempt automatic fixes (not implemented in script, use Claude)
    --python-only: Only test Python notebooks
    --dotnet-only: Only test .NET notebooks
    --timeout: Execution timeout in seconds (default: 300)
    --verbose: Verbose output

Examples:
    python verify_notebooks.py Sudoku --quick
    python verify_notebooks.py Search --python-only
    python verify_notebooks.py all --quick --verbose
"""

import argparse
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Dict, Any


# Notebook families configuration
NOTEBOOK_FAMILIES = {
    "Sudoku": {
        "path": "MyIA.AI.Notebooks/Sudoku",
        "kernel": "dotnet",
        "notes": "Uses #!import, requires cell-by-cell execution"
    },
    "Search": {
        "path": "MyIA.AI.Notebooks/Search",
        "kernel": "mixed",
        "python": ["CSPs_Intro.ipynb", "Exploration_non_informée_Search_uninformed_Exploration.ipynb", "PyGad-EdgeDetection.ipynb"],
        "dotnet": ["GeneticSharp-EdgeDetection.ipynb", "Portfolio_Optimization.ipynb"]
    },
    "SymbolicAI": {
        "path": "MyIA.AI.Notebooks/SymbolicAI",
        "kernel": "mixed",
        "exclude_subdirs": ["Argument_Analysis"]  # Separate family
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
        "kernel": "dotnet"
    },
    "IIT": {
        "path": "MyIA.AI.Notebooks/IIT",
        "kernel": "python"
    },
    "EPF": {
        "path": "MyIA.AI.Notebooks/EPF",
        "kernel": "mixed"
    }
}

# Notebooks to skip (interactive, broken, etc.)
SKIP_NOTEBOOKS = [
    "UI_configuration.ipynb",  # Interactive widgets
    "*_output.ipynb",  # Output files
]


@dataclass
class NotebookResult:
    """Result of notebook verification"""
    path: str
    status: str  # SUCCESS, ERROR, SKIPPED
    kernel: str
    duration: float = 0.0
    error_message: Optional[str] = None
    error_cell: Optional[int] = None


@dataclass
class VerificationReport:
    """Verification report for multiple notebooks"""
    target: str
    timestamp: str
    results: List[NotebookResult] = field(default_factory=list)

    @property
    def success_count(self) -> int:
        return sum(1 for r in self.results if r.status == "SUCCESS")

    @property
    def error_count(self) -> int:
        return sum(1 for r in self.results if r.status == "ERROR")

    @property
    def skipped_count(self) -> int:
        return sum(1 for r in self.results if r.status == "SKIPPED")

    def to_dict(self) -> Dict[str, Any]:
        return {
            "target": self.target,
            "timestamp": self.timestamp,
            "summary": {
                "success": self.success_count,
                "error": self.error_count,
                "skipped": self.skipped_count,
                "total": len(self.results)
            },
            "results": [
                {
                    "path": r.path,
                    "status": r.status,
                    "kernel": r.kernel,
                    "duration": r.duration,
                    "error_message": r.error_message,
                    "error_cell": r.error_cell
                }
                for r in self.results
            ]
        }

    def print_summary(self):
        """Print human-readable summary"""
        print("\n" + "=" * 50)
        print("=== Notebook Verification Report ===")
        print("=" * 50)
        print(f"Date: {self.timestamp}")
        print(f"Target: {self.target}")
        print()
        print("Results:")
        print(f"  - SUCCESS: {self.success_count}")
        print(f"  - ERROR: {self.error_count}")
        print(f"  - SKIPPED: {self.skipped_count}")
        print()
        print("Details:")
        for r in self.results:
            if r.status == "SUCCESS":
                print(f"  [SUCCESS] {r.path} ({r.duration:.1f}s)")
            elif r.status == "ERROR":
                cell_info = f" - Cell {r.error_cell}" if r.error_cell else ""
                error_short = r.error_message[:80] if r.error_message else "Unknown error"
                print(f"  [ERROR] {r.path}{cell_info}: {error_short}")
            else:
                reason = r.error_message or "Skipped"
                print(f"  [SKIPPED] {r.path} - {reason}")
        print("=" * 50)


def get_repo_root() -> Path:
    """Get the repository root directory"""
    script_dir = Path(__file__).parent
    # Go up from scripts/ to repo root
    return script_dir.parent


def detect_notebook_kernel(notebook_path: Path) -> str:
    """Detect the kernel type from notebook metadata"""
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)

        # Check kernel spec
        kernel_spec = nb.get('metadata', {}).get('kernelspec', {})
        kernel_name = kernel_spec.get('name', '').lower()
        language = kernel_spec.get('language', '').lower()

        if 'python' in kernel_name or language == 'python':
            return 'python'
        elif '.net' in kernel_name or language in ['c#', 'csharp', 'f#', 'fsharp']:
            return 'dotnet'

        # Check for .NET magic commands in cells
        cells = nb.get('cells', [])
        for cell in cells:
            if cell.get('cell_type') == 'code':
                source = ''.join(cell.get('source', []))
                if '#!import' in source or '#!csharp' in source or '#!fsharp' in source:
                    return 'dotnet'

        return 'python'  # Default
    except Exception as e:
        print(f"Warning: Could not detect kernel for {notebook_path}: {e}")
        return 'unknown'


def should_skip_notebook(notebook_path: Path) -> Optional[str]:
    """Check if notebook should be skipped, return reason if so"""
    name = notebook_path.name

    for pattern in SKIP_NOTEBOOKS:
        if pattern.startswith('*'):
            if name.endswith(pattern[1:]):
                return f"Matches skip pattern: {pattern}"
        elif name == pattern:
            return f"In skip list: {pattern}"

    return None


def discover_notebooks(target: str, repo_root: Path, python_only: bool = False,
                       dotnet_only: bool = False) -> List[Path]:
    """Discover notebooks to test based on target"""
    notebooks = []

    if target.endswith('.ipynb'):
        # Single notebook
        path = repo_root / target
        if path.exists():
            notebooks.append(path)
        else:
            print(f"Error: Notebook not found: {path}")
    elif target.lower() == 'all':
        # All notebooks
        for family_name, config in NOTEBOOK_FAMILIES.items():
            family_path = repo_root / config['path']
            if family_path.exists():
                for nb in family_path.rglob('*.ipynb'):
                    # Skip subdirectories that are separate families
                    exclude = config.get('exclude_subdirs', [])
                    if any(ex in str(nb) for ex in exclude):
                        continue
                    notebooks.append(nb)
    elif target in NOTEBOOK_FAMILIES:
        # Specific family
        config = NOTEBOOK_FAMILIES[target]
        family_path = repo_root / config['path']
        if family_path.exists():
            for nb in family_path.rglob('*.ipynb'):
                notebooks.append(nb)
        else:
            print(f"Error: Family path not found: {family_path}")
    else:
        # Try as a path pattern
        for nb in repo_root.glob(f"**/{target}"):
            if nb.suffix == '.ipynb':
                notebooks.append(nb)

    # Filter by kernel type
    if python_only or dotnet_only:
        filtered = []
        for nb in notebooks:
            kernel = detect_notebook_kernel(nb)
            if python_only and kernel == 'python':
                filtered.append(nb)
            elif dotnet_only and kernel == 'dotnet':
                filtered.append(nb)
        notebooks = filtered

    return sorted(set(notebooks))


def validate_notebook_structure(notebook_path: Path) -> NotebookResult:
    """Quick validation - just check notebook structure"""
    start_time = time.time()

    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)

        # Check required fields
        if 'cells' not in nb:
            return NotebookResult(
                path=str(notebook_path),
                status="ERROR",
                kernel=detect_notebook_kernel(notebook_path),
                duration=time.time() - start_time,
                error_message="Missing 'cells' field"
            )

        if 'metadata' not in nb:
            return NotebookResult(
                path=str(notebook_path),
                status="ERROR",
                kernel=detect_notebook_kernel(notebook_path),
                duration=time.time() - start_time,
                error_message="Missing 'metadata' field"
            )

        cell_count = len(nb['cells'])
        kernel = detect_notebook_kernel(notebook_path)

        return NotebookResult(
            path=str(notebook_path),
            status="SUCCESS",
            kernel=kernel,
            duration=time.time() - start_time,
            error_message=f"Valid structure ({cell_count} cells)"
        )

    except json.JSONDecodeError as e:
        return NotebookResult(
            path=str(notebook_path),
            status="ERROR",
            kernel="unknown",
            duration=time.time() - start_time,
            error_message=f"Invalid JSON: {e}"
        )
    except Exception as e:
        return NotebookResult(
            path=str(notebook_path),
            status="ERROR",
            kernel="unknown",
            duration=time.time() - start_time,
            error_message=str(e)
        )


def execute_python_notebook(notebook_path: Path, timeout: int = 300,
                            batch_mode: bool = False) -> NotebookResult:
    """Execute a Python notebook using Papermill"""
    start_time = time.time()
    kernel = 'python'

    output_path = notebook_path.parent / f"{notebook_path.stem}_output.ipynb"

    cmd = [
        sys.executable, '-m', 'papermill',
        str(notebook_path),
        str(output_path),
        '--kernel', 'python3'
    ]

    if batch_mode:
        cmd.extend(['-p', 'BATCH_MODE', 'true'])

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(notebook_path.parent)
        )

        duration = time.time() - start_time

        if result.returncode == 0:
            return NotebookResult(
                path=str(notebook_path),
                status="SUCCESS",
                kernel=kernel,
                duration=duration
            )
        else:
            # Try to extract error from stderr
            error_msg = result.stderr[-500:] if result.stderr else "Unknown error"
            return NotebookResult(
                path=str(notebook_path),
                status="ERROR",
                kernel=kernel,
                duration=duration,
                error_message=error_msg
            )

    except subprocess.TimeoutExpired:
        return NotebookResult(
            path=str(notebook_path),
            status="ERROR",
            kernel=kernel,
            duration=timeout,
            error_message=f"Timeout after {timeout}s"
        )
    except Exception as e:
        return NotebookResult(
            path=str(notebook_path),
            status="ERROR",
            kernel=kernel,
            duration=time.time() - start_time,
            error_message=str(e)
        )


def execute_dotnet_notebook(notebook_path: Path, timeout: int = 300) -> NotebookResult:
    """
    Execute a .NET notebook.
    Note: This requires MCP Jupyter tools for proper execution.
    This function just marks them as requiring manual/MCP execution.
    """
    return NotebookResult(
        path=str(notebook_path),
        status="SKIPPED",
        kernel="dotnet",
        duration=0,
        error_message="Requires MCP Jupyter for cell-by-cell execution"
    )


def verify_notebook(notebook_path: Path, quick: bool = False,
                    timeout: int = 300) -> NotebookResult:
    """Verify a single notebook"""
    # Check if should skip
    skip_reason = should_skip_notebook(notebook_path)
    if skip_reason:
        return NotebookResult(
            path=str(notebook_path),
            status="SKIPPED",
            kernel=detect_notebook_kernel(notebook_path),
            error_message=skip_reason
        )

    # Quick mode - just validate structure
    if quick:
        return validate_notebook_structure(notebook_path)

    # Detect kernel and execute accordingly
    kernel = detect_notebook_kernel(notebook_path)

    # Check for family-specific settings
    for family_name, config in NOTEBOOK_FAMILIES.items():
        if config['path'] in str(notebook_path):
            batch_mode = config.get('batch_mode', False)
            break
    else:
        batch_mode = False

    if kernel == 'python':
        return execute_python_notebook(notebook_path, timeout, batch_mode)
    elif kernel == 'dotnet':
        return execute_dotnet_notebook(notebook_path, timeout)
    else:
        return NotebookResult(
            path=str(notebook_path),
            status="SKIPPED",
            kernel=kernel,
            error_message=f"Unknown kernel type: {kernel}"
        )


def main():
    parser = argparse.ArgumentParser(
        description="Verify Jupyter notebooks in CoursIA repository",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('target', nargs='?', default='all',
                        help='Notebook path, family name, or "all"')
    parser.add_argument('--quick', action='store_true',
                        help='Quick validation (structure only)')
    parser.add_argument('--fix', action='store_true',
                        help='Attempt automatic fixes (use Claude for this)')
    parser.add_argument('--python-only', action='store_true',
                        help='Only test Python notebooks')
    parser.add_argument('--dotnet-only', action='store_true',
                        help='Only test .NET notebooks')
    parser.add_argument('--timeout', type=int, default=300,
                        help='Execution timeout in seconds (default: 300)')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Verbose output')
    parser.add_argument('--json', action='store_true',
                        help='Output results as JSON')

    args = parser.parse_args()

    if args.fix:
        print("Note: --fix flag is for Claude Code integration. "
              "Use /verify-notebooks command with --fix for automatic fixes.")

    repo_root = get_repo_root()

    # Discover notebooks
    notebooks = discover_notebooks(
        args.target, repo_root,
        python_only=args.python_only,
        dotnet_only=args.dotnet_only
    )

    if not notebooks:
        print(f"No notebooks found for target: {args.target}")
        sys.exit(1)

    print(f"Found {len(notebooks)} notebook(s) to verify")
    if args.verbose:
        for nb in notebooks:
            print(f"  - {nb.relative_to(repo_root)}")

    # Create report
    report = VerificationReport(
        target=args.target,
        timestamp=datetime.now().isoformat()
    )

    # Verify each notebook
    for i, nb in enumerate(notebooks, 1):
        rel_path = nb.relative_to(repo_root)
        print(f"\n[{i}/{len(notebooks)}] Verifying: {rel_path}")

        result = verify_notebook(nb, quick=args.quick, timeout=args.timeout)
        report.results.append(result)

        if args.verbose or result.status == "ERROR":
            status_symbol = {"SUCCESS": "+", "ERROR": "!", "SKIPPED": "-"}[result.status]
            print(f"  [{status_symbol}] {result.status}", end="")
            if result.duration > 0:
                print(f" ({result.duration:.1f}s)", end="")
            if result.error_message and result.status != "SUCCESS":
                print(f" - {result.error_message[:100]}", end="")
            print()

    # Output results
    if args.json:
        print(json.dumps(report.to_dict(), indent=2))
    else:
        report.print_summary()

    # Exit with error code if any failures
    sys.exit(1 if report.error_count > 0 else 0)


if __name__ == "__main__":
    main()
