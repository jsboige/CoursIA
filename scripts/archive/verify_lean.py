#!/usr/bin/env python3
"""
Lean Notebooks Verification Script for CoursIA

This script verifies the Lean 4 notebook series located in:
MyIA.AI.Notebooks/SymbolicAI/Lean/

It performs the following checks:
1. Structure validation (JSON format, required fields)
2. Kernel configuration (lean4_jupyter expected)
3. Content validation (markdown cells, code cells)
4. Prerequisites check (elan, lean4_jupyter kernel)
5. Optional execution (requires lean4_jupyter installed)
6. Cell-by-cell execution for detailed testing

Usage:
    python verify_lean.py [options]

Options:
    --quick              Structure validation only (no execution)
    --check-env          Check if Lean environment is properly configured
    --execute            Execute notebooks with Papermill
    --cell-by-cell       Execute notebooks cell by cell with jupyter client
    --notebook NAME      Execute only specified notebook(s), comma-separated
    --python-only        Only execute Python notebooks (Lean-1, Lean-7, Lean-8)
    --verbose            Verbose output
    --json               Output results as JSON
    --timeout SECONDS    Timeout per notebook/cell (default: 300)

Examples:
    python verify_lean.py --quick                          # Fast structural check
    python verify_lean.py --check-env                      # Check Lean installation
    python verify_lean.py --execute --verbose              # Full execution test
    python verify_lean.py --cell-by-cell --python-only     # Cell-by-cell Python notebooks
    python verify_lean.py --notebook Lean-1-Setup.ipynb    # Single notebook
    python verify_lean.py --notebook Lean-7,Lean-8         # Multiple notebooks
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple


# Expected Lean notebooks in order
LEAN_NOTEBOOKS = [
    "Lean-1-Setup.ipynb",
    "Lean-2-Dependent-Types.ipynb",
    "Lean-3-Propositions-Proofs.ipynb",
    "Lean-4-Quantifiers.ipynb",
    "Lean-5-Tactics.ipynb",
    "Lean-6-Mathlib-Essentials.ipynb",
    "Lean-7-LLM-Integration.ipynb",
    "Lean-8-Agentic-Proving.ipynb"
]

# Expected support files
SUPPORT_FILES = [
    "README.md",
    ".env.example",
    "examples/basic_logic.lean",
    "examples/quantifiers.lean",
    "examples/tactics_demo.lean",
    "examples/mathlib_examples.lean",
    "examples/llm_assisted_proof.lean"
]

# Expected kernel specifications
EXPECTED_KERNEL = {
    "name": "lean4",
    "display_name": "Lean 4",
    "language": "lean4"
}

# Notebooks that use Python kernel (for LLM/agentic parts)
PYTHON_NOTEBOOKS = [
    "Lean-1-Setup.ipynb",    # Setup/diagnostic uses Python
    "Lean-7-LLM-Integration.ipynb",  # LLM integration uses Python
    "Lean-8-Agentic-Proving.ipynb"   # Multi-agent system uses Python
]

# Notebooks that require Lean4 kernel
LEAN4_NOTEBOOKS = [
    "Lean-2-Dependent-Types.ipynb",
    "Lean-3-Propositions-Proofs.ipynb",
    "Lean-4-Quantifiers.ipynb",
    "Lean-5-Tactics.ipynb",
    "Lean-6-Mathlib-Essentials.ipynb"
]


@dataclass
class NotebookValidation:
    """Result of notebook validation"""
    name: str
    exists: bool = False
    valid_json: bool = False
    has_cells: bool = False
    has_metadata: bool = False
    kernel_correct: bool = False
    markdown_cells: int = 0
    code_cells: int = 0
    total_cells: int = 0
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)

    @property
    def status(self) -> str:
        if not self.exists:
            return "MISSING"
        if self.errors:
            return "ERROR"
        if self.warnings:
            return "WARNING"
        return "OK"


@dataclass
class EnvironmentCheck:
    """Result of environment check"""
    elan_installed: bool = False
    elan_version: Optional[str] = None
    lean_installed: bool = False
    lean_version: Optional[str] = None
    lean4_jupyter_installed: bool = False
    kernel_registered: bool = False
    errors: List[str] = field(default_factory=list)

    @property
    def ready(self) -> bool:
        return self.elan_installed and self.lean_installed

    @property
    def can_execute(self) -> bool:
        return self.ready and self.lean4_jupyter_installed and self.kernel_registered


@dataclass
class LeanVerificationReport:
    """Complete verification report"""
    timestamp: str
    lean_directory: str
    environment: Optional[EnvironmentCheck] = None
    notebooks: List[NotebookValidation] = field(default_factory=list)
    support_files: Dict[str, bool] = field(default_factory=dict)
    execution_results: Dict[str, str] = field(default_factory=dict)

    @property
    def notebook_count(self) -> int:
        return len([n for n in self.notebooks if n.exists])

    @property
    def error_count(self) -> int:
        return len([n for n in self.notebooks if n.status == "ERROR"])

    @property
    def missing_count(self) -> int:
        return len([n for n in self.notebooks if n.status == "MISSING"])

    @property
    def support_files_ok(self) -> bool:
        return all(self.support_files.values())

    def to_dict(self) -> Dict[str, Any]:
        return {
            "timestamp": self.timestamp,
            "lean_directory": self.lean_directory,
            "summary": {
                "notebooks_found": self.notebook_count,
                "notebooks_expected": len(LEAN_NOTEBOOKS),
                "errors": self.error_count,
                "missing": self.missing_count,
                "support_files_ok": self.support_files_ok,
                "environment_ready": self.environment.ready if self.environment else False,
                "can_execute": self.environment.can_execute if self.environment else False
            },
            "environment": {
                "elan_installed": self.environment.elan_installed if self.environment else False,
                "elan_version": self.environment.elan_version if self.environment else None,
                "lean_installed": self.environment.lean_installed if self.environment else False,
                "lean_version": self.environment.lean_version if self.environment else None,
                "lean4_jupyter_installed": self.environment.lean4_jupyter_installed if self.environment else False,
                "kernel_registered": self.environment.kernel_registered if self.environment else False
            } if self.environment else None,
            "notebooks": [
                {
                    "name": n.name,
                    "status": n.status,
                    "exists": n.exists,
                    "valid_json": n.valid_json,
                    "kernel_correct": n.kernel_correct,
                    "markdown_cells": n.markdown_cells,
                    "code_cells": n.code_cells,
                    "total_cells": n.total_cells,
                    "errors": n.errors,
                    "warnings": n.warnings
                }
                for n in self.notebooks
            ],
            "support_files": self.support_files,
            "execution_results": self.execution_results
        }

    def print_summary(self, verbose: bool = False):
        """Print human-readable summary"""
        print("\n" + "=" * 60)
        print("=== Lean Notebooks Verification Report ===")
        print("=" * 60)
        print(f"Date: {self.timestamp}")
        print(f"Directory: {self.lean_directory}")

        # Environment
        if self.environment:
            print("\n--- Environment ---")
            status = "[OK]" if self.environment.ready else "[MISSING]"
            print(f"  elan: {status} {self.environment.elan_version or 'not found'}")
            print(f"  lean: {'[OK]' if self.environment.lean_installed else '[MISSING]'} {self.environment.lean_version or 'not found'}")
            print(f"  lean4_jupyter: {'[OK]' if self.environment.lean4_jupyter_installed else '[MISSING]'}")
            print(f"  kernel registered: {'[OK]' if self.environment.kernel_registered else '[MISSING]'}")
            if self.environment.errors:
                for err in self.environment.errors:
                    print(f"  [!] {err}")

        # Notebooks
        print("\n--- Notebooks ---")
        print(f"  Found: {self.notebook_count}/{len(LEAN_NOTEBOOKS)}")
        print(f"  Errors: {self.error_count}")
        print(f"  Missing: {self.missing_count}")

        for n in self.notebooks:
            status_icon = {
                "OK": "+",
                "WARNING": "~",
                "ERROR": "!",
                "MISSING": "x"
            }.get(n.status, "?")
            print(f"  [{status_icon}] {n.name}: {n.status}", end="")
            if n.exists:
                print(f" ({n.total_cells} cells: {n.markdown_cells} md, {n.code_cells} code)")
            else:
                print()
            if verbose and n.errors:
                for err in n.errors:
                    print(f"      Error: {err}")
            if verbose and n.warnings:
                for warn in n.warnings:
                    print(f"      Warning: {warn}")

        # Support files
        print("\n--- Support Files ---")
        for filepath, exists in self.support_files.items():
            status = "[OK]" if exists else "[MISSING]"
            print(f"  {status} {filepath}")

        # Execution results
        if self.execution_results:
            print("\n--- Execution Results ---")
            for nb, result in self.execution_results.items():
                print(f"  [{result}] {nb}")

        print("=" * 60)


def get_repo_root() -> Path:
    """Get the repository root directory"""
    script_dir = Path(__file__).parent
    return script_dir.parent


def get_lean_directory(repo_root: Path) -> Path:
    """Get the Lean notebooks directory"""
    return repo_root / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean"


def check_environment() -> EnvironmentCheck:
    """Check if Lean environment is properly configured"""
    env = EnvironmentCheck()

    # Check elan
    elan_path = shutil.which("elan")
    if elan_path:
        env.elan_installed = True
        try:
            result = subprocess.run(
                ["elan", "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                env.elan_version = result.stdout.strip().split('\n')[0]
        except Exception as e:
            env.errors.append(f"Error getting elan version: {e}")
    else:
        env.errors.append("elan not found in PATH")

    # Check lean
    lean_path = shutil.which("lean")
    if lean_path:
        env.lean_installed = True
        try:
            result = subprocess.run(
                ["lean", "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                env.lean_version = result.stdout.strip().split('\n')[0]
        except Exception as e:
            env.errors.append(f"Error getting lean version: {e}")
    else:
        env.errors.append("lean not found in PATH (run: elan default leanprover/lean4:stable)")

    # Check lean4_jupyter
    try:
        result = subprocess.run(
            [sys.executable, "-c", "import lean4_jupyter; print('OK')"],
            capture_output=True,
            text=True,
            timeout=10
        )
        env.lean4_jupyter_installed = result.returncode == 0 and "OK" in result.stdout
    except Exception:
        env.lean4_jupyter_installed = False

    if not env.lean4_jupyter_installed:
        env.errors.append("lean4_jupyter not installed (run: pip install lean4_jupyter)")

    # Check if kernel is registered
    try:
        result = subprocess.run(
            ["jupyter", "kernelspec", "list", "--json"],
            capture_output=True,
            text=True,
            timeout=10
        )
        if result.returncode == 0:
            kernels = json.loads(result.stdout)
            # Check for lean4 or lean kernel
            kernel_names = kernels.get("kernelspecs", {}).keys()
            env.kernel_registered = any("lean" in k.lower() for k in kernel_names)
    except Exception as e:
        env.errors.append(f"Error checking Jupyter kernels: {e}")

    if not env.kernel_registered:
        env.errors.append("Lean kernel not registered in Jupyter")

    return env


def validate_notebook(notebook_path: Path) -> NotebookValidation:
    """Validate a single notebook structure and content"""
    result = NotebookValidation(name=notebook_path.name)

    # Check existence
    if not notebook_path.exists():
        result.errors.append("File does not exist")
        return result
    result.exists = True

    # Parse JSON
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
        result.valid_json = True
    except json.JSONDecodeError as e:
        result.errors.append(f"Invalid JSON: {e}")
        return result

    # Check cells
    if 'cells' not in nb:
        result.errors.append("Missing 'cells' field")
    else:
        result.has_cells = True
        cells = nb['cells']
        result.total_cells = len(cells)
        result.markdown_cells = sum(1 for c in cells if c.get('cell_type') == 'markdown')
        result.code_cells = sum(1 for c in cells if c.get('cell_type') == 'code')

        # Validate cell structure
        for i, cell in enumerate(cells):
            if 'cell_type' not in cell:
                result.errors.append(f"Cell {i}: missing 'cell_type'")
            if 'source' not in cell:
                result.errors.append(f"Cell {i}: missing 'source'")

        # Check for pedagogical content (markdown cells)
        if result.markdown_cells < 3:
            result.warnings.append(f"Only {result.markdown_cells} markdown cells (expected >= 3 for pedagogical content)")

        # Check for code content
        if result.code_cells < 2:
            result.warnings.append(f"Only {result.code_cells} code cells (expected >= 2 for examples)")

    # Check metadata
    if 'metadata' not in nb:
        result.errors.append("Missing 'metadata' field")
    else:
        result.has_metadata = True
        metadata = nb['metadata']

        # Check kernel spec
        kernel_spec = metadata.get('kernelspec', {})
        kernel_name = kernel_spec.get('name', '').lower()
        kernel_language = kernel_spec.get('language', '').lower()

        # Accept lean4, lean, lean4_jupyter as valid kernel names
        if 'lean' in kernel_name or kernel_language in ['lean4', 'lean']:
            result.kernel_correct = True
        else:
            # For notebooks 7-8 which use Python for LLM integration
            notebook_num = re.search(r'Lean-(\d+)', notebook_path.name)
            if notebook_num and int(notebook_num.group(1)) >= 7:
                # Notebooks 7-8 may use Python kernel for LLM parts
                if 'python' in kernel_name or kernel_language == 'python':
                    result.kernel_correct = True
                    result.warnings.append("Uses Python kernel (expected for LLM notebooks)")
                else:
                    result.warnings.append(f"Unexpected kernel: {kernel_name}")
            else:
                result.warnings.append(f"Expected lean4 kernel, found: {kernel_name}")

    # Content-specific checks based on notebook number
    notebook_num = re.search(r'Lean-(\d+)', notebook_path.name)
    if notebook_num and result.has_cells:
        num = int(notebook_num.group(1))
        cells = nb['cells']

        # Check for expected patterns
        if num == 1:  # Setup notebook
            has_install = any('#eval' in ''.join(c.get('source', [])) or 'elan' in ''.join(c.get('source', [])).lower()
                            for c in cells)
            if not has_install:
                result.warnings.append("Setup notebook should contain installation/verification code")

        elif num == 2:  # Dependent Types
            has_type_examples = any('#check' in ''.join(c.get('source', [])) for c in cells)
            if not has_type_examples:
                result.warnings.append("Types notebook should contain #check examples")

        elif num == 5:  # Tactics
            has_tactics = any('by' in ''.join(c.get('source', [])) for c in cells)
            if not has_tactics:
                result.warnings.append("Tactics notebook should contain 'by' keyword for tactic mode")

    return result


def check_support_files(lean_dir: Path) -> Dict[str, bool]:
    """Check if all support files exist"""
    results = {}
    for filepath in SUPPORT_FILES:
        full_path = lean_dir / filepath
        results[filepath] = full_path.exists()
    return results


def get_notebook_kernel(notebook_path: Path) -> str:
    """Determine the appropriate kernel for a notebook."""
    notebook_name = notebook_path.name
    if notebook_name in PYTHON_NOTEBOOKS:
        return "python3"
    return "lean4"


def execute_notebook_with_papermill(notebook_path: Path, timeout: int = 300) -> Tuple[bool, str]:
    """
    Execute a notebook using papermill with appropriate kernel.
    Returns (success, message)
    """
    output_path = notebook_path.parent / "output" / f"executed_{notebook_path.name}"
    output_path.parent.mkdir(exist_ok=True)

    kernel = get_notebook_kernel(notebook_path)

    try:
        result = subprocess.run(
            [
                sys.executable, "-m", "papermill",
                str(notebook_path),
                str(output_path),
                "--kernel", kernel
            ],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(notebook_path.parent)
        )

        if result.returncode == 0:
            return True, f"SUCCESS (kernel={kernel})"
        else:
            error_msg = result.stderr[-200:] if result.stderr else "Unknown error"
            return False, f"FAILED: {error_msg}"

    except subprocess.TimeoutExpired:
        return False, f"TIMEOUT ({timeout}s)"
    except Exception as e:
        return False, f"ERROR: {e}"


def execute_notebook_cell_by_cell(notebook_path: Path, timeout: int = 60,
                                   verbose: bool = False) -> Tuple[bool, str, List[Dict]]:
    """
    Execute a notebook cell by cell using jupyter_client.
    Returns (success, message, cell_results)

    Cell results contain: cell_index, cell_type, success, output, error
    """
    try:
        import jupyter_client
    except ImportError:
        return False, "jupyter_client not installed", []

    kernel_name = get_notebook_kernel(notebook_path)
    cell_results = []

    # Read notebook
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
    except Exception as e:
        return False, f"Failed to read notebook: {e}", []

    cells = nb.get('cells', [])
    if not cells:
        return True, "No cells to execute", []

    # Start kernel
    try:
        km = jupyter_client.KernelManager(kernel_name=kernel_name)
        km.start_kernel()
        kc = km.client()
        kc.start_channels()
        kc.wait_for_ready(timeout=30)
    except Exception as e:
        return False, f"Failed to start {kernel_name} kernel: {e}", []

    try:
        # Set working directory to notebook location
        if kernel_name == "python3":
            wd_code = f"import os; os.chdir(r'{notebook_path.parent}')"
            kc.execute(wd_code)
            # Wait for completion
            while True:
                try:
                    msg = kc.get_iopub_msg(timeout=5)
                    if msg['msg_type'] == 'status' and msg['content']['execution_state'] == 'idle':
                        break
                except:
                    break

        # Execute each code cell
        success_count = 0
        error_count = 0

        for i, cell in enumerate(cells):
            cell_type = cell.get('cell_type', 'unknown')
            source = ''.join(cell.get('source', []))

            if cell_type != 'code' or not source.strip():
                cell_results.append({
                    'index': i,
                    'type': cell_type,
                    'success': True,
                    'output': 'skipped (non-code or empty)',
                    'error': None
                })
                continue

            if verbose:
                print(f"  Cell {i} ({cell_type}): ", end="", flush=True)

            # Execute cell
            try:
                msg_id = kc.execute(source)

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
                            errors.append(f"{content.get('ename', 'Error')}: {content.get('evalue', '')}")
                        elif msg_type == 'status' and content.get('execution_state') == 'idle':
                            break
                    except Exception as e:
                        if 'timeout' in str(e).lower():
                            errors.append(f"Timeout after {timeout}s")
                        break

                output_text = '\n'.join(outputs)[:500]  # Limit output
                error_text = '\n'.join(errors) if errors else None
                cell_success = len(errors) == 0

                cell_results.append({
                    'index': i,
                    'type': cell_type,
                    'success': cell_success,
                    'output': output_text,
                    'error': error_text
                })

                if cell_success:
                    success_count += 1
                    if verbose:
                        print("OK")
                else:
                    error_count += 1
                    if verbose:
                        print(f"FAILED: {error_text[:100] if error_text else 'unknown'}")

            except Exception as e:
                cell_results.append({
                    'index': i,
                    'type': cell_type,
                    'success': False,
                    'output': '',
                    'error': str(e)
                })
                error_count += 1
                if verbose:
                    print(f"ERROR: {e}")

        # Summary
        total_code = sum(1 for r in cell_results if r['type'] == 'code' and r['output'] != 'skipped (non-code or empty)')
        message = f"Executed {total_code} code cells: {success_count} OK, {error_count} errors"
        overall_success = error_count == 0

        return overall_success, message, cell_results

    finally:
        # Cleanup
        try:
            kc.stop_channels()
            km.shutdown_kernel(now=True)
        except:
            pass


def execute_notebook_with_lean4(notebook_path: Path, timeout: int = 300) -> Tuple[bool, str]:
    """
    Execute a Lean notebook using papermill with lean4 kernel.
    Returns (success, message)
    DEPRECATED: Use execute_notebook_with_papermill instead.
    """
    return execute_notebook_with_papermill(notebook_path, timeout)


def run_verification(lean_dir: Path, check_env: bool = True,
                     execute: bool = False, verbose: bool = False) -> LeanVerificationReport:
    """Run complete verification"""
    report = LeanVerificationReport(
        timestamp=datetime.now().isoformat(),
        lean_directory=str(lean_dir)
    )

    # Environment check
    if check_env:
        report.environment = check_environment()

    # Validate notebooks
    for notebook_name in LEAN_NOTEBOOKS:
        notebook_path = lean_dir / notebook_name
        validation = validate_notebook(notebook_path)
        report.notebooks.append(validation)

    # Check support files
    report.support_files = check_support_files(lean_dir)

    # Execute notebooks if requested
    if execute:
        if report.environment and not report.environment.can_execute:
            print("Warning: Environment not ready for execution. Skipping...")
        else:
            for notebook_name in LEAN_NOTEBOOKS:
                notebook_path = lean_dir / notebook_name
                if notebook_path.exists():
                    print(f"Executing {notebook_name}...", end=" ", flush=True)
                    success, message = execute_notebook_with_lean4(notebook_path)
                    report.execution_results[notebook_name] = message
                    print(message)
                else:
                    report.execution_results[notebook_name] = "MISSING"

    return report


def filter_notebooks(notebook_list: List[str], filter_str: Optional[str],
                      python_only: bool = False) -> List[str]:
    """Filter notebook list based on criteria."""
    result = notebook_list

    # Filter by name if specified
    if filter_str:
        filters = [f.strip() for f in filter_str.split(',')]
        result = []
        for nb in notebook_list:
            for f in filters:
                if f.lower() in nb.lower():
                    result.append(nb)
                    break

    # Filter Python-only if requested
    if python_only:
        result = [nb for nb in result if nb in PYTHON_NOTEBOOKS]

    return result


def main():
    parser = argparse.ArgumentParser(
        description="Verify Lean notebooks in CoursIA repository",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('--quick', action='store_true',
                        help='Quick structural validation only')
    parser.add_argument('--check-env', action='store_true',
                        help='Check Lean environment configuration')
    parser.add_argument('--execute', action='store_true',
                        help='Execute notebooks with Papermill')
    parser.add_argument('--cell-by-cell', action='store_true',
                        help='Execute notebooks cell by cell with jupyter client')
    parser.add_argument('--notebook', type=str, default=None,
                        help='Execute only specified notebook(s), comma-separated')
    parser.add_argument('--python-only', action='store_true',
                        help='Only execute Python notebooks (Lean-1, Lean-7, Lean-8)')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Verbose output')
    parser.add_argument('--json', action='store_true',
                        help='Output results as JSON')
    parser.add_argument('--timeout', type=int, default=300,
                        help='Timeout per notebook/cell in seconds (default: 300)')

    args = parser.parse_args()

    # Get directories
    repo_root = get_repo_root()
    lean_dir = get_lean_directory(repo_root)

    if not lean_dir.exists():
        print(f"Error: Lean directory not found: {lean_dir}")
        sys.exit(1)

    print(f"Verifying Lean notebooks in: {lean_dir}")

    # Determine which notebooks to process
    notebooks_to_process = filter_notebooks(
        LEAN_NOTEBOOKS,
        args.notebook,
        args.python_only
    )

    if args.notebook or args.python_only:
        print(f"Notebooks selected: {notebooks_to_process}")

    # Run verification
    report = run_verification(
        lean_dir,
        check_env=args.check_env or args.execute or args.cell_by_cell,
        execute=False,  # We'll handle execution separately
        verbose=args.verbose
    )

    # Execute notebooks if requested
    if args.execute or args.cell_by_cell:
        print("\n--- Execution ---")

        for notebook_name in notebooks_to_process:
            notebook_path = lean_dir / notebook_name
            if not notebook_path.exists():
                report.execution_results[notebook_name] = "MISSING"
                continue

            kernel = get_notebook_kernel(notebook_path)
            print(f"\n[{notebook_name}] (kernel: {kernel})")

            if args.cell_by_cell:
                success, message, cell_results = execute_notebook_cell_by_cell(
                    notebook_path,
                    timeout=min(args.timeout, 60),  # Per-cell timeout
                    verbose=args.verbose
                )
                report.execution_results[notebook_name] = message

                if args.verbose and cell_results:
                    errors = [r for r in cell_results if not r['success'] and r['error']]
                    if errors:
                        print(f"  Errors in cells: {[e['index'] for e in errors]}")
                        for e in errors[:3]:  # Show first 3 errors
                            print(f"    Cell {e['index']}: {e['error'][:100]}")
            else:
                print(f"  Executing with Papermill...", end=" ", flush=True)
                success, message = execute_notebook_with_papermill(
                    notebook_path,
                    timeout=args.timeout
                )
                report.execution_results[notebook_name] = message
                print(message)

    # Output results
    if args.json:
        print(json.dumps(report.to_dict(), indent=2))
    else:
        report.print_summary(verbose=args.verbose)

    # Exit code
    if report.missing_count > 0 or report.error_count > 0:
        sys.exit(1)

    # Check execution results
    if args.execute or args.cell_by_cell:
        failed_executions = [k for k, v in report.execution_results.items()
                            if 'FAILED' in v or 'ERROR' in v or 'TIMEOUT' in v]
        if failed_executions:
            print(f"\nFailed executions: {failed_executions}")
            sys.exit(1)

    sys.exit(0)


if __name__ == "__main__":
    main()
