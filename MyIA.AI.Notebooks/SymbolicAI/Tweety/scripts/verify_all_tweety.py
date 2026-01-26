#!/usr/bin/env python3
"""
Tweety Notebooks Verification Script for CoursIA

This script verifies the Tweety notebook series located in:
MyIA.AI.Notebooks/SymbolicAI/Tweety/

It performs the following checks:
1. Structure validation (JSON format, required fields)
2. Kernel configuration (python3 expected)
3. Content validation (markdown cells, code cells)
4. Prerequisites check (JDK, JPype, Tweety JARs)
5. Optional execution (Papermill or cell-by-cell)

Usage:
    python verify_all_tweety.py [options]

Options:
    --quick              Structure validation only (no execution)
    --check-env          Check if Tweety environment is properly configured
    --execute            Execute notebooks with Papermill
    --cell-by-cell       Execute notebooks cell by cell with jupyter client
    --notebook NAME      Execute only specified notebook(s), comma-separated
    --verbose            Verbose output
    --json               Output results as JSON
    --timeout SECONDS    Timeout per notebook/cell (default: 120)

Examples:
    python verify_all_tweety.py --quick                      # Fast structural check
    python verify_all_tweety.py --check-env                  # Check Tweety installation
    python verify_all_tweety.py --execute --verbose          # Full execution test
    python verify_all_tweety.py --cell-by-cell               # Cell-by-cell execution
    python verify_all_tweety.py --notebook Tweety-1-Setup    # Single notebook
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional


# Expected Tweety notebooks in order
TWEETY_NOTEBOOKS = [
    "Tweety-1-Setup.ipynb",
    "Tweety-2-Basic-Logics.ipynb",
    "Tweety-3-Advanced-Logics.ipynb",
    "Tweety-4-Belief-Revision.ipynb",
    "Tweety-5-Abstract-Argumentation.ipynb",
    "Tweety-6-Structured-Argumentation.ipynb",
    "Tweety-7-Advanced-Argumentation.ipynb",  # Original (conservé pour référence)
    "Tweety-7a-Extended-Frameworks.ipynb",
    "Tweety-7b-Ranking-Probabilistic.ipynb",
    "Tweety-8-Agent-Dialogues.ipynb",
    "Tweety-9-Preferences.ipynb",
]

# Expected support directories and files
EXPECTED_SUPPORT = [
    "libs/",  # JARs directory (may be at parent level)
]

# Expected number of Tweety JARs
EXPECTED_JAR_COUNT = 35

# Expected kernel specification
EXPECTED_KERNEL = {
    "name": "python3",
    "language": "python"
}

# TweetyProject versions information
TWEETY_VERSIONS = {
    "1.28": {
        "release_date": "January 2025",
        "new_features": ["arg.caf (Constrained AF)", "k-admissibility reasoner"],
        "status": "stable"
    },
    "1.29": {
        "release_date": "July 2025",
        "new_features": ["arg.eaf (Epistemic AF)", "graph rendering", "minor bugfixes"],
        "status": "latest"
    }
}

# Known issues per notebook (expected failures)
# These limitations are present in both Tweety 1.28 and 1.29
KNOWN_ISSUES = {
    "Tweety-3-Advanced-Logics.ipynb": [
        "SimpleMlReasoner may hang indefinitely without SPASS external prover",
        "Limitation: Install SPASS for modal logic reasoning"
    ],
    "Tweety-4-Belief-Revision.ipynb": [
        "CrMas imports may fail - InformationObject class removed in Tweety 1.28 API refactoring",
        "Limitation: Multi-agent belief revision unavailable via JPype"
    ],
    "Tweety-5-Abstract-Argumentation.ipynb": [
        "AF Learning disabled - ClassCastException (Tautology cannot be cast to AssociativePlFormula)",
        "Limitation: Internal Tweety bug, section commented out"
    ],
    "Tweety-7-Advanced-Argumentation.ipynb": [
        "ADF section may fail - requires native SAT solver (NativeMinisatSolver)",
        "Limitation: Native libraries not loadable via JPype, Sat4j fallback insufficient"
    ],
    "Tweety-7a-Extended-Frameworks.ipynb": [
        "ADF section may fail - requires native SAT solver",
        "Other sections (Bipolar, WAF, SAF, SetAF, Extended) work correctly"
    ],
    "Tweety-7b-Ranking-Probabilistic.ipynb": [
        "All sections should work correctly"
    ],
    "Tweety-8-Agent-Dialogues.ipynb": [
        "Module coverage limited - agents.dialogues is relatively undocumented",
        "Lottery examples from arg.prob work correctly"
    ],
    "Tweety-9-Preferences.ipynb": [
        "preferences module may have limited API exposure",
        "Python simulation of voting rules provided as alternative"
    ],
}


@dataclass
class CellResult:
    """Result of executing a single cell"""
    index: int
    cell_type: str
    success: bool
    execution_time: float = 0.0
    error: Optional[str] = None
    output_preview: str = ""


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
    cell_results: List[CellResult] = field(default_factory=list)
    execution_time: float = 0.0

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
    jdk_installed: bool = False
    jdk_version: Optional[str] = None
    jdk_source: str = ""  # "system" or "portable"
    jpype_installed: bool = False
    jpype_version: Optional[str] = None
    jars_found: int = 0
    jars_path: Optional[str] = None
    clingo_installed: bool = False
    clingo_version: Optional[str] = None
    spass_installed: bool = False
    eprover_installed: bool = False
    eprover_path: Optional[str] = None
    sat_libs_found: List[str] = field(default_factory=list)  # lingeling, minisat, picosat
    sat_libs_path: Optional[str] = None
    errors: List[str] = field(default_factory=list)

    @property
    def ready(self) -> bool:
        return self.jdk_installed and self.jpype_installed and self.jars_found >= 30

    @property
    def can_execute(self) -> bool:
        return self.ready


@dataclass
class TweetyVerificationReport:
    """Complete verification report"""
    timestamp: str
    tweety_directory: str
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

    def to_dict(self) -> Dict[str, Any]:
        return {
            "timestamp": self.timestamp,
            "tweety_directory": self.tweety_directory,
            "summary": {
                "notebooks_found": self.notebook_count,
                "notebooks_expected": len(TWEETY_NOTEBOOKS),
                "errors": self.error_count,
                "missing": self.missing_count,
                "environment_ready": self.environment.ready if self.environment else False,
            },
            "environment": {
                "jdk_installed": self.environment.jdk_installed if self.environment else False,
                "jdk_version": self.environment.jdk_version if self.environment else None,
                "jdk_source": self.environment.jdk_source if self.environment else None,
                "jpype_installed": self.environment.jpype_installed if self.environment else False,
                "jpype_version": self.environment.jpype_version if self.environment else None,
                "jars_found": self.environment.jars_found if self.environment else 0,
                "jars_path": self.environment.jars_path if self.environment else None,
                "clingo_installed": self.environment.clingo_installed if self.environment else False,
                "spass_installed": self.environment.spass_installed if self.environment else False,
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
                    "execution_time": n.execution_time,
                    "errors": n.errors,
                    "warnings": n.warnings,
                    "known_issues": KNOWN_ISSUES.get(n.name, []),
                }
                for n in self.notebooks
            ],
            "support_files": self.support_files,
            "execution_results": self.execution_results,
        }

    def print_summary(self, verbose: bool = False):
        """Print human-readable summary"""
        print("\n" + "=" * 70)
        print("=== Tweety Notebooks Verification Report ===")
        print("=" * 70)
        print(f"Date: {self.timestamp}")
        print(f"Directory: {self.tweety_directory}")

        # Environment
        if self.environment:
            print("\n--- Environment ---")
            jdk_status = "[OK]" if self.environment.jdk_installed else "[MISSING]"
            print(f"  JDK: {jdk_status} {self.environment.jdk_version or 'not found'} ({self.environment.jdk_source})")
            jpype_status = "[OK]" if self.environment.jpype_installed else "[MISSING]"
            print(f"  JPype: {jpype_status} {self.environment.jpype_version or 'not found'}")
            jars_status = "[OK]" if self.environment.jars_found >= 30 else "[MISSING]"
            print(f"  Tweety JARs: {jars_status} {self.environment.jars_found}/{EXPECTED_JAR_COUNT} found")
            if self.environment.jars_path:
                print(f"    Path: {self.environment.jars_path}")
            clingo_status = "[OK]" if self.environment.clingo_installed else "[OPTIONAL]"
            print(f"  Clingo: {clingo_status} {self.environment.clingo_version or 'not found'}")
            spass_status = "[OK]" if self.environment.spass_installed else "[OPTIONAL]"
            print(f"  SPASS: {spass_status}")
            eprover_status = "[OK]" if self.environment.eprover_installed else "[OPTIONAL]"
            eprover_info = self.environment.eprover_path if self.environment.eprover_installed else "not found"
            print(f"  EProver: {eprover_status} {eprover_info}")
            sat_status = "[OK]" if self.environment.sat_libs_found else "[OPTIONAL]"
            sat_info = ", ".join(self.environment.sat_libs_found) if self.environment.sat_libs_found else "not found"
            print(f"  Native SAT libs: {sat_status} {sat_info}")
            if self.environment.sat_libs_path:
                print(f"    Path: {self.environment.sat_libs_path}")
            if self.environment.errors:
                for err in self.environment.errors:
                    print(f"  [!] {err}")

        # Notebooks
        print("\n--- Notebooks ---")
        print(f"  Found: {self.notebook_count}/{len(TWEETY_NOTEBOOKS)}")
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
                time_str = f" ({n.execution_time:.1f}s)" if n.execution_time > 0 else ""
                print(f" ({n.total_cells} cells: {n.markdown_cells} md, {n.code_cells} code){time_str}")
            else:
                print()

            # Known issues
            if n.name in KNOWN_ISSUES:
                for issue in KNOWN_ISSUES[n.name]:
                    print(f"      [Known] {issue}")

            if verbose and n.errors:
                for err in n.errors:
                    print(f"      Error: {err}")
            if verbose and n.warnings:
                for warn in n.warnings:
                    print(f"      Warning: {warn}")

            # Cell-by-cell results
            if verbose and n.cell_results:
                failed_cells = [c for c in n.cell_results if not c.success]
                if failed_cells:
                    print(f"      Failed cells: {len(failed_cells)}/{len(n.cell_results)}")
                    for cell in failed_cells[:3]:  # Show first 3
                        print(f"        Cell {cell.index}: {cell.error[:80] if cell.error else 'Unknown'}")

        # Support files
        if self.support_files:
            print("\n--- Support Files ---")
            for filepath, exists in self.support_files.items():
                status = "[OK]" if exists else "[MISSING]"
                print(f"  {status} {filepath}")

        # Execution results
        if self.execution_results:
            print("\n--- Execution Results ---")
            for nb, result in self.execution_results.items():
                print(f"  [{result}] {nb}")

        # Final status
        print("\n" + "=" * 70)
        if self.environment and self.environment.ready and self.error_count == 0:
            print("[OK] All validations passed!")
        elif self.error_count > 0:
            print(f"[!] {self.error_count} notebook(s) have errors")
        elif self.environment and not self.environment.ready:
            print("[!] Environment not ready - install missing dependencies")
        print("=" * 70)


def get_repo_root() -> Path:
    """Get the repository root directory"""
    script_dir = Path(__file__).parent
    # Navigate up from Tweety/scripts/ to Tweety/ to SymbolicAI/ to MyIA.AI.Notebooks/ to repo root
    return script_dir.parent.parent.parent.parent


def get_tweety_directory(repo_root: Path) -> Path:
    """Get the Tweety notebooks directory"""
    return repo_root / "MyIA.AI.Notebooks" / "SymbolicAI" / "Tweety"


def get_tweety_directory_local() -> Path:
    """Get the Tweety notebooks directory (relative to script location)"""
    script_dir = Path(__file__).parent
    return script_dir.parent  # Tweety/scripts/ -> Tweety/


def find_libs_directory(tweety_dir: Path) -> Optional[Path]:
    """Find the libs directory containing Tweety JARs"""
    # Check multiple possible locations
    possible_paths = [
        tweety_dir / "libs",
        tweety_dir.parent / "libs",  # SymbolicAI/libs
        tweety_dir.parent / "Argument_Analysis" / "libs",
    ]

    for path in possible_paths:
        if path.exists() and path.is_dir():
            jars = list(path.glob("*.jar"))
            if len(jars) >= 10:  # At least some JARs
                return path

    return None


def check_environment(tweety_dir: Path) -> EnvironmentCheck:
    """Check if Tweety environment is properly configured"""
    env = EnvironmentCheck()

    # Check JDK - system first, then portable
    java_home = os.environ.get("JAVA_HOME")
    if java_home and Path(java_home).exists():
        env.jdk_installed = True
        env.jdk_source = "system"
        try:
            java_path = Path(java_home) / "bin" / "java"
            if not java_path.exists():
                java_path = Path(java_home) / "bin" / "java.exe"
            result = subprocess.run(
                [str(java_path), "-version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            # Java version is typically in stderr
            version_output = result.stderr or result.stdout
            for line in version_output.split('\n'):
                if 'version' in line.lower():
                    env.jdk_version = line.strip()
                    break
        except Exception as e:
            env.errors.append(f"Could not get JDK version: {e}")

    # Check portable JDK
    if not env.jdk_installed:
        portable_paths = [
            tweety_dir / "jdk-17-portable",
            tweety_dir.parent / "Argument_Analysis" / "jdk-17-portable",
        ]
        for portable_path in portable_paths:
            if portable_path.exists():
                zulu_dirs = list(portable_path.glob("zulu*"))
                if zulu_dirs:
                    env.jdk_installed = True
                    env.jdk_source = "portable"
                    env.jdk_version = zulu_dirs[0].name
                    break

    # Check JPype
    try:
        import jpype
        env.jpype_installed = True
        env.jpype_version = jpype.__version__
    except ImportError:
        env.errors.append("JPype not installed: pip install jpype1")

    # Check Tweety JARs
    libs_path = find_libs_directory(tweety_dir)
    if libs_path:
        jars = list(libs_path.glob("*.jar"))
        env.jars_found = len(jars)
        env.jars_path = str(libs_path)
    else:
        env.errors.append("Tweety JARs not found - run Tweety-1-Setup.ipynb first")

    # Check Clingo (optional)
    clingo_path = shutil.which("clingo")
    if clingo_path:
        env.clingo_installed = True
        try:
            result = subprocess.run(
                ["clingo", "--version"],
                capture_output=True,
                text=True,
                timeout=5
            )
            if result.returncode == 0:
                env.clingo_version = result.stdout.split('\n')[0].strip()
        except Exception:
            pass

    # Check for local clingo
    if not env.clingo_installed:
        local_clingo_paths = [
            tweety_dir / "ext_tools" / "clingo" / "clingo.exe",
            tweety_dir.parent / "Argument_Analysis" / "ext_tools" / "clingo" / "clingo.exe",
        ]
        for clingo_path in local_clingo_paths:
            if clingo_path.exists():
                env.clingo_installed = True
                env.clingo_version = "local"
                break

    # Check SPASS (optional)
    spass_path = shutil.which("SPASS")
    if spass_path:
        env.spass_installed = True
    else:
        local_spass_paths = [
            tweety_dir / "ext_tools" / "spass" / "SPASS.exe",
            tweety_dir.parent / "Argument_Analysis" / "ext_tools" / "spass" / "SPASS.exe",
        ]
        for spass_path in local_spass_paths:
            if spass_path.exists():
                env.spass_installed = True
                break

    # Check EProver (optional but valuable for FOL reasoning)
    eprover_path = shutil.which("eprover")
    if eprover_path:
        env.eprover_installed = True
        env.eprover_path = eprover_path
    else:
        local_eprover_paths = [
            tweety_dir.parent / "ext_tools" / "EProver" / "eprover.exe",
            tweety_dir.parent / "Argument_Analysis" / "ext_tools" / "EProver" / "eprover.exe",
        ]
        for ep_path in local_eprover_paths:
            if ep_path.exists():
                env.eprover_installed = True
                env.eprover_path = str(ep_path)
                break

    # Check native SAT libraries (lingeling, minisat, picosat)
    native_libs_paths = [
        tweety_dir.parent / "libs" / "native",
        tweety_dir / "libs" / "native",
    ]
    for libs_path in native_libs_paths:
        if libs_path.exists():
            env.sat_libs_path = str(libs_path)
            # Check for each SAT solver library
            for solver in ["lingeling", "minisat", "picosat"]:
                dll_path = libs_path / f"{solver}.dll"
                so_path = libs_path / f"{solver}.so"
                if dll_path.exists() or so_path.exists():
                    env.sat_libs_found.append(solver)
            break

    return env


def validate_notebook_structure(notebook_path: Path) -> NotebookValidation:
    """Validate notebook structure without execution"""
    validation = NotebookValidation(name=notebook_path.name)

    if not notebook_path.exists():
        return validation

    validation.exists = True

    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
        validation.valid_json = True
    except json.JSONDecodeError as e:
        validation.errors.append(f"Invalid JSON: {e}")
        return validation
    except Exception as e:
        validation.errors.append(f"Could not read file: {e}")
        return validation

    # Check cells
    cells = nb.get('cells', [])
    if cells:
        validation.has_cells = True
        validation.total_cells = len(cells)

        for cell in cells:
            cell_type = cell.get('cell_type', '')
            if cell_type == 'markdown':
                validation.markdown_cells += 1
            elif cell_type == 'code':
                validation.code_cells += 1
    else:
        validation.errors.append("No cells found in notebook")

    # Check metadata
    metadata = nb.get('metadata', {})
    if metadata:
        validation.has_metadata = True

        # Check kernel
        kernelspec = metadata.get('kernelspec', {})
        kernel_name = kernelspec.get('name', '')
        kernel_language = kernelspec.get('language', '')

        if kernel_name == EXPECTED_KERNEL['name'] or kernel_language == EXPECTED_KERNEL['language']:
            validation.kernel_correct = True
        else:
            validation.warnings.append(f"Unexpected kernel: {kernel_name} ({kernel_language})")
    else:
        validation.warnings.append("No metadata found")

    # Check for navigation links
    has_navigation = False
    for cell in cells:
        if cell.get('cell_type') == 'markdown':
            source = ''.join(cell.get('source', []))
            if 'Navigation' in source or 'Precedent' in source or 'Suivant' in source:
                has_navigation = True
                break

    if not has_navigation:
        validation.warnings.append("No navigation links found")

    return validation


def execute_with_papermill(notebook_path: Path, timeout: int = 600) -> Dict[str, Any]:
    """Execute notebook with Papermill"""
    output_path = notebook_path.with_suffix('.verified.ipynb')

    cmd = [
        sys.executable, '-m', 'papermill',
        str(notebook_path), str(output_path),
        '--kernel', 'python3',
        '--cwd', str(notebook_path.parent),
    ]

    start_time = time.time()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(notebook_path.parent)
        )
        execution_time = time.time() - start_time

        return {
            'success': result.returncode == 0,
            'returncode': result.returncode,
            'stdout': result.stdout,
            'stderr': result.stderr,
            'output_path': str(output_path),
            'execution_time': execution_time,
        }
    except subprocess.TimeoutExpired:
        return {
            'success': False,
            'error': f'Timeout after {timeout}s',
            'execution_time': timeout,
        }
    except Exception as e:
        return {
            'success': False,
            'error': str(e),
            'execution_time': time.time() - start_time,
        }


def execute_cell_by_cell(notebook_path: Path, timeout: int = 120, verbose: bool = False) -> List[CellResult]:
    """Execute notebook cell by cell using jupyter_client"""
    results = []

    try:
        import jupyter_client
    except ImportError:
        return [CellResult(
            index=0,
            cell_type="error",
            success=False,
            error="jupyter_client not installed: pip install jupyter_client"
        )]

    # Load notebook
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
    except Exception as e:
        return [CellResult(index=0, cell_type="error", success=False, error=str(e))]

    cells = nb.get('cells', [])

    # Start kernel
    try:
        km = jupyter_client.KernelManager(kernel_name='python3')
        km.start_kernel(cwd=str(notebook_path.parent))
        kc = km.client()
        kc.start_channels()
        kc.wait_for_ready(timeout=60)
    except Exception as e:
        return [CellResult(index=0, cell_type="error", success=False, error=f"Kernel start failed: {e}")]

    try:
        # Set working directory
        cwd_code = f"import os; os.chdir(r'{notebook_path.parent}')"
        kc.execute(cwd_code)
        kc.get_shell_msg(timeout=10)

        # Execute each code cell
        for i, cell in enumerate(cells):
            if cell.get('cell_type') != 'code':
                results.append(CellResult(
                    index=i,
                    cell_type=cell.get('cell_type', 'unknown'),
                    success=True
                ))
                continue

            source = ''.join(cell.get('source', []))
            if not source.strip():
                results.append(CellResult(
                    index=i,
                    cell_type='code',
                    success=True,
                    output_preview="(empty cell)"
                ))
                continue

            start_time = time.time()
            cell_result = CellResult(index=i, cell_type='code', success=True)

            try:
                msg_id = kc.execute(source)

                # Wait for completion
                while True:
                    try:
                        msg = kc.get_iopub_msg(timeout=timeout)
                        msg_type = msg.get('msg_type', '')
                        content = msg.get('content', {})

                        if msg_type == 'error':
                            cell_result.success = False
                            ename = content.get('ename', 'Error')
                            evalue = content.get('evalue', '')
                            cell_result.error = f"{ename}: {evalue}"
                            break
                        elif msg_type == 'stream':
                            text = content.get('text', '')
                            if not cell_result.output_preview:
                                cell_result.output_preview = text[:200]
                        elif msg_type == 'status':
                            if content.get('execution_state') == 'idle':
                                break

                    except Exception as e:
                        if 'Timeout' in str(type(e).__name__):
                            cell_result.success = False
                            cell_result.error = f"Timeout after {timeout}s"
                        break

                cell_result.execution_time = time.time() - start_time

            except Exception as e:
                cell_result.success = False
                cell_result.error = str(e)
                cell_result.execution_time = time.time() - start_time

            results.append(cell_result)

            if verbose:
                status = "OK" if cell_result.success else "FAIL"
                print(f"  Cell {i}: [{status}] {cell_result.execution_time:.1f}s", end="")
                if cell_result.error:
                    print(f" - {cell_result.error[:50]}")
                else:
                    print()

    finally:
        # Cleanup
        try:
            kc.stop_channels()
            km.shutdown_kernel(now=True)
        except Exception:
            pass

    return results


def analyze_executed_notebook(notebook_path: Path) -> Dict[str, Any]:
    """Analyze an executed notebook for errors and warnings"""
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
    except Exception as e:
        return {'error': str(e)}

    issues = {
        'errors': [],
        'warnings': [],
        'java_warnings': [],
    }

    code_cells = 0
    successful_cells = 0

    for i, cell in enumerate(nb.get('cells', [])):
        if cell.get('cell_type') != 'code':
            continue

        code_cells += 1
        outputs = cell.get('outputs', [])
        has_error = False

        for output in outputs:
            output_type = output.get('output_type', '')

            if output_type == 'error':
                has_error = True
                issues['errors'].append({
                    'cell': i,
                    'ename': output.get('ename'),
                    'evalue': output.get('evalue'),
                })
            elif output_type == 'stream':
                text = ''.join(output.get('text', []))

                # Check for Java/Tweety warnings
                if 'No default MUS enumerator' in text or 'No default SAT solver' in text:
                    issues['java_warnings'].append({'cell': i, 'text': text[:100]})

                # Check for Python errors in output
                if 'Traceback' in text or 'Error:' in text:
                    issues['warnings'].append({'cell': i, 'text': text[:200]})

        if not has_error:
            successful_cells += 1

    return {
        'code_cells': code_cells,
        'successful_cells': successful_cells,
        'issues': issues,
    }


def main():
    parser = argparse.ArgumentParser(
        description='Verify Tweety notebooks',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('--quick', action='store_true',
                        help='Structure validation only (no execution)')
    parser.add_argument('--check-env', action='store_true',
                        help='Check if Tweety environment is properly configured')
    parser.add_argument('--execute', action='store_true',
                        help='Execute notebooks with Papermill')
    parser.add_argument('--cell-by-cell', action='store_true',
                        help='Execute notebooks cell by cell')
    parser.add_argument('--notebook', type=str,
                        help='Execute only specified notebook(s), comma-separated')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Verbose output')
    parser.add_argument('--json', action='store_true',
                        help='Output results as JSON')
    parser.add_argument('--timeout', type=int, default=120,
                        help='Timeout per notebook/cell in seconds (default: 120)')

    args = parser.parse_args()

    # Get directories
    repo_root = get_repo_root()
    tweety_dir = get_tweety_directory(repo_root)

    if not tweety_dir.exists():
        print(f"ERROR: Tweety directory not found: {tweety_dir}")
        sys.exit(1)

    # Create report
    report = TweetyVerificationReport(
        timestamp=datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        tweety_directory=str(tweety_dir)
    )

    # Check environment
    if args.check_env or not args.quick:
        report.environment = check_environment(tweety_dir)

    # Determine which notebooks to check
    notebooks_to_check = TWEETY_NOTEBOOKS.copy()
    if args.notebook:
        specified = [n.strip() for n in args.notebook.split(',')]
        notebooks_to_check = []
        for spec in specified:
            for nb in TWEETY_NOTEBOOKS:
                if spec in nb:
                    notebooks_to_check.append(nb)
                    break

    # Validate notebook structure
    for notebook_name in notebooks_to_check:
        notebook_path = tweety_dir / notebook_name
        validation = validate_notebook_structure(notebook_path)
        report.notebooks.append(validation)

    # Check support files
    libs_path = find_libs_directory(tweety_dir)
    report.support_files['libs/'] = libs_path is not None

    # Execute notebooks if requested
    if args.execute or args.cell_by_cell:
        if not args.json:
            print("\n--- Execution ---")

        for validation in report.notebooks:
            if not validation.exists:
                report.execution_results[validation.name] = "SKIPPED"
                continue

            notebook_path = tweety_dir / validation.name

            if not args.json:
                print(f"\nExecuting: {validation.name}")

            if args.cell_by_cell:
                # Cell-by-cell execution
                cell_results = execute_cell_by_cell(
                    notebook_path,
                    timeout=args.timeout,
                    verbose=args.verbose
                )
                validation.cell_results = cell_results

                failed_cells = [c for c in cell_results if not c.success and c.cell_type == 'code']
                if failed_cells:
                    validation.errors.extend([f"Cell {c.index}: {c.error}" for c in failed_cells[:3]])
                    report.execution_results[validation.name] = f"FAIL ({len(failed_cells)} cells)"
                else:
                    report.execution_results[validation.name] = "OK"

                validation.execution_time = sum(c.execution_time for c in cell_results)

            else:
                # Papermill execution
                result = execute_with_papermill(notebook_path, timeout=args.timeout * 5)
                validation.execution_time = result.get('execution_time', 0)

                if result.get('success'):
                    report.execution_results[validation.name] = "OK"

                    # Analyze executed notebook
                    output_path = Path(result.get('output_path', ''))
                    if output_path.exists():
                        analysis = analyze_executed_notebook(output_path)
                        if analysis.get('issues', {}).get('errors'):
                            validation.errors.extend([
                                f"Cell {e['cell']}: {e['ename']}: {e['evalue']}"
                                for e in analysis['issues']['errors'][:3]
                            ])
                else:
                    error = result.get('error', result.get('stderr', 'Unknown error'))
                    validation.errors.append(error[:200] if isinstance(error, str) else str(error)[:200])
                    report.execution_results[validation.name] = "FAIL"

    # Output results
    if args.json:
        print(json.dumps(report.to_dict(), indent=2))
    else:
        report.print_summary(verbose=args.verbose)

    # Exit code
    if report.error_count > 0:
        sys.exit(1)
    sys.exit(0)


if __name__ == '__main__':
    main()
