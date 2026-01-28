#!/usr/bin/env python3
"""
Test script for Infer.NET Notebooks
Executes all notebooks using papermill and reports results.
"""

import os
import sys
import argparse
import subprocess
import json
from pathlib import Path
from datetime import datetime

# Configuration
NOTEBOOKS_DIR = Path(__file__).parent.parent  # MyIA.AI.Notebooks/Probas/Infer
OUTPUT_DIR = NOTEBOOKS_DIR / "test_outputs"
KERNEL_NAME = ".net-csharp"

NOTEBOOKS = [
    "Infer-1-Setup.ipynb",
    "Infer-2-Gaussian-Mixtures.ipynb",
    "Infer-3-Factor-Graphs.ipynb",
    "Infer-4-Bayesian-Networks.ipynb",
    "Infer-5-Skills-IRT.ipynb",
    "Infer-6-TrueSkill.ipynb",
    "Infer-7-Classification.ipynb",
    "Infer-8-Model-Selection.ipynb",
    "Infer-9-Topic-Models.ipynb",
    "Infer-10-Crowdsourcing.ipynb",
    "Infer-11-Sequences.ipynb",
    "Infer-12-Recommenders.ipynb",
    "Infer-13-Debugging.ipynb",
]

# ANSI color codes for terminal output
class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'


def print_colored(text, color):
    """Print colored text to terminal."""
    print(f"{color}{text}{Colors.ENDC}")


def verify_kernel_available():
    """Verify that the .NET kernel is available."""
    try:
        result = subprocess.run(
            ["jupyter", "kernelspec", "list"],
            capture_output=True,
            text=True,
            check=True
        )

        if KERNEL_NAME in result.stdout:
            print_colored(f"✓ Kernel {KERNEL_NAME} available", Colors.GREEN)
            return True
        else:
            print_colored(f"✗ Kernel {KERNEL_NAME} not found", Colors.RED)
            print("\nAvailable kernels:")
            print(result.stdout)
            print("\nInstall .NET Interactive:")
            print("  dotnet tool install -g Microsoft.dotnet-interactive")
            print("  dotnet interactive jupyter install")
            return False
    except subprocess.CalledProcessError as e:
        print_colored(f"✗ Error checking kernel: {e}", Colors.RED)
        return False


def setup_output_dir():
    """Create output directory if it doesn't exist."""
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    return OUTPUT_DIR


def run_notebook(notebook_name: str, timeout: int = 600, verbose: bool = False) -> dict:
    """
    Execute a notebook using papermill.

    Returns:
        dict with keys: success, output_path, error, duration
    """
    input_path = NOTEBOOKS_DIR / notebook_name
    output_path = OUTPUT_DIR / f"{notebook_name.replace('.ipynb', '_output.ipynb')}"

    if not input_path.exists():
        return {
            "success": False,
            "output_path": None,
            "error": f"Notebook not found: {input_path}",
            "duration": 0
        }

    start_time = datetime.now()

    cmd = [
        sys.executable, "-m", "papermill",
        str(input_path),
        str(output_path),
        "-k", KERNEL_NAME,
        "--cwd", str(NOTEBOOKS_DIR),
    ]

    if verbose:
        print(f"  Command: {' '.join(cmd)}")

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout
        )

        duration = (datetime.now() - start_time).total_seconds()

        if result.returncode == 0:
            return {
                "success": True,
                "output_path": str(output_path),
                "error": None,
                "duration": duration
            }
        else:
            return {
                "success": False,
                "output_path": str(output_path) if output_path.exists() else None,
                "error": result.stderr[-2000:] if result.stderr else "Unknown error",
                "duration": duration
            }

    except subprocess.TimeoutExpired:
        duration = (datetime.now() - start_time).total_seconds()
        return {
            "success": False,
            "output_path": None,
            "error": f"Timeout after {timeout}s",
            "duration": duration
        }
    except Exception as e:
        duration = (datetime.now() - start_time).total_seconds()
        return {
            "success": False,
            "output_path": None,
            "error": str(e),
            "duration": duration
        }


def extract_errors_from_notebook(notebook_path: str) -> list:
    """Extract error outputs from an executed notebook."""
    errors = []
    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)

        for i, cell in enumerate(nb.get('cells', [])):
            if cell.get('cell_type') == 'code':
                for output in cell.get('outputs', []):
                    if output.get('output_type') == 'error':
                        errors.append({
                            'cell_index': i,
                            'ename': output.get('ename', 'Unknown'),
                            'evalue': output.get('evalue', ''),
                            'traceback': '\n'.join(output.get('traceback', []))[-500:]
                        })
    except Exception as e:
        errors.append({'error': f'Could not parse notebook: {e}'})

    return errors


def main():
    parser = argparse.ArgumentParser(description='Test Infer.NET notebooks')
    parser.add_argument('--notebook', '-n', help='Test a specific notebook')
    parser.add_argument('--timeout', '-t', type=int, default=600, help='Timeout per notebook (seconds)')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    parser.add_argument('--list', '-l', action='store_true', help='List notebooks and exit')
    args = parser.parse_args()

    if args.list:
        print_colored("Available notebooks:", Colors.BOLD)
        for nb in NOTEBOOKS:
            path = NOTEBOOKS_DIR / nb
            if path.exists():
                print_colored(f"  [✓] {nb}", Colors.GREEN)
            else:
                print_colored(f"  [✗] {nb}", Colors.RED)
        return 0

    # Verify kernel before running tests
    if not verify_kernel_available():
        return 1

    setup_output_dir()

    notebooks_to_test = [args.notebook] if args.notebook else NOTEBOOKS

    print(f"\n{'='*60}")
    print_colored("Infer.NET Notebooks Test Suite", Colors.BOLD)
    print(f"{'='*60}")
    print(f"Notebooks directory: {NOTEBOOKS_DIR}")
    print(f"Output directory: {OUTPUT_DIR}")
    print(f"Kernel: {KERNEL_NAME}")
    print(f"Timeout: {args.timeout}s per notebook")
    print(f"{'='*60}\n")

    results = []

    for notebook in notebooks_to_test:
        print_colored(f"Testing: {notebook}", Colors.BOLD)
        result = run_notebook(notebook, timeout=args.timeout, verbose=args.verbose)
        result['notebook'] = notebook
        results.append(result)

        if result['success']:
            print_colored(f"  ✓ SUCCESS ({result['duration']:.1f}s)", Colors.GREEN)
        else:
            print_colored(f"  ✗ FAILED ({result['duration']:.1f}s)", Colors.RED)
            if args.verbose and result['error']:
                print(f"  Error: {result['error'][:200]}...")

            # Try to extract detailed errors from output notebook
            if result['output_path'] and os.path.exists(result['output_path']):
                errors = extract_errors_from_notebook(result['output_path'])
                if errors:
                    print_colored("  Errors found:", Colors.YELLOW)
                    for err in errors[:3]:  # Show first 3 errors
                        print(f"    Cell {err.get('cell_index', '?')}: {err.get('ename', 'Error')}: {err.get('evalue', '')[:100]}")

        print()

    # Summary
    print(f"\n{'='*60}")
    print_colored("SUMMARY", Colors.BOLD)
    print(f"{'='*60}")

    passed = sum(1 for r in results if r['success'])
    failed = len(results) - passed
    total_time = sum(r['duration'] for r in results)

    print(f"Total: {len(results)} notebooks")
    print_colored(f"✓ Passed: {passed}/{len(results)}", Colors.GREEN if passed > 0 else Colors.YELLOW)
    if failed > 0:
        print_colored(f"✗ Failed: {failed}/{len(results)}", Colors.RED)
    print(f"Total time: {total_time:.1f}s ({total_time/60:.1f} minutes)")

    if failed > 0:
        print_colored("\nFailed notebooks:", Colors.YELLOW)
        for r in results:
            if not r['success']:
                print(f"  - {r['notebook']}: {r['error'][:100] if r['error'] else 'Unknown error'}...")

    # Save results to JSON
    results_path = OUTPUT_DIR / "test_results.json"
    with open(results_path, 'w', encoding='utf-8') as f:
        json.dump({
            'timestamp': datetime.now().isoformat(),
            'passed': passed,
            'failed': failed,
            'total_time': total_time,
            'results': results
        }, f, indent=2)
    print(f"\nDetailed results saved to: {results_path}")

    return 0 if failed == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
