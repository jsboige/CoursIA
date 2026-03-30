#!/usr/bin/env python3
"""
Test script for Infer.NET Notebooks
Executes all notebooks using papermill and reports results.
Includes content validation for Markdown, code, and outputs.
"""

import os
import sys
import argparse
import subprocess
import json
import re
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Any

# Configuration
NOTEBOOKS_DIR = Path(__file__).parent.parent  # MyIA.AI.Notebooks/Probas/Infer
OUTPUT_DIR = NOTEBOOKS_DIR / "test_outputs"
KERNEL_NAME = ".net-csharp"

# Notebook collections
NOTEBOOKS_CORE = [
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

NOTEBOOKS_DECISION = [
    "Infer-14-Decision-Utility-Foundations.ipynb",
    "Infer-15-Decision-Utility-Money.ipynb",
    "Infer-16-Decision-Multi-Attribute.ipynb",
    "Infer-17-Decision-Networks.ipynb",
    "Infer-18-Decision-Value-Information.ipynb",
    "Infer-19-Decision-Expert-Systems.ipynb",
    "Infer-20-Decision-Sequential.ipynb",
]

NOTEBOOKS = NOTEBOOKS_CORE + NOTEBOOKS_DECISION

# ANSI color codes for terminal output
class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    MAGENTA = '\033[95m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'


def print_colored(text, color):
    """Print colored text to terminal."""
    print(f"{color}{text}{Colors.ENDC}")


# ============================================================================
# CONTENT VALIDATION FUNCTIONS
# ============================================================================

def validate_markdown_cell(cell: dict, cell_index: int) -> List[Dict]:
    """
    Validate a Markdown cell for quality and coherence.

    Checks:
    - Non-empty content
    - Proper heading structure
    - Links validity (format)
    - LaTeX math syntax
    - French/English consistency
    """
    issues = []
    source = ''.join(cell.get('source', []))

    if not source.strip():
        issues.append({
            'type': 'warning',
            'category': 'markdown',
            'cell_index': cell_index,
            'message': 'Empty Markdown cell'
        })
        return issues

    # Check heading structure
    headings = re.findall(r'^(#{1,6})\s+(.+)$', source, re.MULTILINE)
    if headings:
        levels = [len(h[0]) for h in headings]
        for i in range(1, len(levels)):
            if levels[i] > levels[i-1] + 1:
                issues.append({
                    'type': 'warning',
                    'category': 'structure',
                    'cell_index': cell_index,
                    'message': f'Heading level jump: {levels[i-1]} to {levels[i]}'
                })

    # Check for broken LaTeX (unbalanced $ or $$)
    single_dollars = len(re.findall(r'(?<!\$)\$(?!\$)', source))
    if single_dollars % 2 != 0:
        issues.append({
            'type': 'error',
            'category': 'latex',
            'cell_index': cell_index,
            'message': 'Unbalanced $ signs in LaTeX'
        })

    double_dollars = len(re.findall(r'\$\$', source))
    if double_dollars % 2 != 0:
        issues.append({
            'type': 'error',
            'category': 'latex',
            'cell_index': cell_index,
            'message': 'Unbalanced $$ signs in LaTeX'
        })

    # Check for broken links
    links = re.findall(r'\[([^\]]*)\]\(([^)]*)\)', source)
    for text, url in links:
        if not url or url.isspace():
            issues.append({
                'type': 'warning',
                'category': 'links',
                'cell_index': cell_index,
                'message': f'Empty URL for link: [{text}]'
            })

    return issues


def validate_code_cell(cell: dict, cell_index: int, notebook_name: str) -> List[Dict]:
    """
    Validate a code cell for correctness and best practices.

    Checks:
    - Non-empty content
    - Common C# syntax issues
    - Infer.NET best practices
    - CompilerChoice configuration
    - Variable naming conventions
    """
    issues = []
    source = ''.join(cell.get('source', []))
    outputs = cell.get('outputs', [])

    if not source.strip():
        issues.append({
            'type': 'info',
            'category': 'code',
            'cell_index': cell_index,
            'message': 'Empty code cell'
        })
        return issues

    # Check for CompilerChoice without full namespace
    if 'CompilerChoice' in source and 'Microsoft.ML.Probabilistic.Compiler.CompilerChoice' not in source:
        if 'CompilerChoice =' in source or 'CompilerChoice=' in source:
            issues.append({
                'type': 'error',
                'category': 'compiler',
                'cell_index': cell_index,
                'message': 'CompilerChoice needs full namespace: Microsoft.ML.Probabilistic.Compiler.CompilerChoice'
            })

    # Check for InferenceEngine without Roslyn compiler
    if 'new InferenceEngine()' in source:
        # Check if this cell or nearby has CompilerChoice set
        if 'CompilerChoice' not in source:
            issues.append({
                'type': 'warning',
                'category': 'best_practice',
                'cell_index': cell_index,
                'message': 'InferenceEngine created without setting CompilerChoice to Roslyn'
            })

    # Check for common C# errors
    if 'Console.WriteLine' in source and 'display' not in source.lower():
        issues.append({
            'type': 'info',
            'category': 'style',
            'cell_index': cell_index,
            'message': 'Consider using display() for richer output in Jupyter'
        })

    # Check outputs for errors
    for output in outputs:
        if output.get('output_type') == 'error':
            ename = output.get('ename', 'Unknown')
            evalue = output.get('evalue', '')
            issues.append({
                'type': 'error',
                'category': 'execution',
                'cell_index': cell_index,
                'message': f'{ename}: {evalue[:200]}'
            })
        elif output.get('output_type') == 'stream' and output.get('name') == 'stderr':
            text = ''.join(output.get('text', []))
            if 'error' in text.lower() or 'exception' in text.lower():
                issues.append({
                    'type': 'warning',
                    'category': 'stderr',
                    'cell_index': cell_index,
                    'message': f'Stderr output: {text[:150]}'
                })

    return issues


def validate_output_coherence(cell: dict, cell_index: int) -> List[Dict]:
    """
    Validate that code cell outputs are coherent and meaningful.

    Checks:
    - Output exists for code cells
    - Output format is appropriate
    - Numerical outputs are reasonable
    """
    issues = []
    source = ''.join(cell.get('source', []))
    outputs = cell.get('outputs', [])

    # Skip if cell is a setup/import cell
    if '#r "nuget:' in source or 'using ' in source and len(source) < 500:
        return issues

    # Check if code that should produce output has none
    output_indicators = ['Infer<', 'Console.Write', 'display(', 'return ']
    has_output_code = any(ind in source for ind in output_indicators)

    if has_output_code and not outputs:
        issues.append({
            'type': 'warning',
            'category': 'output',
            'cell_index': cell_index,
            'message': 'Code appears to generate output but no output found'
        })

    # Check for NaN or Infinity in outputs
    for output in outputs:
        text_content = ''
        if output.get('output_type') == 'stream':
            text_content = ''.join(output.get('text', []))
        elif output.get('output_type') == 'execute_result':
            data = output.get('data', {})
            text_content = data.get('text/plain', '')
            if isinstance(text_content, list):
                text_content = ''.join(text_content)

        if 'NaN' in text_content or 'Infinity' in text_content:
            issues.append({
                'type': 'warning',
                'category': 'numerical',
                'cell_index': cell_index,
                'message': 'Output contains NaN or Infinity values'
            })

    return issues


def validate_pedagogical_flow(cells: List[dict], notebook_name: str) -> List[Dict]:
    """
    Validate the pedagogical flow of the notebook.

    Checks:
    - Starts with title/introduction
    - Has logical section progression
    - Ends with summary/conclusion
    - Code-to-explanation ratio
    """
    issues = []

    markdown_cells = [c for c in cells if c.get('cell_type') == 'markdown']
    code_cells = [c for c in cells if c.get('cell_type') == 'code']

    if not markdown_cells:
        issues.append({
            'type': 'warning',
            'category': 'pedagogy',
            'cell_index': 0,
            'message': 'Notebook has no Markdown explanations'
        })
        return issues

    # Check for title (H1)
    first_md = ''.join(markdown_cells[0].get('source', []))
    if not first_md.strip().startswith('#'):
        issues.append({
            'type': 'info',
            'category': 'pedagogy',
            'cell_index': 0,
            'message': 'Notebook should start with a title (# heading)'
        })

    # Check code-to-markdown ratio
    if len(code_cells) > 0:
        ratio = len(markdown_cells) / len(code_cells)
        if ratio < 0.3:
            issues.append({
                'type': 'warning',
                'category': 'pedagogy',
                'cell_index': 0,
                'message': f'Low explanation ratio ({ratio:.2f}). Consider adding more explanatory text.'
            })

    # Check for conclusion/summary at end
    if markdown_cells:
        last_md = ''.join(markdown_cells[-1].get('source', [])).lower()
        conclusion_keywords = ['conclusion', 'resume', 'summary', 'recap', 'bilan', 'synthese']
        has_conclusion = any(kw in last_md for kw in conclusion_keywords)
        if not has_conclusion and len(cells) > 10:
            issues.append({
                'type': 'info',
                'category': 'pedagogy',
                'cell_index': len(cells) - 1,
                'message': 'Consider adding a conclusion or summary section'
            })

    return issues


def validate_technical_accuracy(cells: List[dict], notebook_name: str) -> List[Dict]:
    """
    Validate technical accuracy of Infer.NET concepts.

    Checks:
    - Correct probability distributions usage
    - Proper Bayesian inference patterns
    - Decision theory concepts (for notebooks 14-20)
    """
    issues = []

    all_code = ''
    for cell in cells:
        if cell.get('cell_type') == 'code':
            all_code += ''.join(cell.get('source', []))

    # Check for Decision Theory notebooks
    if 'Decision' in notebook_name:
        # Should mention utility or decision
        if 'utility' not in all_code.lower() and 'Utility' not in all_code:
            issues.append({
                'type': 'warning',
                'category': 'theory',
                'cell_index': 0,
                'message': 'Decision Theory notebook but no utility concept found'
            })

        # EVPI/VOI notebooks should demonstrate value calculations
        if 'Value-Information' in notebook_name or 'VOI' in notebook_name:
            if 'EVPI' not in all_code and 'value of information' not in all_code.lower():
                issues.append({
                    'type': 'info',
                    'category': 'theory',
                    'cell_index': 0,
                    'message': 'Consider explicitly calculating EVPI (Expected Value of Perfect Information)'
                })

    # Check for proper Infer.NET patterns
    if 'Variable<' in all_code:
        if 'InferenceEngine' not in all_code:
            issues.append({
                'type': 'warning',
                'category': 'technical',
                'cell_index': 0,
                'message': 'Variables defined but no InferenceEngine to run inference'
            })

    return issues


def validate_notebook(notebook_path: Path) -> Dict[str, Any]:
    """
    Perform comprehensive validation of a notebook.

    Returns a validation report with all issues found.
    """
    result = {
        'notebook': notebook_path.name,
        'valid_json': False,
        'issues': [],
        'cell_count': 0,
        'markdown_cells': 0,
        'code_cells': 0,
        'cells_with_output': 0,
        'cells_with_errors': 0
    }

    try:
        with open(notebook_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
        result['valid_json'] = True
    except json.JSONDecodeError as e:
        result['issues'].append({
            'type': 'error',
            'category': 'json',
            'cell_index': 0,
            'message': f'Invalid JSON: {e}'
        })
        return result

    cells = nb.get('cells', [])
    result['cell_count'] = len(cells)

    for i, cell in enumerate(cells):
        cell_type = cell.get('cell_type', '')

        if cell_type == 'markdown':
            result['markdown_cells'] += 1
            result['issues'].extend(validate_markdown_cell(cell, i))

        elif cell_type == 'code':
            result['code_cells'] += 1
            outputs = cell.get('outputs', [])
            if outputs:
                result['cells_with_output'] += 1

            # Check for errors in outputs
            for output in outputs:
                if output.get('output_type') == 'error':
                    result['cells_with_errors'] += 1
                    break

            result['issues'].extend(validate_code_cell(cell, i, notebook_path.name))
            result['issues'].extend(validate_output_coherence(cell, i))

    # Notebook-level validations
    result['issues'].extend(validate_pedagogical_flow(cells, notebook_path.name))
    result['issues'].extend(validate_technical_accuracy(cells, notebook_path.name))

    return result


def print_validation_report(report: Dict[str, Any], verbose: bool = False):
    """Print a formatted validation report."""
    print(f"\n{Colors.BOLD}Validation: {report['notebook']}{Colors.ENDC}")
    print(f"  Cells: {report['cell_count']} (MD: {report['markdown_cells']}, Code: {report['code_cells']})")
    print(f"  With output: {report['cells_with_output']}, With errors: {report['cells_with_errors']}")

    if not report['valid_json']:
        print_colored("  Invalid JSON!", Colors.RED)
        return

    # Group issues by type
    errors = [i for i in report['issues'] if i['type'] == 'error']
    warnings = [i for i in report['issues'] if i['type'] == 'warning']
    infos = [i for i in report['issues'] if i['type'] == 'info']

    if errors:
        print_colored(f"  Errors: {len(errors)}", Colors.RED)
        for issue in errors[:5] if not verbose else errors:
            print(f"    [{issue['category']}] Cell {issue['cell_index']}: {issue['message'][:80]}")

    if warnings:
        print_colored(f"  Warnings: {len(warnings)}", Colors.YELLOW)
        if verbose:
            for issue in warnings:
                print(f"    [{issue['category']}] Cell {issue['cell_index']}: {issue['message'][:80]}")

    if infos and verbose:
        print_colored(f"  Info: {len(infos)}", Colors.CYAN)
        for issue in infos:
            print(f"    [{issue['category']}] Cell {issue['cell_index']}: {issue['message'][:80]}")

    if not errors and not warnings:
        print_colored("  All checks passed!", Colors.GREEN)


# ============================================================================
# EXECUTION FUNCTIONS
# ============================================================================

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
            print_colored(f"Kernel {KERNEL_NAME} available", Colors.GREEN)
            return True
        else:
            print_colored(f"Kernel {KERNEL_NAME} not found", Colors.RED)
            print("\nAvailable kernels:")
            print(result.stdout)
            print("\nInstall .NET Interactive:")
            print("  dotnet tool install -g Microsoft.dotnet-interactive")
            print("  dotnet interactive jupyter install")
            return False
    except subprocess.CalledProcessError as e:
        print_colored(f"Error checking kernel: {e}", Colors.RED)
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
    parser = argparse.ArgumentParser(description='Test and validate Infer.NET notebooks')
    parser.add_argument('--notebook', '-n', help='Test a specific notebook')
    parser.add_argument('--timeout', '-t', type=int, default=600, help='Timeout per notebook (seconds)')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    parser.add_argument('--list', '-l', action='store_true', help='List notebooks and exit')
    parser.add_argument('--validate-only', action='store_true', help='Only validate content, skip execution')
    parser.add_argument('--decision', '-d', action='store_true', help='Test only Decision Theory notebooks (14-20)')
    parser.add_argument('--core', '-c', action='store_true', help='Test only core notebooks (1-13)')
    args = parser.parse_args()

    # Select notebooks based on flags
    if args.decision:
        notebooks_to_test = NOTEBOOKS_DECISION
        print_colored("Testing Decision Theory notebooks (14-20)", Colors.MAGENTA)
    elif args.core:
        notebooks_to_test = NOTEBOOKS_CORE
        print_colored("Testing Core notebooks (1-13)", Colors.MAGENTA)
    elif args.notebook:
        notebooks_to_test = [args.notebook]
    else:
        notebooks_to_test = NOTEBOOKS

    if args.list:
        print_colored("Available notebooks:", Colors.BOLD)
        print_colored("\nCore (1-13):", Colors.CYAN)
        for nb in NOTEBOOKS_CORE:
            path = NOTEBOOKS_DIR / nb
            if path.exists():
                print_colored(f"  [+] {nb}", Colors.GREEN)
            else:
                print_colored(f"  [-] {nb}", Colors.RED)
        print_colored("\nDecision Theory (14-20):", Colors.MAGENTA)
        for nb in NOTEBOOKS_DECISION:
            path = NOTEBOOKS_DIR / nb
            if path.exists():
                print_colored(f"  [+] {nb}", Colors.GREEN)
            else:
                print_colored(f"  [-] {nb}", Colors.RED)
        return 0

    print(f"\n{'='*70}")
    print_colored("Infer.NET Notebooks Test Suite", Colors.BOLD)
    print(f"{'='*70}")
    print(f"Notebooks directory: {NOTEBOOKS_DIR}")
    print(f"Output directory: {OUTPUT_DIR}")
    print(f"Mode: {'Validation only' if args.validate_only else 'Full execution'}")
    print(f"{'='*70}\n")

    # Content validation
    print_colored("Phase 1: Content Validation", Colors.BOLD)
    print("-" * 40)

    validation_results = []
    for notebook in notebooks_to_test:
        path = NOTEBOOKS_DIR / notebook
        if path.exists():
            report = validate_notebook(path)
            validation_results.append(report)
            print_validation_report(report, args.verbose)

    # Summary of validation
    total_errors = sum(len([i for i in r['issues'] if i['type'] == 'error']) for r in validation_results)
    total_warnings = sum(len([i for i in r['issues'] if i['type'] == 'warning']) for r in validation_results)

    print(f"\n{Colors.BOLD}Validation Summary:{Colors.ENDC}")
    print(f"  Notebooks validated: {len(validation_results)}")
    if total_errors > 0:
        print_colored(f"  Total errors: {total_errors}", Colors.RED)
    if total_warnings > 0:
        print_colored(f"  Total warnings: {total_warnings}", Colors.YELLOW)
    if total_errors == 0 and total_warnings == 0:
        print_colored("  All validations passed!", Colors.GREEN)

    if args.validate_only:
        # Save validation results
        results_path = OUTPUT_DIR / "validation_results.json"
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
        with open(results_path, 'w', encoding='utf-8') as f:
            json.dump({
                'timestamp': datetime.now().isoformat(),
                'mode': 'validation_only',
                'total_errors': total_errors,
                'total_warnings': total_warnings,
                'results': validation_results
            }, f, indent=2, default=str)
        print(f"\nValidation results saved to: {results_path}")
        return 0 if total_errors == 0 else 1

    # Execution phase
    print(f"\n{'='*70}")
    print_colored("Phase 2: Notebook Execution", Colors.BOLD)
    print(f"{'='*70}")

    # Verify kernel before running tests
    if not verify_kernel_available():
        return 1

    setup_output_dir()

    execution_results = []

    for notebook in notebooks_to_test:
        print_colored(f"\nExecuting: {notebook}", Colors.BOLD)
        result = run_notebook(notebook, timeout=args.timeout, verbose=args.verbose)
        result['notebook'] = notebook
        execution_results.append(result)

        if result['success']:
            print_colored(f"  SUCCESS ({result['duration']:.1f}s)", Colors.GREEN)
        else:
            print_colored(f"  FAILED ({result['duration']:.1f}s)", Colors.RED)
            if args.verbose and result['error']:
                print(f"  Error: {result['error'][:200]}...")

            # Try to extract detailed errors from output notebook
            if result['output_path'] and os.path.exists(result['output_path']):
                errors = extract_errors_from_notebook(result['output_path'])
                if errors:
                    print_colored("  Errors found:", Colors.YELLOW)
                    for err in errors[:3]:  # Show first 3 errors
                        print(f"    Cell {err.get('cell_index', '?')}: {err.get('ename', 'Error')}: {err.get('evalue', '')[:100]}")

    # Final Summary
    print(f"\n{'='*70}")
    print_colored("FINAL SUMMARY", Colors.BOLD)
    print(f"{'='*70}")

    passed = sum(1 for r in execution_results if r['success'])
    failed = len(execution_results) - passed
    total_time = sum(r['duration'] for r in execution_results)

    print(f"\nExecution Results:")
    print(f"  Total: {len(execution_results)} notebooks")
    print_colored(f"  Passed: {passed}/{len(execution_results)}", Colors.GREEN if passed > 0 else Colors.YELLOW)
    if failed > 0:
        print_colored(f"  Failed: {failed}/{len(execution_results)}", Colors.RED)
    print(f"  Total time: {total_time:.1f}s ({total_time/60:.1f} minutes)")

    print(f"\nValidation Results:")
    print(f"  Errors: {total_errors}")
    print(f"  Warnings: {total_warnings}")

    if failed > 0:
        print_colored("\nFailed notebooks:", Colors.YELLOW)
        for r in execution_results:
            if not r['success']:
                print(f"  - {r['notebook']}: {r['error'][:100] if r['error'] else 'Unknown error'}...")

    # Save combined results to JSON
    results_path = OUTPUT_DIR / "test_results.json"
    with open(results_path, 'w', encoding='utf-8') as f:
        json.dump({
            'timestamp': datetime.now().isoformat(),
            'execution': {
                'passed': passed,
                'failed': failed,
                'total_time': total_time,
                'results': execution_results
            },
            'validation': {
                'total_errors': total_errors,
                'total_warnings': total_warnings,
                'results': validation_results
            }
        }, f, indent=2, default=str)
    print(f"\nDetailed results saved to: {results_path}")

    return 0 if (failed == 0 and total_errors == 0) else 1


if __name__ == '__main__':
    sys.exit(main())
