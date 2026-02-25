"""
Check quality of outputs in *_output.ipynb files.
Looks for errors, exceptions, and incomplete executions.
"""
import json
from pathlib import Path

def check_output_quality(notebook_path):
    """Check if outputs are valid (no errors, complete execution)."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    code_cells = [c for c in nb.get('cells', []) if c.get('cell_type') == 'code']
    issues = []

    for i, cell in enumerate(code_cells):
        outputs = cell.get('outputs', [])

        # Check for errors
        for output in outputs:
            if output.get('output_type') == 'error':
                issues.append(f"Cell {i+1}: Error - {output.get('ename', 'Unknown')}: {output.get('evalue', '')[:100]}")

            if 'traceback' in output:
                issues.append(f"Cell {i+1}: Traceback detected")

            # Check for stream errors
            if output.get('name') == 'stderr':
                content = output.get('text', [])
                if isinstance(content, list):
                    content = ''.join(content)
                if 'Error' in content or 'Exception' in content:
                    issues.append(f"Cell {i+1}: stderr output - {content[:100]}")

        # Check for papermill exceptions
        if outputs and any('papermill' in str(o).lower() for o in outputs):
            issues.append(f"Cell {i+1}: Papermill exception detected")

    return {
        'has_errors': len(issues) > 0,
        'issues': issues,
        'total_code_cells': len(code_cells),
        'cells_with_outputs': sum(1 for c in code_cells if c.get('outputs'))
    }

def main():
    texte_dir = Path("MyIA.AI.Notebooks/GenAI/Texte")
    output_files = sorted(texte_dir.glob("*_output.ipynb"))

    print(f"Checking quality of {len(output_files)} output files...\n")

    print("=" * 100)
    print(f"{'Output File':<45} | {'Code Cells':<10} | {'With Output':<12} | {'Status'}")
    print("=" * 100)

    results = {}
    for output_path in output_files:
        quality = check_output_quality(output_path)
        results[output_path.name] = quality

        status = "OK" if not quality['has_errors'] else f"ERRORS ({len(quality['issues'])})"
        print(f"{output_path.name:<45} | {quality['total_code_cells']:<10} | {quality['cells_with_outputs']:<12} | {status}")

        if quality['has_errors']:
            for issue in quality['issues']:
                print(f"  ! {issue}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)

    total = len(results)
    ok = sum(1 for v in results.values() if not v['has_errors'])
    errors = total - ok

    print(f"Total output files: {total}")
    print(f"OK: {ok}")
    print(f"With errors: {errors}")

    if errors > 0:
        print("\nFiles with issues:")
        for name, quality in results.items():
            if quality['has_errors']:
                print(f"  - {name}")

    return errors == 0

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
