"""
Validation report for Texte series notebooks.
Checks which notebooks have outputs and which don't.
"""
import json
from pathlib import Path
from datetime import datetime

def check_notebook_outputs(notebook_path):
    """Check if a notebook has valid outputs."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    code_cells = [c for c in nb.get('cells', []) if c.get('cell_type') == 'code']
    cells_with_output = [c for c in code_cells if c.get('outputs')]

    return {
        'total_cells': len(nb.get('cells', [])),
        'code_cells': len(code_cells),
        'cells_with_output': len(cells_with_output),
        'has_outputs': len(cells_with_output) > 0,
        'fully_executed': len(cells_with_output) == len(code_cells) if code_cells else False,
        'output_ratio': len(cells_with_output) / len(code_cells) if code_cells else 0
    }

def main():
    texte_dir = Path("MyIA.AI.Notebooks/GenAI/Texte")
    notebooks = sorted(texte_dir.glob("*.ipynb"))
    # Filter out output files
    notebooks = [nb for nb in notebooks if not nb.name.endswith('_output.ipynb')]

    print(f"Validating {len(notebooks)} notebooks in Texte series...\n")

    results = {}
    output_files = {}

    # Check for output files
    for nb_path in notebooks:
        base_name = nb_path.stem
        output_file = texte_dir / f"{base_name}_output.ipynb"
        output_files[base_name] = output_file.exists()

    for nb_path in notebooks:
        stats = check_notebook_outputs(nb_path)
        base_name = nb_path.stem
        results[base_name] = stats
        stats['has_output_file'] = output_files[base_name]

    # Print summary table
    print("=" * 100)
    print(f"{'Notebook':<40} | {'Code':<4} | {'Out':<4} | {'%':<6} | {'Output File':<12} | {'Status'}")
    print("=" * 100)

    for name in sorted(results.keys()):
        stats = results[name]
        pct = stats['output_ratio'] * 100
        status = "OK" if stats['has_outputs'] else "NO OUTPUTS"
        if stats['fully_executed']:
            status = "FULL"
        of = "YES" if stats['has_output_file'] else "NO"
        print(f"{name:<40} | {stats['code_cells']:<4} | {stats['cells_with_output']:<4} | {pct:<5.0f}% | {of:<12} | {status}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)

    with_outputs = sum(1 for v in results.values() if v['has_outputs'])
    fully_executed = sum(1 for v in results.values() if v['fully_executed'])
    no_outputs = len(results) - with_outputs
    has_output_file = sum(1 for v in results.values() if v['has_output_file'])

    print(f"Total notebooks: {len(results)}")
    print(f"With outputs: {with_outputs}")
    print(f"Fully executed: {fully_executed}")
    print(f"No outputs: {no_outputs}")
    print(f"Has output file: {has_output_file}")

    if no_outputs > 0:
        print("\nNotebooks WITHOUT outputs:")
        for name, stats in results.items():
            if not stats['has_outputs']:
                has_file = " (has output file)" if stats['has_output_file'] else ""
                print(f"  - {name}{has_file}")

    # Check if we can copy output files to fix missing outputs
    print("\n" + "=" * 100)
    print("RECOMMENDATIONS")
    print("=" * 100)

    missing_outputs = []
    for name, stats in results.items():
        if not stats['has_outputs'] and stats['has_output_file']:
            missing_outputs.append(name)

    if missing_outputs:
        print(f"\n{len(missing_outputs)} notebooks can be fixed by copying output files:")
        for name in missing_outputs:
            print(f"  - {name}.ipynb <- {name}_output.ipynb")
    else:
        print("\nAll notebooks that have output files already have outputs.")

    notebooks_needing_execution = []
    for name, stats in results.items():
        if not stats['has_outputs'] and not stats['has_output_file']:
            notebooks_needing_execution.append(name)

    if notebooks_needing_execution:
        print(f"\n{len(notebooks_needing_execution)} notebooks need execution:")
        for name in notebooks_needing_execution:
            print(f"  - {name}.ipynb")

    return {
        'total': len(results),
        'with_outputs': with_outputs,
        'fully_executed': fully_executed,
        'no_outputs': no_outputs,
        'has_output_file': has_output_file,
        'can_copy_outputs': len(missing_outputs),
        'needs_execution': len(notebooks_needing_execution)
    }

if __name__ == "__main__":
    stats = main()
    print(f"\nValidation rate: {stats['with_outputs']}/{stats['total']} = {stats['with_outputs']/stats['total']*100:.1f}%")
