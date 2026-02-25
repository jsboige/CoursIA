"""
Check outputs of all notebooks in the Texte series.
"""
import json
from pathlib import Path

def check_notebook_outputs(notebook_path):
    """Check if a notebook has valid outputs."""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    total_cells = 0
    code_cells = 0
    cells_with_output = 0
    empty_outputs = 0
    has_stream_output = False
    has_execute_result = False

    for cell in nb.get('cells', []):
        if cell.get('cell_type') == 'code':
            total_cells += 1
            code_cells += 1
            outputs = cell.get('outputs', [])

            if outputs:
                cells_with_output += 1
                for output in outputs:
                    output_type = output.get('output_type', '')
                    if output_type == 'stream':
                        has_stream_output = True
                    elif output_type == 'execute_result':
                        has_execute_result = True
                    # Check if output is empty
                    text_content = output.get('text', [])
                    if isinstance(text_content, list):
                        text_content = ''.join(text_content)
                    if text_content and not text_content.strip():
                        empty_outputs += 1
                    elif 'data' in output:
                        # Has data (images, etc.)
                        pass

    return {
        'total_cells': total_cells,
        'code_cells': code_cells,
        'cells_with_output': cells_with_output,
        'empty_outputs': empty_outputs,
        'has_stream_output': has_stream_output,
        'has_execute_result': has_execute_result,
        'has_outputs': cells_with_output > 0,
        'fully_executed': cells_with_output == code_cells if code_cells > 0 else False
    }

def main():
    texte_dir = Path("MyIA.AI.Notebooks/GenAI/Texte")
    notebooks = sorted(texte_dir.glob("*.ipynb"))

    print(f"Checking {len(notebooks)} notebooks in Texte series...\n")

    results = {}
    for nb_path in notebooks:
        stats = check_notebook_outputs(nb_path)
        results[nb_path.name] = stats

        status = "OK" if stats['has_outputs'] else "NO OUTPUTS"
        if stats['fully_executed']:
            status = "FULLY EXECUTED"

        print(f"{nb_path.name:40} | Code: {stats['code_cells']:2} | With output: {stats['cells_with_output']:2} | {status}")

    print("\n" + "="*80)
    print("SUMMARY")
    print("="*80)

    with_outputs = sum(1 for v in results.values() if v['has_outputs'])
    fully_executed = sum(1 for v in results.values() if v['fully_executed'])
    no_outputs = len(results) - with_outputs

    print(f"Total notebooks: {len(results)}")
    print(f"With outputs: {with_outputs}")
    print(f"Fully executed: {fully_executed}")
    print(f"No outputs: {no_outputs}")

    if no_outputs > 0:
        print("\nNotebooks WITHOUT outputs (need execution):")
        for name, stats in results.items():
            if not stats['has_outputs']:
                print(f"  - {name}")

    return 0 if no_outputs == 0 else 1

if __name__ == "__main__":
    exit(main())
