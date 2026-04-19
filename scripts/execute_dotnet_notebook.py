#!/usr/bin/env python
"""
Execute .NET Interactive notebooks cell-by-cell and save outputs.
Required because Papermill does not work with .NET kernels.
"""

import json
import sys
import time
from pathlib import Path
from jupyter_client import KernelManager

def execute_dotnet_notebook(notebook_path: str, timeout: int = 300):
    """
    Execute a .NET notebook cell-by-cell and save outputs.

    Args:
        notebook_path: Path to the .ipynb file
        timeout: Timeout per cell in seconds

    Returns:
        dict: Execution summary with success status and details
    """
    notebook_path = Path(notebook_path).resolve()

    print(f"=== Executing .NET Notebook: {notebook_path.name} ===")

    # Read notebook
    with open(notebook_path, 'r', encoding='utf-8') as f:
        notebook = json.load(f)

    # Get working directory from notebook location
    working_dir = str(notebook_path.parent)

    # Start .NET C# kernel
    print("Starting .NET C# kernel...")
    km = KernelManager(kernel_name='.net-csharp')
    km.start_kernel()
    kc = km.client()

    # Wait for kernel to be ready
    time.sleep(2)

    results = {
        'notebook': str(notebook_path),
        'total_cells': len(notebook.get('cells', [])),
        'code_cells': 0,
        'executed': 0,
        'successful': 0,
        'errors': 0,
        'cells': []
    }

    try:
        # Set working directory FIRST (critical for relative paths)
        print(f"Setting working directory to: {working_dir}")
        setup_code = f'''System.IO.Directory.SetCurrentDirectory(@"{working_dir}");'''
        kc.execute(setup_code)

        # Wait for setup to complete
        msg = kc.get_shell_msg(timeout=10)
        if msg['content']['status'] == 'error':
            print(f"Warning: Could not set working directory: {msg['content']['evalue']}")

        # Execute cells
        for idx, cell in enumerate(notebook.get('cells', [])):
            if cell.get('cell_type') != 'code':
                continue

            results['code_cells'] += 1
            source = cell.get('source', '')
            if isinstance(source, list):
                source = ''.join(source)

            print(f"\n[Cell {idx}] Executing...")
            print(f"  Preview: {source[:80]}..." if len(source) > 80 else f"  Code: {source}")

            cell_result = {
                'index': idx,
                'success': False,
                'output': None,
                'error': None
            }

            # Clear previous outputs
            cell['outputs'] = []

            try:
                # Execute code
                kc.execute(source)

                # Collect outputs
                outputs = []
                has_error = False
                error_msg = None

                while True:
                    try:
                        msg = kc.get_iopub_msg(timeout=timeout)

                        # Check for execution_state (if present)
                        if 'execution_state' in msg.get('content', {}):
                            if msg['content']['execution_state'] == 'idle':
                                break

                        # Skip status messages
                        if msg['msg_type'] == 'status':
                            continue

                        if msg['msg_type'] == 'stream':
                            outputs.append({
                                'output_type': 'stream',
                                'name': msg['content'].get('name', 'stdout'),
                                'text': msg['content'].get('text', '')
                            })

                        elif msg['msg_type'] == 'execute_result':
                            outputs.append({
                                'output_type': 'execute_result',
                                'data': msg['content'].get('data', {}),
                                'metadata': msg['content'].get('metadata', {}),
                                'execution_count': msg['content'].get('execution_count', 0)
                            })

                        elif msg['msg_type'] == 'display_data':
                            outputs.append({
                                'output_type': 'display_data',
                                'data': msg['content'].get('data', {}),
                                'metadata': msg['content'].get('metadata', {})
                            })

                        elif msg['msg_type'] == 'error':
                            has_error = True
                            error_msg = msg['content'].get('evalue', 'Unknown error')
                            traceback = '\n'.join(msg['content'].get('traceback', []))
                            outputs.append({
                                'output_type': 'error',
                                'ename': msg['content'].get('ename', 'Error'),
                                'evalue': error_msg,
                                'traceback': msg['content'].get('traceback', [])
                            })
                            print(f"  ERROR: {error_msg}")

                    except Exception as e:
                        if 'timeout' in str(e).lower():
                            print(f"  TIMEOUT after {timeout}s")
                            cell_result['error'] = f'Timeout after {timeout}s'
                            results['errors'] += 1
                            break
                        raise

                # Save outputs to cell
                cell['outputs'] = outputs

                cell_result['success'] = not has_error
                cell_result['output'] = outputs

                if has_error:
                    results['errors'] += 1
                    cell_result['error'] = error_msg or 'Unknown error'
                else:
                    results['successful'] += 1
                    print(f"  SUCCESS ({len(outputs)} output(s))")

                results['executed'] += 1

            except Exception as e:
                results['errors'] += 1
                cell_result['error'] = str(e)
                print(f"  EXCEPTION: {e}")

                # Add error as output
                cell['outputs'] = [{
                    'output_type': 'error',
                    'ename': 'ExecutionError',
                    'evalue': str(e),
                    'traceback': [str(e)]
                }]

            results['cells'].append(cell_result)

        # Save notebook with outputs
        print(f"\nSaving notebook to: {notebook_path}")
        with open(notebook_path, 'w', encoding='utf-8') as f:
            json.dump(notebook, f, indent=1, ensure_ascii=False)

        return results

    finally:
        # Stop kernel
        print("\nStopping kernel...")
        km.shutdown_kernel()
        kc.stop_channels()


def print_summary(results: dict):
    """Print execution summary."""
    print("\n" + "="*60)
    print("EXECUTION SUMMARY")
    print("="*60)
    print(f"Notebook: {results['notebook']}")
    print(f"Total cells: {results['total_cells']}")
    print(f"Code cells: {results['code_cells']}")
    print(f"Executed: {results['executed']}")
    print(f"Successful: {results['successful']}")
    print(f"Errors: {results['errors']}")

    if results['errors'] > 0:
        print("\n--- Cells with errors ---")
        for cell in results['cells']:
            if not cell['success']:
                print(f"  Cell {cell['index']}: {cell['error']}")

    print("="*60)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python execute_dotnet_notebook.py <notebook.ipynb> [timeout]")
        sys.exit(1)

    notebook_path = sys.argv[1]
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 300

    results = execute_dotnet_notebook(notebook_path, timeout)
    print_summary(results)

    # Exit with error code if any cell failed
    sys.exit(0 if results['errors'] == 0 else 1)
