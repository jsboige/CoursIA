#!/usr/bin/env python3
"""Execute .NET/C# notebooks cell-by-cell and persist outputs to disk."""

import json
import sys
import time
import base64
from pathlib import Path


def execute_and_persist(notebook_path: str, timeout_per_cell: int = 120):
    """Execute a .NET notebook cell-by-cell and write outputs back."""
    import jupyter_client

    path = Path(notebook_path)
    with open(path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    kernel_name = nb.get('metadata', {}).get('kernelspec', {}).get('name', '.net-csharp')
    print(f"Executing {path.name} (kernel={kernel_name})")

    km = jupyter_client.KernelManager(kernel_name=kernel_name)
    km.start_kernel()
    kc = km.client()
    kc.start_channels()
    kc.wait_for_ready(timeout=120)
    print(f"  Kernel ready")

    nb_dir = str(path.parent)
    if '.net' in kernel_name:
        kc.execute(f'System.IO.Directory.SetCurrentDirectory(@"{nb_dir}")')
        _wait_idle(kc, timeout=15)

    cells = nb['cells']
    executed = 0
    errors = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue

        source = ''.join(cell.get('source', []))
        if not source.strip():
            continue

        cell['outputs'] = []
        executed += 1
        print(f"  Cell {i}: ", end='', flush=True)
        t0 = time.time()

        try:
            kc.execute(source)
            outputs = []
            while True:
                try:
                    msg = kc.get_iopub_msg(timeout=timeout_per_cell)
                    msg_type = msg['msg_type']
                    content = msg.get('content', {})

                    if msg_type == 'stream':
                        text = content.get('text', '')
                        outputs.append({
                            'output_type': 'stream',
                            'name': content.get('name', 'stdout'),
                            'text': _split_lines(text)
                        })
                    elif msg_type == 'execute_result':
                        data = content.get('data', {})
                        out = {
                            'output_type': 'execute_result',
                            'metadata': {},
                            'data': {},
                            'execution_count': content.get('execution_count', executed)
                        }
                        if 'text/plain' in data:
                            out['data']['text/plain'] = _split_lines(data['text/plain'])
                        if 'text/html' in data:
                            out['data']['text/html'] = _split_lines(data['text/html'])
                        if 'image/svg+xml' in data:
                            out['data']['image/svg+xml'] = _split_lines(data['image/svg+xml'])
                        outputs.append(out)
                    elif msg_type == 'display_data':
                        data = content.get('data', {})
                        out = {'output_type': 'display_data', 'metadata': {}, 'data': {}}
                        if 'text/plain' in data:
                            out['data']['text/plain'] = _split_lines(data['text/plain'])
                        if 'text/html' in data:
                            out['data']['text/html'] = _split_lines(data['text/html'])
                        if 'image/svg+xml' in data:
                            out['data']['image/svg+xml'] = _split_lines(data['image/svg+xml'])
                        outputs.append(out)
                    elif msg_type == 'error':
                        ename = content.get('ename', 'Error')
                        evalue = content.get('evalue', '')
                        traceback = content.get('traceback', [])
                        outputs.append({
                            'output_type': 'error',
                            'ename': ename,
                            'evalue': evalue,
                            'traceback': traceback
                        })
                        errors += 1
                    elif msg_type == 'status' and content.get('execution_state') == 'idle':
                        break
                except Exception as e:
                    if 'timeout' in str(e).lower():
                        outputs.append({
                            'output_type': 'error',
                            'ename': 'TimeoutError',
                            'evalue': f'Timeout after {timeout_per_cell}s',
                            'traceback': []
                        })
                        errors += 1
                    break

            cell['outputs'] = outputs
            elapsed = time.time() - t0
            status = 'OK' if not any(o.get('output_type') == 'error' for o in outputs) else 'ERR'
            print(f"{status} ({elapsed:.1f}s, {len(outputs)} outputs)")

        except Exception as e:
            errors += 1
            cell['outputs'] = [{
                'output_type': 'error',
                'ename': type(e).__name__,
                'evalue': str(e),
                'traceback': []
            }]
            print(f"EXCEPTION: {e}")

    kc.stop_channels()
    km.shutdown_kernel(now=True)

    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

    print(f"  Done: {executed} cells executed, {errors} errors, saved to {path.name}")
    return executed, errors


def _wait_idle(kc, timeout=10):
    """Wait for kernel idle state."""
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            msg = kc.get_iopub_msg(timeout=2)
            if msg['msg_type'] == 'status' and msg['content'].get('execution_state') == 'idle':
                return
        except:
            pass


def _split_lines(text):
    """Split text into list of lines (nbformat convention)."""
    lines = text.split('\n')
    return [l + '\n' for l in lines[:-1]] + ([lines[-1]] if lines[-1] else [])


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python exec_dotnet_persist.py <notebook.ipynb> [timeout]")
        sys.exit(1)

    nb_path = sys.argv[1]
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 120

    executed, errors = execute_and_persist(nb_path, timeout_per_cell=timeout)
    print(f"\nResult: {executed} cells, {errors} errors")
    sys.exit(1 if errors > 0 else 0)
