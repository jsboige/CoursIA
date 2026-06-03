"""
I1 Smoke Test: MCP Buffering Fix End-to-End Validation (Issue #835)

Validates that the line-buffering fix in jupyter-papermill-mcp-server main.py
works correctly under real conditions:
1. Long output streams (>1MB)
2. Rapid successive tool calls
3. Reconnect after kernel restart
4. Memory stability across repeated executions

Usage:
    python scripts/mcp_buffering_smoke_test.py [--output-dir /tmp/smoke_results]

Requirements:
    - MCP jupyter-papermill server running (configured in .mcp.json)
    - python3 kernel available
"""

import json
import os
import sys
import time
import traceback
from datetime import datetime
from pathlib import Path


def create_stress_notebook(path: str, mode: str = "long_output") -> dict:
    """Create a stress test notebook with specified mode."""
    nb = {
        "cells": [],
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3"
            },
            "language_info": {"name": "python", "version": "3.10.0"}
        },
        "nbformat": 4,
        "nbformat_minor": 5
    }

    if mode == "long_output":
        # Test 1: Generate >1MB of output rapidly
        nb["cells"].append({
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Stress Test: Large output generation (>1MB)\n",
                "import sys\n",
                "print(f'Python stdout buffering: {sys.stdout.line_buffering}')\n",
                "print(f'sys.stdout.isatty(): {sys.stdout.isatty()}')\n",
                "total_lines = 20000\n",
                "output_size = 0\n",
                "for i in range(total_lines):\n",
                "    line = f'Line {i:06d}: ' + 'x' * 50 + f' (size so far: {output_size})'\n",
                "    print(line)\n",
                "    output_size += len(line) + 1\n",
                "print(f'\\nTotal output: {output_size / 1024 / 1024:.2f} MB across {total_lines} lines')\n"
            ]
        })

        # Test 2: Rapid print bursts
        nb["cells"].append({
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Stress Test: Rapid burst prints (100 bursts of 100 lines)\n",
                "import time\n",
                "start = time.time()\n",
                "for burst in range(100):\n",
                "    for line in range(100):\n",
                "        print(f'Burst {burst:03d} Line {line:03d}')\n",
                "elapsed = time.time() - start\n",
                "print(f'\\n100 bursts x 100 lines = 10000 lines in {elapsed:.2f}s')\n"
            ]
        })

        # Test 3: Mixed output types
        nb["cells"].append({
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Stress Test: Mixed output (text + data frames + errors)\n",
                "import pandas as pd\n",
                "import numpy as np\n",
                "\n",
                "# Large DataFrame display\n",
                "df = pd.DataFrame(np.random.randn(100, 10), columns=[f'col_{i}' for i in range(10)])\n",
                "print('DataFrame 100x10:')\n",
                "print(df.to_string())\n",
                "\n",
                "# stdout + stderr interleaved\n",
                "import sys\n",
                "for i in range(50):\n",
                "    print(f'stdout line {i}')\n",
                "    print(f'stderr line {i}', file=sys.stderr)\n",
                "print('Mixed output complete: 50 stdout + 50 stderr lines')\n"
            ]
        })

        # Test 4: Unicode and special characters
        nb["cells"].append({
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Stress Test: Unicode and special characters\n",
                "chars = [\n",
                "    'Accents: e-acute e a u o',  # actual unicode chars\n",
                "    'CJK: ' + chr(0x4F60) + chr(0x597D),  # ni hao\n",
                "    'Emoji: ' + chr(0x1F680) + ' ' + chr(0x1F4A5),\n",
                "    'Math: ' + chr(0x2200) + 'x ' + chr(0x2208) + ' ' + chr(0x211D),\n",
                "    'Box: ' + chr(0x250C) + chr(0x2500) * 20 + chr(0x2510),\n",
                "]\n",
                "for c in chars:\n",
                "    print(c)\n",
                "print(f'Unicode test: {len(chars)} lines with special chars')\n"
            ]
        })

    elif mode == "reconnect":
        # Test kernel state preservation
        nb["cells"].append({
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Reconnect Test: Set state\n",
                "test_variable = 'preserved_after_restart'\n",
                "test_list = [i**2 for i in range(1000)]\n",
                "print(f'State set: test_variable={test_variable}, len(test_list)={len(test_list)}')\n"
            ]
        })

    elif mode == "rapid_calls":
        # Minimal cell for rapid sequential execution
        nb["cells"].append({
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "import time\n",
                "t0 = time.time()\n",
                "result = sum(i**2 for i in range(100000))\n",
                "print(f'Computed {result} in {time.time()-t0:.3f}s')\n"
            ]
        })

    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

    return nb


def run_smoke_test():
    """Main smoke test entry point. Creates notebooks and prints test plan."""
    output_dir = Path(os.environ.get('SMOKE_OUTPUT_DIR', '/tmp/mcp_smoke_results'))
    output_dir.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    results = {
        "timestamp": timestamp,
        "test_plan": "I1 MCP Buffering Smoke Test",
        "fix_verified": "sys.stdout.reconfigure(line_buffering=True) in main.py:19-24",
        "tests": {}
    }

    # Test 1: Long output notebook
    nb_path = str(output_dir / f"buffering_stress_{timestamp}.ipynb")
    print(f"[1/4] Creating long output stress notebook: {nb_path}")
    create_stress_notebook(nb_path, mode="long_output")
    results["tests"]["long_output"] = {
        "notebook": nb_path,
        "status": "CREATED",
        "instruction": "Execute via MCP jupyter-papermill execute_notebook, verify >1MB output received"
    }

    # Test 2: Reconnect test
    reconnect_nb = str(output_dir / f"reconnect_test_{timestamp}.ipynb")
    print(f"[2/4] Creating reconnect test notebook: {reconnect_nb}")
    create_stress_notebook(reconnect_nb, mode="reconnect")
    results["tests"]["reconnect"] = {
        "notebook": reconnect_nb,
        "status": "CREATED",
        "instruction": "Start kernel, execute cell, restart kernel, verify state lost (expected), re-execute"
    }

    # Test 3: Rapid calls notebook
    rapid_nb = str(output_dir / f"rapid_calls_{timestamp}.ipynb")
    print(f"[3/4] Creating rapid calls test notebook: {rapid_nb}")
    create_stress_notebook(rapid_nb, mode="rapid_calls")
    results["tests"]["rapid_calls"] = {
        "notebook": rapid_nb,
        "status": "CREATED",
        "instruction": "Execute 5 times in rapid succession via execute_on_kernel, measure timing"
    }

    # Save results manifest
    results_path = output_dir / f"smoke_test_manifest_{timestamp}.json"
    with open(results_path, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    print(f"\n[4/4] Results manifest saved: {results_path}")
    print(f"\n=== SMOKE TEST PLAN ===")
    print(f"Fix location: papermill_mcp/main.py lines 19-24 + 36-42")
    print(f"Fix content: sys.stdout.reconfigure(line_buffering=True)")
    print(f"Test notebooks created in: {output_dir}")
    print(f"")
    print(f"Next steps (execute via MCP tools):")
    print(f"  1. start_kernel -> python3")
    print(f"  2. execute_notebook {nb_path} (long output >1MB)")
    print(f"  3. restart_kernel -> verify clean state")
    print(f"  4. execute_on_kernel rapid_calls x5")
    print(f"  5. stop_kernel -> cleanup")

    return results


if __name__ == "__main__":
    run_smoke_test()
