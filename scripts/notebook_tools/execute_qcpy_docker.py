#!/usr/bin/env python3
"""Execute QC-Py notebooks via Docker Jupyter Lab (lean research).

Uses the Jupyter REST API + WebSocket to execute cells one-by-one
in the Docker container running lean research with QuantBook support.

Usage:
    # Start lean research first:
    lean research <project-dir> --lean-config <config> --port 8888

    # Then run this script:
    python execute_qcpy_docker.py [--notebooks QC-Py-12 QC-Py-15 ...]
                                  [--all] [--dry-run] [--timeout 120]
                                  [--base-url http://localhost:8888]

Exit codes:
    0 - All notebooks executed successfully
    1 - One or more notebooks had errors
    2 - Setup/runtime error
"""

import argparse
import json
import os
import sys
import time
import uuid
from pathlib import Path

import requests
import websocket

BASE_URL_DEFAULT = "http://localhost:8888"
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
QCPY_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / "Python"


def get_ws_kernel_id(base_url: str) -> str:
    """Get or create a kernel via session API."""
    # Try to find existing session
    r = requests.get(f"{base_url}/api/sessions", timeout=10)
    sessions = r.json()
    if sessions:
        return sessions[0]["kernel"]["id"]

    # Upload a dummy notebook and create session
    nb = {
        "cells": [{"cell_type": "code", "execution_count": None,
                    "metadata": {}, "outputs": [],
                    "source": ["print('init')"]}],
        "metadata": {
            "kernelspec": {"display_name": "Foundation-Py-Default",
                           "language": "python", "name": "python3"},
            "language_info": {"name": "python", "version": "3.10.0"}
        },
        "nbformat": 4, "nbformat_minor": 5
    }
    requests.put(f"{base_url}/api/contents/_executor.ipynb",
                 json={"type": "notebook", "content": nb, "format": "json"},
                 timeout=10)

    r = requests.post(f"{base_url}/api/sessions", json={
        "kernel": {"name": "python3"},
        "notebook": {"path": "_executor.ipynb"},
        "type": "notebook", "name": "_executor.ipynb"
    }, timeout=10)
    return r.json()["kernel"]["id"]


def exec_code(ws: websocket.WebSocket, code: str, session_id: str,
              timeout: int = 120) -> dict:
    """Execute code via websocket, return collected outputs."""
    msg_id = str(uuid.uuid4())
    msg = {
        "header": {
            "msg_id": msg_id, "msg_type": "execute_request",
            "username": "executor", "session": session_id,
            "version": "5.3",
            "date": time.strftime("%Y-%m-%dT%H:%M:%SZ")
        },
        "parent_header": {}, "metadata": {},
        "content": {
            "code": code, "silent": False, "store_history": True,
            "user_expressions": {}, "allow_stdin": False,
            "stop_on_error": False
        },
        "buffers": [], "channel": "shell"
    }
    ws.send(json.dumps(msg))

    result = {"status": "unknown", "streams": [], "errors": [],
              "result": None, "display_data": []}
    got_reply = False
    start = time.time()

    while time.time() - start < timeout:
        try:
            ws.settimeout(5)
            raw = ws.recv()
            resp = json.loads(raw)
            parent = resp.get("parent_header", {}).get("msg_id", "")
            if parent != msg_id:
                continue

            mt = resp.get("msg_type",
                          resp.get("header", {}).get("msg_type", ""))
            content = resp.get("content", {})

            if mt == "stream":
                result["streams"].append(content.get("text", ""))
            elif mt == "error":
                result["errors"].append({
                    "ename": content.get("ename", ""),
                    "evalue": content.get("evalue", ""),
                    "traceback": content.get("traceback", [])
                })
            elif mt == "execute_result":
                result["result"] = content.get("data", {})
            elif mt == "display_data":
                result["display_data"].append(content.get("data", {}))
            elif mt == "execute_reply":
                got_reply = True
                result["status"] = content.get("status", "unknown")
            elif mt == "status":
                state = content.get("execution_state", "")
                if state == "idle" and got_reply:
                    return result
        except websocket.WebSocketTimeoutException:
            continue
        except Exception as e:
            result["errors"].append({"ename": "WebSocketError",
                                     "evalue": str(e), "traceback": []})
            return result

    result["status"] = "timeout"
    return result


def cell_needs_execution(cell: dict) -> bool:
    """Check if a code cell needs execution."""
    if cell.get("cell_type") != "code":
        return False
    src = "".join(cell.get("source", []))
    if not src.strip():
        return False
    lines = [l.strip() for l in src.split("\n") if l.strip()]
    if all(l.startswith("#") for l in lines):
        return False
    # Skip REFERENCE QC cells (full QCAlgorithm, not executable in QuantBook)
    if "[REFERENCE QC]" in src:
        return False
    return True


def execute_notebook(nb_path: Path, base_url: str, kernel_id: str,
                     timeout: int, exec_count_start: int = 1
                     ) -> tuple[dict, int]:
    """Execute a single notebook via Docker Jupyter API.

    Returns (result_dict, cells_executed_count).
    """
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    cells = nb["cells"]

    ws_url = f"ws://{base_url.replace('http://', '')}/api/kernels/{kernel_id}/channels"
    ws = websocket.create_connection(ws_url, timeout=60)
    ws_session = str(uuid.uuid4())

    exec_count = exec_count_start
    cells_executed = 0
    cells_ok = 0
    cells_err = 0
    cell_results = []

    for i, cell in enumerate(cells):
        if not cell_needs_execution(cell):
            continue

        src = "".join(cell.get("source", []))
        result = exec_code(ws, src, ws_session, timeout=timeout)

        is_error = (result["status"] == "error" or result["status"] == "timeout"
                    or len(result["errors"]) > 0)

        cell_results.append({
            "cell_index": i,
            "status": "error" if is_error else "ok",
            "exec_count": exec_count,
            "outputs_count": (len(result["streams"]) +
                              len(result["errors"]) +
                              (1 if result["result"] else 0))
        })

        if not is_error:
            cells_ok += 1
            cell["execution_count"] = exec_count

            # Build outputs
            outputs = []
            for text in result["streams"]:
                outputs.append({
                    "output_type": "stream",
                    "name": "stdout",
                    "text": text.split("\n")
                })
            for err in result["errors"]:
                outputs.append({
                    "output_type": "error",
                    "ename": err["ename"],
                    "evalue": err["evalue"],
                    "traceback": err.get("traceback", [])
                })
            if result["result"]:
                outputs.append({
                    "output_type": "execute_result",
                    "execution_count": exec_count,
                    "data": result["result"],
                    "metadata": {}
                })
            for dd in result["display_data"]:
                outputs.append({
                    "output_type": "display_data",
                    "data": dd,
                    "metadata": {}
                })
            cell["outputs"] = outputs
        else:
            cells_err += 1
            # Keep execution_count even on error
            cell["execution_count"] = exec_count
            outputs = []
            for err in result["errors"]:
                outputs.append({
                    "output_type": "error",
                    "ename": err["ename"],
                    "evalue": err["evalue"],
                    "traceback": err.get("traceback", [])
                })
            cell["outputs"] = outputs

        exec_count += 1
        cells_executed += 1

    ws.close()

    # Save executed notebook
    nb_path.write_text(json.dumps(nb, indent=1, ensure_ascii=False),
                       encoding="utf-8")

    return {
        "path": str(nb_path.relative_to(REPO_ROOT)),
        "cells_executed": cells_executed,
        "cells_ok": cells_ok,
        "cells_err": cells_err,
        "cell_results": cell_results
    }, cells_executed


def main():
    parser = argparse.ArgumentParser(
        description="Execute QC-Py notebooks via Docker lean research"
    )
    parser.add_argument("--notebooks", nargs="+", help="Specific notebook names")
    parser.add_argument("--all", action="store_true",
                        help="Execute all QC-Py notebooks with null cells")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be executed without running")
    parser.add_argument("--timeout", type=int, default=120,
                        help="Per-cell timeout in seconds (default: 120)")
    parser.add_argument("--base-url", default=BASE_URL_DEFAULT,
                        help=f"Jupyter Lab URL (default: {BASE_URL_DEFAULT})")
    parser.add_argument("--restart-kernel", action="store_true",
                        help="Restart kernel between each notebook for clean state")
    args = parser.parse_args()

    # Collect target notebooks
    targets = []
    all_nbs = sorted(QCPY_DIR.glob("QC-Py-*.ipynb"))
    all_nbs = [n for n in all_nbs if "_output" not in n.name]

    if args.notebooks:
        for name in args.notebooks:
            path = QCPY_DIR / name
            if not path.exists():
                print(f"WARNING: {name} not found, skipping")
                continue
            targets.append(path)
    elif args.all:
        for nb_path in all_nbs:
            nb = json.loads(nb_path.read_text(encoding="utf-8"))
            has_null = any(
                cell_needs_execution(c) and c.get("execution_count") is None
                for c in nb["cells"]
            )
            if has_null:
                targets.append(nb_path)
    else:
        parser.print_help()
        return 2

    if not targets:
        print("No notebooks to execute.")
        return 0

    print(f"Target notebooks: {len(targets)}")
    for t in targets:
        print(f"  {t.name}")

    if args.dry_run:
        for nb_path in targets:
            nb = json.loads(nb_path.read_text(encoding="utf-8"))
            null_cells = [
                i for i, c in enumerate(nb["cells"])
                if cell_needs_execution(c) and c.get("execution_count") is None
            ]
            print(f"  {nb_path.name}: {len(null_cells)} cells to execute")
        return 0

    # Check Jupyter is reachable
    try:
        r = requests.get(f"{args.base_url}/api/kernelspecs", timeout=5)
        r.raise_for_status()
    except Exception as e:
        print(f"ERROR: Cannot reach Jupyter at {args.base_url}: {e}")
        print("Start lean research first:")
        print("  lean research <project-dir> --lean-config <config> --port 8888")
        return 2

    # Get kernel
    try:
        kernel_id = get_ws_kernel_id(args.base_url)
        print(f"Using kernel: {kernel_id}")
    except Exception as e:
        print(f"ERROR: Cannot create kernel: {e}")
        return 2

    # Execute notebooks
    total_executed = 0
    total_ok = 0
    total_err = 0
    failed_nbs = []

    for nb_path in targets:
        # Restart kernel between notebooks if requested
        if args.restart_kernel and targets.index(nb_path) > 0:
            try:
                requests.delete(f"{args.base_url}/api/kernels/{kernel_id}",
                                timeout=10)
            except Exception:
                pass
            try:
                kernel_id = get_ws_kernel_id(args.base_url)
                print(f"  Fresh kernel: {kernel_id[:12]}...")
            except Exception:
                print("  CRITICAL: Cannot create fresh kernel, aborting")
                return 2

        print(f"\nExecuting {nb_path.name}...")
        try:
            result, n = execute_notebook(nb_path, args.base_url, kernel_id,
                                         args.timeout)
            total_executed += result["cells_executed"]
            total_ok += result["cells_ok"]
            total_err += result["cells_err"]

            status = "OK" if result["cells_err"] == 0 else "PARTIAL"
            print(f"  {status}: {result['cells_ok']}/{result['cells_executed']} cells ok")
            if result["cells_err"] > 0:
                failed_nbs.append(nb_path.name)
                for cr in result["cell_results"]:
                    if cr["status"] == "error":
                        print(f"    cell {cr['cell_index']}: ERROR")
        except Exception as e:
            print(f"  FAILED: {e}")
            failed_nbs.append(nb_path.name)
            # Restart kernel on failure
            try:
                kernel_id = get_ws_kernel_id(args.base_url)
                print(f"  Restarted kernel: {kernel_id}")
            except Exception:
                print("  CRITICAL: Cannot restart kernel, aborting")
                return 2

    print(f"\n{'='*60}")
    print(f"Total: {len(targets)} notebooks, {total_executed} cells executed")
    print(f"  OK: {total_ok}, Errors: {total_err}")
    if failed_nbs:
        print(f"  Failed notebooks: {', '.join(failed_nbs)}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
