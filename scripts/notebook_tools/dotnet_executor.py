"""Execute .NET Interactive notebooks cell-by-cell via jupyter_client.

Usage:
    python dotnet_executor.py <notebook_path> [--timeout 120] [--kernel .net-csharp]
    python dotnet_executor.py --batch <directory> [--pattern "Infer-*.ipynb"]

Writes back the notebook with real execution_count and outputs.
"""

import json
import sys
import time
import argparse
import glob
import os
from pathlib import Path

import jupyter_client


def _drain_iopub(kc, parent_msg_id, deadline_s=5):
    """Best-effort drain of iopub messages until the kernel goes idle or a
    short deadline passes.

    Used after ``interrupt_kernel()`` on a cell timeout to discard the
    interrupted request's trailing messages so they do not leak into the next
    cell's iopub loop. Only messages whose ``parent_header.msg_id`` matches
    ``parent_msg_id`` are inspected; unrelated messages are left in the queue
    for their owner. Returns silently on any error (drain is best-effort).
    """
    deadline = time.time() + deadline_s
    while time.time() < deadline:
        try:
            msg = kc.get_iopub_msg(timeout=1)
        except Exception:
            return
        if msg.get("parent_header", {}).get("msg_id") != parent_msg_id:
            continue
        if (msg.get("msg_type") == "status"
                and msg.get("content", {}).get("execution_state") == "idle"):
            return


def execute_notebook(notebook_path, kernel_name=".net-csharp", cell_timeout=120,
                     verbose=False, dry_run=False):
    """Execute a .NET notebook cell-by-cell and update outputs.

    Returns dict with stats: total cells, executed, errors, time.
    """
    notebook_path = Path(notebook_path)
    nb = json.loads(notebook_path.read_text(encoding="utf-8"))
    code_cells = [(i, c) for i, c in enumerate(nb["cells"]) if c["cell_type"] == "code"]

    if not code_cells:
        print(f"  No code cells in {notebook_path.name}")
        return {"total": 0, "executed": 0, "errors": 0, "skipped": True}

    if dry_run:
        exec_count = sum(1 for _, c in code_cells if c.get("execution_count"))
        print(f"  [DRY RUN] {notebook_path.name}: {len(code_cells)} code cells, {exec_count} already executed")
        return {"total": len(code_cells), "executed": exec_count, "errors": 0, "skipped": True}

    print(f"  Starting kernel for {notebook_path.name} ({len(code_cells)} code cells)...")

    # Set working directory to notebook's directory for #load directives
    notebook_dir = notebook_path.parent.resolve()
    orig_dir = os.getcwd()

    # Kernel lifecycle objects are initialized to None BEFORE the try so the
    # finally can robustly clean up partial setups. start_kernel / client /
    # start_channels live INSIDE the try: if setup fails AFTER start_kernel()
    # succeeds (e.g. start_channels() raises on a broken kernel transport), the
    # started kernel must still be shut down -- otherwise the .NET kernel
    # process is leaked as an orphan (notably on Windows). Previously the
    # finally only wrapped cell execution, so a setup failure skipped cleanup
    # entirely and leaked the kernel.
    km = None
    kc = None
    stats = {"total": len(code_cells), "executed": 0, "errors": 0, "time": 0}
    exec_counter = 0
    start_time = time.time()

    try:
        km = jupyter_client.KernelManager(kernel_name=kernel_name)
        km.start_kernel(cwd=str(notebook_dir))
        kc = km.client()
        kc.start_channels()

        # Wait for kernel ready
        time.sleep(3)

        for cell_idx, cell in code_cells:
            source = "".join(cell["source"])
            exec_counter += 1

            if verbose:
                preview = source[:80].replace("\n", " ")
                print(f"    [{exec_counter}/{len(code_cells)}] {preview}...")

            msg_id = kc.execute(source)

            outputs = []
            error_occurred = False
            deadline = time.time() + cell_timeout

            while time.time() < deadline:
                try:
                    msg = kc.get_iopub_msg(timeout=5)
                except Exception:
                    continue

                # Only consume iopub messages belonging to THIS cell's execute
                # request. Without this filter, stale output or a stray idle
                # status emitted for a PRIOR cell can pollute this cell's outputs
                # or break the loop early. Messages lacking a parent_header
                # (some kernel broadcasts) are kept for forward-compatibility.
                parent_id = msg.get("parent_header", {}).get("msg_id")
                if parent_id is not None and parent_id != msg_id:
                    continue

                msg_type = msg["msg_type"]
                content = msg["content"]

                if msg_type == "stream":
                    text = content.get("text", "")
                    stream_name = content.get("name", "stdout")
                    outputs.append({
                        "output_type": "stream",
                        "name": stream_name,
                        "text": text,
                    })
                elif msg_type == "execute_result":
                    data = content.get("data", {})
                    outputs.append({
                        "output_type": "execute_result",
                        "data": data,
                        "metadata": {},
                        "execution_count": exec_counter,
                    })
                elif msg_type == "display_data":
                    data = content.get("data", {})
                    outputs.append({
                        "output_type": "display_data",
                        "data": data,
                        "metadata": {},
                    })
                elif msg_type == "error":
                    error_occurred = True
                    ename = content.get("ename", "Error")
                    evalue = content.get("evalue", "")
                    traceback = content.get("traceback", [])
                    outputs.append({
                        "output_type": "error",
                        "ename": ename,
                        "evalue": evalue,
                        "traceback": traceback,
                    })
                    print(f"    ERROR [{exec_counter}]: {ename}: {evalue[:100]}")
                elif msg_type == "status" and content.get("execution_state") == "idle":
                    break

            if time.time() >= deadline:
                print(f"    TIMEOUT [{exec_counter}] after {cell_timeout}s")
                # Interrupt the stuck execution so the next cell is not queued
                # behind it, then drain this request's trailing iopub messages
                # so they do not consume the next cell's loop budget. Both are
                # defensive: wrapped against kernel managers that do not support
                # interrupt or have nothing left to drain.
                try:
                    km.interrupt_kernel()
                except Exception:
                    pass
                _drain_iopub(kc, msg_id)
                outputs.append({
                    "output_type": "stream",
                    "name": "stderr",
                    "text": f"[TIMEOUT after {cell_timeout}s]\n",
                })

            # Update cell
            cell["execution_count"] = exec_counter
            cell["outputs"] = outputs

            if error_occurred:
                stats["errors"] += 1
            stats["executed"] += 1

    finally:
        elapsed = round(time.time() - start_time, 1)
        stats["time"] = elapsed
        # Guarded cleanup: kc/km may be None if setup failed before they were
        # fully created, and stop_channels / shutdown_kernel may themselves
        # raise on a half-started kernel. Swallow cleanup-side errors so the
        # ORIGINAL setup/execution error propagates instead of being masked.
        if kc is not None:
            try:
                kc.stop_channels()
            except Exception:
                pass
        if km is not None:
            try:
                km.shutdown_kernel()
            except Exception:
                pass
        os.chdir(orig_dir)

    # Write back
    notebook_path.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")

    print(f"  DONE {notebook_path.name}: {stats['executed']}/{stats['total']} cells, "
          f"{stats['errors']} errors, {elapsed}s")
    return stats


def batch_execute(directory, pattern="*.ipynb", kernel_name=".net-csharp",
                  cell_timeout=120, verbose=False, dry_run=False):
    """Execute all matching notebooks in a directory."""
    notebooks = sorted(glob.glob(str(Path(directory) / pattern)))
    print(f"Found {len(notebooks)} notebooks matching '{pattern}' in {directory}")

    results = {}
    for nb_path in notebooks:
        name = Path(nb_path).name
        print(f"\n{'='*60}")
        print(f"Processing: {name}")
        print(f"{'='*60}")
        stats = execute_notebook(nb_path, kernel_name=kernel_name,
                                 cell_timeout=cell_timeout, verbose=verbose,
                                 dry_run=dry_run)
        results[name] = stats

    print(f"\n{'='*60}")
    print("BATCH SUMMARY")
    print(f"{'='*60}")
    for name, stats in results.items():
        if stats.get("skipped"):
            print(f"  {name}: SKIPPED ({stats['total']} cells)")
        else:
            print(f"  {name}: {stats['executed']}/{stats['total']} cells, "
                  f"{stats['errors']} errors, {stats.get('time', 0)}s")

    return results


def main():
    parser = argparse.ArgumentParser(description="Execute .NET notebooks cell-by-cell")
    parser.add_argument("path", help="Notebook path or directory for --batch")
    parser.add_argument("--batch", action="store_true", help="Process all notebooks in directory")
    parser.add_argument("--pattern", default="*.ipynb", help="Glob pattern for batch mode")
    parser.add_argument("--kernel", default=".net-csharp", help="Kernel name")
    parser.add_argument("--timeout", type=int, default=120, help="Cell timeout in seconds")
    parser.add_argument("--verbose", "-v", action="store_true", help="Show each cell execution")
    parser.add_argument("--dry-run", action="store_true", help="Diagnostic only")
    args = parser.parse_args()

    if args.batch:
        batch_execute(args.path, pattern=args.pattern, kernel_name=args.kernel,
                      cell_timeout=args.timeout, verbose=args.verbose, dry_run=args.dry_run)
    else:
        execute_notebook(args.path, kernel_name=args.kernel,
                         cell_timeout=args.timeout, verbose=args.verbose,
                         dry_run=args.dry_run)


if __name__ == "__main__":
    main()
