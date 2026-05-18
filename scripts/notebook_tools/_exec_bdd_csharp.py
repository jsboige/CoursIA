"""
Execute Sudoku-14-BDD-Csharp.ipynb cell-by-cell via .net-csharp kernel.
Uses jupyter_client to connect to the kernel, execute each code cell,
capture outputs, and save the notebook back with results.
"""
import json
import time
import sys
from jupyter_client import KernelManager

NB_PATH = r"d:\dev\CoursIA\MyIA.AI.Notebooks\Sudoku\Sudoku-14-BDD-Csharp.ipynb"

print(f"Loading notebook: {NB_PATH}")
with open(NB_PATH, "r", encoding="utf-8") as f:
    nb = json.load(f)

code_cells = [(i, cell) for i, cell in enumerate(nb["cells"]) if cell["cell_type"] == "code"]
print(f"Found {len(code_cells)} code cells")

# Start kernel
print("Starting .net-csharp kernel (may take 30-60s on cold start)...")
km = KernelManager(kernel_name=".net-csharp")
km.start_kernel()
kc = km.client()
kc.start_channels()

# Wait for kernel ready
print("Waiting for kernel to be ready...")
time.sleep(15)

# Send a test message and wait for response
kc.execute('Console.WriteLine("KERNEL_READY");', store_history=False)
ready = False
deadline = time.time() + 120  # 2 min max wait for kernel
while time.time() < deadline:
    try:
        msg = kc.get_iopub_msg(timeout=60)
    except Exception:
        continue
    msg_type = msg["msg_type"]
    if msg_type == "stream" and "KERNEL_READY" in str(msg["content"].get("text", "")):
        ready = True
        break
    if msg_type == "status" and msg["content"]["execution_state"] == "idle":
        # Kernel is idle, try executing again to confirm
        pass

if not ready:
    # Try one more time
    print("Kernel not ready on first attempt, waiting more...")
    time.sleep(30)
    kc.execute('Console.WriteLine("KERNEL_READY");', store_history=False)
    while time.time() < deadline + 60:
        try:
            msg = kc.get_iopub_msg(timeout=60)
        except Exception:
            break
        if msg["msg_type"] == "stream" and "KERNEL_READY" in str(msg["content"].get("text", "")):
            ready = True
            break
        if msg["msg_type"] == "status" and msg["content"]["execution_state"] == "idle":
            break

if not ready:
    print("WARNING: Kernel may not be fully ready, proceeding anyway...")
else:
    print("Kernel is ready!")

# Execute each code cell
exec_count = 0
cell_results = []

for idx, (cell_index, cell) in enumerate(code_cells):
    source = "".join(cell["source"])
    if not source.strip():
        print(f"  Cell {cell_index}: empty, skipping")
        continue

    exec_count += 1
    print(f"\n--- Cell {cell_index} (exec #{exec_count}) ---")
    print(f"  Source preview: {source[:80].replace(chr(10), ' ')}...")

    # Determine timeout per cell
    # Cell with RowMDDBuilder (index ~8) builds 5.6M nodes, needs more time
    cell_timeout = 600 if "RowMDDBuilder" in source else 300

    msg_id = kc.execute(source)
    outputs = []
    cell_start = time.time()
    cell_deadline = cell_start + cell_timeout
    got_idle = False

    while time.time() < cell_deadline:
        try:
            msg = kc.get_iopub_msg(timeout=60)
        except Exception as e:
            print(f"  Timeout waiting for message: {e}")
            break

        # Only process messages for our execution
        if msg["parent_header"].get("msg_id") != msg_id:
            continue

        msg_type = msg["msg_type"]
        content = msg["content"]

        if msg_type == "stream":
            text = content.get("text", "")
            outputs.append({
                "output_type": "stream",
                "name": content.get("name", "stdout"),
                "text": text
            })
        elif msg_type == "error":
            outputs.append({
                "output_type": "error",
                "ename": content.get("ename", ""),
                "evalue": content.get("evalue", ""),
                "traceback": content.get("traceback", [])
            })
        elif msg_type == "execute_result":
            data = content.get("data", {})
            if data:
                outputs.append({
                    "output_type": "execute_result",
                    "data": data,
                    "metadata": {},
                    "execution_count": exec_count
                })
        elif msg_type == "display_data":
            outputs.append({
                "output_type": "display_data",
                "data": content.get("data", {}),
                "metadata": {}
            })
        elif msg_type == "status" and content["execution_state"] == "idle":
            got_idle = True
            break

    elapsed = time.time() - cell_start
    has_error = any(o["output_type"] == "error" for o in outputs)
    status = "ERROR" if has_error else "OK"

    # Update cell
    cell["execution_count"] = exec_count
    cell["outputs"] = outputs

    # Print summary
    output_summary = []
    for o in outputs:
        if o["output_type"] == "stream":
            text = o["text"][:200].replace("\n", "\\n")
            output_summary.append(f"stream({o['name']}): {text}")
        elif o["output_type"] == "error":
            output_summary.append(f"ERROR: {o['ename']}: {o['evalue']}")
        elif o["output_type"] in ("execute_result", "display_data"):
            output_summary.append(f"{o['output_type']}: {list(o.get('data', {}).keys())}")

    print(f"  Result: {status} | {elapsed:.1f}s | {len(outputs)} outputs")
    for s in output_summary[:5]:
        print(f"    {s}")
    if len(output_summary) > 5:
        print(f"    ... and {len(output_summary) - 5} more")

    cell_results.append({
        "cell_index": cell_index,
        "exec_count": exec_count,
        "status": status,
        "elapsed": elapsed,
        "num_outputs": len(outputs)
    })

# Shutdown kernel
print("\nShutting down kernel...")
kc.stop_channels()
km.shutdown_kernel()

# Save notebook
print(f"Saving notebook to {NB_PATH}")
with open(NB_PATH, "w", encoding="utf-8") as f:
    json.dump(nb, f, ensure_ascii=False, indent=1)

# Summary
print(f"\n{'='*60}")
print(f"EXECUTION SUMMARY")
print(f"{'='*60}")
total_errors = sum(1 for r in cell_results if r["status"] == "ERROR")
total_ok = sum(1 for r in cell_results if r["status"] == "OK")
print(f"Total cells executed: {exec_count}")
print(f"OK: {total_ok} | ERROR: {total_errors}")
print()
for r in cell_results:
    print(f"  Cell {r['cell_index']:3d} | exec #{r['exec_count']:2d} | {r['status']:5s} | {r['elapsed']:6.1f}s | {r['num_outputs']} outputs")
print()

if total_errors > 0:
    print("WARNING: Some cells had errors!")
    for r in cell_results:
        if r["status"] == "ERROR":
            print(f"  Cell {r['cell_index']} had an error")
else:
    print("All cells executed successfully!")

print("\nDone.")
