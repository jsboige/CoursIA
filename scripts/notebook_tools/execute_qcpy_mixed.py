"""Execute MIXED QC-Py notebooks via nbconvert with allow_errors=True.

Copies outputs back to originals. REFERENCE_ONLY notebooks are skipped.
Outputs a JSON report with per-notebook stats.
"""

import json
import os
import sys
import time
import warnings

import nbformat
from nbconvert.preprocessors import ExecutePreprocessor

warnings.filterwarnings("ignore")

QC_DIR = os.path.join("MyIA.AI.Notebooks", "QuantConnect", "Python")
REPORT_PATH = os.path.join(os.environ.get("TEMP", "/tmp"), "qcpy_batch", "report.json")


def classify_notebook(nb):
    code_cells = [c for c in nb.cells if c.cell_type == "code"]
    if not code_cells:
        return "NO_CODE", 0, 0

    has_qc = False
    has_local = False
    for c in code_cells:
        src = "".join(c.source)
        if any(
            marker in src
            for marker in ["[REFERENCE QC]", "QCAlgorithm", "from AlgorithmImports"]
        ):
            has_qc = True
        else:
            has_local = True

    executed = sum(1 for c in code_cells if c.get("execution_count") is not None)
    if executed == len(code_cells):
        return "ALREADY_EXEC", len(code_cells), executed
    if has_qc and not has_local:
        return "REFERENCE_ONLY", len(code_cells), 0
    if has_qc and has_local:
        return "MIXED", len(code_cells), executed
    return "LOCAL_PYTHON", len(code_cells), executed


def execute_notebook(nb_path, timeout=300):
    nb = nbformat.read(nb_path, as_version=4)
    ep = ExecutePreprocessor(timeout=timeout, kernel_name="python3", allow_errors=True)

    t0 = time.time()
    try:
        ep.preprocess(nb, {"metadata": {"path": os.path.dirname(nb_path)}})
    except Exception:
        pass  # allow_errors handles cell-level failures
    elapsed = time.time() - t0

    code_cells = [c for c in nb.cells if c.cell_type == "code"]
    executed = sum(1 for c in code_cells if c.get("execution_count") is not None)
    errors = sum(
        1
        for c in code_cells
        if any(o.get("output_type") == "error" for o in c.get("outputs", []))
    )

    return nb, {
        "cells": len(code_cells),
        "executed": executed,
        "errors": errors,
        "elapsed_s": round(elapsed, 1),
    }


def copy_outputs_back(src_path, executed_nb):
    """Copy execution_count and outputs from executed nb into original file."""
    orig = nbformat.read(src_path, as_version=4)
    orig_code = [c for c in orig.cells if c.cell_type == "code"]
    exec_code = [c for c in executed_nb.cells if c.cell_type == "code"]

    if len(orig_code) != len(exec_code):
        return False, f"Cell count mismatch: orig={len(orig_code)} exec={len(exec_code)}"

    for oc, ec in zip(orig_code, exec_code):
        oc["execution_count"] = ec.get("execution_count")
        oc["outputs"] = ec.get("outputs", [])

    # Use nbformat.write for clean serialization
    nbformat.write(orig, src_path)
    return True, "OK"


def main():
    os.makedirs(os.path.dirname(REPORT_PATH), exist_ok=True)

    # Collect all QC-Py notebooks
    notebooks = sorted(
        f
        for f in os.listdir(QC_DIR)
        if f.startswith("QC-Py-") and f.endswith(".ipynb") and "_output" not in f
    )

    results = {}
    to_execute = []

    print("=== Classification ===")
    for fname in notebooks:
        path = os.path.join(QC_DIR, fname)
        nb = nbformat.read(path, as_version=4)
        cls, n_code, n_exec = classify_notebook(nb)
        results[fname] = {"classification": cls, "code_cells": n_code, "already_exec": n_exec}

        if cls == "MIXED" or cls == "LOCAL_PYTHON":
            to_execute.append(fname)
            print(f"  {fname:<55} {cls:<16} {n_code} cells -> WILL EXECUTE")
        elif cls == "REFERENCE_ONLY":
            print(f"  {fname:<55} {cls:<16} {n_code} cells -> SKIP (ref only)")
        elif cls == "ALREADY_EXEC":
            print(f"  {fname:<55} {cls:<16} {n_code} cells -> SKIP (already done)")
        else:
            print(f"  {fname:<55} {cls:<16} {n_code} cells -> SKIP")

    print(f"\n=== Executing {len(to_execute)} notebooks ===")
    for i, fname in enumerate(to_execute, 1):
        path = os.path.join(QC_DIR, fname)
        print(f"[{i}/{len(to_execute)}] {fname}...", end=" ", flush=True)

        try:
            executed_nb, stats = execute_notebook(path)
            ok, msg = copy_outputs_back(path, executed_nb)
            results[fname].update(stats)
            results[fname]["copy_back"] = "OK" if ok else f"FAIL: {msg}"

            status = "OK" if stats["executed"] == stats["cells"] and stats["errors"] == 0 else "PARTIAL"
            print(
                f"{status} ({stats['executed']}/{stats['cells']}, "
                f"{stats['errors']} err, {stats['elapsed_s']}s)"
            )
        except Exception as e:
            results[fname]["error"] = str(e)
            print(f"FAIL: {e}")

    # Save report
    with open(REPORT_PATH, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, default=str)

    # Summary
    ok_count = sum(
        1 for r in results.values()
        if r.get("copy_back") == "OK" and r.get("executed", 0) == r.get("cells", 0) and r.get("errors", 0) == 0
    )
    partial_count = sum(
        1 for r in results.values()
        if r.get("copy_back") == "OK" and (r.get("executed", 0) < r.get("cells", 0) or r.get("errors", 0) > 0)
    )
    print(f"\n=== SUMMARY ===")
    print(f"FULL_OK: {ok_count}  PARTIAL: {partial_count}  SKIPPED: {len(notebooks) - ok_count - partial_count}")
    print(f"Report: {REPORT_PATH}")


if __name__ == "__main__":
    main()
