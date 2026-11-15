"""Execute Kelly_companion-Optimist-Bias-Python.ipynb via nbclient (simpler)."""

import asyncio
from pathlib import Path

import nbformat
from nbclient import NotebookClient


NB_PATH = Path(r"D:/Dev/CoursIA-2-c1494-19516-optimist/MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion-Optimist-Bias-Python.ipynb")
NB_DIR = NB_PATH.parent


async def main():
    nb = nbformat.read(NB_PATH, as_version=4)

    # nbformat 5.x: ensure all cell sources are str
    for c in nb.cells:
        if isinstance(c.source, list):
            c.source = ''.join(c.source)

    client = NotebookClient(
        nb,
        kernel_name="python3",
        timeout=600,
        resources={"metadata": {"path": str(NB_DIR)}},
    )

    async with client.async_setup_kernel():
        for idx, cell in enumerate(nb.cells):
            if cell.cell_type != "code":
                continue
            try:
                if isinstance(cell.source, list):
                    cell.source = ''.join(cell.source)
                await client.async_execute_cell(cell, cell_index=idx)
                ec = cell.get("execution_count")
                outputs = cell.get("outputs", [])
                err = any(o.get("output_type") == "error" for o in outputs)
                print(f"  Cell {idx}: exec_count={ec}, outputs={len(outputs)}, error={err}")
            except Exception as e:
                print(f"  Cell {idx}: EXCEPTION {type(e).__name__}: {e}")

    nbformat.write(nb, NB_PATH, version=4)
    print(f"\nNotebook written: {NB_PATH}")
    n_code = sum(1 for c in nb.cells if c.cell_type == "code")
    n_exec = sum(1 for c in nb.cells if c.cell_type == "code" and c.get("execution_count") is not None)
    print(f"Total cells: {len(nb.cells)}, code cells: {n_code}, with exec_count: {n_exec}")


if __name__ == "__main__":
    asyncio.run(main())