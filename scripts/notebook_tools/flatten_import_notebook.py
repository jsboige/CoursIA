#!/usr/bin/env python3
"""Flatten (and optionally headless-execute) a notebook that uses the
``#!import`` magic command.

WHY THIS TOOL EXISTS
--------------------
``dotnet-interactive``'s ``#!import <Other.ipynb>`` magic command lets a .NET
notebook pull in another notebook's cells (shared helper classes, e.g. the
Sudoku family's ``Sudoku-0-Environment-Csharp.ipynb`` defining ``SudokuGrid`` /
``SudokuHelper``). It works in the VS Code Interactive / Jupyter context but
THROWS ``ArgumentNullException (key=null)`` in ``LoadAndRunInteractiveDocument``
under headless execution (nbclient / papermill / nbconvert --execute) -- see
the durable #4394 (the ``#!import`` magic command needs a VS Code Interactive
context that headless servers do not provide).

Consequence: 11 of 14 ``Sudoku/*-Csharp.ipynb`` notebooks (every one that
shares helpers via ``#!import``) are NOT re-executable headless. Any source
edit to them = a C.2 violation (cannot re-execute to refresh outputs), and
they are invisible to the H.3 pre-commit / batch-reexecute / #3436 path-leak
scans.

THE WORKAROUND
--------------
This tool PRE-PROCESSES the ``#!import`` directive by textually inlining the
imported notebook's cells at the import site (recursively, for chained
imports), producing a self-contained notebook that nbclient CAN execute
headless -- the imported cells run first in the same kernel, so the kernel
state (classes, helpers) is identical to a real ``#!import``.

Verified firsthand on ``Sudoku-3-Genetic-Csharp``: flatten 28 -> 41 cells,
headless exec via nbclient (.net-csharp kernel) in 69s, 17 code cells
ec 1..17, 0 errors, ``SudokuHelper`` resolves, C.1 stubs intact.

Usage
-----
    # Produce a flattened copy (default: <name>_flat.ipynb beside the input):
    python flatten_import_notebook.py Sudoku-3-Genetic-Csharp.ipynb

    # Flatten + headless-execute, reporting per-cell errors (no file written):
    python flatten_import_notebook.py Sudoku-3-Genetic-Csharp.ipynb --execute

    # Write the flattened notebook to a specific path:
    python flatten_import_notebook.py NB.ipynb --output NB_flat.ipynb

    # Inspect what would be inlined without writing/executing:
    python flatten_import_notebook.py NB.ipynb --stdout | head

Exit codes
----------
    0 -- notebook flattened (and executed with 0 errors if --execute)
    1 -- the notebook has no #!import (nothing to do), or execution had errors

Scope: pure transform + optional execution. NEVER writes the original
notebook in place -- flattening is a build artefact, the source keeps its
``#!import`` (the canonical, VS Code-runnable form).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

import nbformat

# `#!import <path>.ipynb` -- the dotnet-interactive magic command. The target
# is resolved RELATIVE TO THE IMPORTING NOTEBOOK'S DIRECTORY (same convention
# as dotnet-interactive). We match the first .ipynb token after #!import.
IMPORT_RE = re.compile(r"#!import\s+([^\s]+\.ipynb)")


def has_import_directive(nb) -> bool:
    """True if any code cell of ``nb`` contains a ``#!import`` line."""
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        if IMPORT_RE.search("".join(cell.get("source", []))):
            return True
    return False


def flatten_notebook(nb_path: Path, _seen: tuple[Path, ...] = ()):
    """Recursively inline ``#!import`` targets, return a flattened notebook.

    Each ``#!import X.ipynb`` code cell is REPLACED IN PLACE by X's own cells
    (X is itself flattened first, so chained imports A->B->C resolve). The
    import target is resolved relative to ``nb_path``'s parent directory. A
    non-existent target is left AS-IS (the cell is kept verbatim) so the
    failure surfaces as a normal CellExecutionError on execute rather than a
    silent drop.

    Cycle-safe: each resolved absolute path is tracked in ``_seen``; a target
    already on the chain is skipped (prevents infinite recursion on A->B->A).
    """
    nb_path = nb_path.resolve()
    nb = nbformat.read(nb_path, as_version=4)
    if not has_import_directive(nb):
        return nb

    flat_cells = []
    seen = _seen + (nb_path,)
    base_dir = nb_path.parent
    for cell in nb.cells:
        if cell.cell_type != "code":
            flat_cells.append(cell)
            continue
        m = IMPORT_RE.search("".join(cell.source))
        if not m:
            flat_cells.append(cell)
            continue
        target = (base_dir / m.group(1)).resolve()
        if not target.exists() or target in seen:
            # Leave the import cell verbatim -- execute will fail loudly on it.
            flat_cells.append(cell)
            continue
        imported_flat = flatten_notebook(target, seen)
        flat_cells.extend(imported_flat.cells)

    new_nb = nbformat.v4.new_notebook()
    new_nb.cells = flat_cells
    new_nb.metadata = dict(nb.metadata)
    return new_nb


def execute_flattened(nb_path: Path, kernel: str | None = None,
                      timeout: int = 300) -> tuple[bool, str]:
    """Flatten ``nb_path`` then headless-execute it via nbclient.

    Returns ``(ok, message)``. ``ok`` is True iff execution completed with 0
    cell errors. Uses the notebook's own kernelspec unless ``kernel`` overrides
    (needed when the source kernelspec name differs from the registered
    kernel, e.g. ``C#`` display-name vs ``.net-csharp`` registered name).
    """
    from nbclient import NotebookClient  # local import: nbclient is optional for flatten-only

    flat = flatten_notebook(nb_path)
    for c in flat.cells:
        if c.cell_type == "code":
            c.outputs = []
            c.execution_count = None
    kernel_name = kernel or flat.metadata.get("kernelspec", {}).get("name", "python3")
    client = NotebookClient(
        flat, kernel_name=kernel_name, timeout=timeout,
        resources={"metadata": {"path": str(nb_path.resolve().parent)}},
    )
    try:
        client.execute()
    except Exception as exc:  # CellExecutionError or kernel startup failure
        errs = []
        for c in flat.cells:
            if c.cell_type != "code":
                continue
            for o in c.get("outputs", []):
                if o.get("output_type") == "error":
                    errs.append(f"cell ec={c.execution_count}: {o.get('ename')}: {o.get('evalue', '')[:140]}")
        msg = "; ".join(errs) if errs else f"{type(exc).__name__}: {exc}"
        return False, msg
    code = [c for c in flat.cells if c.cell_type == "code"]
    ecs = [c.execution_count for c in code if c.execution_count]
    n_err = sum(1 for c in code for o in c.get("outputs", []) if o.get("output_type") == "error")
    span = f"{min(ecs)}..{max(ecs)}" if ecs else "(none)"
    return True, f"{len(code)} code cells ec {span}, {n_err} errors"


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Flatten (and optionally headless-execute) a #!import notebook (#4394 workaround).",
    )
    p.add_argument("notebook", type=Path, help="Notebook using #!import")
    p.add_argument("--output", "-o", type=Path, default=None,
                   help="Write flattened notebook here (default: <name>_flat.ipynb beside input)")
    p.add_argument("--stdout", action="store_true",
                   help="Write flattened notebook JSON to stdout (no file written)")
    p.add_argument("--execute", action="store_true",
                   help="Flatten then headless-execute via nbclient; report errors (no file written)")
    p.add_argument("--kernel", default=None,
                   help="Override kernel name for --execute (e.g. .net-csharp)")
    p.add_argument("--timeout", type=int, default=300,
                   help="Per-notebook execution timeout in seconds (default 300)")
    args = p.parse_args(argv)

    if not args.notebook.exists():
        print(f"error: notebook not found: {args.notebook}", file=sys.stderr)
        return 2

    source_nb = nbformat.read(args.notebook, as_version=4)
    if not has_import_directive(source_nb):
        print(f"notebook has no #!import directive; nothing to flatten: {args.notebook}")
        return 1

    flat = flatten_notebook(args.notebook)
    n_before = len(source_nb.cells)
    n_after = len(flat.cells)
    # Progress goes to stderr so --stdout emits PURE notebook JSON.
    print(f"flattened: {n_before} -> {n_after} cells ({args.notebook.name})", file=sys.stderr)

    if args.execute:
        ok, msg = execute_flattened(args.notebook, kernel=args.kernel, timeout=args.timeout)
        status = "EXEC SUCCESS" if ok else "EXEC FAILED"
        print(f"{status}: {msg}")
        return 0 if ok else 1

    if args.stdout:
        sys.stdout.write(nbformat.writes(flat))
        return 0

    out = args.output or args.notebook.with_name(args.notebook.stem + "_flat.ipynb")
    nbformat.write(flat, out)
    print(f"wrote flattened notebook: {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
