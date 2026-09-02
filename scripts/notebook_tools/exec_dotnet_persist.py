#!/usr/bin/env python3
"""Compatibility wrapper around the canonical .NET notebook executor.

New callers should use ``dotnet_executor.py`` directly. This module preserves
its historical positional CLI and ``execute_and_persist`` tuple return value.
"""

import json
import sys
from pathlib import Path

from _papermill_meta import strip_stale_papermill_metadata
from dotnet_executor import execute_notebook, split_text_lines


_LEGACY_MIME_TYPES = ("text/plain", "text/html", "image/svg+xml")


def _save_executed(nb: dict, path: Path) -> None:
    """Persist a notebook after removing stale Papermill metadata.

    Kept as a public compatibility helper for callers and unit tests that use
    the historical write boundary without starting a kernel.
    """
    strip_stale_papermill_metadata(nb)
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(nb, handle, indent=1, ensure_ascii=False)


def execute_and_persist(notebook_path: str, timeout_per_cell: int = 120):
    """Execute through the canonical engine and return ``(executed, errors)``."""
    path = Path(notebook_path)
    with open(path, "r", encoding="utf-8") as handle:
        nb = json.load(handle)

    kernel_name = nb.get("metadata", {}).get("kernelspec", {}).get(
        "name", ".net-csharp"
    )
    print(f"Executing {path.name} (kernel={kernel_name})")

    stats = execute_notebook(
        path,
        kernel_name=kernel_name,
        cell_timeout=timeout_per_cell,
        ready_timeout=120,
        skip_empty_code_cells=True,
        text_as_lines=True,
        allowed_mime_types=_LEGACY_MIME_TYPES,
        idle_grace=2.0,
    )
    return stats["executed"], stats["errors"]


def _split_lines(text):
    """Preserve the historical helper name for downstream imports."""
    return split_text_lines(text)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python exec_dotnet_persist.py <notebook.ipynb> [timeout]")
        sys.exit(1)

    nb_path = sys.argv[1]
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 120

    executed, errors = execute_and_persist(nb_path, timeout_per_cell=timeout)
    print(f"\nResult: {executed} cells, {errors} errors")
    sys.exit(1 if errors > 0 else 0)
