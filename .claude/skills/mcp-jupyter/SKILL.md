---
name: mcp-jupyter
description: Reference for MCP Jupyter tools (kernel management, cell execution, Papermill). Use when executing notebooks, managing kernels, or running code interactively via MCP.
user-invocable: false
---

# MCP Jupyter Reference

## Available Tools

| Tool | Description |
|------|-------------|
| `list_kernels()` | List available kernel specs |
| `manage_kernel(action, kernel_name/id)` | start/stop/restart/interrupt kernel |
| `execute_on_kernel(kernel_id, mode, ...)` | Execute code, cell, or full notebook |
| `execute_notebook(input_path, ...)` | Papermill execution (sync/async) |
| `read_notebook(path)` | Read notebook content |
| `read_cells(path, mode)` | Read cells (list/summary) |
| `get_notebook_info(path)` | Notebook metadata |
| `manage_async_job(action, job_id)` | Manage async Papermill jobs |

## Supported Kernels

| Kernel | Name | Notes |
|--------|------|-------|
| Python 3 | `python3` | Via ipykernel in conda `mcp-jupyter-py310` |
| .NET C# | `.net-csharp` | Via dotnet-interactive |
| .NET F# | `.net-fsharp` | Via dotnet-interactive |
| Lean 4 | `lean4` | Via WSL wrapper |

## Execution Patterns

### Python notebooks - Papermill (preferred for batch)

```python
execute_notebook(
    input_path="MyIA.AI.Notebooks/path/notebook.ipynb",
    output_path="MyIA.AI.Notebooks/path/notebook.ipynb",  # Same file = overwrite with outputs
    mode="sync"
)
```

### Python notebooks - Cell-by-cell (for control)

```python
manage_kernel(action="start", kernel_name="python3")
# Execute cells
execute_on_kernel(kernel_id="...", mode="notebook_cell", path="notebook.ipynb", cell_index=0)
# ...
manage_kernel(action="stop", kernel_id="...")
```

### .NET notebooks - Cell-by-cell ONLY

**IMPORTANT**: Papermill does NOT work with .NET notebooks. Always use cell-by-cell.

```python
manage_kernel(action="start", kernel_name=".net-csharp")

# CRITICAL: Set working directory first
execute_on_kernel(
    kernel_id="...", mode="code",
    code='System.IO.Directory.SetCurrentDirectory(@"d:\\dev\\CoursIA\\MyIA.AI.Notebooks\\Sudoku");'
)

# Execute cells sequentially
for idx in range(cell_count):
    execute_on_kernel(kernel_id="...", mode="notebook_cell", path="notebook.ipynb", cell_index=idx)

manage_kernel(action="stop", kernel_id="...")
```

## Known Issues

| Problem | Workaround |
|---------|------------|
| Papermill + `#!import` | Use cell-by-cell execution |
| Papermill + .NET kernels | Kernel hangs at startup; use cell-by-cell |
| .NET cold start timeout | Normal (30-60s); retry once |
| Async progress values incorrect | Known bug; ignore progress numbers |
| Kernel unresponsive after failed Papermill | Stop and restart kernel |
| Relative paths fail | Set working directory explicitly |
| Widgets/interactive elements | Use BATCH_MODE=true parameter |
