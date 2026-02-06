---
name: execute-notebook
description: Execute Jupyter notebooks via MCP Jupyter with kernel management
argument-hint: "<notebook_path> [--mode=full|selective|papermill] [--cells=0,5,10] [--timeout=300] [--batch] [--save]"
disable-model-invocation: true
---

# Execute Notebook

Execute a Jupyter notebook with full kernel lifecycle management.

**Notebook**: `$ARGUMENTS`

## Options

- `--mode`: full (default), selective, papermill
- `--cells`: Specific cells (e.g., 0,5,10)
- `--timeout`: Per-cell timeout in seconds (default 300)
- `--stop-on-error`: Halt on first error
- `--batch`: Enable BATCH_MODE for interactive notebooks
- `--save`: Save outputs to original notebook

## Execution by Kernel Type

### Python (kernel: python3)
- **Papermill** (preferred for batch): `python -m papermill "{nb}" "{output}" --kernel python3`
- **Cell-by-cell** (for control): MCP `manage_kernel` + `execute_on_kernel`

### .NET (kernel: .net-csharp)
- **Cell-by-cell ONLY** - Papermill does NOT work with .NET
- CRITICAL: Set working directory first with `SetCurrentDirectory()`

### GenAI notebooks
- Check `.env` configuration first (use `/validate-genai`)
- Use `--batch` for notebooks with interactive widgets

## Error Handling

| Error | Cause | Solution |
|-------|-------|----------|
| Kernel timeout | .NET cold start | Retry (30-60s normal) |
| File not found | Wrong directory | SetCurrentDirectory() |
| ModuleNotFoundError | Missing dependency | pip install |
| API key missing | .env not configured | Check OPENAI_API_KEY etc. |

## Report Format

Report: notebook name, kernel, mode, total/executed/successful/error cells, timing, error details.
