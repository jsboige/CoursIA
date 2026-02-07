---
name: execute-notebook
description: Execute Jupyter notebooks using local scripts or MCP Jupyter. Arguments: <notebook_path> [--mode] [--cells] [--timeout] [--batch] [--save]
---

# Execute Notebook

Execute a Jupyter notebook with full lifecycle management.

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

**Local scripts (preferred for batch)**:
```bash
# Full execution via notebook_tools.py
python scripts/notebook_tools.py execute {path} --timeout 300

# Cell-by-cell with verbose output via notebook_helpers.py
python scripts/notebook_helpers.py execute {path} --verbose

# Specific cell execution
python scripts/notebook_helpers.py execute {path} --cell 5 --timeout 60
```

**MCP (for interactive debugging)**:
- `manage_kernel(action="start", kernel_name="python3")` + `execute_on_kernel`

### .NET (kernel: .net-csharp)
- **MCP cell-by-cell ONLY** - Papermill and local scripts do NOT work with .NET kernels
- CRITICAL: Set working directory first with `SetCurrentDirectory()`
- See `mcp-jupyter` skill for detailed .NET patterns

### GenAI notebooks
- Check `.env` configuration first (use `/validate-genai`)
- Use `--batch` for notebooks with interactive widgets
- Use dedicated scripts: `python scripts/genai-stack/validate_notebooks.py`

## Error Handling

| Error | Cause | Solution |
|-------|-------|----------|
| Kernel timeout | .NET cold start | Retry (30-60s normal) |
| File not found | Wrong directory | SetCurrentDirectory() |
| ModuleNotFoundError | Missing dependency | pip install |
| API key missing | .env not configured | Check OPENAI_API_KEY etc. |

## Report Format

Report: notebook name, kernel, mode, total/executed/successful/error cells, timing, error details.
