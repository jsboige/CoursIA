Execute a Jupyter notebook with full lifecycle management: $ARGUMENTS

Use the `execute-notebook` and `mcp-jupyter` skills for detailed execution patterns.

Arguments: `<notebook_path> [--mode=full|selective|papermill] [--cells=0,5,10] [--timeout=300] [--batch] [--save]`

Execution methods (choose based on kernel):
- **Python + Papermill** (batch, preferred): `python scripts/notebook_tools.py execute {path} --timeout 300`
- **Python + cell-by-cell** (control): `python scripts/notebook_helpers.py execute {path} --verbose`
- **Python + MCP** (interactive): `manage_kernel(action="start", kernel_name="python3")` + `execute_on_kernel`
- **.NET + MCP only** (Papermill blocked): Cell-by-cell via MCP, set working directory first
- **GenAI**: Check `.env` first with `/validate-genai`, use `--batch` for interactive widgets

Scripts in `scripts/` are the PRIMARY tool for Python notebooks. MCP is required for .NET and interactive debugging.
