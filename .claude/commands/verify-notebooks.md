Verify and test Jupyter notebooks: $ARGUMENTS

Use the `verify-notebooks` skill for the detailed process. Key steps:

1. **Parse target** - Individual file, family name (`Sudoku`, `Search`, `GenAI`, `Tweety`, `Lean`, `GameTheory`, etc.), or `all`
2. **Discover notebooks** - Use `python scripts/notebook_tools.py validate {target} --quick` for structure check
3. **Execute** - Use `python scripts/notebook_tools.py execute {target}` for full execution, or MCP for interactive control
4. **If --fix** - Use notebook-cell-iterator agent for targeted corrections (max 3 attempts per cell)
5. **Report** - Generate summary with SUCCESS/ERROR/SKIPPED per notebook

Arguments: `[target] [--quick] [--fix] [--python-only] [--dotnet-only]`

Tools available:
- **Scripts (preferred for batch)**: `python scripts/notebook_tools.py validate`, `python scripts/notebook_helpers.py execute`
- **MCP Jupyter (for interactive)**: `manage_kernel`, `execute_on_kernel` (cell-by-cell for .NET)
- **Sub-agents**: Use notebook-validator (model: sonnet) for validation, notebook-cell-iterator for fixes
