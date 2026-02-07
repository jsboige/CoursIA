---
name: verify-notebooks
description: Verify and test Jupyter notebooks with iterative fixing. Arguments: [target] [--quick] [--fix] [--python-only] [--dotnet-only]
---

# Verify Notebooks

Verify and test Jupyter notebooks in the CoursIA repository.

**Target**: `$ARGUMENTS`

## Arguments

- `target`: Notebook path, family name (`Sudoku`, `Search`, `SymbolicAI`, `Argument_Analysis`, `GenAI`, `ML`, `Probas`, `IIT`, `Tweety`, `Lean`, `GameTheory`), or `all`
- `--quick`: Structure validation only, no execution
- `--fix`: Attempt automatic fixes (max 3 attempts per cell)
- `--python-only` / `--dotnet-only`: Filter by kernel type

## Process

1. **Parse target** - Determine individual file, family, or all
2. **Discover notebooks** - Use `python scripts/notebook_tools.py validate {target} --quick` for rapid discovery and structure check
3. **Categorize by kernel** - `python scripts/notebook_helpers.py detect-kernel {path}`
4. **Execute tests**:
   - **Python (preferred)**: `python scripts/notebook_tools.py execute {target} --timeout 300`
   - **Python (alternative)**: `python scripts/notebook_helpers.py execute {path} --verbose` (cell-by-cell with output)
   - **.NET**: MCP cell-by-cell only (see `mcp-jupyter` skill) - Papermill does NOT work
5. **Analyze errors** - `python scripts/notebook_helpers.py list {path} --verbose` to inspect failed cells
6. **If --fix**: Use notebook-cell-iterator agent (model: sonnet) for targeted cell corrections (max 3 attempts)
7. **Generate summary report**

## Family Reference

| Family | Path | Kernel | Notes |
|--------|------|--------|-------|
| Sudoku | Sudoku/ | .NET C# | `#!import`, cell-by-cell only |
| Search | Search/ | Mixed | GeneticSharp=C#, PyGad=Python |
| SymbolicAI | SymbolicAI/ | Mixed | Tweety=Python+JPype |
| GenAI | GenAI/ | Python | API keys required, use `/validate-genai` first |
| Probas | Probas/ | .NET C# | Infer.NET |
| GameTheory | GameTheory/ | Python (WSL) | OpenSpiel |
| Lean | SymbolicAI/Lean/ | Lean 4 / Python (WSL) | WSL kernels |

## GenAI-Specific

For GenAI notebooks, use dedicated scripts:
```bash
python scripts/genai-stack/validate_stack.py
python scripts/genai-stack/validate_notebooks.py MyIA.AI.Notebooks/GenAI/Image/
```

Use `/validate-genai` to validate the stack before running notebooks.

## Known Limitations

1. Widgets/interactive notebooks cannot run in batch mode
2. GenAI notebooks require GPU for some operations
3. .NET cold start may timeout initially (30-60s), retry once
4. External services (DBpedia, etc.) may be unavailable
