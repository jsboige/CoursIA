---
name: verify-notebooks
description: Verify and test Jupyter notebooks with iterative fixing
argument-hint: "[target] [--quick] [--fix] [--python-only] [--dotnet-only]"
disable-model-invocation: true
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
2. **Discover notebooks** - Use Glob: `MyIA.AI.Notebooks/{family}/**/*.ipynb` (exclude `*_output.ipynb`)
3. **Categorize by kernel** - Python (Papermill) vs .NET (cell-by-cell via MCP)
4. **Execute tests**:
   - Python: `cd "{dir}" && python -m papermill "{nb}" "{nb}_output.ipynb" --kernel python3 -p BATCH_MODE true`
   - .NET: MCP cell-by-cell (see mcp-jupyter skill for patterns)
5. **Analyze results** - Report SUCCESS/ERROR/SKIPPED per notebook
6. **If --fix**: Read error, identify cell, analyze root cause, apply fix, re-execute (max 3 attempts)
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
