Build, improve, or fix Jupyter notebooks iteratively: $ARGUMENTS

Use the `build-notebook` skill for the detailed workflow and quality scoring.

Actions:
- `new <path> --topic=X --domain=X --level=X` - Create from scratch (notebook-designer, model: inherit)
- `improve <path> [--quality=90] [--focus=execution|pedagogy|content|structure]` - Enhance existing
- `fix <path> [--max-iter=5]` - Correct execution errors

Iterative loop:
1. Execute via `python scripts/notebook_tools.py execute {path}` or MCP cell-by-cell
2. Validate via `python scripts/notebook_tools.py validate {path}`
3. Analyze errors with `python scripts/notebook_helpers.py list {path} --verbose`
4. Apply fixes via appropriate sub-agent (enricher, cell-iterator, cleaner)
5. Re-validate and measure improvement

Quality target default: 90/100. Sub-agents: designer (inherit), executor (sonnet), validator (sonnet), enricher (sonnet), cell-iterator (sonnet), cleaner (sonnet).
