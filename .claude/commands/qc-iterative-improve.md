Execute iterative improvement workflow for QuantConnect strategies: $ARGUMENTS

Use the `qc-iterative-improve` skill for the detailed workflow.

Usage:
- `qc-iterative-improve` - Improve all strategies in lean-workspace
- `qc-iterative-improve BTC-ML` - Improve specific strategy
- `qc-iterative-improve --iterations=5` - Custom iteration count
- `qc-iterative-improve --no-backtest` - Compile only, skip backtests

Workflow per strategy:
1. Verify environment (Docker, lean-cli, QC cloud, MCP)
2. Read notebook + algo + README + last backtest
3. Add diagnostic cells to notebook
4. Explore improvement ideas iteratively
5. Implement confirmed improvements in algo
6. Push to cloud + compile + backtest
7. If improved: commit, else: revert

Sub-agent: qc-strategy-improver (model: sonnet, skills: qc-helpers, notebook-helpers, mcp-jupyter)
