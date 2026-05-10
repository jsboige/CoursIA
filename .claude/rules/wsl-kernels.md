---
paths: "{MyIA.AI.Notebooks/GameTheory/**/*,MyIA.AI.Notebooks/SymbolicAI/Lean/**/*}"
---

# WSL Kernel Rules

## Known Issues

| Problem | Cause | Solution |
|---------|-------|----------|
| Backslashes stripped | WSL shell consumes ALL `\` | Use a bash wrapper (NOT Python) with regex reconstruction |
| Path without separators | `~\AppData\...\kernel.json` becomes `c:UsersjsboiAppData...` | Regex: `^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$` |
| SyntaxWarning: invalid escape | Docstrings with `\A`, `\U` | Use `#` comments, not docstrings |
| Heredoc variables interpolated | `cat << 'EOF'` in `bash -c '...'` | Write script via temp file, then copy to WSL |
| Kernel timeout 60s | Wrapper script errors | Check `/tmp/kernel-wrapper.log` in WSL |

## Solution: WSL Papermill (2026-05-10, T20.17)

Windows-side `jupyter_client` cannot connect to WSL kernels because WSL strips
backslashes from connection file paths. The workaround: **run papermill directly
inside WSL**, avoiding the cross-OS boundary entirely.

### Setup (one-time)

```powershell
wsl -e bash -c "python3 -m venv ~/coursia-wsl"
wsl -e bash -c "source ~/coursia-wsl/bin/activate && pip install nashpy matplotlib papermill ipykernel scipy numpy"
wsl -e bash -c "source ~/coursia-wsl/bin/activate && python3 -m ipykernel install --user --name python3"
```

### Usage

```powershell
# Single notebook
python scripts/notebook_tools/wsl_papermill.py execute <notebook.ipynb> [--timeout 300]

# Batch directory
python scripts/notebook_tools/wsl_papermill.py batch MyIA.AI.Notebooks/GameTheory/ [--timeout 300]

# Check environment
python scripts/notebook_tools/wsl_papermill.py check-env
```

### Verified
- GT-1 Setup: 20/20 cells, 0 errors (3.3s)
- GT-7 ExtensiveForm: 30/30 cells, 0 errors (2s)

## Key Rules

- **For GameTheory/Lean Python notebooks**: use `wsl_papermill.py` (papermill inside WSL)
- **For .NET Interactive notebooks**: use cell-by-cell via MCP Jupyter (Windows-side)
- Cold start for .NET Interactive: first start may timeout (30-60s), retry once
- GameTheory notebooks require nashpy, matplotlib, scipy (installed in WSL venv)
- Lean notebooks use `lake build` directly in WSL for compilation verification
