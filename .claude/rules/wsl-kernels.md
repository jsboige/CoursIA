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

## Key Rules

- A Python wrapper does NOT work for WSL kernels - MUST use a bash wrapper
- Always use absolute paths in `kernel.json` for `dotnet-interactive.exe`
- Cold start for .NET Interactive: first start may timeout (30-60s), retry once
- GameTheory notebooks require `Python (GameTheory WSL + OpenSpiel)` kernel
- Lean notebooks require `Python 3 (WSL)` or `Lean 4 (WSL)` kernels
