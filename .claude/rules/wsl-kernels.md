---
paths: "{MyIA.AI.Notebooks/GameTheory/**/*,MyIA.AI.Notebooks/SymbolicAI/Lean/**/*}"
---

# WSL Kernel Rules

**Diagnostic detaille (issues, paths, heredoc, setup, verifications)** : [docs/wsl-kernels-detail.md](../../docs/wsl-kernels-detail.md).

## Regles HARD

- **GameTheory/Lean Python notebooks** : utiliser `scripts/notebook_tools/wsl_papermill.py` (papermill execute INSIDE WSL, evite la frontiere cross-OS).
- **.NET Interactive notebooks** : cell-by-cell via MCP Jupyter (Windows-side). Pas de Papermill (non supporte).
- **Cold start .NET Interactive** : premier demarrage peut timeout (30-60s) — retry une fois avant d'escalader.
- **Wrapper bash obligatoire** pour kernels WSL — wrapper Python ne marche PAS (backslashes consommes).

## Commandes courantes

```powershell
python scripts/notebook_tools/wsl_papermill.py execute <notebook.ipynb> [--timeout 300]
python scripts/notebook_tools/wsl_papermill.py batch MyIA.AI.Notebooks/GameTheory/
python scripts/notebook_tools/wsl_papermill.py check-env
```
