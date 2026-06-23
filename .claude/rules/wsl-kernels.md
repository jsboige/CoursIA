---
paths: "{MyIA.AI.Notebooks/GameTheory/**/*,MyIA.AI.Notebooks/SymbolicAI/Lean/**/*}"
---

# WSL Kernel Rules

**Detail deporte** : [docs/wsl-kernels-detail.md](../../docs/reference/wsl-kernels-detail.md) — issues/paths/heredoc, architecture kernel Lean 4, setup consolide (`scripts/lean/setup_lean4_all.py`, #1618), commandes de diagnostic, incident 2026-05-27.

## Regles HARD

- **GameTheory/Lean Python notebooks** : utiliser `scripts/notebook_tools/wsl_papermill.py` (papermill execute INSIDE WSL, evite la frontiere cross-OS).
- **.NET Interactive notebooks** : cell-by-cell via MCP Jupyter (Windows-side). Pas de Papermill (non supporte).
- **Cold start .NET Interactive** : premier demarrage peut timeout (30-60s) — retry une fois avant d'escalader.
- **Lean 4 kernel (lean4-wsl)** : utiliser `--kernel lean4-wsl` avec papermill. Le wrapper Python `~/.lean4-kernel-wrapper.py` (v5) gere la conversion Windows→WSL paths et les permissions NTFS. L'ancien wrapper bash `~/lean4-jupyter-wrapper.sh` est **OBSOLETE** — ne pas l'utiliser.

## Setup / diagnostic kernel Lean 4

Point d'entree unique (installe + enregistre + valide, #1618) : `python scripts/lean/setup_lean4_all.py` (`--check-wrapper` verifie que `kernel.json` pointe vers le wrapper v5 `~/.lean4-kernel-wrapper.py`, pas l'ancien bash). Architecture, commandes de diagnostic manuelles et incident 2026-05-27 : [docs/wsl-kernels-detail.md](../../docs/reference/wsl-kernels-detail.md).

## Commandes courantes

```powershell
# Execution notebooks Lean
python scripts/notebook_tools/wsl_papermill.py execute <notebook.ipynb> --kernel lean4-wsl --timeout 600

# Execution notebooks Python
python scripts/notebook_tools/wsl_papermill.py execute <notebook.ipynb> [--timeout 300]

# Batch
python scripts/notebook_tools/wsl_papermill.py batch MyIA.AI.Notebooks/GameTheory/ --kernel lean4-wsl

# Verifier environnement
python scripts/notebook_tools/wsl_papermill.py check-env
```
