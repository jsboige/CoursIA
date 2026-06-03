---
paths: "{MyIA.AI.Notebooks/GameTheory/**/*,MyIA.AI.Notebooks/SymbolicAI/Lean/**/*}"
---

# WSL Kernel Rules

**Diagnostic detaille (issues, paths, heredoc, setup, verifications)** : [docs/wsl-kernels-detail.md](../../docs/wsl-kernels-detail.md).

## Regles HARD

- **GameTheory/Lean Python notebooks** : utiliser `scripts/notebook_tools/wsl_papermill.py` (papermill execute INSIDE WSL, evite la frontiere cross-OS).
- **.NET Interactive notebooks** : cell-by-cell via MCP Jupyter (Windows-side). Pas de Papermill (non supporte).
- **Cold start .NET Interactive** : premier demarrage peut timeout (30-60s) — retry une fois avant d'escalader.
- **Lean 4 kernel (lean4-wsl)** : utiliser `--kernel lean4-wsl` avec papermill. Le wrapper Python `~/.lean4-kernel-wrapper.py` (v5) gere la conversion Windows→WSL paths et les permissions NTFS. L'ancien wrapper bash `~/lean4-jupyter-wrapper.sh` est **OBSOLETE** — ne pas l'utiliser.

## Lean 4 Kernel — Setup et diagnostic

### Architecture

```
Windows (Jupyter)                  WSL (Ubuntu)
   kernel.json ──────────────────> ~/.lean4-kernel-wrapper.py (v5)
   %APPDATA%/jupyter/                ↓
     kernels/lean4-wsl/            ~/.lean4-venv/bin/python3 -m lean4_jupyter
                                    cd ~/lean-projects/notebook_context
                                    REPL: ~/.elan/bin/repl
```

### Installation (scripts existants)

1. **WSL setup** : `MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_lean4.sh`
   - Installe elan, Lean 4 stable, Python venv `~/.lean4-venv`, lean4_jupyter, REPL
   - Cree le wrapper `~/.lean4-kernel-wrapper.py` avec conversion paths Windows→WSL
   - Build le REPL depuis `leanprover-community/repl`, copie dans `~/.elan/bin/`

2. **Windows registration** : `MyIA.AI.Notebooks/GameTheory/scripts/setup_lean4_kernel.ps1`
   - Cree kernel.json dans `%APPDATA%/jupyter/kernels/lean4-wsl/`
   - Utilise `wsl.exe -d Ubuntu -- ~/.lean4-venv/bin/python3 ~/.lean4-kernel-wrapper.py -f {connection_file}`

3. **Validation** : `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/validate_lean_setup.py`
   - `--wsl` pour mode WSL, `--windows` pour mode Windows
   - Verifie: elan, lean, lake, repl, venv, wrapper, lean4_jupyter

4. **Notebook de setup** : `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-1-Setup.ipynb`

### Diagnostic kernel

```powershell
# Verifier registration kernel
wsl -d Ubuntu -- cat ~/.local/share/jupyter/kernels/lean4-wsl/kernel.json

# Le CORRECT wrapper doit pointer vers:
#   /home/jesse/.lean4-venv/bin/python3 /home/jesse/.lean4-kernel-wrapper.py

# Si kernel pointe vers ~/lean4-jupyter-wrapper.sh (OBSOLETE):
# Mettre a jour kernel.json pour pointer vers ~/.lean4-kernel-wrapper.py

# Verifier REPL
wsl -d Ubuntu -- test -f ~/.elan/bin/repl && echo "OK" || echo "MISSING"

# Verifier venv + module
wsl -d Ubuntu -- ~/.lean4-venv/bin/python3 -c "import lean4_jupyter; print('OK')"

# Tester kernel startup
wsl -d Ubuntu -- bash -c "cd ~/lean-projects/notebook_context && ~/.lean4-venv/bin/python3 -c \"
from jupyter_client.manager import KernelManager
km = KernelManager(kernel_name='lean4-wsl')
km.start_kernel()
kc = km.client(); kc.start_channels()
kc.wait_for_ready(timeout=90)
print('KERNEL READY')
kc.stop_channels(); km.shutdown_kernel()
\""
```

### Incident reference (2026-05-27)

Kernel timeout sur 15b notebook. Root cause: kernel.json pointait vers l'ancien wrapper bash `~/lean4-jupyter-wrapper.sh` au lieu du wrapper Python `~/.lean4-kernel-wrapper.py`. Fix: mettre a jour kernel.json pour pointer vers le bon wrapper. Les 3 scripts de setup existaient deja dans le repo mais n'avaient pas ete executes/appliques.

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
