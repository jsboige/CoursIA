# WSL Kernels — Diagnostic et workarounds

Document de référence détaillant les règles auto-loaded de [.claude/rules/wsl-kernels.md](../.claude/rules/wsl-kernels.md).

S'applique aux notebooks `MyIA.AI.Notebooks/GameTheory/**/*` et `MyIA.AI.Notebooks/SymbolicAI/Lean/**/*`.

## Issues connus et workarounds

| Problème | Cause | Solution |
|----------|-------|----------|
| Backslashes consommés | WSL shell mange TOUS les `\` | Wrapper bash (PAS Python) avec reconstruction regex |
| Path sans séparateurs | `~\AppData\...\kernel.json` devient `c:UsersjsboiAppData...` | Regex : `^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$` |
| `SyntaxWarning: invalid escape` | Docstrings avec `\A`, `\U` | Utiliser commentaires `#`, pas docstrings |
| Heredoc variables interpolées | `cat << 'EOF'` dans `bash -c '...'` | Écrire script via fichier temp, copier dans WSL |
| Kernel timeout 60s | Wrapper script errors | Vérifier `/tmp/kernel-wrapper.log` dans WSL |

## Solution : WSL Papermill (2026-05-10, T20.17)

`jupyter_client` côté Windows ne peut pas se connecter aux kernels WSL parce que WSL strippe les backslashes des paths du connection file. Workaround : **run papermill directement dans WSL**, en évitant la frontière cross-OS entièrement.

### Setup (one-time, par machine)

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

### Vérifié

- GT-1 Setup : 20/20 cells, 0 errors (3.3s)
- GT-7 ExtensiveForm : 30/30 cells, 0 errors (2s)

## Notes complémentaires

- Cold start .NET Interactive : premier démarrage peut timeout (30-60s), retry une fois
- GameTheory notebooks requièrent `nashpy`, `matplotlib`, `scipy` (installés dans WSL venv)
- Lean notebooks utilisent `lake build` directement dans WSL pour vérification compilation
