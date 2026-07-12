# WSL Kernels — Diagnostic et workarounds

Document de référence détaillant les règles auto-loaded de [.claude/rules/wsl-kernels.md](../../.claude/rules/wsl-kernels.md).

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

## Lean 4 — setup consolidé (issue #1618)

Point d'entrée unique pour installer/valider le kernel `lean4-wsl` :

```powershell
python scripts/lean/setup_lean4_all.py              # WSL install + registration + validation
python scripts/lean/setup_lean4_all.py --check-wrapper  # verifie kernel.json -> bon wrapper
```

La détection de la régression du 2026-05-27 (kernel.json pointant vers l'ancien wrapper bash `~/lean4-jupyter-wrapper.sh` au lieu du wrapper Python v5 `~/.lean4-kernel-wrapper.py`) est **centralisée** dans `scripts/lean/lean_kernel_check.py` (`inspect_kernel_wrapper`, print-agnostic). Les trois consommateurs y délèguent — plus de logique dupliquée/divergente :

- `scripts/lean/setup_lean4_all.py` (`--check-wrapper`)
- `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/validate_lean_setup.py`
- `MyIA.AI.Notebooks/GameTheory/scripts/validate_lean_setup.py` (auparavant ne détectait PAS la régression)

Test : `python scripts/lean/tests/test_lean_kernel_check.py` (4 cas : ancien bash → error, wrapper v5 → ok, inconnu / absent → warning).

### Architecture du kernel `lean4-wsl`

```
Windows (Jupyter)                  WSL (Ubuntu)
   kernel.json ──────────────────> ~/.lean4-kernel-wrapper.py (v6)
   %APPDATA%/jupyter/                ↓
     kernels/lean4-wsl/            ~/.lean4-venv/bin/python3 -m lean4_jupyter
                                    chdir: lakefile ancêtre le plus proche
                                          (fallback ~/lean-projects/notebook_context)
                                    REPL: ~/.elan/bin/repl  (via `lake env repl`)
```

Le wrapper Python v6 `~/.lean4-kernel-wrapper.py` (source dans le dépôt : `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py`) gère la conversion Windows→WSL des paths, les permissions NTFS, et la détection du lake workspace. v6 = (1) regex mangled-path couvre `AppData/Roaming` (kernelspec) ET `AppData/Local/Temp` (fichiers de connexion nbconvert — le kernel ne meurt plus sous nbconvert/papermill), (2) `find_lake_root()` chdir vers le `lakefile.lean`/`.toml` ancêtre le plus proche pour que `lake env repl` détecte le lake. L'ancien wrapper bash `~/lean4-jupyter-wrapper.sh` est **OBSOLETE** — ne pas l'utiliser. Scripts de setup sous-jacents (orchestrés par `setup_lean4_all.py`) : `MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_lean4.sh` (WSL : elan, Lean 4 stable, venv `~/.lean4-venv`, lean4_jupyter, REPL), `setup_lean4_kernel.ps1` (registration `%APPDATA%/jupyter/kernels/lean4-wsl/`), `SymbolicAI/Lean/scripts/validate_lean_setup.py` (`--wsl`/`--windows`), notebook `SymbolicAI/Lean/Lean-1-Setup.ipynb`.

### Native import d'un lake Mathlib en kernel `lean4-wsl` — VERDICT (a) PROUVÉ (probe 2026-06, c.127)

**Objectif** : un companion notebook **pur-Lean** (kernel natif) qui `import` un lake Mathlib (#4038) et `#check` ses théorèmes — alternative lisible au pattern python3 + `lake env lean --stdin` (companion Lean-12b sensitivity #4388).

**Verdict final : (a) FAISABLE** — un kernel `lean4-wsl` lancé dans un lake workspace nativement `import` le lake Mathlib et rend les signatures `#check` IN-kernel (Alectryon HTML), zéro Python.

**Cause racine (probe c.126 → fix c.127)** : lean4_jupyter hardcode `pexpect.spawn("lake env repl")` (`repl.py:52`). Sous `lake env`, le repl **perd son sysroot** (ne trouve plus `Init` → `#check Nat` = "Unknown identifier"). Asymétrie : `lake env lean` (le compilateur) résout son sysroot nativement ; `lake env repl` non. **Fix** : lancer le repl binary **directement** (pas via `lake env`) avec `LEAN_PATH` capturé de `lake env` (= sysroot toolchain + deps + oleans Mathlib jonctionnés + lake build). Preuve firsthand (notebook natif exécuté dans `sensitivity_lean`, kernel Lean pur, 184s = import Mathlib réel) :

- `import Sensitivity` → OK
- `#check Sensitivity.huang_degree_theorem` → signature réelle : `huang_degree_theorem {m : ℕ} (H : Set (Sensitivity.Q m.succ)) (hH : ...) : ∃ q ∈ H, √(↑m + 1) ≤ ↑(H ∩ q.adjacent).toFinset.card`
- `#check Sensitivity.f_squared` → `(f n) ((f n) v) = ↑n • v`
- `#print axioms Sensitivity.huang_degree_theorem` → **depends on axioms: [propext, Classical.choice, Quot.sound]** (0 sorry, pas de `sorryAx`)

**Prérequis** : (1) le wrapper v6 (`find_lake_root` chdir vers le lakefile ancêtre) pour que le kernel hérite le cwd du lake, (2) un repl binaire matchant la toolchain du lake (`~/.elan/bin/repl` est stable-locked ; rc1/rc2 lakes ont besoin d'un repl matché), (3) le fork `jsboige/lean4_jupyter@v0.0.1-native-import` qui intègre le patch `lean4_jupyter/repl.py` `launch()` (direct-launch REPL + `LEAN_PATH`). Le script `scripts/lean/setup_native_lean4_import.py` automatise l'install du fork + le build de repl par toolchain (`build-repl v4.30.0-rc2` / `v4.31.0-rc1`).

**Setup** :

```powershell
python scripts/lean/setup_native_lean4_import.py install      # install fork jsboige/lean4_jupyter@v0.0.1-native-import (durable — remplace patch)
python scripts/lean/setup_native_lean4_import.py status        # état patch + repl toolchains
python scripts/lean/setup_native_lean4_import.py build-repl v4.30.0-rc2   # build+install repl matché (~2 min)
```

**Note durabilité — RÉSOLU (fork `jsboige/lean4_jupyter@v0.0.1-native-import`, #4394)** : le fork intègre le patch direct-launch directement dans `lean4_jupyter/repl.py`, donc il **survit à un `pip install`/reinstall propre** (le gap de durabilité antérieur est fermé). Le sous-script `install` fait `pip install --force-reinstall --no-deps git+https://github.com/jsboige/lean4_jupyter.git@v0.0.1-native-import` dans le venv `~/.lean4-venv`. Le sous-script `patch` (in-place, idempotent + backup `.bak.native`) reste disponible comme **fallback offline** (machine sans accès GitHub), mais n'est plus le chemin canonique. Source unique du patch : les constantes `REPL_PY_ORIGINAL` / `REPL_PY_PATCH` du setup script, reflétées dans le fork — `status` détecte le patch par le marqueur `_find_lake_root` quelle que soit la voie d'install.

### Diagnostic manuel (commandes)

```powershell
# Verifier registration kernel — doit pointer vers ~/.lean4-venv/bin/python3 ~/.lean4-kernel-wrapper.py
wsl -d Ubuntu -- cat ~/.local/share/jupyter/kernels/lean4-wsl/kernel.json

# Verifier REPL
wsl -d Ubuntu -- test -f ~/.elan/bin/repl && echo "OK" || echo "MISSING"

# Verifier venv + module
wsl -d Ubuntu -- ~/.lean4-venv/bin/python3 -c "import lean4_jupyter; print('OK')"

# Tester kernel startup (timeout 90s)
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

## Notes complémentaires

- Cold start .NET Interactive : premier démarrage peut timeout (30-60s), retry une fois
- GameTheory notebooks requièrent `nashpy`, `matplotlib`, `scipy` (installés dans WSL venv)
- Lean notebooks utilisent `lake build` directement dans WSL pour vérification compilation
