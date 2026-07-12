# Scripts GameTheory

Ce répertoire contient les scripts de configuration et de validation des kernels utilisés par la série GameTheory : kernel Python WSL pour les notebooks OpenSpiel/CFR (`GameTheory-13`, `GameTheory-17`), et kernel Lean 4 (WSL) pour les notebooks Lean natifs (`-2b`, `-8b`, `-15b`, `SocialChoice/02-Lean-SocialChoice-Formal`).

## Scripts disponibles

### Configuration Lean 4 — native (macOS / Linux)

| Script | Description | Usage |
|--------|-------------|-------|
| `setup_lean4_native.sh` | Installe elan, Lean 4, REPL et lean4_jupyter nativement | `bash scripts/setup_lean4_native.sh` |
| `setup_lean4_native.sh --check` | Vérifie l'installation sans modifier | `bash scripts/setup_lean4_native.sh --check` |

### Configuration Lean 4 — WSL (Windows)

| Script | Description | Usage |
|--------|-------------|-------|
| `setup_wsl_lean4.sh` | Configure Lean 4, elan, REPL et lean4_jupyter dans WSL | `bash scripts/setup_wsl_lean4.sh` (dans WSL) |
| `setup_lean4_kernel.ps1` | Crée le kernel Jupyter "Lean 4 (WSL)" sur Windows | `.\scripts\setup_lean4_kernel.ps1` (PowerShell) |

### Configuration OpenSpiel (WSL)

| Script | Description | Usage |
|--------|-------------|-------|
| `setup_wsl_openspiel.sh` | Configure OpenSpiel dans WSL pour les notebooks CFR | `bash scripts/setup_wsl_openspiel.sh` (dans WSL) |
| `setup_wsl_kernel.ps1` | Crée le kernel Python (GameTheory WSL) | `.\scripts\setup_wsl_kernel.ps1` (PowerShell) |

### Validation

| Script | Description | Usage |
|--------|-------------|-------|
| `validate_lean_setup.py` | Validation de l'environnement Lean | `python scripts/validate_lean_setup.py` |
| | Validation WSL | `python scripts/validate_lean_setup.py --wsl` |

> La validation inclut désormais la détection de la régression wrapper kernel.json (issue #1618) : `~/.lean4-kernel-wrapper.py` v5 vs ancien bash. Logique centralisée dans `scripts/lean/lean_kernel_check.py`, partagée avec `scripts/lean/setup_lean4_all.py` et le validateur SymbolicAI/Lean.

## Installation complète

### Étape 0 : Python standard (notebooks 1-12, 14-16)

```bash
pip install -r MyIA.AI.Notebooks/GameTheory/requirements.txt
# open_spiel echoue sur Windows - c'est normal, les notebooks Python natifs n'en ont pas besoin
```

### Étape 1a-native : Configuration Lean 4 native (macOS / Linux)

```bash
# Directement sur macOS ou Linux (pas de WSL necessaire)
cd MyIA.AI.Notebooks/GameTheory/scripts
bash setup_lean4_native.sh

# Verification
bash setup_lean4_native.sh --check
```

Puis redémarrez VSCode et sélectionnez le kernel **"Lean 4 (Native)"**.

### Étape 1a-wsl : Configuration WSL OpenSpiel (GT-13, GT-17) — Windows uniquement

```bash
# Dans WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_openspiel.sh
```

```powershell
# PowerShell Windows
cd D:\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_wsl_kernel.ps1
```

### Étape 1b : Configuration WSL Lean 4 (notebooks b) — Windows uniquement

```bash
# Dans WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_lean4.sh
```

```powershell
# PowerShell Windows
cd D:\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_lean4_kernel.ps1
```

### Étape 2 : Validation

```bash
# Windows
python scripts/validate_lean_setup.py

# WSL
python scripts/validate_lean_setup.py --wsl
```

### Étape 3 : Redémarrer VSCode

Fermer et rouvrir complètement VSCode pour que les nouveaux kernels soient détectés.

## Architecture des kernels

Les notebooks Lean natifs sont suffixés `-b` (kernel Lean 4) ; les notebooks Python miroirs sont suffixés `-c` quand un parallèle Python existe.

| Notebook | Kernel | Description |
|----------|--------|-------------|
| `GameTheory-1` à `GameTheory-12`, `-14`, `-16` | Python (Windows) | Notebooks Python classiques (Nashpy, sympy, networkx) |
| `GameTheory-2b-Lean-Definitions` | **Lean 4 (WSL)** | Définitions formelles, cellules Lean natives |
| `GameTheory-4b-Lean-NashExistence` | Python (WSL) | Lecture guidée, orchestration via `lean_runner.py` |
| `GameTheory-4c-NashExistence-Python` | Python (Windows) | Miroir numérique (sympy, scipy) |
| `GameTheory-8b-Lean-CombinatorialGames` | **Lean 4 (WSL)** | PGame mathlib, cellules Lean natives |
| `GameTheory-8c-CombinatorialGames-Python` | Python (Windows) | Miroir Sprague-Grundy en Python |
| `GameTheory-13-ImperfectInfo-CFR` | Python (WSL) | OpenSpiel CFR (WSL requis : pas de wheel Windows) |
| `GameTheory-15-CooperativeGames` | Python (Windows) | Solutions coopératives (Shapley, core, nucleolus) |
| `GameTheory-15b-Lean-CooperativeGames` | **Lean 4 (WSL)** | Formalisation Shapley (Lean 4) |
| `GameTheory-15c-CooperativeGames-Python` | Python (Windows) | Miroir Python du calcul Shapley |
| `GameTheory-17-MultiAgent-RL` | Python (WSL) | OpenSpiel multi-agent RL (idem GT-13, WSL requis) |
| `SocialChoice/02-Lean-SocialChoice-Formal` | **Lean 4 (WSL)** | Arrow, Sen, électeur médian |

## Troubleshooting

### Kernel ne démarre pas

```bash
# Verifier les logs du wrapper
wsl -d Ubuntu -- cat ~/.lean4-wrapper.log
```

### REPL non trouvé

```bash
# Dans WSL, recompiler le REPL
cd ~/repl
lake build
cp .lake/build/bin/repl ~/.elan/bin/
```

### lean4_jupyter non installé

```bash
# Dans WSL
source ~/.lean4-venv/bin/activate
pip install lean4_jupyter
```

### Connection file manquant

Ceci peut arriver si VSCode passe des chemins Windows malformés. Le wrapper gère ce cas automatiquement. Si le problème persiste :

1. Redémarrer VSCode complètement
2. Vérifier que WSL Ubuntu est bien installé : `wsl -l -v`
3. Vérifier le chemin du wrapper : `wsl -d Ubuntu -- ls -la ~/.lean4-kernel-wrapper.py`

## Dépendances

### Lean 4 (via elan)
- Lean 4.27.0+ (stable)
- Lake (build system)
- REPL (pour lean4_jupyter)

### Python (dans WSL)
- lean4_jupyter
- ipykernel
- pyyaml

### Python (Windows)
- nashpy
- numpy
- sympy (pour calculs Shapley)
- matplotlib
- networkx
