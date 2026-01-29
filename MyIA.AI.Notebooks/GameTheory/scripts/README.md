# Scripts GameTheory

Ce repertoire contient les scripts de configuration et validation pour les notebooks Lean de la serie GameTheory.

## Scripts disponibles

### Configuration Lean 4 (WSL)

| Script | Description | Usage |
|--------|-------------|-------|
| `setup_wsl_lean4.sh` | Configure Lean 4, elan, REPL et lean4_jupyter dans WSL | `bash scripts/setup_wsl_lean4.sh` (dans WSL) |
| `setup_lean4_kernel.ps1` | Cree le kernel Jupyter "Lean 4 (WSL)" sur Windows | `.\scripts\setup_lean4_kernel.ps1` (PowerShell) |

### Configuration OpenSpiel (WSL)

| Script | Description | Usage |
|--------|-------------|-------|
| `setup_wsl_openspiel.sh` | Configure OpenSpiel dans WSL pour les notebooks CFR | `bash scripts/setup_wsl_openspiel.sh` (dans WSL) |
| `setup_wsl_kernel.ps1` | Cree le kernel Python (GameTheory WSL) | `.\scripts\setup_wsl_kernel.ps1` (PowerShell) |

### Validation

| Script | Description | Usage |
|--------|-------------|-------|
| `validate_lean_setup.py` | Validation de l'environnement Lean | `python scripts/validate_lean_setup.py` |
| | Validation WSL | `python scripts/validate_lean_setup.py --wsl` |

## Installation complete

### Etape 1 : Configuration WSL (Lean 4)

```bash
# Dans WSL Ubuntu
cd /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_lean4.sh
```

### Etape 2 : Kernel Windows

```powershell
# PowerShell Windows
cd C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_lean4_kernel.ps1
```

### Etape 3 : Validation

```bash
# Windows
python scripts/validate_lean_setup.py

# WSL
python scripts/validate_lean_setup.py --wsl
```

### Etape 4 : Redemarrer VSCode

Fermer et rouvrir completement VSCode pour que les nouveaux kernels soient detectes.

## Architecture des kernels

| Notebook | Kernel | Description |
|----------|--------|-------------|
| 1-16 | Python | Notebooks Python classiques |
| 17 (Lean-Definitions) | **Lean 4 (WSL)** | Definitions formelles, cellules Lean natives |
| 18 (Lean-NashExistence) | Python (WSL) | Lecture guidee, orchestration via lean_runner.py |
| 19 (Lean-CombinatorialGames) | **Lean 4 (WSL)** | PGame mathlib, cellules Lean natives |
| 20 (Lean-SocialChoice) | **Lean 4 (WSL)** | Arrow, Sen, electeur median |
| 21 (Lean-CooperativeGames) | **Lean 4 (WSL)** | Formalisation Shapley |

## Troubleshooting

### Kernel ne demarre pas

```bash
# Verifier les logs du wrapper
wsl -d Ubuntu -- cat ~/.lean4-wrapper.log
```

### REPL non trouve

```bash
# Dans WSL, recompiler le REPL
cd ~/repl
lake build
cp .lake/build/bin/repl ~/.elan/bin/
```

### lean4_jupyter non installe

```bash
# Dans WSL
source ~/.lean4-venv/bin/activate
pip install lean4_jupyter
```

### Connection file manquant

Ceci peut arriver si VSCode passe des chemins Windows malformes. Le wrapper gere ce cas automatiquement. Si le probleme persiste :

1. Redemarrer VSCode completement
2. Verifier que WSL Ubuntu est bien installe : `wsl -l -v`
3. Verifier le chemin du wrapper : `wsl -d Ubuntu -- ls -la ~/.lean4-kernel-wrapper.py`

## Dependances

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
