# Scripts GameTheory

Ce repertoire contient les scripts de configuration et de validation des kernels utilises par la serie GameTheory : kernel Python WSL pour les notebooks OpenSpiel/CFR (`GameTheory-13`, `GameTheory-17`), et kernel Lean 4 (WSL) pour les notebooks Lean natifs (`-2b`, `-8b`, `-15b`, `SocialChoice/02-Lean-SocialChoice-Formal`).

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

### Etape 0 : Python standard (notebooks 1-12, 14-16)

```bash
pip install -r MyIA.AI.Notebooks/GameTheory/requirements.txt
# open_spiel echoue sur Windows - c'est normal, les notebooks Python natifs n'en ont pas besoin
```

### Etape 1a : Configuration WSL OpenSpiel (GT-13, GT-17)

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

### Etape 1b : Configuration WSL Lean 4 (notebooks b)

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

### Etape 2 : Validation

```bash
# Windows
python scripts/validate_lean_setup.py

# WSL
python scripts/validate_lean_setup.py --wsl
```

### Etape 3 : Redemarrer VSCode

Fermer et rouvrir completement VSCode pour que les nouveaux kernels soient detectes.

## Architecture des kernels

Les notebooks Lean natifs sont suffixes `-b` (kernel Lean 4) ; les notebooks Python miroirs sont suffixes `-c` quand un parallele Python existe.

| Notebook | Kernel | Description |
|----------|--------|-------------|
| `GameTheory-1` a `GameTheory-12`, `-14`, `-16` | Python (Windows) | Notebooks Python classiques (Nashpy, sympy, networkx) |
| `GameTheory-2b-Lean-Definitions` | **Lean 4 (WSL)** | Definitions formelles, cellules Lean natives |
| `GameTheory-4b-Lean-NashExistence` | Python (WSL) | Lecture guidee, orchestration via `lean_runner.py` |
| `GameTheory-4c-NashExistence-Python` | Python (Windows) | Miroir numerique (sympy, scipy) |
| `GameTheory-8b-Lean-CombinatorialGames` | **Lean 4 (WSL)** | PGame mathlib, cellules Lean natives |
| `GameTheory-8c-CombinatorialGames-Python` | Python (Windows) | Miroir Sprague-Grundy en Python |
| `GameTheory-13-ImperfectInfo-CFR` | Python (WSL) | OpenSpiel CFR (WSL requis : pas de wheel Windows) |
| `GameTheory-15-CooperativeGames` | Python (Windows) | Solutions cooperatives (Shapley, core, nucleolus) |
| `GameTheory-15b-Lean-CooperativeGames` | **Lean 4 (WSL)** | Formalisation Shapley (Lean 4) |
| `GameTheory-15c-CooperativeGames-Python` | Python (Windows) | Miroir Python du calcul Shapley |
| `GameTheory-17-MultiAgent-RL` | Python (WSL) | OpenSpiel multi-agent RL (idem GT-13, WSL requis) |
| `SocialChoice/02-Lean-SocialChoice-Formal` | **Lean 4 (WSL)** | Arrow, Sen, electeur median |

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
