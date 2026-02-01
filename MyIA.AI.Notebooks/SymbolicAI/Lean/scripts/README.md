# Scripts Lean

Ce repertoire contient les scripts de configuration, validation et maintenance pour les notebooks Lean.

## Structure

```
scripts/
├── validate_lean_setup.py   # Validation environnement (Windows/WSL)
├── verify_lean.py           # Verification complete des notebooks
├── notebook_utils.py        # Utilitaires notebooks (list, format, info)
├── demo_manager.py          # Gestion des DEMOs Lean-9
├── lean4-kernel-wrapper.py  # Wrapper kernel Lean4 WSL
├── setup_wsl_python.sh      # Setup Python WSL
├── tests/                   # Tests unitaires
│   ├── test_leandojo_basic.py
│   ├── test_leandojo_repos.py
│   └── test_wsl_lean4_jupyter.py
└── archive/                 # Scripts temporaires archives (32 scripts)
```

## Scripts Principaux

### validate_lean_setup.py

Validation rapide de l'environnement Lean.

```bash
# Validation Windows
python scripts/validate_lean_setup.py

# Validation WSL
python scripts/validate_lean_setup.py --wsl
```

**Verifie** : Python, elan, Lean 4, Lake, packages (lean4-jupyter, openai, anthropic), kernels Jupyter, .env, lean_runner.py

### verify_lean.py

Verification complete avec execution de notebooks.

```bash
# Verification rapide (structure uniquement)
python scripts/verify_lean.py --quick

# Verification environnement
python scripts/verify_lean.py --check-env

# Execution via Papermill
python scripts/verify_lean.py --execute

# Execution cellule par cellule
python scripts/verify_lean.py --cell-by-cell

# Notebooks Python uniquement
python scripts/verify_lean.py --python-only

# Notebook specifique
python scripts/verify_lean.py --notebook Lean-7
```

### notebook_utils.py

Utilitaires pour manipuler les notebooks Jupyter.

```bash
# Lister les cellules
python scripts/notebook_utils.py list ../Lean-9-SK-Multi-Agents.ipynb

# Formater le markdown (ajoute lignes vides)
python scripts/notebook_utils.py format ../Lean-9-SK-Multi-Agents.ipynb

# Apercu sans modification
python scripts/notebook_utils.py format ../Lean-9-SK-Multi-Agents.ipynb --dry-run

# Informations notebook
python scripts/notebook_utils.py info ../Lean-9-SK-Multi-Agents.ipynb

# Obtenir le source d'une cellule
python scripts/notebook_utils.py get-source ../Lean-9-SK-Multi-Agents.ipynb 39

# Obtenir l'output d'une cellule
python scripts/notebook_utils.py get-output ../Lean-9-SK-Multi-Agents.ipynb 39
```

### demo_manager.py

Gestion centralisee des demonstrations Lean-9.

```bash
# Afficher la configuration actuelle
python scripts/demo_manager.py show

# Mettre a jour le notebook avec les DEMOs
python scripts/demo_manager.py update

# Apercu sans modification
python scripts/demo_manager.py update --dry-run

# Echanger deux demos (ex: DEMO_2 <-> DEMO_3)
python scripts/demo_manager.py reorder 2 3
```

**Pour modifier les DEMOs** : Editer `DEFAULT_DEMOS` dans `demo_manager.py`, puis executer `update`.

### setup_wsl_python.sh

Configure l'environnement Python dans WSL pour les notebooks 7-9.

```bash
bash scripts/setup_wsl_python.sh
```

**Installe** : venv Python, ipykernel, python-dotenv, openai, anthropic, semantic-kernel

### lean4-kernel-wrapper.py

Wrapper pour le kernel Lean4 via WSL. Utilise automatiquement par Jupyter.

## Utilisation Typique

### Premiere Installation

```bash
# 1. Ouvrir et executer Lean-1-Setup.ipynb (toutes les cellules)

# 2. Valider l'installation Windows
python scripts/validate_lean_setup.py

# 3. Si notebooks 7-9 necessaires, configurer WSL
bash scripts/setup_wsl_python.sh

# 4. Valider l'installation WSL
python scripts/validate_lean_setup.py --wsl
```

### Verification Quotidienne

```bash
# Verifier que tout est OK avant de lancer les notebooks
python scripts/validate_lean_setup.py
```

### Modification des DEMOs

```bash
# 1. Editer DEFAULT_DEMOS dans demo_manager.py
# 2. Verifier les changements
python scripts/demo_manager.py show

# 3. Appliquer au notebook
python scripts/demo_manager.py update
```

### Formatage Markdown

```bash
# Corriger le formatage (lignes vides manquantes)
python scripts/notebook_utils.py format ../Lean-9-SK-Multi-Agents.ipynb
```

## Tests Unitaires

```bash
# Executer tous les tests
python -m pytest scripts/tests/

# Test specifique
python -m pytest scripts/tests/test_leandojo_basic.py
```

## Archive

Le dossier `archive/` contient 32 scripts temporaires utilises pendant le developpement :

- `fix_*.py` - Corrections ponctuelles
- `update_demos_*.py` - Anciennes versions de demo_manager
- `test_*.py` - Tests ponctuels
- Autres scripts one-shot

Ces scripts sont conserves pour reference mais ne sont plus necessaires.

## Structure du Projet

```
MyIA.AI.Notebooks/SymbolicAI/Lean/
├── Lean-1-Setup.ipynb              # Installation
├── Lean-2-Dependent-Types.ipynb    # Types dependants
├── Lean-3-Propositions-Proofs.ipynb # Logique propositionnelle
├── Lean-4-Quantifiers.ipynb        # Quantificateurs
├── Lean-5-Tactics.ipynb            # Tactiques
├── Lean-6-Mathlib-Essentials.ipynb # Mathlib4
├── Lean-7-LLM-Integration.ipynb    # Python WSL requis
├── Lean-8-Agentic-Proving.ipynb    # Python WSL requis
├── Lean-9-SK-Multi-Agents.ipynb    # Python WSL requis
├── lean_runner.py                  # Backend Python pour Lean
├── .env                            # Configuration API
└── scripts/                        # CE REPERTOIRE
```

## Dependances Python

### Windows (kernel Python standard)

- `lean4-jupyter` - Kernel Jupyter pour Lean
- `python-dotenv` - Chargement .env
- `openai` - API OpenAI (notebooks 7-9)
- `anthropic` - API Claude (notebooks 7-9, optionnel)

### WSL (kernel Python 3 WSL)

- Installees dans `~/.python3-wsl-venv/`
- `ipykernel` - Kernel Jupyter
- `python-dotenv` - Chargement .env
- `openai` - API OpenAI
- `anthropic` - API Claude

## Validation Attendue

Sortie normale de `validate_lean_setup.py` :

```text
OK Python 3.13
OK elan: elan 4.1.2
OK Lean 4: Lean (version 4.27.0, ...)
OK Lake: lake 4.27.0
OK lean4-jupyter: 0.0.2
OK python-dotenv: 1.0.0
OK openai: 1.109.1
OK anthropic: 0.x.x
OK Kernel Jupyter: lean4
OK Kernel Jupyter: python3-wsl
OK .env: Present avec 3/3 cles
OK lean_runner.py: OK (51186 bytes)

Tous les composants OK (12/12)
```

## Troubleshooting

### anthropic non installe

```bash
pip install anthropic
```

### Venv WSL corrompu

```bash
rm -rf ~/.python3-wsl-venv
bash scripts/setup_wsl_python.sh
```

### Kernel Python 3 (WSL) ne demarre pas

```bash
# Verifier les logs wrapper
wsl cat ~/.python3-wrapper.log

# Reinstaller le kernel
python scripts/validate_lean_setup.py
```

### .env non charge dans notebooks 7-9

```bash
wsl ~/.python3-wsl-venv/bin/python3 -c "import dotenv; print(dotenv.__version__)"
```

## Maintenance

Avant chaque commit :

```bash
# 1. Valider l'environnement
python scripts/validate_lean_setup.py

# 2. Verifier la structure des notebooks
python scripts/verify_lean.py --quick

# 3. Executer les tests
python -m pytest scripts/tests/
```
