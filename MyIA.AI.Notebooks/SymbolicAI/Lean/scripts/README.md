# Scripts Lean

Ce répertoire contient tous les scripts de configuration et validation pour les notebooks Lean.

## Scripts disponibles

### Configuration

| Script | Description | Usage |
|--------|-------------|-------|
| `setup_wsl_python.sh` | Configure le venv Python WSL avec toutes les dépendances | `bash scripts/setup_wsl_python.sh` |
| `lean4-kernel-wrapper.py` | Wrapper pour le kernel Lean4 via WSL | Utilisé automatiquement par Jupyter |

### Validation

| Script | Description | Usage |
|--------|-------------|-------|
| `validate_lean_setup.py` | Validation rapide de l'environnement (elan, lean, packages, kernels) | `python scripts/validate_lean_setup.py` |
| | Validation WSL | `python scripts/validate_lean_setup.py --wsl` |
| `verify_lean.py` | Validation complète avec exécution de notebooks (structure + tests) | `python scripts/verify_lean.py --quick` |
| | Validation environnement | `python scripts/verify_lean.py --check-env` |
| | Exécution via Papermill | `python scripts/verify_lean.py --execute` |
| | Exécution cellule par cellule | `python scripts/verify_lean.py --cell-by-cell` |
| | Notebooks Python uniquement | `python scripts/verify_lean.py --python-only` |
| | Notebook spécifique | `python scripts/verify_lean.py --notebook Lean-7` |

## Utilisation typique

### Première installation

```bash
# 1. Ouvrir et exécuter Lean-1-Setup.ipynb (toutes les cellules)

# 2. Valider l'installation Windows
python scripts/validate_lean_setup.py

# 3. Si notebooks 7-8 nécessaires, configurer WSL
bash scripts/setup_wsl_python.sh

# 4. Valider l'installation WSL
python scripts/validate_lean_setup.py --wsl
```

### Vérification rapide

```bash
# Vérifier que tout est OK avant de lancer les notebooks
python scripts/validate_lean_setup.py
```

### Réinstallation propre

```bash
# Supprimer les venv
rm -rf ~/.python3-wsl-venv

# Réinstaller
bash scripts/setup_wsl_python.sh

# Valider
python scripts/validate_lean_setup.py --wsl
```

## Structure du projet

```
MyIA.AI.Notebooks/SymbolicAI/Lean/
├── Lean-1-Setup.ipynb              # Notebook d'installation
├── Lean-2-Dependent-Types.ipynb    # Types dépendants
├── Lean-3-Propositions-Proofs.ipynb # Logique propositionnelle
├── Lean-4-Quantifiers.ipynb        # Quantificateurs
├── Lean-5-Tactics.ipynb            # Tactiques
├── Lean-6-Mathlib-Essentials.ipynb # Mathlib4
├── Lean-7-LLM-Integration.ipynb    # Nécessite Python WSL
├── Lean-8-Agentic-Proving.ipynb    # Nécessite Python WSL
├── lean_runner.py                  # Backend Python pour Lean
├── .env                            # Configuration API (à créer depuis .env.example)
└── scripts/                        # TOUS LES SCRIPTS ET TESTS ICI
    ├── README.md                   # Cette documentation
    ├── setup_wsl_python.sh         # Config Python WSL
    ├── validate_lean_setup.py      # Validation environnement
    ├── verify_lean.py              # Validation notebooks complète
    ├── lean4-kernel-wrapper.py     # Wrapper kernel WSL
    └── tests/                      # Tests unitaires
        ├── test_leandojo_basic.py
        ├── test_leandojo_repos.py
        └── test_wsl_lean4_jupyter.py
```

## Dépendances Python

### Windows (kernel Python standard)
- `lean4-jupyter` - Kernel Jupyter pour Lean
- `python-dotenv` - Chargement .env
- `openai` - API OpenAI (notebooks 7-8)
- `anthropic` - API Claude (notebooks 7-8, optionnel)

### WSL (kernel Python 3 WSL)
- Installées dans `~/.python3-wsl-venv/`
- `ipykernel` - Kernel Jupyter
- `python-dotenv` - Chargement .env
- `openai` - API OpenAI
- `anthropic` - API Claude

## Validation attendue

Sortie normale de `validate_lean_setup.py` :

```
✓ Python 3.13
✓ elan: elan 4.1.2
✓ Lean 4: Lean (version 4.27.0, ...)
✓ Lake: lake 4.27.0
✓ lean4-jupyter: 0.0.2
✓ python-dotenv: 1.0.0
✓ openai: 1.109.1
✓ anthropic: 0.x.x
✓ Kernel Jupyter: lean4
✓ Kernel Jupyter: python3-wsl
✓ .env: Present avec 3/3 cles
✓ lean_runner.py: OK (51186 bytes)

Tous les composants OK (12/12)
```

## Troubleshooting

### anthropic non installé
```bash
pip install anthropic
```

### Venv WSL corrompu
```bash
rm -rf ~/.python3-wsl-venv
bash scripts/setup_wsl_python.sh
```

### Kernel Python 3 (WSL) ne démarre pas
```bash
# Vérifier les logs wrapper
wsl cat ~/.python3-wrapper.log

# Réinstaller le kernel
python scripts/validate_lean_setup.py  # Régénère kernel.json
```

### .env non chargé dans notebooks 7-8
Vérifier que `python-dotenv` est installé dans le venv WSL :
```bash
wsl ~/.python3-wsl-venv/bin/python3 -c "import dotenv; print(dotenv.__version__)"
```

## Tests unitaires

Les tests sont dans `scripts/tests/` :

| Test | Description |
|------|-------------|
| `test_leandojo_basic.py` | Tests de base LeanDojo |
| `test_leandojo_repos.py` | Tests dépôts LeanDojo |
| `test_wsl_lean4_jupyter.py` | Tests kernel WSL |

```bash
# Exécuter tous les tests
python -m pytest scripts/tests/

# Test spécifique
python -m pytest scripts/tests/test_leandojo_basic.py
```

## Maintenance

Les scripts doivent rester **exécutables et auto-suffisants**. Avant chaque commit :

```bash
# 1. Valider l'environnement
python scripts/validate_lean_setup.py

# 2. Vérifier la structure des notebooks
python scripts/verify_lean.py --quick

# 3. Tester le setup WSL (dans WSL)
wsl bash scripts/setup_wsl_python.sh

# 4. Exécuter les tests unitaires
python -m pytest scripts/tests/
```
