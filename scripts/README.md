# Scripts - Outils Utilitaires

Scripts de gestion, validation et execution pour l'ecosysteme CoursIA.

## Vue d'ensemble

| Categorie | Scripts | Description |
|-----------|---------|-------------|
| **Manipulation notebooks** | 3 | Lecture, ecriture, analyse de notebooks |
| **Execution** | 3 | Execution .NET et Python |
| **GenAI** | 10+ | Validation et gestion Docker |
| **Infrastructure** | 4 | Setup environnement, FFmpeg |

## Structure

```
scripts/
├── notebook_tools.py              # CLI consolide (skeleton, validate, analyze)
├── notebook_helpers.py            # Helpers manipulation notebooks
├── extract_notebook_skeleton.py   # Extraction structure pour README
│
├── execute_dotnet_notebook.py     # Execution notebooks C#
├── execute_sudoku_python.py       # Execution Sudoku Python
├── execute_all_sudoku.py          # Batch execution Sudoku
│
├── genai-stack/                   # Validation GenAI complete
│   ├── genai.py                   # CLI unifie (docker, validate, notebooks)
│   ├── check_vram.py              # Verification VRAM GPU
│   └── README.md                  # Documentation GenAI
│
├── tests/                         # Tests unitaires
├── archive/                       # Scripts legacy archives
└── historical-migrations/         # Scripts de migration historiques
```

## Scripts Principaux

### notebook_tools.py

Outil CLI multi-fonction pour la gestion des notebooks.

```bash
# Extraire la structure d'une serie de notebooks
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown

# Valider les notebooks (structure uniquement)
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick

# Analyser le contenu
python scripts/notebook_tools.py analyze MyIA.AI.Notebooks/Sudoku

# Verifier l'environnement
python scripts/notebook_tools.py check-env Sudoku
```

### notebook_helpers.py

Fonctions utilitaires pour la manipulation programmatique de notebooks.

```bash
# Lister les cellules
python scripts/notebook_helpers.py list notebook.ipynb

# Analyser un notebook
python scripts/notebook_helpers.py analyze notebook.ipynb

# Obtenir le source d'une cellule
python scripts/notebook_helpers.py get-source notebook.ipynb 5

# Obtenir la sortie d'une cellule
python scripts/notebook_helpers.py get-output notebook.ipynb 5
```

## Validation GenAI

Le repertoire `genai-stack/` contient tous les outils pour valider et gerer l'infrastructure GenAI.

```bash
# CLI unifie - aide complete
python scripts/genai-stack/genai.py --help

# Gestion Docker
python scripts/genai-stack/genai.py docker status
python scripts/genai-stack/genai.py docker start all
python scripts/genai-stack/genai.py docker test --remote

# Validation stack
python scripts/genai-stack/genai.py validate --full
python scripts/genai-stack/genai.py validate --notebooks

# GPU
python scripts/genai-stack/genai.py gpu
```

Voir [genai-stack/README.md](genai-stack/README.md) pour la documentation complete.

## Scripts d'Installation

### Environnement FFmpeg

```bash
# Windows (PowerShell)
./scripts/install-ffmpeg.ps1

# Linux/macOS
./scripts/install-ffmpeg.sh
```

### Audit environnement

```powershell
# Audit complet de l'environnement
./scripts/audit_environment.ps1
```

## Execution Notebooks .NET

Les notebooks C# necessitent une execution speciale car Papermill ne supporte pas `#!import`.

```bash
# Execution d'un notebook .NET
python scripts/execute_dotnet_notebook.py MyIA.AI.Notebooks/Sudoku/Sudoku-6-Probabilistic.ipynb

# Execution batch Sudoku
python scripts/execute_all_sudoku.py
```

## Tests

```bash
# Executer les tests unitaires
python -m pytest scripts/tests/
```

## Licence

Voir la licence du repository principal.
