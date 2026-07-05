# Scripts - Outils Utilitaires

Scripts de gestion, validation et execution pour l'ecosysteme CoursIA.

## Structure

```
scripts/
├── notebook_tools/              # Outils manipulation notebooks
│   ├── notebook_tools.py        # CLI (skeleton, validate, analyze, execute)
│   ├── notebook_helpers.py      # Helpers manipulation programmatique
│   ├── extract_notebook_skeleton.py  # Extraction structure pour README
│   └── fix_audio_dependencies.py     # Fix dependances audio
│
├── genai-stack/                 # CLI GenAI (Docker, validation, modeles)
│   └── genai.py                 # Point d'entree unifie
│
├── kernels/                     # Configurations kernels Jupyter
│   └── lean4-wsl/               # Kernel Lean4 via WSL
│
├── mcp-maintenance/             # Troubleshooting MCP/NuGet
│   ├── docs/                    # Documentation resolution problemes
│   ├── scripts/                 # Scripts de diagnostic
│   └── config/                  # Variables critiques
│
├── environment/                 # Scripts environnement
│   ├── audit_environment.ps1    # Audit environnement Windows
│   ├── setup_environment.ps1    # Setup environnement Windows
│   ├── install-ffmpeg.ps1       # Installation FFmpeg Windows
│   └── install-ffmpeg.sh        # Installation FFmpeg Linux/macOS
│
├── translation/                 # Synchro traduction multilingue (#4957 / #1650)
│   └── extract_cells_to_csv.py  # Extraction cellules -> CSV (drift-detection)
│
├── tests/                       # Tests unitaires
│
└── validate_lean11.py           # Validation Lean11
```

## Scripts Principaux

### notebook_tools.py

CLI multi-fonction pour la gestion des notebooks.

```bash
# Extraire la structure
python scripts/notebook_tools/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown

# Valider (structure uniquement)
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick

# Analyser le contenu
python scripts/notebook_tools/notebook_tools.py analyze MyIA.AI.Notebooks/Sudoku

# Executer
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/GenAI --timeout 300
```

### notebook_helpers.py

Fonctions utilitaires pour manipulation programmatique.

```bash
python scripts/notebook_tools/notebook_helpers.py list notebook.ipynb
python scripts/notebook_tools/notebook_helpers.py analyze notebook.ipynb
python scripts/notebook_tools/notebook_helpers.py get-source notebook.ipynb 5
```

### genai.py (CLI GenAI)

```bash
# Statut services Docker
python scripts/genai-stack/genai.py docker status

# Validation complete
python scripts/genai-stack/genai.py validate --full

# Verification GPU
python scripts/genai-stack/genai.py gpu
```

Voir [genai-stack/README.md](genai-stack/README.md) pour la documentation complete.

### extract_cells_to_csv.py (Synchro traduction)

Extrait les cellules d'un notebook ou d'une série vers le CSV de synchro traduction
(`translations/<famille>/<série>.csv`), source de vérité de l'alignement multilingue.
Schéma ratified #4957 §1 : `notebook, cell_id, cell_type, src_lang, src_hash, text_<lang>, hash_<lang>`
(8 langues EN/FR/ES/AR/FA/ZH/RU/PT). Les hashes bidirectionnels rendent la désynchronisation
détectable mécaniquement (source modifiée sans retraduction, ou traduction éditée à la main).

```bash
# Extraire le CSV initial d'une série (langue pivot fr, #1650 Phase 0.5)
python scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ \
    -o translations/symbolicai/argument_analysis.csv

# Un seul notebook (POC / schema review)
python scripts/translation/extract_cells_to_csv.py notebook.ipynb -o poc.csv
```

Le script est la couche T1 de l'infrastructure #4957 ; le drift-detection CI (T2) et la
resync par le moteur Argumentum (T3, gated #1650 Phase 1) viennent dans les tranches suivantes.

## Installation

```bash
# Windows - FFmpeg
./scripts/environment/install-ffmpeg.ps1

# Audit environnement
./scripts/environment/audit_environment.ps1

# Setup environnement
./scripts/environment/setup_environment.ps1
```

## Validation Lean

```bash
# Valider Lean11
python scripts/kernels/validate_lean11.py
```

## Tests

```bash
python -m pytest scripts/tests/
```
