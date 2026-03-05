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
├── tests/                       # Tests unitaires
│
├── audit_environment.ps1        # Audit environnement Windows
├── setup_environment.ps1        # Setup environnement Windows
├── install-ffmpeg.ps1/.sh       # Installation FFmpeg
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

## Installation

```bash
# Windows - FFmpeg
./scripts/install-ffmpeg.ps1

# Audit environnement
./scripts/audit_environment.ps1
```

## Tests

```bash
python -m pytest scripts/tests/
```
