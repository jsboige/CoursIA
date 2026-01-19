# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

CoursIA is an educational AI course platform combining:
- **Jupyter notebooks** for AI learning (C# with .NET Interactive and Python)
- **Docker infrastructure** for GenAI services (ComfyUI + Qwen image editing)
- **GradeBookApp** for student evaluation with collegial grading
- **Production-ready ecosystem** with authentication, orchestration, and validation

Repository: https://github.com/jsboige/CoursIA

## Common Commands

### Python Environment Setup

```bash
python -m venv venv
venv\Scripts\activate  # Windows
source venv/bin/activate  # Linux/macOS
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"
```

### C# Notebooks (.NET Interactive)
```bash
dotnet restore MyIA.CoursIA.sln
```
Target framework: .NET 9.0. Configuration: Copy `MyIA.AI.Notebooks/Config/settings.json.openai-example` to `settings.json`

### Docker/ComfyUI Services
```bash
cd docker-configurations/comfyui-qwen
cp .env.example .env
docker-compose up -d
```
Access: http://localhost:8188 (requires Bearer token authentication)

### Validation & Testing

```bash
python scripts/genai-stack/validate_notebooks.py  # Notebook validation
python scripts/genai-stack/validate_stack.py      # GenAI stack validation
python scripts/genai-stack/check_vram.py          # VRAM check
```
GitHub Actions validates notebooks on PR (`.github/workflows/notebook-validation.yml`)

### GradeBookApp
```bash
python GradeBookApp/gradebook.py           # Python version
dotnet run --project GradeBookApp          # C# version
python GradeBookApp/run_epf_mis_2026.py    # EPF MIS multi-epreuves
```

## Architecture

```
MyIA.AI.Notebooks/           # Interactive notebooks by topic
├── GenAI/                   # GenAI ecosystem (18 notebooks: image generation, LLMs)
├── ML/                      # ML.NET tutorials
├── Sudoku/                  # Constraint solving (Backtracking, Z3, OR-Tools, Genetic)
├── Search/                  # Optimization algorithms (GeneticSharp, PyGad)
├── SymbolicAI/              # RDF, Z3 solver, OR-Tools
├── Probas/                  # Infer.NET probabilistic programming
├── IIT/                     # PyPhi - Integrated Information Theory
├── EPF/                     # Student assignments (CC1, CC2)
└── Config/                  # API settings (settings.json)

MyIA.AI.Shared/              # Shared C# library

GradeBookApp/                # Student grading system
├── configs/                 # Course-specific grading configs (EPF, EPITA)
├── legacy/                  # Archived/deprecated scripts
└── gradebook.py             # Main grading logic (unified pipeline)

docker-configurations/       # Production infrastructure
├── comfyui-qwen/           # Main ComfyUI + Qwen service
├── models/                 # Shared model storage
├── cache/                  # Shared cache layer
└── orchestrator/           # Service orchestration

scripts/
├── genai-stack/            # Validation and management scripts
├── archive/                # Legacy scripts
└── notebook-fixes/         # Notebook repair utilities

notebook-infrastructure/     # Papermill automation & MCP maintenance
```

### GenAI Notebooks Structure (4 levels)
- **00-GenAI-Environment**: Setup and configuration
- **01-Images-Foundation**: DALL-E 3, GPT-5, basic operations
- **02-Images-Advanced**: Qwen, FLUX, Stable Diffusion 3.5, Z-Image
- **03-Images-Orchestration**: Multi-model comparison, workflows
- **04-Images-Applications**: Educational content, production integration

## Code Style Guidelines

- **No emojis** in code, variable names, or generated files
- Follow PEP 8 for Python, standard conventions for C#
- Keep naming professional and descriptive
- Avoid prefixes like "Pure", "Enhanced", "Advanced", "Ultimate" - use descriptive names instead
- Do not commit without explicit user approval

### Branch Naming
```
type/name-short-descriptif
```
Examples: `feature/notebook-transformers`, `fix/ml-example-bug`, `docs/improve-readme`

### Commit Messages
```
Type: description courte de la modification
```
Examples: `Add: notebook sur les Transformers`, `Fix: correction d'erreurs dans l'exemple ML.NET`

## Key Technologies

**AI/ML**: OpenAI API, Anthropic Claude, Qwen 2.5-VL, Hugging Face, Diffusers
**ComfyUI**: Custom Qwen nodes (16-channel VAE, vision tokens, multi-image editing)
**Docker**: Containerized GPU services (RTX 3090, 24GB VRAM recommended)
**.NET**: ML.NET, .NET Interactive, Microsoft.SemanticKernel, AutoGen
**Jupyter**: Python and C# kernels, papermill for execution

## Configuration

- **OpenAI/API keys**: `MyIA.AI.Notebooks/GenAI/.env` (template: `.env.example`)
  - `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_BEARER_TOKEN`, `HUGGINGFACE_TOKEN`
- **C# settings**: `MyIA.AI.Notebooks/Config/settings.json`
- **Docker env**: Variables in `docker-compose.yml` (ports, memory limits)

## Language

Primary documentation language is French. Code comments may be in French or English.

---

## GradeBookApp - Systeme de Notation par Evaluations Collegiales

### Vue d'ensemble

GradeBookApp est un systeme de notation qui combine les evaluations collegiales des etudiants avec celle du professeur. Le pipeline existe en deux versions :

- **Notebook C#** : `MyIA.AI.Notebooks/GradeBook.ipynb` (version interactive originale)
- **Python** : `GradeBookApp/gradebook.py` (version consolidee pour production)

### Pipeline de notation

1. **Chargement des donnees** - Fichiers inscription CSV + evaluations Google Forms
2. **Filtrage** - Notes hors limites, dates incoherentes, auto-evaluations, doublons
3. **Calcul note brute** - Moyenne ponderee (etudiants + professeur avec TEACHER_WEIGHT)
4. **Rectification** - Bonus/malus taille groupe + centrage-reduction statistique
5. **Generation Excel** - Resume etudiants + feedbacks par epreuve

### Configuration multi-epreuves

```python
CONFIG = {
    'nom_classe': 'EPF MIS 2026',
    'inscriptions_path': 'chemin/inscriptions.csv',
    'epreuves': [
        {'nom': 'CC1', 'inscription_col': 'Groupe CC1', 'poids': 0.5, 'target_mean': 15.0},
        {'nom': 'Projet ML', 'inscription_col': 'Sujet', 'poids': 0.5, 'target_mean': 15.5}
    ],
    'output_path': 'chemin/Notes_Finales.xlsx',
    'professor_email': 'jsboige@gmail.com'
}
```

### Fonctions principales (gradebook.py)

| Fonction | Description |
| -------- | ----------- |
| `run_pipeline(config)` | Pipeline mono-epreuve |
| `run_multi_epreuve_pipeline(config)` | Pipeline multi-epreuves avec moyenne ponderee |
| `apply_rectification(proj_eval, mean, std)` | Applique bonus/malus + centrage-reduction |
| `generate_excel_workbook(...)` | Genere l'Excel avec filtrage NaN |

### Dependances Python GradeBookApp

```bash
pip install pandas numpy openpyxl rapidfuzz unidecode
```
