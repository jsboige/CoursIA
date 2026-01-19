# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

CoursIA is an AI course repository containing interactive Jupyter notebooks in both Python and C# (.NET Interactive). It covers machine learning, generative AI, symbolic AI, probabilistic programming, and optimization algorithms. The repository also includes Docker infrastructure for local GenAI image generation services and a GradeBookApp for student evaluation.

## Common Commands

### Python Environment Setup
```bash
python -m venv venv
venv\Scripts\activate  # Windows
pip install jupyter openai
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"
```

### C# Notebooks (.NET Interactive)
```bash
dotnet restore MyIA.CoursIA.sln
```
Target framework: .NET 9.0. Configuration in `MyIA.AI.Notebooks/Config/settings.json` (copy from `settings.json.openai-example`).

### Docker GenAI Services
```bash
docker-compose up -d              # Start all services
docker-compose down               # Stop services
```
PowerShell scripts available: `scripts/docker-setup.ps1`, `scripts/docker-start.ps1`, `scripts/docker-stop.ps1`

Services: FLUX.1-dev (8189), Stable Diffusion 3.5 (8190), ComfyUI Workflows (8191), Orchestrator (8193)

### Running Tests
```bash
python tests/validate_genai_ecosystem.py
```

### GradeBookApp
```bash
python GradeBookApp/gradebook.py           # Python version
dotnet run --project GradeBookApp          # C# version
```

## Architecture

```
MyIA.AI.Notebooks/           # Interactive notebooks by topic
  GenAI/                     # OpenAI, RAG, Semantic Kernel, local LLMs
  ML/                        # ML.NET tutorials
  Sudoku/                    # Constraint solving (Backtracking, Z3, OR-Tools, Genetic)
  Search/                    # Optimization algorithms (GeneticSharp, PyGad)
  SymbolicAI/                # RDF, Z3 solver, OR-Tools
  Probas/                    # Infer.NET probabilistic programming
  IIT/                       # PyPhi - Integrated Information Theory
  EPF/                       # Student assignments (CC1, CC2)
  Config/                    # API settings (settings.json)

MyIA.AI.Shared/              # Shared C# library

GradeBookApp/                # Student grading system (see detailed section below)
  configs/                   # Course-specific grading configs (EPF, EPITA)
  legacy/                    # Archived/deprecated scripts
  gradebook.py               # Main grading logic (Python, unified pipeline)

docker-configurations/       # GenAI Docker service configs
  flux-1-dev/
  stable-diffusion-35/
  comfyui-workflows/
  orchestrator/

notebook-infrastructure/     # Papermill automation & MCP maintenance
scripts/                     # PowerShell/Python utilities
```

## Key Dependencies

**C# Notebooks**: Microsoft.DotNet.Interactive, Microsoft.SemanticKernel, Microsoft.ML.Probabilistic, dotNetRdf, AutoGen

**Python GenAI**: openai, anthropic, pillow, numpy, pandas, matplotlib, python-dotenv

**Docker**: NVIDIA GPU support required for GenAI services

## Configuration

- **OpenAI/API keys**: `MyIA.AI.Notebooks/GenAI/.env` (template: `.env.example`)
- **C# settings**: `MyIA.AI.Notebooks/Config/settings.json`
- **Docker env**: Variables in `docker-compose.yml` (ports, memory limits)

## Language

Primary documentation language is French. Code comments may be in French or English.

---

## MCP Jupyter Papermill - Exécution de Notebooks

Claude Code dispose d'un MCP (Model Context Protocol) pour exécuter les notebooks Jupyter de ce repository.

### Capacités

| Catégorie | Outils disponibles |
|-----------|-------------------|
| **Lecture/Écriture** | `read_notebook`, `write_notebook`, `create_notebook`, `read_cells`, `add_cell`, `update_cell`, `remove_cell` |
| **Inspection** | `inspect_notebook`, `list_notebook_files`, `get_notebook_info` |
| **Kernels** | `list_kernels`, `manage_kernel` (start/stop/restart/interrupt) |
| **Exécution interactive** | `execute_on_kernel` (code brut, cellule spécifique, notebook complet) |
| **Exécution Papermill** | `execute_notebook` (sync/async avec injection de paramètres) |
| **Jobs asynchrones** | `manage_async_job` (status, logs, cancel, list, cleanup) |

### Kernels supportés

- **Python 3** : `python3` (via ipykernel dans conda `mcp-jupyter-py310`)
- **.NET Interactive** : `.net-csharp`, `.net-fsharp`, `.net-powershell` (via dotnet interactive)

### Configuration MCP (référence)

Le MCP est configuré dans `~/.claude.json` avec les variables d'environnement nécessaires pour :
- L'environnement conda `mcp-jupyter-py310`
- Le SDK .NET et MSBuild pour les notebooks C#
- Les chemins Jupyter pour trouver tous les kernels

### Exemples d'utilisation

```
# Lister les notebooks du repo
list_notebook_files(directory="MyIA.AI.Notebooks", recursive=true)

# Lire les cellules d'un notebook
read_cells(path="MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb", mode="list")

# Exécuter un notebook Python complet
execute_notebook(input_path="MyIA.AI.Notebooks/IIT/Intro_to_PyPhi.ipynb", mode="sync")

# Démarrer un kernel et exécuter du code interactif
manage_kernel(action="start", kernel_name="python3")
execute_on_kernel(kernel_id="...", mode="code", code="print('Hello')")
```

### Limitations connues

- Le reporting de progression des jobs async peut afficher des valeurs incorrectes
- Les notebooks .NET Interactive nécessitent que `dotnet interactive` soit installé globalement

---

## GradeBookApp - Système de Notation par Évaluations Collégiales

### Vue d'ensemble

GradeBookApp est un système de notation qui combine les évaluations collégiales des étudiants avec celle du professeur. Le pipeline existe en deux versions :

- **Notebook C#** : `MyIA.AI.Notebooks/GradeBook.ipynb` (version interactive originale)
- **Python** : `GradeBookApp/gradebook.py` (version consolidée pour production)

Les deux versions sont fonctionnellement équivalentes et supportent les multi-épreuves.

### Architecture des fichiers

```
GradeBookApp/
├── gradebook.py              # Pipeline unifié (EPF + EPITA, mono + multi-épreuves)
├── run_grading.py            # Point d'entrée EPITA
├── run_epf_mis_2026.py       # Exemple config multi-épreuves EPF MIS
├── configs/                  # Configurations par classe
│   ├── __init__.py
│   ├── README.md             # Guide création configs
│   ├── epf_2026_ml.py        # Config EPF MIS (Machine Learning)
│   └── epf_2026_genai.py     # Config EPF GenAI
├── legacy/                   # Scripts archivés
│   └── generate_notes_finales_epf.py
└── [fichiers C#]             # Version .NET (EvaluationRecord.cs, etc.)
```

### Pipeline de notation

Le pipeline suit ces étapes (conformes au notebook original) :

1. **Chargement des données**
   - Fichier d'inscription CSV (un fichier unique avec colonnes de groupe par épreuve)
   - Fichier(s) d'évaluation CSV (export Google Forms, un par épreuve)

2. **Filtrage des évaluations invalides**
   - Notes hors limites (< 1 ou > 19.5)
   - Dates incohérentes (± 5h par rapport à la médiane du groupe)
   - Évaluateurs non inscrits au cours
   - Auto-évaluations (membre du groupe évalué)
   - Évaluations en double

3. **Calcul de la note brute par groupe**
   - Formule : `Note = (Communication + Théorique + Technique + Organisation) × 2 / NbCritères`
   - Moyenne pondérée : `(moyenneÉtudiants + noteProfesseur × TEACHER_WEIGHT) / (1 + TEACHER_WEIGHT)`
   - Avec `TEACHER_WEIGHT = 1.0`, la note du prof compte 50%

4. **Rectification en deux étapes**
   - **Étape A** : Bonus/malus selon taille du groupe

     ```text
     Taille 1 : +3.0 points
     Taille 2 : +1.0 point
     Taille 3 :  0.0 (référence)
     Taille 4 : -1.0 point
     Taille 5 : -3.0 points
     ```

   - **Étape B** : Centrage-réduction statistique

     ```text
     noteFinale = ((note - moyenne) / écartType) × écartTypeCible + moyenneCible
     ```

     Borné entre 0 et 20.

5. **Génération du fichier Excel**
   - Onglet "Résumé Étudiants" : Nom, Prénom, [Groupe + Note par épreuve], Moyenne finale
   - Onglet "[Épreuve] Feedback" par épreuve : feedbacks qualitatifs (filtrés des lignes NaN)

### Commandes d'exécution

```bash
# EPF MIS 2026 (multi-épreuves : CC1 + Projet ML)
python GradeBookApp/run_epf_mis_2026.py

# EPF GenAI 2026 (mono-épreuve)
python GradeBookApp/configs/epf_2026_genai.py

# EPITA (ancien modèle)
python GradeBookApp/run_grading.py
```

### Format des fichiers d'entrée

**Fichier d'inscription (CSV)** :

```csv
Prénom,Nom de famille,Adresse de courriel,Sujet,Groupe CC1
Jean,DUPONT,jean.dupont@epf.fr,Projet IA,Groupe 1
```

**Fichier d'évaluation Google Forms (CSV)** :

```csv
Horodateur,Adresse e-mail,Votre nom,Votre prénom,Groupe à évaluer,Qualité de la présentation (communication, la forme),Qualité théorique (...),Qualité technique (...),Organisation (...),Points positifs,Points négatifs,Recommandations
2026-01-10 14:30:00,jsboige@gmail.com,Boige,Jean-Sylvain,Groupe 1,9,8,9,8,Bon travail,RAS,Continuer
```

### Configuration multi-épreuves

```python
CONFIG = {
    'nom_classe': 'EPF MIS 2026',
    'inscriptions_path': 'chemin/inscriptions.csv',
    'epreuves': [
        {
            'nom': 'CC1',
            'inscription_col': 'Groupe CC1',
            'evaluations_path': 'chemin/CC1_Evaluations.csv',
            'poids': 0.5,  # 50% de la note finale
            'target_mean': 15.0,
            'target_std': 2.0
        },
        {
            'nom': 'Projet ML',
            'inscription_col': 'Sujet',
            'evaluations_path': 'chemin/Projet_Evaluations.csv',
            'poids': 0.5,
            'target_mean': 15.5,
            'target_std': 2.0
        }
    ],
    'output_path': 'chemin/Notes_Finales.xlsx',
    'professor_email': 'jsboige@gmail.com'
}
```

### Fonctions principales (gradebook.py)

| Fonction                                    | Description                                   |
| ------------------------------------------- | --------------------------------------------- |
| `run_pipeline(config)`                      | Pipeline mono-épreuve (modèle EPF)            |
| `run_multi_epreuve_pipeline(config)`        | Pipeline multi-épreuves avec moyenne pondérée |
| `process_grades(...)`                       | Pipeline EPITA (ancien modèle)                |
| `load_student_records(file, mapping)`       | Charge les inscriptions avec mapping colonnes |
| `load_grades_from_file(file, ...)`          | Charge les évaluations Google Forms           |
| `apply_rectification(proj_eval, mean, std)` | Applique bonus/malus + centrage-réduction     |
| `generate_excel_workbook(...)`              | Génère l'Excel avec filtrage NaN              |
| `is_feedback_empty(evaluation)`             | Détecte les feedbacks vides (NaN)             |

### Classes de données

| Classe              | Attributs principaux                                            |
| ------------------- | --------------------------------------------------------------- |
| `StudentRecord`     | prenom, nom, sujets[], notes[], moyenne                         |
| `EvaluationRecord`  | date, email, nom, prenom, groupe, notes{}, is_teacher           |
| `GroupEvaluation`   | groupe, evaluations[], group_members[], note_rectifiee, moyenne |
| `ProjectEvaluation` | professor_email, grouped_evaluations[], moyenne, ecart_type     |

### Dépendances Python

```bash
pip install pandas numpy openpyxl rapidfuzz unidecode
```
