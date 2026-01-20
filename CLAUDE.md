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

### Installation des kernels .NET

Les kernels .NET Interactive doivent être installés dans le répertoire de l'environnement conda :

```
C:/Users/<user>/.conda/envs/mcp-jupyter-py310/share/jupyter/kernels/
├── .net-csharp/
├── .net-fsharp/
└── .net-powershell/
```

**Configuration requise dans `kernel.json`** : Utiliser le chemin absolu vers `dotnet-interactive.exe` :

```json
{
  "argv": [
    "C:\\Users\\<user>\\.dotnet\\tools\\dotnet-interactive.exe",
    "jupyter",
    "--default-kernel",
    "csharp",
    "{connection_file}",
    "--http-port-range",
    "2048-3000"
  ],
  "env": {
    "DOTNET_ROOT": "C:\\Program Files\\dotnet"
  },
  "display_name": ".NET (C#)",
  "language": "C#"
}
```

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

### Notebooks .NET avec `#!import` - Exécution cellule par cellule

Les notebooks .NET utilisant la directive `#!import` (comme les notebooks Sudoku) **ne fonctionnent pas bien avec Papermill**. Utiliser l'exécution cellule par cellule :

```python
# 1. Démarrer un kernel .NET
manage_kernel(action="start", kernel_name=".net-csharp")

# 2. Définir le répertoire de travail (important pour les chemins relatifs)
execute_on_kernel(
    kernel_id="...",
    mode="code",
    code='System.IO.Directory.SetCurrentDirectory(@"d:\dev\CoursIA\MyIA.AI.Notebooks\Sudoku")'
)

# 3. Exécuter les cellules une par une
execute_on_kernel(kernel_id="...", mode="notebook_cell", path="notebook.ipynb", cell_index=0)
execute_on_kernel(kernel_id="...", mode="notebook_cell", path="notebook.ipynb", cell_index=1)
# ...

# 4. Arrêter le kernel à la fin
manage_kernel(action="stop", kernel_id="...")
```

### Répertoire de travail pour notebooks

Les notebooks Sudoku et autres utilisant des chemins relatifs (ex: `puzzles/Easy.txt`) nécessitent de définir le répertoire de travail :

```csharp
// En C# (.NET Interactive)
System.IO.Directory.SetCurrentDirectory(@"d:\dev\CoursIA\MyIA.AI.Notebooks\Sudoku");
```

```python
# En Python
import os
os.chdir(r"d:\dev\CoursIA\MyIA.AI.Notebooks\Sudoku")
```

### Limitations et problèmes connus

| Problème | Impact | Contournement |
| -------- | ------ | ------------- |
| **Papermill + `#!import`** | L'exécution reste bloquée | Utiliser `execute_on_kernel` cellule par cellule |
| **Papermill + kernels .NET** | Le kernel reste bloqué au démarrage (>60s) | Préférer exécution manuelle ou cellule par cellule |
| **Cold start .NET** | Premier démarrage peut timeout (30-60s) | Relancer une seconde fois après timeout |
| **Progression async** | Valeurs incorrectes (ex: 100/50 pour 21 cellules) | Bug connu, ignorer les chiffres de progression |
| **Kernel unresponsive** | Après exécution Papermill échouée | Arrêter et redémarrer le kernel |
| **Chemins relatifs** | "File not found" dans notebooks | Définir `Directory.SetCurrentDirectory()` |
| **PyGad long runtime** | Algorithme génétique >300s avec 100 générations | Réduire `num_generations` pour tests rapides |

### Résolution de problèmes

**Le kernel .NET ne démarre pas** :

1. Vérifier que `dotnet-interactive` est installé : `dotnet tool list -g`
2. Vérifier le chemin absolu dans `kernel.json`
3. Vérifier que `DOTNET_ROOT` pointe vers l'installation .NET

**Le notebook échoue avec "couldn't find file"** :

1. Vérifier le répertoire de travail avec `System.IO.Directory.GetCurrentDirectory()`
2. Définir explicitement le répertoire avec `SetCurrentDirectory()`

**Timeout au premier démarrage** :

- Normal pour .NET Interactive (compilation JIT). Relancer après timeout.

---

## État des Notebooks - Vérifications et Corrections (Janvier 2026)

### Corrections effectuées

| Notebook | Problème | Correction |
| -------- | -------- | ---------- |
| **CSPs_Intro.ipynb** | min_conflicts O(n²) par itération, timeout avec n=256 | Version optimisée avec compteurs incrémentaux (O(n)), supporte n=256 en 0.036s et n=1000 en 0.5s |
| **Sudoku-0-Environment.ipynb** | `DisplayResults()` affichage inversé | Paramètres `values`/`Keys` de `Chart2D.Chart.Bar` corrigés |
| **GeneticSharp-EdgeDetection.ipynb** | `#load "../Config/SkiaUtils.cs"` échoue avec Papermill | Code SkiaUtils intégré directement dans le notebook |
| **RDF.Net.ipynb** | Erreur DBpedia (service externe instable) | Try/catch ajouté avec message d'erreur gracieux |

### Notebooks vérifiés

| Notebook | Statut | Notes |
| -------- | ------ | ----- |
| **Tweety.ipynb** (72 cellules) | ✅ OK | 0 erreurs, JVM démarre correctement, warning `InformationObject` non bloquant |
| **Argument_Analysis_Agentic-0-init.ipynb** | ✅ OK | Exécution Python 43.4s, config OpenAI validée |
| **Argument_Analysis_Executor.ipynb** | ✅ OK (batch) | Mode batch ajouté (`BATCH_MODE=true` dans `.env`), analyse complète en 122s |
| **PyGad-EdgeDetection.ipynb** | ⚠️ Timeout | 100 générations × 100 individus dépasse 300s |
| **OR-Tools-Stiegler.ipynb** | ⚠️ Kernel .NET | Papermill bloque au démarrage, exécution manuelle requise |
| **Sudoku-2-Genetic.ipynb** | 📋 Manuel | Utilise `#!import`, test manuel requis |
| **Sudoku-6-Infer.ipynb** | 📋 Manuel | Utilise `#!import` + Infer.NET, test manuel requis |

### Notebooks avec dépendances externes

| Notebook | Dépendance | Notes |
| -------- | ---------- | ----- |
| **Tweety.ipynb** | JDK 17+, JARs Tweety dans `libs/` | Auto-détection JAVA_HOME |
| **Argument_Analysis/** | OpenAI API (`.env`) | 7 notebooks avec Semantic Kernel, mode batch supporté |
| **RDF.Net.ipynb** | DBpedia (service web) | Peut échouer si DBpedia indisponible |
| **Fast-Downward.ipynb** | Exécutable Fast Downward | Chemin configurable |

### Mode batch pour Argument_Analysis

Le notebook **Argument_Analysis_Executor.ipynb** supporte un mode batch pour les tests automatisés (Papermill/MCP) :

**Configuration dans `.env`** :

```bash
# Mode batch pour exécution non-interactive
BATCH_MODE="true"
# Texte personnalisé optionnel (sinon texte d'exemple utilisé)
# BATCH_TEXT="Votre texte à analyser..."
```

**Comportement** :

- `BATCH_MODE=true` : Skip le chargement de `UI_configuration.ipynb` (widgets bloquants), utilise texte d'exemple ou `BATCH_TEXT`
- `BATCH_MODE=false` (défaut) : Mode interactif avec interface widgets

**Notebooks testables en mode batch** :

- `Argument_Analysis_Executor.ipynb` - Orchestrateur complet (~122s)
- `Argument_Analysis_Agentic-0-init.ipynb` - Config uniquement (~43s)
- `Argument_Analysis_Agentic-1-informal_agent.ipynb` - Définition agent (~5s)
- `Argument_Analysis_Agentic-2-pl_agent.ipynb` - Définition agent (~5s)

**Notebooks NON testables automatiquement** :

- `Argument_Analysis_UI_configuration.ipynb` - Widgets interactifs (polling loop)
- `Argument_Analysis_Agentic-3-orchestration.ipynb` - Dépend de 0/1/2 chargés

---

## GradeBookApp - Système de Notation par Évaluations Collégiales

### Vue d'ensemble

GradeBookApp est un système de notation qui combine les évaluations collégiales des étudiants avec celle du professeur. Le pipeline existe en deux versions :

- **Notebook C#** : `MyIA.AI.Notebooks/GradeBook.ipynb` (version interactive originale)
- **Python** : `GradeBookApp/gradebook.py` (version consolidée pour production)

Les deux versions sont fonctionnellement équivalentes et supportent les multi-épreuves.

### Architecture des fichiers

```text
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
