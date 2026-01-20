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

---

## GenAI Services - ComfyUI Image Generation

### Services disponibles

| Service | Modele | VRAM | Description |
|---------|--------|------|-------------|
| **Qwen Image Edit** | qwen_image_edit_2509 | ~29GB | Edition d'images avec prompts multimodaux |
| **Z-Image/Lumina** | Lumina-Next-SFT | ~10GB | Generation text-to-image haute qualite |

### Architecture Qwen (Phase 29)

Workflow ComfyUI pour Qwen Image Edit 2509 :

```
VAELoader (qwen_image_vae.safetensors, 16 channels)
    |
CLIPLoader (qwen_2.5_vl_7b_fp8_scaled.safetensors, type: sd3)
    |
UNETLoader (qwen_image_edit_2509_fp8_e4m3fn.safetensors)
    |
ModelSamplingAuraFlow (shift=3.0)
    |
CFGNorm (strength=1.0)
    |
TextEncodeQwenImageEdit (clip, prompt, vae)
    |
ConditioningZeroOut (negative)
    |
EmptySD3LatentImage (16 channels)
    |
KSampler (scheduler=beta, cfg=1.0, sampler=euler)
    |
VAEDecode
```

**Points critiques** :
- VAE 16 canaux (pas SDXL standard)
- `scheduler=beta` obligatoire
- `cfg=1.0` (pas de CFG classique, utilise CFGNorm)
- `ModelSamplingAuraFlow` avec shift=3.0

### Architecture Z-Image/Lumina

Workflow ComfyUI simplifie avec LuminaDiffusersNode :

```
LuminaDiffusersNode (Alpha-VLLM/Lumina-Next-SFT-diffusers)
    |
VAELoader (sdxl_vae.safetensors)
    |
VAEDecode
    |
SaveImage
```

**Parametres LuminaDiffusersNode** :
- `model_path`: "Alpha-VLLM/Lumina-Next-SFT-diffusers"
- `num_inference_steps`: 20-40
- `guidance_scale`: 3.0-5.0
- `scaling_watershed`: 0.3
- `proportional_attn`: true
- `max_sequence_length`: 256

**Note technique (Janvier 2025)** : Le node utilise `LuminaPipeline` (diffusers 0.34+), ancien nom `LuminaText2ImgPipeline` obsolete.

### Approches abandonnees

| Approche | Raison abandon |
|----------|----------------|
| Z-Image GGUF | Incompatibilite dimensionnelle (2560 vs 2304) entre RecurrentGemma et Gemma-2 |
| Qwen GGUF | Non teste, prefer les poids fp8 pour qualite |

## Configuration

- **OpenAI/API keys**: `MyIA.AI.Notebooks/GenAI/.env` (template: `.env.example`)
  - `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_BEARER_TOKEN`, `HUGGINGFACE_TOKEN`
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
| **RDF.Net.ipynb** | Erreur DBpedia + fichiers manquants | Try/catch DBpedia + exemples in-memory pour cellules 107-113 |
| **PyGad-EdgeDetection.ipynb** | `plt.show()` bloque en mode batch, timeout >300s | Ajout `plt.close()` après chaque `plt.show()`, support `BATCH_MODE` |
| **Tweety.ipynb** | Warning trompeur sur InformationObject | Message corrigé : seule section CrMas affectée, reste du notebook OK |

### Notebooks vérifiés

| Notebook | Statut | Notes |
| -------- | ------ | ----- |
| **Tweety.ipynb** (72 cellules) | OK | JVM démarre avec JDK portable, InformationObject manquant (Tweety 1.28 API) n'affecte que CrMas |
| **Argument_Analysis_Agentic-0-init.ipynb** | OK | Exécution Python 43.4s, config OpenAI validée |
| **Argument_Analysis_Executor.ipynb** | OK (batch) | Mode batch ajouté (`BATCH_MODE=true` dans `.env`), analyse complète en 122s |
| **PyGad-EdgeDetection.ipynb** | OK (corrigé) | `plt.close()` ajouté, supporte `BATCH_MODE`, reste long (~300s avec 100 générations) |
| **Exploration_non_informée...ipynb** | OK | Exécution Papermill réussie |
| **OR-Tools-Stiegler.ipynb** | Kernel .NET | Papermill bloque au démarrage, exécution manuelle requise |
| **Sudoku-2-Genetic.ipynb** | Manuel | Utilise `#!import`, test manuel requis |
| **Sudoku-6-Infer.ipynb** | Manuel | Utilise `#!import` + Infer.NET, test manuel requis |

### Notebooks avec dépendances externes

| Notebook | Dépendance | Notes |
| -------- | ---------- | ----- |
| **Tweety.ipynb** | JDK 17+ | Auto-téléchargement JDK portable Zulu 17, JARs dans `libs/` |
| **Argument_Analysis/** | OpenAI API (`.env`) | 6 notebooks avec Semantic Kernel, mode batch supporté |
| **RDF.Net.ipynb** | DBpedia (service web) | Peut échouer si DBpedia indisponible, exemples in-memory en fallback |
| **Fast-Downward.ipynb** | Exécutable Fast Downward | Auto-compilation si manquant |

### Structure Argument_Analysis (après nettoyage Janvier 2026)

```
MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/
├── .env / .env.example          # Configuration API (OPENAI_API_KEY, BATCH_MODE)
├── Argument_Analysis_*.ipynb    # 6 notebooks du workflow
├── install_jdk_portable.py      # Utilitaire installation JDK
├── data/                        # Données (taxonomie sophismes, etc.)
├── ext_tools/                   # Outils externes
├── jdk-17-portable/             # JDK Zulu 17 (ignoré git)
├── libs/                        # JARs Tweety
├── ontologies/                  # Ontologies OWL
└── resources/                   # Ressources Tweety
```

**Fichiers supprimés** (nettoyage) :
- Scripts temporaires : `fix_*.py`, `text_sanitizer.py`
- Fichiers exemples obsolètes : `ExemplesTweetyJava*.txt`
- Notebook dupliqué : `Tweety.ipynb` (copie dans Argument_Analysis)

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
