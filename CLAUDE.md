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
cd docker-configurations/services/comfyui-qwen
cp .env.example .env
docker-compose up -d
```
Access: http://localhost:8188 (requires Bearer token authentication)

### Validation & Testing

```bash
python scripts/genai-stack/validate_notebooks.py  # Notebook validation
python scripts/genai-stack/validate_stack.py      # GenAI stack validation
python scripts/genai-stack/check_vram.py          # VRAM check
python scripts/notebook_tools.py validate [target] # Multi-family notebook verification
```
GitHub Actions validates notebooks on PR (`.github/workflows/notebook-validation.yml`)

### Claude Code Commands

```
/verify-notebooks [target] [options]    # Verify and test notebooks with iterative fixing
```

**Arguments:**
- `target`: Notebook path, family name (`Sudoku`, `Search`, `SymbolicAI`, `Argument_Analysis`, etc.), or `all`
- `--quick`: Structure validation only (no execution)
- `--fix`: Attempt automatic fixes iteratively
- `--python-only` / `--dotnet-only`: Filter by kernel type

**Examples:**
```
/verify-notebooks Sudoku --quick
/verify-notebooks Argument_Analysis --fix
/verify-notebooks MyIA.AI.Notebooks/Search/CSPs_Intro.ipynb --fix
```

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
├── notebook_helpers.py     # Low-level notebook manipulation (NotebookHelper, CellIterator)
├── notebook_tools.py       # High-level CLI: validate, skeleton, analyze, check-env, execute
├── extract_notebook_skeleton.py  # Notebook structure extraction
├── genai-stack/            # GenAI validation and management scripts
└── archive/                # Archived legacy and one-shot scripts

notebook-infrastructure/     # Papermill automation & MCP maintenance
```

### Notebook Scripts (IMPORTANT pour Claude Code)

Ces scripts sont essentiels pour la manipulation et l'iteration sur les notebooks :

**notebook_helpers.py** - Classes de base :

```python
from notebook_helpers import NotebookHelper, CellIterator, NotebookExecutor

# Manipulation de notebook
helper = NotebookHelper("path/to/notebook.ipynb")
helper.list_cells()                    # Liste toutes les cellules
helper.get_cell_source(5)              # Source de la cellule 5
helper.set_cell_source(5, "new code")  # Modifier une cellule
helper.find_cells_with_pattern("import")  # Recherche par regex
helper.find_cells_with_errors()        # Cellules en erreur
helper.save()                          # Sauvegarder

# Iteration corrective sur une cellule
iterator = CellIterator(
    notebook_path="notebook.ipynb",
    cell_index=5,
    objective="Output should contain 'SUCCESS'",
    max_iterations=5
)
```

**notebook_tools.py** - CLI et validation :

```bash
# Valider un notebook ou une famille
python scripts/notebook_tools.py validate Lean --quick
python scripts/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku/Sudoku-1.ipynb

# Extraire le squelette (pour README)
python scripts/notebook_tools.py skeleton MyIA.AI.Notebooks/Tweety --output markdown

# Analyser la structure
python scripts/notebook_tools.py analyze MyIA.AI.Notebooks/SymbolicAI

# Verifier l'environnement
python scripts/notebook_tools.py check-env Lean

# Executer (cell-by-cell ou papermill)
python scripts/notebook_tools.py execute GameTheory --timeout 120 --cell-by-cell
```

**notebook_helpers.py** - CLI pour execution et debug :

```bash
# Lister les cellules d'un notebook
python scripts/notebook_helpers.py list notebook.ipynb --verbose

# Executer une cellule specifique (pour debug)
python scripts/notebook_helpers.py execute notebook.ipynb --cell 5 --timeout 60

# Executer tout le notebook cell-by-cell
python scripts/notebook_helpers.py execute notebook.ipynb --verbose

# Detecter le kernel
python scripts/notebook_helpers.py detect-kernel notebook.ipynb

# Obtenir la source ou output d'une cellule
python scripts/notebook_helpers.py get-source notebook.ipynb 5
python scripts/notebook_helpers.py get-output notebook.ipynb 5
```

**IMPORTANT** : Utiliser ces scripts plutot que du code Python ad-hoc lors de l'iteration sur les notebooks

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

### Git Best Practices

- **NEVER use `git push --force` or `--force-with-lease`** unless absolutely necessary and explicitly approved by the user
- If secrets are accidentally committed, prefer creating a new clean branch with cherry-pick rather than rewriting history
- Always commit incrementally to avoid needing force pushes later
- If a force push seems necessary, ask the user first and explain the risks

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

## Claude Code - Agents, Skills et Scripts

### Skills (Commandes slash)

Commandes disponibles via `/command` dans Claude Code :

| Skill | Fichier | Description |
|-------|---------|-------------|
| `/verify-notebooks` | `.claude/commands/verify-notebooks.md` | Verifier et tester les notebooks avec correction iterative |
| `/enrich-notebooks` | `.claude/commands/enrich-notebooks.md` | Enrichir les notebooks avec du contenu pedagogique |
| `/cleanup-notebooks` | `.claude/commands/cleanup-notebooks.md` | Nettoyer et reorganiser le markdown des notebooks |

**Exemples** :
```bash
/verify-notebooks Sudoku --quick
/enrich-notebooks Infer --consecutive
/cleanup-notebooks Tweety --dry-run
```

### Agents

Agents specialises utilisables via Task tool :

#### Agents de conception et construction

| Agent | Fichier | Mission |
|-------|---------|---------|
| **notebook-designer** | `.claude/agents/notebook-designer.md` | Concevoir et creer de nouveaux notebooks from scratch |
| **notebook-iterative-builder** | `.claude/agents/notebook-iterative-builder.md` | Orchestrer la construction/amelioration iterative de notebooks |

#### Agents d'execution et validation

| Agent | Fichier | Mission |
|-------|---------|---------|
| **notebook-executor** | `.claude/agents/notebook-executor.md` | Executer des notebooks via MCP Jupyter avec gestion des kernels |
| **notebook-validator** | `.claude/agents/notebook-validator.md` | Valider tous les aspects d'un notebook (structure, execution, pedagogie) |

#### Agents d'enrichissement et correction

| Agent | Fichier | Mission |
|-------|---------|---------|
| **notebook-enricher** | `.claude/agents/notebook-enricher.md` | Ajouter du markdown pedagogique aux notebooks |
| **notebook-cell-iterator** | `.claude/agents/notebook-cell-iterator.md` | Iterer sur des cellules pour atteindre un objectif (correction, optimisation) |
| **infer-notebook-enricher** | `.claude/agents/infer-notebook-enricher.md` | Specialisation pour notebooks Infer.NET |
| **notebook-cleaner** | `.claude/agents/notebook-cleaner.md` | Nettoyer et reorganiser les notebooks |

#### Agents utilitaires

| Agent | Fichier | Mission |
|-------|---------|---------|
| **readme-updater** | `.claude/agents/readme-updater.md` | Mettre a jour les README de series de notebooks |

**Invocation type** :
```python
Task(
    subagent_type="general-purpose",
    prompt="Tu es un agent readme-updater. Lis .claude/agents/readme-updater.md et mets a jour: {path}",
    description="Update README"
)
```

#### Workflows de conception iterative

Les agents peuvent etre combines pour des workflows complets :

**1. Creation d'un nouveau notebook** :
```python
# Workflow complet via notebook-iterative-builder
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent: notebook-iterative-builder
    Mode: new
    Topic: "K-Means Clustering"
    Domain: ML
    Level: intermediate
    Notebook path: MyIA.AI.Notebooks/ML/KMeans-Intro.ipynb
    Quality target: 90
    Max iterations: 5
    """,
    description="Build KMeans notebook"
)
```

**2. Amelioration d'un notebook existant** :
```python
# Etape 1 : Valider
Task(subagent_type="general-purpose",
     prompt="notebook-validator: validate MyIA.AI.Notebooks/Probas/Infer/Infer-2.ipynb")

# Etape 2 : Enrichir selon le rapport
Task(subagent_type="general-purpose",
     prompt="notebook-enricher: enrich MyIA.AI.Notebooks/Probas/Infer/Infer-2.ipynb --execute")

# Etape 3 : Re-valider
Task(subagent_type="general-purpose",
     prompt="notebook-validator: validate MyIA.AI.Notebooks/Probas/Infer/Infer-2.ipynb")
```

**3. Correction d'erreurs d'execution** :
```python
# Workflow via notebook-iterative-builder mode fix
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent: notebook-iterative-builder
    Mode: fix
    Notebook path: MyIA.AI.Notebooks/GameTheory/GameTheory-15.ipynb
    Quality target: 100  # 100% execution sans erreurs
    Focus areas: ["execution"]
    """,
    description="Fix execution errors"
)
```

**4. Iteration sur une cellule specifique** :
```python
# Corriger une cellule avec objectif precis
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent: notebook-cell-iterator
    Notebook: MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb
    Cell index: 39
    Objective: "iterations: 4"  # Sortie attendue
    Max iterations: 5
    Kernel: python3
    """,
    description="Fix Lean demo cell"
)
```

### Scripts Python

Scripts utilitaires dans `scripts/` :

| Script | Description |
|--------|-------------|
| `verify_notebooks.py` | Verification multi-famille des notebooks (structure et execution) |
| `extract_notebook_skeleton.py` | Extraction structure notebooks pour generation README |
| `verify_lean.py` | Validation environnement Lean 4 |
| `split_tweety_jvm.py` | Utilitaires JVM pour Tweety |
| `split_tweety_setup.py` | Configuration Tweety |

**Utilisation `extract_notebook_skeleton.py`** :
```bash
# Resume rapide
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku

# Format tableau markdown pour README
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output markdown

# Format detaille avec previews de code
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output detailed --code-preview

# JSON pour traitement programmatique
python scripts/extract_notebook_skeleton.py MyIA.AI.Notebooks/Sudoku --output json
```

### Scripts par famille de notebooks

| Repertoire | Scripts |
|------------|---------|
| `scripts/genai-stack/` | `validate_notebooks.py`, `validate_stack.py`, `check_vram.py` |
| `MyIA.AI.Notebooks/Probas/Infer/scripts/` | `test_notebooks.py` (validation contenu + execution) |
| `MyIA.AI.Notebooks/SymbolicAI/scripts/` | `extract_notebook_content.py` |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/` | `validate_lean_setup.py`, `setup_wsl_python.sh` |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety/scripts/` | `verify_all_tweety.py`, `sat_comparison_demo.py` |
| `MyIA.AI.Notebooks/GameTheory/scripts/` | `validate_lean_setup.py` |

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

### Kernels WSL - Problemes connus (Janvier 2026)

Lors de la creation de kernels Jupyter qui s'executent dans WSL (comme pour OpenSpiel, Lean4, etc.), plusieurs pieges sont a eviter :

| Probleme | Cause | Solution |
| -------- | ----- | -------- |
| **Backslashes completement supprimes** | Le shell WSL consomme TOUS les `\` avant que le script les recoive | Utiliser un wrapper **bash** (pas Python) avec regex de reconstruction |
| **Chemin recu sans separateurs** | `~\AppData\...\kernel.json` devient `c:UsersjsboiAppDataRoaming...` | Regex: `^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$` |
| **SyntaxWarning: invalid escape sequence** | Docstrings Python avec `\A`, `\U`, etc. | Utiliser `#` commentaires, pas docstrings |
| **Variables heredoc interpolees** | `cat << 'EOF'` dans `bash -c '...'` interprete quand meme `$VAR` | Ecrire le script via fichier temporaire Windows, puis copier vers WSL |
| **Kernel timeout 60s** | Wrapper script a des erreurs silencieuses | Verifier `/tmp/kernel-wrapper.log` dans WSL |

**IMPORTANT** : Un wrapper Python direct ne fonctionne PAS car les backslashes sont consommes par le shell WSL avant que Python les recoive. Il faut un wrapper **bash**.

**kernel.json correct** :

```json
{
  "argv": [
    "wsl.exe", "-d", "Ubuntu", "--",
    "bash", "/home/<user>/.gametheory-kernel-wrapper.sh",
    "-f", "{connection_file}"
  ],
  "display_name": "Python (GameTheory WSL + OpenSpiel)",
  "language": "python"
}
```

**Template de wrapper BASH** (seul qui fonctionne) :

```bash
#!/bin/bash
# Kernel wrapper for WSL - handles stripped backslashes
# VSCode envoie: ~\AppData\Roaming\jupyter\runtime\kernel-xxx.json
# Wrapper recoit: c:UsersjsboiAppDataRoamingjupyterruntimekernel-xxx.json

LOGFILE="/tmp/kernel-wrapper.log"
echo "=== Kernel wrapper started ===" > "$LOGFILE"
echo "Args: $@" >> "$LOGFILE"

ARGS=()
NEXT_IS_CONN=false

for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        echo "Original path: $arg" >> "$LOGFILE"

        # Case 1: Tilde notation (rare, mais possible)
        if [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
        fi

        # Case 2: Backslashes strippes - CRITIQUE
        # Pattern: c:Users<user>AppDataRoamingjupyterruntimekernel-xxx.json
        if [[ "$arg" =~ ^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$ ]]; then
            USERNAME="${BASH_REMATCH[1]}"
            FILENAME="${BASH_REMATCH[2]}"
            arg="C:\\Users\\${USERNAME}\\AppData\\Roaming\\jupyter\\runtime\\${FILENAME}"
            echo "Reconstructed path: $arg" >> "$LOGFILE"
        fi

        # Convert to Linux path
        if [[ "$arg" == *":"* ]] || [[ "$arg" == *"\\"* ]]; then
            LINUX_PATH=$(wslpath -u "$arg" 2>/dev/null)
            if [ -n "$LINUX_PATH" ]; then
                arg="$LINUX_PATH"
            fi
        fi

        echo "Final path: $arg" >> "$LOGFILE"
        ARGS+=("$arg")
        NEXT_IS_CONN=false
    elif [ "$arg" = "-f" ]; then
        ARGS+=("$arg")
        NEXT_IS_CONN=true
    else
        ARGS+=("$arg")
    fi
done

export PATH="/home/<user>/.gametheory-venv/bin:$PATH"
cd ~
exec /home/<user>/.gametheory-venv/bin/python3 -m ipykernel_launcher "${ARGS[@]}"
```

**Scripts de deploiement** : Voir `MyIA.AI.Notebooks/GameTheory/scripts/` et `install_wsl_kernel.md`

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

### Mises à jour Janvier 2026 - Notebooks Search, Sudoku, SymbolicAI

**Notebooks Tweety (10 notebooks)** : Série complète sur TweetyProject, bibliothèque Java pour l'IA symbolique.

| Notebook | Contenu | Cellules |
| -------- | ------- | -------- |
| Tweety-1-Setup.ipynb | Configuration JDK/JPype, téléchargement JARs, outils externes | 34 |
| Tweety-2-Basic-Logics.ipynb | Logique Propositionnelle (PL), First-Order Logic (FOL), SAT4J, pySAT | 31 |
| Tweety-3-Advanced-Logics.ipynb | Description Logic (DL), Modal, QBF, Conditional Logic | 23 |
| Tweety-4-Belief-Revision.ipynb | CrMas multi-agent, mesures incohérence, MUS, MaxSAT | 22 |
| Tweety-5-Abstract-Argumentation.ipynb | Frameworks Dung, sémantiques (grounded, preferred, stable, CF2) | 14 |
| Tweety-6-Structured-Argumentation.ipynb | ASPIC+, DeLP, ABA, Deductive, ASP (Clingo) | 15 |
| Tweety-7a-Extended-Frameworks.ipynb | ADF, Bipolar, WAF, SAF, SetAF, EAF/REAF | 18 |
| Tweety-7b-Ranking-Probabilistic.ipynb | Ranking semantics, probabilistic argumentation | 10 |
| Tweety-8-Agent-Dialogues.ipynb | Agents argumentatifs, protocoles de dialogue | 11 |
| Tweety-9-Preferences.ipynb | Préférences, voting theory, social choice | 11 |

**Module partagé** : `tweety_init.py` centralise l'initialisation JVM et la détection des outils externes.

```python
from tweety_init import init_tweety, EXTERNAL_TOOLS, get_tool_path
jvm_ready = init_tweety()
```

**Outils externes supportés** :
- **Clingo** : ASP solver pour logique ASP
- **SPASS** : Prouveur de théorèmes modal (requiert droits admin sur Windows)
- **EProver** : Prouveur FOL
- **pySAT** : SAT solvers Python (CaDiCaL, Glucose)
- **MARCO** : Énumérateur MUS avec Z3

**Limitations connues** :
- SPASS.exe requiert des droits administrateur sur Windows (erreur 740)
- ADF nécessite un SAT solver natif incrémental (NativeMinisatSolver), Sat4jSolver ne fonctionne pas
- InformationObject manquant dans Tweety 1.28 affecte uniquement CrMas (notebook 4)

**Nouveaux notebooks Python Sudoku** :

| Notebook | Description |
| -------- | ----------- |
| Sudoku-Python-Backtracking.ipynb | Backtracking simple + MRV, visualisation matplotlib |
| Sudoku-Python-ORTools-Z3.ipynb | OR-Tools CP-SAT + Z3 SMT, comparaison performances |

**Amélioration Argument_Analysis_Executor.ipynb** : Ajout d'une cellule de validation finale qui génère un rapport JSON structuré avec :
- Cross-validation (COMPLETE_VALIDATED, PARTIAL, MINIMAL, INCOMPLETE)
- Score de confiance (0-100%)
- Checks : ARGUMENTS_IDENTIFIED, FALLACIES_ANALYZED, BELIEF_SET_CREATED, QUERIES_EXECUTED, CONCLUSION_GENERATED
- Export JSON vers `output/analysis_report.json`

---

## Lean - Proof Assistant et Verification Formelle (8 notebooks)

### Vue d'ensemble

Serie de notebooks pour Lean 4, un assistant de preuves et langage de programmation fonctionnel base sur la theorie des types dependants. Les notebooks 6-8 couvrent l'etat de l'art 2025-2026 : Mathlib4, integration LLM, et agents autonomes pour les preuves.

**Repertoire** : `MyIA.AI.Notebooks/SymbolicAI/Lean/`

**IMPORTANT - Kernels WSL uniquement** :

- `Python 3 (WSL)` - Notebook 1 (installation/setup) + Notebooks 7-9 (LLM/LeanDojo)
- `Lean 4 (WSL)` - Notebooks 2-6 (preuves Lean natives)

**Les kernels Windows NE fonctionnent PAS** (signal.SIGPIPE, problemes chemins)

**Duree totale** : ~5h55

### Structure des notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| **Partie 1 : Fondations** | | | |
| 1 | Lean-1-Setup | Installation elan, kernel Jupyter, verification | 15 min |
| 2 | Lean-2-Dependent-Types | Calcul des Constructions, types, polymorphisme | 35 min |
| 3 | Lean-3-Propositions-Proofs | Prop, connecteurs, Curry-Howard, preuves par termes | 45 min |
| 4 | Lean-4-Quantifiers | forall, exists, egalite, arithmetique Nat | 40 min |
| 5 | Lean-5-Tactics | Mode tactique, apply/exact/intro/rw/simp | 50 min |
| **Partie 2 : Etat de l'art** | | | |
| 6 | Lean-6-Mathlib-Essentials | Mathlib4, tactiques ring/linarith/omega, recherche | 45 min |
| 7 | Lean-7-LLM-Integration | LeanCopilot, AlphaProof, patterns LLM-Lean | 50 min |
| 8 | Lean-8-Agentic-Proving | Agents autonomes, APOLLO, problemes Erdos | 55 min |

### Installation

**IMPORTANT** : Tous les scripts sont dans `scripts/`, exécuter uniquement depuis là.

```bash
# 1. Ouvrir et exécuter Lean-1-Setup.ipynb (toutes les cellules)
#    Le notebook installe automatiquement : elan, Lean 4, lean4_jupyter, kernels

# 2. Valider l'installation
python scripts/validate_lean_setup.py

# 3. Pour notebooks 7-8 (LLM), configurer Python WSL
#    Installe: python-dotenv, openai, anthropic, matplotlib, semantic-kernel
bash scripts/setup_wsl_python.sh

# 4. Valider WSL
python scripts/validate_lean_setup.py --wsl
```

### Configuration

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean
cp .env.example .env
# Éditer .env et ajouter :
#   OPENAI_API_KEY=sk-...       (requis pour notebooks 7-8)
#   ANTHROPIC_API_KEY=sk-ant-... (optionnel)
#   GITHUB_TOKEN=ghp_...        (pour LeanDojo)
```

### Validation

```bash
python scripts/validate_lean_setup.py          # Valider environnement Windows
python scripts/validate_lean_setup.py --wsl    # Valider environnement WSL
```

Sortie attendue : `Tous les composants OK (12/12)`

### Percees recentes (2024-2026)

| Systeme | Accomplissement |
|---------|-----------------|
| **AlphaProof** (DeepMind) | Medaille d'argent IMO 2024, publie dans Nature |
| **Harmonic Aristotle** | Resolution Erdos #124 variant (~30 ans ouvert) en 6h |
| **DeepSeek-Prover** | Resolution de problemes Erdos 379, 987, 730, 198 |
| **Mathlib4** v4.27.0-rc1 | 4M+ lignes, utilise par Terry Tao |

### Concepts cles

- **Lean 4** (pas Lean 3) - syntaxe moderne
- **Curry-Howard** : propositions = types, preuves = termes
- **Tactiques** : apply, exact, intro, rw, simp, omega, ring, linarith
- **Preuves constructives** + logique classique (via `open Classical`)
- **Progression** : termes -> tactiques -> Mathlib -> LLMs -> agents

### Structure du répertoire

```
Lean/
├── Lean-1-Setup.ipynb ... Lean-8-Agentic-Proving.ipynb  # Notebooks (racine)
├── lean_runner.py                # Backend Python pour Lean
├── .env / .env.example           # Configuration API
├── requirements.txt              # Dependencies Python (semantic-kernel, openai, etc.)
├── scripts/                      # TOUS LES SCRIPTS
│   ├── README.md                 # Documentation scripts
│   ├── setup_wsl_python.sh       # Config Python WSL
│   ├── validate_lean_setup.py    # Validation environnement
│   └── lean4-kernel-wrapper.py   # Wrapper kernel WSL
├── tests/                        # Tests unitaires
│   ├── test_leandojo_basic.py
│   └── test_wsl_lean4_jupyter.py
└── examples/
    ├── basic_logic.lean          # Exemples Lean
    └── llm_assisted_proof.lean
```

### Document source

- Notebooks 1-5 : `D:\Dropbox\IA101\TPs\TP - Z3 - Tweety - Lean.pdf` (Section VI)
- Notebooks 6-8 : Recherches etat de l'art 2025-2026 (Mathlib4, AlphaProof, APOLLO, Harmonic Aristotle)

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
