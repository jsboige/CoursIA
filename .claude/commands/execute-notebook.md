# Execute Notebook Command

Execute des notebooks Jupyter via MCP Jupyter avec gestion des kernels.

## Usage

```
/execute-notebook <notebook_path> [options]
```

## Arguments

- `notebook_path`: Chemin du notebook à exécuter
  - Absolu: `d:/dev/CoursIA/MyIA.AI.Notebooks/Sudoku/Sudoku-1.ipynb`
  - Relatif: `MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-DALLE3.ipynb`

- Options:
  - `--mode=<mode>`: Mode d'exécution (full, selective, papermill)
  - `--cells=<list>`: Cellules spécifiques (ex: --cells=0,5,10)
  - `--timeout=<seconds>`: Timeout par cellule (défaut: 300)
  - `--stop-on-error`: Arrêter à la première erreur
  - `--batch`: Mode batch (BATCH_MODE=true)
  - `--save`: Sauvegarder les sorties

## Instructions pour Claude

### 1. Charger l'agent notebook-executor

L'agent détaillé est dans `.claude/agents/notebook-executor.md`. Utiliser ces instructions.

### 2. Détecter le kernel

```python
# Lire les metadata du notebook
Read(notebook_path)
# Extraire kernelspec.name : python3, .net-csharp, lean4, etc.
```

### 3. Exécution selon le type de kernel

#### Python notebooks (kernel: python3)

```python
# Option 1: MCP Jupyter cell-by-cell
manage_kernel(action="start", kernel_name="python3")
execute_on_kernel(kernel_id=..., mode="notebook_cell", path=notebook_path, cell_index=0)
# ...
manage_kernel(action="stop", kernel_id=...)

# Option 2: Papermill (mode=papermill)
Bash: cd "{dir}" && python -m papermill "{notebook}" "{output}" --kernel python3 -p BATCH_MODE true
```

#### .NET notebooks (kernel: .net-csharp)

**IMPORTANT**: Ne PAS utiliser Papermill pour .NET. Utiliser MCP uniquement.

```python
# 1. Démarrer kernel
manage_kernel(action="start", kernel_name=".net-csharp")

# 2. CRITIQUE: Définir le répertoire de travail
execute_on_kernel(
    kernel_id=...,
    mode="code",
    code='System.IO.Directory.SetCurrentDirectory(@"d:\\dev\\CoursIA\\MyIA.AI.Notebooks\\Sudoku");'
)

# 3. Exécuter cellule par cellule
for idx in range(cell_count):
    execute_on_kernel(kernel_id=..., mode="notebook_cell", path=notebook_path, cell_index=idx)

# 4. Arrêter kernel
manage_kernel(action="stop", kernel_id=...)
```

#### Notebooks GenAI (Python avec services)

Pour les notebooks GenAI, vérifier les prérequis avec `/validate-genai` :

```python
# 1. Vérifier .env
env_path = "MyIA.AI.Notebooks/GenAI/.env"
# Vérifier COMFYUI_AUTH_TOKEN, OPENAI_API_KEY, etc.

# 2. Déterminer les services requis
# 01-Foundation: OpenAI API (cloud)
# 02-Advanced: ComfyUI local ou remote

# 3. Exécuter
# Si widgets/interactive, utiliser --batch
```

### 4. Scripts GenAI pour validation

Pour les notebooks GenAI, utiliser les scripts dédiés :

```bash
# Valider un notebook GenAI spécifique
python scripts/genai-stack/validate_notebooks.py MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-DALLE3.ipynb

# Valider un groupe
python scripts/genai-stack/validate_notebooks.py MyIA.AI.Notebooks/GenAI/Image/01-Foundation/
```

### 5. Gestion des erreurs

| Erreur | Cause | Solution |
|--------|-------|----------|
| Kernel timeout | Cold start .NET | Relancer (30-60s normal au premier démarrage) |
| File not found | Mauvais répertoire | SetCurrentDirectory() pour .NET |
| ModuleNotFoundError | Dépendance manquante | pip install dans l'environnement |
| API key missing | .env mal configuré | Vérifier OPENAI_API_KEY, etc. |
| CUDA error | GPU non disponible | Vérifier avec check_vram.py |

### 6. Rapport d'exécution

```markdown
=== Notebook Execution Report ===
Notebook: MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-DALLE3.ipynb
Kernel: python3
Mode: full

--- Summary ---
Total cells: 25
Code cells: 15
Executed: 15
Successful: 14
Errors: 1

--- Errors ---
Cell 12: APIError: Invalid API key

--- Timing ---
Total time: 45.3s
Average per cell: 3.0s

--- Recommendations ---
- Fix: Configure OPENAI_API_KEY in .env
```

## Exemples

```
/execute-notebook MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb
/execute-notebook MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-DALLE3.ipynb --batch
/execute-notebook MyIA.AI.Notebooks/IIT/Intro_to_PyPhi.ipynb --timeout=600
/execute-notebook notebook.ipynb --mode=selective --cells=0,5,10,15
```

## Agent associé

Pour des cas complexes, utiliser l'agent complet :

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Tu es un agent notebook-executor.
    Lis .claude/agents/notebook-executor.md

    Notebook: {notebook_path}
    Mode: full
    Stop on error: false
    """,
    description="Execute notebook"
)
```

## Outils MCP Jupyter disponibles

| Outil | Description |
|-------|-------------|
| `list_kernels()` | Liste les kernels disponibles |
| `manage_kernel(action, kernel_name/id)` | start/stop/restart kernel |
| `execute_on_kernel(kernel_id, mode, ...)` | Exécuter code ou cellule |
| `execute_notebook(input_path, ...)` | Exécution Papermill |
| `get_kernel_status(kernel_id)` | Status du kernel |
| `read_notebook(path)` | Lire notebook |
| `read_cells(path, mode)` | Lire cellules |
