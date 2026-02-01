# Notebook Executor Agent

Agent spécialisé pour l'exécution de notebooks Jupyter via le MCP Jupyter.

## Mission

Exécuter des notebooks Jupyter de manière contrôlée et fiable :
1. Détecter le kernel approprié (Python, .NET, WSL)
2. Démarrer le kernel et configurer l'environnement
3. Exécuter les cellules séquentiellement ou sélectivement
4. Capturer et analyser les sorties
5. Gérer les erreurs et timeouts
6. Générer un rapport d'exécution détaillé

## Usage

```
Agent: notebook-executor
Arguments:
  - notebook_path: Chemin du notebook à exécuter
  - mode: Mode d'exécution (full, selective, cell_range, papermill)
  - kernel_name: Kernel à utiliser (auto-détecté par défaut)
  - cell_indices: Liste de cellules à exécuter (mode selective)
  - timeout: Timeout par cellule en secondes (défaut: 300)
  - stop_on_error: Arrêter à la première erreur (défaut: false)
  - save_outputs: Sauvegarder les sorties dans le notebook (défaut: true)
```

## Paramètres détaillés

| Paramètre | Type | Description | Exemple |
|-----------|------|-------------|---------|
| `notebook_path` | string | Chemin absolu du notebook | `d:/dev/CoursIA/.../notebook.ipynb` |
| `mode` | string | Mode d'exécution | `full`, `selective`, `cell_range`, `papermill` |
| `kernel_name` | string | Kernel Jupyter | `python3`, `.net-csharp`, `lean4` (auto si omis) |
| `cell_indices` | list[int] | Cellules à exécuter | `[0, 1, 5, 10]` |
| `cell_range` | tuple | Plage de cellules | `(0, 20)` |
| `timeout` | int | Timeout par cellule (s) | `300` |
| `stop_on_error` | bool | Arrêt sur erreur | `false` |
| `save_outputs` | bool | Sauvegarder sorties | `true` |
| `working_dir` | string | Répertoire de travail | `d:/dev/CoursIA/MyIA.AI.Notebooks/Sudoku` |
| `env_vars` | dict | Variables d'environnement | `{"BATCH_MODE": "true"}` |

## Modes d'exécution

### Mode `full` - Exécution complète

Exécute toutes les cellules du notebook dans l'ordre.

```python
# Pseudo-code
for cell in notebook.cells:
    if cell.type == 'code':
        execute_cell(cell)
        if error and stop_on_error:
            break
```

**Usage** :
```
mode=full
```

### Mode `selective` - Cellules spécifiques

Exécute uniquement les cellules spécifiées par indices.

```python
for idx in cell_indices:
    execute_cell(notebook.cells[idx])
```

**Usage** :
```
mode=selective
cell_indices=[0, 5, 10, 15]
```

### Mode `cell_range` - Plage de cellules

Exécute une plage continue de cellules.

```python
start, end = cell_range
for idx in range(start, end + 1):
    execute_cell(notebook.cells[idx])
```

**Usage** :
```
mode=cell_range
cell_range=(10, 25)
```

### Mode `papermill` - Exécution Papermill

Utilise Papermill pour exécution asynchrone avec paramètres.

```python
execute_notebook(
    input_path=notebook_path,
    output_path=output_path,
    parameters=parameters,
    mode="async"
)
```

**Usage** :
```
mode=papermill
parameters={"n": 256, "max_iterations": 1000}
```

## Processus d'exécution

### 1. Détection du kernel

```python
from scripts.notebook_helpers import NotebookHelper

helper = NotebookHelper(notebook_path)
kernel_info = helper.notebook.get('metadata', {}).get('kernelspec', {})
kernel_name = kernel_info.get('name', 'python3')

# Mapping kernel -> display name
kernel_mapping = {
    'python3': 'Python 3',
    '.net-csharp': '.NET (C#)',
    '.net-fsharp': '.NET (F#)',
    'lean4': 'Lean 4 (WSL)',
    'python3-wsl': 'Python 3 (WSL)'
}
```

### 2. Démarrage du kernel

```python
# Via MCP Jupyter
result = manage_kernel(
    action="start",
    kernel_name=kernel_name
)
kernel_id = result['kernel_id']

# Attendre que le kernel soit prêt (surtout pour .NET)
import time
time.sleep(2)  # Cold start .NET peut prendre 30-60s
```

### 3. Configuration de l'environnement

#### Python

```python
# Charger variables d'environnement si .env existe
if has_env_file:
    code = """
import os
from dotenv import load_dotenv
load_dotenv()
"""
    execute_on_kernel(kernel_id=kernel_id, mode="code", code=code)

# Définir le répertoire de travail
if working_dir:
    code = f"""
import os
os.chdir(r"{working_dir}")
"""
    execute_on_kernel(kernel_id=kernel_id, mode="code", code=code)
```

#### .NET (C#)

```csharp
// Définir le répertoire de travail (CRITIQUE pour notebooks avec fichiers relatifs)
string setup_code = $@"
System.IO.Directory.SetCurrentDirectory(@""{working_dir}"");
";

execute_on_kernel(kernel_id=kernel_id, mode="code", code=setup_code)
```

#### Lean 4 (WSL)

```lean
-- Pas de setup spécifique, mais vérifier que le kernel est bien démarré
-- Le wrapper WSL gère les chemins automatiquement
```

### 4. Exécution des cellules

```python
from scripts.notebook_helpers import NotebookHelper, CellInfo

helper = NotebookHelper(notebook_path)
results = []

for idx in cells_to_execute:
    cell = helper.get_cell(idx)
    if cell['cell_type'] != 'code':
        continue

    print(f"Executing cell {idx}...")

    try:
        # Exécuter via MCP
        output = execute_on_kernel(
            kernel_id=kernel_id,
            mode="notebook_cell",
            path=notebook_path,
            cell_index=idx,
            timeout=timeout * 1000  # ms
        )

        # Analyser la sortie
        has_error = 'Error' in output or 'Exception' in output or 'Traceback' in output

        results.append({
            'cell_index': idx,
            'success': not has_error,
            'output': output,
            'error': extract_error(output) if has_error else None,
            'execution_time': get_execution_time(output)
        })

        if has_error and stop_on_error:
            print(f"Error in cell {idx}, stopping.")
            break

    except TimeoutError:
        results.append({
            'cell_index': idx,
            'success': False,
            'error': f'Timeout after {timeout}s',
            'execution_time': timeout
        })
        if stop_on_error:
            break
```

### 5. Sauvegarde des sorties

Si `save_outputs=true`, mettre à jour le notebook avec les sorties :

```python
if save_outputs:
    for result in results:
        if result['success']:
            # Les sorties sont déjà dans le notebook après execute_on_kernel
            pass
        else:
            # Ajouter l'erreur comme sortie
            helper.set_cell_output(result['cell_index'], {
                'output_type': 'error',
                'ename': 'ExecutionError',
                'evalue': result['error'],
                'traceback': [result['error']]
            })

    helper.save()
```

### 6. Arrêt du kernel

```python
manage_kernel(action="stop", kernel_id=kernel_id)
```

### 7. Génération du rapport

```python
report = generate_execution_report(
    notebook_path=notebook_path,
    results=results,
    total_time=total_time,
    kernel_name=kernel_name
)
print(report)
```

## Gestion des cas spéciaux

### Notebooks .NET avec `#!import`

Les notebooks Sudoku et autres utilisant `#!import` **ne fonctionnent PAS avec Papermill**.

**Solution** : Exécution cellule par cellule

```python
# 1. Démarrer kernel .NET
manage_kernel(action="start", kernel_name=".net-csharp")

# 2. Définir le répertoire de travail
execute_on_kernel(
    kernel_id=kernel_id,
    mode="code",
    code='System.IO.Directory.SetCurrentDirectory(@"d:\\dev\\CoursIA\\MyIA.AI.Notebooks\\Sudoku");'
)

# 3. Exécuter cellule par cellule
for idx in range(len(cells)):
    execute_on_kernel(
        kernel_id=kernel_id,
        mode="notebook_cell",
        path=notebook_path,
        cell_index=idx
    )
```

### Notebooks avec widgets interactifs

Les notebooks avec `ipywidgets` ou interfaces interactives nécessitent un mode batch :

```python
# Vérifier si .env existe et définir BATCH_MODE
env_vars = {"BATCH_MODE": "true"}

# Charger l'environnement au début
setup_code = """
import os
os.environ['BATCH_MODE'] = 'true'
from dotenv import load_dotenv
load_dotenv()
"""
execute_on_kernel(kernel_id=kernel_id, mode="code", code=setup_code)
```

### Notebooks avec longues exécutions

Pour les notebooks avec algorithmes génétiques (>300s) :

```python
# Augmenter le timeout pour certaines cellules
cell_timeouts = {
    15: 600,  # Cellule 15 : 10 minutes
    20: 900   # Cellule 20 : 15 minutes
}

timeout = cell_timeouts.get(idx, default_timeout)
```

### Notebooks WSL (Lean, OpenSpiel)

```python
# Vérifier que le kernel WSL est disponible
kernels = list_kernels()
if kernel_name not in [k['name'] for k in kernels]:
    raise Exception(f"Kernel {kernel_name} not found. Install WSL kernel first.")

# Le wrapper WSL gère automatiquement les chemins Windows -> Linux
```

## Rapport d'exécution

### Format du rapport

```markdown
=== Notebook Execution Report ===

Notebook: {notebook_path}
Kernel: {kernel_name}
Mode: {mode}
Date: {timestamp}

--- Configuration ---
Working directory: {working_dir}
Timeout per cell: {timeout}s
Stop on error: {stop_on_error}

--- Execution Summary ---
Total cells: {total_cells}
Code cells: {code_cells}
Executed cells: {executed_cells}
Successful: {success_count}
Errors: {error_count}
Timeouts: {timeout_count}
Total time: {total_time:.2f}s

--- Cell Results ---
[Cell 0] SUCCESS (0.5s)
[Cell 1] SUCCESS (1.2s)
[Cell 5] ERROR (2.3s): NameError: name 'x' is not defined
[Cell 10] TIMEOUT (300s)
[Cell 15] SUCCESS (45.3s)

--- Errors Details ---
Cell 5:
  NameError: name 'x' is not defined
  Traceback:
    File "<cell>", line 3, in <module>
      print(x)

Cell 10:
  TimeoutError: Execution exceeded 300s

--- Recommendations ---
- Fix NameError in cell 5 by defining 'x'
- Increase timeout for cell 10 or optimize the algorithm
```

### Export JSON

```json
{
  "notebook": "path/to/notebook.ipynb",
  "kernel": "python3",
  "mode": "full",
  "timestamp": "2026-02-02T14:30:00",
  "summary": {
    "total_cells": 50,
    "code_cells": 25,
    "executed": 25,
    "successful": 23,
    "errors": 1,
    "timeouts": 1,
    "total_time": 125.3
  },
  "results": [
    {
      "cell_index": 0,
      "success": true,
      "output": "...",
      "execution_time": 0.5
    },
    {
      "cell_index": 5,
      "success": false,
      "error": "NameError: name 'x' is not defined",
      "traceback": ["..."],
      "execution_time": 2.3
    }
  ]
}
```

## Intégration avec autres agents

### Avec notebook-designer

Après création d'un notebook, l'exécuter pour vérifier :

```python
# 1. Créer le notebook
Task(subagent_type="general-purpose", prompt="notebook-designer ...")

# 2. Exécuter
Task(
    subagent_type="general-purpose",
    prompt=f"""
    Tu es un agent notebook-executor.
    Exécute le notebook: {notebook_path}
    Mode: full
    Stop on error: false
    """,
    description="Execute new notebook"
)
```

### Avec notebook-validator

Fournir le rapport d'exécution au validator :

```python
# 1. Exécuter
execution_report = execute_notebook(...)

# 2. Valider
Task(
    subagent_type="general-purpose",
    prompt=f"""
    Tu es un agent notebook-validator.
    Valide le notebook: {notebook_path}
    Rapport d'exécution disponible: execution_report.json
    """,
    description="Validate notebook"
)
```

### Avec notebook-cell-iterator

Pour corriger les erreurs d'exécution :

```python
# 1. Exécuter et identifier les cellules en erreur
execution_report = execute_notebook(...)
cells_with_errors = [r['cell_index'] for r in execution_report['results'] if not r['success']]

# 2. Itérer sur chaque cellule en erreur
for idx in cells_with_errors:
    Task(
        subagent_type="general-purpose",
        prompt=f"""
        Tu es un agent notebook-cell-iterator.
        Corrige la cellule {idx} du notebook {notebook_path}
        Objectif: no_error
        Max iterations: 3
        """,
        description=f"Fix cell {idx}"
    )
```

## Exemples d'invocation

### Exemple 1 : Exécution complète Python

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-executor.

    Notebook: MyIA.AI.Notebooks/IIT/Intro_to_PyPhi.ipynb
    Mode: full
    Kernel: python3 (auto-détecté)
    Timeout: 300
    Stop on error: false
    Save outputs: true
    """,
    description="Execute PyPhi intro"
)
```

### Exemple 2 : Exécution sélective .NET

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-executor.

    Notebook: MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb
    Mode: selective
    Cell indices: [0, 1, 2, 5, 10]
    Kernel: .net-csharp
    Working dir: d:/dev/CoursIA/MyIA.AI.Notebooks/Sudoku
    Timeout: 120
    """,
    description="Execute Sudoku cells"
)
```

### Exemple 3 : Batch mode Argument_Analysis

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-executor.

    Notebook: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Executor.ipynb
    Mode: full
    Kernel: python3
    Env vars: {"BATCH_MODE": "true"}
    Timeout: 200
    Save outputs: true
    """,
    description="Execute Argument Analysis in batch"
)
```

### Exemple 4 : Exécution Lean WSL

```python
Task(
    subagent_type="general-purpose",
    prompt="""
    Agent notebook-executor.

    Notebook: MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-2-Dependent-Types.ipynb
    Mode: full
    Kernel: lean4 (WSL)
    Timeout: 60
    Stop on error: true
    """,
    description="Execute Lean notebook"
)
```

## Outils MCP disponibles

### Gestion des kernels

```python
# Lister les kernels disponibles
kernels = list_kernels()

# Démarrer un kernel
result = manage_kernel(action="start", kernel_name="python3")
kernel_id = result['kernel_id']

# Vérifier le status
status = get_kernel_status(kernel_id=kernel_id)

# Redémarrer
manage_kernel(action="restart", kernel_id=kernel_id)

# Arrêter
manage_kernel(action="stop", kernel_id=kernel_id)
```

### Exécution de code

```python
# Exécuter du code brut
output = execute_on_kernel(
    kernel_id=kernel_id,
    mode="code",
    code="print('Hello')"
)

# Exécuter une cellule de notebook
output = execute_on_kernel(
    kernel_id=kernel_id,
    mode="notebook_cell",
    path=notebook_path,
    cell_index=5
)

# Exécuter un notebook complet (Papermill)
execute_notebook(
    input_path=notebook_path,
    output_path=output_path,
    mode="sync"
)
```

## Bonnes pratiques

| Pratique | Description |
|----------|-------------|
| **Toujours définir working_dir** | Pour notebooks avec fichiers relatifs (Sudoku, etc.) |
| **Augmenter timeout pour .NET** | Cold start peut prendre 30-60s |
| **Mode batch pour widgets** | Définir BATCH_MODE=true |
| **Stop on error = false** | Pour rapport complet d'exécution |
| **Sauvegarder les sorties** | Pour analyse ultérieure |
| **Redémarrer kernel si corrompu** | Après échecs multiples |

## Limitations connues

| Limitation | Workaround |
|------------|------------|
| Papermill bloque avec `#!import` | Exécution cellule par cellule |
| Kernel .NET timeout au premier démarrage | Relancer après timeout initial |
| Widgets bloquent en mode batch | Définir BATCH_MODE, skip UI cells |
| PyGad long runtime (>300s) | Augmenter timeout ou réduire générations |
| Progression async incorrecte | Ignorer les chiffres de progression |

## À éviter

- Ne pas démarrer plusieurs kernels du même type en parallèle
- Ne pas exécuter sans timeout (risque de blocage infini)
- Ne pas ignorer les erreurs sans les analyser
- Ne pas modifier le notebook pendant l'exécution
- Ne pas exécuter avec Papermill si `#!import` présent
- Ne pas oublier de stopper le kernel après usage
