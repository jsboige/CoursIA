# Verify Notebooks Command

Verify and test Jupyter notebooks in the CoursIA repository.

## Usage

```
/verify-notebooks [target] [options]
```

## Arguments

- `target`: Notebook path, family name, or "all"
  - Individual: `MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking.ipynb`
  - Family: `Sudoku`, `Search`, `SymbolicAI`, `Argument_Analysis`, `GenAI`, `ML`, `Probas`, `IIT`
  - All: `all` (validates all notebooks)

- Options (in target string):
  - `--quick`: Quick validation (check structure only, no execution)
  - `--fix`: Attempt to fix errors automatically
  - `--python-only`: Only test Python notebooks
  - `--dotnet-only`: Only test .NET notebooks

## Instructions for Claude

When this command is invoked:

### 1. Parse the target argument

Determine if the user wants to test:
- A specific notebook file
- A notebook family (directory)
- All notebooks

### 2. Discover notebooks to test

Use Glob to find notebooks:

```python
# For a family
pattern = f"MyIA.AI.Notebooks/{family}/**/*.ipynb"

# For all
pattern = "MyIA.AI.Notebooks/**/*.ipynb"
```

Exclude output notebooks (`*_output.ipynb`).

### 3. Categorize notebooks by kernel type

- **Python notebooks**: Can be executed with Papermill
- **.NET notebooks**: Require cell-by-cell execution via MCP
  - Check for `.net-csharp`, `.net-fsharp` kernel in metadata
  - Check for `#!import` directives (incompatible with Papermill)

### 4. Execute tests based on notebook type

#### Python Notebooks

```bash
cd "{notebook_dir}" && python -m papermill "{notebook_name}" "{notebook_name}_output.ipynb" --kernel python3 -p BATCH_MODE true
```

For notebooks with widgets or interactive elements, use BATCH_MODE=true.

#### .NET Notebooks

Use MCP Jupyter tools for cell-by-cell execution:

1. Start kernel: `manage_kernel(action="start", kernel_name=".net-csharp")`
2. Set working directory in first cell
3. Execute cells sequentially: `execute_on_kernel(kernel_id, mode="notebook_cell", cell_index=N)`
4. Stop kernel: `manage_kernel(action="stop", kernel_id=...)`

### 5. Analyze results

For each notebook, report:
- **Status**: SUCCESS, ERROR, SKIPPED
- **Execution time**
- **Error details** (if any)
- **Cell that failed** (if applicable)

### 6. If --fix is specified

When errors are detected:

1. Read the error message and traceback
2. Identify the problematic cell
3. Analyze the root cause:
   - Missing dependency
   - Syntax error
   - API change
   - Path issue
   - Timeout
4. Propose and apply a fix
5. Re-execute the notebook
6. Repeat until success or max 3 attempts

### 7. Generate summary report

```
=== Notebook Verification Report ===
Date: {timestamp}
Target: {target}

Results:
  - SUCCESS: {count}
  - ERROR: {count}
  - SKIPPED: {count}

Details:
  [SUCCESS] Notebook1.ipynb (12.3s)
  [ERROR] Notebook2.ipynb - Cell 5: ImportError: No module named 'xyz'
  [SKIPPED] Notebook3.ipynb - Interactive widgets not supported in batch mode

{if --fix}
Fixes Applied:
  - Notebook2.ipynb: Added missing import for 'xyz'
{endif}
```

## Notebook Families Reference

| Family | Path | Kernel | Notes |
|--------|------|--------|-------|
| Sudoku | MyIA.AI.Notebooks/Sudoku/ | .NET C# | Uses `#!import`, cell-by-cell only |
| Search | MyIA.AI.Notebooks/Search/ | Mixed | GeneticSharp=C#, PyGad=Python |
| SymbolicAI | MyIA.AI.Notebooks/SymbolicAI/ | Mixed | Tweety=Python+JPype, Linq2Z3=C# |
| Argument_Analysis | MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ | Python | Requires `.env` with API keys |
| GenAI | MyIA.AI.Notebooks/GenAI/ | Python | Requires API keys, some need GPU |
| ML | MyIA.AI.Notebooks/ML/ | .NET C# | ML.NET tutorials |
| Probas | MyIA.AI.Notebooks/Probas/ | .NET C# | Infer.NET |
| IIT | MyIA.AI.Notebooks/IIT/ | Python | PyPhi |
| EPF | MyIA.AI.Notebooks/EPF/ | Mixed | Student assignments |

## Known Limitations

1. **Widgets/Interactive**: Notebooks with `ipywidgets` polling loops cannot run in batch mode
2. **GPU Required**: Some GenAI notebooks require GPU (CUDA)
3. **API Keys**: GenAI and Argument_Analysis require valid API keys in `.env`
4. **External Services**: Some notebooks depend on external services (DBpedia, etc.)
5. **.NET Cold Start**: First .NET kernel start may timeout (30-60s), retry once

## GenAI Notebooks - Configuration spécifique

### Scripts dédiés (scripts/genai-stack/)

Pour les notebooks GenAI, utiliser les scripts spécialisés :

```bash
# Validation complète de la stack GenAI
python scripts/genai-stack/validate_stack.py

# Validation des notebooks GenAI avec authentification
python scripts/genai-stack/validate_notebooks.py MyIA.AI.Notebooks/GenAI/Image/

# Vérification GPU/VRAM
python scripts/genai-stack/check_vram.py

# Liste des modèles ComfyUI disponibles
python scripts/genai-stack/list_models.py
```

### Mapping notebooks -> services requis

| Notebooks | Service | Prérequis |
|-----------|---------|-----------|
| 01-1, 01-3 | OpenAI API | OPENAI_API_KEY dans .env |
| 01-4, 02-3 | SD Forge | Service local ou myia.io |
| 01-5, 02-1 | ComfyUI Qwen | COMFYUI_AUTH_TOKEN, ~29GB VRAM |
| 02-4 | Z-Image/vLLM | ~10GB VRAM |
| 03-* | Multi-modèles | Tous les services |
| 04-* | Applications | Variable |

### Configuration .env requise

```bash
# MyIA.AI.Notebooks/GenAI/.env
LOCAL_MODE=false              # true pour Docker local
COMFYUI_API_URL=https://qwen-image-edit.myia.io
COMFYUI_AUTH_TOKEN=...        # Bearer token requis
OPENAI_API_KEY=...            # Pour DALL-E
ZIMAGE_API_URL=https://z-image.myia.io
```

### Skill associé

Utiliser `/validate-genai` pour valider la stack avant les notebooks :

```
/validate-genai all           # Validation complète
/validate-genai services      # Services uniquement
/validate-genai notebooks     # Notebooks uniquement
```

## Examples

```
/verify-notebooks Sudoku
/verify-notebooks Search --quick
/verify-notebooks MyIA.AI.Notebooks/SymbolicAI/Tweety.ipynb --fix
/verify-notebooks Argument_Analysis --python-only
/verify-notebooks GenAI --quick
/verify-notebooks GenAI/Image/01-Foundation --fix
/verify-notebooks all --quick
```
