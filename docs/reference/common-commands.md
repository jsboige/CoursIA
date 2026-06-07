# Common Commands - CoursIA

## Environment Setup

```bash
# Python
python -m venv venv && venv\Scripts\activate
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt

# C# (.NET 9.0)
dotnet restore MyIA.CoursIA.sln
```

## Docker / ComfyUI Services

```bash
python scripts/genai-stack/genai.py docker status    # Statut des services
python scripts/genai-stack/genai.py docker start all # Demarrer tous les services
python scripts/genai-stack/genai.py docker stop all  # Arreter tous les services
```

Cf [genai-services.md](./genai-services.md) pour le detail des services et notebooks.

## Validation & Testing

**IMPORTANT : Always use existing scripts for notebook validation/execution. Never write ad-hoc execution scripts.**

### Notebook Tools (multi-family CLI)

```bash
python scripts/notebook_tools/notebook_tools.py validate [target]         # Structure validation
python scripts/notebook_tools/notebook_tools.py execute [target]          # Execute via Papermill
python scripts/notebook_tools/notebook_tools.py execute [target] --cell-by-cell  # Cell-by-cell (.NET/Lean)
python scripts/notebook_tools/notebook_tools.py analyze [path]            # Analyze structure
python scripts/notebook_tools/notebook_tools.py skeleton [path]           # Generate skeleton
```

**Kernel auto-detection** : `notebook_tools.py` reads kernel name from notebook metadata and uses it automatically. Custom kernels (smartcontracts, lean4-wsl) are supported with extended startup timeouts.

### SmartContracts-specific validator

```bash
python scripts/smartcontracts/validate_sc_notebooks.py                    # Full SC validation
python scripts/smartcontracts/validate_sc_notebooks.py --quick            # Structure only
python scripts/smartcontracts/validate_sc_notebooks.py --execute --anvil  # Execute with anvil
```

### GenAI stack validation

```bash
python scripts/genai-stack/genai.py validate --full       # Validation complete ComfyUI
python scripts/genai-stack/genai.py validate --notebooks   # Validation syntaxe notebooks
python scripts/genai-stack/genai.py notebooks              # Validation Papermill notebooks
python scripts/genai-stack/genai.py gpu                    # Verification VRAM
```

GitHub Actions validates notebooks on PR : `.github/workflows/notebook-validation.yml`

## Slash commands Claude Code

```
/verify-notebooks [target] [--quick] [--fix]      # Verify and test notebooks
/enrich-notebooks [target] [--execute] [--strict]  # Add pedagogical content
/cleanup-notebooks [target] [--dry-run]             # Clean markdown structure
/build-notebook <action> <path> [--quality=90]      # Create/improve/fix notebooks
/execute-notebook <path> [--batch] [--save]         # Execute via MCP
/validate-genai [target] [--local]                  # Validate GenAI stack
```

Cf [claude-code-config.md](./claude-code-config.md) pour le detail agents/skills/rules.

## GradeBookApp

```bash
python GradeBookApp/gradebook.py               # Python grading pipeline
python GradeBookApp/run_epf_mis_2026.py         # EPF MIS multi-epreuves
```

Cf [ece-grading.md](./ece-grading.md) pour le contexte ECE.
