# Scripts Archive

This directory contains archived scripts that are no longer actively used but preserved for reference.

## Contents

### notebook-fixes-2024/
Historical emergency fix scripts from October-December 2024 for notebook corruption and metadata issues.

| Script | Purpose |
|--------|---------|
| `fix_corrupted_notebooks_metadata.py` | Repair notebooks with corrupted JSON structure |
| `fix_notebooks_missing_metadata.py` | Add missing metadata to notebooks |
| `fix_pm_sequencing_logic.py` | Fix Papermill cell ordering issues |
| `resolve_notebooks_conflicts.py` | Resolve git merge conflicts in notebooks |
| `resolve_gradebook_conflict.py` | Specific fix for GradeBook.ipynb conflicts |
| `verify_notebooks_resolution.py` | Validate notebooks after conflict resolution |
| `analyze_notebook_differences.py` | Diff analysis between notebook versions |

### tweety-maintenance-2026/
One-shot maintenance scripts for Tweety notebook reorganization (January 2026).

| Script | Purpose |
|--------|---------|
| `split_tweety_setup.py` | Split Tweety-1-Setup.ipynb into smaller cells |
| `split_tweety_jvm.py` | Separate JVM setup logic into dedicated cells |

### genai-auth-legacy-20251215/
Legacy GenAI authentication scripts (December 2025).

### Other archived scripts

| Script | Purpose | Replaced by |
|--------|---------|-------------|
| `verify_notebooks.py` | Notebook validation CLI | `notebook_tools.py validate` |
| `verify_lean.py` | Root-level Lean validation | `Lean/scripts/verify_lean.py` |

## Usage

These scripts are preserved for reference. If you need similar functionality:

1. **Notebook validation**: Use `scripts/notebook_tools.py validate`
2. **Lean-specific validation**: Use `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/verify_lean.py`
3. **Tweety validation**: Use `MyIA.AI.Notebooks/SymbolicAI/Tweety/scripts/verify_all_tweety.py`

## Restore if needed

If you need to restore a script, copy it from this archive to the appropriate location.
