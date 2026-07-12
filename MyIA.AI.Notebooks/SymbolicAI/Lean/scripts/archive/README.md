# Lean Scripts Archive

This directory contains archived one-shot fix and update scripts for Lean notebooks (January 2026).

## Purpose

These scripts were used during the initial development and debugging of Lean-8 and Lean-9 notebooks. They are preserved for reference but should not be run again as the fixes have already been applied.

## fix_*.py Scripts (14 files)

Scripts that fixed specific issues in Lean-8-Agentic-Proving.ipynb:

| Script | Issue Fixed |
|--------|-------------|
| `fix_agent_instructions.py` | Agent instruction formatting |
| `fix_execution_errors.py` | Runtime execution errors |
| `fix_group_chat.py` | Group chat agent configuration |
| `fix_lean8_execution_errors.py` | Major execution fixes (17KB) |
| `fix_logs_and_demo4.py` | Logging and Demo 4 issues |
| `fix_markdown_cells.py` | Markdown formatting |
| `fix_notebook_formatting.py` | General notebook formatting |
| `fix_notebooks_execution.py` | Execution flow issues |
| `fix_proof_agent_group_chat.py` | Proof agent group chat |
| `fix_section_numbers.py` | Section renumbering |
| `fix_sk_dependent_cells.py` | Semantic Kernel dependencies |
| `fix_timestamps_to_duration.py` | Timestamp to duration conversion |

## update_demos_*.py Scripts (5 versions)

Different strategies for Lean-9 demo configurations:

| Script | Strategy |
|--------|----------|
| `update_demos_complete.py` | Full demo configurations |
| `update_demos_for_progression.py` | Progressive iteration (1->1->2->4) |
| `update_demos_progressive.py` | Alternative progressive approach |
| `update_demos_v2.py` | TacticAgent vs SearchAgent focus |
| `update_demos_v3.py` | Structural complexity via induction |

## Other Scripts

| Script | Purpose |
|--------|---------|
| `add_lean9_conclusion.py` | Add conclusion section to Lean-9 |
| `analyze_notebook_errors.py` | Error analysis utility |
| `list_notebook_cells.py` | Cell listing utility |
| `rebuild_notebooks_correct.py` | Notebook reconstruction |
| `update_fallback_logging.py` | Fallback logging updates |
| `update_simulation_logic.py` | Simulation logic updates |
| `validate_fixes.py` | Validation after fixes |

## Common Utilities

All these scripts shared similar notebook manipulation functions that are now consolidated in `../notebook_utils.py`:

- `read_notebook(path)` - Read notebook JSON
- `write_notebook(path, nb)` - Write notebook JSON
- `get_cell_source(cell)` - Get cell content
- `set_cell_source(cell, source)` - Set cell content
- `create_code_cell(source)` - Create new code cell
- `create_markdown_cell(source)` - Create new markdown cell

## Warning

Do not run these scripts on the current notebooks - they were designed for specific states of the notebooks at specific points in time. Running them again may cause issues.
