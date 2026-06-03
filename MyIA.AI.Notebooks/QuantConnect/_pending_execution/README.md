# `_pending_execution/` - QuantBook notebooks awaiting QC Cloud execution

This directory holds QC Cloud research notebooks that use `QuantBook()` and therefore
cannot be executed locally or via Papermill. They are kept here pending manual
execution in QC Cloud Research IDE.

## H.3 / C.2 rationale

CLAUDE.md rule **H.3** forbids commiting notebooks with `execution_count: null` AND
empty `outputs: []`. CLAUDE.md rule **C.2** requires QuantBook notebooks to be
executed via QC Cloud Research (no markdown-only contournement).

Notebooks in this directory satisfy neither yet; they wait here until someone runs
them in the QC Cloud Research IDE and writes the executed `.ipynb` back to the
project directory (`projects/<project-name>/research.ipynb`).

## Execution checklist (per notebook)

1. Locate the QC Cloud project ID listed in the project README
2. Open https://www.quantconnect.com/project/<project_id> and ensure the notebook is uploaded
3. Run All cells in QC Cloud Research IDE
4. Verify all cells have `execution_count != null` and `outputs != []`
5. Download the executed notebook (.ipynb) via QC Cloud "Download -> Notebook"
6. Move it back to `projects/<project-name>/research.ipynb` (and remove the file here)
7. Open a PR with the executed notebook
