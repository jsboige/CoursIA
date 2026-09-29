"""Tests for _papermill_meta.strip_stale_papermill_metadata — per-cell metadata sweep (#18305, suite #11146).

Pins the contract on miniature notebooks:
- notebook-level metadata.papermill + metadata.execution.papermill are removed.
- per-cell metadata.papermill + metadata.execution.papermill are removed (new, #18305).
- empty per-cell metadata dicts are tolerated (not crashed).
- absent metadata (notebook or cell) is a no-op.
- markdown cells with metadata are also processed.
- non-papermill keys (eg `tags`, `deletable`) are preserved.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from _papermill_meta import strip_stale_papermill_metadata


PAPERMILL_NOTEBOOK = {
    "start_time": "2026-08-20T12:27:00.000Z",
    "end_time": "2026-08-20T12:27:11.000Z",
    "duration": 11.0,
    "input_path": "/tmp/old.ipynb",
}


def make_nb(cell_meta_specs=None, notebook_papermill=None, notebook_exec=None):
    """Build a tiny notebook with per-cell metadata specs.

    cell_meta_specs: list of dicts (or None for no metadata on cell).
    """
    cells = []
    for i, spec in enumerate(cell_meta_specs or []):
        cell = {
            "cell_type": "code",
            "execution_count": 1,
            "source": f"print({i})",
            "outputs": [],
        }
        if spec is not None:
            cell["metadata"] = dict(spec)
        else:
            cell["metadata"] = {}
        cells.append(cell)

    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    if notebook_papermill is not None:
        nb["metadata"]["papermill"] = dict(notebook_papermill)
    if notebook_exec is not None:
        nb["metadata"]["execution"] = dict(notebook_exec)
    return nb


def test_notebook_level_papermill_is_stripped():
    nb = make_nb(notebook_papermill=PAPERMILL_NOTEBOOK)
    strip_stale_papermill_metadata(nb)
    assert "papermill" not in nb["metadata"], (
        "notebook-level metadata.papermill should be removed"
    )


def test_notebook_level_execution_papermill_is_stripped():
    nb = make_nb(
        notebook_exec={
            "iopub.execute_input": "2026-08-20T12:27:01Z",
            "papermill": {"start_time": "2026-08-20T12:27:00Z"},
        }
    )
    strip_stale_papermill_metadata(nb)
    execution = nb["metadata"].get("execution")
    assert execution is None or "papermill" not in execution, (
        "notebook-level metadata.execution.papermill should be removed "
        "and the wrapper dropped if emptied"
    )


def test_cell_level_papermill_is_stripped():
    nb = make_nb(
        cell_meta_specs=[
            {"papermill": {"start_time": "2026-08-20T12:27:00Z", "duration": 0.1}}
        ]
    )
    strip_stale_papermill_metadata(nb)
    cell_meta = nb["cells"][0]["metadata"]
    assert "papermill" not in cell_meta, (
        "cell-level metadata.papermill should be removed (#18305)"
    )


def test_cell_level_execution_papermill_is_stripped_and_wrapper_dropped():
    nb = make_nb(
        cell_meta_specs=[
            {
                "execution": {
                    "iopub.status.busy": "2026-08-20T12:27:00Z",
                    "papermill": {"start_time": "2026-08-20T12:27:00Z"},
                },
                "tags": ["keep-me"],
            }
        ]
    )
    strip_stale_papermill_metadata(nb)
    cell_meta = nb["cells"][0]["metadata"]
    assert "papermill" not in cell_meta.get("execution", {}), (
        "cell-level metadata.execution.papermill should be removed"
    )
    assert cell_meta.get("tags") == ["keep-me"], (
        "non-papermill metadata keys must be preserved"
    )
    assert "execution" not in cell_meta or "papermill" not in cell_meta["execution"], (
        "empty execution wrapper should be dropped"
    )


def test_cell_level_execution_wrapper_dropped_entirely():
    """Le wrapper ``execution`` est retire ENTIEREMENT (et non partiellement) :
    chaque cle qu'il porte (``iopub.status.busy``, ``iopub.status.idle``,
    ``iopub.execute_input``, ``shell.execute_reply``) date une passe
    anterieure. Une preservation par cle laisserait passer une nouvelle cle
    Jupyter sans gate au prochain ajout de la spec. Voir docstring de
    ``strip_stale_papermill_metadata`` pour la mesure MGS-02 (#18305).
    """
    nb = make_nb(
        cell_meta_specs=[
            {
                "execution": {
                    "iopub.status.busy": "2026-08-20T12:27:00Z",
                    "iopub.status.idle": "2026-08-20T12:27:01Z",
                    "iopub.execute_input": "2026-08-20T12:27:00Z",
                    "shell.execute_reply": "2026-08-20T12:27:00Z",
                    "papermill": {"start_time": "2026-08-20T12:27:00Z"},
                },
                "tags": ["keep-me"],
            }
        ]
    )
    strip_stale_papermill_metadata(nb)
    cell_meta = nb["cells"][0]["metadata"]
    assert "execution" not in cell_meta, (
        "cell-level metadata.execution wrapper should be dropped entirely "
        "(iopub.* keys date an earlier run; preserve-by-key was the bug pinned "
        "by #18305's instance)"
    )
    assert cell_meta.get("tags") == ["keep-me"], (
        "non-papermill, non-execution metadata keys must be preserved"
    )


def test_notebook_level_execution_wrapper_dropped_entirely():
    """Meme regle au niveau carnet : ``metadata.execution`` est retire entier."""
    nb = make_nb(
        notebook_exec={
            "iopub.execute_input": "2026-08-20T12:27:01Z",
            "papermill": {"start_time": "2026-08-20T12:27:00Z"},
        }
    )
    strip_stale_papermill_metadata(nb)
    assert "execution" not in nb["metadata"], (
        "notebook-level metadata.execution should be removed entirely"
    )


def test_empty_cell_metadata_is_noop():
    nb = make_nb(cell_meta_specs=[{}, {}, {}])
    strip_stale_papermill_metadata(nb)
    for cell in nb["cells"]:
        assert cell["metadata"] == {}


def test_no_metadata_key_on_cell_is_noop():
    nb = {
        "cells": [
            {"cell_type": "code", "execution_count": 1, "source": "x", "outputs": []}
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    strip_stale_papermill_metadata(nb)
    assert nb["cells"][0] == {
        "cell_type": "code",
        "execution_count": 1,
        "source": "x",
        "outputs": [],
    }


def test_no_notebook_metadata_is_noop():
    nb = {"cells": [], "nbformat": 4, "nbformat_minor": 5}
    strip_stale_papermill_metadata(nb)
    assert "metadata" not in nb


def test_markdown_cells_with_papermill_metadata_also_stripped():
    nb = make_nb(
        cell_meta_specs=[
            {"papermill": {"start_time": "2026-08-20T12:27:00Z"}}
        ]
    )
    # rewrite first cell to markdown
    nb["cells"][0]["cell_type"] = "markdown"
    nb["cells"][0]["source"] = "# title"
    nb["cells"][0].pop("execution_count", None)
    nb["cells"][0].pop("outputs", None)
    strip_stale_papermill_metadata(nb)
    assert "papermill" not in nb["cells"][0]["metadata"]


def test_realistic_instance_min_mgs_02():
    """Pinned reproduction of the instance measured in #18305 : 11 cellules,
    toutes portant un ``metadata.execution`` date du 2026-08-20, plus un
    ``metadata.papermill`` par cellule. Apres strip, le carnet ne doit plus
    dater les sorties d'un autre run.
    """
    nb = make_nb(cell_meta_specs=[{} for _ in range(11)])
    for cell in nb["cells"]:
        cell["metadata"] = {
            "execution": {
                "iopub.status.busy": "2026-08-20T12:27:00.123456Z",
                "iopub.status.idle": "2026-08-20T12:27:00.456789Z",
                "iopub.execute_input": "2026-08-20T12:27:00.234567Z",
                "shell.execute_reply": "2026-08-20T12:27:00.345678Z",
                "papermill": {"start_time": "2026-08-20T12:27:00Z", "duration": 0.1},
            },
            "papermill": {"start_time": "2026-08-20T12:27:00Z", "duration": 0.1},
            "tags": ["exercise"],
        }
    strip_stale_papermill_metadata(nb)
    for i, cell in enumerate(nb["cells"]):
        assert "papermill" not in cell["metadata"], f"cell {i}: papermill present"
        execution = cell["metadata"].get("execution", {})
        assert "papermill" not in execution, f"cell {i}: execution.papermill present"
        assert cell["metadata"].get("tags") == ["exercise"], f"cell {i}: tags lost"
