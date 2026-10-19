"""Tests FORGED_BLOCK -- ratchet papermill deux-couches (#21299).

Le ratchet d'origine (#11155) comparait le bloc top-level a lui-meme et
manquait le pattern « top-level re-ecrit a la main, per-cell intacte »
observe en c.1611 sur #21229, #21230, #21232 (bloc top-level
9aae1042-fb1d-4f9c-... ecrit avec end_time microsecond-identical au bloc
precedent, per-cell blocks non touches). Le fix ajoute
``cell_papermill_signature`` + consulte la matrice 2x2 dans ``classify``.

6 tests in-memory :

- 4 sur la matrice de classification (les nouvelles classes)
  - FORGED_BLOCK : top-level change, per-cell identique, outputs differents
  - BLOCK_MOVED : top-level change, per-cell change (re-exec reelle)
  - STALE_BLOCK : top-level identique, per-cell identique, outputs differents
    (voie legacy preservee)
  - OUTPUTS_UNCHANGED : tout identique (markdown-only edit legal)
- 2 sanity (verdict additif)
  - ADDED : notebook absent a la base
  - BLOCK_REMOVED : top-level absent a head, outputs differents

Aucun subprocess git reel -- les tests utilisent ``classify`` directement
avec des ``state_at_base`` / ``state_at_head`` construits a la main. La
matrice de regression reste celle de ``classify``, et c'est elle qu'il
faut verrouiller.
"""

import json
import sys
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parent.parent / "notebook_tools"
sys.path.insert(0, str(TOOLS))

import check_papermill_ratchet as cpr


# --- helpers ----------------------------------------------------------------

def _nb(top_block, per_cell_blocks, outputs_executed=True,
         cell_outputs=None, cell_exec_count=None):
    """Build a notebook with the given papermill layers and outputs.

    per_cell_blocks is a list (one entry per cell, in cell order). Each
    entry is either None (no per-cell block) or a dict that will be
    JSON-serialized by the gate.

    cell_outputs / cell_exec_count override the default per-cell outputs
    (used to simulate a re-execution that produced different output).
    """
    cells = []
    for i, per in enumerate(per_cell_blocks):
        if cell_outputs is not None:
            outs = cell_outputs if i < len(cell_outputs) else []
        else:
            outs = [] if outputs_executed else []
        if cell_exec_count is not None:
            ec = cell_exec_count if i < len(cell_exec_count) else \
                (1 if outputs_executed else None)
        else:
            ec = 1 if outputs_executed else None
        cells.append({
            "cell_type": "code",
            "id": f"c{i}",
            "metadata": {} if per is None else {"papermill": dict(per)},
            "execution_count": ec,
            "outputs": outs,
            "source": "1 + 1",
        })
    return {
        "cells": cells,
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "language": "python",
                           "name": "python3"},
            "language_info": {"name": "python"},
            "papermill": dict(top_block) if top_block is not None else None,
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _states(base_nb, head_nb, base_stripped_thunk=None):
    """Wrap two notebooks as (base_state, head_state) tuples for classify."""
    return (
        ("OK", cpr.exec_evidence(base_nb), cpr.papermill_block(base_nb),
         cpr.cell_papermill_signature(base_nb), base_stripped_thunk),
        ("OK", cpr.exec_evidence(head_nb), cpr.papermill_block(head_nb),
         cpr.cell_papermill_signature(head_nb), None),
    )


# Reusable blocks -----------------------------------------------------------

TOP_RUN_A = {
    "default_parameters": {},
    "duration": 9.28,
    "end_time": "2026-05-31T22:55:02.293900+00:00",
    "environment_variables": {},
    "exception": None,
    "start_time": "2026-05-31T22:54:53.016187+00:00",
    "version": "2.6.0",
}

TOP_RUN_B = {
    "default_parameters": {},
    "duration": 12.50,
    "end_time": "2026-10-18T22:00:00.000000+00:00",  # different from A
    "environment_variables": {},
    "exception": None,
    "start_time": "2026-10-18T21:59:50.000000+00:00",  # different from A
    "version": "2.6.0",
}

PER_CELL_A = [{"duration": 9.28, "start_time": "2026-05-31T22:54:53.016187+00:00",
               "end_time": "2026-05-31T22:55:02.293900+00:00"}]

PER_CELL_B = [{"duration": 12.50, "start_time": "2026-10-18T21:59:50.000000+00:00",
               "end_time": "2026-10-18T22:00:00.000000+00:00"}]


# --- the 4 matrix tests -----------------------------------------------------

def test_forged_block_top_changed_per_cell_identical():
    """The new regression class: hand-rewritten top over a previous run.

    Outputs MUST differ between base and head, otherwise classify short-
    circuits to OUTPUTS_UNCHANGED before consulting the block layer.
    """
    base_out = []
    head_out = [{"output_type": "stream", "name": "stdout",
                 "text": ["2\n"]}]
    base = _nb(TOP_RUN_A, PER_CELL_A,
               cell_outputs=[base_out], cell_exec_count=[1])
    head = _nb(TOP_RUN_B, PER_CELL_A,  # per-cell UNCHANGED, top CHANGED
               cell_outputs=[head_out], cell_exec_count=[2])
    verdict, regression = cpr.classify(*_states(base, head))
    assert verdict == "FORGED_BLOCK", f"got {verdict}"
    assert regression is True


def test_block_moved_top_changed_per_cell_changed():
    """Legitimate re-execution: both layers rewritten. Outputs differ."""
    base_out = []
    head_out = [{"output_type": "stream", "name": "stdout",
                 "text": ["2\n"]}]
    base = _nb(TOP_RUN_A, PER_CELL_A,
               cell_outputs=[base_out], cell_exec_count=[1])
    head = _nb(TOP_RUN_B, PER_CELL_B,  # both layers CHANGED
               cell_outputs=[head_out], cell_exec_count=[2])
    verdict, regression = cpr.classify(*_states(base, head))
    assert verdict == "BLOCK_MOVED", f"got {verdict}"
    assert regression is False


def test_stale_block_top_identical_per_cell_identical_outputs_differ():
    """Legacy regression path: top-level and per-cell layer both byte-
    identical, but the cell outputs changed -- the previous run's cover
    no longer matches what the cells produced."""
    # Build a base and a head with identical top + identical per-cell, but
    # the cell execution_count / outputs differ (different output).
    base = _nb(TOP_RUN_A, PER_CELL_A)
    head_nb = _nb(TOP_RUN_A, PER_CELL_A)
    head_nb["cells"][0]["outputs"] = [{"output_type": "stream",
                                        "name": "stdout",
                                        "text": ["2\n"]}]
    head_nb["cells"][0]["execution_count"] = 2
    verdict, regression = cpr.classify(*_states(base, head_nb))
    assert verdict == "STALE_BLOCK", f"got {verdict}"
    assert regression is True


def test_outputs_unchanged_all_identical():
    """Markdown-only edit rides the block legally: outputs unchanged."""
    base = _nb(TOP_RUN_A, PER_CELL_A)
    head = _nb(TOP_RUN_A, PER_CELL_A)  # byte-identical
    # Simulate a markdown cell added (no change in evidence / block / cell sig)
    head["cells"].append({
        "cell_type": "markdown", "id": "m0", "metadata": {},
        "source": "# Note",
    })
    verdict, regression = cpr.classify(*_states(base, head))
    assert verdict == "OUTPUTS_UNCHANGED", f"got {verdict}"
    assert regression is False


# --- 2 sanity tests --------------------------------------------------------

def test_added_notebook_absent_at_base():
    """Notebook absent at base = ADDED, no regression."""
    base_state = ("ABSENT", None, None, None, None)
    head = _nb(TOP_RUN_A, PER_CELL_A)
    head_state = ("OK", cpr.exec_evidence(head), cpr.papermill_block(head),
                  cpr.cell_papermill_signature(head), None)
    verdict, regression = cpr.classify(base_state, head_state)
    assert verdict == "ADDED", f"got {verdict}"
    assert regression is False


def test_block_removed_top_absent_at_head():
    """Block removed at head is explicitly allowed by the issue body."""
    base = _nb(TOP_RUN_A, PER_CELL_A)
    head = _nb(None, PER_CELL_B)  # top-level removed, per-cell rewritten
    verdict, regression = cpr.classify(*_states(base, head))
    assert verdict == "BLOCK_REMOVED", f"got {verdict}"
    assert regression is False


# --- direct unit test of the new signature --------------------------------

def test_cell_papermill_signature_distinguishes_layers():
    """The new signature must change when a per-cell block is rewritten,
    even if the top-level block is byte-identical. This is the whole point
    of the new layer: it lets classify see what a hand-rewritten top
    cannot hide."""
    base = _nb(TOP_RUN_A, PER_CELL_A)
    head = _nb(TOP_RUN_A, PER_CELL_B)  # per-cell differs, top identical
    sig_base = cpr.cell_papermill_signature(base)
    sig_head = cpr.cell_papermill_signature(head)
    assert sig_base != sig_head, "per-cell layer must move the signature"
    # The top-level papermill_block, in contrast, is byte-identical here:
    assert cpr.papermill_block(base) == cpr.papermill_block(head)
