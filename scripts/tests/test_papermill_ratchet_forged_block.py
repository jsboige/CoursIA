"""Tests du verdict FORGED_BLOCK dans check_papermill_ratchet.classify (#21299).

Le defaut mesure sur 3 PRs poussees en force le 18/10 (cf. issue #21299) :
un committeur peut reecrire a la main le bloc ``metadata.papermill`` de
haut niveau (start_time / end_time / duration a 16.0 s exactement) sans
toucher aux blocs ``cells[i].metadata.papermill`` par cellule. Le ratchet
pre-#21299 voyait le top-level differ et rendait ``BLOCK_MOVED`` (vert) -
un faux negatif qui laisse passer une reexecution-fantome.

Le correctif ajoute une signature de la couche par cellule. Une
re-execution reelle reecrit les deux couches ; un hand-rewrite de la
couche de haut niveau seule laisse la signature inchangee. Le verdict
devient ``FORGED_BLOCK`` (rouge) sur ce croisement.

Ces tests ne chargent aucun blob - ils construisent in-memory les etats
base/head que ``classify`` consomme directement, ce qui isole le verdict
du bruit du depot et des fixtures reelles.
"""

import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parent.parent / "notebook_tools"
sys.path.insert(0, str(TOOLS))

import check_papermill_ratchet as cpr


def _cell(ec, outputs, pm=None):
    """Build a code cell with a papermill block of shape `pm` (or none)."""
    cell = {
        "cell_type": "code",
        "execution_count": ec,
        "metadata": {},
        "outputs": outputs,
        "source": ["x = 1"],
    }
    if pm is not None:
        cell["metadata"]["papermill"] = pm
    return cell


def _pm(start, end, duration):
    return {
        "duration": duration,
        "end_time": end,
        "exception": None,
        "start_time": start,
        "status": "completed",
    }


# Two identical per-cell papermill blocks (the sign of a hand rewrite).
SHARED_CELL_PM = _pm("2026-10-15T11:05:09.679521+00:00",
                      "2026-10-15T11:05:09.688863+00:00",
                      0.009342)

# A real re-execution produces these fresh per-cell blocks.
FRESH_CELL_PM = _pm("2026-10-18T03:26:56.791771+00:00",
                    "2026-10-18T03:27:00.217140+00:00",
                    3.425369)

# A real run also produces a top-level block.
REAL_TOP = {
    "default_parameters": {},
    "duration": 3.425369,
    "end_time": "2026-10-18T03:27:00.217140+00:00",
    "environment_variables": {},
    "exception": None,
    "input_path": "x.ipynb",
    "output_path": "x.executed.ipynb",
    "parameters": {},
    "start_time": "2026-10-18T03:26:56.791771+00:00",
    "version": "2.6.0",
}

# A hand-rewritten top-level block (the 16.0 s exactly class).
HAND_TOP = dict(REAL_TOP, duration=16.0,
                start_time="2026-10-18T00:58:47.663116+00:00",
                end_time="2026-10-18T00:59:03.663116+00:00",
                input_path="x.ipynb", output_path="x.executed.ipynb")


def _state_from_nb(nb, *, status="OK"):
    return (status, cpr.exec_evidence(nb), cpr.papermill_block(nb),
            None, cpr.cell_papermill_signature(nb))


def _nb(top_block, cell_pm, base_outputs, head_outputs=None):
    """Notebook with a head variant - outputs may differ between base/head."""
    head_outputs = head_outputs if head_outputs is not None else base_outputs
    return {
        "cells": [
            _cell(1, head_outputs, cell_pm),
            _cell(2, [{"text": ["world"]}], cell_pm),
        ],
        "metadata": {"papermill": top_block},
    }


def _states(top_block_b, top_block_h, cell_pm_b, cell_pm_h, base_outputs, head_outputs):
    base = _state_from_nb(_nb(top_block_b, cell_pm_b, base_outputs, base_outputs))
    head = _state_from_nb(_nb(top_block_h, cell_pm_h, base_outputs, head_outputs))
    return base, head


# --- FORGED_BLOCK -----------------------------------------------------------


def test_forged_block_hand_rewrite_top_level_only():
    """Top-level block changed, per-cell blocks identical, outputs changed -> FORGED_BLOCK.

    This is the regression class of #21229/#21230/#21232: outputs differ
    (a fresh run produced new text), the top-level block was hand-edited
    (16.0 s exactly), but the per-cell blocks still describe the previous
    run. Real papermill re-execution would have rewritten both layers.
    """
    base, head = _states(
        REAL_TOP, HAND_TOP,
        SHARED_CELL_PM, SHARED_CELL_PM,  # per-cell blocks identical
        [{"text": ["hello"]}],
        [{"text": ["hello fresh"]}],  # outputs DID change
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "FORGED_BLOCK", verdict
    assert regression is True, regression


def test_forged_block_real_reexecution_is_block_moved():
    """Top-level AND per-cell blocks changed, outputs changed -> BLOCK_MOVED.

    Legitimate papermill re-execution path: the executor rewrote the
    top-level block AND every per-cell block, AND the outputs reflect the
    new run. The top-level + per-cell layers move together; this is the
    OK path.
    """
    base, head = _states(
        REAL_TOP, HAND_TOP,
        SHARED_CELL_PM, FRESH_CELL_PM,  # per-cell blocks differ
        [{"text": ["hello"]}],
        [{"text": ["hello fresh"]}],
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "BLOCK_MOVED", verdict
    assert regression is False, regression


def test_stale_block_still_detected_when_top_level_unchanged():
    """Outputs changed but the top-level block is byte-identical -> STALE_BLOCK.

    The original regression class of issue #11155. The per-cell blocks
    are also identical (no new papermill layer was written), which is
    consistent with the original stale-block reading.
    """
    base, head = _states(
        REAL_TOP, REAL_TOP,  # top-level byte-identical
        SHARED_CELL_PM, SHARED_CELL_PM,
        [{"text": ["hello"]}],
        [{"text": ["changed"]}],
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "STALE_BLOCK", verdict
    assert regression is True, regression


def test_outputs_unchanged_passes_regardless_of_block():
    """A markdown-only edit keeps exec_evidence identical -> OUTPUTS_UNCHANGED."""
    base, head = _states(
        REAL_TOP, REAL_TOP,
        SHARED_CELL_PM, SHARED_CELL_PM,
        [{"text": ["hello"]}],
        [{"text": ["hello"]}],  # same outputs
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "OUTPUTS_UNCHANGED", verdict
    assert regression is False, regression


def test_forged_block_not_triggered_on_added_notebook():
    """b_block is None on an added notebook - the FORGED_BLOCK branch requires it."""
    base = ("ABSENT", None, None, None, None)
    head = _state_from_nb(_nb(HAND_TOP, SHARED_CELL_PM, [{"text": ["hello fresh"]}], [{"text": ["hello fresh"]}]))
    verdict, regression = cpr.classify(base, head)
    assert verdict == "ADDED", verdict
    assert regression is False, regression


def test_block_removed_returns_block_removed():
    """Block removed at head - explicitly allowed by the issue body."""
    base, head = _states(
        REAL_TOP, None,  # block removed at head
        SHARED_CELL_PM, None,
        [{"text": ["hello"]}],
        [{"text": ["hello fresh"]}],
    )
    # Override head to have a notebook with NO papermill block at all (not even per-cell)
    head_nb = {
        "cells": [
            _cell(1, [{"text": ["hello fresh"]}], None),  # no per-cell block
            _cell(2, [{"text": ["world"]}], None),
        ],
        "metadata": {},  # no top-level block
    }
    head = _state_from_nb(head_nb)
    verdict, regression = cpr.classify(base, head)
    assert verdict == "BLOCK_REMOVED", verdict
    assert regression is False, regression
