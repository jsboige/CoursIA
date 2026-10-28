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
            None, cpr.cell_papermill_signature(nb),
            cpr.cell_papermill_blocks(nb), None)


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
    base = ("ABSENT", None, None, None, None, None, None)
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


# --- per-cell FORGED_BLOCK (c2187-ask, refine #21299) --------------------
#
# The original FORGED_BLOCK detector compares the global per-cell signature
# (a concatenation of every per-cell block). It catches the all-identical
# case (the 3 PRs that founded #21299 rode this path). The c2187-ask
# refines it: a hand-rewrite that touches the top-level AND some per-cell
# blocks but leaves at least one cell-with-changed-output's per-cell block
# byte-identical to the base is still FORGED_BLOCK. A real re-execution
# rewrites every per-cell block together with the top-level one.

# A SECOND legitimate per-cell block (the 3rd code cell's run was retried
# by the executor) -- distinct from FRESH_CELL_PM by both timestamps and
# duration.
ALT_CELL_PM = _pm("2026-10-19T07:11:43.123456+00:00",
                  "2026-10-19T07:11:46.789012+00:00",
                  3.665556)


def _nb_with_per_cell_pms(top_block, cell_pms, base_outputs, head_outputs):
    """Notebook with one code cell per entry in cell_pms (and outputs).

    cell_pms[i] is the per-cell papermill block of code cell i (or None to
    skip). base_outputs[i] and head_outputs[i] are the outputs lists of
    cell i. Cell count = len(cell_pms) = len(base_outputs) =
    len(head_outputs).
    """
    assert len(cell_pms) == len(base_outputs) == len(head_outputs)
    cells = [_cell(i + 1, head_outputs[i], cell_pms[i])
             for i in range(len(cell_pms))]
    return {
        "cells": cells,
        "metadata": {"papermill": top_block},
    }


def _states_with_per_cell(top_block_b, top_block_h, cell_pms_b, cell_pms_h,
                          base_outputs, head_outputs):
    base = _state_from_nb(_nb_with_per_cell_pms(
        top_block_b, cell_pms_b, base_outputs, base_outputs))
    head = _state_from_nb(_nb_with_per_cell_pms(
        top_block_h, cell_pms_h, base_outputs, head_outputs))
    return base, head


def test_forged_block_partial_per_cell_hand_rewrite():
    """Per-cell check: only SOME per-cell blocks touched, one cell's block
    still identical to base while its outputs changed -> FORGED_BLOCK.

    c2187-ask. The global signature check above is the special case where
    ALL per-cell blocks are identical; this test pins the partial case.
    The hand-rewriter touched the top-level block AND cell 1's per-cell
    block (the executor-like signal), but cell 0's per-cell block is still
    the base block while its outputs changed - a real re-execution would
    have rewritten both.
    """
    base, head = _states_with_per_cell(
        REAL_TOP, HAND_TOP,  # top-level changed
        [SHARED_CELL_PM, SHARED_CELL_PM],  # base per-cell
        [SHARED_CELL_PM, ALT_CELL_PM],     # head: cell 0 untouched, cell 1 retried
        [{"text": ["hello"]}, {"text": ["world"]}],
        [{"text": ["hello fresh"]}, {"text": ["world"]}],  # only cell 0's outputs changed
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "FORGED_BLOCK", verdict
    assert regression is True, regression


def test_forged_block_per_cell_does_not_flag_legit_partial():
    """Legit re-execution: per-cell blocks ALL changed (one per cell, even
    if they happen to share a value with the base by accident) AND outputs
    changed -> BLOCK_MOVED, NOT FORGED_BLOCK.

    A real re-execution can produce a per-cell block byte-identical to the
    base by accident (same kernel, same code, same duration). The check
    must NOT flag this as FORGED_BLOCK. The per-cell check is gated on
    ``b_line != h_line`` (outputs changed) AND ``b_pm == h_pm`` (block
    identical). A real run with rewritten outputs will have rewritten
    per-cell blocks for those cells; this test confirms the gate.
    """
    base, head = _states_with_per_cell(
        REAL_TOP, HAND_TOP,
        [SHARED_CELL_PM, SHARED_CELL_PM],
        [FRESH_CELL_PM, FRESH_CELL_PM],  # all per-cell blocks rewritten
        [{"text": ["hello"]}, {"text": ["world"]}],
        [{"text": ["hello fresh"]}, {"text": ["world fresh"]}],
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "BLOCK_MOVED", verdict
    assert regression is False, regression


def test_forged_block_per_cell_block_added_not_flagged():
    """A new per-cell block at head (not in base) is not a forgery. Real
    re-execution can populate a per-cell block that the base lacked. The
    check requires a per-cell block on BOTH sides."""
    base, head = _states_with_per_cell(
        REAL_TOP, HAND_TOP,
        [None, SHARED_CELL_PM],     # base: cell 0 had no per-cell block
        [FRESH_CELL_PM, ALT_CELL_PM],  # head: cell 0 now has a fresh one
        [{"text": ["hello"]}, {"text": ["world"]}],
        [{"text": ["hello fresh"]}, {"text": ["world fresh"]}],
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "BLOCK_MOVED", verdict
    assert regression is False, regression


def test_forged_block_not_triggered_on_notebook_without_per_cell_blocks():
    """Notebooks with a top-level papermill block but no per-cell blocks
    (legacy papermill versions, or pre-per-cell-write runs) cannot be a
    hand-rewrite of the top-level -- the per-cell layer is simply absent.
    Without the ``b_cell_pms`` truthiness guard on the global signature
    branch, a legitimate BLOCK_MOVED (executor rewrote the top-level
    alongside outputs) was being mis-routed as FORGED_BLOCK because both
    per-cell signatures are the empty string.

    C'est le cas du test legacy ``test_block_moved_passes`` (run 39179203301
    rouge au head ``c0799dd1``) : les notebooks construits par ``make_nb``
    n'ont qu'un bloc top-level, et la garde globale se declenchait a tort
    (regression du contrat #11155, reproduit in-memory par Hermes en revue
    c2190, 19/10 03:08Z). Le correctif ajoute ``b_cell_pms`` truthiness a
    la branche FORGED_BLOCK globale, ce qui retablit BLOCK_MOVED pour les
    notebooks sans per-cell blocks.
    """
    base, head = _states(
        REAL_TOP, HAND_TOP,
        None, None,  # no per-cell blocks on either side
        [{"text": ["hello"]}],
        [{"text": ["hello fresh"]}],
    )
    verdict, regression = cpr.classify(base, head)
    assert verdict == "BLOCK_MOVED", verdict
    assert regression is False, regression
