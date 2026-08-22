"""Unit tests for count_exercises.py.

Fix #12305 : the first pass (markdown-header detection) used to push
ExerciseHits unconditionally -- a notebook titled ``## Exercice 1 : ...``
followed by a *complete* solution cell rendered `count=1, conforming=True`.
The fix defers the push to the pairing pass and gates it on the paired code
cell being an actual stub.

This module pins the 4 acceptance criteria from the issue:

1. A notebook with 3 ``## Exercice N`` titles + 3 *complete* solutions
   renders **0** (was 3).
2. A notebook with the same 3 titles + 3 *real stubs* still renders **3**
   (non-regression -- the most-claimed path on the corpus).
3. A bare stub (no header) is still counted once (non-regression -- the
   pass-2 logic).
4. A bare title (no code cell after it at all) renders **0** (was 1).

Also pins repo-wide rollout safety : GT-20 / GT-21 with the fix behave the
same as before (those notebooks have real stubs, not solutions, so the
behaviour change is a no-op there).

Run from repo root::

    python -m pytest scripts/tests/test_count_exercises_stub_gate.py -q
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_SCRIPTS = Path(__file__).resolve().parent.parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

# `count_exercises.py` lives at `scripts/notebook_tools/count_exercises.py`
# as a flat module (no `__init__.py` makes `notebook_tools/` a package, and
# the parent directory `scripts/notebook_tools.py` is a separate shim). To
# import the SUT directly, we add the *directory* to sys.path and pull the
# module by name -- mirroring the bootstrap pattern of
# test_relabel_qc_exercises.py.
_NOTEBOOK_TOOLS_DIR = _SCRIPTS / "notebook_tools"
if str(_NOTEBOOK_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_NOTEBOOK_TOOLS_DIR))

from count_exercises import count_exercises_in_notebook  # noqa: E402


def _write_notebook(tmp_path: Path, name: str, cells: list[dict]) -> Path:
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / name
    p.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")
    return p


# --- acceptance criteria from #12305 ----------------------------------------


def test_fixture_a_title_with_complete_solution_counts_zero(tmp_path):
    """#12305 criterion 1 : title + complete solution -> 0."""
    cells = [
        {"cell_type": "markdown", "source": ["Intro."], "metadata": {}},
        {"cell_type": "markdown", "source": ["## Exercice 1 : the duel"], "metadata": {}},
        # Solution complete: ~14 effective code lines (def + arithmetic + assert),
        # no stub marker -- this is the BUG pattern.
        {
            "cell_type": "code",
            "source": [
                "def solve():\n",
                "    x = 5\n",
                "    y = 10\n",
                "    z = x + y\n",
                "    return z * 2\n",
                "\n",
                "result = solve()\n",
                "assert result == 30\n",
                "print(result)\n",
            ],
            "metadata": {},
            "outputs": [],
            "execution_count": 1,
        },
        {"cell_type": "markdown", "source": ["## Exercice 2 : couple"], "metadata": {}},
        {
            "cell_type": "code",
            "source": [
                "def couple():\n",
                "    return 42\n",
                "\n",
                "assert couple() == 42\n",
                "print(couple())\n",
            ],
            "metadata": {},
            "outputs": [],
            "execution_count": 2,
        },
        {"cell_type": "markdown", "source": ["## Exercice 3 : evanouissement"], "metadata": {}},
        {
            "cell_type": "code",
            "source": [
                "x = 100\n",
                "if x > 50:\n",
                "    print('big')\n",
                "else:\n",
                "    print('small')\n",
                "print('done')\n",
            ],
            "metadata": {},
            "outputs": [],
            "execution_count": 3,
        },
    ]
    p = _write_notebook(tmp_path, "fixture_a.ipynb", cells)
    nb = count_exercises_in_notebook(p)
    assert nb.count == 0, f"expected 0 (title-only, no stubs), got {nb.count}"
    # NB : conforming is the cross-section (3 stubs in the issue's spec = 3
    # to honor). 0 exercises = no obligation = trivially conforming. The bug
    # was that `conforming` evaluated to True with `count == 3` and *no real
    # stubs*. After the fix, count==0 (correct), conforming==True (no
    # obligation to violate). This is the desired new behaviour.


def test_fixture_b_title_with_real_stub_counts_three(tmp_path):
    """#12305 criterion 2 : title + stub -> 3 (non-regression)."""
    cells = [
        {"cell_type": "markdown", "source": ["Intro GT-21."], "metadata": {}},
        {"cell_type": "markdown", "source": ["## Exercice 1 : composition"], "metadata": {}},
        {"cell_type": "code", "source": ["# Exercice 1 : a completer\n"], "metadata": {}, "outputs": [], "execution_count": 1},
        {"cell_type": "markdown", "source": ["## Exercice 2 : ordre"], "metadata": {}},
        {"cell_type": "code", "source": ["# Exercice 2 : a completer\n"], "metadata": {}, "outputs": [], "execution_count": 2},
        {"cell_type": "markdown", "source": ["## Exercice 3 : types"], "metadata": {}},
        {"cell_type": "code", "source": ["# Exercice 3 : a completer\n"], "metadata": {}, "outputs": [], "execution_count": 3},
    ]
    p = _write_notebook(tmp_path, "fixture_b.ipynb", cells)
    nb = count_exercises_in_notebook(p)
    assert nb.count == 3, f"expected 3 (3 real stubs), got {nb.count}"
    assert nb.conforming is True


def test_fixture_c_bare_stub_still_counts(tmp_path):
    """#12305 criterion 3 : stub without title -> 1 (non-regression)."""
    cells = [
        {"cell_type": "code", "source": ["# Exercice : a completer\n"], "metadata": {}, "outputs": [], "execution_count": 1},
    ]
    p = _write_notebook(tmp_path, "fixture_c.ipynb", cells)
    nb = count_exercises_in_notebook(p)
    assert nb.count == 1, f"expected 1 (bare stub), got {nb.count}"


def test_fixture_d_title_alone_counts_zero(tmp_path):
    """#12305 criterion 4 : bare title (no code after) -> 0 (was 1)."""
    cells = [
        {"cell_type": "markdown", "source": ["## Exercice 1 : no code follows"], "metadata": {}},
        {"cell_type": "markdown", "source": ["## Continuer avec autre chose"], "metadata": {}},
    ]
    p = _write_notebook(tmp_path, "fixture_d.ipynb", cells)
    nb = count_exercises_in_notebook(p)
    assert nb.count == 0, f"expected 0 (title alone, no stub), got {nb.count}"
    # count==0 = trivially conforming (no obligation). The fix's substance
    # is on `count`, not `conforming`.


def test_fixture_e_numbered_header_with_complete_solution_counts_zero(tmp_path):
    """PR #12246 / GT-20 case (the actual founder of #12305).

    A numbered header `## Exercice 1` followed by a complete solution
    (`def solve(): ...; assert result == 30` -- multi-line, no `# TODO` /
    `pass` / `return None` / `# Indice` markers, ~10 effective code lines)
    must NOT count as an exercise.

    c.458's first attempt over-applied the gate (`_is_stub_code` AND
    `_code_cell_mentions_exercise`), which broke the corpus's canonical
    stubs that use `# TODO` as the marker (TODO does not contain the
    word "exercice"). c.459 relaxes to `_is_stub_code` alone, which is
    what the issue text prescribes: "n'ajouter le ExerciseHit de titre
    que si la cellule code appariee est un stub au sens de _is_stub_code".
    """
    cells = [
        {"cell_type": "markdown", "source": ["## Exercice 1 : complete solution follows"], "metadata": {}},
        {
            "cell_type": "code",
            "source": [
                "def solve():\n",
                "    x = 5\n",
                "    y = 10\n",
                "    z = x + y\n",
                "    return z * 2\n",
                "\n",
                "result = solve()\n",
                "assert result == 30\n",
                "print(result)\n",
            ],
            "metadata": {},
            "outputs": [],
            "execution_count": 1,
        },
    ]
    p = _write_notebook(tmp_path, "fixture_e.ipynb", cells)
    nb = count_exercises_in_notebook(p)
    assert nb.count == 0, f"GT-20 case: expected 0 (numbered + complete solution), got {nb.count}"


def test_fixture_f_todo_stub_marker_counts(tmp_path):
    """Canonical corpus pattern : `# TODO` + `pass` (no "exercice" word).

    The corpus's most common stub form is `# TODO etudiant` / `# TODO` /
    `# Indice` followed by `pass` / `return None`. These do NOT contain the
    word "exercice". c.458's first attempt over-applied by requiring
    `_code_cell_mentions_exercise` (an "exercice" reference in a comment),
    which broke the corpus. c.459 uses `_is_stub_code` alone -- `# TODO`
    matches STUB_PATTERNS, so the cell qualifies as a stub.
    """
    cells = [
        {"cell_type": "markdown", "source": ["## Exercice 1 : canon"], "metadata": {}},
        {"cell_type": "code", "source": ["# TODO etudiant\n", "pass\n"], "metadata": {}, "outputs": [], "execution_count": 1},
    ]
    p = _write_notebook(tmp_path, "fixture_f.ipynb", cells)
    nb = count_exercises_in_notebook(p)
    assert nb.count == 1, f"expected 1 (TODO+pass canonical stub), got {nb.count}"


# --- non-regression on the corpus --------------------------------------------


REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
GT20 = REPO_ROOT / "MyIA.AI.Notebooks" / "GameTheory" / "GameTheory-20-Commitment-Stackelberg.ipynb"
GT21 = REPO_ROOT / "MyIA.AI.Notebooks" / "GameTheory" / "GameTheory-21-Deux-Especes-de-Fleches.ipynb"


@pytest.mark.skipif(not GT20.exists(), reason="GT-20 not on this checkout")
def test_gt20_real_stubs_count_4():
    """GT-20 : real student stubs (8/14/16) + headers 7/13/15 -- paired via
    forward stub, 3 markdown_header pushes (one doubled in the source = 4)."""
    nb = count_exercises_in_notebook(GT20)
    # The existing 4-count behaviour is preserved (no regression) -- the
    # third title cell has 2 instance_lines matched by the same forward
    # stub (an unrelated pre-existing double-count, NOT introduced by the
    # fix; it pre-dated #12305). Documented in the topic file.
    assert nb.count == 4, f"GT-20 expected 4 (vrais stubs, defaut doublon pre-existant), got {nb.count}"


@pytest.mark.skipif(not GT21.exists(), reason="GT-21 not on this checkout")
def test_gt21_real_stubs_count_3():
    """GT-21 : real stubs via 'stub-puis-header' layout -> pairing backward
    + pass-2 code_cell_comment, count = 3."""
    nb = count_exercises_in_notebook(GT21)
    assert nb.count == 3, f"GT-21 expected 3 (stubs detected as code_cell_comment), got {nb.count}"


# --- check that the discriminators are exported (gate against refactor) -----


def test_discriminators_are_exported():
    """The fix relies on `_is_stub_code` and `_code_cell_mentions_exercise`
    being importable from count_exercises.py -- a future refactor that
    inlines them or moves them into a private helper would re-open the bug
    silently. Pin the contract."""
    import count_exercises as _ce  # noqa: PLC0415 -- local import by design

    assert callable(getattr(_ce, "_is_stub_code", None))
    assert callable(getattr(_ce, "_code_cell_mentions_exercise", None))
    assert callable(getattr(_ce, "_exercise_number", None))
