"""Tests for check_twin_parity --coverage (python_twin_candidates).

Why this exists
---------------
The registry can only detect drift in pairs it already declares: an unregistered
pair never drifts, never fails, never appears. `--check` printed `OK=136 DRIFT=0`
while 19 real Python/C# pairs were watched by nobody.

The census that surfaced them was itself wrong on the first pass. It tested a
single naming convention (`Foo-Csharp` -> `Foo`) and confidently reported
"1 gap, 29 C#-only". The repo actually uses THREE conventions, and the other two
were silently misfiled as C#-only:

    Tweety-10-MLN-Csharp      <-> Tweety-10-MLN            suffix dropped
    Sudoku-7-Norvig-Csharp    <-> Sudoku-7-Norvig-Python   suffix substituted
    SW-10-CSharp-RDFStar      <-> SW-10-Python-RDFStar     medial token

A too-narrow predicate does not fail loudly; it returns a confident wrong
answer. Every convention is pinned here so a future edit to the matcher cannot
silently shrink coverage again -- which is the exact failure mode the tool is
meant to expose.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_twin_parity import python_twin_candidates  # noqa: E402

GT = "MyIA.AI.Notebooks/GameTheory"
SUD = "MyIA.AI.Notebooks/Sudoku"
TW = "MyIA.AI.Notebooks/SymbolicAI/Tweety"
SW = "MyIA.AI.Notebooks/SymbolicAI/SemanticWeb"

UNIVERSE = {
    # convention 1 -- suffix dropped
    f"{TW}/Tweety-10-MLN-Csharp.ipynb",
    f"{TW}/Tweety-10-MLN.ipynb",
    # convention 2 -- suffix substituted
    f"{SUD}/Sudoku-7-Norvig-Csharp.ipynb",
    f"{SUD}/Sudoku-7-Norvig-Python.ipynb",
    f"{GT}/GameTheory-4c-NashExistence-Csharp.ipynb",
    f"{GT}/GameTheory-4c-NashExistence-Python.ipynb",
    # convention 3 -- medial token
    f"{SW}/SW-10-CSharp-RDFStar.ipynb",
    f"{SW}/SW-10-Python-RDFStar.ipynb",
    # genuinely C#-only
    f"{TW}/Tweety-2c-FOL-Csharp.ipynb",
    f"{SUD}/Sudoku-0-Environment-Csharp.ipynb",
    f"{SW}/SW-1-CSharp-Setup.ipynb",
    f"{GT}/GameTheory-2-NormalForm-Csharp-Part2.ipynb",
}


def test_convention_suffix_dropped():
    assert python_twin_candidates(f"{TW}/Tweety-10-MLN-Csharp.ipynb", UNIVERSE) == [
        f"{TW}/Tweety-10-MLN.ipynb"
    ]


def test_convention_suffix_substituted():
    assert python_twin_candidates(f"{SUD}/Sudoku-7-Norvig-Csharp.ipynb", UNIVERSE) == [
        f"{SUD}/Sudoku-7-Norvig-Python.ipynb"
    ]


def test_convention_medial_token():
    """The case a suffix-only matcher cannot see: CSharp sits mid-name."""
    assert python_twin_candidates(f"{SW}/SW-10-CSharp-RDFStar.ipynb", UNIVERSE) == [
        f"{SW}/SW-10-Python-RDFStar.ipynb"
    ]


def test_csharp_only_has_no_candidate():
    """No Python sibling on disk -> legitimately C#-only, not a registry gap."""
    for cs in (
        f"{TW}/Tweety-2c-FOL-Csharp.ipynb",
        f"{SUD}/Sudoku-0-Environment-Csharp.ipynb",
        f"{SW}/SW-1-CSharp-Setup.ipynb",
    ):
        assert python_twin_candidates(cs, UNIVERSE) == [], cs


def test_part2_extension_is_csharp_only():
    """`-Csharp-Part2` is a C#-side extension: dropping the token yields
    `GameTheory-2-NormalForm-Part2`, which does not exist. No false pairing
    against the Part1 Python notebook."""
    assert python_twin_candidates(
        f"{GT}/GameTheory-2-NormalForm-Csharp-Part2.ipynb", UNIVERSE
    ) == []


def test_absent_sibling_yields_no_candidate():
    """A convention that matches by name but whose target is absent from the
    universe must not be reported -- the predicate is existence, not naming."""
    universe = {f"{SUD}/Sudoku-3-Genetic-Csharp.ipynb"}
    assert python_twin_candidates(f"{SUD}/Sudoku-3-Genetic-Csharp.ipynb", universe) == []


def test_same_directory_preferred_over_homonym_elsewhere():
    """A sibling in the same directory wins over a same-stem file elsewhere."""
    universe = {
        f"{SUD}/Sudoku-7-Norvig-Csharp.ipynb",
        f"{SUD}/Sudoku-7-Norvig-Python.ipynb",
        f"{GT}/Sudoku-7-Norvig-Python.ipynb",
    }
    assert python_twin_candidates(f"{SUD}/Sudoku-7-Norvig-Csharp.ipynb", universe) == [
        f"{SUD}/Sudoku-7-Norvig-Python.ipynb"
    ]


def test_case_variants_of_the_token():
    """`Csharp`, `CSharp` and `csharp` are all in use across the repo."""
    universe = {
        "d/A-Csharp.ipynb", "d/A.ipynb",
        "d/B-CSharp.ipynb", "d/B.ipynb",
        "d/c-csharp.ipynb", "d/c.ipynb",
    }
    for cs, expected in (
        ("d/A-Csharp.ipynb", "d/A.ipynb"),
        ("d/B-CSharp.ipynb", "d/B.ipynb"),
        ("d/c-csharp.ipynb", "d/c.ipynb"),
    ):
        assert python_twin_candidates(cs, universe) == [expected], cs


def test_no_duplicates_and_convention_order_preserved():
    """When several conventions resolve, each path appears once and the order is
    convention priority (dropped, then substituted) -- not alphabetical. The
    first candidate is the likeliest twin, which is what a reader acts on."""
    universe = {"d/X-Csharp.ipynb", "d/X.ipynb", "d/X-Python.ipynb"}
    got = python_twin_candidates("d/X-Csharp.ipynb", universe)
    assert len(got) == len(set(got))
    assert got == ["d/X.ipynb", "d/X-Python.ipynb"]
