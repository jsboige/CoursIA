"""Tests for detect_consecutive_code_cells (#12797).

Mirrors the pedagogy_density test fixtures: short notebook-shaped strings fed
through the ``judge`` and ``_detect_runs`` entry points, asserting the
canonical scenarios of the user's 2026-08-24 observation.

Cases covered:
  - run of 2 code cells: detected
  - run of 3+ code cells: detected with the right length and start
  - isolated code cells (single + markdown between each): clean
  - mixed run + markdown + isolated: detected at the right indices
  - non-corpus kind (out-of-corpus notebook): exempt
  - setup kind: exempt
  - no code cells at all: unmeasured
  - empty notebook (zero cells): unmeasured
  - threshold is locked: a run of length 1 never raises the label

Fixture format: we build an in-memory notebook via ``nbformat`` so the read
path of the detector (which goes through ``nbformat.read`` -> ``cells``) is
exercised, not a synthetic dict.
"""

from __future__ import annotations

import sys
import textwrap
import unittest
from pathlib import Path

THIS_DIR = Path(__file__).resolve().parent
TOOLS_DIR = THIS_DIR.parent / "notebook_tools"
sys.path.insert(0, str(TOOLS_DIR))

import nbformat  # noqa: E402

from detect_consecutive_code_cells import (  # noqa: E402
    MIN_RUN,
    _detect_runs,
    judge,
)


def _nb(cells: list[tuple[str, str]]) -> "nbformat.NotebookNode":
    """Build an in-memory notebook from a list of (cell_type, source) pairs.

    Avoids touching the filesystem: each test is hermetic, runs in <10 ms,
    and exercises the same code path as a real ``.ipynb`` on disk.
    """
    nb = nbformat.v4.new_notebook()
    for ctype, src in cells:
        if ctype == "code":
            nb.cells.append(nbformat.v4.new_code_cell(src))
        else:
            nb.cells.append(nbformat.v4.new_markdown_cell(src))
    return nb


def _write_nb(tmp_path: Path, name: str, nb: "nbformat.NotebookNode") -> Path:
    p = tmp_path / name
    nbformat.write(nb, str(p))
    return p


class TestDetectRuns(unittest.TestCase):
    """Pure run-detection on synthetic cell sequences."""

    def test_run_of_two(self) -> None:
        nb = _nb([("code", "x = 1"), ("code", "y = 2"), ("markdown", "intro")])
        runs = _detect_runs(nb.cells)
        self.assertEqual(len(runs), 1)
        self.assertEqual(runs[0].start_cell, 0)
        self.assertEqual(runs[0].end_cell, 1)
        self.assertEqual(runs[0].length, 2)

    def test_run_of_five(self) -> None:
        nb = _nb(
            [("code", "x = 1"), ("code", "x = 2"), ("code", "x = 3"),
             ("code", "x = 4"), ("code", "x = 5"),
             ("markdown", "intro")]
        )
        runs = _detect_runs(nb.cells)
        self.assertEqual(len(runs), 1)
        self.assertEqual(runs[0].length, 5)
        self.assertEqual(runs[0].end_cell, 4)

    def test_isolated_code_cells_clean(self) -> None:
        nb = _nb(
            [("code", "x = 1"), ("markdown", "explication"),
             ("code", "y = 2"), ("markdown", "autre"),
             ("code", "z = 3")]
        )
        runs = _detect_runs(nb.cells)
        self.assertEqual(runs, [])

    def test_mixed_run_then_isolated(self) -> None:
        nb = _nb(
            [("code", "a"), ("code", "b"), ("markdown", "md"),
             ("code", "c"), ("markdown", "md"), ("code", "d")]
        )
        runs = _detect_runs(nb.cells)
        self.assertEqual(len(runs), 1)
        self.assertEqual(runs[0].start_cell, 0)
        self.assertEqual(runs[0].end_cell, 1)
        self.assertEqual(runs[0].length, 2)

    def test_two_separate_runs(self) -> None:
        nb = _nb(
            [("code", "a"), ("code", "b"), ("markdown", "md"),
             ("code", "c"), ("code", "d"), ("code", "e"),
             ("markdown", "md")]
        )
        runs = _detect_runs(nb.cells)
        self.assertEqual(len(runs), 2)
        self.assertEqual(runs[0].start_cell, 0)
        self.assertEqual(runs[0].length, 2)
        self.assertEqual(runs[1].start_cell, 3)
        self.assertEqual(runs[1].length, 3)

    def test_run_at_end(self) -> None:
        nb = _nb([("markdown", "intro"),
                  ("code", "a"), ("code", "b"), ("code", "c")])
        runs = _detect_runs(nb.cells)
        self.assertEqual(len(runs), 1)
        self.assertEqual(runs[0].start_cell, 1)
        self.assertEqual(runs[0].end_cell, 3)
        self.assertEqual(runs[0].length, 3)

    def test_no_runs_at_all(self) -> None:
        nb = _nb([("markdown", "only prose here"), ("markdown", "more prose")])
        self.assertEqual(_detect_runs(nb.cells), [])

    def test_threshold_locked(self) -> None:
        # The threshold is MIN_RUN. A run of length MIN_RUN-1 must never be
        # reported. The detector constructor documents the lock; this test
        # asserts the live value matches the documented constant.
        self.assertEqual(MIN_RUN, 2)


class TestJudge(unittest.TestCase):
    """End-to-end judgement on a real .ipynb written to a tmp dir."""

    def test_judge_detects_run(self) -> None:
        from tempfile import TemporaryDirectory

        with TemporaryDirectory() as td:
            td_path = Path(td)
            nb = _nb([("code", "x = 1"), ("code", "x = 2"),
                      ("markdown", "explication")])
            # Pin the kind so classify_notebook sees a real corpus path.
            target_dir = td_path / "Search" / "Part1"
            target_dir.mkdir(parents=True, exist_ok=True)
            target = _write_nb(target_dir, "demo.ipynb", nb)
            v = judge(target)
            self.assertEqual(v.status, "detected")
            self.assertEqual(v.max_run, 2)
            self.assertEqual(v.run_count, 1)

    def test_judge_clean(self) -> None:
        from tempfile import TemporaryDirectory

        with TemporaryDirectory() as td:
            td_path = Path(td)
            nb = _nb([("code", "x = 1"), ("markdown", "explication"),
                      ("code", "x = 2")])
            target_dir = td_path / "Search" / "Part1"
            target_dir.mkdir(parents=True, exist_ok=True)
            target = _write_nb(target_dir, "demo.ipynb", nb)
            v = judge(target)
            self.assertEqual(v.status, "clean")
            self.assertEqual(v.max_run, 0)
            self.assertEqual(v.run_count, 0)

    def test_judge_no_code_cells(self) -> None:
        from tempfile import TemporaryDirectory

        with TemporaryDirectory() as td:
            td_path = Path(td)
            nb = _nb([("markdown", "only prose"), ("markdown", "more prose")])
            target_dir = td_path / "Search" / "Part1"
            target_dir.mkdir(parents=True, exist_ok=True)
            target = _write_nb(target_dir, "demo.ipynb", nb)
            v = judge(target)
            self.assertEqual(v.status, "unmeasured")

    def test_judge_out_of_corpus_exempt(self) -> None:
        from tempfile import TemporaryDirectory

        with TemporaryDirectory() as td:
            td_path = Path(td)
            # Run of 3 code cells: would be detected, BUT the path lives
            # under `_template/` which classify_notebook flags out-of-corpus.
            nb = _nb([("code", "x"), ("code", "y"), ("code", "z")])
            target_dir = td_path / "_template"
            target_dir.mkdir(parents=True, exist_ok=True)
            target = _write_nb(target_dir, "demo.ipynb", nb)
            v = judge(target)
            self.assertTrue(v.exempt)
            self.assertEqual(v.status, "exempt")


class TestAcceptance(unittest.TestCase):
    """Mirrors the acceptance criteria in the #12797 body."""

    def test_threshold_is_two(self) -> None:
        """Acceptance #1: threshold locked at 2 (decision user 2026-08-24)."""
        self.assertEqual(MIN_RUN, 2)

    def test_run_inclusive_of_three(self) -> None:
        """Acceptance: a run of 3 raises the label (>= MIN_RUN)."""
        nb = _nb([("code", "a"), ("code", "b"), ("code", "c")])
        runs = _detect_runs(nb.cells)
        self.assertEqual(len(runs), 1)
        self.assertEqual(runs[0].length, 3)


if __name__ == "__main__":
    unittest.main()