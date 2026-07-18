#!/usr/bin/env python3
"""Tests for ``detect_papermill_cell_level_state.py``.

Coverage:

- ``_classify_cell_level_state`` — clean cell / cell with exception truthy
  / cell with status pending / cell with error-tag / cell with both
  exception and error-tag (single defect) / cell with missing metadata
  / cell with malformed types / non-dict metadata / ``exception=False``
  baseline.
- ``scan_notebook`` — unreadable notebook returns a structured defect,
  no papermill cell-level metadata returns no defect, cell-level defect
  is reported with cell_index / file / kind / severity fields.
- ``scan_tree`` — recursive scan skips noise dirs, returns defects in
  notebook-then-cell order.
- ``main`` — CLI exit codes 0 (clean), 1 (defect found, ``--check``),
  2 (path does not exist), ``--summary`` rendering.

Run::

    python scripts/notebook_tools/tests/test_detect_papermill_cell_level_state.py
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Make the parent ``scripts/notebook_tools/`` importable so we can load
# the detector module directly.
_HERE = Path(__file__).resolve()
_SCRIPTS_DIR = _HERE.parent.parent
sys.path.insert(0, str(_SCRIPTS_DIR))

import detect_papermill_cell_level_state as detector  # noqa: E402


# --- Test fixtures ---


def _nb(cells_meta: list[dict]) -> dict:
    """Build a minimal notebook with the given per-cell metadata blocks.

    Each entry in ``cells_meta`` becomes one cell; the cell_type defaults
    to ``"code"`` (the detector does not branch on type — papermill
    metadata is written on every executed cell, code or markdown).
    """
    cells: list[dict] = []
    for cm in cells_meta:
        cell: dict = {
            "cell_type": "code",
            "metadata": cm,
            "source": [],
            "outputs": [],
            "execution_count": None,
        }
        cells.append(cell)
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _clean_meta() -> dict:
    """A cell-level metadata block representing a clean papermill run."""
    return {
        "papermill": {
            "duration": 0.123,
            "end_time": "2026-06-03T01:51:47.762780+00:00",
            "exception": False,
            "start_time": "2026-06-03T01:51:45.447442+00:00",
            "status": "completed",
        }
    }


def _failed_meta() -> dict:
    """A cell-level metadata block where the cell itself raised."""
    return {
        "papermill": {
            "duration": 4.466384,
            "end_time": "2026-06-03T01:51:52.343377+00:00",
            "exception": True,
            "start_time": "2026-06-03T01:51:47.876993+00:00",
            "status": "failed",
        }
    }


def _pending_meta() -> dict:
    """A cell-level metadata block where the run never finished."""
    return {
        "papermill": {
            "duration": None,
            "end_time": None,
            "exception": None,
            "start_time": None,
            "status": "pending",
        }
    }


def _tag_only_meta() -> dict:
    """Cell-level metadata with the error-tag but no papermill block.

    This is the canonical fingerprint left when ``metadata.papermill``
    was scrubbed but the tag was not. Same defect class as the version
    where both are present.
    """
    return {"tags": ["papermill-error-cell-tag"]}


def _empty_meta() -> dict:
    """Cell-level metadata with no papermill fingerprint at all."""
    return {}


# --- Classification tests ---


class TestClassifyCellLevelState(unittest.TestCase):
    """``_classify_cell_level_state`` returns the right defects per cell."""

    def test_clean_cell_returns_no_defect(self):
        self.assertEqual(detector._classify_cell_level_state(_clean_meta()), [])

    def test_empty_metadata_returns_no_defect(self):
        self.assertEqual(detector._classify_cell_level_state(_empty_meta()), [])

    def test_cell_with_exception_truthy_returns_hard_failure(self):
        defects = detector._classify_cell_level_state(_failed_meta())
        self.assertEqual(len(defects), 1)
        d = defects[0]
        self.assertEqual(d["kind"], "cell_papermill_hard_failure")
        self.assertEqual(d["location"], "metadata.papermill.exception")
        self.assertEqual(d["severity"], "high")
        self.assertIs(d["exception"], True)
        self.assertEqual(d["status"], "failed")

    def test_cell_with_pending_status_returns_pending_defect(self):
        defects = detector._classify_cell_level_state(_pending_meta())
        self.assertEqual(len(defects), 1)
        d = defects[0]
        self.assertEqual(d["kind"], "cell_papermill_pending")
        self.assertEqual(d["location"], "metadata.papermill.status")
        self.assertEqual(d["severity"], "medium")
        self.assertEqual(d["status"], "pending")

    def test_cell_with_error_tag_only_returns_tag_defect(self):
        defects = detector._classify_cell_level_state(_tag_only_meta())
        self.assertEqual(len(defects), 1)
        d = defects[0]
        self.assertEqual(d["kind"], "cell_papermill_error_tag")
        self.assertEqual(d["location"], "metadata.tags")
        self.assertEqual(d["severity"], "medium")
        self.assertEqual(d["tag"], "papermill-error-cell-tag")

    def test_exception_truthy_dominates_error_tag(self):
        """A cell with both exception=True and the error tag yields one defect.

        The hard failure absorbs the tag (single defect per cell — the
        more severe class wins). Same discipline as the top-level
        detector's single-defect-per-notebook.
        """
        meta = {**_failed_meta(), "tags": ["papermill-error-cell-tag"]}
        defects = detector._classify_cell_level_state(meta)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["kind"], "cell_papermill_hard_failure")

    def test_exception_falsy_does_not_trigger_hard_failure(self):
        """``exception: False`` is a clean baseline."""
        meta = {"papermill": {"exception": False, "status": "completed"}}
        self.assertEqual(detector._classify_cell_level_state(meta), [])

    def test_non_dict_metadata_returns_no_defect(self):
        self.assertEqual(detector._classify_cell_level_state("not a dict"), [])  # type: ignore[arg-type]

    def test_malformed_papermill_block_returns_no_defect(self):
        """A papermill block that is not a dict is silently skipped.

        Mirrors ``detect_papermill_failed_state``: the classifier only
        inspects well-typed fields. Garbage in, no false defect out.
        """
        meta = {"papermill": "not a dict"}
        self.assertEqual(detector._classify_cell_level_state(meta), [])

    def test_papermill_block_missing_returns_no_defect(self):
        meta = {"tags": ["unrelated"]}
        self.assertEqual(detector._classify_cell_level_state(meta), [])


# --- scan_notebook tests ---


class TestScanNotebook(unittest.TestCase):
    """``scan_notebook`` walks every cell and emits defects in cell order."""

    def _write_nb(self, nb: dict, tmpdir: Path) -> Path:
        path = tmpdir / "fixture.ipynb"
        path.write_text(json.dumps(nb), encoding="utf-8")
        return path

    def test_no_papermill_metadata_returns_no_defect(self):
        nb = _nb([_empty_meta(), _empty_meta()])
        with tempfile.TemporaryDirectory() as td:
            path = self._write_nb(nb, Path(td))
            self.assertEqual(detector.scan_notebook(path), [])

    def test_clean_cell_returns_no_defect(self):
        nb = _nb([_clean_meta(), _clean_meta()])
        with tempfile.TemporaryDirectory() as td:
            path = self._write_nb(nb, Path(td))
            self.assertEqual(detector.scan_notebook(path), [])

    def test_single_failed_cell_returns_single_defect(self):
        nb = _nb([_clean_meta(), _failed_meta(), _clean_meta()])
        with tempfile.TemporaryDirectory() as td:
            path = self._write_nb(nb, Path(td))
            defects = detector.scan_notebook(path)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["cell_index"], 1)
            self.assertEqual(defects[0]["kind"], "cell_papermill_hard_failure")
            self.assertTrue(defects[0]["file"].endswith("fixture.ipynb"))

    def test_multiple_defects_preserve_cell_order(self):
        nb = _nb([
            _clean_meta(),
            _pending_meta(),
            _failed_meta(),
            _tag_only_meta(),
            _clean_meta(),
        ])
        with tempfile.TemporaryDirectory() as td:
            path = self._write_nb(nb, Path(td))
            defects = detector.scan_notebook(path)
            self.assertEqual(len(defects), 3)
            self.assertEqual([d["cell_index"] for d in defects], [1, 2, 3])
            self.assertEqual(defects[0]["kind"], "cell_papermill_pending")
            self.assertEqual(defects[1]["kind"], "cell_papermill_hard_failure")
            self.assertEqual(defects[2]["kind"], "cell_papermill_error_tag")

    def test_exception_and_tag_in_same_cell_yields_single_defect(self):
        nb = _nb([
            {**_failed_meta(), "tags": ["papermill-error-cell-tag"]},
        ])
        with tempfile.TemporaryDirectory() as td:
            path = self._write_nb(nb, Path(td))
            defects = detector.scan_notebook(path)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["kind"], "cell_papermill_hard_failure")

    def test_unreadable_notebook_returns_structured_defect(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "broken.ipynb"
            path.write_text("not valid json {", encoding="utf-8")
            defects = detector.scan_notebook(path)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["kind"], "unreadable_notebook")
            self.assertEqual(defects[0]["severity"], "high")

    def test_malformed_cells_field_returns_no_defect(self):
        """A notebook whose ``cells`` field is not a list yields no defect.

        Defensive: corrupted notebooks should not crash the scan.
        """
        nb = {"cells": "not a list", "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        with tempfile.TemporaryDirectory() as td:
            path = self._write_nb(nb, Path(td))
            self.assertEqual(detector.scan_notebook(path), [])

    def test_non_dict_cell_is_skipped(self):
        """A cell that is not a dict is silently skipped.

        Defensive: corrupt cells should not yield phantom defects.
        """
        # Build cells list with one valid cell, one malformed entry, one
        # failed cell. The malformed entry must be skipped, leaving the
        # failed cell at its original cell index.
        cells = [
            {"cell_type": "code", "metadata": _clean_meta(), "source": [], "outputs": [], "execution_count": None},
            "not a dict",
            {"cell_type": "code", "metadata": _failed_meta(), "source": [], "outputs": [], "execution_count": None},
        ]
        nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        with tempfile.TemporaryDirectory() as td:
            path = self._write_nb(nb, Path(td))
            defects = detector.scan_notebook(path)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["cell_index"], 2)


# --- scan_tree tests ---


class TestScanTree(unittest.TestCase):
    """``scan_tree`` walks a directory tree, skipping noise dirs."""

    def test_clean_tree_returns_no_defects(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.ipynb").write_text(
                json.dumps(_nb([_clean_meta()])), encoding="utf-8"
            )
            sub = root / "sub"
            sub.mkdir()
            (sub / "b.ipynb").write_text(
                json.dumps(_nb([_empty_meta()])), encoding="utf-8"
            )
            self.assertEqual(detector.scan_tree(root), [])

    def test_finds_defects_recursively(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "top.ipynb").write_text(
                json.dumps(_nb([_clean_meta(), _pending_meta()])), encoding="utf-8"
            )
            sub = root / "sub"
            sub.mkdir()
            (sub / "deep.ipynb").write_text(
                json.dumps(_nb([_failed_meta()])), encoding="utf-8"
            )
            defects = detector.scan_tree(root)
            self.assertEqual(len(defects), 2)
            # Paths are relative to root (forward- or back-slashes depending
            # on platform) and file order follows ``rglob`` lexicographic
            # order on the full absolute paths — assert by content, not
            # by position.
            file_to_cell = {d["file"]: d["cell_index"] for d in defects}
            self.assertEqual(
                {k.replace(chr(92), "/"): v for k, v in file_to_cell.items()},
                {"sub/deep.ipynb": 0, "top.ipynb": 1},
            )

    def test_skips_noise_directories(self):
        """``.git``, ``_archives``, ``__pycache__``, ``node_modules`` are skipped."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for noise in [".git", "_archives", "__pycache__", "node_modules"]:
                d = root / noise
                d.mkdir()
                (d / "hidden.ipynb").write_text(
                    json.dumps(_nb([_failed_meta()])), encoding="utf-8"
                )
            # One clean notebook to anchor the scan.
            (root / "anchor.ipynb").write_text(
                json.dumps(_nb([_clean_meta()])), encoding="utf-8"
            )
            self.assertEqual(detector.scan_tree(root), [])


# --- CLI tests ---


class TestMainCLI(unittest.TestCase):
    """``main`` returns the right exit codes and JSON shape."""

    def test_exit_0_when_clean(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "clean.ipynb").write_text(
                json.dumps(_nb([_clean_meta()])), encoding="utf-8"
            )
            rc = detector.main(["--scan-all", str(root)])
            self.assertEqual(rc, 0)

    def test_exit_1_when_defect_with_check(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "broken.ipynb").write_text(
                json.dumps(_nb([_pending_meta()])), encoding="utf-8"
            )
            rc = detector.main(["--scan-all", str(root), "--check"])
            self.assertEqual(rc, 1)

    def test_exit_2_when_path_missing(self):
        rc = detector.main(["--scan", "/does/not/exist.ipynb"])
        self.assertEqual(rc, 2)

    def test_summary_renders_kind_breakdown(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            nb = _nb([_pending_meta(), _failed_meta(), _tag_only_meta()])
            (root / "mix.ipynb").write_text(json.dumps(nb), encoding="utf-8")
            rc = detector.main(["--scan-all", str(root), "--summary"])
            self.assertEqual(rc, 0)

    def test_json_output_is_valid(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "x.ipynb").write_text(
                json.dumps(_nb([_failed_meta()])), encoding="utf-8"
            )
            rc = detector.main(["--scan-all", str(root)])
            self.assertEqual(rc, 0)
            # If --summary not passed, JSON is printed to stdout.
            # Re-run capturing stdout to validate shape.
            import io
            from contextlib import redirect_stdout
            buf = io.StringIO()
            with redirect_stdout(buf):
                detector.main(["--scan-all", str(root)])
            data = json.loads(buf.getvalue())
            self.assertEqual(len(data), 1)
            self.assertEqual(data[0]["kind"], "cell_papermill_hard_failure")
            self.assertEqual(data[0]["cell_index"], 0)
            # ``file`` is the absolute path the detector stamps; the
            # ``iter_notebooks`` rglob order on Windows puts absolute
            # paths on stdout. Check suffix, not exact string.
            self.assertTrue(data[0]["file"].endswith("x.ipynb"))

    def test_single_file_scan(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            path = root / "single.ipynb"
            path.write_text(json.dumps(_nb([_pending_meta()])), encoding="utf-8")
            rc = detector.main(["--scan", str(path), "--check"])
            self.assertEqual(rc, 1)

    def test_subprocess_invocation(self):
        """End-to-end: invoke the script as a subprocess, like CI would."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "z.ipynb").write_text(
                json.dumps(_nb([_failed_meta()])), encoding="utf-8"
            )
            script = Path(detector.__file__).resolve()
            proc = subprocess.run(
                [sys.executable, str(script), "--scan-all", str(root), "--check", "--summary"],
                capture_output=True,
                text=True,
            )
            self.assertEqual(proc.returncode, 1)
            self.assertIn("cell_papermill_hard_failure", proc.stderr)


if __name__ == "__main__":
    unittest.main()