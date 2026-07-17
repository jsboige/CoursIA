#!/usr/bin/env python3
"""Tests for ``detect_papermill_failed_state.py``.

Coverage:

- ``_classify_papermill_state`` — clean / hard failure (exception truthy)
  / pending status / both failure modes coexisting / missing metadata /
  malformed types.
- ``scan_notebook`` — unreadable notebook returns a structured defect,
  no papermill metadata returns no defect (manual execution is valid).
- ``scan_tree`` — recursive discovery skips ``.git``/``_archives``/etc,
  preserves a sorted order, and tags each defect with the file path
  relative to the scan root.
- CLI behaviour (``main``) — exit codes (0 clean, 1 defects, 2 usage),
  JSON output suppression under ``--check``, and summary rendering.

Run with::

    cd scripts/notebook_tools
    python -m pytest tests/test_detect_papermill_failed_state.py -v

or directly::

    python tests/test_detect_papermill_failed_state.py
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Allow running the test directly without installing the package.
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))

from detect_papermill_failed_state import (  # noqa: E402
    _classify_papermill_state,
    iter_notebooks,
    main as cli_main,
    scan_notebook,
    scan_tree,
)


def _make_nb(tmp: Path, name: str, nb: dict) -> Path:
    p = tmp / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _empty_nb() -> dict:
    return {
        "cells": [],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _clean_papermill_meta() -> dict:
    """Return a papermill metadata block corresponding to a successful run."""
    return {
        "exception": None,
        "start_time": "2026-07-17T19:00:00.000000+00:00",
        "end_time": "2026-07-17T19:00:08.578410+00:00",
        "duration": 8.57841,
        "parameters": {},
        "input_path": "MyNotebook.ipynb",
        "output_path": "MyNotebook.ipynb",
        "version": "2.7.0",
    }


# --- _classify_papermill_state ---


class ClassifyPapermillStateTests(unittest.TestCase):
    def test_clean_state_no_defect(self):
        self.assertEqual(_classify_papermill_state(_clean_papermill_meta()), [])

    def test_hard_failure_flagged(self):
        pm = _clean_papermill_meta()
        pm["exception"] = True
        defects = _classify_papermill_state(pm)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["kind"], "papermill_hard_failure")
        self.assertEqual(defects[0]["location"], "metadata.papermill.exception")
        self.assertEqual(defects[0]["severity"], "high")
        self.assertTrue(defects[0]["exception"])

    def test_pending_status_flagged(self):
        pm = _clean_papermill_meta()
        pm["status"] = "pending"
        # exception stays None → only soft failure
        defects = _classify_papermill_state(pm)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["kind"], "papermill_pending")
        self.assertEqual(defects[0]["severity"], "medium")

    def test_hard_failure_dominates_pending(self):
        # If both are present, the hard failure is reported and the
        # pending signal is suppressed (single defect entry per notebook).
        pm = _clean_papermill_meta()
        pm["exception"] = True
        pm["status"] = "pending"
        defects = _classify_papermill_state(pm)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["kind"], "papermill_hard_failure")

    def test_string_exception_treated_as_hard_failure(self):
        # Older papermill versions may record a string traceback in
        # ``exception`` rather than the boolean True. Treat any
        # non-None value as a hard failure.
        pm = _clean_papermill_meta()
        pm["exception"] = "ZeroDivisionError at cell 12"
        defects = _classify_papermill_state(pm)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["kind"], "papermill_hard_failure")

    def test_explicit_none_exception_with_completed_status_clean(self):
        # ``status == "completed"`` is a no-op signal: the canonical
        # clean state has status unset and exception None.
        pm = _clean_papermill_meta()
        pm["status"] = "completed"
        self.assertEqual(_classify_papermill_state(pm), [])

    def test_missing_metadata_no_crash(self):
        # No papermill block at all = the notebook was not run through
        # papermill. Not flagged (manual execution is valid).
        self.assertEqual(_classify_papermill_state({}), [])
        # Malformed type → no crash, no defect.
        self.assertEqual(_classify_papermill_state({"papermill": "x"}), [])


# --- scan_notebook ---


class ScanNotebookTests(unittest.TestCase):
    def test_clean_notebook_no_defect(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(
                Path(tmp), "clean.ipynb",
                {"metadata": {"papermill": _clean_papermill_meta()}, "cells": []},
            )
            self.assertEqual(scan_notebook(p), [])

    def test_notebook_without_papermill_no_defect(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(Path(tmp), "manual.ipynb", _empty_nb())
            self.assertEqual(scan_notebook(p), [])

    def test_hard_failure_defect(self):
        pm = _clean_papermill_meta()
        pm["exception"] = True
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(
                Path(tmp), "failed.ipynb",
                {"metadata": {"papermill": pm}, "cells": []},
            )
            defects = scan_notebook(p)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["kind"], "papermill_hard_failure")

    def test_unreadable_notebook_structured_defect(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "bad.ipynb"
            p.write_text("{ not valid json", encoding="utf-8")
            defects = scan_notebook(p)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["kind"], "unreadable_notebook")
            self.assertEqual(defects[0]["severity"], "high")


# --- iter_notebooks / scan_tree ---


class ScanTreeTests(unittest.TestCase):
    def test_iter_notebooks_skips_noise_dirs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "good").mkdir()
            (root / "good" / "a.ipynb").write_text("{}", encoding="utf-8")
            (root / ".git").mkdir()
            (root / ".git" / "b.ipynb").write_text("{}", encoding="utf-8")
            (root / "_archives").mkdir()
            (root / "_archives" / "c.ipynb").write_text("{}", encoding="utf-8")
            (root / "__pycache__").mkdir()
            (root / "__pycache__" / "d.ipynb").write_text("{}", encoding="utf-8")
            found = iter_notebooks(root)
            self.assertEqual([p.name for p in found], ["a.ipynb"])

    def test_iter_notebooks_sorted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("c.ipynb", "a.ipynb", "b.ipynb"):
                (root / name).write_text("{}", encoding="utf-8")
            found = iter_notebooks(root)
            self.assertEqual([p.name for p in found], ["a.ipynb", "b.ipynb", "c.ipynb"])

    def test_iter_notebooks_single_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            f = _make_nb(Path(tmp), "solo.ipynb", _empty_nb())
            self.assertEqual(iter_notebooks(f), [f])
            txt = Path(tmp) / "readme.txt"
            txt.write_text("hi", encoding="utf-8")
            self.assertEqual(iter_notebooks(txt), [])

    def test_scan_tree_tags_relative_file_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            nb_dir = root / "sub"
            nb_dir.mkdir()
            failed_pm = _clean_papermill_meta()
            failed_pm["exception"] = True
            _make_nb(
                nb_dir, "fail.ipynb",
                {"metadata": {"papermill": failed_pm}, "cells": []},
            )
            _make_nb(
                nb_dir, "clean.ipynb",
                {"metadata": {"papermill": _clean_papermill_meta()}, "cells": []},
            )
            _make_nb(nb_dir, "manual.ipynb", _empty_nb())
            report = scan_tree(root)
            files = sorted({d["file"] for d in report})
            self.assertEqual(files, [str(Path("sub") / "fail.ipynb")])
            self.assertEqual(report[0]["kind"], "papermill_hard_failure")

    def test_scan_tree_preserves_file_order(self):
        # When multiple notebooks fail, the order matches iter_notebooks
        # (sorted by path) so CI logs are reproducible.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            failed_pm = _clean_papermill_meta()
            failed_pm["exception"] = True
            for name in ("z_fail.ipynb", "a_fail.ipynb", "m_fail.ipynb"):
                _make_nb(
                    root, name,
                    {"metadata": {"papermill": failed_pm}, "cells": []},
                )
            report = scan_tree(root)
            files = [d["file"] for d in report]
            self.assertEqual(files, ["a_fail.ipynb", "m_fail.ipynb", "z_fail.ipynb"])


# --- CLI integration ---


class CliTests(unittest.TestCase):
    def _run(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable,
             str(_HERE.parent / "detect_papermill_failed_state.py"),
             *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )

    def test_scan_clean_exits_0(self):
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(
                Path(tmp), "clean.ipynb",
                {"metadata": {"papermill": _clean_papermill_meta()}, "cells": []},
            )
            cp = self._run("--scan", str(Path(tmp) / "clean.ipynb"))
            self.assertEqual(cp.returncode, 0)
            self.assertEqual(json.loads(cp.stdout), [])

    def test_scan_no_papermill_exits_0(self):
        # Manual notebook (no papermill metadata) is NOT a defect.
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(Path(tmp), "manual.ipynb", _empty_nb())
            cp = self._run("--scan", str(p))
            self.assertEqual(cp.returncode, 0)
            self.assertEqual(json.loads(cp.stdout), [])

    def test_scan_failure_exits_0_with_json(self):
        # JSON output mode: report on stdout, exit 0 (defects don't
        # trigger a non-zero exit unless ``--check`` is passed).
        failed_pm = _clean_papermill_meta()
        failed_pm["exception"] = True
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(
                Path(tmp), "fail.ipynb",
                {"metadata": {"papermill": failed_pm}, "cells": []},
            )
            cp = self._run("--scan", str(p))
            self.assertEqual(cp.returncode, 0)
            report = json.loads(cp.stdout)
            self.assertEqual(len(report), 1)
            self.assertEqual(report[0]["kind"], "papermill_hard_failure")

    def test_check_clean_exits_0(self):
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(
                Path(tmp), "clean.ipynb",
                {"metadata": {"papermill": _clean_papermill_meta()}, "cells": []},
            )
            cp = self._run("--scan-all", tmp, "--check")
            self.assertEqual(cp.returncode, 0)
            self.assertEqual(cp.stdout.strip(), "")

    def test_check_defects_exits_1(self):
        failed_pm = _clean_papermill_meta()
        failed_pm["exception"] = True
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(
                Path(tmp), "fail.ipynb",
                {"metadata": {"papermill": failed_pm}, "cells": []},
            )
            cp = self._run("--scan-all", tmp, "--check")
            self.assertEqual(cp.returncode, 1)

    def test_check_with_summary_keeps_human_output(self):
        failed_pm = _clean_papermill_meta()
        failed_pm["exception"] = True
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(
                Path(tmp), "fail.ipynb",
                {"metadata": {"papermill": failed_pm}, "cells": []},
            )
            cp = self._run(
                "--scan-all", tmp, "--check", "--summary",
            )
            self.assertEqual(cp.returncode, 1)
            self.assertIn("papermill_hard_failure", cp.stderr)

    def test_pending_reported_as_pending(self):
        pm = _clean_papermill_meta()
        pm["status"] = "pending"
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(
                Path(tmp), "pending.ipynb",
                {"metadata": {"papermill": pm}, "cells": []},
            )
            cp = self._run("--scan", str(p))
            self.assertEqual(cp.returncode, 0)
            report = json.loads(cp.stdout)
            self.assertEqual(len(report), 1)
            self.assertEqual(report[0]["kind"], "papermill_pending")
            self.assertEqual(report[0]["severity"], "medium")

    def test_missing_path_exits_2(self):
        cp = self._run("--scan", "/nonexistent/path.ipynb")
        self.assertEqual(cp.returncode, 2)

    def test_cli_main_handles_clean_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(
                Path(tmp), "clean.ipynb",
                {"metadata": {"papermill": _clean_papermill_meta()}, "cells": []},
            )
            rc = cli_main(["--scan-all", tmp])
            self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()