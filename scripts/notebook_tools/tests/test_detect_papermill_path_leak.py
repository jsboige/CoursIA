#!/usr/bin/env python3
"""Tests for ``detect_papermill_path_leak.py``.

Coverage:

- ``_is_absolute`` — positive (Windows drive, POSIX root, UNC) and negative
  (basename, empty string, non-string) cases.
- ``_scan_metadata_papermill`` — absolute path in ``output_path`` /
  ``input_path`` is flagged, relative basenames are clean, missing /
  malformed metadata is tolerated.
- ``_scan_output_text`` — class B leak patterns across ``stream.text``,
  ``data['text/plain']`` (str and list), and the skip rules (HTML / image
  data ignored).
- ``scan_notebook`` — unreadable notebooks are reported with a structured
  defect, never raised as exceptions.
- ``scan_tree`` — recursive discovery skips ``.git``/``_archives``/etc,
  preserves a sorted order, and tags each defect with the file path
  relative to the scan root.
- CLI behaviour (``main``) — exit codes (0 clean, 1 defects, 2 usage),
  JSON output suppression under ``--check``, and summary rendering.

Run with::

    cd scripts/notebook_tools
    python -m pytest tests/test_detect_papermill_path_leak.py -v

or directly::

    python tests/test_detect_papermill_path_leak.py
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from textwrap import dedent

# Allow running the test directly without installing the package.
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))

from detect_papermill_path_leak import (  # noqa: E402
    ABS_PATH_RE,
    LEAK_PATTERNS,
    _is_absolute,
    _scan_metadata_papermill,
    _scan_output_text,
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


# --- _is_absolute ---


class IsAbsoluteTests(unittest.TestCase):
    def test_windows_drive_backslash(self):
        self.assertTrue(_is_absolute(r"C:\Users\jsboi\AppData\Local\Temp\x.ipynb"))

    def test_windows_drive_forward_slash(self):
        self.assertTrue(_is_absolute("D:/tmp/x.ipynb"))

    def test_posix_root_home(self):
        self.assertTrue(_is_absolute("/home/jesse/x.ipynb"))

    def test_posix_root_users_macos(self):
        self.assertTrue(_is_absolute("/Users/jsboige/x.ipynb"))

    def test_unc_path(self):
        self.assertTrue(_is_absolute(r"\\server\share\x.ipynb"))

    def test_relative_basename_is_not_absolute(self):
        self.assertFalse(_is_absolute("MyNotebook.ipynb"))

    def test_relative_subdir_is_not_absolute(self):
        self.assertFalse(_is_absolute("notebooks/MyNotebook.ipynb"))

    def test_empty_string_is_not_absolute(self):
        self.assertFalse(_is_absolute(""))

    def test_none_is_not_absolute(self):
        self.assertFalse(_is_absolute(None))

    def test_int_is_not_absolute(self):
        self.assertFalse(_is_absolute(42))


# --- _scan_metadata_papermill ---


class ScanMetadataPapermillTests(unittest.TestCase):
    def test_clean_relative_paths(self):
        nb = {
            "metadata": {
                "papermill": {
                    "input_path": "MyNotebook.ipynb",
                    "output_path": "MyNotebook.ipynb",
                }
            }
        }
        self.assertEqual(_scan_metadata_papermill(nb), [])

    def test_absolute_output_path_flagged(self):
        nb = {
            "metadata": {
                "papermill": {
                    "input_path": "MyNotebook.ipynb",
                    "output_path": r"C:\Users\jsboi\AppData\Local\Temp\MyNotebook.ipynb",
                }
            }
        }
        defects = _scan_metadata_papermill(nb)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["kind"], "metadata_papermill_absolute")
        self.assertEqual(defects[0]["location"], "metadata.papermill.output_path")
        self.assertEqual(defects[0]["severity"], "high")

    def test_absolute_input_path_flagged(self):
        nb = {
            "metadata": {
                "papermill": {"input_path": "/home/jesse/MyNotebook.ipynb"}
            }
        }
        defects = _scan_metadata_papermill(nb)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["location"], "metadata.papermill.input_path")

    def test_both_paths_flagged(self):
        nb = {
            "metadata": {
                "papermill": {
                    "input_path": "C:/in.ipynb",
                    "output_path": "D:/out.ipynb",
                }
            }
        }
        defects = _scan_metadata_papermill(nb)
        self.assertEqual(len(defects), 2)

    def test_missing_metadata_no_crash(self):
        self.assertEqual(_scan_metadata_papermill({}), [])
        self.assertEqual(_scan_metadata_papermill({"metadata": {}}), [])
        self.assertEqual(_scan_metadata_papermill({"metadata": {"papermill": None}}), [])

    def test_malformed_papermill_dict_no_crash(self):
        # Even if ``papermill`` is the wrong type, we must not crash.
        self.assertEqual(_scan_metadata_papermill({"metadata": {"papermill": "x"}}), [])


# --- _scan_output_text ---


class ScanOutputTextTests(unittest.TestCase):
    def test_clean_outputs_no_leak(self):
        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "outputs": [
                        {"output_type": "stream", "name": "stdout", "text": "hello\n"},
                        {
                            "output_type": "display_data",
                            "data": {"text/plain": "42"},
                        },
                    ],
                }
            ]
        }
        self.assertEqual(_scan_output_text(nb), [])

    def test_stream_text_windows_user_profile_flagged(self):
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "stream",
                            "name": "stderr",
                            "text": (
                                'UserWarning: figure layout changed at '
                                r'C:\Users\jsboi\AppData\Local\Temp\ipykernel_1234\foo.py:42'
                            ),
                        }
                    ]
                }
            ]
        }
        defects = _scan_output_text(nb)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["kind"], "output_text_path_leak")
        self.assertIn("cells[0].outputs[0].stream.text", defects[0]["location"])
        self.assertIn(r"C:\Users\jsboi", defects[0]["match"])

    def test_text_plain_str_flagged(self):
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "execute_result",
                            "data": {
                                "text/plain": "loaded /home/jesse/.nuget/packages/x.dll",
                            },
                        }
                    ]
                }
            ]
        }
        defects = _scan_output_text(nb)
        self.assertEqual(len(defects), 1)
        self.assertEqual(defects[0]["match"], "/home/jesse/.nuget/packages/x.dll")

    def test_text_plain_list_flagged(self):
        # nbformat wraps long stream stdout text as ``list[str]``. The
        # detector must walk each piece independently.
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "stream",
                            "name": "stdout",
                            "text": ["", "starting run in C:/Users/jsboi/repo\n"],
                        }
                    ]
                }
            ]
        }
        defects = _scan_output_text(nb)
        self.assertEqual(len(defects), 1)
        self.assertIn("stream.text[1]", defects[0]["location"])
        self.assertEqual(
            defects[0]["match"], "C:/Users/jsboi/repo",
        )

    def test_data_text_plain_list_flagged(self):
        # When ``data['text/plain']`` is itself a list (multi-line
        # ``execute_result``), each element is scanned independently and
        # reported with its index in the location string.
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "execute_result",
                            "data": {
                                "text/plain": [
                                    "",
                                    "result: 42 at /home/jesse/run.py",
                                ],
                            },
                        }
                    ]
                }
            ]
        }
        defects = _scan_output_text(nb)
        self.assertEqual(len(defects), 1)
        self.assertIn("data['text/plain'][1]", defects[0]["location"])
        self.assertEqual(
            defects[0]["match"], "/home/jesse/run.py",
        )

    def test_html_and_image_outputs_ignored(self):
        # Binary / structured data must NOT be scanned as text.
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "display_data",
                            "data": {
                                "text/html": "<p>C:\\Users\\jsboi\\index.html</p>",
                                "image/png": b"\x89PNG\r\n\x1a\n C:\\Users\\jsboi\\fake",
                            },
                        }
                    ]
                }
            ]
        }
        self.assertEqual(_scan_output_text(nb), [])

    def test_no_outputs_no_crash(self):
        self.assertEqual(_scan_output_text({"cells": []}), [])
        self.assertEqual(_scan_output_text({"cells": [{"outputs": []}]}), [])

    def test_multiple_leaks_in_one_cell(self):
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "stream",
                            "name": "stderr",
                            "text": (
                                r"failed at C:\Users\jsboi\file.py\n"
                                r"also /home/jesse/other.py\n"
                            ),
                        }
                    ]
                }
            ]
        }
        defects = _scan_output_text(nb)
        # Both leaks in the same string are reported.
        self.assertGreaterEqual(len(defects), 2)


# --- scan_notebook ---


class ScanNotebookTests(unittest.TestCase):
    def test_clean_notebook(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(Path(tmp), "clean.ipynb", _empty_nb())
            self.assertEqual(scan_notebook(p), [])

    def test_unreadable_notebook_returns_structured_defect(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "bad.ipynb"
            p.write_text("{ this is not json", encoding="utf-8")
            defects = scan_notebook(p)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["kind"], "unreadable_notebook")
            self.assertEqual(defects[0]["severity"], "high")

    def test_outputs_flagged_when_enabled(self):
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "stream",
                            "name": "stderr",
                            "text": r"warn: C:\Users\jsboi\.nuget\packages",
                        }
                    ]
                }
            ]
        }
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(Path(tmp), "leaky.ipynb", nb)
            self.assertEqual(scan_notebook(p), [])  # default off
            self.assertEqual(len(scan_notebook(p, include_outputs=True)), 1)

    def test_metadata_defect_always_included(self):
        nb = {
            "metadata": {"papermill": {"output_path": "/tmp/x.ipynb"}},
            "cells": [],
        }
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(Path(tmp), "leaky.ipynb", nb)
            self.assertEqual(len(scan_notebook(p)), 1)
            self.assertEqual(len(scan_notebook(p, include_outputs=True)), 1)


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
            # Non-ipynb file: empty list.
            txt = Path(tmp) / "readme.txt"
            txt.write_text("hi", encoding="utf-8")
            self.assertEqual(iter_notebooks(txt), [])

    def test_scan_tree_tags_relative_file_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            nb_dir = root / "sub"
            nb_dir.mkdir()
            nb = {
                "metadata": {"papermill": {"output_path": "/tmp/x.ipynb"}},
                "cells": [],
            }
            _make_nb(nb_dir, "leak.ipynb", nb)
            _make_nb(nb_dir, "clean.ipynb", _empty_nb())
            report = scan_tree(root)
            files = sorted({d["file"] for d in report})
            self.assertEqual(files, [str(Path("sub") / "leak.ipynb")])
            self.assertEqual(report[0]["kind"], "metadata_papermill_absolute")


# --- CLI integration ---


class CliTests(unittest.TestCase):
    def _run(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable,
             str(_HERE.parent / "detect_papermill_path_leak.py"),
             *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )

    def test_scan_clean_exits_0(self):
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(Path(tmp), "clean.ipynb", _empty_nb())
            cp = self._run("--scan", str(Path(tmp) / "clean.ipynb"))
            self.assertEqual(cp.returncode, 0)
            report = json.loads(cp.stdout)
            self.assertEqual(report, [])

    def test_scan_defects_exits_0_with_json(self):
        nb = {
            "metadata": {"papermill": {"output_path": "/tmp/x.ipynb"}},
            "cells": [],
        }
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(Path(tmp), "leak.ipynb", nb)
            cp = self._run("--scan", str(p))
            self.assertEqual(cp.returncode, 0)
            report = json.loads(cp.stdout)
            self.assertEqual(len(report), 1)

    def test_check_clean_exits_0(self):
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(Path(tmp), "clean.ipynb", _empty_nb())
            cp = self._run("--scan-all", tmp, "--check")
            self.assertEqual(cp.returncode, 0)
            # --check suppresses JSON on stdout
            self.assertEqual(cp.stdout.strip(), "")

    def test_check_defects_exits_1(self):
        nb = {
            "metadata": {"papermill": {"output_path": "/tmp/x.ipynb"}},
            "cells": [],
        }
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(Path(tmp), "leak.ipynb", nb)
            cp = self._run("--scan-all", tmp, "--check")
            self.assertEqual(cp.returncode, 1)

    def test_check_with_summary_keeps_human_output(self):
        nb = {
            "metadata": {"papermill": {"output_path": "/tmp/x.ipynb"}},
            "cells": [],
        }
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(Path(tmp), "leak.ipynb", nb)
            cp = self._run(
                "--scan-all", tmp, "--check", "--summary",
            )
            self.assertEqual(cp.returncode, 1)
            self.assertIn("metadata_papermill_absolute", cp.stderr)

    def test_missing_path_exits_2(self):
        cp = self._run("--scan", "/nonexistent/path.ipynb")
        self.assertEqual(cp.returncode, 2)

    def test_scan_all_default_cwd(self):
        cp = self._run("--scan-all")
        # Either clean (0) or defects (0 with JSON); never crash.
        self.assertIn(cp.returncode, (0, 1))

    def test_outputs_flag_passed_through(self):
        nb = {
            "cells": [
                {
                    "outputs": [
                        {
                            "output_type": "stream",
                            "name": "stderr",
                            "text": r"C:\Users\jsboi\.nuget\packages\foo",
                        }
                    ]
                }
            ]
        }
        with tempfile.TemporaryDirectory() as tmp:
            p = _make_nb(Path(tmp), "leak.ipynb", nb)
            # Without --outputs: clean (0 defects).
            cp = self._run("--scan", str(p))
            self.assertEqual(cp.returncode, 0)
            # With --outputs: defect found.
            cp = self._run("--scan", str(p), "--outputs")
            self.assertEqual(cp.returncode, 0)
            report = json.loads(cp.stdout)
            self.assertEqual(len(report), 1)
            self.assertEqual(report[0]["kind"], "output_text_path_leak")


# --- Module-level invariants ---


class ModuleInvariantsTests(unittest.TestCase):
    def test_abs_path_re_matches_known_cases(self):
        self.assertTrue(ABS_PATH_RE.match(r"C:\foo"))
        self.assertTrue(ABS_PATH_RE.match("D:/foo"))
        self.assertTrue(ABS_PATH_RE.match("/foo"))
        self.assertTrue(ABS_PATH_RE.match(r"\\server\share\foo"))
        self.assertFalse(ABS_PATH_RE.match("foo.ipynb"))
        self.assertFalse(ABS_PATH_RE.match(""))

    def test_leak_patterns_compile(self):
        # The module exposes at least the documented leak patterns.
        kinds = {p.pattern[:10] for p in LEAK_PATTERNS}
        self.assertGreaterEqual(len(LEAK_PATTERNS), 5)

    def test_cli_main_handles_clean_run(self):
        # Direct call into the CLI main() with synthetic argv; should
        # never raise on a clean temp tree.
        with tempfile.TemporaryDirectory() as tmp:
            _make_nb(Path(tmp), "clean.ipynb", _empty_nb())
            rc = cli_main(["--scan-all", tmp])
            self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()