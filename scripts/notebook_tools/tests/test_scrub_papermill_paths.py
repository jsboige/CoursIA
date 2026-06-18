"""Tests for scripts/notebook_tools/scrub_papermill_paths.py

Covers: absolute path detection (Windows drive + POSIX), the basename
replacement, byte-identical preservation of everything else via the
text-level surgical edit, ambiguous/duplicate-value skip, and the
no-papermill / relative-only clean cases.
"""

import json
import sys
from pathlib import Path

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

from scrub_papermill_paths import (
    ABS_PATH_RE,
    find_papermill_defects,
    is_absolute,
    scrub_notebook,
)


def _write_nb(path: Path, pm: dict | None, extra_metadata: dict | None = None) -> Path:
    nb = {
        "cells": [],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    if pm is not None:
        nb["metadata"]["papermill"] = pm
    if extra_metadata:
        nb["metadata"].update(extra_metadata)
    # Use indent=1 to mirror the committed-notebook canonical format.
    path.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    return path


def test_is_absolute_detects_windows_and_posix():
    assert is_absolute("C:/Users/jsboi/Temp/x.ipynb")
    assert is_absolute("D:\\tmp\\x.ipynb")
    assert is_absolute("/tmp/x.ipynb")
    assert not is_absolute("x.ipynb")
    assert not is_absolute("dir/x.ipynb")
    assert not is_absolute(None)
    assert not is_absolute(123)


def test_find_defects_none_when_no_papermill(tmp_path):
    p = _write_nb(tmp_path / "nb.ipynb", pm=None)
    assert find_papermill_defects(str(p)) == []


def test_find_defects_none_when_relative(tmp_path):
    p = _write_nb(tmp_path / "nb.ipynb", pm={"output_path": "nb.ipynb"})
    assert find_papermill_defects(str(p)) == []


def test_find_defects_flags_absolute_output_and_input(tmp_path):
    p = _write_nb(tmp_path / "nb.ipynb", pm={
        "output_path": "C:/Users/jsboi/AppData/Local/Temp/nb_out.ipynb",
        "input_path": "C:/dev/repo/nb.ipynb",
        "version": "2.6.0",
    })
    defects = find_papermill_defects(str(p))
    keys = [k for k, _ in defects]
    assert keys == ["output_path", "input_path"]


def test_scrub_replaces_absolute_with_basename_and_preserves_rest(tmp_path):
    p = tmp_path / "SC-1-Setup-Foundry.ipynb"
    pm = {
        "output_path": "C:/Users/jsboi/AppData/Local/Temp/sc1_output.ipynb",
        "input_path": "MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations/SC-1-Setup-Foundry.ipynb",
        "duration": 2.305612,
        "version": "2.6.0",
        "exception": None,
    }
    _write_nb(p, pm=pm)
    before = p.read_text(encoding="utf-8")

    defects, fixed = scrub_notebook(str(p), apply=True)
    assert len(fixed) == 1  # only output_path was absolute
    assert fixed[0][0] == "output_path"

    after = p.read_text(encoding="utf-8")
    nb = json.loads(after)
    assert nb["metadata"]["papermill"]["output_path"] == "SC-1-Setup-Foundry.ipynb"
    # input_path was already relative -> untouched
    assert nb["metadata"]["papermill"]["input_path"] == pm["input_path"]
    # duration preserved exactly (no float coercion)
    assert nb["metadata"]["papermill"]["duration"] == 2.305612
    assert nb["metadata"]["papermill"]["version"] == "2.6.0"
    # Everything outside the output_path substring is byte-identical.
    assert before.replace(
        "C:/Users/jsboi/AppData/Local/Temp/sc1_output.ipynb",
        "SC-1-Setup-Foundry.ipynb",
    ) == after


def test_scrub_handles_backslash_paths(tmp_path):
    p = tmp_path / "nb.ipynb"
    _write_nb(p, pm={"output_path": "D:\\tmp\\nb_out.ipynb"})
    defects, fixed = scrub_notebook(str(p), apply=True)
    assert len(fixed) == 1
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["papermill"]["output_path"] == "nb.ipynb"


def test_scrub_handles_nonascii_path_stored_literally(tmp_path):
    """Non-ASCII char stored literally (ensure_ascii=False) must be scrubbed.

    Regression: the previous single-needle form built the needle with
    json.dumps default (ensure_ascii=True), escaping the accent to \\uXXXX,
    which never matched the literal accent on disk -> silent skip.
    """
    name = "Exploration_informée_intro.ipynb"
    p = tmp_path / name
    nb = {
        "cells": [],
        "metadata": {"papermill": {
            "output_path": "D:\\dev\\CoursIA\\Exploration_informée_intro_output.ipynb",
            "input_path": "D:\\dev\\CoursIA\\Exploration_informée_intro.ipynb",
        }},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    # ensure_ascii=False -> the accent is written literally to disk.
    p.write_text(json.dumps(nb, indent=1, ensure_ascii=False), encoding="utf-8")

    defects, fixed = scrub_notebook(str(p), apply=True)
    assert len(fixed) == 2
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["papermill"]["output_path"] == name
    assert after["metadata"]["papermill"]["input_path"] == name


def test_scrub_handles_nonascii_path_stored_escaped(tmp_path):
    """Non-ASCII char stored escaped (\\uXXXX, ensure_ascii=True) must scrub too."""
    name = "Exploration_informée_intro.ipynb"
    p = tmp_path / name
    nb = {
        "cells": [],
        "metadata": {"papermill": {
            "output_path": "D:\\dev\\CoursIA\\Exploration_informée_intro_output.ipynb",
        }},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    # ensure_ascii=True (default) -> the accent is written as \uXXXX on disk.
    p.write_text(json.dumps(nb, indent=1, ensure_ascii=True), encoding="utf-8")
    assert "\\u00e9" in p.read_text(encoding="utf-8")  # confirm escaped on disk

    defects, fixed = scrub_notebook(str(p), apply=True)
    assert len(fixed) == 1
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["papermill"]["output_path"] == name


def test_scrub_dry_run_does_not_write(tmp_path):
    p = tmp_path / "nb.ipynb"
    _write_nb(p, pm={"output_path": "/tmp/nb_out.ipynb"})
    before = p.read_text(encoding="utf-8")
    defects, fixed = scrub_notebook(str(p), apply=False)
    assert len(defects) == 1
    assert len(fixed) == 1  # would-fix reported even in dry-run
    # but the file is untouched in dry-run
    assert p.read_text(encoding="utf-8") == before


def test_scrub_skips_ambiguous_duplicate(tmp_path):
    """If the same key:value needle appears twice the edit is ambiguous -> skip."""
    p = tmp_path / "nb.ipynb"
    # Raw text with the SAME output_path key:value literally twice (invalid
    # JSON, but exercises the count>1 guard on malformed content).
    raw = (
        '{\n "cells": [],\n '
        '"metadata": {\n  "papermill": {\n'
        '   "output_path": "C:/tmp/x.ipynb",\n'
        '   "output_path": "C:/tmp/x.ipynb"\n  }\n },\n'
        ' "nbformat": 4\n}\n'
    )
    p.write_text(raw, encoding="utf-8")
    defects, fixed = scrub_notebook(str(p), apply=True)
    # needle count > 1 -> skipped, file untouched
    assert fixed == []
    assert p.read_text(encoding="utf-8") == raw


def test_scrub_clean_notebook_is_noop(tmp_path):
    p = _write_nb(tmp_path / "nb.ipynb", pm={"output_path": "nb.ipynb"})
    before = p.read_text(encoding="utf-8")
    defects, fixed = scrub_notebook(str(p), apply=True)
    assert defects == []
    assert fixed == []
    assert p.read_text(encoding="utf-8") == before


def test_abs_path_regex():
    assert ABS_PATH_RE.match("C:/x")
    assert ABS_PATH_RE.match("Z:\\x")
    assert ABS_PATH_RE.match("/x")
    assert not ABS_PATH_RE.match("x.ipynb")
    assert not ABS_PATH_RE.match("a/b.ipynb")
