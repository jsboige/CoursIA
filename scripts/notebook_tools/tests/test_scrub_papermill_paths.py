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
    find_output_path_defects,
    is_absolute,
    scrub_notebook,
    scrub_output_paths,
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


# ---------------------------------------------------------------------------
# --outputs mode: machine-local paths inside output text
# ---------------------------------------------------------------------------

def _write_nb_with_output(path, source_line, output_text):
    """Write a 1-cell notebook whose stdout output contains `output_text`."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "source": [source_line],
                "outputs": [
                    {"output_type": "stream", "name": "stdout", "text": [output_text]}
                ],
                "execution_count": 1,
                "metadata": {},
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, indent=1, ensure_ascii=False), encoding="utf-8")
    return path


def test_find_output_defects_none_for_clean(tmp_path):
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "print('hi')", "hi\n")
    assert find_output_path_defects(str(p)) == 0


def test_find_output_defects_counts_home_leak(tmp_path):
    p = _write_nb_with_output(
        tmp_path / "nb.ipynb",
        "import ortools",
        "Requirement already satisfied: ortools in "
        "C:\\Users\\jsboi\\AppData\\Local\\Packages\\PythonSoftwareFoundation.Python.3.13\n",
    )
    assert find_output_path_defects(str(p)) == 1


def test_scrub_outputs_anonymizes_home_and_preserves_rest(tmp_path):
    raw = (
        "Requirement already satisfied: ortools in "
        "C:\\Users\\jsboi\\AppData\\Local\\Packages\\site-packages (9.15.6755)\n"
    )
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "import ortools", raw)
    before = p.read_text(encoding="utf-8")

    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1
    assert fixed >= 1

    after = p.read_text(encoding="utf-8")
    # home root anonymized
    assert "C:\\\\Users\\\\jsboi" not in after
    assert "~" in after
    # rest of path preserved (package version + site-packages)
    assert "site-packages" in after
    assert "9.15.6755" in after
    # source cell byte-identical
    nb_after = json.loads(after)
    assert nb_after["cells"][0]["source"] == ["import ortools"]
    # the ONLY change is the home-root substring -> ~
    assert before.replace("C:\\\\Users\\\\jsboi", "~") == after


def test_scrub_outputs_anonymizes_ipykernel_pid(tmp_path):
    raw = (
        "C:\\Users\\jsboi\\AppData\\Local\\Temp\\ipykernel_85268\\3959998143.py:74: "
        "UserWarning: figure\n"
    )
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "plt.plot()", raw)

    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1
    after = p.read_text(encoding="utf-8")
    # home + ipykernel PID anonymized
    assert "C:\\\\Users\\\\jsboi" not in after
    assert "ipykernel_<pid>" in after
    # cell hash + warning message preserved (diagnostic value)
    assert "3959998143.py:74" in after
    assert "UserWarning" in after


def test_scrub_outputs_dry_run_does_not_write(tmp_path):
    raw = "Loading from C:\\Users\\jsboi\\.nuget\\packages\\plotly.net.interactive\\3.0.2\n"
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "load()", raw)
    before = p.read_text(encoding="utf-8")

    found, fixed = scrub_output_paths(str(p), apply=False)
    assert found == 1
    assert fixed >= 1  # would-fix reported
    assert p.read_text(encoding="utf-8") == before  # file untouched in dry-run


def test_scrub_outputs_clean_notebook_is_noop(tmp_path):
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "print('ok')", "ok\n")
    before = p.read_text(encoding="utf-8")
    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 0
    assert fixed == 0
    assert p.read_text(encoding="utf-8") == before


def test_scrub_outputs_does_not_touch_relative_paths(tmp_path):
    # A relative-looking path with no home root must NOT be altered.
    raw = "loading module from ./local/relative/path/module.py\n"
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "load()", raw)
    before = p.read_text(encoding="utf-8")
    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 0
    assert fixed == 0
    assert p.read_text(encoding="utf-8") == before


def test_scrub_outputs_handles_repr_escaped_double_backslash(tmp_path):
    """A home path repr-escaped inside a Python exception must be scrubbed.

    Regression: archive Fast-Downward-Legacy (#3891). Python formats the path
    inside FileNotFoundError/PermissionError via repr(), so each separator is
    TWO literal backslashes ('C:\\\\Users\\\\jsboi' in the actual output text).
    The home regex previously required exactly one separator and missed these,
    so the final exception line stayed leaked while traceback frames scrubbed.
    """
    raw = (
        "FileNotFoundError: [Errno 2] No such file or directory: "
        "'C:\\\\Users\\\\jsboi\\\\.local\\\\fast-downward\\\\release\\\\domain.pddl'\n"
    )
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "open('x')", raw)
    before = p.read_text(encoding="utf-8")

    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1
    assert fixed >= 1
    after = p.read_text(encoding="utf-8")
    # machine-local home root gone even with doubled backslashes
    assert "jsboi" not in after
    assert "~" in after
    # repo-relative tail preserved (diagnostic value)
    assert "fast-downward" in after
    assert "domain.pddl" in after
    # source cell byte-identical
    assert json.loads(after)["cells"][0]["source"] == ["open('x')"]


def test_scrub_outputs_handles_mixed_single_and_repr_escaped_home(tmp_path):
    """A single output mixing single-backslash (traceback frame) and repr-doubled
    (exception line) home paths must scrub BOTH with no collision.

    Regression: archive #3891, where traceback frames scrubbed but the final
    FileNotFoundError line did not. The two forms produce distinct on-disk
    backslash counts (2 vs 4) so neither needle substitutes for the other.
    """
    raw = (
        '  File "C:\\Users\\jsboi\\.local\\app\\driver.py", line 14, in main\n'
        "FileNotFoundError: [Errno 2] No such file: 'C:\\\\Users\\\\jsboi\\\\.local\\\\app\\\\data.pddl'\n"
    )
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "run()", raw)
    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1  # one leaked output blob
    after = p.read_text(encoding="utf-8")
    # BOTH forms scrubbed: the username appears nowhere
    assert "jsboi" not in after
    assert "~" in after


def test_scrub_outputs_anonymizes_checkout_root(tmp_path):
    """A checkout-root path (repo clone location, NOT under Users/home) -> <repo>.

    Regression: #3892. The leak 'D:\\dev\\CoursIA-2\\Tweety\\libs' is a
    machine-local checkout path that the home regexes (Users/home) never match,
    so it needs its own pattern (the repo dir name CoursIA as a segment).
    """
    raw = "Classpath charge depuis : D:\\dev\\CoursIA-2\\Tweety\\libs\n"
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "load()", raw)
    before = p.read_text(encoding="utf-8")

    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1
    assert fixed >= 1
    after = p.read_text(encoding="utf-8")
    assert "<repo>" in after
    # the machine-local drive path is gone
    assert "D:\\\\dev" not in after
    assert "CoursIA-2" not in after
    # the repo-relative tail is preserved
    assert "Tweety" in after
    assert "libs" in after
    # source cell byte-identical
    assert json.loads(after)["cells"][0]["source"] == ["load()"]


def test_scrub_outputs_preserves_file_url_scheme(tmp_path):
    """A file:/// URL entering the repo checkout keeps its scheme.

    Regression: SW-8 (#3899). _REPO_RES matched the 'e:' inside 'file:' (the 'e'
    preceded by 'l'), consuming 'e:///D:/dev/CoursIA/' and mangling the URL into
    '<fil<repo>...>'. The negative lookbehind (?<![a-zA-Z]) blocks that: only the
    real 'D:' (preceded by '/') matches, so the scheme survives and just the
    checkout-root path is anonymized.
    """
    raw = (
        "<file:///D:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/"
        "data/not-an-email>\n"
    )
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "open(...)", raw)

    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1
    assert fixed >= 1
    after = p.read_text(encoding="utf-8")
    # scheme preserved, checkout-root anonymized
    assert "<file:///<repo>" in after
    # the critical mangle must NOT happen
    assert "<fil<repo>" not in after
    assert "file" in after  # 'file' scheme word still present
    # the machine-local drive path into the repo is gone
    assert "D:/dev/CoursIA" not in after
    # repo-relative tail preserved
    assert "not-an-email" in after
    assert "SemanticWeb" in after
    # source cell byte-identical
    assert json.loads(after)["cells"][0]["source"] == ["open(...)"]


def test_scrub_outputs_posix_checkout_root(tmp_path):
    """A WSL /mnt/<drive>/.../CoursIA(-2)/ checkout path -> <repo>.

    Regression: Lean-13/15b/16a. The Windows _REPO_RES never matches a POSIX
    path (no drive letter), so the WSL view of the project leaked while the
    Windows view was scrubbed. POSIX checkout paths are the same defect class
    (machine-local clone location), just the Linux representation that
    WSL-executed Lean/Python notebooks print alongside the Windows path.
    """
    raw = (
        "Projet Lean (WSL) : /mnt/c/dev/CoursIA-2/MyIA.AI.Notebooks/"
        "SymbolicAI/Lean/conway_lean\n"
    )
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "setup()", raw)
    before = p.read_text(encoding="utf-8")

    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1
    assert fixed >= 1
    after = p.read_text(encoding="utf-8")
    out_text = "".join(json.loads(after)["cells"][0]["outputs"][0]["text"])
    # the machine-local WSL clone path is anonymized
    assert out_text.count("<repo>") == 1
    assert "/mnt/c/dev/CoursIA-2" not in out_text
    # the label + repo-relative tail survive
    assert "Projet Lean (WSL)" in out_text
    assert "SymbolicAI/Lean/conway_lean" in out_text
    # source cell byte-identical
    assert json.loads(after)["cells"][0]["source"] == ["setup()"]


def test_scrub_outputs_repo_regex_does_not_span_newlines(tmp_path):
    """A Windows checkout path and a POSIX checkout path on consecutive lines
    are scrubbed INDEPENDENTLY; the _REPO_RES char class must not accept newlines
    and so capture both paths (plus the label prose between) as one giant needle.

    Regression: Lean-13/15b/16a. The old char class [^\\/...]+ accepted newlines,
    so 'C:\\dev\\CoursIA-2\\...\\mod\\nWSL: /mnt/c/dev/CoursIA-2/.../mod' matched
    as ONE needle reaching the SECOND CoursIA across the newline. That needle
    never matched the raw on-disk JSON (real newline vs 2-char '\\n' escape) ->
    0 fixed, leak left in place AND, if it ever did match, it would delete the
    label prose between the two paths. With the newline exclusion both checkout
    roots are scrubbed independently and the labels survive.
    """
    raw = (
        "Windows: C:\\dev\\CoursIA-2\\proj\\mod\n"
        "WSL: /mnt/c/dev/CoursIA-2/proj/mod\n"
    )
    p = _write_nb_with_output(tmp_path / "nb.ipynb", "show()", raw)

    found, fixed = scrub_output_paths(str(p), apply=True)
    assert found == 1
    after = p.read_text(encoding="utf-8")
    out_text = "".join(json.loads(after)["cells"][0]["outputs"][0]["text"])
    # BOTH checkout roots anonymized (one <repo> per line), username-free
    assert out_text.count("<repo>") == 2
    assert "CoursIA" not in out_text
    # the two labels survived (not eaten by a greedy multi-line match)
    assert "Windows:" in out_text
    assert "WSL:" in out_text
    # repo-relative tails preserved
    assert out_text.count("proj") == 2
    # source cell byte-identical
    assert json.loads(after)["cells"][0]["source"] == ["show()"]
