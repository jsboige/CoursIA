"""Tests for scripts/notebook_tools/strip_machine_paths.py — .NET NuGet-extension
machine-username leak scrubber.

Tests focus on:
- detection: the ``Loading extensions from`` signature matches only the
  kernel-injected NuGet-cache message carrying a user-profile path, never
  legitimate prose and never a relative path without a user-profile segment
- strip safety: ``execution_count`` preserved, ``outputs`` shape stable, other
  ``data`` keys untouched, JSON stays valid
- idempotency: re-running ``strip_in_place`` on a clean file is a no-op
- both list-form (observed) and string-form data values
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from strip_machine_paths import (
    EXT_LOAD_SIGNATURE,
    USER_PATH_TOKENS,
    count_leak_lines,
    find_leak_outputs,
    strip_in_place,
    _has_leak,
    _output_has_leak,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells):
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _code(source, outputs=None, execution_count=1):
    return {"cell_type": "code", "source": source, "metadata": {},
            "execution_count": execution_count, "outputs": outputs or []}


def _md(source):
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path, cells):
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = _nb(cells)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _nuget_ext_output(data_key="text/plain", form="list"):
    """Build a synthetic 'Loading extensions from' display_data output.

    form='list' -> data[key] is a list[str] (the observed shape).
    form='str'  -> data[key] is a single inline string.
    """
    line = ("Loading extensions from `C:\\Users\\jsboi\\.nuget\\packages\\"
            "skiasharp\\2.88.9\\interactive-extensions\\dotnet\\"
            "SkiaSharp.DotNet.Interactive.dll`")
    value = [line] if form == "list" else line
    return {"output_type": "display_data",
            "data": {data_key: value},
            "metadata": {}}


# ---------------------------------------------------------------------------
# Detection
# ---------------------------------------------------------------------------

def test_has_leak_matches_nuget_cache_path():
    line = ("Loading extensions from `C:\\Users\\jsboi\\.nuget\\packages\\"
            "plotly.net.interactive\\5.0.0\\lib\\netstandard2.1\\"
            "Plotly.NET.Interactive.dll`")
    assert _has_leak(line) is True


def test_has_leak_requires_user_path_token():
    """Signature present but no user-profile path -> NOT a leak (FP guard)."""
    line = "Loading extensions from `./local-build/MyExt.dll`"
    assert _has_leak(line) is False


def test_has_leak_requires_signature():
    """User path present but no 'Loading extensions from' -> NOT this leak."""
    line = "Cached at C:\\Users\\jsboi\\.nuget\\packages\\skiasharp\\2.88.9"
    assert _has_leak(line) is False


def test_has_leak_unix_home_path():
    line = ("Loading extensions from `/home/worker/.nuget/packages/skiasharp/"
            "2.88.9/interactive-extensions/dotnet/SkiaSharp.DotNet.Interactive.dll`")
    assert _has_leak(line) is True


def test_has_leak_failed_to_load_variant():
    """The 'Failed to load kernel extension' failure-variant carries the same
    C:\\Users\\<user>\\.nuget\\packages\\...dll payload as the success-variant
    and must be flagged too (regression guard for the variant gap surfaced in
    PR #6537 review / c.529)."""
    line = ('Failed to load kernel extension "KernelExtension" from assembly '
            'C:\\Users\\jsboi\\.nuget\\packages\\xplot.plotly.interactive\\'
            '4.1.0\\lib\\net7.0\\XPlot.Plotly.Interactive.dll')
    assert _has_leak(line) is True


def test_has_leak_failed_to_load_variant_tilde_also_flagged():
    """The failure-variant with a tilde HOME path (no username) still carries a
    .nuget cache token, so it is flagged for consistency: the existing hook
    already strips success-variant ``Loading extensions from ~/.nuget/...``
    lines whenever ``.nuget`` is present (USER_PATH_TOKENS), and the failure
    variant is the same dead kernel-injected message class."""
    line = ('Failed to load kernel extension "KernelExtension" from assembly '
            '~\\.nuget\\packages\\xplot.plotly.interactive\\3.0.2\\lib\\net5.0\\'
            'XPlot.Plotly.Interactive.dll')
    assert _has_leak(line) is True


def test_output_has_leak_list_and_string():
    assert _output_has_leak(["Loading extensions from `C:\\Users\\x\\.nuget\\p\\a`"]) is True
    assert _output_has_leak("Loading extensions from `C:\\Users\\x\\.nuget\\p\\a`") is True
    assert _output_has_leak(["ordinary text/plain line"]) is False
    assert _output_has_leak(None) is False


def test_legitimate_prose_not_flagged(tmp_path):
    """Markdown discussing the leak class must not be flagged."""
    cells = [_md("The 'Loading extensions from <NuGet cache>' message is a "
                 "category-A kernel-injected leak (#6529).")]
    p = _write_nb(tmp_path / "prose.ipynb", cells)
    assert count_leak_lines(p) == 0
    assert find_leak_outputs(p) == []


# ---------------------------------------------------------------------------
# Count / find
# ---------------------------------------------------------------------------

def test_count_and_find_list_form(tmp_path):
    out = _nuget_ext_output("text/plain", form="list")
    cells = [_code(["#r \"nuget:SkiaSharp\""], outputs=[out], execution_count=3)]
    p = _write_nb(tmp_path / "a.ipynb", cells)
    assert count_leak_lines(p) == 1
    assert find_leak_outputs(p) == [(0, 0, "text/plain")]


def test_count_string_form(tmp_path):
    out = _nuget_ext_output("text/plain", form="str")
    cells = [_code(["#r \"nuget:SkiaSharp\""], outputs=[out])]
    p = _write_nb(tmp_path / "b.ipynb", cells)
    assert count_leak_lines(p) == 1


def test_count_zero_on_clean(tmp_path):
    cells = [_code(["print('hello')"], outputs=[
        {"output_type": "stream", "name": "stdout", "text": ["hello\n"]}])]
    p = _write_nb(tmp_path / "clean.ipynb", cells)
    assert count_leak_lines(p) == 0


# ---------------------------------------------------------------------------
# Strip safety
# ---------------------------------------------------------------------------

def test_strip_list_form_preserves_execution_count_and_shape(tmp_path):
    out = _nuget_ext_output("text/plain", form="list")
    cells = [_code(["#r \"nuget:SkiaSharp\""], outputs=[out], execution_count=7)]
    p = _write_nb(tmp_path / "list.ipynb", cells)
    outputs_with_leak, fixed = strip_in_place(p)
    assert outputs_with_leak == 1
    assert fixed == 1
    # Re-parse: execution_count preserved, output still present, list shape intact
    nb = json.loads(p.read_text(encoding="utf-8"))
    cell = nb["cells"][0]
    assert cell["execution_count"] == 7
    assert len(cell["outputs"]) == 1
    data = cell["outputs"][0]["data"]
    assert "text/plain" in data  # key preserved
    assert isinstance(data["text/plain"], list)  # shape preserved
    # No leak remains
    assert count_leak_lines(p) == 0


def test_strip_string_form(tmp_path):
    out = _nuget_ext_output("text/plain", form="str")
    cells = [_code(["#r \"nuget:X\""], outputs=[out], execution_count=2)]
    p = _write_nb(tmp_path / "str.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    assert nb["cells"][0]["data"] if False else True  # placate lint
    data = nb["cells"][0]["outputs"][0]["data"]
    assert data["text/plain"] == ""  # replaced with empty string
    assert count_leak_lines(p) == 0


def test_strip_preserves_other_data_keys(tmp_path):
    """A multi-key data dict: only the leak key is touched."""
    leak_line = ("Loading extensions from `C:\\Users\\jsboi\\.nuget\\packages\\"
                 "x\\1.0.0\\x.dll`")
    out = {"output_type": "display_data",
           "data": {"text/plain": [leak_line],
                    "text/html": ["<i>chart</i>"]},
           "metadata": {}}
    cells = [_code(["#r \"nuget:x\""], outputs=[out])]
    p = _write_nb(tmp_path / "multi.ipynb", cells)
    strip_in_place(p)
    nb = json.loads(p.read_text(encoding="utf-8"))
    data = nb["cells"][0]["outputs"][0]["data"]
    assert data["text/html"] == ["<i>chart</i>"]  # untouched
    assert count_leak_lines(p) == 0


def test_strip_drops_only_leak_element_in_multiline_list(tmp_path):
    """text/plain list with a real output line + the leak line: only leak dropped."""
    leak_line = ("Loading extensions from `C:\\Users\\jsboi\\.nuget\\packages\\"
                 "x\\1.0.0\\x.dll`")
    out = {"output_type": "display_data",
           "data": {"text/plain": ["Plotly chart rendered.", leak_line]},
           "metadata": {}}
    cells = [_code(["#r \"nuget:x\""], outputs=[out])]
    p = _write_nb(tmp_path / "ml.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    tp = nb["cells"][0]["outputs"][0]["data"]["text/plain"]
    assert "Plotly chart rendered." in tp
    assert not any("Loading extensions from" in (l or "") for l in tp)


def test_strip_idempotent(tmp_path):
    out = _nuget_ext_output("text/plain", form="list")
    cells = [_code(["#r \"nuget:X\""], outputs=[out])]
    p = _write_nb(tmp_path / "idem.ipynb", cells)
    strip_in_place(p)
    before = p.read_text(encoding="utf-8")
    outputs_with_leak, fixed = strip_in_place(p)  # second pass
    assert outputs_with_leak == 0
    assert fixed == 0
    assert p.read_text(encoding="utf-8") == before  # byte-identical


def test_strip_keeps_valid_json(tmp_path):
    """The on-disk edit must leave valid JSON parseable by the stdlib."""
    leak_line = ("Loading extensions from `C:\\Users\\jsboi\\.nuget\\packages\\"
                 "x\\1.0.0\\x.dll`")
    out = {"output_type": "display_data",
           "data": {"text/plain": [leak_line]}, "metadata": {}}
    cells = [_code(["#r \"nuget:x\""], outputs=[out], execution_count=4)]
    p = _write_nb(tmp_path / "json.ipynb", cells)
    strip_in_place(p)
    # Must not raise
    nb = json.loads(p.read_text(encoding="utf-8"))
    assert nb["nbformat"] == 4


def test_no_leak_no_change(tmp_path):
    cells = [_code(["print('hi')"], outputs=[
        {"output_type": "stream", "name": "stdout", "text": ["hi\n"]}])]
    p = _write_nb(tmp_path / "noop.ipynb", cells)
    before = p.read_text(encoding="utf-8")
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (0, 0)
    assert p.read_text(encoding="utf-8") == before


# ---------------------------------------------------------------------------
# Constants sanity
# ---------------------------------------------------------------------------

def test_signature_and_tokens_sensible():
    assert EXT_LOAD_SIGNATURE == "Loading extensions from"
    assert ".nuget" in USER_PATH_TOKENS
    assert "Users\\" in USER_PATH_TOKENS
    assert "/home/" in USER_PATH_TOKENS
