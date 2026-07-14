"""Tests for scripts/notebook_tools/strip_machine_paths.py — multi-category
machine-username path scrubber (nuget + pip + ipykernel + conda + hfcache).

Detection is **path-based** (per-runtime cache-context token + username
absolute-path marker). The legacy v1 nuget-only categories still work
(``Loading extensions from`` display_data + ``Failed to load kernel
extension`` stream) and the tilde HOME placeholder
(``~\\.nuget\\packages\\...``, no username) is correctly left untouched.

The c.441 c4 extension adds four Python-side runtime categories:
- ``pip`` (AppData\\Roaming\\Python), ``ipykernel`` (AppData\\Local\\Temp\\ipykernel),
- ``conda`` (.conda\\envs), ``hfcache`` (.cache\\huggingface).

Tests focus on:
- detection per category: each runtime's signature path is caught in its
  category, not in the others (verifies per-category isolation)
- tilde HOME placeholder passes through (no PII = no leak)
- missing username = no leak (token alone never trips a hit)
- strip safety: ``execution_count`` preserved, ``outputs`` shape stable, the
  leak-bearing line is the only thing removed
- strip idempotency: re-running on a clean file is a no-op
- per-category CLI filter (``ACTIVE_CATEGORIES = {category}``) scopes the
  scan/apply to one runtime only
- multi-token regression: extending the categories does NOT regress the
  legacy nuget-only detection (the v1 hook's job)
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import strip_machine_paths as _smp
from strip_machine_paths import (
    CACHE_TOKENS,
    USERNAME_MARKERS,
    STREAM_KEY,
    DATA_KEYS,
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


_DISPLAY_LINE = (
    "Loading extensions from `C:\\Users\\jsboi\\.nuget\\packages\\"
    "skiasharp\\2.88.9\\interactive-extensions\\dotnet\\"
    "SkiaSharp.DotNet.Interactive.dll`"
)
_STREAM_LINE = (
    'Failed to load kernel extension "KernelExtension" from assembly '
    "C:\\Users\\jsboi\\.nuget\\packages\\xplot.plotly.interactive\\4.1.0\\"
    "lib\\net7.0\\XPlot.Plotly.Interactive.dll"
)
_TILDE_DISPLAY_LINE = (
    "Loading extensions from `~\\.nuget\\packages\\xplot.plotly.interactive\\"
    "4.1.0\\lib\\net7.0\\XPlot.Plotly.Interactive.dll`"
)
_TILDE_STREAM_LINE = (
    'Failed to load kernel extension "KernelExtension" from assembly '
    "~\\.nuget\\packages\\xplot.plotly.interactive\\4.1.0\\lib\\net7.0\\"
    "XPlot.Plotly.Interactive.dll"
)


def _display_output(line, data_key="text/plain", form="list"):
    value = [line] if form == "list" else line
    return {"output_type": "display_data", "data": {data_key: value},
            "metadata": {}}


def _stream_output(line, form="list"):
    value = [line] if form == "list" else line
    return {"output_type": "stream", "name": "stderr", "text": value}


# ---------------------------------------------------------------------------
# Detection
# ---------------------------------------------------------------------------

def test_has_leak_matches_display_username_path():
    assert _has_leak(_DISPLAY_LINE) is True


def test_has_leak_matches_stream_username_path():
    """The 'Failed to load kernel extension ... from assembly' stream variant
    (the one the v1 signature-based hook missed, cf #6537 review)."""
    assert _has_leak(_STREAM_LINE) is True


def test_has_leak_requires_username_marker_not_just_nuget():
    """Tilde HOME placeholder + NuGet cache = NOT a leak (no username)."""
    assert _has_leak(_TILDE_DISPLAY_LINE) is False
    assert _has_leak(_TILDE_STREAM_LINE) is False


def test_has_leak_requires_nuget_context():
    """Username path present but no NuGet-cache context -> not this leak
    (avoids over-matching arbitrary C:\\Users\\x\\ paths in other outputs)."""
    line = "Wrote output to C:\\Users\\jsboi\\Documents\\report.txt"
    assert _has_leak(line) is False


def test_has_leak_no_signature_still_matches_via_path():
    """Path-based detection: a username NuGet path IS a leak regardless of the
    message prefix (the v1 hook wrongly required 'Loading extensions from')."""
    line = "Cached package at C:\\Users\\jsboi\\.nuget\\packages\\skiasharp\\2.88.9"
    assert _has_leak(line) is True


def test_has_leak_relative_path():
    line = "Loading extensions from `./local-build/MyExt.dll`"
    assert _has_leak(line) is False


def test_has_leak_unix_home_path():
    line = ("Loading extensions from `/home/worker/.nuget/packages/skiasharp/"
            "2.88.9/interactive-extensions/dotnet/SkiaSharp.DotNet.Interactive.dll`")
    assert _has_leak(line) is True


def test_output_has_leak_list_and_string():
    assert _output_has_leak([_DISPLAY_LINE]) is True
    assert _output_has_leak(_STREAM_LINE) is True
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
# Count / find — display_data + stream
# ---------------------------------------------------------------------------

def test_count_and_find_display_list_form(tmp_path):
    out = _display_output(_DISPLAY_LINE, "text/plain", form="list")
    cells = [_code(["#r \"nuget:SkiaSharp\""], outputs=[out], execution_count=3)]
    p = _write_nb(tmp_path / "a.ipynb", cells)
    assert count_leak_lines(p) == 1
    assert find_leak_outputs(p) == [(0, 0, "text/plain")]


def test_count_display_string_form(tmp_path):
    out = _display_output(_DISPLAY_LINE, "text/plain", form="str")
    cells = [_code(["#r \"nuget:SkiaSharp\""], outputs=[out])]
    p = _write_nb(tmp_path / "b.ipynb", cells)
    assert count_leak_lines(p) == 1


def test_count_and_find_stream_list_form(tmp_path):
    """The stream 'Failed to load kernel extension' variant (ML-5-TimeSeries)."""
    out = _stream_output(_STREAM_LINE, form="list")
    cells = [_code(["#r \"nuget:XPlot.Plotly.Interactive\""], outputs=[out])]
    p = _write_nb(tmp_path / "s.ipynb", cells)
    assert count_leak_lines(p) == 1
    assert find_leak_outputs(p) == [(0, 0, STREAM_KEY)]


def test_count_stream_string_form(tmp_path):
    out = _stream_output(_STREAM_LINE, form="str")
    cells = [_code(["#r \"nuget:X\""], outputs=[out])]
    p = _write_nb(tmp_path / "s2.ipynb", cells)
    assert count_leak_lines(p) == 1


def test_count_both_messages_in_one_output(tmp_path):
    """ML-5-TimeSeries shape: display_data 'Loading' + stream 'Failed to load'
    in the same cell. Both must be counted."""
    cells = [_code(["#r \"nuget:XPlot.Plotly.Interactive\""], outputs=[
        _display_output(_DISPLAY_LINE, "text/plain", form="list"),
        _stream_output(_STREAM_LINE, form="list"),
    ])]
    p = _write_nb(tmp_path / "both.ipynb", cells)
    assert count_leak_lines(p) == 2
    assert sorted(find_leak_outputs(p)) == [(0, 0, "text/plain"), (0, 1, STREAM_KEY)]


def test_count_zero_on_tilde_only(tmp_path):
    """ML-7-Recommendation / OR-tools-Stiegler shape: tilde variants only -> 0."""
    cells = [_code(["#r \"nuget:XPlot.Plotly.Interactive\""], outputs=[
        _display_output(_TILDE_DISPLAY_LINE, "text/plain", form="list"),
        _stream_output(_TILDE_STREAM_LINE, form="list"),
    ])]
    p = _write_nb(tmp_path / "tilde.ipynb", cells)
    assert count_leak_lines(p) == 0
    assert find_leak_outputs(p) == []


def test_count_zero_on_clean(tmp_path):
    cells = [_code(["print('hello')"], outputs=[
        {"output_type": "stream", "name": "stdout", "text": ["hello\n"]}])]
    p = _write_nb(tmp_path / "clean.ipynb", cells)
    assert count_leak_lines(p) == 0


# ---------------------------------------------------------------------------
# Strip safety
# ---------------------------------------------------------------------------

def test_strip_display_list_form_preserves_execution_count_and_shape(tmp_path):
    out = _display_output(_DISPLAY_LINE, "text/plain", form="list")
    cells = [_code(["#r \"nuget:SkiaSharp\""], outputs=[out], execution_count=7)]
    p = _write_nb(tmp_path / "list.ipynb", cells)
    outputs_with_leak, fixed = strip_in_place(p)
    assert outputs_with_leak == 1
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    cell = nb["cells"][0]
    assert cell["execution_count"] == 7
    assert len(cell["outputs"]) == 1
    data = cell["outputs"][0]["data"]
    assert "text/plain" in data
    assert isinstance(data["text/plain"], list)
    assert count_leak_lines(p) == 0


def test_strip_display_string_form(tmp_path):
    out = _display_output(_DISPLAY_LINE, "text/plain", form="str")
    cells = [_code(["#r \"nuget:X\""], outputs=[out], execution_count=2)]
    p = _write_nb(tmp_path / "str.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    data = nb["cells"][0]["outputs"][0]["data"]
    assert data["text/plain"] == ""
    assert count_leak_lines(p) == 0


def test_strip_stream_list_form(tmp_path):
    """Strip the 'Failed to load kernel extension' stream variant."""
    out = _stream_output(_STREAM_LINE, form="list")
    cells = [_code(["#r \"nuget:X\""], outputs=[out], execution_count=5)]
    p = _write_nb(tmp_path / "stream.ipynb", cells)
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (1, 1)
    nb = json.loads(p.read_text(encoding="utf-8"))
    cell = nb["cells"][0]
    assert cell["execution_count"] == 5
    assert len(cell["outputs"]) == 1
    assert isinstance(cell["outputs"][0]["text"], list)
    assert count_leak_lines(p) == 0


def test_strip_stream_string_form(tmp_path):
    out = _stream_output(_STREAM_LINE, form="str")
    cells = [_code(["#r \"nuget:X\""], outputs=[out])]
    p = _write_nb(tmp_path / "sstream.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    assert nb["cells"][0]["outputs"][0]["text"] == ""


def test_strip_both_messages_one_cell(tmp_path):
    """ML-5-TimeSeries: both messages stripped, execution_count preserved."""
    cells = [_code(["#r \"nuget:XPlot.Plotly.Interactive\""], outputs=[
        _display_output(_DISPLAY_LINE, "text/plain", form="list"),
        _stream_output(_STREAM_LINE, form="list"),
    ], execution_count=1)]
    p = _write_nb(tmp_path / "ml5.ipynb", cells)
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (2, 2)
    assert count_leak_lines(p) == 0


def test_strip_does_not_touch_tilde_variants(tmp_path):
    """Tilde display_data + stream lines must survive a strip untouched."""
    cells = [_code(["#r \"nuget:XPlot.Plotly.Interactive\""], outputs=[
        _display_output(_TILDE_DISPLAY_LINE, "text/plain", form="list"),
        _stream_output(_TILDE_STREAM_LINE, form="list"),
    ], execution_count=2)]
    p = _write_nb(tmp_path / "tilde2.ipynb", cells)
    before = p.read_text(encoding="utf-8")
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (0, 0)
    assert p.read_text(encoding="utf-8") == before  # byte-identical


def test_strip_preserves_other_data_keys(tmp_path):
    out = {"output_type": "display_data",
           "data": {"text/plain": [_DISPLAY_LINE],
                    "text/html": ["<i>chart</i>"]},
           "metadata": {}}
    cells = [_code(["#r \"nuget:x\""], outputs=[out])]
    p = _write_nb(tmp_path / "multi.ipynb", cells)
    strip_in_place(p)
    nb = json.loads(p.read_text(encoding="utf-8"))
    data = nb["cells"][0]["outputs"][0]["data"]
    assert data["text/html"] == ["<i>chart</i>"]
    assert count_leak_lines(p) == 0


def test_strip_drops_only_leak_element_in_multiline_list(tmp_path):
    out = {"output_type": "display_data",
           "data": {"text/plain": ["Plotly chart rendered.", _DISPLAY_LINE]},
           "metadata": {}}
    cells = [_code(["#r \"nuget:x\""], outputs=[out])]
    p = _write_nb(tmp_path / "ml.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    tp = nb["cells"][0]["outputs"][0]["data"]["text/plain"]
    assert "Plotly chart rendered." in tp
    assert not any("Loading extensions from" in (l or "") for l in tp)


def test_strip_stream_drops_only_leak_element(tmp_path):
    """Stream text with a legit stderr line + the leak: only leak dropped."""
    out = _stream_output("[stderr] some benign warning\n", form="str")
    # build a list with a legit line + the leak line
    out2 = {"output_type": "stream", "name": "stderr",
            "text": ["[stderr] benign warning\n", _STREAM_LINE + "\n"]}
    cells = [_code(["#r \"nuget:x\""], outputs=[out2])]
    p = _write_nb(tmp_path / "mls.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    txt = nb["cells"][0]["outputs"][0]["text"]
    assert any("benign warning" in (l or "") for l in txt)
    assert not any("Failed to load kernel extension" in (l or "") for l in txt)


def test_strip_idempotent(tmp_path):
    cells = [_code(["#r \"nuget:X\""], outputs=[
        _display_output(_DISPLAY_LINE, "text/plain", form="list"),
        _stream_output(_STREAM_LINE, form="list"),
    ])]
    p = _write_nb(tmp_path / "idem.ipynb", cells)
    strip_in_place(p)
    before = p.read_text(encoding="utf-8")
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (0, 0)
    assert p.read_text(encoding="utf-8") == before


def test_strip_keeps_valid_json(tmp_path):
    cells = [_code(["#r \"nuget:x\""], outputs=[
        _display_output(_DISPLAY_LINE, "text/plain", form="list"),
        _stream_output(_STREAM_LINE, form="list"),
    ], execution_count=4)]
    p = _write_nb(tmp_path / "json.ipynb", cells)
    strip_in_place(p)
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

def test_constants_sensible():
    """The v1 hook's NuGet-only detection is preserved as the FIRST entry
    of the multi-category registry. Username markers are unchanged."""
    labels = {label for label, _ in CACHE_TOKENS}
    assert "nuget" in labels, "v1 nuget category MUST be preserved"
    # The new categories added in c.441 c4 (#6529 follow-up scope):
    assert {"pip", "ipykernel", "conda", "hfcache"} <= labels, \
        "missing one of the c.441 c4 categories: pip/ipykernel/conda/hfcache"
    assert "Users\\" in USERNAME_MARKERS
    assert "Users/" in USERNAME_MARKERS
    assert "/home/" in USERNAME_MARKERS
    assert STREAM_KEY == "text"
    assert "text/plain" in DATA_KEYS and "text/html" in DATA_KEYS


# ---------------------------------------------------------------------------
# New categories (c.441 c4 #6529 follow-up scope)
# ---------------------------------------------------------------------------

# Canonical kernel-injected shapes observed in the wild.
_PIP_LINE = (
    r"C:\Users\jsboi\AppData\Roaming\Python\Python313\site-packages\peft"
    r"\tuners\lora\layer.py:2504: UserWarning: fan_in_fan_out is set to False"
)
_IPYKERNEL_LINE = (
    r"C:\Users\jsboi\AppData\Local\Temp\ipykernel_30104\1424116259.py:8: "
    "DeprecationWarning: generate_image is deprecated. Use generate_images."
)
_CONDA_LINE = (
    r"C:\Users\jsboi\.conda\envs\mcp-jupyter-py310\lib\site-packages\torch"
    r"\nn\utils\weight_norm.py:30: UserWarning: torch.nn.utils.weight_norm"
    " is deprecated in favor of torch.nn.utils.parametrizations.weight_norm."
)
_HFCACHE_LINE = (
    r"Downloading dataset to C:\Users\jsboi\.cache\huggingface\dataset"
    r"\wikitext-2-raw-v1"
)


def test_pip_appdata_warning_caught():
    """pip-import warnings carry the AppData\\Roaming\\Python site-packages
    path (peft/torch/etc.) — these are stderr lines, multi-line tracebacks."""
    assert _has_leak(_PIP_LINE) is True


def test_ipykernel_temp_warning_caught():
    """ipykernel temp-file deprecation warnings carry ``AppData\\Local\\Temp
    \\ipykernel_<pid>\\<file>:<line>:`` paths."""
    assert _has_leak(_IPYKERNEL_LINE) is True


def test_conda_env_warning_caught():
    """Conda-env warnings carry ``.conda\\envs\\<env>\\lib\\site-packages
    \\<pkg>\\<file>:<line>:`` paths."""
    assert _has_leak(_CONDA_LINE) is True


def test_hfcache_download_warning_caught():
    """HF transformers/datasets download warnings carry ``.cache\\huggingface
    \\dataset\\<name>`` paths."""
    assert _has_leak(_HFCACHE_LINE) is True


def test_cross_category_isolation_when_filtered():
    """With ``ACTIVE_CATEGORIES = {'pip'}`` set, a conda-env leak must NOT
    trip — and vice-versa. Verifies per-category isolation.

    Mutates ``_smp.ACTIVE_CATEGORIES`` (module global) — NOT a locally
    rebound copy — because ``_iter_tokens`` reads the module attribute. A
    bare ``from strip_machine_paths import ACTIVE_CATEGORIES`` rebinds the
    test's local name only, leaving the module global untouched.
    """
    saved = _smp.ACTIVE_CATEGORIES
    try:
        _smp.ACTIVE_CATEGORIES = {"pip"}
        assert _has_leak(_PIP_LINE) is True
        assert _has_leak(_CONDA_LINE) is False
        assert _has_leak(_IPYKERNEL_LINE) is False
        assert _has_leak(_HFCACHE_LINE) is False
        assert _has_leak(_DISPLAY_LINE) is False  # nuget
    finally:
        _smp.ACTIVE_CATEGORIES = saved


def test_token_alone_no_username_never_leaks():
    """The cache-context token must NEVER trigger alone — the username is
    what makes it PII. A ``\.conda\\envs\\foo`` mention on Linux (no
    ``Users\\jsboi``) is not a leak."""
    assert _has_leak(r".conda\envs\myenv\lib\foo.py") is False
    assert _has_leak(r".cache\huggingface\dataset\foo") is False
    assert _has_leak(r".nuget\packages\x") is False
    assert _has_leak(r"AppData\Roaming\Python\Python313\site-packages\x") is False
    assert _has_leak(r"AppData\Local\Temp\ipykernel_1234\foo.py") is False


def test_unrelated_user_path_no_token_no_leak():
    """A username-bearing path that ISN'T a runtime cache = no leak.
    E.g. ``C:\\Users\\jsboi\\Documents\\foo.txt``."""
    assert _has_leak(r"C:\Users\jsboi\Documents\foo.txt") is False


# ---------------------------------------------------------------------------
# Strip safety for new categories
# ---------------------------------------------------------------------------

def test_strip_removes_pip_warning_line_keeps_body(tmp_path):
    """The typical pip traceback shape: leak-bearing first line + a
    ``warnings.warn(...)`` continuation. The strip drops only the leak line."""
    out = {"output_type": "stream", "name": "stderr",
           "text": [_PIP_LINE + "\n", "  warnings.warn()\n"]}
    cells = [_code(["x = 1"], outputs=[out], execution_count=1)]
    p = _write_nb(tmp_path / "pip.ipynb", cells)
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (1, 1)
    nb = json.loads(p.read_text(encoding="utf-8"))
    cell = nb["cells"][0]
    assert cell["execution_count"] == 1, "execution_count MUST be preserved"
    assert cell["outputs"][0]["text"] == ["  warnings.warn()\n"]


def test_strip_removes_conda_line_keeps_body(tmp_path):
    out = {"output_type": "stream", "name": "stderr",
           "text": [_CONDA_LINE + "\n", "  warnings.warn()\n"]}
    cells = [_code(["x = 1"], outputs=[out], execution_count=2)]
    p = _write_nb(tmp_path / "conda.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    assert nb["cells"][0]["execution_count"] == 2
    assert nb["cells"][0]["outputs"][0]["text"] == ["  warnings.warn()\n"]


def test_strip_removes_hfcache_line(tmp_path):
    out = {"output_type": "stream", "name": "stderr",
           "text": [_HFCACHE_LINE + "\n"]}
    cells = [_code(["x = 1"], outputs=[out], execution_count=3)]
    p = _write_nb(tmp_path / "hf.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    assert nb["cells"][0]["outputs"][0]["text"] == [""]
