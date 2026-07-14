"""Tests for scripts/notebook_tools/strip_machine_paths.py — .NET NuGet-cache
machine-username leak scrubber.

Detection is **path-based** (NuGet-cache token + username absolute-path
marker), so it matches BOTH dotnet-interactive kernel messages:
- ``display_data`` ``data["text/plain"]``: "Loading extensions from <path>"
- ``stream`` ``text``: "Failed to load kernel extension ... from assembly <path>"

and leaves the **tilde** HOME-placeholder variant (``~\\.nuget\\packages\\...``)
untouched (no username = no leak), cf. the ``#6537`` review.

Tests focus on:
- detection: username NuGet path matches in BOTH messages; tilde never matches;
  relative paths never match
- strip safety: ``execution_count`` preserved, ``outputs`` shape stable, other
  ``data`` keys untouched, JSON stays valid
- idempotency: re-running ``strip_in_place`` on a clean file is a no-op
- list-form (observed) and string-form data/stream values
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from strip_machine_paths import (
    NUGET_CACHE_TOKEN,
    MACHINE_PATH_TOKENS,
    REDACT_TOKENS,
    USERNAME_MARKERS,
    STREAM_KEY,
    DATA_KEYS,
    count_leak_lines,
    find_leak_outputs,
    strip_in_place,
    _has_leak,
    _is_redactable,
    _redact_path,
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


# ---------------------------------------------------------------------------
# Python-side category-A families (EPIC #6529 follow-up): path-based detection
# broadened to AppData / HF-cache / conda / site-packages / ipykernel contexts.
# ---------------------------------------------------------------------------

def test_has_leak_appdata_site_packages():
    """pip --user install warning carrying the user-site path."""
    line = (r"C:\Users\jsboi\AppData\Roaming\Python\Python313\site-packages"
            r"\triton\windows_utils.py:433: UserWarning: Failed to find CUDA.")
    assert _has_leak(line) is True


def test_has_leak_huggingface_cache():
    """HuggingFace hub cache path embedded in an error message."""
    line = (r"Error parsing line in C:\Users\jsboi\.cache\huggingface\hub"
            r"\models--LTX-Video\tokenizer\spiece.model")
    assert _has_leak(line) is True


def test_has_leak_conda_env():
    """conda env site-packages path in a warning."""
    line = (r"C:\Users\jsboi\.conda\envs\bonsai\Lib\site-packages\peft\utils"
            r"\other.py:1419: UserWarning: fetch failed")
    assert _has_leak(line) is True


def test_has_leak_ipykernel_temp():
    """ipykernel temp-dir path in a deprecation warning."""
    line = (r"C:\Users\jsboi\AppData\Local\Temp\ipykernel_30104\1424116259.py"
            r":8: DeprecationWarning: generate_image is deprecated.")
    assert _has_leak(line) is True


def test_has_leak_torch_hub_cache():
    """torch hub download cache path (forward-slash variant)."""
    line = r"Downloading to C:\Users\jsboi/.cache/torch/hub/checkpoints/x.th"
    assert _has_leak(line) is True


def test_has_leak_requires_context_token_fp_guard():
    """Username present but NO machine-path context token -> NOT a leak (FP
    guard preserves prose discussing the username without a cache/env/site)."""
    line = r"The leak class Users\jsboi is category-A (#6529)."
    assert _has_leak(line) is False


def test_is_redactable_python_yes_nuget_no():
    """Python families are redactable (warning text is pedagogical); .nuget is
    NOT (self-contained kernel noise -> dropped, cf #6567)."""
    assert _is_redactable(r"C:\Users\jsboi\AppData\Roaming\Python\site-packages") is True
    assert _is_redactable(r"C:\Users\jsboi\.conda\envs\bonsai\lib") is True
    assert _is_redactable(r"Loading extensions from C:\Users\jsboi\.nuget\packages") is False


def test_redact_path_preserves_warning_removes_username():
    """Redaction replaces the username segment with ~ but keeps the rest of the
    path and the trailing warning text (the pedagogical content)."""
    win = _redact_path(r"C:\Users\jsboi\AppData\Roaming\Python\Python313"
                       r"\site-packages\triton\windows_utils.py:433: "
                       r"UserWarning: Failed to find CUDA.")
    assert "jsboi" not in win
    assert win.startswith("~")
    assert "Failed to find CUDA." in win
    assert "site-packages" in win
    unix = _redact_path(r"/home/worker/.conda/envs/bonsai/lib/site-packages/peft/x.py:1: W: foo")
    assert "worker" not in unix
    assert unix.startswith("~")
    assert "W: foo" in unix


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
# Python redaction (EPIC #6529): AppData/HF-cache/conda/site-packages/ipykernel
# leaks are REDACTED (path -> ~) not dropped, preserving the warning text.
# ---------------------------------------------------------------------------

def test_strip_redacts_python_stream_warning(tmp_path):
    """A pip --user warning in a stream is REDACTED (path -> ~), not dropped:
    the warning text is pedagogical and must survive the strip."""
    line = (r"C:\Users\jsboi\AppData\Roaming\Python\Python313\site-packages"
            r"\triton\windows_utils.py:433: UserWarning: Failed to find CUDA.")
    out = _stream_output(line, form="list")
    cells = [_code(["import torch"], outputs=[out], execution_count=3)]
    p = _write_nb(tmp_path / "warn.ipynb", cells)
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (1, 1)
    nb = json.loads(p.read_text(encoding="utf-8"))
    cell = nb["cells"][0]
    assert cell["execution_count"] == 3              # preserved
    assert len(cell["outputs"]) == 1                 # output NOT dropped
    text = cell["outputs"][0]["text"]
    redacted = text[0] if isinstance(text, list) else text
    assert "jsboi" not in redacted                   # username gone
    assert "Failed to find CUDA." in redacted        # warning text kept
    assert redacted.startswith("~")                  # path prefix redacted
    assert count_leak_lines(p) == 0


def test_strip_redacts_multiline_stream_only_leak_lines(tmp_path):
    """A multi-line stream with one clean line + one leak line: only the leak
    line is redacted, the clean line is untouched, the line count is stable."""
    clean = "Starting training...\n"
    leak = (r"C:\Users\jsboi\.conda\envs\bonsai\Lib\site-packages\peft\x.py:1: "
            r"UserWarning: config not found.")
    out = {"output_type": "stream", "name": "stderr", "text": [clean, leak]}
    cells = [_code(["train()"], outputs=[out])]
    p = _write_nb(tmp_path / "multi.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    text = nb["cells"][0]["outputs"][0]["text"]
    assert text[0] == clean                          # clean line untouched
    assert "jsboi" not in text[1]
    assert "config not found." in text[1]            # warning kept
    assert count_leak_lines(p) == 0


def test_strip_idempotent_after_redaction(tmp_path):
    """Re-running on a redacted notebook is a no-op (redacted path has no
    username marker -> no longer a leak)."""
    line = r"C:\Users\jsboi\.cache\huggingface\hub\models--X\tokenizer\t.model"
    out = _stream_output(line, form="list")
    cells = [_code(["load()"], outputs=[out])]
    p = _write_nb(tmp_path / "idem.ipynb", cells)
    strip_in_place(p)
    before = p.read_text(encoding="utf-8")
    outputs_with_leak, fixed = strip_in_place(p)     # second pass
    assert (outputs_with_leak, fixed) == (0, 0)
    assert p.read_text(encoding="utf-8") == before


# ---------------------------------------------------------------------------
# Constants sanity
# ---------------------------------------------------------------------------

def test_constants_sensible():
    assert NUGET_CACHE_TOKEN == ".nuget"
    assert ".nuget" in MACHINE_PATH_TOKENS
    for tok in ("AppData", ".cache", ".conda", "site-packages", "ipykernel"):
        assert tok in MACHINE_PATH_TOKENS
        assert tok in REDACT_TOKENS
    assert ".nuget" not in REDACT_TOKENS             # .nuget -> drop, not redact
    assert "Users\\" in USERNAME_MARKERS
    assert "Users/" in USERNAME_MARKERS
    assert "/home/" in USERNAME_MARKERS
    assert STREAM_KEY == "text"
    assert "text/plain" in DATA_KEYS and "text/html" in DATA_KEYS
