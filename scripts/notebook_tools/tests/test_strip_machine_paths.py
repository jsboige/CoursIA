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
    USERNAME_MARKERS,
    MACHINE_PATH_TOKENS,
    ACTIVE_CATEGORIES,
    STREAM_KEY,
    DATA_KEYS,
    count_leak_lines,
    find_leak_outputs,
    strip_in_place,
    _has_leak,
    _output_has_leak,
    _redact_line,
    _first_matching_label,
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
    assert NUGET_CACHE_TOKEN == ".nuget"
    assert "Users\\" in USERNAME_MARKERS
    assert "Users/" in USERNAME_MARKERS
    assert "/home/" in USERNAME_MARKERS
    assert STREAM_KEY == "text"
    assert "text/plain" in DATA_KEYS and "text/html" in DATA_KEYS


# ---------------------------------------------------------------------------
# Multi-runtime category coverage (L496 — pre-flight for #6529 follow-up,
# cf. cycles-c441-c441-multi-cat-strip.md, C534-L1 REDACT design).
#
# Detection is **path-based** (cache-context token + username absolute-path
# marker). Six runtime categories are wired:
#   - nuget     .nuget                                  (dotnet-interactive)
#   - pip       AppData\Roaming\Python                  (CPython peft/torch)
#   - ipykernel AppData\Local\Temp\ipykernel            (kernel pid temp)
#   - conda     .conda\envs                             (conda env, e.g.
#                                                          nn.utils.weight_norm)
#   - hf        .cache\huggingface                      (HF download cache)
#   - other     AppData\Local\Temp                      (generic local Temp
#                                                          audio/scratch)
#
# The original NuGet hook (#6563) used a **DROP** strategy (drop the entire
# string-form value / drop the leak element in list-form). The new Python
# categories use **REDACT** (replace the username-bearing prefix with the
# stable ``<USER_PATH>`` placeholder, preserve the rest of the line).
# REDACT is the right strategy when the path is embedded in a pédagogique
# warning the notebook author wants readers to see — see C534-L1.
# ---------------------------------------------------------------------------

import strip_machine_paths as _smp  # NB: NEVER ``from ... import`` here,
#                                    # see L496 — module-global rebinding
#                                    # via ``from X import G; G = v`` is a
#                                    # NO-OP; we mutate the actual module
#                                    # attribute.

# Reset hook between tests (matters for tests that mutate ``ACTIVE_CATEGORIES``).
@pytest.fixture(autouse=True)
def _reset_active_categories():
    saved = _smp.ACTIVE_CATEGORIES
    yield
    _smp.ACTIVE_CATEGORIES = saved


# Synthetic leak lines — one per category — used to drive detection + REDACT.
_PIP_LINE = (
    "C:\\Users\\jsboi\\AppData\\Roaming\\Python\\Python313\\site-packages\\"
    "triton\\windows_utils.py:433: UserWarning: Failed to find CUDA."
)
_IPYKERNEL_LINE = (
    "C:\\Users\\jsboi\\AppData\\Local\\Temp\\ipykernel_30104\\1424116259.py:8: "
    "DeprecationWarning: generate_image is deprecated."
)
_CONDA_LINE = (
    "C:\\Users\\jsboi\\.conda\\envs\\mcp-jupyter-py310\\lib\\site-packages\\"
    "torch\\nn\\utils\\weight_norm.py:30: UserWarning: "
    "torch.nn.utils.weight_norm is deprecated."
)
_HF_LINE = (
    "C:\\Users\\jsboi\\.cache\\huggingface\\hub\\models--gpt2\\"
    "snapshots\\abc123\\config.json"
)
_OTHER_LINE = "C:\\Users\\jsboi\\AppData\\Local\\Temp\\test_audio.mp3"


def test_machine_path_tokens_canonical():
    """The category taxonomy MUST be exactly the 6 listed in C534-L1.

    Order matters for ``_first_matching_label`` (first hit wins): nuget →
    pip → ipykernel → conda → hf → other. The hf token (``.cache\\huggingface``)
    overlaps the ``other`` token (``AppData\\Local\\Temp``) **not at all**;
    what can happen is a single line matching pip THEN hf (because
    ``huggingface_hub`` lives under ``AppData\\Roaming\\Python\\site-packages``),
    and we want the more specific pip label to win (it is more diagnostic
    for the source machine — same env-name, same Python interpreter).
    """
    labels = [label for label, _ in MACHINE_PATH_TOKENS]
    assert labels == ["nuget", "pip", "ipykernel", "conda", "hf", "other"]
    # Backwards-compat surface preserved.
    assert MACHINE_PATH_TOKENS[0] == ("nuget", NUGET_CACHE_TOKEN)


def test_has_leak_per_category_default_all():
    """Default ``ACTIVE_CATEGORIES = None`` ⇒ ALL 5 new categories match."""
    assert _has_leak(_PIP_LINE) is True
    assert _has_leak(_IPYKERNEL_LINE) is True
    assert _has_leak(_CONDA_LINE) is True
    assert _has_leak(_HF_LINE) is True
    assert _has_leak(_OTHER_LINE) is True


def test_has_leak_still_matches_nuget_default():
    """The merged #6563 hook surface MUST keep matching NuGet leaks."""
    assert _has_leak(_DISPLAY_LINE) is True
    assert _has_leak(_STREAM_LINE) is True


def test_first_matching_label_per_category():
    assert _first_matching_label(_PIP_LINE) == "pip"
    assert _first_matching_label(_IPYKERNEL_LINE) == "ipykernel"
    assert _first_matching_label(_CONDA_LINE) == "conda"
    assert _first_matching_label(_HF_LINE) == "hf"
    assert _first_matching_label(_OTHER_LINE) == "other"
    assert _first_matching_label(_DISPLAY_LINE) == "nuget"
    # No token match ⇒ empty label.
    assert _first_matching_label("plain prose line") == ""
    # Defensive: non-string input.
    assert _first_matching_label(None) == ""  # type: ignore[arg-type]


def test_redact_line_strips_username_prefix():
    """The C534-L1 REDACT design: ``C:\\Users\\<u>\\...`` → ``<USER_PATH>\\...``
    where the username (``jsboi`` here) is **fully removed**, not preserved.
    """
    redacted = _redact_line(_PIP_LINE)
    assert redacted.startswith("<USER_PATH>\\")
    # Username MUST NOT appear post-REDACT.
    assert "jsboi" not in redacted
    # ``Users\\`` MUST NOT appear post-REDACT.
    assert "Users\\" not in redacted
    # Runtime-distinct segment preserved (the pedagogical part).
    assert "AppData\\Roaming\\Python" in redacted
    assert "Failed to find CUDA." in redacted


def test_redact_line_per_category():
    """REDACT applies uniformly — every category's username prefix is dropped
    and the runtime-distinct segment is preserved."""
    cases = [
        (_PIP_LINE, "AppData\\Roaming\\Python"),
        (_IPYKERNEL_LINE, "AppData\\Local\\Temp\\ipykernel_30104"),
        (_CONDA_LINE, ".conda\\envs\\mcp-jupyter-py310"),
        (_HF_LINE, ".cache\\huggingface"),
        (_OTHER_LINE, "AppData\\Local\\Temp\\test_audio.mp3"),
        (_DISPLAY_LINE, ".nuget\\packages"),
    ]
    for line, runtime_segment in cases:
        redacted = _redact_line(line)
        assert redacted.startswith("<USER_PATH>\\"), (line, redacted)
        assert "jsboi" not in redacted, (line, redacted)
        assert runtime_segment in redacted, (line, redacted, runtime_segment)


def test_redact_line_unix_home_path():
    """Unix ``/home/<u>/...`` marker is also recognized, and the full
    ``/home/<u>`` segment is dropped (not just the marker)."""
    line = (
        "/home/worker/.nuget/packages/skiasharp/2.88.9/"
        "interactive-extensions/dotnet/SkiaSharp.DotNet.Interactive.dll"
    )
    redacted = _redact_line(line)
    assert redacted.startswith("<USER_PATH>\\")
    assert "worker" not in redacted
    assert ".nuget" in redacted  # runtime segment preserved


def test_redact_line_no_username_marker_noop():
    """Defensive: caller should check ``_has_leak`` first. If there's no
    username marker, the line is returned verbatim (caller invariant)."""
    line = "AppData\\Roaming\\Python is just a path string here, no prefix."
    assert _redact_line(line) == line


def test_redact_line_empty_and_non_string():
    """Defensive: empty / non-string input must not crash."""
    assert _redact_line("") == ""
    # Non-string input — caller invariant is to check ``_has_leak`` first
    # which itself returns False on non-strings, so this branch is defensive.
    assert _redact_line(None) is None  # type: ignore[arg-type]


# --- ACTIVE_CATEGORIES filter (L496 anti-rebinding) ---------------------

def test_active_categories_none_means_all():
    """The default (``None``) keeps the ALL-categories behaviour; this is the
    production deployment invariant the pre-commit hook relies on."""
    _smp.ACTIVE_CATEGORIES = None
    assert _has_leak(_PIP_LINE) is True
    assert _has_leak(_HF_LINE) is True
    assert _has_leak(_DISPLAY_LINE) is True


def test_active_categories_filter_to_pip_only():
    """With ``ACTIVE_CATEGORIES = {"pip"}``, ONLY pip matches. This is the
    triage mode a worker would use to ship a per-category batch PR
    (e.g. pip-only, conda-only) without re-introducing cross-cat churn.

    CRITICAL: the test mutates the **module global** via ``_smp.X = ...``
    (NOT ``from strip_machine_paths import ACTIVE_CATEGORIES; X = ...``).
    The latter rebinds the **test module's local namespace** and leaves the
    module untouched — pytest's ``_has_leak`` reads the module global
    directly, so the local rebind would be a silent no-op. See L496.
    """
    _smp.ACTIVE_CATEGORIES = {"pip"}
    assert _has_leak(_PIP_LINE) is True
    assert _has_leak(_IPYKERNEL_LINE) is False  # not in filter
    assert _has_leak(_CONDA_LINE) is False
    assert _has_leak(_HF_LINE) is False
    assert _has_leak(_OTHER_LINE) is False
    # NuGet also filtered out.
    assert _has_leak(_DISPLAY_LINE) is False


def test_active_categories_filter_to_nuget_only_backwards_compat():
    """A pure-nuget filter reproduces the v1 hook behaviour exactly — proves
    the multi-cat extension does not regress the merged #6563 surface."""
    _smp.ACTIVE_CATEGORIES = {"nuget"}
    assert _has_leak(_DISPLAY_LINE) is True
    assert _has_leak(_STREAM_LINE) is True
    assert _has_leak(_PIP_LINE) is False
    assert _has_leak(_CONDA_LINE) is False


def test_active_categories_filter_multi_subset():
    """Multi-category subset (e.g. ``{nuget, pip}``) works as intersection —
    common triage for batched PRs that touch two runtimes."""
    _smp.ACTIVE_CATEGORIES = {"nuget", "pip"}
    assert _has_leak(_DISPLAY_LINE) is True
    assert _has_leak(_PIP_LINE) is True
    assert _has_leak(_IPYKERNEL_LINE) is False
    assert _has_leak(_CONDA_LINE) is False
    assert _has_leak(_HF_LINE) is False
    assert _has_leak(_OTHER_LINE) is False


def test_active_categories_unknown_label_filter():
    """An unknown category label is silently ignored (the filter intersects
    with the canonical label set, so an empty intersection means nothing
    matches — i.e. ZERO leaks, even if the line is dirty)."""
    _smp.ACTIVE_CATEGORIES = {"unknown-runtime-xyz"}
    assert _has_leak(_PIP_LINE) is False
    assert _has_leak(_DISPLAY_LINE) is False


# --- strip_in_place REDACT behaviour ------------------------------------

def test_strip_python_display_list_form_redacts_in_place(tmp_path):
    """A pip AppData leak in ``text/plain`` list-form gets REDACTed in place:
    the runtime segment + warning message survive, only the ``C:\\Users\\<u>``
    prefix is replaced with ``<USER_PATH>\\``."""
    out = _display_output(_PIP_LINE, "text/plain", form="list")
    cells = [_code(["import warnings"], outputs=[out], execution_count=11)]
    p = _write_nb(tmp_path / "redact.ipynb", cells)
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (1, 1)
    nb = json.loads(p.read_text(encoding="utf-8"))
    cell = nb["cells"][0]
    # execution_count preserved (C.2 invariant).
    assert cell["execution_count"] == 11
    # The list element got REDACTed, not dropped — the runtime segment
    # + warning message must still be present.
    redacted_line = cell["outputs"][0]["data"]["text/plain"][0]
    assert redacted_line.startswith("<USER_PATH>\\")
    assert "jsboi" not in redacted_line
    assert "AppData\\Roaming\\Python" in redacted_line
    assert "Failed to find CUDA." in redacted_line
    # Re-scan: zero leaks.
    assert count_leak_lines(p) == 0


def test_strip_python_stream_string_form_redacts(tmp_path):
    """String-form stream text gets REDACTed in place (not dropped)."""
    out = _stream_output(_PIP_LINE, form="str")
    cells = [_code(["import warnings"], outputs=[out], execution_count=12)]
    p = _write_nb(tmp_path / "stream_str.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    text = nb["cells"][0]["outputs"][0]["text"]
    assert text.startswith("<USER_PATH>\\")
    assert "jsboi" not in text
    assert count_leak_lines(p) == 0


def test_strip_python_conda_redacts_warning_kept_intact(tmp_path):
    """The conda ``UserWarning: torch.nn.utils.weight_norm is deprecated``
    pedagogical content MUST survive the strip (C534-L1 REDACT, not DROP)."""
    out = _display_output(_CONDA_LINE, "text/plain", form="list")
    cells = [_code(["import torch.nn.utils.weight_norm as wn"], outputs=[out])]
    p = _write_nb(tmp_path / "conda.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    line = nb["cells"][0]["outputs"][0]["data"]["text/plain"][0]
    assert "weight_norm is deprecated" in line  # pedagogical message preserved
    assert "jsboi" not in line
    assert "mcp-jupyter-py310" in line  # conda env name preserved
    assert count_leak_lines(p) == 0


def test_strip_nuget_drops_element_keeps_list_shape(tmp_path):
    """Backwards-compat: the NuGet branch still DROPs leak elements in
    list-form (not REDACTs) — this is the surface merged via #6567 and
    changing it would re-open the already-merged batch."""
    out = _display_output(_DISPLAY_LINE, "text/plain", form="list")
    cells = [_code(["#r \"nuget:X\""], outputs=[out], execution_count=9)]
    p = _write_nb(tmp_path / "nuget.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 1
    nb = json.loads(p.read_text(encoding="utf-8"))
    tp = nb["cells"][0]["outputs"][0]["data"]["text/plain"]
    # The NuGet leak element is DROPPED, not redacted.
    assert all("Loading extensions from" not in (l or "") for l in tp)
    assert all("jsboi" not in (l or "") for l in tp)


def test_strip_redact_idempotent(tmp_path):
    """Re-running ``strip_in_place`` on a REDACTed file is a no-op (zero
    leaks, no further mutation). Mirrors the NuGet idempotency invariant."""
    out = _display_output(_PIP_LINE, "text/plain", form="list")
    cells = [_code(["import warnings"], outputs=[out])]
    p = _write_nb(tmp_path / "idem2.ipynb", cells)
    strip_in_place(p)
    before = p.read_text(encoding="utf-8")
    outputs_with_leak, fixed = strip_in_place(p)
    assert (outputs_with_leak, fixed) == (0, 0)
    assert p.read_text(encoding="utf-8") == before


def test_strip_mixed_categories_one_cell_redact_then_drop(tmp_path):
    """Both NuGet (DROP) and pip (REDACT) leaks in the same cell: each gets
    its strategy applied. NuGet element dropped from list, pip element
    REDACTed in place."""
    out = {"output_type": "display_data",
           "data": {"text/plain": [_DISPLAY_LINE, _PIP_LINE]},
           "metadata": {}}
    cells = [_code(["mixed"], outputs=[out], execution_count=14)]
    p = _write_nb(tmp_path / "mixed.ipynb", cells)
    _, fixed = strip_in_place(p)
    assert fixed == 2
    nb = json.loads(p.read_text(encoding="utf-8"))
    tp = nb["cells"][0]["outputs"][0]["data"]["text/plain"]
    # NuGet dropped.
    assert not any("Loading extensions from" in (l or "") for l in tp)
    # pip REDACTed (preserved with username prefix gone).
    assert any(l.startswith("<USER_PATH>\\AppData\\Roaming\\Python") for l in tp)
    assert count_leak_lines(p) == 0
