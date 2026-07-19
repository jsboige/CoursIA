"""Tests for scripts/notebook_tools/regression_scan.py — notebook health-regression detector.

The module is the anti-regression scanner (temporal git-diff + CI guard for
soft output-health degradation). It was a **test orphan**: 0 ``test_`` files
repo-wide despite being critical infra (the axis-2 layer forensic_scan /
diagnose_broken miss). This suite pins the **pure, git-free** logic: output
text extraction, source detection, cell-health classification (structural +
error + soft markers), snippet windowing, and allowlist matching.

No git, no subprocess, no network — just notebook dicts and regexes.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import regression_scan as rs  # noqa: E402


# --- _scannable -------------------------------------------------------------

def test_scannable_drops_benign_lines():
    text = "mode interactif non disponible\nreal output line\nif dot program is not installed: see docs"
    out = rs._scannable(text)
    assert "real output line" in out
    assert "mode interactif non disponible" not in out
    assert "not installed" not in out


def test_scannable_keeps_all_when_no_benign():
    text = "line one\nline two\nline three"
    assert rs._scannable(text) == text


def test_scannable_empty():
    assert rs._scannable("") == ""


# --- _output_text -----------------------------------------------------------

def test_output_text_stream_list_and_str():
    cell = {"outputs": [
        {"output_type": "stream", "text": ["hello\n", "world\n"]},
        {"output_type": "stream", "text": "plain"},
    ]}
    assert "hello" in rs._output_text(cell) and "world" in rs._output_text(cell)
    assert "plain" in rs._output_text(cell)


def test_output_text_execute_result_data_keys():
    cell = {"outputs": [
        {"output_type": "execute_result", "data": {"text/plain": ["x=", "1"]}},
        {"output_type": "display_data", "data": {"text/html": "<b>hi</b>"}},
    ]}
    out = rs._output_text(cell)
    assert "x=1" in out
    assert "<b>hi</b>" in out


def test_output_text_error_payload():
    cell = {"outputs": [
        {"output_type": "error", "ename": "ValueError", "evalue": "bad",
         "traceback": ["line1", "line2"]},
    ]}
    out = rs._output_text(cell)
    assert "ValueError" in out and "bad" in out
    assert "line1" in out and "line2" in out


def test_output_text_empty_cell():
    assert rs._output_text({"outputs": []}) == ""


def test_output_text_unknown_output_type_ignored():
    cell = {"outputs": [{"output_type": "something_else", "text": "ignored"}]}
    assert rs._output_text(cell) == ""


# --- _has_source ------------------------------------------------------------

def test_has_source_list():
    assert rs._has_source({"source": ["x = 1\n", "y = 2\n"]}) is True


def test_has_source_str():
    assert rs._has_source({"source": "x = 1"}) is True


def test_has_source_whitespace_only():
    assert rs._has_source({"source": "   \n  "}) is False


def test_has_source_empty():
    assert rs._has_source({"source": ""}) is False
    assert rs._has_source({"source": []}) is False


# --- classify_cell_health ---------------------------------------------------

def _code(source, execution_count=1, outputs=None):
    return {
        "cell_type": "code",
        "source": source if isinstance(source, list) else [source],
        "execution_count": execution_count,
        "outputs": outputs or [],
    }


def test_classify_non_code_returns_empty():
    cell = {"cell_type": "markdown", "source": ["# hi"], "outputs": []}
    assert rs.classify_cell_health(cell, 0) == []


def test_classify_no_source_returns_empty():
    cell = {"cell_type": "code", "source": [], "execution_count": 1, "outputs": []}
    assert rs.classify_cell_health(cell, 0) == []


def test_classify_never_exec_marker():
    cell = _code("x = 1", execution_count=None)
    markers = rs.classify_cell_health(cell, 0)
    causes = [m["cause"] for m in markers]
    assert "NEVER_EXEC" in causes
    nev = next(m for m in markers if m["cause"] == "NEVER_EXEC")
    assert nev["severity"] == "LOW"
    assert nev["family"] == "STRUCTURAL"


def test_classify_no_output_marker():
    cell = _code("x = 1", execution_count=1, outputs=[])
    markers = rs.classify_cell_health(cell, 0)
    assert any(m["cause"] == "NO_OUTPUT" and m["severity"] == "LOW" for m in markers)


def test_classify_skip_structural_drops_both():
    cell = _code("x = 1", execution_count=None, outputs=[])
    markers = rs.classify_cell_health(cell, 0, skip_structural=True)
    causes = [m["cause"] for m in markers]
    assert "NEVER_EXEC" not in causes and "NO_OUTPUT" not in causes


def test_classify_error_output_high_severity():
    cell = _code("import missing_mod", execution_count=1, outputs=[
        {"output_type": "error", "ename": "ModuleNotFoundError",
         "evalue": "No module named 'missing_mod'", "traceback": []},
    ])
    markers = rs.classify_cell_health(cell, 0)
    errs = [m for m in markers if m["severity"] == "HIGH"]
    assert errs
    # ModuleNotFoundError -> MISSING_DEP cause via diagnose_broken ERROR_PATTERNS.
    assert any(m["cause"] == "MISSING_DEP" for m in errs)


def test_classify_soft_marker_token_starve():
    cell = _code("call_llm()", execution_count=1, outputs=[
        {"output_type": "stream", "text": 'finish_reason: "length"'},
    ])
    markers = rs.classify_cell_health(cell, 0)
    assert any(m["cause"] == "TOKEN_STARVE" for m in markers)


def test_classify_soft_marker_graphviz():
    cell = _code("render()", execution_count=1, outputs=[
        {"output_type": "stream", "text": "Graphviz non disponible"},
    ])
    markers = rs.classify_cell_health(cell, 0)
    assert any(m["cause"] == "GRAPHVIZ_PATH" for m in markers)


def test_classify_solver_downgrade_infeasible():
    cell = _code("solve()", execution_count=1, outputs=[
        {"output_type": "stream", "text": "Status: INFEASIBLE"},
    ])
    markers = rs.classify_cell_health(cell, 0)
    assert any(m["cause"] == "SOLVER_DOWNGRADE" for m in markers)


def test_classify_bare_unsat_not_flagged():
    """Bare UNSAT is the EXPECTED result in theorem-proof notebooks -> no marker."""
    cell = _code("prove()", execution_count=1, outputs=[
        {"output_type": "stream", "text": "negation = unsat => VALIDE"},
    ])
    markers = rs.classify_cell_health(cell, 0)
    assert all(m["cause"] != "SOLVER_DOWNGRADE" for m in markers)


def test_classify_healthy_cell_no_markers():
    cell = _code("print('ok')", execution_count=1, outputs=[
        {"output_type": "stream", "text": "ok\n"},
    ])
    assert rs.classify_cell_health(cell, 0) == []


def test_classify_benign_line_suppressed():
    """A benign by-design line does not produce a soft FALLBACK/TOOL_MISSING marker."""
    cell = _code("render()", execution_count=1, outputs=[
        {"output_type": "stream", "text":
            "mode interactif non disponible (batch)"},
    ])
    markers = rs.classify_cell_health(cell, 0)
    # The benign line is dropped before scanning -> no spurious marker from it.
    assert all(m["severity"] != "HIGH" or m["cause"] in ("TOKEN_STARVE", "GRAPHVIZ_PATH")
               for m in markers)


def test_classify_marker_carries_cell_index():
    cell = _code("x = 1", execution_count=None)
    markers = rs.classify_cell_health(cell, 42)
    assert all(m["cell"] == 42 for m in markers)


# --- _snippet ---------------------------------------------------------------

def test_snippet_windowed_and_truncated():
    import re
    text = "x" * 200
    m = re.search("xxx", text)
    snip = rs._snippet(text, m)
    assert len(snip) <= 90
    assert "xxx" in snip


def test_snippet_clamps_at_text_start():
    import re
    text = "match here"
    m = re.search("match", text)
    snip = rs._snippet(text, m)
    assert "match" in snip


# --- is_allowlisted ---------------------------------------------------------

def test_allowlist_match_by_path_suffix():
    allow = [{"path": "GenAI/foo.ipynb", "cause": "GRAPHVIZ_PATH"}]
    hit = rs.is_allowlisted("MyIA.AI.Notebooks/GenAI/foo.ipynb", "GRAPHVIZ_PATH", allow)
    assert hit is not None


def test_allowlist_match_backslash_path():
    allow = [{"path": "GenAI\\foo.ipynb", "cause": "GRAPHVIZ_PATH"}]
    hit = rs.is_allowlisted("MyIA.AI.Notebooks/GenAI/foo.ipynb", "GRAPHVIZ_PATH", allow)
    assert hit is not None


def test_allowlist_wildcard_cause_matches_any():
    allow = [{"path": "GenAI/foo.ipynb", "cause": "*"}]
    assert rs.is_allowlisted("GenAI/foo.ipynb", "TOKEN_STARVE", allow) is not None


def test_allowlist_none_cause_matches_any():
    allow = [{"path": "GenAI/foo.ipynb"}]  # no cause key
    assert rs.is_allowlisted("GenAI/foo.ipynb", "ANYTHING", allow) is not None


def test_allowlist_cause_list_membership():
    allow = [{"path": "GenAI/foo.ipynb", "cause": ["GRAPHVIZ_PATH", "TOOL_MISSING"]}]
    assert rs.is_allowlisted("GenAI/foo.ipynb", "TOOL_MISSING", allow) is not None
    assert rs.is_allowlisted("GenAI/foo.ipynb", "TOKEN_STARVE", allow) is None


def test_allowlist_cause_exact_mismatch():
    allow = [{"path": "GenAI/foo.ipynb", "cause": "GRAPHVIZ_PATH"}]
    assert rs.is_allowlisted("GenAI/foo.ipynb", "TOKEN_STARVE", allow) is None


def test_allowlist_no_match_returns_none():
    allow = [{"path": "Other/bar.ipynb", "cause": "*"}]
    assert rs.is_allowlisted("GenAI/foo.ipynb", "X", allow) is None


def test_allowlist_empty_returns_none():
    assert rs.is_allowlisted("any/path.ipynb", "X", []) is None
