#!/usr/bin/env python3
"""Tests for scripts/notebook_tools/regression_scan.py (axis-2 detector).

Covers the three modes (SNAPSHOT / HISTORY / GUARD) and the building blocks
that the modes compose (markers, allowlist, helpers). Pure stdlib + hermetic
subprocess mocks for git. No network. No on-disk fixtures (in-memory nb dicts
+ pytest tmp_path for allowlist).

Sibling detector pattern: matches test_check_plotly_static_risk.py / test_v4_*
co-located test conventions. The detector itself is the canonical real product
under test, not a toy re-implementation.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent
TARGET_DIR = SCRIPT_DIR.parent  # scripts/notebook_tools/
if str(TARGET_DIR) not in sys.path:
    sys.path.insert(0, str(TARGET_DIR))

import regression_scan  # noqa: E402


# --------------------------------------------------------------------------- #
# Fixtures
# --------------------------------------------------------------------------- #
def _code_cell(source="x = 1", outputs=None, execution_count=1):
    """Build a minimal code cell dict (source-as-list or string)."""
    cell = {
        "cell_type": "code",
        "source": source,
        "metadata": {},
        "execution_count": execution_count,
        "outputs": outputs or [],
    }
    return cell


def _md_cell(source="# heading"):
    return {"cell_type": "markdown", "source": source, "metadata": {}}


def _text_output(text):
    return {"output_type": "stream", "name": "stdout", "text": text}


def _display_output(text, mime="text/plain"):
    return {"output_type": "display_data", "data": {mime: text}, "metadata": {}}


def _error_output(ename="RuntimeError", evalue="boom", tb=None):
    return {
        "output_type": "error",
        "ename": ename,
        "evalue": evalue,
        "traceback": tb or [ename + ": " + evalue],
    }


def _nb(cells, qc_reference=False):
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    if qc_reference:
        nb["metadata"]["qc_reference"] = True
    return nb


# --------------------------------------------------------------------------- #
# TestConstants — module-level invariants
# --------------------------------------------------------------------------- #
class TestConstants:
    def test_sev_weight_defined(self):
        assert regression_scan.SEV_WEIGHT == {"HIGH": 4, "MED": 2, "LOW": 0}

    def test_error_category_family_maps_to_env_or_code(self):
        e2f = regression_scan.ERROR_CATEGORY_FAMILY
        # MISSING_DEP / KERNEL_ERROR / API_KEY -> ENV_DEGRADATION
        assert e2f["MISSING_DEP"] == "ENV_DEGRADATION"
        assert e2f["KERNEL_ERROR"] == "ENV_DEGRADATION"
        assert e2f["API_KEY"] == "ENV_DEGRADATION"
        # RUNTIME_ERROR / UNKNOWN -> CODE_ERROR
        assert e2f["RUNTIME_ERROR"] == "CODE_ERROR"
        assert e2f["UNKNOWN"] == "CODE_ERROR"

    def test_soft_markers_count_at_least_8(self):
        # 10 causes documented: TOKEN_STARVE, GRAPHVIZ_PATH, TOOL_MISSING,
        # MISSING_DEP, API_ENDPOINT, SOLVER_DOWNGRADE, FALLBACK + 3 variants.
        assert len(regression_scan.SOFT_MARKERS) >= 8

    def test_soft_markers_compiled(self):
        for entry in regression_scan.SOFT_MARKERS:
            rx, cause, family, sev = entry
            assert hasattr(rx, "search"), f"{cause} regex not compiled"
            assert cause in regression_scan.REPAIR_HINT, f"{cause} missing REPAIR_HINT"
            assert sev in ("HIGH", "MED", "LOW"), f"{cause} bad severity {sev!r}"

    def test_soft_markers_causes_cover_documented_set(self):
        causes = {c for _, c, _, _ in regression_scan.SOFT_MARKERS}
        # Expected core set
        assert "TOKEN_STARVE" in causes
        assert "GRAPHVIZ_PATH" in causes
        assert "MISSING_DEP" in causes
        assert "API_ENDPOINT" in causes
        assert "SOLVER_DOWNGRADE" in causes
        assert "FALLBACK" in causes

    def test_benign_line_compiled(self):
        assert hasattr(regression_scan.BENIGN_LINE, "search")
        # Benign line: "execution non-interactive"
        assert regression_scan.BENIGN_LINE.search("execution non-interactive")

    def test_caveat_prose_compiled(self):
        assert hasattr(regression_scan.CAVEAT_PROSE, "search")
        assert regression_scan.CAVEAT_PROSE.search("MiniZinc non disponible")

    def test_abspath_marker_compiled_and_matches(self):
        assert hasattr(regression_scan.ABSPATH_MARKER, "search")
        # Windows absolute path
        assert regression_scan.ABSPATH_MARKER.search(r"C:\Users\jsboi\notebook.ipynb")
        # Linux absolute path
        assert regression_scan.ABSPATH_MARKER.search("/mnt/c/Users/foo/x.ipynb")
        # WSL
        assert regression_scan.ABSPATH_MARKER.search("/home/jsboige/AppData/x.ipynb")
        # Papermill tmp
        assert regression_scan.ABSPATH_MARKER.search("/tmp/abc123-papermill.ipynb")
        # Plain relative path -> NO match
        assert not regression_scan.ABSPATH_MARKER.search("MyIA.AI.Notebooks/foo.ipynb")

    def test_repair_hint_keys_match_soft_markers_and_structurals(self):
        # Repair hint MUST cover all soft-marker causes + NEVER_EXEC/NO_OUTPUT/PAPERMILL_ABSPATH
        causes = {c for _, c, _, _ in regression_scan.SOFT_MARKERS}
        causes.update(["NEVER_EXEC", "NO_OUTPUT", "PAPERMILL_ABSPATH"])
        for cause in causes:
            assert cause in regression_scan.REPAIR_HINT, f"missing REPAIR_HINT for {cause}"
            assert isinstance(regression_scan.REPAIR_HINT[cause], str)
            assert regression_scan.REPAIR_HINT[cause].strip()

    def test_repair_hint_excludes_unknown_cause(self):
        # Sanity: unknown causes return '-' in render_snapshot, REPAIR_HINT
        # does NOT have to list them. Confirm no false claim.
        assert "FAKE_CAUSE" not in regression_scan.REPAIR_HINT


# --------------------------------------------------------------------------- #
# TestScannable — benign-line drop helper
# --------------------------------------------------------------------------- #
class TestScannable:
    def test_drops_benign_line(self):
        text = "import os\nmode interactif non disponible\nprint('x')"
        out = regression_scan._scannable(text)
        assert "mode interactif non disponible" not in out
        assert "import os" in out
        assert "print('x')" in out

    def test_drops_non_interactive_french(self):
        text = "exécution non-interactive"
        out = regression_scan._scannable(text)
        assert "non-interactive" not in out

    def test_keeps_non_benign_lines(self):
        text = "Graphviz non disponible"
        out = regression_scan._scannable(text)
        # "Graphviz non disponible" is NOT in the BENIGN_LINE drop list
        assert "Graphviz non disponible" in out

    def test_empty_input(self):
        assert regression_scan._scannable("") == ""

    def test_preserves_other_lines(self):
        text = "import numpy\nfallback to numpy\n# TODO fix"
        out = regression_scan._scannable(text)
        assert "fallback to numpy" in out  # 'fallback' is a SOFT marker, not benign


# --------------------------------------------------------------------------- #
# TestOutputText — concat outputs helper
# --------------------------------------------------------------------------- #
class TestOutputText:
    def test_stream_output_string(self):
        cell = _code_cell(outputs=[_text_output("hello\n")])
        text = regression_scan._output_text(cell)
        assert "hello" in text

    def test_stream_output_list(self):
        cell = _code_cell(outputs=[_text_output(["line1\n", "line2\n"])])
        text = regression_scan._output_text(cell)
        assert "line1" in text
        assert "line2" in text

    def test_display_data_text_plain(self):
        cell = _code_cell(outputs=[_display_output("42", mime="text/plain")])
        text = regression_scan._output_text(cell)
        assert "42" in text

    def test_display_data_html_ignored_for_text_extraction(self):
        # _output_text only extracts text/plain/markdown/html payload
        cell = _code_cell(outputs=[_display_output("<svg/>", mime="image/svg+xml")])
        text = regression_scan._output_text(cell)
        # image/svg+xml not in extract list
        assert text.strip() == ""

    def test_error_output_extracts_ename_evalue_tb(self):
        cell = _code_cell(outputs=[_error_output("ValueError", "bad value", ["tb1", "tb2"])])
        text = regression_scan._output_text(cell)
        assert "ValueError" in text
        assert "bad value" in text
        assert "tb1" in text

    def test_multiple_outputs_concatenated(self):
        cell = _code_cell(outputs=[
            _text_output("stdout line\n"),
            _display_output("answer = 42", mime="text/plain"),
            _error_output("E", "msg", ["trace"]),
        ])
        text = regression_scan._output_text(cell)
        assert "stdout line" in text
        assert "answer = 42" in text
        assert "E" in text

    def test_empty_outputs(self):
        cell = _code_cell(outputs=[])
        assert regression_scan._output_text(cell) == ""

    def test_missing_outputs_key(self):
        cell = {"cell_type": "code", "source": "x = 1"}
        assert regression_scan._output_text(cell) == ""


# --------------------------------------------------------------------------- #
# TestHasSource
# --------------------------------------------------------------------------- #
class TestHasSource:
    def test_string_source_nonempty(self):
        assert regression_scan._has_source({"source": "x = 1"})

    def test_string_source_whitespace(self):
        assert not regression_scan._has_source({"source": "   \n  "})

    def test_list_source_nonempty(self):
        assert regression_scan._has_source({"source": ["x = 1\n", "y = 2"]})

    def test_list_source_empty(self):
        assert not regression_scan._has_source({"source": ["", ""]})

    def test_missing_source(self):
        assert not regression_scan._has_source({})


# --------------------------------------------------------------------------- #
# TestSnippet — match context window
# --------------------------------------------------------------------------- #
class TestSnippet:
    def test_snippet_window_size(self):
        text = "a" * 100 + "TOKEN_STARVE" + "b" * 100
        m = regression_scan.SOFT_MARKERS[0][0]  # TOKEN_STARVE pattern
        # Find TOKEN_STARVE in text manually
        import re as _re
        match = _re.search("content.*None", text) or m.search(text)
        if match is None:
            # Manually construct
            import re as _re2
            match = _re2.search("TOKEN_STARVE", text)
        snippet = regression_scan._snippet(text, match)
        assert len(snippet) <= 90 + 6  # +6 for newline replace etc.

    def test_snippet_replaces_newlines(self):
        text = "line1\nline2\nline3\nMATCH\nline4\nline5"
        import re
        match = re.search("MATCH", text)
        snippet = regression_scan._snippet(text, match)
        assert "\n" not in snippet
        assert "MATCH" in snippet

    def test_snippet_at_start(self):
        text = "MATCH_and_more_text_here_continued_long"
        import re
        match = re.search("MATCH", text)
        snippet = regression_scan._snippet(text, match)
        assert snippet.startswith("MATCH")


# --------------------------------------------------------------------------- #
# TestClassifyCellHealth
# --------------------------------------------------------------------------- #
class TestClassifyCellHealth:
    def test_markdown_cell_returns_empty(self):
        cell = _md_cell("# hi")
        markers = regression_scan.classify_cell_health(cell, 0)
        assert markers == []

    def test_empty_source_returns_empty(self):
        cell = _code_cell(source="   \n  ", outputs=[])
        markers = regression_scan.classify_cell_health(cell, 0)
        assert markers == []

    def test_never_exec_emits_low_structural(self):
        cell = _code_cell(source="x = 1", outputs=[], execution_count=None)
        markers = regression_scan.classify_cell_health(cell, 0)
        assert any(m["cause"] == "NEVER_EXEC" and m["severity"] == "LOW" for m in markers)

    def test_no_output_emits_low_structural(self):
        cell = _code_cell(source="x = 1", outputs=[], execution_count=1)
        markers = regression_scan.classify_cell_health(cell, 0)
        assert any(m["cause"] == "NO_OUTPUT" and m["severity"] == "LOW" for m in markers)

    def test_skip_structural_suppresses_never_exec(self):
        cell = _code_cell(source="x = 1", outputs=[], execution_count=None)
        markers = regression_scan.classify_cell_health(cell, 0, skip_structural=True)
        assert not any(m["cause"] == "NEVER_EXEC" for m in markers)

    def test_hard_error_emits_high(self):
        cell = _code_cell(source="1/0", outputs=[_error_output("ZeroDivisionError", "div by 0")], execution_count=1)
        markers = regression_scan.classify_cell_health(cell, 0)
        assert any(m["severity"] == "HIGH" and m["family"] in ("CODE_ERROR", "ENV_DEGRADATION") for m in markers)

    @pytest.mark.parametrize("output_text,expected_cause", [
        ("finish_reason: 'length'", "TOKEN_STARVE"),
        ("content = None", "TOKEN_STARVE"),
        ("<empty> result", "TOKEN_STARVE"),
        ("Graphviz non disponible", "GRAPHVIZ_PATH"),
        ("Rendu Graphviz failed", "GRAPHVIZ_PATH"),
        ("MiniZinc non disponible", "TOOL_MISSING"),
        ("JVM non disponible", "TOOL_MISSING"),
        ("Tweety non disponible", "TOOL_MISSING"),
        ("ImportError: no module", "MISSING_DEP"),
        ("ModuleNotFoundError: foo", "MISSING_DEP"),
        ("No module named 'x'", "MISSING_DEP"),
        ("Solution valide = False", "SOLVER_DOWNGRADE"),
        ("is_valid() = False", "SOLVER_DOWNGRADE"),
        ("INFEASIBLE", "SOLVER_DOWNGRADE"),
        ("Skipped", "TOOL_MISSING"),
        ("fallback to numpy", "FALLBACK"),
        ("falling back to cached", "FALLBACK"),
        ("mode dégradé", "FALLBACK"),
    ])
    def test_soft_marker_patterns_detected(self, output_text, expected_cause):
        cell = _code_cell(
            source="print('x')",
            outputs=[_text_output(output_text)],
            execution_count=1,
        )
        markers = regression_scan.classify_cell_health(cell, 0)
        assert any(m["cause"] == expected_cause for m in markers), \
            f"expected {expected_cause} for {output_text!r}, got {[m['cause'] for m in markers]}"

    def test_soft_marker_benign_dropped(self):
        # 'execution non-interactive' is a benign line, MUST be dropped
        cell = _code_cell(
            source="print('x')",
            outputs=[_text_output("execution non-interactive")],
            execution_count=1,
        )
        markers = regression_scan.classify_cell_health(cell, 0)
        # After drop, no markers from output text
        soft = [m for m in markers if m["cause"] not in ("NEVER_EXEC", "NO_OUTPUT")]
        assert soft == []

    def test_snippet_included_for_soft_marker(self):
        cell = _code_cell(
            source="x = 1",
            outputs=[_text_output("Graphviz non disponible: please install")],
            execution_count=1,
        )
        markers = regression_scan.classify_cell_health(cell, 0)
        graph = [m for m in markers if m["cause"] == "GRAPHVIZ_PATH"]
        assert len(graph) == 1
        assert "snippet" in graph[0]
        assert "Graphviz" in graph[0]["snippet"]


# --------------------------------------------------------------------------- #
# TestNotebookHealth — aggregate, worst wins, ACKNOWLEDGED verdict
# --------------------------------------------------------------------------- #
class TestNotebookHealth:
    def test_empty_notebook_healthy(self):
        nb = _nb([])
        h = regression_scan.notebook_health(nb)
        assert h["verdict"] == "HEALTHY"
        assert h["score"] == 0
        assert h["causes"] == []
        assert h["families"] == []

    def test_healthy_code_cell_no_markers(self):
        nb = _nb([_code_cell(source="x = 1", outputs=[_text_output("ok")], execution_count=1)])
        h = regression_scan.notebook_health(nb)
        assert h["verdict"] == "HEALTHY"

    def test_high_marker_makes_degraded(self):
        nb = _nb([_code_cell(
            source="x = 1",
            outputs=[_error_output("ImportError", "No module", ["tb"])],
            execution_count=1,
        )])
        h = regression_scan.notebook_health(nb)
        assert h["verdict"] == "DEGRADED"
        assert h["score"] > 0
        assert "MISSING_DEP" in h["causes"] or "UNKNOWN" in h["causes"]

    def test_med_marker_makes_degraded(self):
        nb = _nb([_code_cell(
            source="x = 1",
            outputs=[_text_output("fallback to degraded mode")],
            execution_count=1,
        )])
        h = regression_scan.notebook_health(nb)
        assert h["verdict"] == "DEGRADED"
        assert "FALLBACK" in h["causes"]

    def test_low_only_structural_healthy(self):
        # NEVER_EXEC + NO_OUTPUT alone = LOW severity, does NOT flip to DEGRADED
        nb = _nb([
            _code_cell(source="x = 1", outputs=[], execution_count=None),
            _code_cell(source="y = 2", outputs=[], execution_count=1),
        ])
        h = regression_scan.notebook_health(nb)
        # All structural causes are LOW -> verdict remains HEALTHY
        assert h["verdict"] == "HEALTHY"

    def test_qc_reference_skips_structural(self):
        # QC quantbook: never-executed is BY DESIGN, structural markers dropped
        nb = _nb(
            [_code_cell(source="x = 1", outputs=[], execution_count=None)],
            qc_reference=True,
        )
        h = regression_scan.notebook_health(nb)
        assert h["verdict"] == "HEALTHY"

    def test_md_caveat_counted(self):
        nb = _nb([
            _code_cell(source="x = 1", outputs=[_text_output("ok")], execution_count=1),
            _md_cell("# Caveat: MiniZinc non disponible"),
        ])
        h = regression_scan.notebook_health(nb)
        assert h["md_caveats"] >= 1

    def test_abspath_marker_detected(self):
        # Pass raw JSON containing an absolute machine path
        raw = json.dumps({"cells": [{"cell_type": "code", "source": "x = 1", "metadata": {}}]}) + \
              " C:\\Users\\jsboi\\path.ipynb"
        nb = _nb([])
        h = regression_scan.notebook_health(nb, raw=raw)
        assert any(m["cause"] == "PAPERMILL_ABSPATH" for m in h["markers"])

    def test_no_abspath_no_marker(self):
        raw = json.dumps({"cells": []})
        nb = _nb([])
        h = regression_scan.notebook_health(nb, raw=raw)
        assert not any(m["cause"] == "PAPERMILL_ABSPATH" for m in h["markers"])

    def test_worst_cell_wins(self):
        # Two cells: one low, one high. Verdict = DEGRADED (worst wins).
        nb = _nb([
            _code_cell(source="x = 1", outputs=[], execution_count=None),  # LOW
            _code_cell(source="y = 2", outputs=[_error_output("X", "Y", ["z"])], execution_count=1),  # HIGH
        ])
        h = regression_scan.notebook_health(nb)
        assert h["verdict"] == "DEGRADED"


# --------------------------------------------------------------------------- #
# TestAllowlist — load + is_allowlisted
# --------------------------------------------------------------------------- #
class TestAllowlist:
    def test_load_allowlist_missing_file(self, tmp_path, monkeypatch):
        # Patch ALLOWLIST_PATH to a missing path
        monkeypatch.setattr(regression_scan, "ALLOWLIST_PATH", tmp_path / "absent.json")
        assert regression_scan.load_allowlist() == []

    def test_load_allowlist_malformed_json(self, tmp_path, monkeypatch):
        path = tmp_path / "allowlist.json"
        path.write_text("{ not valid json")
        monkeypatch.setattr(regression_scan, "ALLOWLIST_PATH", path)
        assert regression_scan.load_allowlist() == []

    def test_load_allowlist_dict_with_acknowledged(self, tmp_path, monkeypatch):
        path = tmp_path / "allowlist.json"
        path.write_text(json.dumps({"acknowledged": [{"path": "foo/bar.ipynb", "cause": "MISSING_DEP"}]}))
        monkeypatch.setattr(regression_scan, "ALLOWLIST_PATH", path)
        result = regression_scan.load_allowlist()
        assert len(result) == 1
        assert result[0]["path"] == "foo/bar.ipynb"

    def test_load_allowlist_list_form(self, tmp_path, monkeypatch):
        path = tmp_path / "allowlist.json"
        path.write_text(json.dumps([{"path": "x", "cause": "*"}]))
        monkeypatch.setattr(regression_scan, "ALLOWLIST_PATH", path)
        result = regression_scan.load_allowlist()
        assert len(result) == 1

    def test_is_allowlisted_no_match(self):
        allow = [{"path": "foo/bar.ipynb", "cause": "MISSING_DEP"}]
        assert regression_scan.is_allowlisted("other.ipynb", "MISSING_DEP", allow) is None

    def test_is_allowlisted_path_match_cause_match(self):
        allow = [{"path": "foo/bar.ipynb", "cause": "MISSING_DEP"}]
        result = regression_scan.is_allowlisted("foo/bar.ipynb", "MISSING_DEP", allow)
        assert result == allow[0]

    def test_is_allowlisted_path_match_wildcard_cause(self):
        allow = [{"path": "foo/bar.ipynb", "cause": "*"}]
        result = regression_scan.is_allowlisted("foo/bar.ipynb", "ANYTHING", allow)
        assert result == allow[0]

    def test_is_allowlisted_windows_path_normalization(self):
        allow = [{"path": "foo\\bar.ipynb", "cause": "MISSING_DEP"}]
        result = regression_scan.is_allowlisted("foo/bar.ipynb", "MISSING_DEP", allow)
        assert result == allow[0]

    def test_is_allowlisted_partial_path_match(self):
        # Suffix match: allowlist path "/bar.ipynb" matches relpath "foo/bar.ipynb"
        allow = [{"path": "/bar.ipynb", "cause": "X"}]
        result = regression_scan.is_allowlisted("foo/bar.ipynb", "X", allow)
        assert result == allow[0]

    def test_is_allowlisted_cause_list_form(self):
        allow = [{"path": "foo/bar.ipynb", "cause": ["A", "B", "C"]}]
        assert regression_scan.is_allowlisted("foo/bar.ipynb", "B", allow) == allow[0]
        assert regression_scan.is_allowlisted("foo/bar.ipynb", "D", allow) is None


# --------------------------------------------------------------------------- #
# TestDiscover
# --------------------------------------------------------------------------- #
class TestDiscover:
    def test_discover_finds_ipynb(self, tmp_path):
        (tmp_path / "a.ipynb").write_text("{}")
        (tmp_path / "b.ipynb").write_text("{}")
        (tmp_path / "c.txt").write_text("not notebook")
        result = regression_scan.discover(tmp_path, series=None)
        names = sorted(p.name for p in result)
        assert "a.ipynb" in names
        assert "b.ipynb" in names
        assert "c.txt" not in names

    def test_discover_excludes_forensic_scan_excluded_dirs(self, tmp_path):
        # EXCLUDE_DIRS comes from forensic_scan sibling
        # Simulate excluded dir (e.g. _output papermill artifacts)
        excluded = tmp_path / ".ipynb_checkpoints"
        excluded.mkdir()
        (excluded / "x.ipynb").write_text("{}")
        kept = tmp_path / "y.ipynb"
        kept.write_text("{}")
        result = regression_scan.discover(tmp_path, series=None)
        names = [p.name for p in result]
        assert "x.ipynb" not in names
        assert "y.ipynb" in names


# --------------------------------------------------------------------------- #
# TestRel — relative path helper
# --------------------------------------------------------------------------- #
class TestRel:
    def test_rel_within_repo(self, tmp_path, monkeypatch):
        # Patch REPO_ROOT so .resolve().relative_to() works
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path)
        nb = tmp_path / "foo" / "bar.ipynb"
        nb.parent.mkdir()
        nb.write_text("{}")
        assert regression_scan.rel(nb) == "foo/bar.ipynb"

    def test_rel_outside_repo_fallback(self, tmp_path, monkeypatch):
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path / "elsewhere")
        nb = tmp_path / "bar.ipynb"
        nb.write_text("{}")
        # Path.resolve().relative_to() raises ValueError -> fallback to as_posix
        result = regression_scan.rel(nb)
        assert "bar.ipynb" in result


# --------------------------------------------------------------------------- #
# TestRenderSnapshot — markdown output format
# --------------------------------------------------------------------------- #
class TestRenderSnapshot:
    def test_render_snapshot_header(self):
        data = {"results": []}
        out = regression_scan.render_snapshot(data)
        assert "Notebook health snapshot (axis-2)" in out
        assert "DEGRADED: 0" in out
        assert "HEALTHY: 0" in out

    def test_render_snapshot_degraded_table(self):
        results = [{
            "verdict": "DEGRADED", "score": 4, "n_markers": 1,
            "markers": [{"cell": 0, "cause": "MISSING_DEP", "family": "ENV_DEGRADATION", "severity": "HIGH"}],
            "causes": ["MISSING_DEP"], "families": ["ENV_DEGRADATION"],
            "md_caveats": 0, "path": "foo/x.ipynb", "series": "Test",
            "acknowledged": [],
        }]
        data = {"results": results}
        out = regression_scan.render_snapshot(data)
        assert "DEGRADED: 1" in out
        assert "ENV_DEGRADATION" in out
        assert "MISSING_DEP" in out
        assert "x.ipynb" in out

    def test_render_snapshot_includes_repair_hint(self):
        results = [{
            "verdict": "DEGRADED", "score": 4, "n_markers": 1,
            "markers": [{"cell": 0, "cause": "GRAPHVIZ_PATH", "family": "ENV_DEGRADATION", "severity": "HIGH"}],
            "causes": ["GRAPHVIZ_PATH"], "families": ["ENV_DEGRADATION"],
            "md_caveats": 0, "path": "p/x.ipynb", "series": "S", "acknowledged": [],
        }]
        data = {"results": results}
        out = regression_scan.render_snapshot(data)
        # Repair hint for GRAPHVIZ_PATH
        assert "FactorGraphHelper" in out or "put dot on PATH" in out

    def test_render_snapshot_acknowledged_section(self):
        results = [{
            "verdict": "ACKNOWLEDGED", "score": 4, "n_markers": 1,
            "markers": [{"cell": 0, "cause": "MISSING_DEP", "family": "ENV_DEGRADATION", "severity": "HIGH"}],
            "causes": ["MISSING_DEP"], "families": ["ENV_DEGRADATION"],
            "md_caveats": 0, "path": "ack/y.ipynb", "series": "S",
            "acknowledged": ["MISSING_DEP"],
        }]
        data = {"results": results}
        out = regression_scan.render_snapshot(data)
        assert "Acknowledged" in out
        assert "ack/y.ipynb" in out

    def test_render_snapshot_axis_disclaimer(self):
        data = {"results": []}
        out = regression_scan.render_snapshot(data)
        assert "axis-1" in out
        assert "not judged" in out


# --------------------------------------------------------------------------- #
# TestRenderHistory
# --------------------------------------------------------------------------- #
class TestRenderHistory:
    def test_render_history_header(self):
        data = {"results": []}
        out = regression_scan.render_history(data)
        assert "Notebook regression history" in out
        assert "still degraded at HEAD" in out

    def test_render_history_still_degraded_section(self):
        results = [{
            "path": "foo/x.ipynb", "series": "S", "current_score": 4,
            "current_verdict": "DEGRADED", "current_causes": ["MISSING_DEP"],
            "n_revisions": 3, "transitions": [
                {"kind": "REGRESSION", "sha": "abc123456", "date": "2026-01-01",
                 "author": "dev", "added": ["MISSING_DEP"], "score": "0->4"},
            ],
            "regressions": [
                {"kind": "REGRESSION", "sha": "abc123456", "date": "2026-01-01",
                 "author": "dev", "added": ["MISSING_DEP"], "score": "0->4"},
            ],
        }]
        data = {"results": results}
        out = regression_scan.render_history(data)
        assert "STILL DEGRADED at HEAD" in out
        assert "MISSING_DEP" in out
        assert "abc12345" in out  # short sha
        assert "foo/x.ipynb" in out

    def test_render_history_repaired_section(self):
        results = [{
            "path": "bar/y.ipynb", "series": "S", "current_score": 0,
            "current_verdict": "HEALTHY", "current_causes": [],
            "n_revisions": 2, "transitions": [
                {"kind": "RECOVERY", "sha": "def456789", "date": "2026-02-01",
                 "author": "dev", "removed": ["GRAPHVIZ_PATH"], "score": "4->0"},
            ],
            "regressions": [],
        }]
        data = {"results": results}
        out = regression_scan.render_history(data)
        assert "Repaired since" in out
        assert "bar/y.ipynb" in out


# --------------------------------------------------------------------------- #
# TestRunGuard — CI gate
# --------------------------------------------------------------------------- #
class TestRunGuard:
    def _stub_health(self, base_score=0, head_score=0, head_cause=None):
        """Returns (notebook_health, git_show_notebook) fakes wired together.

        run_guard calls notebook_health in this order:
          1. head_h = notebook_health(head_nb, head_raw)
          2. base_score = notebook_health(base_nb, base_raw)['score'] if base_nb else 0
        So fake_health.n == 1 == HEAD, n == 2 == BASE.
        """
        def fake_health(nb, raw=None):
            fake_health.n += 1
            if fake_health.n == 1:
                # HEAD
                markers = []
                if head_cause and head_score > 0:
                    markers = [{
                        "cell": 0, "cause": head_cause,
                        "family": "ENV_DEGRADATION", "severity": "HIGH",
                    }]
                return {"score": head_score, "markers": markers,
                        "verdict": "DEGRADED" if head_score > 0 else "HEALTHY"}
            # BASE
            return {"score": base_score, "markers": [], "verdict": "HEALTHY"}
        fake_health.n = 0

        def fake_git_show(rev, relpath):
            return {"cells": []}, "{}"
        return fake_health, fake_git_show

    def test_guard_no_failures_returns_zero(self, monkeypatch):
        fake_health, fake_git_show = self._stub_health(head_score=0)
        monkeypatch.setattr(regression_scan, "notebook_health", fake_health)
        monkeypatch.setattr(regression_scan, "git_show_notebook", fake_git_show)
        result = regression_scan.run_guard(
            base="base_sha", head="head_sha",
            paths=["foo/x.ipynb"],
            allow=[],
        )
        assert result == 0
        assert fake_health.n == 2  # base + head

    def test_guard_health_to_degraded_fails(self, monkeypatch):
        fake_health, fake_git_show = self._stub_health(
            base_score=0, head_score=4, head_cause="MISSING_DEP",
        )
        monkeypatch.setattr(regression_scan, "notebook_health", fake_health)
        monkeypatch.setattr(regression_scan, "git_show_notebook", fake_git_show)
        result = regression_scan.run_guard(
            base="base_sha", head="head_sha",
            paths=["foo/x.ipynb"],
            allow=[],
        )
        assert result == 1

    def test_guard_allowlisted_regression_passes(self, monkeypatch, tmp_path):
        # Allowlist the path+cause -> guard passes despite regression
        allow_path = tmp_path / "allowlist.json"
        allow_path.write_text(json.dumps({"acknowledged": [
            {"path": "foo/x.ipynb", "cause": "*"}
        ]}))
        monkeypatch.setattr(regression_scan, "ALLOWLIST_PATH", allow_path)
        fake_health, fake_git_show = self._stub_health(
            base_score=0, head_score=4, head_cause="MISSING_DEP",
        )
        monkeypatch.setattr(regression_scan, "notebook_health", fake_health)
        monkeypatch.setattr(regression_scan, "git_show_notebook", fake_git_show)
        result = regression_scan.run_guard(
            base="base_sha", head="head_sha",
            paths=["foo/x.ipynb"],
            allow=regression_scan.load_allowlist(),
        )
        assert result == 0

    def test_guard_skips_catalog_paths(self, monkeypatch):
        calls = []
        def fake_health(nb, raw=None):
            calls.append("called")
            return {"score": 4, "markers": [], "verdict": "DEGRADED"}
        monkeypatch.setattr(regression_scan, "notebook_health", fake_health)
        # COURSE_CATALOG and CATALOG-STATUS marker paths MUST be skipped
        result = regression_scan.run_guard(
            base="base_sha", head="head_sha",
            paths=["COURSE_CATALOG.generated.md", "MyIA.AI.Notebooks/README.md"],
            allow=[],
        )
        assert result == 0
        assert calls == []  # skipped entirely

    def test_guard_empty_paths_returns_zero(self, monkeypatch):
        result = regression_scan.run_guard(
            base="base_sha", head="head_sha", paths=[], allow=[],
        )
        assert result == 0


# --------------------------------------------------------------------------- #
# TestRunSnapshot
# --------------------------------------------------------------------------- #
class TestRunSnapshot:
    def test_run_snapshot_scans_ipynb(self, tmp_path, monkeypatch):
        # Create a notebook with a degraded output
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps(_nb([
            _code_cell(source="x = 1", outputs=[_error_output("ImportError", "No module", ["tb"])], execution_count=1),
        ])))
        monkeypatch.setattr(regression_scan, "NOTEBOOKS_DIR", tmp_path)
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path)

        result = regression_scan.run_snapshot(tmp_path, series=None, allow=[], git_tracked_only=False)
        assert len(result["results"]) == 1
        assert result["results"][0]["verdict"] == "DEGRADED"

    def test_run_snapshot_skips_malformed_json(self, tmp_path, monkeypatch):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("not valid json")
        monkeypatch.setattr(regression_scan, "NOTEBOOKS_DIR", tmp_path)
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path)
        result = regression_scan.run_snapshot(tmp_path, series=None, allow=[], git_tracked_only=False)
        assert result["results"] == []


# --------------------------------------------------------------------------- #
# TestMain — CLI exit codes
# --------------------------------------------------------------------------- #
class TestMain:
    def test_main_guard_requires_base(self, capsys, monkeypatch):
        # main() returns 2 + prints to stderr (no SystemExit raised — argparse default)
        monkeypatch.setattr(regression_scan, "load_allowlist", lambda: [])
        with patch("sys.argv", ["prog", "--guard"]):
            rc = regression_scan.main()
            assert rc == 2
            captured = capsys.readouterr()
            assert "--guard requires --base" in captured.err

    def test_main_snapshot_default(self, tmp_path, monkeypatch, capsys):
        # No notebooks in tmp_path -> SNAPSHOT prints empty report
        monkeypatch.setattr(regression_scan, "NOTEBOOKS_DIR", tmp_path)
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path)
        monkeypatch.setattr(regression_scan, "load_allowlist", lambda: [])
        with patch("sys.argv", ["prog", "--root", str(tmp_path)]):
            rc = regression_scan.main()
            assert rc == 0
            captured = capsys.readouterr()
            assert "Notebook health snapshot" in captured.out

    def test_main_json_output(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(regression_scan, "NOTEBOOKS_DIR", tmp_path)
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path)
        monkeypatch.setattr(regression_scan, "load_allowlist", lambda: [])
        json_path = tmp_path / "out.json"
        with patch("sys.argv", ["prog", "--root", str(tmp_path), "--json", str(json_path)]):
            rc = regression_scan.main()
            assert rc == 0
            assert json_path.exists()
            data = json.loads(json_path.read_text())
            assert "results" in data


# --------------------------------------------------------------------------- #
# TestGitHelpers — subprocess mocked
# --------------------------------------------------------------------------- #
class TestGitRevisions:
    def test_git_revisions_parses_output(self, monkeypatch):
        fake_output = "abc123\x1f2026-01-01T00:00:00+00:00\x1falice\ndef456\x1f2026-02-01\x1fbob\n"
        cp = subprocess.CompletedProcess(args=[], returncode=0, stdout=fake_output, stderr="")
        monkeypatch.setattr(regression_scan, "_git", lambda args: cp)
        revs = regression_scan.git_revisions("foo.ipynb")
        assert len(revs) == 2
        assert revs[0]["sha"] == "abc123"
        assert revs[0]["date"] == "2026-01-01T00:00:00+00:00"
        assert revs[0]["author"] == "alice"
        assert revs[1]["author"] == "bob"

    def test_git_revisions_empty(self, monkeypatch):
        cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
        monkeypatch.setattr(regression_scan, "_git", lambda args: cp)
        revs = regression_scan.git_revisions("foo.ipynb")
        assert revs == []

    def test_git_revisions_malformed_line(self, monkeypatch):
        cp = subprocess.CompletedProcess(
            args=[], returncode=0,
            stdout="only_two\x1fparts\n",
            stderr="")
        monkeypatch.setattr(regression_scan, "_git", lambda args: cp)
        revs = regression_scan.git_revisions("foo.ipynb")
        assert revs == []


class TestGitShowNotebook:
    def test_parses_json(self, monkeypatch):
        nb = _nb([_code_cell(source="x = 1", outputs=[_text_output("ok")], execution_count=1)])
        cp = subprocess.CompletedProcess(args=[], returncode=0, stdout=json.dumps(nb), stderr="")
        monkeypatch.setattr(regression_scan, "_git", lambda args: cp)
        parsed, raw = regression_scan.git_show_notebook("sha", "foo.ipynb")
        assert parsed is not None
        assert raw is not None
        assert len(parsed["cells"]) == 1

    def test_returns_none_on_nonzero(self, monkeypatch):
        cp = subprocess.CompletedProcess(args=[], returncode=1, stdout="", stderr="err")
        monkeypatch.setattr(regression_scan, "_git", lambda args: cp)
        parsed, raw = regression_scan.git_show_notebook("sha", "foo.ipynb")
        assert parsed is None
        assert raw is None

    def test_returns_none_on_invalid_json(self, monkeypatch):
        cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="not json", stderr="")
        monkeypatch.setattr(regression_scan, "_git", lambda args: cp)
        parsed, raw = regression_scan.git_show_notebook("sha", "foo.ipynb")
        assert parsed is None
        assert raw is None


# --------------------------------------------------------------------------- #
# TestRunHistory
# --------------------------------------------------------------------------- #
class TestRunHistory:
    def test_run_history_returns_results(self, tmp_path, monkeypatch):
        # Empty notebooks dir -> empty results
        monkeypatch.setattr(regression_scan, "NOTEBOOKS_DIR", tmp_path)
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path)
        result = regression_scan.run_history(
            root=tmp_path, series=None, since=None, workers=2,
            git_tracked_only=False,
        )
        assert "results" in result
        assert result["results"] == []

    def test_run_history_skips_always_healthy(self, tmp_path, monkeypatch):
        # Notebook that is ALWAYS healthy -> filtered out (timeline[-1]['score'] == 0 and no regressions)
        # Simplest path: empty timeline -> _walk_one returns None
        monkeypatch.setattr(regression_scan, "NOTEBOOKS_DIR", tmp_path)
        monkeypatch.setattr(regression_scan, "REPO_ROOT", tmp_path)
        nb = tmp_path / "x.ipynb"
        nb.write_text(json.dumps(_nb([_code_cell(source="x = 1", outputs=[_text_output("ok")], execution_count=1)])))
        # git_revisions returns empty (no commits in tmp_path)
        monkeypatch.setattr(regression_scan, "git_revisions", lambda *args, **kwargs: [])
        result = regression_scan.run_history(
            root=tmp_path, series=None, since=None, workers=1,
            git_tracked_only=False,
        )
        assert result["results"] == []


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))