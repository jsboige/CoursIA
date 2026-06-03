"""Tests for generate_catalog.py and expand_catalog_markers.py.

Covers pure functions from the catalog generation pipeline:
- estimate_duration, check_errors, determine_status, classify_maturity
- count_todos, _is_exercise_stub, _is_outputless_by_design
- extract_title, detect_requirements, has_markdown_intro_conclusion
- compute_counter, compute_breakdown, compute_maturity_distribution
- format_catalog_status_block, expand_file
"""

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

# Add paths so we can import the modules
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from generate_catalog import (
    estimate_duration,
    check_errors,
    determine_status,
    classify_maturity,
    count_todos,
    _is_exercise_stub,
    _is_outputless_by_design,
    _is_papermill_injected,
    _is_comment_only_cell,
    _normalize_text,
    extract_title,
    detect_requirements,
    has_markdown_intro_conclusion,
    _effective_code_cells,
    NOTEBOOKS_DIR,
)
from expand_catalog_markers import (
    compute_counter,
    compute_breakdown,
    compute_maturity_distribution,
    compute_status_distribution,
    format_catalog_status_block,
    expand_file,
    _to_lf,
    MARKER_RE,
)


# =============================================================================
# estimate_duration
# =============================================================================

class TestEstimateDuration:
    def test_zero_cells(self):
        assert estimate_duration(0, "python", {}) == "5min"

    def test_few_python_cells(self):
        # 3 cells * 2 min = 6 → max(5, 6) = 6 → "15min" (under 15)
        assert estimate_duration(3, "python", {}) == "15min"

    def test_many_python_cells(self):
        # 30 cells * 2 = 60 → "1h"
        assert estimate_duration(30, "python", {}) == "1h"

    def test_dotnet_multiplier(self):
        # 10 cells * 3 = 30 → "45min"
        assert estimate_duration(10, ".net-csharp", {}) == "45min"

    def test_gpu_extends_duration(self):
        # 20 cells * 2 = 40 * 1.5 = 60 → "1h"
        assert estimate_duration(20, "python", {"requires_gpu": True}) == "1h"

    def test_cloud_extends_duration(self):
        # 30 cells * 2 = 60 * 1.5 = 90 → "1h30"
        assert estimate_duration(30, "python", {"requires_cloud": True}) == "1h30"

    def test_very_long(self):
        # 80 cells * 2 = 160 → "2h+"
        assert estimate_duration(80, "python", {}) == "2h+"


# =============================================================================
# check_errors
# =============================================================================

class TestCheckErrors:
    def test_no_errors(self):
        assert check_errors([{"output_type": "stream", "text": "ok"}]) == []

    def test_single_error(self):
        assert check_errors([{"output_type": "error", "ename": "ValueError"}]) == ["ValueError"]

    def test_multiple_errors(self):
        errors = check_errors([
            {"output_type": "error", "ename": "TypeError"},
            {"output_type": "stream", "text": "ok"},
            {"output_type": "error", "ename": "NameError"},
        ])
        assert errors == ["TypeError", "NameError"]

    def test_empty_outputs(self):
        assert check_errors([]) == []


# =============================================================================
# determine_status
# =============================================================================

class TestDetermineStatus:
    """Tests for determine_status.

    _is_research_path uses NOTEBOOKS_DIR hardcoded, so we mock it to avoid
    ValueError when nb_path is outside NOTEBOOKS_DIR (tmp_path).
    """

    @patch("generate_catalog._is_research_path", return_value=False)
    def test_ready_all_outputs(self, mock_rp, tmp_path):
        nb_path = tmp_path / "Test.ipynb"
        nb_path.write_text("{}")
        code_cells = [
            {"cell_type": "code", "outputs": [{"output_type": "stream"}]},
        ]
        status = determine_status(nb_path, {}, code_cells, {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}, True)
        assert status == "READY"

    @patch("generate_catalog._is_research_path", return_value=False)
    def test_broken_with_errors(self, mock_rp, tmp_path):
        nb_path = tmp_path / "Test.ipynb"
        nb_path.write_text("{}")
        code_cells = [
            {"cell_type": "code", "outputs": [{"output_type": "error", "ename": "ValueError"}]},
        ]
        status = determine_status(nb_path, {}, code_cells, {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}, True)
        assert status == "BROKEN"

    @patch("generate_catalog._is_research_path", return_value=False)
    def test_broken_no_outputs_no_requires(self, mock_rp, tmp_path):
        nb_path = tmp_path / "Test.ipynb"
        nb_path.write_text("{}")
        code_cells = [
            {"cell_type": "code", "outputs": []},
        ]
        status = determine_status(nb_path, {}, code_cells, {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}, True)
        assert status == "BROKEN"

    @patch("generate_catalog._is_research_path", return_value=False)
    def test_demo_no_outputs_requires_api(self, mock_rp, tmp_path):
        nb_path = tmp_path / "Test.ipynb"
        nb_path.write_text("{}")
        code_cells = [
            {"cell_type": "code", "outputs": []},
        ]
        status = determine_status(nb_path, {}, code_cells, {"requires_api": True, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}, True)
        assert status == "DEMO"

    def test_research_path_keywords(self):
        # Verify _is_research_path uses expected keywords
        from generate_catalog import RESEARCH_DIR_KEYWORDS
        assert "research" in RESEARCH_DIR_KEYWORDS


# =============================================================================
# _is_exercise_stub
# =============================================================================

class TestIsExerciseStub:
    def test_pass_with_todo(self):
        cell = {"cell_type": "code", "source": ["# TODO: implement\n", "pass\n"]}
        assert _is_exercise_stub(cell) is True

    def test_return_none_with_todo(self):
        cell = {"cell_type": "code", "source": ["# TODO etudiant\n", "return None\n"]}
        assert _is_exercise_stub(cell) is True

    def test_print_exercice(self):
        cell = {"cell_type": "code", "source": ["# TODO\n", 'print("Exercice a completer")\n']}
        assert _is_exercise_stub(cell) is True

    def test_var_none_with_todo(self):
        cell = {"cell_type": "code", "source": ["# TODO: remplacer\n", "result = None\n"]}
        assert _is_exercise_stub(cell) is True

    def test_not_a_stub_no_marker(self):
        cell = {"cell_type": "code", "source": ["x = 42\n", "print(x)\n"]}
        assert _is_exercise_stub(cell) is False

    def test_comment_only_with_todo(self):
        cell = {"cell_type": "code", "source": ["# TODO etudiant: implementez la fonction\n", "# Indice: utiliser recursive\n"]}
        assert _is_exercise_stub(cell) is True

    def test_csharp_return_null(self):
        cell = {"cell_type": "code", "source": ["// TODO etudiant\n", "return null;\n"]}
        assert _is_exercise_stub(cell) is True


# =============================================================================
# _is_outputless_by_design
# =============================================================================

class TestIsOutputlessByDesign:
    def test_assignment(self):
        cell = {"source": ["x = 42\n"]}
        assert _is_outputless_by_design(cell) is True

    def test_import(self):
        cell = {"source": ["import numpy as np\n"]}
        assert _is_outputless_by_design(cell) is True

    def test_function_def(self):
        cell = {"source": ["def foo(x):\n", "    return x * 2\n"]}
        assert _is_outputless_by_design(cell) is True

    def test_class_def(self):
        cell = {"source": ["class MyClass:\n", "    pass\n"]}
        assert _is_outputless_by_design(cell) is True

    def test_print_produces_output(self):
        cell = {"source": ["print('hello')\n"]}
        assert _is_outputless_by_design(cell) is False

    def test_empty_cell(self):
        cell = {"source": [""]}
        assert _is_outputless_by_design(cell) is True

    def test_comment_only(self):
        cell = {"source": ["# just a comment\n"]}
        assert _is_outputless_by_design(cell) is True

    def test_ipython_magic(self):
        cell = {"source": ["%matplotlib inline\n"]}
        assert _is_outputless_by_design(cell) is True

    def test_config_call(self):
        # plt.style.use, warnings.filterwarnings, etc.
        cell = {"source": ["plt.style.use('ggplot')\n"]}
        assert _is_outputless_by_design(cell) is True


# =============================================================================
# _is_papermill_injected
# =============================================================================

class TestIsPapermillInjected:
    def test_injected_tag(self):
        cell = {"metadata": {"tags": ["injected-parameters"]}}
        assert _is_papermill_injected(cell) is True

    def test_no_tags(self):
        cell = {"metadata": {}}
        assert _is_papermill_injected(cell) is False

    def test_other_tags(self):
        cell = {"metadata": {"tags": ["my-tag"]}}
        assert _is_papermill_injected(cell) is False


# =============================================================================
# extract_title
# =============================================================================

class TestExtractTitle:
    def test_simple_title(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["# My Title\n"]}]}
        assert extract_title(nb) == "My Title"

    def test_h2_not_first_title(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["## Subtitle\n"]}]}
        assert extract_title(nb) == "Subtitle"

    def test_no_markdown(self):
        nb = {"cells": [{"cell_type": "code", "source": ["x = 1\n"]}]}
        assert extract_title(nb) == ""

    def test_empty_cells(self):
        nb = {"cells": []}
        assert extract_title(nb) == ""

    def test_markdown_no_heading(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["Just text\n"]}]}
        assert extract_title(nb) == ""


# =============================================================================
# detect_requirements
# =============================================================================

class TestDetectRequirements:
    def test_no_requirements(self):
        nb = {"cells": [{"cell_type": "code", "source": ["x = 42\n"]}]}
        req = detect_requirements(nb)
        assert req["requires_api"] is False
        assert req["requires_gpu"] is False
        assert req["requires_cloud"] is False
        assert req["requires_wsl"] is False

    def test_api_detection(self):
        nb = {"cells": [{"cell_type": "code", "source": ["import openai\n"]}]}
        req = detect_requirements(nb)
        assert req["requires_api"] is True

    def test_gpu_detection(self):
        nb = {"cells": [{"cell_type": "code", "source": ["device = 'cuda'\n"]}]}
        req = detect_requirements(nb)
        assert req["requires_gpu"] is True

    def test_cloud_detection(self):
        nb = {"cells": [{"cell_type": "code", "source": ["from AlgorithmImports import *\n"]}]}
        req = detect_requirements(nb)
        assert req["requires_cloud"] is True

    def test_markdown_cells_ignored(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["Use CUDA for GPU\n"]}]}
        req = detect_requirements(nb)
        assert req["requires_gpu"] is False


# =============================================================================
# count_todos
# =============================================================================

class TestCountTodos:
    def test_no_todos(self):
        nb = {"cells": [{"cell_type": "code", "source": ["x = 42\n"]}]}
        assert count_todos(nb) == 0

    def test_todo_in_non_stub_cell(self):
        # "# TODO implement\nx = 42\n" is NOT comment-only → not an exercise stub
        nb = {"cells": [{"cell_type": "code", "source": ["# TODO implement\n", "x = 42\n"], "outputs": []}]}
        assert count_todos(nb) == 1

    def test_todo_in_executed_cell_excluded(self):
        nb = {"cells": [{"cell_type": "code", "source": ["# TODO implement\n"], "outputs": [{"output_type": "stream"}]}]}
        assert count_todos(nb) == 0

    def test_exercise_stub_excluded(self):
        nb = {"cells": [{"cell_type": "code", "source": ["# TODO\n", "pass\n"], "outputs": []}]}
        assert count_todos(nb) == 0


# =============================================================================
# has_markdown_intro_conclusion
# =============================================================================

class TestHasMarkdownIntroConclusion:
    def test_intro_and_conclusion(self):
        cells = [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "markdown", "source": ["## Introduction\n", "Welcome to this notebook.\n"]},
            {"cell_type": "code", "source": ["x = 1\n"]},
            {"cell_type": "markdown", "source": ["## Conclusion\n", "Summary of results.\n"]},
        ]
        has_intro, has_conclusion = has_markdown_intro_conclusion(cells)
        assert has_intro is True
        assert has_conclusion is True

    def test_no_markdown(self):
        cells = [
            {"cell_type": "code", "source": ["x = 1\n"]},
        ]
        has_intro, has_conclusion = has_markdown_intro_conclusion(cells)
        assert has_intro is False
        assert has_conclusion is False

    def test_intro_only(self):
        cells = [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "markdown", "source": ["## Objectifs d'apprentissage\n"]},
        ]
        has_intro, has_conclusion = has_markdown_intro_conclusion(cells)
        assert has_intro is True
        assert has_conclusion is False

    def test_conclusion_keywords_recapitulatif(self):
        cells = [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "code", "source": ["x = 1\n"]},
            {"cell_type": "markdown", "source": ["## Recapitulatif\n"]},
        ]
        has_intro, has_conclusion = has_markdown_intro_conclusion(cells)
        assert has_conclusion is True

    def test_accented_heading_detected(self):
        # _normalize_text strips accents, so "Synthèse" matches "synthese"
        cells = [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "code", "source": ["x = 1\n"]},
            {"cell_type": "markdown", "source": ["## Synthèse des apprentissages\n"]},
        ]
        has_intro, has_conclusion = has_markdown_intro_conclusion(cells)
        assert has_conclusion is True


# =============================================================================
# _normalize_text
# =============================================================================

class TestNormalizeText:
    def test_strips_accents(self):
        assert "e" in _normalize_text("é")
        assert "a" in _normalize_text("à")

    def test_removes_fenced_code(self):
        result = _normalize_text("hello ```resultat -> synthese``` world")
        assert "resultat" not in result
        assert "hello" in result
        assert "world" in result

    def test_normalizes_apostrophes(self):
        result = _normalize_text("l'apostrophe")
        assert "'" in result


# =============================================================================
# classify_maturity
# =============================================================================

class TestClassifyMaturity:
    def test_template(self):
        assert classify_maturity({}, [], "unknown", is_template=True) == "TEMPLATE"

    def test_draft_no_markdown(self):
        nb = {"cells": [{"cell_type": "code", "source": ["x = 1\n"]}]}
        assert classify_maturity(nb, [], "python") == "DRAFT"

    def test_production_full(self):
        # print() is NOT outputless_by_design → _effective_code_cells keeps it
        nb = {"cells": [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "markdown", "source": ["## Introduction\n"]},
            {"cell_type": "code", "source": ["print('hello')\n"], "outputs": [{"output_type": "stream"}]},
            {"cell_type": "markdown", "source": ["## Conclusion\n"]},
        ]}
        code_cells = [nb["cells"][2]]
        result = classify_maturity(nb, code_cells, "python")
        assert result == "PRODUCTION"

    def test_beta_missing_conclusion(self):
        # Has intro + outputs but no conclusion → BETA
        nb = {"cells": [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "markdown", "source": ["## Introduction\n"]},
            {"cell_type": "code", "source": ["print('hello')\n"], "outputs": [{"output_type": "stream"}]},
        ]}
        code_cells = [nb["cells"][2]]
        result = classify_maturity(nb, code_cells, "python")
        assert result == "BETA"

    def test_draft_no_outputs(self):
        # Has markdown but no code outputs → DRAFT
        nb = {"cells": [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "code", "source": ["print('hello')\n"], "outputs": []},
        ]}
        code_cells = [nb["cells"][1]]
        result = classify_maturity(nb, code_cells, "python")
        assert result == "DRAFT"

    def test_alpha_many_todos(self):
        nb = {"cells": [
            {"cell_type": "markdown", "source": ["# Title\n"]},
            {"cell_type": "code", "source": ["# TODO 1\n", "# TODO 2\n", "# TODO 3\n", "# TODO 4\n", "# TODO 5\n", "# TODO 6\n", "# TODO 7\n"], "outputs": []},
            {"cell_type": "code", "source": ["x = 1\n"], "outputs": [{"output_type": "stream"}]},
        ]}
        code_cells = [nb["cells"][1], nb["cells"][2]]
        # With exclude_executed=True, TODO in cell with outputs is excluded
        # The first cell has no outputs, so TODOs count (7 TODOs > 5 → ALPHA)
        result = classify_maturity(nb, code_cells, "python")
        assert result in ("ALPHA", "DRAFT")


# =============================================================================
# compute_counter (expand_catalog_markers)
# =============================================================================

class TestComputeCounter:
    def test_total_count(self):
        entries = [{"serie": "ML"}, {"serie": "GenAI"}, {"serie": "ML"}]
        assert compute_counter(entries, {}) == "3"

    def test_filter_serie(self):
        entries = [{"serie": "ML"}, {"serie": "GenAI"}, {"serie": "ML"}]
        assert compute_counter(entries, {"serie": "ML"}) == "2"

    def test_filter_serie_status(self):
        entries = [
            {"serie": "ML", "status": "READY"},
            {"serie": "ML", "status": "BROKEN"},
            {"serie": "GenAI", "status": "READY"},
        ]
        assert compute_counter(entries, {"serie": "ML", "status": "READY"}) == "1"

    def test_filter_maturity(self):
        entries = [
            {"serie": "ML", "maturity": "PRODUCTION"},
            {"serie": "ML", "maturity": "BETA"},
        ]
        assert compute_counter(entries, {"serie": "ML", "maturity": "PRODUCTION"}) == "1"

    def test_empty_entries(self):
        assert compute_counter([], {}) == "0"


# =============================================================================
# compute_breakdown
# =============================================================================

class TestComputeBreakdown:
    def test_basic_breakdown(self):
        entries = [
            {"serie": "ML", "sous_serie": "Part1"},
            {"serie": "ML", "sous_serie": "Part1"},
            {"serie": "ML", "sous_serie": "Part2"},
            {"serie": "ML"},  # no sous_serie → "root"
        ]
        result = compute_breakdown(entries, "ML")
        assert result == {"Part1": 2, "Part2": 1, "root": 1}

    def test_no_entries(self):
        result = compute_breakdown([], "ML")
        assert result == {}


# =============================================================================
# compute_maturity_distribution / compute_status_distribution
# =============================================================================

class TestDistributions:
    def test_maturity_distribution(self):
        entries = [
            {"serie": "ML", "maturity": "PRODUCTION"},
            {"serie": "ML", "maturity": "BETA"},
            {"serie": "ML", "maturity": "PRODUCTION"},
        ]
        result = compute_maturity_distribution(entries, "ML")
        assert result == {"PRODUCTION": 2, "BETA": 1}

    def test_status_distribution(self):
        entries = [
            {"serie": "GenAI", "status": "READY"},
            {"serie": "GenAI", "status": "DEMO"},
            {"serie": "ML", "status": "READY"},
        ]
        result = compute_status_distribution(entries, "GenAI")
        assert result == {"READY": 1, "DEMO": 1}

    def test_maturity_all_no_filter(self):
        entries = [
            {"maturity": "PRODUCTION"},
            {"maturity": "DRAFT"},
        ]
        result = compute_maturity_distribution(entries, None)
        assert result == {"PRODUCTION": 1, "DRAFT": 1}


# =============================================================================
# format_catalog_status_block
# =============================================================================

class TestFormatCatalogStatusBlock:
    def test_all_series(self):
        entries = [
            {"serie": "ML"},
            {"serie": "ML"},
            {"serie": "GenAI"},
        ]
        block = format_catalog_status_block(entries, "ALL")
        assert "series: ALL" in block
        assert "total: 3" in block
        assert "ML=2" in block
        assert "GenAI=1" in block

    def test_single_series(self):
        entries = [
            {"serie": "ML", "sous_serie": "Part1", "maturity": "PRODUCTION"},
            {"serie": "ML", "sous_serie": "Part2", "maturity": "BETA"},
        ]
        block = format_catalog_status_block(entries, "ML")
        assert "series: ML" in block
        assert "pedagogical_count: 2" in block


# =============================================================================
# expand_file
# =============================================================================

class TestExpandFile:
    def test_no_markers_unchanged(self):
        content = "# Title\n\nSome text\n"
        new_content, changes = expand_file(content, [])
        assert new_content == content
        assert changes == []

    def test_catalog_status_block_updated(self):
        entries = [{"serie": "ML", "sous_serie": "Part1", "maturity": "PRODUCTION"}]
        content = (
            "# Title\n\n"
            "<!-- CATALOG-STATUS\n"
            "series: ML\n"
            "pedagogical_count: 0\n"
            "breakdown: \n"
            "maturity: \n"
            "-->\n"
        )
        new_content, changes = expand_file(content, entries)
        assert len(changes) == 1
        assert "ML" in changes[0]

    def test_catalog_status_block_no_drift(self):
        entries = [{"serie": "ML", "sous_serie": "Part1", "maturity": "PRODUCTION"}]
        block = format_catalog_status_block(entries, "ML")
        content = f"# Title\n\n{block}\n"
        new_content, changes = expand_file(content, entries)
        assert changes == []


# =============================================================================
# _to_lf
# =============================================================================

class TestToLf:
    def test_crlf_to_lf(self):
        assert _to_lf("hello\r\nworld") == "hello\nworld"

    def test_cr_to_lf(self):
        assert _to_lf("hello\rworld") == "hello\nworld"

    def test_lf_unchanged(self):
        assert _to_lf("hello\nworld") == "hello\nworld"

    def test_mixed(self):
        assert _to_lf("a\r\nb\rc\nd") == "a\nb\nc\nd"


# =============================================================================
# MARKER_RE
# =============================================================================

class TestMarkerRegex:
    def test_counter_total(self):
        m = MARKER_RE.search("<!-- CATALOG:counter:total -->")
        assert m is not None
        assert m.group(1) == "counter"
        assert m.group(2) == "total"

    def test_counter_with_params(self):
        m = MARKER_RE.search("<!-- CATALOG:counter:serie=ML;status=READY -->")
        assert m is not None
        assert m.group(2) == "serie=ML;status=READY"

    def test_no_match(self):
        m = MARKER_RE.search("just some text")
        assert m is None
