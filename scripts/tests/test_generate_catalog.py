"""Tests for scripts/notebook_tools/generate_catalog.py — notebook catalog generator.

Tests focus on pure functions: estimate_duration, detect_kernel, extract_title,
detect_requirements, check_errors, _is_exercise_stub, _is_outputless_by_design,
count_todos, has_markdown_intro_conclusion. classify_maturity tested via
effective code cells. No filesystem I/O on production files.
"""

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from generate_catalog import (
    _effective_code_cells,
    _is_exercise_stub,
    _is_outputless_by_design,
    check_errors,
    classify_maturity,
    count_todos,
    detect_kernel,
    detect_requirements,
    estimate_duration,
    extract_title,
    has_markdown_intro_conclusion,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells, metadata=None):
    """Build a minimal notebook dict."""
    nb = {"cells": cells, "metadata": {}}
    if metadata:
        nb["metadata"] = metadata
    return nb


def _code_cell(source, outputs=None, exec_count=1, tags=None):
    """Build a code cell."""
    cell = {
        "cell_type": "code",
        "source": [source] if isinstance(source, str) else source,
        "execution_count": exec_count,
        "outputs": outputs or [],
        "metadata": {},
    }
    if tags:
        cell["metadata"]["tags"] = tags
    return cell


def _md_cell(source):
    """Build a markdown cell."""
    return {
        "cell_type": "markdown",
        "source": [source] if isinstance(source, str) else source,
        "metadata": {},
    }


# ---------------------------------------------------------------------------
# estimate_duration
# ---------------------------------------------------------------------------

class TestEstimateDuration:
    def test_zero_cells(self):
        assert estimate_duration(0, "python3", {}) == "5min"

    def test_few_python_cells(self):
        # 3 cells * 2 min = 6 → max(5,6) = 6 → <15 → "15min"
        assert estimate_duration(3, "python3", {}) == "15min"

    def test_dotnet_slower(self):
        # 3 cells * 3 min = 9 → max(5,9) = 9 → <15 → "15min"
        assert estimate_duration(3, ".NET (C#)", {}) == "15min"

    def test_gpu_increases(self):
        # 5 cells * 2 = 10, GPU * 1.5 = 15 → >=15 → "30min"
        result = estimate_duration(5, "python3", {"requires_gpu": True})
        assert result == "30min"

    def test_cloud_increases(self):
        # 5 cells * 2 = 10, cloud * 1.5 = 15 → >=15 → "30min"
        result = estimate_duration(5, "python3", {"requires_cloud": True})
        assert result == "30min"

    def test_large_notebook(self):
        # 40 cells * 2 = 80 → GPU * 1.5 = 120 → "2h+"
        assert estimate_duration(40, "python3", {"requires_gpu": True}) == "2h+"

    def test_one_hour_range(self):
        # 20 cells * 3 = 60 → "1h"
        assert estimate_duration(20, ".NET (C#)", {}) == "1h"


# ---------------------------------------------------------------------------
# detect_kernel
# ---------------------------------------------------------------------------

class TestDetectKernel:
    def test_display_name(self):
        nb = _nb([], {"kernelspec": {"display_name": "Python 3", "name": "python3"}})
        assert detect_kernel(nb) == "Python 3"

    def test_fallback_to_name(self):
        nb = _nb([], {"kernelspec": {"name": "python3"}})
        assert detect_kernel(nb) == "python3"

    def test_no_kernelspec(self):
        nb = _nb([])
        assert detect_kernel(nb) == "unknown"

    def test_empty_kernelspec(self):
        nb = _nb([], {"kernelspec": {}})
        assert detect_kernel(nb) == "unknown"


# ---------------------------------------------------------------------------
# extract_title
# ---------------------------------------------------------------------------

class TestExtractTitle:
    def test_h1_title(self):
        nb = _nb([_md_cell("# My Title\nSome text")])
        assert extract_title(nb) == "My Title"

    def test_h2_title(self):
        nb = _nb([_md_cell("## Subtitle")])
        assert extract_title(nb) == "Subtitle"

    def test_h3_title(self):
        nb = _nb([_md_cell("### Deep Title")])
        assert extract_title(nb) == "Deep Title"

    def test_no_markdown(self):
        nb = _nb([_code_cell("x = 1")])
        assert extract_title(nb) == ""

    def test_markdown_no_heading(self):
        nb = _nb([_md_cell("Just some text")])
        assert extract_title(nb) == ""

    def test_empty_notebook(self):
        assert extract_title({"cells": []}) == ""

    def test_first_heading_wins(self):
        nb = _nb([_md_cell("## Second\n# First")])
        assert extract_title(nb) == "Second"


# ---------------------------------------------------------------------------
# detect_requirements
# ---------------------------------------------------------------------------

class TestDetectRequirements:
    def test_openai_api(self):
        nb = _nb([_code_cell("import openai\nopenai.api_key = '...'")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is True

    def test_gpu_cuda(self):
        nb = _nb([_code_cell("import torch\ndevice = torch.device('cuda')")])
        reqs = detect_requirements(nb)
        assert reqs["requires_gpu"] is True

    def test_cloud_quantbook(self):
        nb = _nb([_code_cell("from AlgorithmImports import *\nclass MyAlgo(QCAlgorithm)")])
        reqs = detect_requirements(nb)
        assert reqs["requires_cloud"] is True

    def test_wsl(self):
        nb = _nb([_code_cell("# Run via WSL\nimport subprocess")])
        reqs = detect_requirements(nb)
        assert reqs["requires_wsl"] is True

    def test_plain_python(self):
        nb = _nb([_code_cell("x = [1, 2, 3]\nprint(x)")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is False
        assert reqs["requires_gpu"] is False
        assert reqs["requires_cloud"] is False
        assert reqs["requires_wsl"] is False

    def test_no_code_cells(self):
        nb = _nb([_md_cell("# Title")])
        reqs = detect_requirements(nb)
        assert all(not v for v in reqs.values())


# ---------------------------------------------------------------------------
# check_errors
# ---------------------------------------------------------------------------

class TestCheckErrors:
    def test_no_errors(self):
        assert check_errors([{"output_type": "stream", "text": ["ok"]}]) == []

    def test_single_error(self):
        outputs = [{"output_type": "error", "ename": "ImportError", "evalue": "bad"}]
        assert check_errors(outputs) == ["ImportError"]

    def test_multiple_errors(self):
        outputs = [
            {"output_type": "error", "ename": "TypeError", "evalue": "bad1"},
            {"output_type": "error", "ename": "ValueError", "evalue": "bad2"},
        ]
        assert check_errors(outputs) == ["TypeError", "ValueError"]

    def test_empty_outputs(self):
        assert check_errors([]) == []


# ---------------------------------------------------------------------------
# _is_exercise_stub
# ---------------------------------------------------------------------------

class TestIsExerciseStub:
    def test_pass_stub(self):
        assert _is_exercise_stub(_code_cell("# TODO: implement\npass"))

    def test_return_none_stub(self):
        assert _is_exercise_stub(_code_cell("# TODO\nreturn None"))

    def test_print_exercice_stub(self):
        assert _is_exercise_stub(_code_cell('# TODO\nprint("Exercice a completer")'))

    def test_var_none_todo(self):
        assert _is_exercise_stub(_code_cell("result = None  # TODO etudiant"))

    def test_not_a_stub_no_todo(self):
        assert not _is_exercise_stub(_code_cell("x = 42"))

    def test_not_a_stub_real_solution(self):
        assert not _is_exercise_stub(_code_cell("# TODO: implement this\nreturn compute(x)"))

    def test_comment_only_with_todo(self):
        """Comment-only cells with # TODO are exercise instructions (excluded)."""
        assert _is_exercise_stub(_code_cell("# TODO etudiant\n# Indice: utiliser map()"))

    # --- New markers from #1942: # ETAPE, # ÉTAPE, # INDICE ---

    def test_etape_marker_pass(self):
        """# Etape N marker is recognized as exercise stub."""
        assert _is_exercise_stub(_code_cell("# Etape 1: implement BFS\npass"))

    def test_etape_accent_marker(self):
        """# Étape (with accent) marker is recognized."""
        assert _is_exercise_stub(_code_cell("# Étape 2: complétez\npass"))

    def test_indice_marker_return_none(self):
        """# Indice marker with return None stub."""
        assert _is_exercise_stub(_code_cell("# Indice: utiliser sorted()\nreturn None"))

    def test_comment_only_with_etape(self):
        """Comment-only cells with # Etape are exercise instructions."""
        assert _is_exercise_stub(_code_cell("# Etape 3: analysez le résultat\n# Indice: regardez la complexité"))

    def test_comment_only_with_indice(self):
        """Comment-only cells with # Indice are exercise instructions."""
        assert _is_exercise_stub(_code_cell("# Indice: utiliser une file de priorité"))

    def test_no_marker_not_stub(self):
        """Cell without any exercise marker is not a stub."""
        assert not _is_exercise_stub(_code_cell("pass"))

    # --- code_part stripping from #1942 ---

    def test_pass_with_inline_comment(self):
        """pass with trailing inline # TODO comment is stripped and matched."""
        assert _is_exercise_stub(_code_cell("pass  # TODO: implement this"))

    def test_return_none_with_inline_comment(self):
        """return None with trailing inline comment is matched."""
        assert _is_exercise_stub(_code_cell("return None  # TODO etudiant"))

    def test_var_none_without_todo_on_last_line(self):
        """var = None matches even without # TODO on the last line (marker checked in source)."""
        assert _is_exercise_stub(_code_cell("# TODO etudiant\nresult = None"))

    def test_print_completer_with_code_part(self):
        """print(...) with 'completer' matched via code_part stripping."""
        assert _is_exercise_stub(_code_cell('# TODO\nprint("A completer")'))

    def test_print_completer_single_quotes(self):
        """print(...) with 'completer' in single quotes."""
        assert _is_exercise_stub(_code_cell("# TODO\nprint('Exercice a completer')"))

    def test_real_solution_with_etape_not_stub(self):
        """# Etape marker with real computation is NOT a stub."""
        assert not _is_exercise_stub(_code_cell("# Etape 1\nreturn compute(x)"))


# ---------------------------------------------------------------------------
# _effective_code_cells
# ---------------------------------------------------------------------------


class TestEffectiveCodeCells:
    def _make_code_cells(self, sources):
        """Build a list of code cells from source strings."""
        return [_code_cell(s) for s in sources]

    def test_filters_papermill_injected(self):
        """Papermill injected-parameters cells are excluded."""
        cells = self._make_code_cells(["x = 42"])
        cells[0]["metadata"]["tags"] = ["injected-parameters"]
        result = _effective_code_cells(cells)
        assert len(result) == 0

    def test_filters_outputless_assignments(self):
        """Pure assignment cells are excluded."""
        cells = self._make_code_cells(["x = 42"])
        result = _effective_code_cells(cells)
        assert len(result) == 0

    def test_filters_function_defs(self):
        """Function definition cells are excluded."""
        cells = self._make_code_cells(["def foo():\n    pass"])
        result = _effective_code_cells(cells)
        assert len(result) == 0

    def test_filters_exercise_stubs(self):
        """C.1-compliant exercise stubs are excluded."""
        cells = self._make_code_cells(["# TODO\npass"])
        result = _effective_code_cells(cells)
        assert len(result) == 0

    def test_keeps_print_cells(self):
        """Cells with print() are kept (they produce output)."""
        cells = self._make_code_cells(["print('hello')"])
        result = _effective_code_cells(cells)
        assert len(result) == 1

    def test_keeps_expression_cells(self):
        """Cells with bare expressions are kept."""
        cells = self._make_code_cells(["42"])
        result = _effective_code_cells(cells)
        assert len(result) == 1

    def test_mixed_filtering(self):
        """Mix of excluded and kept cells."""
        cells = self._make_code_cells([
            "x = 42",                     # outputless -> excluded
            "# TODO\npass",               # exercise stub -> excluded
            "print('result')",            # has output -> kept
            "def foo():\n    pass",        # function def -> excluded
            "2 + 2",                       # expression -> kept
        ])
        result = _effective_code_cells(cells)
        assert len(result) == 2

    def test_empty_list(self):
        """Empty list returns empty."""
        assert _effective_code_cells([]) == []

    def test_etape_stub_filtered(self):
        """Exercise stub with # Etape marker is filtered."""
        cells = self._make_code_cells(["# Etape 1\npass"])
        result = _effective_code_cells(cells)
        assert len(result) == 0


# ---------------------------------------------------------------------------
# _is_outputless_by_design
# ---------------------------------------------------------------------------

class TestIsOutputlessByDesign:
    def test_assignment(self):
        assert _is_outputless_by_design(_code_cell("x = 42"))

    def test_function_def(self):
        assert _is_outputless_by_design(_code_cell("def foo():\n    pass"))

    def test_class_def(self):
        assert _is_outputless_by_design(_code_cell("class Bar:\n    pass"))

    def test_import_not_outputless(self):
        """AST Import is not in the outputless tuple (Assign, FunctionDef, ClassDef).
        Imports are NOT classified as outputless — they may have side effects."""
        assert not _is_outputless_by_design(_code_cell("import os\nimport sys"))

    def test_print_produces_output(self):
        assert not _is_outputless_by_design(_code_cell("print('hello')"))

    def test_expression_produces_output(self):
        assert not _is_outputless_by_design(_code_cell("42"))

    def test_empty_cell(self):
        assert _is_outputless_by_design(_code_cell(""))

    def test_comment_only(self):
        assert _is_outputless_by_design(_code_cell("# Just a comment"))

    def test_mixed_assign_and_call(self):
        assert not _is_outputless_by_design(_code_cell("x = foo()\nprint(x)"))


# ---------------------------------------------------------------------------
# count_todos
# ---------------------------------------------------------------------------

class TestCountTodos:
    def test_no_todos(self):
        nb = _nb([_code_cell("x = 42")])
        assert count_todos(nb) == 0

    def test_comment_only_todo_excluded(self):
        """Comment-only cells with # TODO are exercise stubs → excluded from count."""
        nb = _nb([_code_cell("# TODO: implement")])
        assert count_todos(nb) == 0

    def test_executed_todo_excluded(self):
        """Cells with outputs are excluded from TODO count."""
        nb = _nb([
            _code_cell("# TODO: done", outputs=[{"output_type": "stream", "text": ["ok"]}]),
        ])
        assert count_todos(nb) == 0

    def test_exercise_stub_excluded(self):
        """C.1-compliant stubs are excluded."""
        nb = _nb([_code_cell("# TODO\npass")])
        assert count_todos(nb) == 0

    def test_real_todo_in_code(self):
        """# TODO in a non-stub, non-comment-only code cell is counted."""
        nb = _nb([_code_cell("x = 42  # TODO refactor")])
        assert count_todos(nb) == 1

    def test_case_insensitive(self):
        nb = _nb([_code_cell("x = 1  # todo: fix this")])
        assert count_todos(nb) == 1


# ---------------------------------------------------------------------------
# has_markdown_intro_conclusion
# ---------------------------------------------------------------------------

class TestHasMarkdownIntroConclusion:
    def test_has_intro(self):
        nb = _nb([_md_cell("# Introduction au sujet"), _md_cell("Content")])
        intro, _ = has_markdown_intro_conclusion(nb["cells"])
        assert intro is True

    def test_has_conclusion(self):
        nb = _nb([_md_cell("Content"), _md_cell("## Conclusion et perspectives")])
        _, concl = has_markdown_intro_conclusion(nb["cells"])
        assert concl is True

    def test_has_both(self):
        nb = _nb([
            _md_cell("# Objectifs du cours"),
            _md_cell("Content"),
            _md_cell("## Résumé de la session"),
        ])
        intro, concl = has_markdown_intro_conclusion(nb["cells"])
        assert intro is True
        assert concl is True

    def test_no_md_cells(self):
        nb = _nb([_code_cell("x=1")])
        intro, concl = has_markdown_intro_conclusion(nb["cells"])
        assert intro is False
        assert concl is False

    def test_no_keywords(self):
        nb = _nb([_md_cell("# Random Title"), _md_cell("# Random End")])
        intro, concl = has_markdown_intro_conclusion(nb["cells"])
        assert intro is False
        assert concl is False


# ---------------------------------------------------------------------------
# classify_maturity
# ---------------------------------------------------------------------------

class TestClassifyMaturity:
    def _make_nb(self, code_cells, md_cells=None):
        """Build notebook with code cells that produce output (print calls, not assignments)."""
        cells = []
        if md_cells:
            for src in md_cells:
                cells.append(_md_cell(src))
        for src in code_cells:
            # Use print() so cells are NOT outputless-by-design
            cells.append(_code_cell(src, outputs=[{"output_type": "stream", "text": ["ok"]}]))
        nb = {"cells": cells}
        # Return ALL code cells (classify_maturity applies _effective_code_cells internally)
        code = [c for c in cells if c["cell_type"] == "code"]
        return nb, code

    def test_production(self):
        md = ["# Introduction", "Content", "## Conclusion"]
        code = ["print('a')", "print('b')"]
        nb, code_cells = self._make_nb(code, md)
        assert classify_maturity(nb, code_cells, "Python 3") == "PRODUCTION"

    def test_beta_no_conclusion(self):
        """Outputs present, <5 TODO, has intro but no conclusion → BETA."""
        md = ["# Introduction", "Content"]
        code = ["print('a')", "print('b')"]
        nb, code_cells = self._make_nb(code, md)
        assert classify_maturity(nb, code_cells, "Python 3") == "BETA"

    def test_template_overrides(self):
        nb, code_cells = self._make_nb(["print('x')"], ["# Title"])
        assert classify_maturity(nb, code_cells, "Python 3", is_template=True) == "TEMPLATE"

    def test_draft_no_markdown(self):
        """No markdown cells → DRAFT."""
        code = ["print('x')"]
        cells = [_code_cell("print('x')", outputs=[{"output_type": "stream", "text": ["1"]}])]
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "DRAFT"

    def test_alpha_partial_outputs(self):
        """Some effective cells with outputs, some without → ALPHA.
        Note: _effective_code_cells filters outputless-by-design cells (assignments).
        To get ALPHA, we need print() cells where some have outputs and some don't."""
        cells = [
            _md_cell("# Intro"),
            _md_cell("Content"),
            _md_cell("## Conclusion"),
            _code_cell("print('a')", outputs=[{"output_type": "stream", "text": ["a"]}]),
            _code_cell("print('b')", outputs=[{"output_type": "stream", "text": ["b"]}]),
            _code_cell("print('c')"),  # no output on a print cell → NOT outputless
            _code_cell("print('d')"),  # another without output
        ]
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "ALPHA"

    def test_beta_partial_outputs_with_structure(self):
        """Most cells have outputs, 1 missing → BETA (nearly_all_outputs)."""
        cells = [
            _md_cell("# Introduction"),
            _md_cell("Content"),
            _md_cell("## Conclusion"),
            _code_cell("print('a')", outputs=[{"output_type": "stream", "text": ["a"]}]),
            _code_cell("print('b')", outputs=[{"output_type": "stream", "text": ["b"]}]),
            _code_cell("print('c')", outputs=[{"output_type": "stream", "text": ["c"]}]),
            _code_cell("print('d')"),  # 1 missing → nearly_all (<=1)
        ]
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        # 4 cells effective, 3 with outputs, 1 without → nearly_all_outputs=True
        # But not all_have_outputs → not PRODUCTION → BETA
        assert classify_maturity(nb, code_cells, "Python 3") == "BETA"
