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
    CURATED_GIT_FIELDS,
    _effective_code_cells,
    _is_comment_only_cell,
    _is_exercise_stub,
    _is_outputless_by_design,
    _is_papermill_injected,
    _merge_curated_fields,
    _normalize_text,
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


def _make_nb(code_cells, md_cells=None):
    """Build notebook with code cells that produce output (print calls, not assignments)."""
    cells = []
    if md_cells:
        for src in md_cells:
            cells.append(_md_cell(src))
    for src in code_cells:
        cells.append(_code_cell(src, outputs=[{"output_type": "stream", "text": ["ok"]}]))
    nb = {"cells": cells}
    code = [c for c in cells if c["cell_type"] == "code"]
    return nb, code


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

    def test_import_is_outputless(self):
        """AST Import is in the outputless tuple (added by PR #2006/#2018).
        Imports produce no visible Jupyter output and should not block PRODUCTION."""
        assert _is_outputless_by_design(_code_cell("import os\nimport sys"))

    def test_import_from_is_outputless(self):
        """from X import Y also produces no output."""
        assert _is_outputless_by_design(_code_cell("from pathlib import Path"))

    def test_config_call_outputless(self):
        """Bare config calls (plt.style.use, warnings.filterwarnings) produce no output."""
        assert _is_outputless_by_design(_code_cell("plt.style.use('ggplot')"))

    def test_config_call_warnings(self):
        assert _is_outputless_by_design(_code_cell("warnings.filterwarnings('ignore')"))

    def test_config_call_numpy(self):
        assert _is_outputless_by_design(_code_cell("np.set_printoptions(precision=2)"))

    def test_display_call_not_outputless(self):
        """display() is in _OUTPUT_FUNCS and should NOT be outputless."""
        assert not _is_outputless_by_design(_code_cell("display(df)"))

    def test_pprint_call_not_outputless(self):
        """pprint() is in _OUTPUT_FUNCS."""
        assert not _is_outputless_by_design(_code_cell("pprint(data)"))

    def test_show_call_not_outputless(self):
        """show() is in _OUTPUT_FUNCS."""
        assert not _is_outputless_by_design(_code_cell("plt.show()"))

    def test_render_call_not_outputless(self):
        """render() is in _OUTPUT_FUNCS."""
        assert not _is_outputless_by_design(_code_cell("render(template)"))

    def test_mixed_import_and_config(self):
        """Import + config call both outputless."""
        assert _is_outputless_by_design(_code_cell("import matplotlib\nplt.rcParams['font.size'] = 12"))

    def test_assign_and_config(self):
        """Assignment + config call both outputless."""
        assert _is_outputless_by_design(_code_cell("x = 42\nnp.set_printoptions(precision=2)"))

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
    def test_production(self):
        md = ["# Introduction", "Content", "## Conclusion"]
        code = ["print('a')", "print('b')"]
        nb, code_cells = _make_nb(code, md)
        assert classify_maturity(nb, code_cells, "Python 3") == "PRODUCTION"

    def test_beta_no_conclusion(self):
        """Outputs present, <5 TODO, has intro but no conclusion → BETA."""
        md = ["# Introduction", "Content"]
        code = ["print('a')", "print('b')"]
        nb, code_cells = _make_nb(code, md)
        assert classify_maturity(nb, code_cells, "Python 3") == "BETA"

    def test_template_overrides(self):
        nb, code_cells = _make_nb(["print('x')"], ["# Title"])
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


# ---------------------------------------------------------------------------
# classify_maturity — requires_cloud edge cases
# ---------------------------------------------------------------------------

class TestClassifyMaturityCloud:
    def test_cloud_no_outputs_promoted(self):
        """Cloud notebooks with no outputs are promoted (requires_cloud=True)."""
        cells = [
            _md_cell("# Introduction"),
            _md_cell("Content"),
            _md_cell("## Conclusion"),
            _code_cell("print('a')"),  # no output, but cloud bypass
            _code_cell("print('b')"),  # no output
        ]
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        result = classify_maturity(nb, code_cells, "Python 3", requires_cloud=True)
        assert result == "PRODUCTION"

    def test_cloud_with_real_outputs_still_production(self):
        """Cloud notebooks with actual outputs still reach PRODUCTION."""
        md = ["# Introduction", "Content", "## Conclusion"]
        code = ["print('a')", "print('b')"]
        nb, code_cells = _make_nb(code, md)
        result = classify_maturity(nb, code_cells, "Python 3", requires_cloud=True)
        assert result == "PRODUCTION"

    def test_cloud_no_markdown_still_draft(self):
        """Cloud notebooks without markdown still DRAFT (cloud doesn't fix structure)."""
        cells = [_code_cell("print('a')")]
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        result = classify_maturity(nb, code_cells, "Python 3", requires_cloud=True)
        assert result == "DRAFT"

    def test_cloud_no_code_cells(self):
        """Cloud notebook with zero code cells → ALPHA (no code, but md present).

        classify_maturity returns ALPHA when total_code=0 and no outputs to check,
        because the final return is ALPHA. Cloud override only applies when total_code > 0.
        """
        md = ["# Introduction", "Content", "## Conclusion"]
        cells = [_md_cell(s) for s in md]
        nb = {"cells": cells}
        result = classify_maturity(nb, [], "Python 3", requires_cloud=True)
        # total_code=0 → cloud bypass doesn't fire → falls through to ALPHA
        assert result == "ALPHA"


# ---------------------------------------------------------------------------
# classify_maturity — kernel edge cases
# ---------------------------------------------------------------------------

class TestClassifyMaturityKernel:
    def test_unknown_kernel_beta(self):
        """Unknown kernel prevents PRODUCTION even with all outputs."""
        md = ["# Introduction", "Content", "## Conclusion"]
        code = ["print('a')", "print('b')"]
        nb, code_cells = _make_nb(code, md)
        assert classify_maturity(nb, code_cells, "unknown") == "BETA"

    def test_empty_kernel_beta(self):
        """Empty kernel prevents PRODUCTION."""
        md = ["# Introduction", "Content", "## Conclusion"]
        code = ["print('a')"]
        nb, code_cells = _make_nb(code, md)
        assert classify_maturity(nb, code_cells, "") == "BETA"

    def test_none_kernel_beta(self):
        """None kernel prevents PRODUCTION."""
        md = ["# Introduction", "Content", "## Conclusion"]
        code = ["print('a')"]
        nb, code_cells = _make_nb(code, md)
        assert classify_maturity(nb, code_cells, None) == "BETA"


# ---------------------------------------------------------------------------
# classify_maturity — todo boundary tests
# ---------------------------------------------------------------------------

class TestClassifyMaturityTodoBoundary:
    """Test TODO count interaction with output checks in classify_maturity.

    Key insight: classify_maturity checks 'no outputs → DRAFT' (line 480)
    BEFORE checking TODO count (line 484+). So cells without outputs always
    hit DRAFT regardless of TODO count. These tests verify the actual behavior:
    - All cells without outputs → DRAFT (TODO count irrelevant)
    - Mix of output + no-output cells with TODOs → ALPHA (partial outputs gate)
    """

    def test_all_todo_cells_no_outputs_draft(self):
        """Cells with TODOs but no outputs → DRAFT (output gate fires first)."""
        md = ["# Introduction", "Content", "## Conclusion"]
        cells = [_md_cell(s) for s in md]
        for i in range(6):
            cells.append(_code_cell(f"print('value{i}')  # TODO refactor{i}"))
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        result = classify_maturity(nb, code_cells, "Python 3")
        assert result == "DRAFT"

    def test_mixed_outputs_and_todos_alpha(self):
        """Mix of output cells + TODO cells without outputs → ALPHA (partial outputs)."""
        md = ["# Introduction", "Content", "## Conclusion"]
        cells = [_md_cell(s) for s in md]
        # 2 cells WITH outputs (not outputless, no TODO)
        for i in range(2):
            cells.append(_code_cell(f"print('result{i}')", outputs=[
                {"output_type": "stream", "text": [f"result{i}"]}
            ]))
        # 6 TODO cells WITHOUT outputs → partial outputs → ALPHA
        for i in range(6):
            cells.append(_code_cell(f"print('val{i}')  # TODO step{i}"))
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        result = classify_maturity(nb, code_cells, "Python 3")
        assert result == "ALPHA"

    def test_mixed_outputs_and_many_todos_draft(self):
        """Mix of output cells + >10 TODO cells without outputs → DRAFT."""
        md = ["# Introduction", "Content", "## Conclusion"]
        cells = [_md_cell(s) for s in md]
        # 2 cells WITH outputs
        for i in range(2):
            cells.append(_code_cell(f"print('result{i}')", outputs=[
                {"output_type": "stream", "text": [f"result{i}"]}
            ]))
        # 12 TODO cells WITHOUT outputs → >10 TODO → DRAFT
        for i in range(12):
            cells.append(_code_cell(f"print('val{i}')  # TODO step{i}"))
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        result = classify_maturity(nb, code_cells, "Python 3")
        assert result == "DRAFT"

    def test_nearly_all_outputs_with_few_todos_beta(self):
        """nearly_all_outputs with <5 TODOs and structure → BETA."""
        md = ["# Introduction", "Content", "## Conclusion"]
        cells = [_md_cell(s) for s in md]
        # 5 print cells with outputs (print is NOT outputless-by-design)
        for i in range(5):
            cells.append(_code_cell(f"print({i})", outputs=[
                {"output_type": "stream", "text": [str(i)]}
            ]))
        # 1 TODO print cell without outputs (within nearly_all threshold of 1)
        cells.append(_code_cell("print(compute())  # TODO implement"))
        nb = {"cells": cells}
        code_cells = [c for c in cells if c["cell_type"] == "code"]
        result = classify_maturity(nb, code_cells, "Python 3")
        assert result == "BETA"


# ---------------------------------------------------------------------------
# _is_outputless_by_design — config call branches (continued)
# ---------------------------------------------------------------------------

class TestIsOutputlessConfigCalls:
    def test_method_call_outputless(self):
        """Attribute call (plt.style.use) is config, not output."""
        assert _is_outputless_by_design(_code_cell("plt.style.use('ggplot')"))

    def test_simple_name_call_not_in_output_funcs(self):
        """A simple name call not in _OUTPUT_FUNCS is outputless (config)."""
        assert _is_outputless_by_design(_code_cell("setup_logging()"))

    def test_annotated_assign_outputless(self):
        """Annotated assignment (x: int = 5) is outputless."""
        assert _is_outputless_by_design(_code_cell("x: int = 42"))

    def test_async_function_def_outputless(self):
        """Async function definitions produce no output."""
        assert _is_outputless_by_design(_code_cell("async def fetch():\n    pass"))

    def test_syntax_error_not_outputless(self):
        """Invalid Python returns False."""
        assert not _is_outputless_by_design(_code_cell("def foo("))

    def test_config_call_with_args(self):
        """Config call with multiple args is outputless."""
        assert _is_outputless_by_design(_code_cell("os.environ.setdefault('KEY', 'val')"))


# ---------------------------------------------------------------------------
# _merge_curated_fields
# ---------------------------------------------------------------------------


class TestMergeCuratedFields:
    """Tests for _merge_curated_fields — critical for stale-catalog poison prevention.

    When catalog is regenerated on a branch behind main, curated git-derived fields
    (last_validation, last_validator, issue_pr_associee) may be blank for entries
    not modified on the current branch. This function preserves them from main.
    """

    def test_empty_main_catalog(self):
        """Empty main catalog returns entries unchanged."""
        entries = [{"path": "a.ipynb", "last_validation": "2026-01-01"}]
        result = _merge_curated_fields(entries, {})
        assert len(result) == 1
        assert result[0]["last_validation"] == "2026-01-01"

    def test_empty_entries(self):
        """Empty entries list returns empty list."""
        result = _merge_curated_fields([], {"a.ipynb": {"path": "a.ipynb"}})
        assert result == []

    def test_preserves_from_main_when_empty(self):
        """Blank curated fields are filled from main catalog."""
        entries = [{"path": "a.ipynb", "last_validation": "", "last_validator": "", "issue_pr_associee": ""}]
        main = {"a.ipynb": {"path": "a.ipynb", "last_validation": "2026-06-01", "last_validator": "ai-01", "issue_pr_associee": "#123"}}
        result = _merge_curated_fields(entries, main)
        assert result[0]["last_validation"] == "2026-06-01"
        assert result[0]["last_validator"] == "ai-01"
        assert result[0]["issue_pr_associee"] == "#123"

    def test_keeps_current_when_not_empty(self):
        """Non-empty current fields are NOT overwritten by main."""
        entries = [{"path": "a.ipynb", "last_validation": "2026-06-05", "last_validator": "po-2023", "issue_pr_associee": "#456"}]
        main = {"a.ipynb": {"path": "a.ipynb", "last_validation": "2026-06-01", "last_validator": "ai-01", "issue_pr_associee": "#123"}}
        result = _merge_curated_fields(entries, main)
        assert result[0]["last_validation"] == "2026-06-05"
        assert result[0]["last_validator"] == "po-2023"
        assert result[0]["issue_pr_associee"] == "#456"

    def test_mixed_fill_and_keep(self):
        """Some fields filled from main, some kept from current."""
        entries = [{"path": "a.ipynb", "last_validation": "2026-06-05", "last_validator": "", "issue_pr_associee": ""}]
        main = {"a.ipynb": {"path": "a.ipynb", "last_validation": "2026-06-01", "last_validator": "ai-01", "issue_pr_associee": "#123"}}
        result = _merge_curated_fields(entries, main)
        assert result[0]["last_validation"] == "2026-06-05"  # kept (non-empty)
        assert result[0]["last_validator"] == "ai-01"  # filled from main
        assert result[0]["issue_pr_associee"] == "#123"  # filled from main

    def test_missing_fields_treated_as_empty(self):
        """Missing curated fields (no key at all) are filled from main."""
        entries = [{"path": "a.ipynb"}]
        main = {"a.ipynb": {"path": "a.ipynb", "last_validation": "2026-06-01", "last_validator": "ai-01", "issue_pr_associee": "#789"}}
        result = _merge_curated_fields(entries, main)
        assert result[0]["last_validation"] == "2026-06-01"
        assert result[0]["last_validator"] == "ai-01"
        assert result[0]["issue_pr_associee"] == "#789"

    def test_no_match_in_main(self):
        """Entry not in main catalog is left unchanged."""
        entries = [{"path": "new.ipynb", "last_validation": "", "last_validator": ""}]
        main = {"old.ipynb": {"path": "old.ipynb", "last_validation": "2026-06-01"}}
        result = _merge_curated_fields(entries, main)
        assert result[0]["last_validation"] == ""

    def test_multiple_entries(self):
        """Multiple entries are processed independently."""
        entries = [
            {"path": "a.ipynb", "last_validation": "", "last_validator": "", "issue_pr_associee": ""},
            {"path": "b.ipynb", "last_validation": "2026-06-05", "last_validator": "po-2023", "issue_pr_associee": "#999"},
        ]
        main = {
            "a.ipynb": {"path": "a.ipynb", "last_validation": "2026-06-01", "last_validator": "ai-01", "issue_pr_associee": "#100"},
            "b.ipynb": {"path": "b.ipynb", "last_validation": "2026-05-01", "last_validator": "other", "issue_pr_associee": "#200"},
        }
        result = _merge_curated_fields(entries, main)
        # a.ipynb: all fields filled from main
        assert result[0]["last_validation"] == "2026-06-01"
        assert result[0]["last_validator"] == "ai-01"
        # b.ipynb: current values preserved (non-empty)
        assert result[1]["last_validation"] == "2026-06-05"
        assert result[1]["last_validator"] == "po-2023"
        assert result[1]["issue_pr_associee"] == "#999"

    def test_does_not_modify_non_curated_fields(self):
        """Non-curated fields (title, kernel, etc.) are never touched."""
        entries = [{"path": "a.ipynb", "title": "My Notebook", "kernel": "Python 3", "last_validation": ""}]
        main = {"a.ipynb": {"path": "a.ipynb", "title": "Old Title", "kernel": "Python 2", "last_validation": "2026-06-01"}}
        result = _merge_curated_fields(entries, main)
        assert result[0]["title"] == "My Notebook"  # unchanged
        assert result[0]["kernel"] == "Python 3"  # unchanged
        assert result[0]["last_validation"] == "2026-06-01"  # filled

    def test_none_main_catalog(self):
        """None main catalog returns entries unchanged (treated as empty)."""
        entries = [{"path": "a.ipynb", "last_validation": "2026-01-01"}]
        result = _merge_curated_fields(entries, None)
        assert result[0]["last_validation"] == "2026-01-01"

    def test_curated_git_fields_constant(self):
        """CURATED_GIT_FIELDS contains exactly the 3 expected fields."""
        assert CURATED_GIT_FIELDS == ("last_validation", "last_validator", "issue_pr_associee")

    def test_merge_is_not_deep_copy(self):
        """Entries are modified in-place (same dict objects)."""
        entries = [{"path": "a.ipynb", "last_validation": ""}]
        main = {"a.ipynb": {"path": "a.ipynb", "last_validation": "2026-06-01"}}
        result = _merge_curated_fields(entries, main)
        assert result[0] is entries[0]  # same object, mutated


# ---------------------------------------------------------------------------
# _normalize_text
# ---------------------------------------------------------------------------


class TestNormalizeText:
    """Tests for _normalize_text — accent stripping, code fence removal, lowercasing."""

    def test_lowercase(self):
        """Converts to lowercase."""
        result = _normalize_text("Hello WORLD")
        assert result == "hello world"

    def test_strips_accents(self):
        """Removes combining characters (accents)."""
        result = _normalize_text("synthese")
        assert "synthese" in result
        result2 = _normalize_text("synthèse")
        assert "synthese" in result2

    def test_normalizes_apostrophes(self):
        """Curly quotes apostrophes become straight apostrophes."""
        result = _normalize_text("l’objectif")
        assert "l'objectif" in result

    def test_removes_fenced_code_blocks(self):
        """Fenced code blocks are removed entirely."""
        text = "before ```flow\nresultat -> synthese\n``` after"
        result = _normalize_text(text)
        assert "resultat" not in result
        assert "before" in result
        assert "after" in result

    def test_preserves_non_fenced_code(self):
        """Non-fenced content is preserved."""
        result = _normalize_text("conclusion section here")
        assert "conclusion" in result

    def test_empty_string(self):
        """Empty string returns empty string."""
        assert _normalize_text("") == ""

    def test_multiline_fenced_code(self):
        """Multi-line fenced code blocks are removed."""
        text = "intro\n```\nline1\nline2\n```\nconclusion"
        result = _normalize_text(text)
        assert "line1" not in result
        assert "intro" in result
        assert "conclusion" in result


# ---------------------------------------------------------------------------
# _is_papermill_injected
# ---------------------------------------------------------------------------


class TestIsPapermillInjected:
    """Tests for _is_papermill_injected — Papermill parameter cell detection."""

    def test_injected_tag(self):
        """Cell with injected-parameters tag is detected."""
        cell = _code_cell("param = 42", tags=["injected-parameters"])
        assert _is_papermill_injected(cell)

    def test_no_tags(self):
        """Cell without tags is not injected."""
        cell = _code_cell("param = 42")
        assert not _is_papermill_injected(cell)

    def test_other_tags(self):
        """Cell with other tags but not injected-parameters is not injected."""
        cell = _code_cell("param = 42", tags=["parameters"])
        assert not _is_papermill_injected(cell)

    def test_empty_tags(self):
        """Cell with empty tags list is not injected."""
        cell = _code_cell("param = 42", tags=[])
        assert not _is_papermill_injected(cell)

    def test_no_metadata(self):
        """Cell without metadata is not injected."""
        cell = {"cell_type": "code", "source": ["x = 1"], "outputs": []}
        assert not _is_papermill_injected(cell)


# ---------------------------------------------------------------------------
# _is_comment_only_cell
# ---------------------------------------------------------------------------


class TestIsCommentOnlyCell:
    """Tests for _is_comment_only_cell — comment-only code cell detection."""

    def test_comment_only(self):
        """Cell with only comments returns True."""
        cell = _code_cell("# This is a comment\n# Another comment")
        assert _is_comment_only_cell(cell)

    def test_code_with_comment(self):
        """Cell with code and comment returns False."""
        cell = _code_cell("x = 1  # with comment")
        assert not _is_comment_only_cell(cell)

    def test_empty_source(self):
        """Cell with empty source returns True."""
        cell = _code_cell("")
        assert _is_comment_only_cell(cell)

    def test_whitespace_only(self):
        """Cell with only whitespace returns True."""
        cell = _code_cell("   \n   \n")
        assert _is_comment_only_cell(cell)

    def test_mixed_comments_and_blank_lines(self):
        """Cell with comments and blank lines returns True."""
        cell = _code_cell("# comment\n\n# another\n")
        assert _is_comment_only_cell(cell)

    def test_actual_code(self):
        """Cell with actual code returns False."""
        cell = _code_cell("print('hello')")
        assert not _is_comment_only_cell(cell)

    def test_multiline_comment(self):
        """Cell with multi-line comment (triple-quoted string) is NOT comment-only."""
        cell = _code_cell('"""docstring"""')
        # Triple-quoted strings are parsed as Expr(Str), not comments
        assert not _is_comment_only_cell(cell)
