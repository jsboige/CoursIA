"""Tests for generate_catalog.py — catalog generation heuristics.

Covers: detect_kernel, extract_title, detect_requirements, check_errors,
determine_status, count_todos, has_markdown_intro_conclusion,
classify_maturity.
"""

import json
import sys
import tempfile
from pathlib import Path

import pytest

# Add parent dir to path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from generate_catalog import (
    NOTEBOOKS_DIR,
    _effective_code_cells,
    _is_exercise_stub,
    check_errors,
    classify_maturity,
    count_todos,
    detect_kernel,
    detect_requirements,
    determine_status,
    extract_title,
    has_markdown_intro_conclusion,
)


def _nb(cells, metadata=None):
    """Build a minimal notebook dict."""
    nb = {"cells": cells, "metadata": {}}
    if metadata:
        nb["metadata"] = metadata
    return nb


def _md(source, cell_type="markdown"):
    """Build a markdown/code cell with newline-terminated source."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {"cell_type": cell_type, "source": source, "outputs": [],
            "execution_count": 1}


def _code(source, outputs=None, execution_count=1):
    """Build a code cell."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {
        "cell_type": "code",
        "source": source,
        "outputs": outputs or [],
        "execution_count": execution_count,
    }


def _error_output(ename="RuntimeError", evalue="test error"):
    """Build an error output dict."""
    return {
        "output_type": "error",
        "ename": ename,
        "evalue": evalue,
        "traceback": [],
    }


def _stream_output(text="hello"):
    """Build a stdout stream output."""
    return {"output_type": "stream", "name": "stdout", "text": [text]}


# --- detect_kernel ---

class TestDetectKernel:
    def test_display_name(self):
        nb = _nb([], metadata={"kernelspec": {"display_name": "Python 3", "name": "python3"}})
        assert detect_kernel(nb) == "Python 3"

    def test_fallback_to_name(self):
        nb = _nb([], metadata={"kernelspec": {"name": "python3"}})
        assert detect_kernel(nb) == "python3"

    def test_no_kernelspec(self):
        nb = _nb([], metadata={})
        assert detect_kernel(nb) == "unknown"

    def test_empty_kernelspec(self):
        nb = _nb([], metadata={"kernelspec": {}})
        assert detect_kernel(nb) == "unknown"


# --- extract_title ---

class TestExtractTitle:
    def test_h1_title(self):
        nb = _nb([_md("# Mon Titre")])
        assert extract_title(nb) == "Mon Titre"

    def test_h2_title(self):
        nb = _nb([_md("## Section Title")])
        assert extract_title(nb) == "Section Title"

    def test_skips_non_heading(self):
        nb = _nb([_md("Some text\n## Real Title")])
        assert extract_title(nb) == "Real Title"

    def test_no_markdown_cells(self):
        nb = _nb([_code("x = 1")])
        assert extract_title(nb) == ""

    def test_empty_cells(self):
        nb = _nb([])
        assert extract_title(nb) == ""


# --- detect_requirements ---

class TestDetectRequirements:
    def test_no_requirements(self):
        nb = _nb([_code("x = 1")])
        reqs = detect_requirements(nb)
        assert all(not v for v in reqs.values())

    def test_api_requirement(self):
        nb = _nb([_code("import openai")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is True

    def test_gpu_requirement(self):
        nb = _nb([_code("device = torch.device('cuda')")])
        reqs = detect_requirements(nb)
        assert reqs["requires_gpu"] is True

    def test_cloud_requirement(self):
        nb = _nb([_code("qb = QuantBook()")])
        reqs = detect_requirements(nb)
        assert reqs["requires_cloud"] is True

    def test_wsl_requirement(self):
        nb = _nb([_code("import wsl_helper")])
        reqs = detect_requirements(nb)
        assert reqs["requires_wsl"] is True

    def test_multiple_requirements(self):
        nb = _nb([_code("openai.api_key = x\ntorch.cuda.is_available()")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is True
        assert reqs["requires_gpu"] is True

    def test_ignores_markdown(self):
        nb = _nb([_md("# openai is cool")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is False


# --- check_errors ---

class TestCheckErrors:
    def test_no_errors(self):
        assert check_errors([_stream_output()]) == []

    def test_single_error(self):
        assert check_errors([_error_output("ImportError")]) == ["ImportError"]

    def test_multiple_errors(self):
        errors = check_errors([_error_output("Err1"), _stream_output(), _error_output("Err2")])
        assert errors == ["Err1", "Err2"]

    def test_empty_outputs(self):
        assert check_errors([]) == []


# --- determine_status ---

class TestDetermineStatus:
    def _make_path(self, name="Test.ipynb"):
        return NOTEBOOKS_DIR / name

    def test_research_path(self):
        # RESEARCH is keyed off the directory: any path part in
        # RESEARCH_DIR_KEYWORDS (research/archive/examples/partner-course).
        nb = _nb([_code("x=1", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        path = self._make_path("Search/research/Test.ipynb")
        assert determine_status(path, nb, code_cells, reqs, pedagogical=False) == "RESEARCH"

    def test_ready_with_outputs(self):
        nb = _nb([_code("x=1", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "READY"

    def test_broken_with_errors(self):
        nb = _nb([_code("x=1", [_error_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "BROKEN"

    def test_broken_no_outputs_no_deps(self):
        nb = _nb([_code("x=1")])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "BROKEN"

    def test_demo_no_outputs_with_api(self):
        nb = _nb([_code("openai.api_key = 'x'")])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": True, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "DEMO"

    def test_demo_partial_outputs_with_gpu(self):
        # Partial outputs (some cell missing) + external requirement -> DEMO.
        nb = _nb([
            _code("torch.cuda()", [_stream_output()]),
            _code("model.train()"),  # no output
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        reqs = {"requires_api": False, "requires_gpu": True, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "DEMO"

    def test_ready_all_outputs_with_gpu(self):
        # #963: when ALL code cells have outputs, status is READY regardless of
        # requires_* — outputs are proof of successful execution.
        nb = _nb([_code("torch.cuda()", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": True, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "READY"

    def test_ready_empty_code_cells(self):
        nb = _nb([_md("# Title")])
        code_cells = []
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "READY"


# --- count_todos ---

class TestCountTodos:
    def test_no_todos(self):
        nb = _nb([_code("x = 1")])
        assert count_todos(nb) == 0

    def test_single_todo(self):
        # Genuine (non-stub) TODO in an unexecuted cell is counted.
        nb = _nb([_code("compute()  # TODO refine this")])
        assert count_todos(nb) == 1

    def test_multiple_todos(self):
        nb = _nb([
            _code("step1()  # TODO step 1"),
            _code("step2()  # TODO step 2"),
        ])
        assert count_todos(nb) == 2

    def test_case_insensitive(self):
        nb = _nb([_code("model = build()  # todo implement")])
        assert count_todos(nb) == 1

    def test_ignores_markdown(self):
        nb = _nb([_md("# TODO list")])
        assert count_todos(nb) == 0

    def test_excludes_exercise_stub(self):
        # #1644: C.1-compliant exercise stubs (var = None # TODO, pass, ...) are
        # pedagogically complete, not incomplete work -> not counted.
        nb = _nb([_code("x = None  # TODO student")])
        assert count_todos(nb) == 0

    def test_excludes_executed_cell_todo(self):
        # #1480: a TODO in an executed cell (has outputs) is a resolved exercise.
        nb = _nb([_code("result = train()  # TODO tune", [_stream_output()])])
        assert count_todos(nb) == 0


# --- has_markdown_intro_conclusion ---

class TestHasMarkdownIntroConclusion:
    def test_both_present(self):
        cells = [
            _md("# Introduction et objectifs"),
            _code("x = 1"),
            _md("## Conclusion et résumé"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is True
        assert conclusion is True

    def test_no_intro(self):
        cells = [
            _md("# Something else"),
            _code("x = 1"),
            _md("## Conclusion"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is False
        assert conclusion is True

    def test_no_conclusion(self):
        cells = [
            _md("# Introduction"),
            _code("x = 1"),
            _md("## More content"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is True
        assert conclusion is False

    def test_no_markdown(self):
        cells = [_code("x = 1")]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is False
        assert conclusion is False

    def test_french_keywords(self):
        cells = [
            _md("# Objectif du TP"),
            _md("## Pour aller plus loin"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is True
        assert conclusion is True

    def test_intro_in_second_cell(self):
        # #1901-precedent: title + nav header is cell 0, the real intro is in cell 1.
        cells = [
            _md("# Lean-13 Grothendieck\n**Navigation**: [Index](../README.md)"),
            _md("## Introduction : pourquoi Grothendieck dans une serie Lean ?"),
            _code("x = 1"),
            _md("## Conclusion"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is True
        assert conclusion is True

    def test_intro_learning_objectives_phrase(self):
        # "A la fin de ce notebook, vous saurez" is a learning-objectives intro.
        cells = [
            _md("# SW-3 GraphOperations\n## Operations RDF\nA la fin de ce notebook, vous saurez :\n1. Lire un graphe"),
            _md("Importation des espaces de noms"),
            _md("## Conclusion"),
        ]
        intro, _ = has_markdown_intro_conclusion(cells)
        assert intro is True

    def test_intro_vue_densemble(self):
        cells = [
            _md("# Lean-7b\nCe notebook fait suite au precedent."),
            _md("## Vue d'ensemble du notebook"),
            _md("## Conclusion"),
        ]
        intro, _ = has_markdown_intro_conclusion(cells)
        assert intro is True

    def test_conclusion_accented(self):
        # Latent bug fix: accented "Synthèse" must match (accent-stripping).
        cells = [
            _md("# Introduction"),
            _md("## Synthèse des concepts"),
        ]
        _, conclusion = has_markdown_intro_conclusion(cells)
        assert conclusion is True

    def test_conclusion_behind_footer(self):
        # Conclusion is not the last md cell (a nav footer follows).
        cells = [
            _md("# Introduction"),
            _md("## Conclusion et bilan"),
            _md("**Navigation**: [<- Index](../README.md)"),
        ]
        _, conclusion = has_markdown_intro_conclusion(cells)
        assert conclusion is True

    def test_no_intro_continuation_notebook(self):
        # A mid-series continuation with no intro section must NOT be flagged.
        cells = [
            _md("## 7. Orchestration des strategies"),
            _md("### Role des strategies dans Semantic Kernel"),
            _md("## Conclusion"),
        ]
        intro, _ = has_markdown_intro_conclusion(cells)
        assert intro is False

    def test_conclusion_synthese_in_code_fence_ignored(self):
        # Function_Calling FP: "synthese" inside a fenced flow diagram is NOT a
        # conclusion; the notebook ends on a bonus exercise, not a wrap-up section.
        cells = [
            _md("# Introduction"),
            _md("Flux de donnees :\n```\nanalyse -> appel tool -> resultat -> synthese\n```"),
            _md("# Challenge bonus\nA vous de jouer."),
        ]
        _, conclusion = has_markdown_intro_conclusion(cells)
        assert conclusion is False

    def test_conclusion_synthese_heading_outside_fence_matches(self):
        # A genuine "## Synthese des apprentissages" heading must still be detected
        # even when a fenced code block is present elsewhere in the same cell.
        cells = [
            _md("# Introduction"),
            _md("## Synthese des apprentissages\n```\nx = demo()\n```\nCe que nous avons vu."),
        ]
        _, conclusion = has_markdown_intro_conclusion(cells)
        assert conclusion is True

    def test_bilan_alone_is_not_a_conclusion(self):
        # "bilan" was dropped as a keyword: as bare prose ("le bilan des ressources")
        # it does not mark a real wrap-up section (Creative-Video FP).
        cells = [
            _md("# Introduction"),
            _md("Nous affichons le bilan des ressources consommees par technique."),
            _md("## Exercice : creez votre clip."),
        ]
        _, conclusion = has_markdown_intro_conclusion(cells)
        assert conclusion is False


# --- classify_maturity ---

class TestClassifyMaturity:
    def _full_nb(self, cells):
        return _nb(cells, metadata={"kernelspec": {"display_name": "Python 3", "name": "python3"}})

    def test_production(self):
        # Note: code cell must produce output by design — a bare assignment
        # (x = 1) is now filtered as "outputless-by-design" (#1644), so we use
        # an expression that yields a visible result.
        nb = self._full_nb([
            _md("# Introduction"),
            _code("print('result')", [_stream_output()]),
            _md("## Conclusion"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "PRODUCTION"

    def test_beta_missing_conclusion(self):
        nb = self._full_nb([
            _md("# Introduction"),
            _code("print('result')", [_stream_output()]),
            _md("## More"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "BETA"

    def test_alpha_partial_outputs(self):
        nb = self._full_nb([
            _md("# Title"),
            _code("x = 1", [_stream_output()]),
            _code("y = 2"),  # no outputs
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "ALPHA"

    def test_alpha_many_todos(self):
        code_cells = [_code(f"x{i} = None  # TODO {i}", [_stream_output()]) for i in range(7)]
        nb = self._full_nb([_md("# Title")] + code_cells)
        assert classify_maturity(nb, code_cells, "Python 3") == "ALPHA"

    def test_draft_no_outputs(self):
        # Output-producing cell with NO committed output -> DRAFT.
        nb = self._full_nb([
            _md("# Title"),
            _code("print('x')"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "DRAFT"

    def test_draft_no_markdown(self):
        nb = self._full_nb([_code("print('x')", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        assert classify_maturity(nb, code_cells, "Python 3") == "DRAFT"

    def test_draft_too_many_todos(self):
        # >10 counted TODOs -> DRAFT. TODOs only count in unexecuted, non-stub
        # cells (#1480/#1644), so use unexecuted call cells; one executed cell
        # provides outputs so the no-output DRAFT rule does not fire first.
        executed = _code("print('ok')", [_stream_output()])
        todo_cells = [_code(f"func_{i}()  # TODO {i}") for i in range(12)]
        code_cells = [executed] + todo_cells
        nb = self._full_nb([_md("# Title")] + code_cells)
        assert classify_maturity(nb, code_cells, "Python 3") == "DRAFT"


# --- _is_exercise_stub ---

class TestIsExerciseStub:
    def test_pass_with_trailing_todo_comment(self):
        # #1939: "pass  # TODO: ..." must match the bare `pass` pattern after
        # the inline comment is stripped (the marker is also the comment).
        assert _is_exercise_stub(_code('"""docstring"""\npass  # TODO: implementez')) is True

    def test_pass_alone_with_separate_marker(self):
        assert _is_exercise_stub(_code("# TODO student\npass")) is True

    def test_etape_marker(self):
        # # Etape N is a valid C.1 exercise marker (accent-tolerant).
        assert _is_exercise_stub(_code("# Etape: assemblez le systeme\npass  # Etape: a faire")) is True

    def test_etape_accented_marker(self):
        assert _is_exercise_stub(_code("# Étape 2\npass")) is True

    def test_indice_marker(self):
        assert _is_exercise_stub(_code("# Indice: voir l'exemple precedent\npass  # Remplacer")) is True

    def test_print_exercice_completer(self):
        assert _is_exercise_stub(_code('# TODO\nprint("Exercice a completer (phe non installe)")')) is True

    def test_return_none_stub(self):
        assert _is_exercise_stub(_code("# TODO complete\ndef f():\n    return None  # a faire")) is True

    def test_var_assign_none(self):
        assert _is_exercise_stub(_code("result = None  # TODO etudiant")) is True

    def test_comment_only_with_marker(self):
        # An instruction-only cell (only comments) carrying a marker is a stub.
        assert _is_exercise_stub(_code("# TODO: implementez la fonction ci-dessous")) is True

    def test_no_marker_not_a_stub(self):
        # No exercise marker -> not a stub even if it ends with `pass`.
        assert _is_exercise_stub(_code("def f():\n    pass")) is False

    def test_marker_but_real_code_not_a_stub(self):
        # Marker present but the last line is real computed code -> not a stub.
        assert _is_exercise_stub(_code("# TODO refine\nx = compute()\nprint(x)")) is False


# --- _effective_code_cells ---

class TestEffectiveCodeCells:
    def test_excludes_exercise_stub(self):
        # #1939: C.1 exercise stubs are output-free by design and must not be
        # counted against the maturity output-coverage check.
        cells = [
            _code("print('real')", [_stream_output()]),
            _code('"""doc"""\npass  # TODO: implementez'),
        ]
        eff = _effective_code_cells(cells)
        assert len(eff) == 1
        assert eff[0] is cells[0]

    def test_excludes_outputless_by_design(self):
        cells = [_code("print('x')", [_stream_output()]), _code("x = 1")]
        assert len(_effective_code_cells(cells)) == 1

    def test_keeps_real_output_cells(self):
        cells = [_code("print('a')", [_stream_output()]), _code("print('b')", [_stream_output()])]
        assert len(_effective_code_cells(cells)) == 2


# --- classify_maturity: exercise-stub promotion (#1939 regression) ---

class TestClassifyMaturityExerciseStub:
    def _full_nb(self, cells):
        return _nb(cells, metadata={"kernelspec": {"display_name": "Python 3", "name": "python3"}})

    def test_stub_does_not_block_production(self):
        # #1939: a pedagogically complete notebook (intro + conclusion + every
        # real cell has output) must reach PRODUCTION even with a C.1 exercise
        # stub whose `pass  # TODO` produces no output. Before the fix the stub
        # was wrongly counted as a missing-output cell and capped it at ALPHA.
        nb = self._full_nb([
            _md("# Introduction et objectifs"),
            _code("print('demo result')", [_stream_output()]),
            _code('"""Exercice"""\npass  # TODO: implementez la fonction', execution_count=2),
            _md("## Conclusion et synthèse"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "PRODUCTION"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
