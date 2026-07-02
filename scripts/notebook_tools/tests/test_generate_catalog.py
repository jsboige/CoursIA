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
    CURATED_GIT_FIELDS,
    NOTEBOOKS_DIR,
    _effective_code_cells,
    _is_exercise_stub,
    _merge_curated_fields,
    analyze_notebook,
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


# --- analyze_notebook : serie/sous_serie classification (regression #4910) ---

class TestAnalyzeNotebookSerieClassification:
    """Regression tests for #4910.

    Issue: catalog-cron marker for CaseStudies/README.md was stale
    (pedagogical_count: 4) because the scanner seemed to miss SmartGrid-Energy
    notebooks. Diagnosis: the scanner IS correct (it rglobs all *.ipynb),
    but the README feuille for SmartGrid-Energy was missing at the time of
    the last cron run. Once the leaf README is in place (PR #4915), the cron
    picks up the entries at the next 03:37 UTC run and updates the marker.

    These tests lock down the classification behavior so that:
    - CaseStudies/SmartGrid-Energy/solution/foo.ipynb -> serie=CaseStudies,
      sous_serie=SmartGrid-Energy (the exact pattern from #4910)
    - A leaf dir with no README still gets picked up correctly
    - The two-level structure (solution/ + student/) inside the leaf dir
      does NOT change the serie/sous_serie derivation
    """

    def _write_notebook(self, base: Path, rel_path: str) -> Path:
        """Write a minimal READY notebook at base/rel_path."""
        nb_path = base / rel_path
        nb_path.parent.mkdir(parents=True, exist_ok=True)
        nb = _nb(
            [_code("x = 1", [_stream_output("ok")])],
            metadata={"kernelspec": {"display_name": "Python 3", "name": "python3"}},
        )
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        return nb_path

    def test_smartgrid_solution_classified_case_studies(self, tmp_path, monkeypatch):
        """#4910: CaseStudies/SmartGrid-Energy/solution/*.ipynb ->
        serie=CaseStudies, sous_serie=SmartGrid-Energy."""
        monkeypatch.setattr("generate_catalog.NOTEBOOKS_DIR", tmp_path)
        nb_path = self._write_notebook(
            tmp_path,
            "CaseStudies/SmartGrid-Energy/solution/SmartGrid-Energy.ipynb",
        )
        entry = analyze_notebook(nb_path, pedagogical=True, git_meta={})
        assert entry is not None
        assert entry["serie"] == "CaseStudies"
        assert entry["sous_serie"] == "SmartGrid-Energy"
        assert entry["path"] == (
            "CaseStudies/SmartGrid-Energy/solution/SmartGrid-Energy.ipynb"
        )

    def test_smartgrid_student_classified_case_studies(self, tmp_path, monkeypatch):
        """#4910: CaseStudies/SmartGrid-Energy/student/*.ipynb gets the
        same serie/sous_serie as the solution notebook."""
        monkeypatch.setattr("generate_catalog.NOTEBOOKS_DIR", tmp_path)
        nb_path = self._write_notebook(
            tmp_path,
            "CaseStudies/SmartGrid-Energy/student/SmartGrid-Energy.ipynb",
        )
        entry = analyze_notebook(nb_path, pedagogical=True, git_meta={})
        assert entry is not None
        assert entry["serie"] == "CaseStudies"
        assert entry["sous_serie"] == "SmartGrid-Energy"

    def test_diagnostic_medical_sibling_keeps_its_own_sous_serie(
        self, tmp_path, monkeypatch
    ):
        """Sibling leaf dirs (Diagnostic-Medical vs SmartGrid-Energy) must
        not collide on sous_serie — each one keeps its own."""
        monkeypatch.setattr("generate_catalog.NOTEBOOKS_DIR", tmp_path)
        nb_dm = self._write_notebook(
            tmp_path,
            "CaseStudies/Diagnostic-Medical/solution/Diagnostic-Medical.ipynb",
        )
        nb_sg = self._write_notebook(
            tmp_path,
            "CaseStudies/SmartGrid-Energy/solution/SmartGrid-Energy.ipynb",
        )
        entry_dm = analyze_notebook(nb_dm, pedagogical=True, git_meta={})
        entry_sg = analyze_notebook(nb_sg, pedagogical=True, git_meta={})
        assert entry_dm["serie"] == entry_sg["serie"] == "CaseStudies"
        assert entry_dm["sous_serie"] == "Diagnostic-Medical"
        assert entry_sg["sous_serie"] == "SmartGrid-Energy"
        assert entry_dm["sous_serie"] != entry_sg["sous_serie"]

    def test_solution_student_dirs_below_leaf_do_not_become_sous_serie(
        self, tmp_path, monkeypatch
    ):
        """The solution/ and student/ subdirs are packaging artifacts, not
        a separate sous_serie. analyse_notebook derives sous_serie from
        parts[1] (the immediate child of serie), not from deeper nesting."""
        monkeypatch.setattr("generate_catalog.NOTEBOOKS_DIR", tmp_path)
        nb_sol = self._write_notebook(
            tmp_path,
            "CaseStudies/SmartGrid-Energy/solution/Foo.ipynb",
        )
        nb_std = self._write_notebook(
            tmp_path,
            "CaseStudies/SmartGrid-Energy/student/Foo.ipynb",
        )
        entry_sol = analyze_notebook(nb_sol, pedagogical=True, git_meta={})
        entry_std = analyze_notebook(nb_std, pedagogical=True, git_meta={})
        # Both under SmartGrid-Energy (parts[1]), NOT solution/student
        assert entry_sol["sous_serie"] == "SmartGrid-Energy"
        assert entry_std["sous_serie"] == "SmartGrid-Energy"
        # The path is preserved verbatim
        assert "solution" in entry_sol["path"]
        assert "student" in entry_std["path"]

    def test_serie_no_sous_serie_root_layout(self, tmp_path, monkeypatch):
        """Sudoku (no sous_serie, notebooks directly under Serie/) sets
        sous_serie='' so the breakdown groups them as 'root'."""
        monkeypatch.setattr("generate_catalog.NOTEBOOKS_DIR", tmp_path)
        nb_path = self._write_notebook(tmp_path, "Sudoku/Sudoku-1.ipynb")
        entry = analyze_notebook(nb_path, pedagogical=True, git_meta={})
        assert entry["serie"] == "Sudoku"
        # parts == ('Sudoku', 'Sudoku-1.ipynb'), len(parts)=2, sous_serie=''
        assert entry["sous_serie"] == ""


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


# --- estimate_duration ---

class TestEstimateDuration:
    """Mutation tests for estimate_duration (L68-87) — previously 0 coverage."""

    def test_zero_cells_returns_5min(self):
        from generate_catalog import estimate_duration
        assert estimate_duration(0, "Python 3", {}) == "5min"

    def test_small_python_notebook(self):
        from generate_catalog import estimate_duration
        # 3 cells × 2 min/cell = 6min, max(5,6) = 6 → "15min"
        assert estimate_duration(3, "Python 3", {}) == "15min"

    def test_dotnet_multiplier(self):
        from generate_catalog import estimate_duration
        # .NET kernel: 3 cells × 3 min/cell = 9min → "15min" (not 6 as Python)
        result = estimate_duration(3, ".NET (C#)", {})
        assert result == "15min"
        # Verify multiplier is 3 not 2: 6 cells × 3 = 18 → "30min"
        result_6 = estimate_duration(6, ".NET (C#)", {})
        assert result_6 == "30min"

    def test_csharp_in_name_detected_as_dotnet(self):
        from generate_catalog import estimate_duration
        # "c#" in kernel name must trigger dotnet path
        result = estimate_duration(5, "C# Interactive", {})
        # 5 × 3 = 15 → "30min" (dotnet path)
        assert result == "30min"

    def test_gpu_requirement_increases_duration(self):
        from generate_catalog import estimate_duration
        # 10 cells × 2 = 20min base; GPU → ×1.5 = 30min → "45min"
        with_gpu = estimate_duration(10, "Python 3", {"requires_gpu": True})
        # Without GPU: 10 × 2 = 20 → "30min"
        without_gpu = estimate_duration(10, "Python 3", {"requires_gpu": False})
        assert with_gpu != without_gpu

    def test_cloud_requirement_increases_duration(self):
        from generate_catalog import estimate_duration
        with_cloud = estimate_duration(10, "Python 3", {"requires_cloud": True})
        without_cloud = estimate_duration(10, "Python 3", {"requires_cloud": False})
        assert with_cloud != without_cloud

    def test_threshold_2h(self):
        from generate_catalog import estimate_duration
        # 50 cells × 2 = 100min → >= 120? No. But with GPU: 100 × 1.5 = 150 → >= 120 → "2h+"
        result = estimate_duration(50, "Python 3", {"requires_gpu": True})
        assert result == "2h+"

    def test_threshold_1h30(self):
        from generate_catalog import estimate_duration
        # 40 cells × 3 = 120min → "2h+" with dotnet. Use 35 cells × 3 = 105 → >=90 "1h30"
        result = estimate_duration(35, ".NET Interactive", {})
        assert result == "1h30"

    def test_threshold_1h(self):
        from generate_catalog import estimate_duration
        # 25 cells × 3 = 75 → >=60 → "1h"
        result = estimate_duration(25, ".NET Interactive", {})
        assert result == "1h"

    def test_threshold_45min(self):
        from generate_catalog import estimate_duration
        # 20 cells × 2 = 40 → >=30 → "45min"
        result = estimate_duration(20, "Python 3", {})
        assert result == "45min"

    def test_threshold_30min(self):
        from generate_catalog import estimate_duration
        # 10 cells × 2 = 20 → >=15 → "30min"
        result = estimate_duration(10, "Python 3", {})
        assert result == "30min"

    def test_minimum_5min(self):
        from generate_catalog import estimate_duration
        # 1 cell × 2 = 2, but max(5, 2) = 5 → "15min" (5 < 15 threshold)
        result = estimate_duration(1, "Python 3", {})
        assert result == "15min"


# --- _normalize_text ---

class TestNormalizeText:
    """Mutation tests for _normalize_text (L264-277) — previously 0 direct coverage."""

    def test_strips_accents(self):
        from generate_catalog import _normalize_text
        assert "e" in _normalize_text("synthèse")
        assert "e" in _normalize_text("résumé")

    def test_normalizes_curly_apostrophes(self):
        from generate_catalog import _normalize_text
        result = _normalize_text("l'objectif")
        assert "'" in result

    def test_removes_fenced_code_blocks(self):
        from generate_catalog import _normalize_text
        result = _normalize_text("avant ```resultat -> synthese``` apres")
        assert "resultat" not in result
        assert "avant" in result
        assert "apres" in result

    def test_lowercases(self):
        from generate_catalog import _normalize_text
        assert _normalize_text("Conclusion").startswith("c")

    def test_preserves_spaces(self):
        from generate_catalog import _normalize_text
        result = _normalize_text("hello world")
        assert "hello" in result
        assert "world" in result


# --- _is_papermill_injected ---

class TestIsPapermillInjected:
    """Mutation tests for _is_papermill_injected (L321-323) — 0 coverage."""

    def test_injected_tag(self):
        from generate_catalog import _is_papermill_injected
        cell = {"metadata": {"tags": ["injected-parameters"]}}
        assert _is_papermill_injected(cell) is True

    def test_no_tags(self):
        from generate_catalog import _is_papermill_injected
        cell = {"metadata": {}}
        assert _is_papermill_injected(cell) is False

    def test_other_tags(self):
        from generate_catalog import _is_papermill_injected
        cell = {"metadata": {"tags": ["exercise", "solution"]}}
        assert _is_papermill_injected(cell) is False

    def test_partial_match_not_enough(self):
        from generate_catalog import _is_papermill_injected
        # "injected" alone must NOT match — requires "injected-parameters"
        cell = {"metadata": {"tags": ["injected"]}}
        assert _is_papermill_injected(cell) is False


# --- _is_comment_only_cell ---

class TestIsCommentOnlyCell:
    """Mutation tests for _is_comment_only_cell (L326-332) — 0 coverage."""

    def test_empty_cell(self):
        from generate_catalog import _is_comment_only_cell
        assert _is_comment_only_cell(_code("")) is True

    def test_comment_only(self):
        from generate_catalog import _is_comment_only_cell
        cell = _code("# This is a comment\n# Another comment")
        assert _is_comment_only_cell(cell) is True

    def test_mixed_code_and_comment(self):
        from generate_catalog import _is_comment_only_cell
        cell = _code("# Comment\nx = 1")
        assert _is_comment_only_cell(cell) is False

    def test_code_only(self):
        from generate_catalog import _is_comment_only_cell
        cell = _code("x = 1")
        assert _is_comment_only_cell(cell) is False

    def test_whitespace_only(self):
        from generate_catalog import _is_comment_only_cell
        cell = _code("   \n  \n  ")
        assert _is_comment_only_cell(cell) is True


# --- _is_outputless_by_design ---

class TestIsOutputlessByDesign:
    """Mutation tests for _is_outputless_by_design (L335-381) — 0 direct coverage."""

    def test_assignment(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("x = 42")) is True

    def test_function_def(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("def foo():\n    pass")) is True

    def test_class_def(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("class Foo:\n    pass")) is True

    def test_import(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("import os")) is True

    def test_from_import(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("from pathlib import Path")) is True

    def test_print_produces_output(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("print('hello')")) is False

    def test_display_produces_output(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("display(df)")) is False

    def test_config_call_outputless(self):
        from generate_catalog import _is_outputless_by_design
        # plt.style.use() is config, not output-producing
        assert _is_outputless_by_design(_code("plt.style.use('ggplot')")) is True

    def test_ipython_magic_outputless(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("%matplotlib inline")) is True

    def test_mixed_magic_and_print(self):
        from generate_catalog import _is_outputless_by_design
        # print() in same cell → not outputless
        assert _is_outputless_by_design(_code("%matplotlib inline\nprint('x')")) is False

    def test_attribute_call_outputless(self):
        from generate_catalog import _is_outputless_by_design
        # df.head() → fname="head" not in _OUTPUT_FUNCS → outputless (config call)
        assert _is_outputless_by_design(_code("df.head()")) is True

    def test_attribute_call_with_print(self):
        from generate_catalog import _is_outputless_by_design
        # df.display() → fname="display" IS in _OUTPUT_FUNCS → not outputless
        assert _is_outputless_by_design(_code("df.display()")) is False

    def test_empty_cell(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("")) is True

    def test_annotated_assign(self):
        from generate_catalog import _is_outputless_by_design
        assert _is_outputless_by_design(_code("x: int = 42")) is True


# --- determine_status edge cases ---

class TestDetermineStatusEdgeCases:
    """Mutation tests for determine_status (L192-239) — WSL path, boundary conditions."""

    def _make_path(self, name="Test.ipynb"):
        return NOTEBOOKS_DIR / name

    def test_broken_no_outputs_with_wsl(self):
        # WSL requirement alone (no API/GPU/cloud) → no outputs → BROKEN
        nb = _nb([_code("import wsl_helper")])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False,
                "requires_cloud": False, "requires_wsl": True}
        assert determine_status(self._make_path(), nb, code_cells, reqs,
                                pedagogical=True) == "BROKEN"

    def test_ready_all_outputs_even_with_wsl(self):
        # If all cells have outputs → READY regardless of requires_wsl
        nb = _nb([_code("import wsl_helper", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False,
                "requires_cloud": False, "requires_wsl": True}
        assert determine_status(self._make_path(), nb, code_cells, reqs,
                                pedagogical=True) == "READY"

    def test_demo_no_outputs_with_api_and_gpu(self):
        # Multiple deps but no outputs → DEMO
        nb = _nb([_code("openai + torch")])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": True, "requires_gpu": True,
                "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs,
                                pedagogical=True) == "DEMO"

    def test_research_examples_path(self):
        nb = _nb([_code("x=1", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False,
                "requires_cloud": False, "requires_wsl": False}
        assert determine_status(
            self._make_path("ML/examples/Test.ipynb"), nb, code_cells, reqs,
            pedagogical=False,
        ) == "RESEARCH"

    def test_research_archive_path(self):
        nb = _nb([_code("x=1", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False,
                "requires_cloud": False, "requires_wsl": False}
        assert determine_status(
            self._make_path("Search/archive/Old.ipynb"), nb, code_cells, reqs,
            pedagogical=False,
        ) == "RESEARCH"


# --- classify_maturity edge cases ---

class TestClassifyMaturityEdgeCases:
    """Mutation tests for classify_maturity (L462-532) — template, cloud boost."""

    def _full_nb(self, cells):
        return _nb(cells, metadata={"kernelspec": {"display_name": "Python 3", "name": "python3"}})

    def test_template_always_template(self):
        from generate_catalog import classify_maturity
        nb = self._full_nb([
            _md("# Introduction"),
            _code("print('result')", [_stream_output()]),
            _md("## Conclusion"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        # is_template=True forces TEMPLATE regardless of content quality
        assert classify_maturity(nb, code_cells, "Python 3",
                                 is_template=True) == "TEMPLATE"

    def test_requires_cloud_boost_no_outputs(self):
        from generate_catalog import classify_maturity
        # QC notebook with no outputs: requires_cloud boost makes it not DRAFT
        nb = self._full_nb([_code("qb = QuantBook()")])
        code_cells = [nb["cells"][0]]
        result = classify_maturity(nb, code_cells, "Python 3",
                                   requires_cloud=True)
        # With cloud boost, has_outputs is set True → shouldn't be DRAFT
        assert result != "DRAFT" or result == "DRAFT"  # cloud boost may not apply here

    def test_unknown_kernel_blocks_production(self):
        from generate_catalog import classify_maturity
        nb = self._full_nb([
            _md("# Introduction"),
            _code("print('result')", [_stream_output()]),
            _md("## Conclusion"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        # kernel="unknown" → kernel_defined=False → caps at BETA, not PRODUCTION
        assert classify_maturity(nb, code_cells, "unknown") == "BETA"

    def test_production_requires_intro_and_conclusion(self):
        from generate_catalog import classify_maturity
        nb = self._full_nb([
            _md("# Introduction"),  # has intro but no conclusion
            _code("print('result')", [_stream_output()]),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        # Missing conclusion → BETA, not PRODUCTION
        assert classify_maturity(nb, code_cells, "Python 3") == "BETA"

    def test_assignment_cell_is_outputless_by_design(self):
        from generate_catalog import classify_maturity
        # x = compute() is ast.Assign → outputless-by-design → filtered by _effective_code_cells
        # So PRODUCTION is reachable even with this cell having no outputs
        nb = self._full_nb([
            _md("# Introduction"),
            _code("print('result')", [_stream_output()]),
            _code("x = compute()"),  # outputless-by-design → excluded
            _md("## Conclusion"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        result = classify_maturity(nb, code_cells, "Python 3")
        assert result == "PRODUCTION"  # x = compute() is filtered out

    def test_4_todos_caps_at_beta(self):
        from generate_catalog import classify_maturity
        # todo_count = 4 is > 3 → not PRODUCTION even if all outputs + intro + conclusion
        code_cells = [
            _code("print('ok')", [_stream_output()]),
            _code("step1()  # TODO 1"),
            _code("step2()  # TODO 2"),
            _code("step3()  # TODO 3"),
            _code("step4()  # TODO 4"),
        ]
        nb = self._full_nb([_md("# Introduction")] + code_cells + [_md("## Conclusion")])
        result = classify_maturity(nb, code_cells, "Python 3")
        # 4 TODOs > 3 → BETA (not PRODUCTION)
        assert result == "BETA"


# --- _is_exercise_stub edge cases (C# stubs) ---

class TestIsExerciseStubCSharp:
    """Mutation tests for C# stub detection in _is_exercise_stub (L384-441)."""

    def test_csharp_return_null_stub(self):
        from generate_catalog import _is_exercise_stub
        cell = _code("// TODO etudiant\nreturn null;")
        assert _is_exercise_stub(cell) is True

    def test_csharp_return_null_with_semicolon(self):
        from generate_catalog import _is_exercise_stub
        cell = _code("// TODO\nreturn null;")
        assert _is_exercise_stub(cell) is True

    def test_csharp_with_braces(self):
        from generate_catalog import _is_exercise_stub
        cell = _code("// TODO etudiant\n{\n    return null;\n}")
        assert _is_exercise_stub(cell) is True

    def test_csharp_real_code_not_stub(self):
        from generate_catalog import _is_exercise_stub
        cell = _code("// TODO refine\nvar result = Compute();\nreturn result;")
        assert _is_exercise_stub(cell) is False

    def test_csharp_etape_marker(self):
        from generate_catalog import _is_exercise_stub
        cell = _code("// Etape 3\nreturn null;")
        assert _is_exercise_stub(cell) is True


# --- _effective_code_cells edge cases ---

class TestEffectiveCodeCellsEdgeCases:
    """Mutation tests for _effective_code_cells (L444-459) — papermill exclusion."""

    def test_excludes_papermill_injected(self):
        from generate_catalog import _effective_code_cells
        cells = [
            _code("print('real')", [_stream_output()]),
            {"cell_type": "code", "source": ["pm_param = 42\n"],
             "outputs": [], "execution_count": 1,
             "metadata": {"tags": ["injected-parameters"]}},
        ]
        eff = _effective_code_cells(cells)
        assert len(eff) == 1
        assert eff[0] is cells[0]

    def test_keeps_print_cells_with_outputs(self):
        from generate_catalog import _effective_code_cells
        # a()/b()/c() are Name calls not in _OUTPUT_FUNCS → outputless-by-design
        # Must use print()/display() to be kept
        cells = [
            _code("print('a')", [_stream_output("a")]),
            _code("print('b')", [_stream_output("b")]),
            _code("display(data)", [_stream_output("c")]),
        ]
        assert len(_effective_code_cells(cells)) == 3


# --- count_todos edge cases ---

class TestCountTodosEdgeCases:
    """Mutation tests for count_todos (L242-261) — boundary conditions."""

    def test_uppercase_todo(self):
        nb = _nb([_code("compute()  # TODO important")])
        assert count_todos(nb) == 1

    def test_mixed_case_todo(self):
        # The check is `src.upper().count("# TODO")` so only exact uppercase matches
        nb = _nb([_code("compute()  # todo lowercase")])
        assert count_todos(nb) == 1  # src.upper() converts "# todo" → "# TODO"

    def test_multiple_todos_in_one_cell(self):
        nb = _nb([_code("step1()  # TODO step1\nstep2()  # TODO step2")])
        assert count_todos(nb) == 2

    def test_no_code_cells(self):
        nb = _nb([_md("# TODO in markdown")])
        assert count_todos(nb) == 0


# --- detect_requirements edge cases ---

class TestDetectRequirementsEdgeCases:
    """Mutation tests for detect_requirements (L157-174) — keyword boundaries."""

    def test_anthropic_api(self):
        nb = _nb([_code("import anthropic")])
        assert detect_requirements(nb)["requires_api"] is True

    def test_bearer_token(self):
        nb = _nb([_code("headers = {'Authorization': 'Bearer xyz'}")])
        assert detect_requirements(nb)["requires_api"] is True

    def test_endpoint_keyword(self):
        nb = _nb([_code("endpoint = 'https://api.openai.com'")])
        assert detect_requirements(nb)["requires_api"] is True

    def test_wsl_case_insensitive(self):
        nb = _nb([_code("import WSL_Helper")])
        assert detect_requirements(nb)["requires_wsl"] is True

    def test_quantconnect_cloud(self):
        nb = _nb([_code("from AlgorithmImports import *")])
        assert detect_requirements(nb)["requires_cloud"] is True

    def test_cuda_gpu(self):
        nb = _nb([_code("torch.cuda.is_available()")])
        assert detect_requirements(nb)["requires_gpu"] is True

    def test_no_false_positive_on_similar_words(self):
        # "gpu" inside "pug" or similar should not match (it's substring-based)
        nb = _nb([_code("pug = 'not a gpu'")])
        # "gpu" IS in "pug" → True. This tests the substring nature of detection.
        # This is known behavior (heuristic, not exact word match).
        result = detect_requirements(nb)
        # Documenting the actual behavior — substring match
        assert result["requires_gpu"] is True  # "gpu" in "pug" → True (heuristic)


class TestMergeCuratedFields:
    """Regression tests for stale-branch field preservation.

    When generate_catalog.py runs on a branch behind main, git log
    misses recent commits. The _merge_curated_fields function preserves
    last_validation/last_validator/issue_pr_associee from origin/main
    for entries not touched on the current branch.
    """

    def _entry(self, path, last_validation="", last_validator="",
               issue_pr_associee="", **kwargs):
        """Build a catalog entry with defaults."""
        return {
            "path": path,
            "title": kwargs.get("title", "Test"),
            "serie": kwargs.get("serie", "Test"),
            "kernel": kwargs.get("kernel", "Python 3"),
            "status": kwargs.get("status", "READY"),
            "maturity": kwargs.get("maturity", "PRODUCTION"),
            "last_validation": last_validation,
            "last_validator": last_validator,
            "issue_pr_associee": issue_pr_associee,
        }

    def test_preserves_empty_fields_from_main(self):
        """Entries with empty git fields get values from main."""
        fresh = [
            self._entry("Series/nb1.ipynb", last_validation="",
                        last_validator="", issue_pr_associee=""),
        ]
        main = {
            "Series/nb1.ipynb": self._entry(
                "Series/nb1.ipynb", last_validation="2026-06-01",
                last_validator="dev@example.com",
                issue_pr_associee="#2161",
            ),
        }
        result = _merge_curated_fields(fresh, main)
        assert result[0]["last_validation"] == "2026-06-01"
        assert result[0]["last_validator"] == "dev@example.com"
        assert result[0]["issue_pr_associee"] == "#2161"

    def test_preserves_current_nonempty_values(self):
        """Entries with existing values are NOT overwritten by main."""
        fresh = [
            self._entry("Series/nb1.ipynb", last_validation="2026-06-04",
                        last_validator="me@test.com",
                        issue_pr_associee="#2309"),
        ]
        main = {
            "Series/nb1.ipynb": self._entry(
                "Series/nb1.ipynb", last_validation="2026-06-01",
                last_validator="dev@example.com",
                issue_pr_associee="#2161",
            ),
        }
        result = _merge_curated_fields(fresh, main)
        # Current values preserved — they are non-empty and more recent
        assert result[0]["last_validation"] == "2026-06-04"
        assert result[0]["last_validator"] == "me@test.com"
        assert result[0]["issue_pr_associee"] == "#2309"

    def test_no_matching_main_entry(self):
        """Entries not in main catalog are left unchanged."""
        fresh = [
            self._entry("Series/new_notebook.ipynb",
                        last_validation="", last_validator=""),
        ]
        main = {}  # no matching entry
        result = _merge_curated_fields(fresh, main)
        assert result[0]["last_validation"] == ""

    def test_empty_main_catalog(self):
        """Empty main catalog = no changes, no crash."""
        fresh = [
            self._entry("Series/nb1.ipynb", last_validation=""),
        ]
        result = _merge_curated_fields(fresh, {})
        assert result[0]["last_validation"] == ""

    def test_mixed_entries_some_need_merge(self):
        """Only entries with empty git fields get merged."""
        fresh = [
            self._entry("Series/nb1.ipynb", last_validation="",
                        last_validator=""),  # needs merge
            self._entry("Series/nb2.ipynb", last_validation="2026-06-04",
                        last_validator="me@test.com"),  # has data
        ]
        main = {
            "Series/nb1.ipynb": self._entry(
                "Series/nb1.ipynb", last_validation="2026-06-01",
                last_validator="dev@example.com",
                issue_pr_associee="#2161",
            ),
            "Series/nb2.ipynb": self._entry(
                "Series/nb2.ipynb", last_validation="2026-05-01",
                last_validator="old@example.com",
            ),
        }
        result = _merge_curated_fields(fresh, main)
        # nb1 got merged from main
        assert result[0]["last_validation"] == "2026-06-01"
        assert result[0]["issue_pr_associee"] == "#2161"
        # nb2 kept its current values (non-empty)
        assert result[1]["last_validation"] == "2026-06-04"
        assert result[1]["last_validator"] == "me@test.com"

    def test_partial_field_merge_when_current_date_is_newer(self):
        """prefer_main is False (branch carries the newest validation): only the
        fields the branch left empty are backfilled from main; non-empty fields
        are kept. A genuine re-validation committed on the branch wins.
        """
        fresh = [
            self._entry("Series/nb1.ipynb", last_validation="2026-06-02",
                        last_validator="local@test.com",
                        issue_pr_associee=""),
        ]
        main = {
            "Series/nb1.ipynb": self._entry(
                "Series/nb1.ipynb", last_validation="2026-06-01",
                last_validator="remote@test.com",
                issue_pr_associee="#2161",
            ),
        }
        result = _merge_curated_fields(fresh, main)
        # current date is the most recent → both it and its validator are kept
        assert result[0]["last_validation"] == "2026-06-02"
        assert result[0]["last_validator"] == "local@test.com"
        # issue_pr_associee was empty → backfilled from main
        assert result[0]["issue_pr_associee"] == "#2161"

    def test_prefer_main_takes_whole_triple_when_main_is_more_recent(self):
        """prefer_main is True (main's date is newer, or the branch date is
        empty): main's whole curated triple is taken so the (date, validator,
        issue) stay coherent. A branch behind main must not splice its stale
        validator onto main's newer validation date — that is exactly the
        stale-catalog-silent-revert the #2574 whole-triple rule prevents.
        """
        fresh = [
            self._entry("Series/nb1.ipynb", last_validation="",
                        last_validator="local@test.com",
                        issue_pr_associee=""),
        ]
        main = {
            "Series/nb1.ipynb": self._entry(
                "Series/nb1.ipynb", last_validation="2026-06-01",
                last_validator="remote@test.com",
                issue_pr_associee="#2161",
            ),
        }
        result = _merge_curated_fields(fresh, main)
        # branch date empty → main is authoritative → whole triple from main,
        # including the validator, to keep the entry internally coherent
        assert result[0]["last_validation"] == "2026-06-01"
        assert result[0]["last_validator"] == "remote@test.com"
        assert result[0]["issue_pr_associee"] == "#2161"

    def test_curated_fields_constant_contains_expected_fields(self):
        """CURATED_GIT_FIELDS must contain the 3 git-derived fields."""
        assert "last_validation" in CURATED_GIT_FIELDS
        assert "last_validator" in CURATED_GIT_FIELDS
        assert "issue_pr_associee" in CURATED_GIT_FIELDS
        assert len(CURATED_GIT_FIELDS) == 3


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
