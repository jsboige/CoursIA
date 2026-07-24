"""Tests for scripts/notebook_tools/detect_solution_leaks.py — solution leak scanner.

Tests focus on pure functions: is_stub_code, scan_notebook, discover_notebooks.
Uses synthetic notebook dicts and tmp_path for filesystem isolation.
"""

import json
import re
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_solution_leaks import (
    EXERCISE_HEADER_RE,
    SOUMIS_PAR_RE,
    SOLUTION_MARKER_RE,
    STUB_PATTERNS,
    _last_exercise_header_match,
    _numbered_exercise_header_between,
    closest_preceding_header_is_example,
    code_cell_first_comment_labels_example,
    commented_template_stub,
    discover_notebooks,
    is_stub_code,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells: list[dict]) -> dict:
    return {"cells": cells, "metadata": {}}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": [source]}


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# is_stub_code
# ---------------------------------------------------------------------------

class TestIsStubCode:
    def test_pass_is_stub(self):
        assert is_stub_code("pass") is True

    def test_indented_pass_is_stub(self):
        # Regression: the `^\s*pass\s*$` stub pattern requires re.MULTILINE to
        # match an INDENTED `pass` inside a function body (the real-world stub
        # case). Without MULTILINE it only matched a top-level `pass` at the
        # start of the cell, so function-stub exercises (def f(): ... pass)
        # were systematically false-positive as HIGH leaks across the Python
        # notebooks (e.g. CSP-2 path_consistency).
        code = (
            'def path_consistency(csp, domains):\n'
            '    """Apply path consistency."""\n'
            '    # A COMPLETER\n'
            '    # Pour chaque paire (Xi, Xj) ...\n'
            '    pass\n'
            'print("Exercice 2 : implementer path_consistency")\n'
        )
        assert is_stub_code(code) is True

    def test_print_exercice_a_completer(self):
        assert is_stub_code('print("Exercice a completer")') is True

    def test_return_none(self):
        assert is_stub_code("return None") is True

    def test_todo_comment(self):
        assert is_stub_code("# TODO: implement") is True

    def test_console_writeline_french(self):
        assert is_stub_code('Console.WriteLine("Exercice a completer")') is True

    def test_real_code_not_stub(self):
        code = "def solve(x):\n    return x ** 2 + 3 * x + 1\nresult = solve(42)"
        assert is_stub_code(code) is False

    def test_empty_is_stub(self):
        assert is_stub_code("") is True

    def test_whitespace_only_is_stub(self):
        assert is_stub_code("   \n  \n  ") is True

    def test_single_import_plus_pass(self):
        assert is_stub_code("import numpy as np\npass") is True

    def test_two_code_lines_not_stub(self):
        code = "x = compute(data)\ny = transform(x)"
        assert is_stub_code(code) is False

    def test_import_only_is_stub(self):
        assert is_stub_code("import pandas as pd") is True

    def test_comment_only_is_stub(self):
        assert is_stub_code("# just a comment\n# another") is True

    def test_csharp_pass_is_stub(self):
        # C# comments start with //
        assert is_stub_code("// TODO\nreturn null;") is True

    def test_csharp_multiline_todo_stub(self):
        # Regression: a richly-scaffolded C# exercise stub (TODO + Etapes +
        # default return + display call) has many code lines, so the
        # `len(code_lines) <= 1` shortcut does NOT apply. Before recognizing
        # `// TODO` as a stub marker, these were systematically false-positive
        # as HIGH leaks across the .NET Interactive notebooks (GameTheory etc.).
        code = (
            "// Exercice 1 (a completer) : voisinage de swap\n"
            "// TODO etudiant : implémenter ExploreSwapNeighbors\n"
            "// Etape 1 : iterer sur swaps. Etape 2 : calculer les voisins.\n"
            "public List<(OrdinalGame, string, int)> ExploreSwapNeighbors(OrdinalGame g)\n"
            "{\n"
            "    // TODO etudiant\n"
            "    return new List<(OrdinalGame, string, int)>();\n"
            "}\n"
            'display("Exercice 1 : stub a completer.");'
        )
        assert is_stub_code(code) is True

    def test_lean_dashdash_todo_is_stub(self):
        # Lean line comments start with `--`, not `#` or `//`. Exercise stubs
        # like `-- TODO etudiant` were systematically false-positive as HIGH
        # leaks across the Lean notebooks (e.g. SocialChoice-02 cell 32).
        code = (
            "-- EXERCICE 4 : Verifier que le Pareto est respecte\n"
            "-- TODO etudiant : calculer si la SWF respecte Pareto\n"
            "#eval dictatorship_alice profils"
        )
        assert is_stub_code(code) is True

    def test_lean_sorry_is_stub(self):
        # `sorry` admits the goal — an exercise proof using it is a stub.
        assert is_stub_code("theorem ex : 1 + 1 = 2 := by sorry") is True

    def test_dotnet_display_a_completer_is_stub(self):
        # .NET Interactive `.Display("...a completer")` idiom; the existing
        # patterns only covered Console.WriteLine / print.
        assert is_stub_code('display("Exercice 2 : stub a completer.")') is True
        assert is_stub_code('foo.Display("stub a compléter")') is True

    def test_python_assign_none_todo_is_stub(self):
        # `matrice = None  # Remplacez None` defers the work to the student.
        # `return None` only matches a return statement, not this assignment.
        code = (
            "matrice = None  # Remplacez None\n"
            "transposee = None  # Remplacez None\n"
            "produit = None  # TODO etudiant\n"
            'print("resultats")'
        )
        assert is_stub_code(code) is True

    def test_python_assign_none_without_stub_intent_not_stub(self):
        # A bare `x = None` without a stub-intent comment is NOT a stub
        # (avoids false-negative on real code that resets a variable).
        assert is_stub_code("x = None\ny = compute(x)\nz = process(y)") is False

    def test_real_lean_without_stub_not_stub(self):
        # Regression guard: a real Lean proof with no sorry/TODO is not a stub.
        code = "theorem add_comm (n m : Nat) : n + m = m + n := by\n  omega"
        assert is_stub_code(code) is False


# ---------------------------------------------------------------------------
# EXERCISE_HEADER_RE
# ---------------------------------------------------------------------------

class TestExerciseHeaderRe:
    def test_french_exercice(self):
        m = EXERCISE_HEADER_RE.search("## Exercice 1 : Tri")
        assert m is not None
        assert m.group(1) == "1"
        assert "Tri" in m.group(2)

    def test_exercice_no_number(self):
        m = EXERCISE_HEADER_RE.search("### Exercice")
        assert m is not None

    def test_english_exercise(self):
        m = EXERCISE_HEADER_RE.search("# Exercise 3: Sorting")
        assert m is not None
        assert m.group(1) == "3"

    def test_with_dot_separator(self):
        m = EXERCISE_HEADER_RE.search("## 2. Exercice")
        assert m is not None

    def test_no_match_regular_heading(self):
        assert EXERCISE_HEADER_RE.search("## Introduction") is None

    def test_no_match_example(self):
        assert EXERCISE_HEADER_RE.search("## Exemple guide") is None

    def test_h3_exercice(self):
        m = EXERCISE_HEADER_RE.search("### Exercice 5")
        assert m is not None
        assert m.group(1) == "5"


# ---------------------------------------------------------------------------
# SOUMIS_PAR_RE
# ---------------------------------------------------------------------------

class TestSoumisParRe:
    def test_french(self):
        assert SOUMIS_PAR_RE.search("Solution soumis par Jean") is not None

    def test_english(self):
        assert SOUMIS_PAR_RE.search("submitted by Alice") is not None

    def test_no_match(self):
        assert SOUMIS_PAR_RE.search("Random text") is None


# ---------------------------------------------------------------------------
# SOLUTION_MARKER_RE
# ---------------------------------------------------------------------------

class TestSolutionMarkerRe:
    def test_solution(self):
        assert SOLUTION_MARKER_RE.search("# Solution") is not None

    def test_reponse(self):
        assert SOLUTION_MARKER_RE.search("## Reponse") is not None

    def test_resultat(self):
        assert SOLUTION_MARKER_RE.search("Resultat:") is not None

    def test_no_match(self):
        assert SOLUTION_MARKER_RE.search("Code here") is None


# ---------------------------------------------------------------------------
# scan_notebook
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_stub_exercise(self, tmp_path):
        nb_path = _write_nb(tmp_path / "clean.ipynb", [
            _md("## Exercice 1 : Tri"),
            _code("pass"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_solution_leak_high(self, tmp_path):
        nb_path = _write_nb(tmp_path / "leak.ipynb", [
            _md("## Exercice 1 : Tri"),
            _code("# Solution\ndef quicksort(arr):\n    if len(arr) <= 1:\n        return arr\n    pivot = arr[0]\n    left = [x for x in arr[1:] if x <= pivot]\n    right = [x for x in arr[1:] if x > pivot]\n    return quicksort(left) + [pivot] + quicksort(right)\nresult = quicksort(data)\nprint(result)"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "HIGH" for f in findings)

    def test_soumis_par_leak(self, tmp_path):
        nb_path = _write_nb(tmp_path / "soumis.ipynb", [
            _md("## Exercice 2 soumis par Alice"),
            _code("x = complex_calc(data)\ny = transform(x)\nresult = finalize(y)"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "HIGH" for f in findings)
        assert any("soumis par" in f["message"] for f in findings)

    def test_soumis_par_with_stub_ok(self, tmp_path):
        nb_path = _write_nb(tmp_path / "ok.ipynb", [
            _md("## Exercice 2 soumis par Alice"),
            _code("pass"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_duplicate_exercise_number(self, tmp_path):
        nb_path = _write_nb(tmp_path / "dup.ipynb", [
            _md("## Exercice 1 : First"),
            _code("pass"),
            _md("## Exercice 1 : Second"),
            _code("pass"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "MEDIUM" for f in findings)

    def test_no_exercises_clean(self, tmp_path):
        nb_path = _write_nb(tmp_path / "none.ipynb", [
            _md("# Title"),
            _code("x = 1"),
            _md("## Conclusion"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_invalid_json(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{invalid json!!!", encoding="utf-8")
        findings = scan_notebook(str(bad))
        assert any(f["severity"] == "ERROR" for f in findings)

    def test_code_cell_gap(self, tmp_path):
        """Next code cell within 3 cells after exercise header with >8 lines."""
        nb_path = _write_nb(tmp_path / "gap.ipynb", [
            _md("## Exercice 1"),
            _md("Some instructions"),
            _md("More instructions"),
            _code("def solve():\n    data = load()\n    x = preprocess(data)\n    y = model(x)\n    z = postprocess(y)\n    result = validate(z)\n    return result\noutput = solve()\nprint(output)"),
        ])
        findings = scan_notebook(str(nb_path))
        assert any(f["severity"] == "HIGH" for f in findings)

    def test_code_cell_too_far(self, tmp_path):
        """Next code cell beyond 3 cells is not checked."""
        nb_path = _write_nb(tmp_path / "far.ipynb", [
            _md("## Exercice 1"),
            _md("A"),
            _md("B"),
            _md("C"),
            _code("def solve():\n    return complex_thing(data)\nresult = solve()"),
        ])
        findings = scan_notebook(str(nb_path))
        assert len(findings) == 0

    def test_exercise_no_number(self, tmp_path):
        nb_path = _write_nb(tmp_path / "nonum.ipynb", [
            _md("## Exercice"),
            _code("x = full_solution(data)\ny = process(x)\nresult = y"),
        ])
        findings = scan_notebook(str(nb_path))
        # No soumis par, but has solution marker or >8 lines
        assert any(f["severity"] == "HIGH" for f in findings)


# ---------------------------------------------------------------------------
# discover_notebooks
# ---------------------------------------------------------------------------

class TestDiscoverNotebooks:
    def test_finds_notebooks(self, tmp_path):
        (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "b.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 2

    def test_excludes_checkpoints(self, tmp_path):
        (tmp_path / ".ipynb_checkpoints").mkdir()
        (tmp_path / ".ipynb_checkpoints" / "hidden.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "visible.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_excludes_output_files(self, tmp_path):
        (tmp_path / "nb.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "nb_output.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_excludes_output_dir(self, tmp_path):
        (tmp_path / "_output").mkdir()
        (tmp_path / "_output" / "exec.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "real.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_empty_dir(self, tmp_path):
        result = discover_notebooks(str(tmp_path))
        assert result == []

    def test_nested_dirs(self, tmp_path):
        sub = tmp_path / "sub" / "deep"
        sub.mkdir(parents=True)
        (sub / "nb.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert len(result) == 1

    def test_sorted_output(self, tmp_path):
        (tmp_path / "z.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert result[0].endswith("a.ipynb")
        assert result[1].endswith("z.ipynb")

    def test_non_ipynb_ignored(self, tmp_path):
        (tmp_path / "readme.md").write_text("hello", encoding="utf-8")
        (tmp_path / "script.py").write_text("pass", encoding="utf-8")
        result = discover_notebooks(str(tmp_path))
        assert result == []


# ---------------------------------------------------------------------------
# STUB_PATTERNS constants
# ---------------------------------------------------------------------------

class TestStubPatterns:
    def test_patterns_exist(self):
        assert len(STUB_PATTERNS) > 0

    def test_patterns_are_valid_regex(self):
        for pattern in STUB_PATTERNS:
            assert re.compile(pattern) is not None


# ---------------------------------------------------------------------------
# Worked-example attribution (closest-preceding-header-wins, precision fix)
# ---------------------------------------------------------------------------

# A non-stub code body (>8 lines, no stub markers) so the detector would flag it
# as a HIGH leak if it were under an Exercice header.
_SOLUTION_BODY = "\n".join(
    [
        "def solve(x):",
        "    # Solution complete",
        "    a = x + 1",
        "    b = a * 2",
        "    c = b - 3",
        "    d = c ** 2",
        "    e = d % 7",
        "    f = e // 2",
        "    g = f + x",
        "    return g",
    ]
)


class TestClosestPrecedingHeaderIsExample:
    def _cells(self, *specs):
        cells = []
        for ct, src in specs:
            cells.append({"cell_type": ct, "source": [src]})
        return cells

    def test_example_header_is_true(self):
        cells = self._cells(("markdown", "### Exemple guide : demo"), ("code", _SOLUTION_BODY))
        assert closest_preceding_header_is_example(cells, 1) is True

    def test_exercise_header_is_false(self):
        cells = self._cells(("markdown", "### Exercice 4 : a faire"), ("code", _SOLUTION_BODY))
        assert closest_preceding_header_is_example(cells, 1) is False

    def test_no_header_is_false(self):
        cells = self._cells(("markdown", "Just some prose, no header."), ("code", _SOLUTION_BODY))
        assert closest_preceding_header_is_example(cells, 1) is False

    def test_intervening_example_header_wins_over_section(self):
        # "## 10. Exercices" section header, then "### Exemple guide" sub-header,
        # then code: the code belongs to the worked example, NOT the section.
        cells = self._cells(
            ("markdown", "## 10. Exercices\n\nQuelques exercices."),
            ("markdown", "### Exemple guide : cas resolu"),
            ("code", _SOLUTION_BODY),
        )
        assert closest_preceding_header_is_example(cells, 2) is True

    def test_multi_header_single_cell_last_line_wins(self):
        # One markdown cell holding BOTH a section header and a closer example
        # sub-header (the Lean-11 case). The LAST header line wins.
        cells = self._cells(
            ("markdown", "## 8. Exercices\n\nIntro.\n\n### Exemple guide 1 : demo"),
            ("code", _SOLUTION_BODY),
        )
        assert closest_preceding_header_is_example(cells, 1) is True

    def test_prose_between_code_and_header_still_finds_it(self):
        # A prose-only markdown cell between the example header and the code does
        # not break attribution: scan keeps going back to the example header.
        cells = self._cells(
            ("markdown", "### Exemple guide : demo"),
            ("markdown", "Un paragraphe explicatif sans header."),
            ("code", _SOLUTION_BODY),
        )
        assert closest_preceding_header_is_example(cells, 2) is True


class TestCodeCellFirstCommentLabelsExample:
    # Worked examples sometimes label themselves via a leading CODE comment
    # ('# Exemple guide : ...') under a '## Exercices' section, with no markdown
    # sub-header. The first-comment check suppresses that false positive.
    def test_python_example_comment_is_true(self):
        assert code_cell_first_comment_labels_example(
            "# Exemple guide : Apprendre grandmother/2\nPOS_GM = [...]\n"
        ) is True

    def test_numbered_example_comment_is_true(self):
        assert code_cell_first_comment_labels_example(
            "# Exemple guide 1 : Operateur OR parametrique\n..."
        ) is True

    def test_csharp_example_comment_is_true(self):
        assert code_cell_first_comment_labels_example(
            "// Example 1 : extend the schema\npublic void Foo() { }"
        ) is True

    def test_exercise_comment_is_false(self):
        assert code_cell_first_comment_labels_example(
            "# Exercice : Apprendre mother/2\n# TODO etudiant\nprint('a completer')"
        ) is False

    def test_real_code_no_comment_is_false(self):
        assert code_cell_first_comment_labels_example(
            "def solve(x):\n    return x + 1\n"
        ) is False

    def test_leading_blank_then_example_comment_is_true(self):
        # Blank/whitespace lines before the label are skipped.
        assert code_cell_first_comment_labels_example(
            "\n   \n# Exemple resolu : cas simple\nresult = compute()"
        ) is True

    def test_empty_is_false(self):
        assert code_cell_first_comment_labels_example("") is False


class TestWorkedExampleFalsePositiveSuppression:
    def test_worked_example_under_exercises_section_not_flagged(self, tmp_path):
        # The measured false positive: a complete code cell under a "## Exercices"
        # section header whose immediate sub-header is "### Exemple guide".
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("## 10. Exercices\n\nSection intro."),
                _md("### Exemple guide : cas resolu\n\nOn montre..."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        assert not any(f.get("severity") == "HIGH" for f in findings)

    def test_real_exercise_still_flagged(self, tmp_path):
        # True positive preserved: code cell directly under "### Exercice N".
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("### Exercice 3 : a completer\n\nImplementez..."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1
        assert highs[0]["cell_index"] == 1

    def test_worked_example_self_labeled_by_code_comment_not_flagged(self, tmp_path):
        # The SL-5 residual false positive: a "## Exercices" section header
        # followed directly by a code cell whose FIRST comment line self-labels
        # as a worked example ('# Exemple guide : ...'). There is NO intervening
        # markdown sub-header to attribute to, so header-only attribution would
        # wrongly flag it. The code-comment check suppresses the FP.
        body = "# Exemple guide : Apprendre grandmother/2\n" + _SOLUTION_BODY
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("## 8. Exercices\n\nSection intro."),
                _code(body),
            ],
        )
        findings = scan_notebook(str(nb))
        assert not any(f.get("severity") == "HIGH" for f in findings)

    def test_cross_cell_higher_header_breaks_attribution(self, tmp_path):
        # The Kokoro / Infer-6 residual false positive: an "### Exercice 3"
        # header, then an intervening SAME-OR-HIGHER-level section header
        # ("## Conclusion"), then a demo code cell. The code belongs to the
        # Conclusion section, not the exercise — the intervening header breaks
        # the attribution. Without the guard this is wrongly flagged HIGH.
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("---\n\n### Exercice 3 : Synthese\n\nObjectif..."),
                _md("## Conclusion\n\nRecap."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        assert not any(f.get("severity") == "HIGH" for f in findings)

    def test_cross_cell_sibling_header_breaks_attribution(self, tmp_path):
        # Same-level sibling header also breaks: "### Exercice 2" (level 3)
        # followed by "### 6.1 Fonctions" (level 3 sibling) then a code cell.
        # The code belongs to section 6.1, not the exercise.
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("### Exercice 2 : Impact du prior\n\nObjectif..."),
                _md("### 6.1 Fonctions de diagnostic\n\nDetails..."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        assert not any(f.get("severity") == "HIGH" for f in findings)

    def test_deeper_subheader_does_not_break_attribution(self, tmp_path):
        # Recall guard: a DEEPER sub-header ("### Indice" under a "## Exercice 1"
        # level-2 header) is a CHILD of the exercise, not a new section. The code
        # after it is still the exercise's and MUST stay flagged (no recall
        # regression from the cross-cell guard).
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("## Exercice 1 : Objectif\n\nEnonce..."),
                _md("### Indice\n\nPensez a la reciprocite."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1
        assert highs[0]["cell_index"] == 2


# ---------------------------------------------------------------------------
# Commented-template stub (commented-solution-prompt precision fix)
# ---------------------------------------------------------------------------

class TestCommentedTemplateStub:
    # A code cell whose whole solution is COMMENTED OUT and whose only
    # executable code is data assignments + a prompt print is a legitimate
    # exercise skeleton (the student uncomments and fills the TODOs), not a
    # leak. The helper returns True (suppress) for these.

    def test_commented_python_class_plus_data_is_stub(self):
        # The measured Search-3 cell 64 false positive: WeightedGridProblem
        # class + weighted_manhattan + A* call all commented out, only the
        # weighted_grid test data and a prompt print execute.
        code = (
            "# --- Exercice 5 : Pathfinding sur grille ponderee ---\n"
            "# class WeightedGridProblem(GridProblem):\n"
            "#     def actions(self, state):\n"
            "#         return [...]\n"
            "#     def step_cost(self, state, action, next_state):\n"
            "#         pass  # student fills here\n"
            "# def weighted_manhattan(state, goal, min_cost):\n"
            "#     pass  # student fills here\n"
            "weighted_grid = [\n"
            "    [2, 2, 2, 2, 2, 2, 2, 2],\n"
            "    [2, 3, 3, 3, 0, 2, 2, 2],\n"
            "]\n"
            'print("Exercice 5 : implementez les TODO ci-dessus.")\n'
        )
        assert commented_template_stub(code) is True

    def test_commented_loop_plus_empty_list_is_stub(self):
        # The measured ML-FinBERT cell 13 false positive: mes_titres empty list
        # with commented TODO items, the for-loop commented out, a prompt print.
        code = (
            "# Exercice 1 - Votre propre jeu de titres\n"
            "# Etape 1: completez la liste mes_titres ci-dessous.\n"
            "mes_titres = [\n"
            "    # 'TODO etudiant: titre 1',\n"
            "    # 'TODO etudiant: titre 2',\n"
            "]\n"
            "# for h in mes_titres:\n"
            "#     print(h, finbert_sentiment(h))\n"
            "print('Exercice 1 a completer')\n"
        )
        assert commented_template_stub(code) is True

    def test_assignment_none_stubs_with_prompt_is_stub(self):
        # The measured Lab4 cell 22 false positive: three `= None` assignment
        # stubs (no trailing inline comment, so the assignment-stub STUB_PATTERN
        # does not match) plus prints. 'votre code' carries the prompt marker.
        code = (
            "# Votre code pour l'Exercice 1\n"
            "df['mois'] = None\n"
            "ca_par_mois = None\n"
            "mois_max_ca = None\n"
            "print(ca_par_mois)\n"
        )
        assert commented_template_stub(code) is True

    def test_real_executable_def_is_not_stub(self):
        # Recall guard: a real solution with an EXECUTABLE def is never a
        # commented-template stub.
        code = (
            "# Exercice : implementez f\n"
            "def f(x):\n"
            "    return x * 2\n"
            "print(f(5))\n"
        )
        assert commented_template_stub(code) is False

    def test_real_executable_loop_is_not_stub(self):
        # Recall guard: a real solution with a non-trivial executable line (a
        # loop) is never a commented-template stub, even with no def.
        code = (
            "# Exercice : sommez la liste\n"
            "total = 0\n"
            "for x in data:\n"  # non-trivial executable line
            "    total += x\n"
            "print(total)\n"
        )
        assert commented_template_stub(code) is False

    def test_no_prompt_marker_is_not_stub(self):
        # Recall guard: trivial executable code WITHOUT a prompt/TODO marker is
        # not suppressed (a complete trivial solution never carries a prompt).
        code = (
            "weighted_grid = [[2, 2], [3, 3]]\n"
            "start_w = (0, 0)\n"
            'print("resultat")\n'
        )
        assert commented_template_stub(code) is False


class TestCommentedTemplateSuppression:
    def test_commented_template_under_exercice_not_flagged(self, tmp_path):
        # Integration: the commented-template cell under an Exercice header is
        # not flagged HIGH (the FP class is suppressed end-to-end).
        body = (
            "# Exercice 5 : implementez\n"
            "# class Foo:\n"
            "#     def bar(self):\n"
            "#         pass  # student fills\n"
            "data = [1, 2, 3]\n"
            'print("Exercice 5 : implementez les TODO ci-dessus.")\n'
        )
        nb = _write_nb(
            tmp_path / "nb.ipynb",
            [
                _md("### Exercice 5 : a completer\n\nImplementez la classe."),
                _code(body),
            ],
        )
        findings = scan_notebook(str(nb))
        assert not any(f.get("severity") == "HIGH" for f in findings)


# ---------------------------------------------------------------------------
# Exercise-header attribution precision (multi-header + num-less-section FP
# class fixes for #8084).
# ---------------------------------------------------------------------------


class TestLastExerciseHeaderMatch:
    """The `_last_exercise_header_match` helper picks the LAST numbered match
    in a single markdown cell. Used by the detector to close the `Exercice ?`
    message class for multi-header cells (parent num-less `## N. Exercices`
    + numbered sub-header `### Exercice M`).
    """

    def test_single_numbered_header(self):
        m = _last_exercise_header_match("## Exercice 5 : a faire")
        assert m is not None
        assert m.group(1) == "5"

    def test_single_numless_header(self):
        m = _last_exercise_header_match("## Exercices")
        assert m is not None
        assert m.group(1) == ""

    def test_multi_header_picks_last_numbered(self):
        # The exact real-world pattern: num-less parent + numbered sub-header.
        src = "## 6. Exercices\n\nIntro.\n\n### Exercice 1 — Volume d'un noeud torique"
        m = _last_exercise_header_match(src)
        assert m is not None
        assert m.group(1) == "1", "last numbered match must win (closes Exercice ? FP)"

    def test_multi_header_all_numless(self):
        # Two num-less headers (no numbered anywhere) — last one wins.
        src = "## 6. Exercices\n\n### Exercices avances"
        m = _last_exercise_header_match(src)
        assert m is not None
        assert m.group(1) == "", "with no numbered matches, last match wins"

    def test_multi_header_recall_keeps_numbered(self):
        # Recall guard: when MULTIPLE numbered matches exist in the same cell
        # (the "suggestions block" pattern, e.g. a num-less parent + multiple
        # numbered `#### Exercice 1, 2, 3` siblings), the helper falls back to
        # the FIRST match to preserve the original numbering semantics. The
        # suggestions are a SEPARATE numbering, not duplicates of earlier
        # exercises — switching to "last numbered" would surface phantom
        # duplicate-number MEDIUM findings.
        src = "## Exercice 1 : Foo\n\n## Exercice 2 : Bar"
        m = _last_exercise_header_match(src)
        assert m is not None
        assert m.group(1) == "1", "with multiple numbered matches, first match wins (suggestions-block recall)"

    def test_suggestions_block_pattern_first_match(self):
        # The real-world SUGG-BLOCK pattern that introduced the duplicate-MEDIUM
        # regression when always picking the last numbered match.
        src = "## Conclusion et exercices\n\n### Exercices suggeres\n\n#### Exercice 1 : Foo\n\n#### Exercice 2 : Bar\n\n#### Exercice 3 : Baz"
        m = _last_exercise_header_match(src)
        assert m is not None
        assert m.group(1) == "", "first match (num-less 'Exercices suggeres') wins when multiple numbered siblings follow"

    def test_no_match(self):
        assert _last_exercise_header_match("## Introduction") is None


class TestNumberedExerciseHeaderBetween:
    """The `_numbered_exercise_header_between` helper detects a numbered
    sub-header sitting between a num-less parent and the next code cell. When
    True, the detector skips the num-less parent so the code cell is not
    double-flagged.
    """

    def _cells(self, *specs):
        return [{"cell_type": ct, "source": [src]} for ct, src in specs]

    def test_numbered_subheader_present(self):
        cells = self._cells(
            ("markdown", "## Exercices\n\nSection intro."),
            ("markdown", "### Exercice 1 : foo"),
            ("code", "x = 1"),
        )
        assert _numbered_exercise_header_between(cells, 0, 2) is True

    def test_no_subheader(self):
        cells = self._cells(
            ("markdown", "## Exercices\n\nSection intro."),
            ("code", "x = 1"),
        )
        assert _numbered_exercise_header_between(cells, 0, 1) is False

    def test_only_numless_subheader(self):
        # A sibling num-less sub-header does NOT count — we need a numbered one.
        cells = self._cells(
            ("markdown", "## 6. Exercices\nIntro."),
            ("markdown", "### Exercices avances"),
            ("code", "x = 1"),
        )
        assert _numbered_exercise_header_between(cells, 0, 2) is False

    def test_intervening_code_does_not_break(self):
        # A code cell between the two markdown cells (the helper iterates
        # strictly between) — still finds the numbered sub-header.
        cells = self._cells(
            ("markdown", "## Exercices"),
            ("code", "intro_print()"),
            ("markdown", "### Exercice 1 : foo"),
            ("code", "real_solution()"),
        )
        assert _numbered_exercise_header_between(cells, 0, 3) is True


class TestMultiHeaderAttributionFix:
    """End-to-end integration tests for the two FP-class fixes. Mirrors the
    recall-guard pattern used in TestWorkedExampleFalsePositiveSuppression and
    TestCommentedTemplateSuppression (real-world FP cases that the fix must
    close without leaking new FNs).
    """

    def test_multi_header_single_cell_reports_numbered(self, tmp_path):
        # Close Fix 1: a multi-header cell with a num-less parent and a
        # numbered sub-header reports the code cell with the NUMBERED message,
        # not 'Exercice ?'.
        nb = _write_nb(
            tmp_path / "multi.ipynb",
            [
                _md("## 6. Exercices\n\nIntro.\n\n### Exercice 1 — Volume"),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1
        assert "Exercice 1" in highs[0]["message"]
        assert "Exercice ?" not in highs[0]["message"]

    def test_numless_parent_then_numbered_child_no_duplicate(self, tmp_path):
        # Close Fix 2: a num-less parent cell + a numbered sub-header cell +
        # code cell → exactly ONE HIGH (the numbered attribution), not two.
        nb = _write_nb(
            tmp_path / "numlessdup.ipynb",
            [
                _md("## Exercices\n\nSection intro."),
                _md("### Exercice 1 : a faire"),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1, "num-less parent must not produce a duplicate"
        assert "Exercice 1" in highs[0]["message"]
        assert highs[0]["cell_index"] == 2

    def test_genuinely_numless_closest_still_question(self, tmp_path):
        # Recall guard: a markdown cell whose LAST exercise header is genuinely
        # num-less (no numbered sub-header in the same cell) still flags with
        # 'Exercice ?' — the helper has not over-rotated. The code cell is
        # still HIGH; the message is num-less for the right reason.
        nb = _write_nb(
            tmp_path / "numless.ipynb",
            [
                _md("## Exercices avances\n\nBlock without a numbered sub-header."),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1
        assert "Exercice ?" in highs[0]["message"]

    def test_single_header_unchanged_under_fix1(self, tmp_path):
        # Recall guard: a single `### Exercice N` header is a no-op for Fix 1
        # (only one match exists, so "last" = "first"). HIGH still flags with
        # the correct number.
        nb = _write_nb(
            tmp_path / "single.ipynb",
            [
                _md("### Exercice 5 : a completer"),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1
        assert "Exercice 5" in highs[0]["message"]

    def test_real_leak_still_flagged_under_multi_header(self, tmp_path):
        # Recall guard: Fix 1 makes the message more accurate but never
        # suppresses a real leak. The code cell under a multi-header cell is
        # still HIGH (the whole point of the detector).
        nb = _write_nb(
            tmp_path / "releak.ipynb",
            [
                _md("## 6. Exercices\n\nIntro.\n\n### Exercice 3 : resolv"),
                _code(_SOLUTION_BODY),
            ],
        )
        findings = scan_notebook(str(nb))
        highs = [f for f in findings if f.get("severity") == "HIGH"]
        assert len(highs) == 1
        assert "Exercice 3" in highs[0]["message"]


# ---------------------------------------------------------------------------
# End of new tests
# ---------------------------------------------------------------------------

