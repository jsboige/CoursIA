"""Tests for scripts/notebook_tools/count_exercises.py

Covers the two #2161 G.1 trap cases that the historical strict
`^#+\\s*Exercice` scan undercounted, plus baseline stub/header detection
and the `_output.ipynb` execution-artifact exclusion.

Pure functions, no I/O on the real repo (uses tmp_path fixtures).
"""

import json
import sys
from pathlib import Path

import pytest

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

import count_exercises
from count_exercises import (
    OUT_OF_CORPUS_KINDS,
    _classify,
    corpus_scope,
    _is_stub_code,
    count_exercises_in_notebook,
    iter_pedagogical_notebooks,
    run,
)


def _write_nb(path: Path, cells: list[dict]) -> Path:
    """Write a minimal notebook with the given cells to path."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _split_source(source: str) -> list[str]:
    """Split a source string into nbformat's list-of-lines form.

    nbformat stores `source` as a list where every element EXCEPT possibly the
    last includes its trailing newline. Splitting on '\\n' and dropping the
    separator breaks multi-line stub detection (`_is_stub_code` joins the list
    and then sees a single mangled line). We preserve the newlines.
    """
    if not source:
        return []
    lines = source.splitlines(keepends=True)
    return lines


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": _split_source(source), "metadata": {}}


def _code(source: str) -> dict:
    return {
        "cell_type": "code",
        "source": _split_source(source),
        "metadata": {},
        "execution_count": None,
        "outputs": [],
    }


# ---------------------------------------------------------------------------
# Header detection
# ---------------------------------------------------------------------------

class TestHeaderDetection:
    def test_plain_exercice_header_counts(self, tmp_path):
        nb = _write_nb(
            tmp_path / "a.ipynb",
            [
                _md("# Titre"),
                _md("### Exercice 1 : un"),
                _code("# TODO\npass"),
                _md("### Exercice 2 : deux"),
                _code("return None"),
                _md("### Exercice 3 : trois"),
                _code("# Indice\nx = None"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3
        assert result.parse_error is None

    def test_numbered_section_header_is_counted(self, tmp_path):
        """Trap case: `## 8. Exercice` (numbered section header).

        The strict `^#+\\s*Exercice` regex requires the word right after the
        hashes with no intervening number/dot/space, so it missed this form.
        Our \\bexercice\\b-anywhere header match must catch it.
        """
        nb = _write_nb(
            tmp_path / "b.ipynb",
            [
                _md("## 8. Exercice : le piege numerote"),
                _code("# TODO etudiant\npass"),
                _md("## 9. Exercice"),
                _code("return None"),
                _md("## 10. Exercice"),
                _code("# TODO\nx = None"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, "Numbered headers (## 8. Exercice) must count"

    def test_dash_separator_header_is_counted(self, tmp_path):
        """Trap case: `### Exercice - Exploration` (dash separator, no number)."""
        nb = _write_nb(
            tmp_path / "c.ipynb",
            [
                _md("### Exercice - Exploration"),
                _code("# TODO\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1

    def test_english_exercise_header_counts(self, tmp_path):
        nb = _write_nb(
            tmp_path / "d.ipynb",
            [_md("### Exercise 1"), _code("pass"), _md("### Exercise 2"), _code("pass")],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 2

    def test_setext_separator_is_not_a_header(self, tmp_path):
        """A `---` horizontal rule must NOT pair as a header over a code cell.

        Regression for the mis-pairing that initially counted a `---` separator
        as a Setext H2 and consumed the exercise code cell below it as its
        paired stub (so the code cell was missed).
        """
        nb = _write_nb(
            tmp_path / "e.ipynb",
            [
                _md("---\n\n## Exercice : apres separateur"),
                _code("# TODO\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        # The `---` is NOT a header; the real header `## Exercice` is cell 0.
        assert result.count == 1
        assert result.exercises[0].cell_index == 0


# ---------------------------------------------------------------------------
# Code-cell-only exercises (the second G.1 trap case)
# ---------------------------------------------------------------------------

class TestCodeCellOnlyExercise:
    def test_code_cell_exercice_without_header_is_counted(self, tmp_path):
        """Trap case: a stub code cell whose comments name an exercise but with
        NO preceding markdown Exercice header. A header-only counter misses it.
        """
        nb = _write_nb(
            tmp_path / "f.ipynb",
            [
                _md("# Titre"),
                _md("### Exercice 1"),
                _code("# Exercice 1 : a faire\n# TODO etudiant\npass"),
                # NO markdown header here -- code-cell-only exercise:
                _code("# Exercice 2 : bonus sans header\n# TODO\nreturn None"),
                _md("### Exercice 3"),
                _code("# Indice\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "Code-cell-only exercise (no markdown header) must count"
        )
        detected_as = {h.detected_by for h in result.exercises}
        assert "markdown_header" in detected_as
        assert "code_cell_comment" in detected_as

    def test_code_cell_exercice_paired_with_header_not_double_counted(
        self, tmp_path
    ):
        """A markdown header immediately followed by its stub code cell is ONE
        exercise, not two.
        """
        nb = _write_nb(
            tmp_path / "g.ipynb",
            [
                _md("### Exercice 1"),
                _code("# Exercice 1 : implementation\n# TODO\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1

    def test_stub_preceding_its_header_same_number_not_double_counted(
        self, tmp_path
    ):
        """The "fill-in box then description" layout: a stub code cell at cell
        i PRECEDES its own descriptive markdown header at cell i+1. Both
        reference the same exercise number, so they are ONE exercise -- not
        two. This is the forward-only-dedup blind-spot documented in #5179
        (genuine case: Oncology-Planning reported 6 exercises for 3 real ones).
        """
        nb = _write_nb(
            tmp_path / "backward.ipynb",
            [
                _code("# Exercice 1 : etendre l'ontologie\n# TODO etudiant\npass"),
                _md("### Exercice 1 : Etendre l'ontologie avec de nouveaux medicaments"),
                _code("# Exercice 2 : sensibilite au prior\n# TODO\nreturn None"),
                _md("### Exercice 2 : Sensibilite du modele bayesien au prior"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 2, (
            "stub-then-header same-number layout must not double-count"
        )
        # The header is the canonical representative; the stub is absorbed.
        assert all(h.detected_by == "markdown_header" for h in result.exercises)

    def test_stub_with_print_exercice_marker_no_comment_is_counted(
        self, tmp_path
    ):
        """Trap case (#6051 Bug 4): a stub code cell whose exercise reference is
        NOT in a ``#``/``//``/``--`` comment -- e.g. a ``print("Exercice ... a
        completer")`` / ``display(...)`` stub marker, or a ``# Partie N`` /
        ``# Etape`` scaffold whose only "exercice" word lives in a print
        statement. The comment-aware ``_code_cell_mentions_exercise`` misses it;
        the broadened full-source scan in pass-2 must catch it (genuine case:
        SC-26-Final-Project Parties 2/3/4, reported 0 for 3 real stubs).
        """
        nb = _write_nb(
            tmp_path / "print_marker.ipynb",
            [
                _md("# Titre"),
                _md("### Partie 1 : Chiffrement"),
                _code(
                    "# Partie 2 : Paillier\n"
                    "# Etape: Implementer le chiffrement\n"
                    "# Indice: voir SC-16\n"
                    'pass  # Etape: Implementez\n'
                    'print("Exercice a completer")'
                ),
                _md("### Partie 3 : ZKP"),
                _code(
                    "# Partie 3 : Preuve\n"
                    "# TODO\n"
                    'display("Exercice 3 a completer")\n'
                    "pass"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 2, (
            "Stub cells whose exercise word is only in a print/display marker "
            "(not a #/// //-- comment) must be counted via the broadened scan"
        )
        assert all(h.detected_by == "code_cell_comment" for h in result.exercises)

    def test_stub_preceding_different_number_header_is_not_absorbed(
        self, tmp_path
    ):
        """SAFETY GUARD (anti under-count): the normal sequential layout is
        ``header N -> stub N -> header N+1``. The stub at cell i belongs to
        exercise N, the header at cell i+1 introduces exercise N+1. The
        backward pairing must NOT absorb the stub here (numbers differ), or
        exercise N would be silently lost. Verified repo-wide: 27 sequential
        notebooks (GameTheory, Sudoku-12, Lean, SW) stay byte-identical.
        """
        nb = _write_nb(
            tmp_path / "sequential.ipynb",
            [
                _md("### Exercice 1 : premier"),
                _code("# Exercice 1 : premiere impl\n# TODO\npass"),
                _md("### Exercice 2 : second"),
                _code("# Exercice 2 : seconde impl\n# TODO\npass"),
                _md("### Exercice 3 : troisieme"),
                _code("# Exercice 3 : troisieme impl\n# TODO\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "sequential layout must count each exercise once (no under-count)"
        )

    def test_stub_preceding_header_with_hint_cell_between_pairs(
        self, tmp_path
    ):
        """Backward pairing skips an intervening non-code (markdown hint) cell
        to find the stub, as long as the number matches. A gap of one markdown
        hint between the stub and its header is still paired.
        """
        nb = _write_nb(
            tmp_path / "gap.ipynb",
            [
                _code("# Exercice 4 : mini-KG\n# Indice\nresult = None"),
                _md("**Indice:** pensez aux cycles."),
                _md("### Exercice 4 : Un mini-KG ou la PCA est trompeuse"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "stub + hint + same-number header is one exercise"
        )

    def test_stub_preceding_numberless_header_left_unpaired(self, tmp_path):
        """A stub with NO number before a header with NO number cannot be
        safely pair-matched (conservative -- we cannot tell whether the stub
        belongs to this header or the previous exercise). It is left
        unpaired: both the stub and the header count, which may leave a
        residual double-count but never under-counts.
        """
        nb = _write_nb(
            tmp_path / "numberless.ipynb",
            [
                _code("# Exercice : free-form\n# TODO\npass"),
                _md("### Exercice : description sans numero"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 2, (
            "numberless stub/header are not absorbed (conservative)"
        )

    def test_csharp_double_slash_comment_exercise_is_counted(self, tmp_path):
        """The .NET / C# family uses ``//`` for line comments (not ``#``).
        A stub code cell whose ``// Exercice ...`` comment names an exercise
        with NO preceding markdown header must be counted -- historically this
        was the canonical-tool blind-spot (agents re-discovered it ad-hoc on
        Probas/Infer and ML.Net).
        """
        nb = _write_nb(
            tmp_path / "cs.ipynb",
            [
                _md("# Titre C#"),
                # C# code-cell-only exercise, no markdown header above:
                _code(
                    "// Exercice : backdoor adjustment\n"
                    "// TODO etudiant : implement SCM\n"
                    "pass"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "C# // Exercice stub (no markdown header) must count"
        )
        assert result.exercises[0].detected_by == "code_cell_comment"

    def test_csharp_scaffolded_exercise_todo_with_code_is_counted(
        self, tmp_path
    ):
        """A scaffolded C# exercise -- ``// Exercice N`` + ``// TODO etudiant``
        ABOVE a partial class skeleton (multiple code lines) -- is a student
        stub, NOT a solution. The ``// TODO`` line-comment marker must classify
        it as a stub even though it has more than one effective code line (the
        ``<= 1 effective code-line`` rule alone misses it).

        Regression for ``Search-11-Metaheuristics-Csharp`` cells 24-26 (ABC /
        inertia-schedule / Schwefel): each ``// Exercice N`` + ``// TODO etudiant``
        + partial skeleton was silently under-counted, so the notebook read as
        1 exercise instead of its real 3.
        """
        nb = _write_nb(
            tmp_path / "scaffold.ipynb",
            [
                _md("# Titre C#"),
                _code(
                    "// Exercice 1 : Artificial Bee Colony (ABC).\n"
                    "// TODO etudiant : implementez ABC (phases employe/onlooker/scout)\n"
                    "public class ABC\n"
                    "{\n"
                    "    public double[] Best;\n"
                    "    public double BestFitness = double.MaxValue;\n"
                    "}\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "Scaffolded C# exercise (// TODO + multi-line skeleton) must count"
        )
        assert result.exercises[0].detected_by == "code_cell_comment"

    def test_csharp_interpolated_console_writeline_exercice_is_counted(
        self, tmp_path
    ):
        """``Console.WriteLine($"Exercice ...")`` (C# interpolated string) is a
        stub marker. The ``$?`` in the pattern accepts the optional interpolation
        sigil -- the quote-only variant missed ``$"Exercice"`` (idiomatic C#).
        """
        nb = _write_nb(
            tmp_path / "interp.ipynb",
            [
                _md("# Titre"),
                _code(
                    "// Exercice 2 : comparer schedules d'inertie.\n"
                    'Console.WriteLine($"Exercice 2 a completer : fitness");\n'
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            'C# interpolated Console.WriteLine($"Exercice ...") must count'
        )

    def test_csharp_display_fn_exercice_is_counted(self, tmp_path):
        """``display("Exercice ...")`` (the .NET Interactive ``display`` helper,
        not ``Console.WriteLine``) is a stub marker. Authors use ``display(...)``
        because ``Console.WriteLine`` is swallowed in headless papermill. A stub
        cell that carries ``display("Exercice ... a completer")`` but neither
        ``// TODO`` nor ``// Indice`` must still be counted.

        Regression for ``GameTheory-5-ZeroSum-Minimax-Csharp`` Ex2, whose stub
        marker ``display("Exercice 2 a completer ...")`` was silently
        under-counted (notebook read as 2 exercises instead of its real 3).
        """
        nb = _write_nb(
            tmp_path / "display.ipynb",
            [
                _md("# Titre C#"),
                _code(
                    "// Exercice 2 : verifier le theoreme minimax.\n"
                    'display("Exercice 2 a completer : matrice 3x3 -> SolveMatrixGame");\n'
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "display(\"Exercice ...\") stub (no // TODO / // Indice) must count"
        )

    def test_inline_csharp_comment_after_code_is_not_a_stub_marker(
        self, tmp_path
    ):
        """An inline trailing ``// Exercice`` after executable code is a
        reference, not a stub marker -- the exercise-word must be on a
        full-line comment to count. (Guards against over-counting.)
        """
        nb = _write_nb(
            tmp_path / "inline.ipynb",
            [
                _md("# Titre"),
                _code(
                    "var x = Compute();  // Exercice reference inline\n"
                    "Console.WriteLine(x);"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 0, (
            "Inline // Exercice after code must NOT count as a stub"
        )

    def test_solution_code_cell_is_not_an_exercise(self, tmp_path):
        """A code cell whose comments mention 'Exercice' but holds a COMPLETE
        solution (not a stub) is an example, not an exercise -- not counted.
        """
        solution = (
            "# Exercice 1 : solution complete\n"
            "def solve(x):\n"
            "    return x * 2\n"
            "print(solve(21))\n"
        )
        nb = _write_nb(
            tmp_path / "h.ipynb",
            [
                _md("# Titre"),
                _code(solution),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 0

    def test_a_completer_line_comment_skeleton_stub_is_counted(self, tmp_path):
        """``# a completer`` LINE-COMMENT stub marker (Bug 5 of #6051). A
        scaffolded cell whose comment says "(a completer)" / "a completer"
        but carries a multi-line skeleton (no ``# TODO``/``pass``/``return
        None``) escaped STUB_PATTERNS and the ``<= 1 effective code-line``
        rule, so it was under-counted. Regression for
        ``Search-11-Metaheuristics`` cell 43 (``# A COMPLETER`` + truncated
        ``problem_profit = Problem(`` skeleton).
        """
        nb = _write_nb(
            tmp_path / "acompleter.ipynb",
            [
                _md("# Titre"),
                _code(
                    "# Exercice 1 : Probleme d'optimisation\n"
                    "def profit_function(solution):\n"
                    "    x, y = solution\n"
                    "    return 50*x + 80*y\n"
                    "\n"
                    "# A COMPLETER\n"
                    "bounds = [(0, 20), (0, 20)]\n"
                    "problem = Problem(bounds=bounds,\n"
                    "                 minmax=\"min\",\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "Cell with '# a completer' line comment + skeleton must count"
        )
        assert result.exercises[0].detected_by == "code_cell_comment"

    def test_a_completer_in_solution_prose_not_counted(self, tmp_path):
        """Bug 5 guard (anti over-count): the comment-anchored ``a completer``
        pattern must NOT count a complete solution whose prose comment merely
        references completion in passing. A real solution with multiple code
        lines and no actual stub scaffold is an example, not an exercise.
        """
        nb = _write_nb(
            tmp_path / "acompleter_sol.ipynb",
            [
                _md("# Titre"),
                _code(
                    "# Exercice 1 : la cellule suivante est a completer\n"
                    "# par l'etudiant -- ici la solution de reference.\n"
                    "def solve(x):\n"
                    "    return x * 2\n"
                    "print(solve(21))\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        # The narrow pattern requires "a completer" as the LEADING comment
        # content, so mid-sentence prose ("la cellule suivante est a
        # completer") does NOT match -- this complete solution is not counted.
        assert result.count == 0, (
            "Mid-sentence 'a completer' prose in a solution must NOT count"
        )


# ---------------------------------------------------------------------------
# Lean (``--`` line comment) detection -- mirrors the C# ``//`` tests above.
# ---------------------------------------------------------------------------

class TestLeanDoubleDashCommentExercise:
    def test_lean_double_dash_comment_exercise_is_counted(self, tmp_path):
        """Lean 4 / Haskell line comments use ``--`` (not ``#`` or ``//``).
        A stub code cell whose ``-- Exercice ...`` comment names an exercise
        with NO preceding markdown header must be counted -- historically the
        canonical tool was blind to the entire Lean family (GameTheory-Lean
        ``-- Exercice N`` stubs), re-discovered ad-hoc notebook by notebook.
        """
        nb = _write_nb(
            tmp_path / "lean.ipynb",
            [
                _md("# Titre Lean"),
                # Lean code-cell-only exercise, no markdown header above:
                _code(
                    "-- Exercice : Shapley value for n = 3\n"
                    "-- TODO etudiant : calculer phi_i\n"
                    "sorry\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "Lean -- Exercice stub (no markdown header) must count"
        )
        assert result.exercises[0].detected_by == "code_cell_comment"

    def test_lean_scaffolded_exercise_todo_with_code_is_counted(
        self, tmp_path
    ):
        """A scaffolded Lean exercise -- ``-- Exercice N`` + ``-- TODO etudiant``
        ABOVE a partial formalisation skeleton (multiple lines, each a ``--``
        comment) -- is a student stub, NOT a solution. The ``-- TODO`` marker
        must classify it as a stub; without the ``--`` comment-stripping the
        ``<= 1 effective code-line`` rule counted every ``--`` comment line as
        code and the cell escaped stub classification.

        Regression for ``SocialChoice/02-Lean-SocialChoice-Formal`` cells
        32-34 (Pareto / Condorcet / median): each ``-- EXERCICE N`` +
        ``-- TODO etudiant`` + formalisation skeleton was silently
        under-counted, so the notebook read as 1 exercise instead of its
        real 4 (markdown header + 3 code stubs).
        """
        nb = _write_nb(
            tmp_path / "lean_scaffold.ipynb",
            [
                _md("# Theorie du choix social"),
                _md("## Exercice 1 : Pareto"),
                _code(
                    "-- Exercice 1 : verifier le respect de Pareto\n"
                    "-- Soit 2 individus et 3 alternatives.\n"
                    "-- TODO etudiant : prouver le resultat\n"
                    "--   etape 1 : appliquer la definition\n"
                    "theorem pareto_respected : True := by trivial\n"
                ),
                _md("## Exercice 2 : Condorcet"),
                _code(
                    "-- Exercice 2 : cycle de Condorcet\n"
                    "-- 3 electeurs, 3 alternatives.\n"
                    "-- TODO etudiant : calculer les marges\n"
                    "theorem condorcet_cycle : True := by trivial\n"
                ),
                _md("## Exercice 3 : electeur median"),
                _code(
                    "-- Exercice 3 : preferences unimodales\n"
                    "-- TODO etudiant : verifier le vainqueur\n"
                    "theorem median_winner : True := by trivial\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "3 scaffolded Lean -- Exercice stubs must each count"
        )

    def test_lean_solution_code_cell_is_not_an_exercise(self, tmp_path):
        """A Lean code cell whose ``-- Exercice`` comment sits ABOVE a COMPLETE
        proof (not a stub) is an example, not an exercise -- not counted,
        mirroring ``test_solution_code_cell_is_not_an_exercise`` for the
        Python form.
        """
        solution = (
            "-- Exercice 1 : preuve complete\n"
            "-- Demonstration du theoreme.\n"
            "theorem foo (n : Nat) : n + 0 = n := by\n"
            "  rw [Nat.add_zero]\n"
        )
        nb = _write_nb(
            tmp_path / "lean_sol.ipynb",
            [
                _md("# Titre Lean"),
                _code(solution),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 0, (
            "Lean -- Exercice above a complete proof is an example, not counted"
        )


# ---------------------------------------------------------------------------
# Stub classification
# ---------------------------------------------------------------------------

class TestStubClassification:
    @pytest.mark.parametrize(
        "source",
        [
            "# TODO etudiant\npass\n",
            "# Indice\nreturn None\n",
            'print("Exercice a completer")\n',
            "result = None  # TODO etudiant\n",
            "# Exercice 1 : a faire\n",
        ],
    )
    def test_recognized_stubs(self, source):
        """These patterns must classify as stubs (work for the student)."""
        assert _is_stub_code(source) is True

    @pytest.mark.parametrize(
        "source",
        [
            "# Exercice 1 : solution complete\n"
            "def solve(x):\n"
            "    return x * 2\n"
            "print(solve(21))\n",
            "import numpy as np\n"
            "x = np.array([1, 2, 3])\n"
            "print(x.mean())\n",
        ],
    )
    def test_solutions_are_not_stubs(self, source):
        """Complete working code is not a stub."""
        assert _is_stub_code(source) is False

    def test_banned_patterns_still_count_as_exercise_cell(self, tmp_path):
        """C.1 says raise NotImplementedError / assert False / 1/0 are banned,
        but if present they are still stubs (work for the student). The tool
        counts the exercise; the lint pass (audit_c1_c3) flags the banned form.
        They are orthogonal concerns.
        """
        nb = _write_nb(
            tmp_path / "ban.ipynb",
            [_md("### Exercice 1"), _code("raise NotImplementedError\n")],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1


# ---------------------------------------------------------------------------
# Evidence fields
# ---------------------------------------------------------------------------

class TestEvidence:
    def test_each_hit_has_cell_index_and_preview(self, tmp_path):
        nb = _write_nb(
            tmp_path / "ev.ipynb",
            [
                _md("### Exercice 1 : premier"),
                _code("pass"),
                _md("### Exercice 2 : second"),
                _code("pass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 2
        for hit in result.exercises:
            assert hit.cell_index >= 0
            assert hit.cell_type in {"markdown", "code"}
            assert isinstance(hit.preview, str)
            assert hit.preview  # non-empty

    def test_malformed_notebook_records_parse_error(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{not valid json", encoding="utf-8")
        result = count_exercises_in_notebook(bad)
        assert result.parse_error is not None
        assert result.count == 0


# ---------------------------------------------------------------------------
# iter_pedagogical_notebooks exclusions
# ---------------------------------------------------------------------------

class TestExclusions:
    def test_excludes_output_artifacts(self, tmp_path):
        """`Name_output.ipynb` execution artifacts are excluded to avoid
        double-counting the lab + its papermill output.
        """
        _write_nb(tmp_path / "Course" / "Lab1-Real.ipynb", [])
        _write_nb(tmp_path / "Course" / "Lab1-Real_output.ipynb", [])
        result = iter_pedagogical_notebooks(tmp_path)
        names = sorted(p.name for p in result)
        assert names == ["Lab1-Real.ipynb"]

    def test_excludes_checkpoint_dir(self, tmp_path):
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "x-checkpoint.ipynb").write_text("{}", encoding="utf-8")
        _write_nb(tmp_path / "Course" / "y.ipynb", [])
        result = iter_pedagogical_notebooks(tmp_path)
        assert [p.name for p in result] == ["y.ipynb"]

    def test_excludes_research_archive(self, tmp_path):
        for d in ("research", "archive", "_output"):
            sub = tmp_path / d
            sub.mkdir()
            (sub / "skip.ipynb").write_text("{}", encoding="utf-8")
        _write_nb(tmp_path / "Course" / "keep.ipynb", [])
        result = iter_pedagogical_notebooks(tmp_path)
        assert [p.name for p in result] == ["keep.ipynb"]

    def test_excludes_quantconnect_trashbin(self, tmp_path):
        """`.QuantConnect/` is the QuantConnect CLI app-data dir; its `TrashBin/`
        holds recycled (deleted) project research.ipynb. Counting these 450+
        trashed notebooks as pedagogical inflated the sub-threshold tally --
        they must be excluded (same artifact-gap class as `_output.ipynb`).
        """
        qc = tmp_path / "ESGF-Workspace" / ".QuantConnect" / "TrashBin"
        qc.mkdir(parents=True)
        # A trashed project's research notebook (the real-world shape).
        (qc / "1777304234858_ESGF-Deleted").mkdir()
        (qc / "1777304234858_ESGF-Deleted" / "research.ipynb").write_text(
            "{}", encoding="utf-8"
        )
        # Sibling: the hidden `.QuantConnect` root itself (config etc.) -- also out.
        (tmp_path / "ESGF-Workspace" / ".QuantConnect" / "config.json").write_text(
            "{}", encoding="utf-8"
        )
        (tmp_path / "ESGF-Workspace" / "ESGF-Real.ipynb").write_text("{}", encoding="utf-8")
        result = iter_pedagogical_notebooks(tmp_path)
        assert [p.name for p in result] == ["ESGF-Real.ipynb"]

    @pytest.mark.parametrize("skip_named_ancestor", [
        "archive",   # the canonical #8858 case (clone under .../archive/CoursIA)
        "research",  # the historical twin case
        "bin",       # a common build-output / checkout-parent name
    ])
    def test_clone_under_skip_named_ancestor_is_not_silenced(
        self, tmp_path, skip_named_ancestor
    ):
        """#8858-class guard: a checkout's ABSOLUTE path is not signal.

        ``corpus_scope`` filters ``root.rglob`` results against ``EXCLUDE_DIRS``.
        The bug: it tested ``nb_path.parts`` -- the ABSOLUTE components -- so a
        clone living under a skip-named ancestor (e.g.
        ``/home/u/archive/CoursIA/MyIA.AI.Notebooks``) matched ``archive`` in
        its absolute path and was excluded wholesale. The corpus emptied, an
        empty corpus counts zero below-threshold notebooks, and ``--check``
        passes trivially -- a false-clean fleet scan with no signal that
        anything was inspected.

        The sibling ``test_excludes_research_archive`` does NOT catch this: it
        makes ``research`` a SUBDIR of the scan root (a real relative
        exclusion), not an ANCESTOR of the scan root (the false absolute one).
        This test anchors the filter at ``relative_to(root)`` -- the same fix
        as ``detect_papermill_path_leak.py``'s ``#8858-class guard``.
        """
        # The scan root lives UNDER a skip-named ancestor (real-world: a
        # second clone, a CI checkout, a worktree under .../archive/...).
        root = tmp_path / skip_named_ancestor / "clone" / "MyIA.AI.Notebooks"
        nb_path = root / "ML" / "Lesson-1.ipynb"
        _write_nb(nb_path, [_md("## Exercice 1"), _code("pass")])

        corpus, removed = corpus_scope(root)
        assert [p.name for p in corpus] == ["Lesson-1.ipynb"], (
            f"clone under .../{skip_named_ancestor}/... was silenced: "
            f"corpus={corpus!r} removed={removed!r}"
        )


# ---------------------------------------------------------------------------
# Threshold / verdict integration
# ---------------------------------------------------------------------------

class TestThresholdIntegration:
    def test_sub_threshold_notebook_flagged(self, tmp_path):
        nb = _write_nb(
            tmp_path / "low.ipynb",
            [_md("### Exercice 1"), _code("pass")],  # only 1
        )
        result = count_exercises_in_notebook(nb)
        assert result.count < 3


# ---------------------------------------------------------------------------
# #6051 -- grouped markdown headers + plural section headers
# ---------------------------------------------------------------------------

class TestGroupedAndPluralHeaders:
    """Regression tests for the two interacting counting bugs in #6051.

    Bug 1 -- a single markdown cell that groups several exercise statements
    under sub-headers (`### Exercice 1`, `### Exercice 2`, `### Exercice 3`)
    was under-counted as 1 (one hit per CELL). It must count one per INSTANCE
    header line.

    Bug 2 -- a PLURAL section header (`## 9. Exercices`) was (a) counted as an
    exercise instance AND (b) forward-pairing the next code cell, so the section
    stood in for the real exercise and masked the count. A plural section must
    count as nothing and steal no code cell.
    """

    def test_grouped_markdown_cell_counts_per_instance(self, tmp_path):
        """Bug 1 repro: one markdown cell with three exercise sub-headers over
        one code cell holding three stubs must count 3, not 1.

        Mirrors ``GameTheory/SocialChoice/04-...-SAT-Z3-Csharp.ipynb``.
        """
        nb = _write_nb(
            tmp_path / "grouped.ipynb",
            [
                _md(
                    "## 8. Exercices\n\n"
                    "### Exercice 1 : premier\n\n**Indice 1** : ...\n\n"
                    "### Exercice 2 : second\n\n**Indice 1** : ...\n\n"
                    "### Exercice 3 : troisieme\n\n**Indice 1** : ..."
                ),
                _code(
                    "// Exercice 1 : a\n// TODO etudiant\n"
                    "// Exercice 2 : b\n// TODO etudiant\n"
                    "// Exercice 3 : c\n// TODO etudiant\n"
                    "display(\"a completer\");"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "a grouped markdown cell with 3 instance headers must count 3"
        )

    def test_plural_section_header_does_not_count_as_instance(self, tmp_path):
        """Bug 2 (counting side): a plural section header `## 9. Exercices`
        alone (no instance in the cell) must NOT be counted as an exercise.
        """
        nb = _write_nb(
            tmp_path / "plural.ipynb",
            [
                _md("## 9. Exercices\n\nLes exercices suivants..."),
                _code("// Exercice 1 : a\n// TODO etudiant\npass"),
                _code("// Exercice 2 : b\n// TODO etudiant\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        # 2 real code stubs; the plural section is NOT a 3rd instance.
        assert result.count == 2, (
            "a plural section header must not inflate the exercise count"
        )

    def test_plural_section_does_not_steal_forward_pairing(self, tmp_path):
        """Bug 2 (pairing side): a plural section header must NOT forward-pair
        the code cell below it. The real Exercice 1 stub must be counted in its
        own right. Mirrors ``GameTheory/GameTheory-5-ZeroSum-Minimax-Csharp.ipynb``
        where the section `## 9. Exercices` stole cell 21 (Exercice 1).
        """
        nb = _write_nb(
            tmp_path / "steal.ipynb",
            [
                _md("## 9. Exercices"),
                _code("// Exercice 1 : Colonel Blotto\n// TODO etudiant\npass"),
                _code("// Exercice 2 : autre\n// TODO etudiant\npass"),
                _code("// Exercice 3 : dernier\n// TODO etudiant\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "plural section must not steal Exercice 1's code cell (no under-count)"
        )
        # All three are detected via their own code-cell comment, none absorbed.
        detected_cells = {h.cell_index for h in result.exercises}
        assert detected_cells == {1, 2, 3}, (
            "the three code stubs must each be counted on their own"
        )

    def test_plural_section_then_grouped_instances(self, tmp_path):
        """Combined case: a plural section header followed (same cell or next)
        by real instance headers. The plural line is ignored; each singular
        instance line counts.
        """
        nb = _write_nb(
            tmp_path / "mix.ipynb",
            [
                _md(
                    "## 9. Exercices\n\n"
                    "### Exercice 1 : un\n\n### Exercice 2 : deux\n\n"
                    "### Exercice 3 : trois"
                ),
                _code("# Exercice 1\n# TODO\npass"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "3 instance lines under a plural section count 3 (section ignored)"
        )

    def test_singular_section_header_still_counts(self, tmp_path):
        """Guard against over-fixing: a SINGULAR numbered section header
        `## 8. Exercice : ...` is an INSTANCE (not a plural section) and must
        still count. This is the trap case preserved by test_numbered_section
        _header_is_counted -- reaffirmed here in the plural-aware regime.
        """
        nb = _write_nb(
            tmp_path / "singular.ipynb",
            [
                _md("## 8. Exercice : le piege"),
                _code("# TODO etudiant\npass"),
                _md("## 9. Exercice : autre"),
                _code("return None"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 2



class TestCorpusScope:
    """Corpus scope and the #2161 exception table (`classify_notebook`).

    The convention has two parts the counter historically collapsed into one
    `count < 3` test: WHICH notebooks are course material, and WHAT minimum
    applies to those that are. Collapsing them reported 168 sub-threshold
    notebooks repo-wide, of which 133 were QuantConnect research artifacts and
    nearly all the rest were rule-exempt setup/Lean/archive notebooks.
    """

    @pytest.mark.parametrize(
        "stem",
        [
            "research",            # QC projects/*/research.ipynb
            "Research",            # CSharp-BTC-MACD-ADX/Research.ipynb (capital)
            "quantbook",           # QC projects/*/quantbook.ipynb
            "output_v2",           # Sector-Momentum-Researcher/output_v2.ipynb
            "research_robustness",
            "m12_har_rv_j_research",
            "sector_momentum_research_v2",
            "CrossSubmissionCaptureRepro",
        ],
    )
    def test_execution_artifacts_are_out_of_corpus(self, tmp_path, stem):
        kind, threshold = _classify(tmp_path / f"{stem}.ipynb", standard_threshold=3, root=tmp_path)
        assert threshold is None, f"{stem} should carry no exercise budget"
        assert kind in OUT_OF_CORPUS_KINDS

    def test_templates_and_internal_notebooks_are_out_of_corpus(self, tmp_path):
        for stem, expect in [
            ("Workbook-Template", "template"),
            ("Notebook-Template", "template"),
            ("_e2e_quant_validation", "tooling"),
        ]:
            kind, threshold = _classify(tmp_path / f"{stem}.ipynb", standard_threshold=3, root=tmp_path)
            assert (kind, threshold) == (expect, None), stem

    def test_underscore_directory_is_out_of_corpus(self, tmp_path):
        for parent in ("_archives", "_probes", "_docs"):
            nb = tmp_path / parent / "Serie-2-Concepts.ipynb"
            kind, threshold = _classify(nb, standard_threshold=3, root=tmp_path)
            assert (kind, threshold) == ("archive", None), parent

    def test_legacy_directory_excluded_but_legacy_filename_kept(self, tmp_path):
        """The precision case that a naive `legacy` match gets wrong.

        `SemanticWeb/RDF.Net-Legacy/RDF.Net.ipynb` sits in a legacy FOLDER and
        is not maintained. `GenAI/Image/04-Applications/04-4-Cross-Stitch-
        Pattern-Maker-Legacy.ipynb` is a maintained lesson in a numbered series
        whose SUBJECT happens to be a legacy pattern-maker -- it carries 4
        exercises. Dropping it would remove a conforming course notebook from
        the denominator, which is the same defect as leaving artifacts in it and
        considerably harder to notice.
        """
        in_legacy_dir = tmp_path / "RDF.Net-Legacy" / "RDF.Net.ipynb"
        assert _classify(in_legacy_dir, standard_threshold=3, root=tmp_path) == ("legacy", None)

        legacy_named = tmp_path / "GenAI-Image" / "04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb"
        kind, threshold = _classify(legacy_named, standard_threshold=3, root=tmp_path)
        assert kind == "standard"
        assert threshold == 3

    def test_setup_and_lean_are_in_corpus_but_exempt(self, tmp_path):
        """Rule table: Setup/Environment `0-1`, purely-Lean `0-2`.

        The column is *Minimum exercices* and both rows include zero, so these
        kinds are never sub-threshold. Encoding 1 and 2 as FLOORS would invent a
        stricter policy than the rule states.
        """
        for stem, expect in [
            ("Lean-1-Setup", "setup"),
            ("Sudoku-0-Environment-Csharp", "setup"),
            ("SC-1-Setup-Foundry", "setup"),
            ("Argument_Analysis_Agentic-0-init_agent", "setup"),
            ("Lean-3-Propositions-Proofs", "lean"),
            ("GameTheory-11b-Lean-BayesianGamesExt", "lean"),
            ("DecInfer-9-Lean-Gittins", "lean"),
        ]:
            kind, threshold = _classify(tmp_path / "Course" / f"{stem}.ipynb", standard_threshold=3, root=tmp_path)
            assert kind == expect, stem
            assert threshold == 0, f"{stem}: rule exempts this kind, floor must be 0"

    def test_environment_directory_scopes_its_notebooks_as_setup(self, tmp_path):
        """`GenAI/00-GenAI-Environment/00-2-Docker-Services-Management.ipynb`
        carries no setup marker in its own stem -- the directory supplies it."""
        nb = tmp_path / "00-GenAI-Environment" / "00-2-Docker-Services-Management.ipynb"
        assert _classify(nb, standard_threshold=3, root=tmp_path) == ("setup", 0)

    def test_ordinary_course_notebook_keeps_the_full_budget(self, tmp_path):
        nb = tmp_path / "Serie" / "SW-4-Ontologies.ipynb"
        assert _classify(nb, standard_threshold=3, root=tmp_path) == ("standard", 3)

    def test_raising_threshold_does_not_raise_exempt_kinds(self, tmp_path):
        """`--threshold 5` must not invent an exercise budget for setup/Lean."""
        assert _classify(tmp_path / "Course" / "Lean-1-Setup.ipynb", standard_threshold=5, root=tmp_path)[1] == 0
        assert _classify(tmp_path / "Course" / "X-Lean-Y.ipynb", standard_threshold=5, root=tmp_path)[1] == 0
        assert _classify(tmp_path / "Course" / "X-Concepts.ipynb", standard_threshold=5, root=tmp_path)[1] == 5

    def test_iter_pedagogical_notebooks_drops_out_of_corpus(self, tmp_path):
        cells = [_md("## Exercice 1"), _code("pass")]
        _write_nb(tmp_path / "Course" / "SW-4-Ontologies.ipynb", cells)
        _write_nb(tmp_path / "research.ipynb", cells)
        _write_nb(tmp_path / "quantbook.ipynb", cells)
        _write_nb(tmp_path / "Workbook-Template.ipynb", cells)
        found = {p.name for p in iter_pedagogical_notebooks(tmp_path)}
        assert found == {"SW-4-Ontologies.ipynb"}

    def test_gate_can_still_fail_positive_control(self, tmp_path):
        """The control that matters for any scope-NARROWING change.

        Restricting what a checker looks at can quietly produce a checker that
        cannot fail at all -- green because it inspects nothing, indistinguish-
        able from green because everything is clean. A standard course notebook
        below the floor must still be reported, and `--check` must still exit 1.
        """
        _write_nb(
            tmp_path / "Course" / "SW-4-Ontologies.ipynb",
            [_md("## Exercice 1 : une seule"), _code("# TODO etudiant\npass")],
        )
        targets = iter_pedagogical_notebooks(tmp_path)
        assert len(targets) == 1
        assert count_exercises_in_notebook(targets[0]).count == 1
        assert run(targets, threshold=3, json_out=False, check=True) == 1
        # ... and conversely stays silent once the notebook conforms.
        assert run(targets, threshold=1, json_out=False, check=True) == 0

    def test_corpus_scope_reports_what_it_removed(self, tmp_path):
        """The denominator must be reported, not merely applied.

        A scope filter that silently drops material leaves the reader unable to
        distinguish a tool that inspected everything from one that narrowed its
        own scope -- which is the defect this change fixes, so the fix must not
        reintroduce it one level up.
        """
        cells = [_md("## Exercice 1"), _code("pass")]
        _write_nb(tmp_path / "Course" / "SW-4-Ontologies.ipynb", cells)
        _write_nb(tmp_path / "research.ipynb", cells)
        _write_nb(tmp_path / "quantbook.ipynb", cells)
        _write_nb(tmp_path / "Workbook-Template.ipynb", cells)
        (tmp_path / "_archives").mkdir()
        _write_nb(tmp_path / "_archives" / "Old-Serie-1.ipynb", cells)

        corpus, removed = corpus_scope(tmp_path)
        assert [p.name for p in corpus] == ["SW-4-Ontologies.ipynb"]
        assert removed == {"artifact": 2, "template": 1, "archive": 1}
        assert sum(removed.values()) + len(corpus) == 5, "every notebook accounted for"

    def test_root_prefix_carries_no_classification_signal(self, tmp_path):
        """A checkout path is not signal.

        `_classify` scans path components for `_`-prefixed and legacy folders.
        Anchoring at the scan root keeps a clone living under e.g.
        `.../_worktrees/` or `.../legacy-box/` from classifying the entire
        repository as archive -- which would empty the corpus, and an empty
        corpus passes `--check` silently.
        """
        hostile = tmp_path / "_worktrees" / "RDF-Legacy-box"
        hostile.mkdir(parents=True)
        nb = _write_nb(hostile / "Course" / "SW-4-Ontologies.ipynb", [_md("## Exercice 1"), _code("pass")])

        assert _classify(nb, standard_threshold=3, root=hostile) == ("standard", 3)
        corpus, removed = corpus_scope(hostile)
        assert corpus == [nb]
        assert removed == {}


# ---------------------------------------------------------------------------
# #8835 -- path-form invariance: relative vs absolute must classify identically
# ---------------------------------------------------------------------------
class TestPathFormInvariance:
    """#8835: ``classify_notebook`` must return the SAME verdict for a file
    whether the path is relative (as ``check_pr_exercises.py --stdin`` receives
    from ``git diff --name-only``) or absolute (as the ``count_exercises.py``
    fleet scan passes it). The bug: the top-of-tree rule gated on
    ``path.is_absolute()`` instead of the normalized ``parts``, so a RELATIVE
    top-of-tree notebook silently skipped the rule and fell through to
    ``standard`` -- the PR gate and the fleet scan then disagreed on the same
    file, and the liar (the PR gate, which poses labels) wrongly flagged the
    notebook ``exercises-below-threshold``. The fix gates on ``len(parts) == 1``
    (form-invariant by construction, like every other directory rule).

    What is fixed is the FORM-INVARIANCE, not one corpus line -- hence the
    parametrization over ``tooling`` / ``setup`` / ``standard`` (acceptance
    criterion 2). The ``tooling`` case is the discriminating one: on the buggy
    code it returned ``standard`` for both forms (the relative form skipped the
    rule, the absolute form failed ``relative_to(NOTEBOOKS_DIR)`` on a tmp file),
    so the ``assert ... == "tooling"`` failed; on the fix it returns
    ``tooling`` for both.
    """

    @pytest.mark.parametrize("rel_inside,expected_kind", [
        ("GradeBook.ipynb", "tooling"),    # top-of-tree (the #8835 case)
        ("ML/00-Setup.ipynb", "setup"),    # setup-stem in a family dir
        ("ML/Lesson.ipynb", "standard"),   # standard in a family dir
    ])
    def test_relative_and_absolute_paths_agree(
        self, tmp_path, monkeypatch, rel_inside, expected_kind
    ):
        # A minimal notebooks tree: one file at the root (top-of-tree), one
        # setup-stem and one standard file inside a family dir.
        root = tmp_path / "nb_root"
        (root / "ML").mkdir(parents=True)
        _write_nb(root / "GradeBook.ipynb", [])
        _write_nb(root / "ML" / "00-Setup.ipynb", [])
        _write_nb(root / "ML" / "Lesson.ipynb", [])
        # chdir so the RELATIVE path resolves under tmp_path (mirrors a worker
        # whose cwd is the repo root passing ``git diff --name-only`` output).
        monkeypatch.chdir(tmp_path)
        # Anchor NOTEBOOKS_DIR at the synthetic root so the OLD top-of-tree
        # rule (which bypassed `parts` and read NOTEBOOKS_DIR directly) treats
        # the absolute path as "under NOTEBOOKS_DIR" -- reproducing the reported
        # divergence (relative -> standard, absolute -> tooling) on buggy code,
        # so the equality assertion below FAILS there. The fixed rule consumes
        # `parts` (= _scope_parts with root=), so it is unaffected by this patch.
        monkeypatch.setattr(count_exercises, "NOTEBOOKS_DIR", root)

        rel = Path("nb_root") / rel_inside
        absolute = (root / rel_inside).resolve()

        verdict_rel = _classify(rel, standard_threshold=3, root=root)
        verdict_abs = _classify(absolute, standard_threshold=3, root=root)

        # The invariant the bug broke: same verdict under either form.
        assert verdict_rel == verdict_abs, (
            f"form divergence for {rel_inside!r}: "
            f"relative={verdict_rel} absolute={verdict_abs}"
        )
        # And the expected kind (top-of-tree -> tooling is the #8835 fix).
        assert verdict_rel[0] == expected_kind, (
            f"{rel_inside!r}: expected {expected_kind!r}, got {verdict_rel[0]!r}"
        )

    def test_top_of_tree_is_tooling_under_both_forms(self, tmp_path, monkeypatch):
        """The exact #8835 reproduction: a top-of-tree notebook classifies as
        ``tooling`` whether passed relative or absolute -- so neither consumer
        (fleet scan nor PR gate) can disagree."""
        root = tmp_path / "nb_root"
        root.mkdir()
        _write_nb(root / "GradeBook.ipynb", [])
        monkeypatch.chdir(tmp_path)
        monkeypatch.setattr(count_exercises, "NOTEBOOKS_DIR", root)
        rel = Path("nb_root/GradeBook.ipynb")
        absolute = (root / "GradeBook.ipynb").resolve()
        assert _classify(rel, standard_threshold=3, root=root) == ("tooling", None)
        assert _classify(absolute, standard_threshold=3, root=root) == ("tooling", None)
