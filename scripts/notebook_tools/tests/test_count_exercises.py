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
        SC-26-Final-Project-Python Parties 2/3/4, reported 0 for 3 real stubs).
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

    def test_numbered_print_marker_computing_skeleton_is_counted(
        self, tmp_path
    ):
        """Numbered C.1 print idiom on a scaffolded skeleton whose body
        computes (the rl_8_model_based_dyna_q Ex2 shape). The skeleton's
        ``# TODO etudiant`` markers sit above scaffolding with a DERIVED
        return (``return list(steps), Q`` -- a call), so the comment-marker
        gate in ``_is_stub_code`` skips them ("leftover comments above a body
        that computes") and the only executable marker left is
        ``print("Exercice 2 a completer")`` -- which the pre-fix pattern
        missed because of the digit. The markdown header above must pair to
        exactly one hit, not double-count.
        """
        nb = _write_nb(
            tmp_path / "numbered_print_skeleton.ipynb",
            [
                _md("# Titre"),
                _md("### Exercice 2 — Prioritized Sweeping"),
                _code(
                    "import heapq\n"
                    "\n"
                    "\n"
                    "def sweep(env, n_episodes=50):\n"
                    '    """Squelette — a completer (exercice 2)."""\n'
                    "    Q = {}\n"
                    "    steps = []\n"
                    "    for _ in range(n_episodes):\n"
                    "        # TODO etudiant — Etape 1 : inserer dans la file\n"
                    "        steps.append(1)\n"
                    "    return list(steps), Q\n"
                    "\n"
                    "\n"
                    "# TODO etudiant — Etape 2 : comparer avec dyna_q\n"
                    'print("Exercice 2 a completer")'
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "A scaffolded skeleton whose only executable marker is the "
            "numbered print idiom must count as one exercise"
        )
        assert result.exercises[0].detected_by == "markdown_header"

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

        Regression for ``Search-11-Metaheuristics-CSharp`` cells 24-26 (ABC /
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

        Regression for ``GameTheory-05-ZeroSum-Minimax-CSharp`` Ex2, whose stub
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

    @pytest.mark.parametrize(
        "source",
        [
            # Issue #14212 -- typed-empty return literals were the only
            # neutral-empty form NOT in STUB_PATTERNS, so a function whose
            # contract is a list/dict/tuple/numeric/set/string returning its
            # typed empty value read as multi-line real code and was
            # under-counted. See auditer-la-conformite-visuelle cells 38/39
            # vs cell 40: structurally identical stubs, three different counts
            # (0/0/1) before the patch.
            "# Exercice 1 : enumerer les primaires avec leur contexte\n"
            "def detecteur_primaire_contexte(html_str):\n"
            "    # Parcourir les balises...\n"
            "    return []\n",
            "# Exercice 2 : rapport agrege\n"
            "def rapport_conformite(html_str, charte):\n"
            "    # Reunir les trois detecteurs...\n"
            "    return {}\n",
            "# Exercice 3 : tuple vide\n"
            "def fn():\n"
            "    return ()\n",
            "# Exercice 4 : zero numerique\n"
            "def fn():\n"
            "    return 0\n",
            "# Exercice 5 : set vide\n"
            "def fn():\n"
            "    return set()\n",
            '# Exercice 6 : chaine vide\n'
            'def fn():\n'
            '    return ""\n',
        ],
    )
    def test_typed_empty_returns_are_stubs(self, source):
        """Typed-empty return literals are stubs (issue #14212).

        A function whose contract is a list/dict/tuple/numeric/set/string and
        that returns the typed empty literal is structurally identical to
        ``return None`` -- a neutral value that keeps the notebook executable
        end-to-end while being an obvious TODO marker. ``\b`` boundaries keep
        the match tight (``return 100`` or ``return False`` are NOT matched).
        """
        assert _is_stub_code(source) is True

    @pytest.mark.parametrize(
        "source",
        [
            # Counter-examples (negative control). These return REAL values,
            # not empty literals, so they must NOT be classified as stubs.
            "def fn():\n    return 100\n",
            "def fn():\n    return False\n",
            "def fn():\n    return [1, 2, 3]\n",
            'def fn():\n    return {"a": 1}\n',
            "def fn():\n    return (1,)\n",
            "def fn():\n    return set([1])\n",
            'def fn():\n    return "hello"\n',
        ],
    )
    def test_non_empty_returns_are_not_stubs(self, source):
        """Real return values are NOT stubs (control for #14212)."""
        assert _is_stub_code(source) is False

    def test_three_typed_stubs_render_three_exercises_issue_14212(self, tmp_path):
        """Reproduce the auditer-la-conformite-visuelle scenario.

        Before the fix, three structurally identical stubs (return [],
        return {}, return None) rendered 1/3 in count_exercises_in_notebook.
        After the fix, they must render 3/3. The notebook has no
        ``## Exercice N`` headers -- these are detected via the code-cell
        comment + stub pairing.
        """
        nb = _write_nb(
            tmp_path / "sub" / "audit.ipynb",
            [
                _md("# Audit conformite visuelle\n"),
                _code(
                    "# Exercice 1 : enumerer les primaires.\n"
                    "def detecteur_primaire_contexte(html_str):\n"
                    "    return []\n"
                ),
                _code(
                    "# Exercice 2 : rapport agrege.\n"
                    "def rapport_conformite(html_str, charte):\n"
                    "    return {}\n"
                ),
                _code(
                    "# Exercice 3 : le piege du smoke vert.\n"
                    "def piege_smoke_vert(page):\n"
                    "    return None\n"
                ),
            ],
        )
        cnt = count_exercises_in_notebook(nb)
        assert cnt.count == 3, f"expected 3 exercises, got {cnt.count}"

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

    def test_empty_return_stub_forms_are_recognized(self):
        """Empty-typed returns (`return []`, `return {}`, `return ()`,
        `return 0`, `return set()`, `return ""`) are the pedagogically-correct
        stub for a function that promises a list/dict/tuple/num/str/set, but
        ONLY `return None` was in STUB_PATTERNS (issue #14212). A COMPACT cell
        whose last effective statement is one of these is a stub.
        """
        compact_stubs = [
            "def f():\n    # completer\n    return []\n",
            "def f():\n    return {}\n",
            "def f():\n    return ()\n",
            "def f():\n    return 0\n",
            "def f():\n    return set()\n",
            'def f():\n    return ""\n',
            "def f():\n    return ''\n",
        ]
        for src in compact_stubs:
            assert _is_stub_code(src) is True, src

    def test_empty_return_inside_worked_example_is_not_a_stub(self):
        """A `return []` / `return 0` buried in a multi-line WORKED example is a
        real computed answer (an empty neighbor list, an MST base case, a
        `return float('inf')` sentinel), NOT a stub marker. It must not be
        counted. Without this guard a substring `\\breturn\\s+\\[\\]` over the
        whole source over-counted Search-3-Informed (cells 4/65 were already
        complete frameworks/demos).
        """
        worked_examples = [
            # A fully-written search framework class, `return []` is one line.
            "class Node:\n"
            "    def __init__(self, state, path_cost=0, h=0):\n"
            "        self.state = state\n"
            "        self.path_cost = path_cost\n"
            "        self.h = h\n"
            "    def children(self):\n"
            "        return []\n"
            "    def path_cost_plus_h(self):\n"
            "        return self.path_cost + self.h\n"
            "    def inf(self):\n"
            "        return float('inf')\n"
            "print('Framework de recherche informee pret.')\n",
            # An MST heuristic with a legitimate numeric base case.
            "def mst_cost_prim(nodes, graph):\n"
            "    if len(nodes) <= 1:\n"
            "        return 0\n"
            "    nodes = list(nodes)\n"
            "    cost = 0\n"
            "    return cost\n",
        ]
        for src in worked_examples:
            assert _is_stub_code(src) is False, src

    def test_positive_control_three_exercise_cells_count_as_three(self, tmp_path):
        """Acceptance criterion (#14212): a notebook with three exercise stub
        cells (markdown Exercice header + `return []` / `return {}` /
        `return None`) counts 3, not 1. Mirrors the real
        auditer-la-conformite-visuelle.ipynb cells 38/39/40.
        """
        nb = _write_nb(
            tmp_path / "auditer.ipynb",
            [
                _md("### Exercice 1 : Enumerer les primaires avec leur contexte\n"),
                _code(
                    "def detecteur_primaire_contexte(html_str):\n"
                    "    # Parcourir les balises, ...\n"
                    "    return []\n"
                ),
                _md("### Exercice 2 : Rapport agrege.\n"),
                _code(
                    "def rapport_conformite(html_str, charte):\n"
                    "    # Reunir les trois detecteurs...\n"
                    "    return {}\n"
                ),
                _md("### Exercice 3 : Le piege du smoke vert.\n"),
                _code(
                    "def piege_smoke_vert(page):\n"
                    "    # On suppose deja que...\n"
                    "    return None\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3


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
        own right. Mirrors ``GameTheory/GameTheory-05-ZeroSum-Minimax-CSharp.ipynb``
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
            ("Lean-01-Setup-Lean-Python", "setup"),
            ("Sudoku-00-Environment-CSharp", "setup"),
            ("SC-01-Setup-Foundry-Python", "setup"),
            ("Argument_Analysis_Agentic-0-init_agent", "setup"),
            ("Lean-03-Propositions-Proofs-Lean", "lean"),
            ("GameTheory-11b-Lean-BayesianGamesExt-Lean", "lean"),
            ("DecInfer-09-Lean-Gittins", "lean"),
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
        assert _classify(tmp_path / "Course" / "Lean-01-Setup-Lean-Python.ipynb", standard_threshold=5, root=tmp_path)[1] == 0
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

    def test_research_dirs_are_out_of_corpus(self, tmp_path):
        """NON_PEDAGOGICAL_DIRS hold R&D deliverables, not taught series, so
        their notebooks carry no exercise budget. Locks the
        ML-Training-Pipeline / Research-Executor exclusions (FallacyDetection
        descended into GenAI/ as tranche 1 of #13581, so its notebooks are now
        in-corpus and exercised against the standard threshold)."""
        cells = [_md("## Exercice 1"), _code("pass")]
        for d in ("ML-Training-Pipeline", "Research-Executor"):
            _write_nb(tmp_path / d / "some_research.ipynb", cells)
        for d in ("ML-Training-Pipeline", "Research-Executor"):
            nb = tmp_path / d / "some_research.ipynb"
            kind, threshold = _classify(nb, standard_threshold=3, root=tmp_path)
            assert threshold is None, f"{d} should carry no exercise budget"
            assert kind in OUT_OF_CORPUS_KINDS, f"{d} should be out of corpus"
        # iter_pedagogical_notebooks skips the whole excluded directory
        assert {p.name for p in iter_pedagogical_notebooks(tmp_path)} == set()

    def test_genai_fallacydetection_is_in_corpus(self, tmp_path):
        """Tranche 1 of #13581 moved FallacyDetection under GenAI/. Its
        notebooks now carry the standard pedagogical budget (not out-of-corpus)
        and must be exercised against the standard threshold."""
        cells = [_md("## Exercice 1"), _code("pass"), _md("## Exercice 2"), _code("pass"), _md("## Exercice 3"), _code("pass")]
        _write_nb(tmp_path / "GenAI" / "FallacyDetection" / "01-taxonomy-intro.ipynb", cells)
        nb = tmp_path / "GenAI" / "FallacyDetection" / "01-taxonomy-intro.ipynb"
        kind, threshold = _classify(nb, standard_threshold=3, root=tmp_path)
        assert kind not in OUT_OF_CORPUS_KINDS, "GenAI/FallacyDetection is now in-corpus (post-#13581 tranche 1)"
        assert threshold == 3, "GenAI/FallacyDetection carries the standard pedagogical threshold"


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

    def test_family_dir_scanned_as_root_is_not_emptied(self, tmp_path, monkeypatch):
        """#2161 false-negative: scanning a FAMILY directory as the scan root
        silently emptied the corpus.

        The top-of-tree ``tooling`` rule (catching ``GradeBook.ipynb`` directly
        under ``NOTEBOOKS_DIR``) was gated on ``len(_scope_parts(path, root)) == 1``.
        ``_scope_parts`` relativizes to the scan ``root``, so when a family dir
        was the scan target, EVERY notebook in it sat at relative-depth-1 and
        was false-classified ``tooling`` -- the whole family dropped out of the
        corpus, ``--check`` saw nothing, and returned a trivially-green exit 0.
        Observed on ``Sudoku/``, ``IIT/``, ``ML/`` scanned alone. The fix anchors
        the top-of-tree check on ``NOTEBOOKS_DIR`` specifically (not the scan
        root), mirroring how the other directory rules already key off ``parts``.
        """
        root = tmp_path / "nb_root"
        family = root / "Sudoku"
        family.mkdir(parents=True)
        _write_nb(family / "Sudoku-01-Backtracking-CSharp.ipynb", [])
        _write_nb(family / "Sudoku-00-Environment-CSharp.ipynb", [])
        _write_nb(root / "GradeBook.ipynb", [])  # the only TRUE top-of-tree file
        monkeypatch.setattr(count_exercises, "NOTEBOOKS_DIR", root)

        # Scanning the FAMILY dir as root must still see its notebooks -- they
        # are NOT top-of-tree (GradeBook is). On buggy code both returned
        # ("tooling", None) and corpus_scope(family) yielded an empty list.
        assert _classify(
            family / "Sudoku-01-Backtracking-CSharp.ipynb",
            standard_threshold=3, root=family,
        ) == ("standard", 3)
        assert _classify(
            family / "Sudoku-00-Environment-CSharp.ipynb",
            standard_threshold=3, root=family,
        ) == ("setup", 0)
        corpus, removed = corpus_scope(family)
        assert len(corpus) == 2, (
            f"family scanned as root was emptied (corpus={len(corpus)}, "
            f"removed={removed}) -- the #2161 false-negative"
        )

        # The genuine top-of-tree file is still tooling (regression guard on
        # the fix itself -- anchoring on NOTEBOOKS_DIR must not over-correct).
        assert _classify(
            root / "GradeBook.ipynb", standard_threshold=3, root=root,
        ) == ("tooling", None)


# ---------------------------------------------------------------------------
# #15080 D01 -- a complete solution carrying a leftover `# TODO etudiant` is NOT
# an open exercise; a header with no following code cell is a declared subject
# with no write-space (distinguishable from "no exercise at all").
# ---------------------------------------------------------------------------

class TestD01CompletedSolutionWithTodo:
    def test_complete_solution_with_todo_comment_is_not_a_stub(self, tmp_path):
        """R05 c30/c32/c34 each render a full implementation below a surviving
        `# TODO etudiant` comment (issue #15080 D01, acceptance 2). The counter
        must NOT read them as open exercises -- this is the inversion the finding
        names. Validated by its false negative: none of the three is counted.
        """
        c30 = (
            "def mur_latence_exo(dims=64, sizes=(10**4, 10**5), seed=0):\n"
            "    # TODO etudiant : completer la mesure -- reutiliser exact_knn, renvoyer [(n, ms)].\n"
            "    rows = []\n"
            "    rng = np.random.default_rng(seed)\n"
            "    for n in sizes:\n"
            "        db = rng.random((n, dims), dtype=np.float32)\n"
            "        q = rng.random(dims).astype(np.float32)\n"
            "        t0 = time.perf_counter()\n"
            "        for _ in range(3):\n"
            "            exact_knn(db, q)\n"
            "        rows.append((n, (time.perf_counter() - t0) / 3 * 1000))\n"
            "    return rows\n"
            "\n"
            'result = mur_latence_exo(dims=128)\n'
            'print("Exercice 1 : latence dims=128 :", [(n, round(ms, 1)) for n, ms in result])\n'
        )
        # The header precedes the complete solution: it is a SOLVED example
        # (corrige), not an orphan -- so count 0 AND unpaired 0.
        nb = _write_nb(
            tmp_path / "r05_solution.ipynb",
            [
                _md("## Exercice 1 : latence vs dimension"),
                _code(c30),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 0, (
            "A complete solution with a leftover '# TODO etudiant' must not count "
            "as an open exercise (got %d)" % result.count
        )
        assert result.unpaired_markdown_instances == 0, (
            "A header followed by a complete solution is a solved example, not an "
            "orphaned subject"
        )

    def test_todo_with_passthrough_or_skeleton_remains_a_stub(self):
        """The override must NOT swallow genuine stubs: a `# TODO` above a
        passthrough return or a multi-line scaffold with no computed result stays
        a stub (guard on the existing scaffolded C#/Lean tests)."""
        passthrough = "def solve(grid):\n    # TODO etudiant : completer\n    return grid\n"
        assert _is_stub_code(passthrough) is True, (
            "A passthrough return (unchanged parameter) is a placeholder stub"
        )
        skeleton = (
            "// Exercice 1 : Artificial Bee Colony (ABC).\n"
            "// TODO etudiant : implementez ABC\n"
            "public class ABC\n"
            "{\n"
            "    public double[] Best;\n"
            "    public double BestFitness = double.MaxValue;\n"
            "}\n"
        )
        assert _is_stub_code(skeleton) is True, (
            "A scaffolded C# skeleton with // TODO is a student stub"
        )

    @pytest.mark.parametrize(
        "source",
        [
            # Issue #15676 -- STUB_PATTERNS previously required ``result =
            # None`` literally; ``resultat = None``, ``response_json = None``,
            # ``data = None`` (any identifier) escaped the matcher, and
            # ``return <name>`` of such a placeholder counted as a derived
            # return by `_body_computes_result` (the variable IS assigned in
            # the body). Now generalized to ``^\s*<name>\s*=\s*None\b`` for
            # any identifier, so a 6-cell stub with these shapes is
            # recognized as a stub without further reduction.
            # AEV 13b_Agent_Evaluation cell 18 -- ``resultat = None`` form:
            "# Exercice 1 : verificateur deterministe.\n"
            "# TODO etudiant : complete verificateur\n"
            "def verificateur(code, probleme):\n"
            "    # Indice : passes == total.\n"
            "    resultat = None  # TODO etudiant\n"
            "    return resultat\n",
            # Claudish cell 14 -- ``response_json = None``:
            "# Exercice 1 : appel brut.\n"
            "def call_claudish_raw(prompt: str, model: str = \"glm-5.2\"):\n"
            "    response_json = None  # TODO etudiant\n"
            "    return response_json\n",
            # Generic data binding -- another common idiome:
            "# Exercice 1 : charger le dataset.\n"
            "def charger(path: str):\n"
            "    data = None\n"
            "    return data\n",
        ],
    )
    def test_generic_none_variable_is_stub_issue_15676(self, source):
        """Issue #15676: ``<name> = None`` (any identifier) is a stub.

        Was previously limited to ``result = None`` literally; under that
        shape, AEV (``resultat = None``), Claudish (``response_json = None``)
        and any ``data = None`` / ``reponse = None`` placeholder escaped
        detection, falsely reading as a derived-body solution. The pattern is
        now identifier-agnostic.
        """
        assert _is_stub_code(source) is True, source

    @pytest.mark.parametrize(
        "source",
        [
            # Issue #15676 -- sentinel-return shapes whose value SPELLS the
            # placeholder (``a determiner``, ``a trancher``, ``a completer``,
            # ``unknown``, etc.). A worked ``return "unknown"`` IS possible
            # in some classifiers, but the whitelist here is short and the
            # cost of an exercise slightly under-counted is much smaller
            # than the cost of falsely counting a worked classifier. See
            # ``00-Parcours-QA-OWUI.ipynb`` cells 13 (`classer` returning
            # ``"a determiner"``) and 15 (`verdict` returning
            # ``"a trancher"``).
            '# Exercice 1 : determiner la categorie.\n'
            'def classer(status, retries=0, reason=""):\n'
            '    # TODO etudiant : completer\n'
            '    return "a determiner"\n',
            '# Exercice 2 : verdict go/no-go.\n'
            "def verdict(echecs_reels, skips, total):\n"
            "    # TODO etudiant : completer\n"
            '    return "a trancher"\n',
            '# Exercice 3 : resultat inconnu.\n'
            "def get_unknown():\n"
            "    return \"unknown\"\n",
        ],
    )
    def test_sentinel_string_return_is_stub_issue_15676(self, source):
        """Issue #15676: ``return "<whitelisted-sentinel>"`` is a stub.

        The string ITSELF spells the placeholder (``a determiner`` /
        ``a trancher`` / ``unknown`` / ``a completer`` / ``a definir`` /
        ``TODO``); no line-tail comment is required. A REAL classifier
        returning ``"unknown"`` would over-flag -- an accepted trade-off in
        favour of not under-counting textbook placeholder cells: the
        whitelist is deliberately unconditional, so no counter-test is
        possible against it by design, not for lack of one (wording
        reconciled in #15688; the earlier "no counter-test can pass today"
        implied one was pending).
        """
        assert _is_stub_code(source) is True, source

    def test_sentinel_numeric_return_with_placeholder_comment_is_stub_issue_15676(
        self,
    ):
        """Issue #15676: ``return -1  # ... a completer / placeholder / neutre``.

        OWUI cell 11 (``tests_du_module`` returning ``return -1  # valeur
        \"a completer\" (placeholder neutre)``) was under-counted because
        ``return -1`` is not part of the empty-typed literals and the
        line-tail comment vocabulary matches the new sentinelle comment.
        """
        source = (
            "# Exercice 1 : compter les tests d'un module.\n"
            "def tests_du_module(code):\n"
            "    # TODO etudiant : completer\n"
            '    return -1  # valeur "a completer" (placeholder neutre)\n'
        )
        assert _is_stub_code(source) is True, source

    def test_issue_15676_three_notebooks_count_3_3(self, tmp_path):
        """Reproduce the audit H02 GenAI scenario at #15676.

        Three notebooks whose three idiomes (variable form / sentinelle
        string / sentinelle numeric + comment) used to render 0/3 each now
        render 3/3.
        """
        # Notebook 1: ``resultat = None`` variable form (AEV analog).
        nb1 = _write_nb(
            tmp_path / "aev_like.ipynb",
            [
                _md("# Audit GenAI 13b\n"),
                _code(
                    "# Exercice 1 : verifier.\n"
                    "def verificateur(code, probleme):\n"
                    "    # Indice : passes == total.\n"
                    "    resultat = None  # TODO etudiant\n"
                    "    return resultat\n"
                ),
                _code(
                    "# Exercice 2 : ablater.\n"
                    "def ablater(outils, nom):\n"
                    "    resultat = None  # TODO etudiant\n"
                    "    return resultat\n"
                ),
                _code(
                    "# Exercice 3 : renversement.\n"
                    "def renversement(v_ab, v_ba):\n"
                    "    resultat = None  # TODO etudiant\n"
                    "    return resultat\n"
                ),
            ],
        )
        # Notebook 2: sentinelle string return (OWUI analog).
        nb2 = _write_nb(
            tmp_path / "owui_like.ipynb",
            [
                _md("# Parcours QA-OWUI\n"),
                _md("## Exercice 1 — Compter les tests d'un module\n"),
                _code(
                    "def tests_du_module(code):\n"
                    "    # TODO etudiant\n"
                    '    return -1  # valeur "a completer" (placeholder neutre)\n'
                ),
                _md("## Exercice 2 — Qualifier un resultat de test\n"),
                _code(
                    "def classer(status, retries=0, reason=\"\"):\n"
                    "    # TODO etudiant\n"
                    '    return "a determiner"\n'
                ),
                _md("## Exercice 3 — Trancher : go / no-go\n"),
                _code(
                    "def verdict(echecs_reels, skips, total):\n"
                    "    # TODO etudiant\n"
                    '    return "a trancher"\n'
                ),
            ],
        )
        # Notebook 3: ``response_json = None`` form (Claudish analog) +
        # sentinelle string + numeric. Three distinct idiomes in one NB
        # to cover the union.
        nb3 = _write_nb(
            tmp_path / "claudish_like.ipynb",
            [
                _md("# 01-claude-code-via-claudish\n"),
                _md("## 6. Exercice 1 : appel direct\n"),
                _code(
                    "def call_claudish_raw(prompt: str, model: str = \"glm-5.2\"):\n"
                    "    response_json = None  # TODO etudiant\n"
                    "    return response_json\n"
                ),
                _md("## 7. Exercice 2 : comparer 3 tiers\n"),
                _code(
                    "def compare_tiers(question: str, max_tokens: int = 128):\n"
                    "    resultat = None  # TODO etudiant\n"
                    "    return resultat\n"
                ),
                _md("## 8. Exercice 3 : classifier HTTP\n"),
                _code(
                    "def classify_http_error(status_code: int) -> str:\n"
                    "    # TODO etudiant\n"
                    '    return "a determiner"\n'
                ),
            ],
        )
        for nb in (nb1, nb2, nb3):
            cnt = count_exercises_in_notebook(nb)
            assert cnt.count == 3, (
                f"{nb.name}: expected 3 exercises, got {cnt.count}"
            )


class TestGenericNoneAssignGate15713:
    """#15713 (follow-up #15688, Hermes demand 1): the generic ``<name> = None``
    marker is retained only for the placeholder-passthrough shape -- the
    None-assigned name flows UNCHANGED to a bare ``return <name>`` and is
    never reassigned a computed value."""

    @pytest.mark.parametrize(
        "source",
        [
            # Kokoro-01-5 cell 38 (distilled, Hermes demand 2a): the 109-line
            # Inflect-Nano demo INITIALIZES ``inflect_samples = None`` then
            # overwrites it inside a computing pipeline; no bare
            # ``return inflect_samples`` exists.
            "inflect_loaded = False\n"
            "inflect_samples = None\n"
            "inflect_sample_rate = 24000\n"
            "try:\n"
            "    snap_dir = snapshot_download(repo_id='owensong/Inflect-Nano-v1')\n"
            "    inflect_samples = vmodel(mel).squeeze().detach().cpu().numpy()\n"
            "    inflect_samples = np.clip(inflect_samples, -1.0, 1.0)\n"
            "    print('INFLECT-NANO ok', len(inflect_samples))\n"
            "except Exception as exc:\n"
            "    print('modele non disponible :', exc)\n",
            # AI-Engine-WordPress crossed-delete cell (distilled): the None
            # init is overwritten with a computed tuple under an ``if``;
            # 'exercice' appears only inside a print.
            "croise = None\n"
            "if ADMIN_MDP:\n"
            "    ok = login_wordpress(session_autre, 'consent.admin', ADMIN_MDP)\n"
            "    statut_c, rep_c = api_files(session_autre, nonce, 'delete')\n"
            "    croise = (statut_c, rep_c)\n"
            "    print('delete croise :', statut_c)\n"
            "else:\n"
            "    print('(absent : test croise non execute -- voir exercice 2)')\n",
            # Guard-variable idiome in a working cell: ``best = None`` is a
            # loop sentinel, OVERWRITTEN by the computing loop below -- a
            # solution, not a placeholder.
            "best = None\n"
            "for score in scores:\n"
            "    if best is None or score > best:\n"
            "        best = score\n"
            "print('meilleur :', best)\n",
        ],
    )
    def test_demo_none_initialization_is_not_stub_issue_15713(self, source):
        assert _is_stub_code(source) is False, source

    def test_none_assign_reassigned_then_returned_is_not_stub_issue_15713(self):
        """A function whose None default is OVERWRITTEN with a computed value
        before ``return`` is a real solution, not a placeholder."""
        source = (
            "def synthese(donnees):\n"
            "    resultat = None\n"
            "    if donnees:\n"
            "        resultat = sum(donnees) / len(donnees)\n"
            "    return resultat\n"
        )
        assert _is_stub_code(source) is False, source

    def test_passthrough_none_assign_stays_stub_issue_15713(self):
        """The gate must not swallow the #15676 idioms it exists to protect:
        AEV/Claudish ``<name> = None`` + bare ``return <name>`` passthrough."""
        source = (
            "def verificateur(code, probleme):\n"
            "    # Indice : passes == total.\n"
            "    resultat = None  # TODO etudiant\n"
            "    return resultat\n"
        )
        assert _is_stub_code(source) is True, source

    @pytest.mark.parametrize(
        "source",
        [
            # Search-03-Informed c4 -- a complete ``class Node`` whose only
            # ``= None`` hit is a CONTINUED SIGNATURE DEFAULT. STUB_PATTERNS
            # [10] is multiline-anchored and ``\s`` folds the newline, so the
            # bare pattern fired on the parameter line (#15688, measured at
            # PR head).
            'class Node:\n'
            '    def __init__(\n'
            '        self,\n'
            '        grille=None,\n'
            '        explored_order=None,\n'
            '        heuristic_name=""):\n'
            '        self.grille = grille\n'
            '        self.explored = explored_order\n'
            '        self.h = heuristic_name\n',
            # App-26 c23 -- keyword default ``candidate_order=None`` on the
            # second line of the ``def`` (second measured false positive of
            # the same class, found by the #15688 corpus A/B).
            "def greedy_cover(domains, strength, row_allowed=lambda _row: True,\n"
            "                 candidate_order=None):\n"
            "    suite = couvrir(domains, strength, row_allowed)\n"
            "    return suite\n",
        ],
    )
    def test_none_signature_default_is_not_stub_issue_15688(self, source):
        """#15688: a ``= None`` INSIDE an open bracket is an argument default
        (or a keyword argument in a call), not a hole left for the student --
        the cell executes as-is."""
        assert _is_stub_code(source) is False, source

    def test_dead_none_in_complete_generator_is_not_stub_issue_15688(self):
        """GameTheory-16b c3 (#15688, measured at PR head): ``best_M = None``
        never reassigned, never returned, no other marker, in a complete
        generator whose return is a computed tuple -- a dead initializer,
        not an exercise. Note ``\\bbest_M\\b`` does not match inside
        ``best_M_partial`` (the underscore is a word character)."""
        source = (
            "def generer_mecanisme(n):\n"
            "    best_M = None\n"
            "    best_M_partial = []\n"
            "    for i in range(n):\n"
            "        best_M_partial.append(construire(i))\n"
            "    payment_table = tabuler(best_M_partial)\n"
            "    best_J = max(j for j in range(n))\n"
            "    return (best_M_partial[0], payment_table), best_J\n"
        )
        assert _is_stub_code(source) is False, source

    def test_mixed_cell_todo_none_placeholder_stays_stub_issue_15688(self):
        """12-TTS c29 / research_l1_tsmom c18 / App-22 c17 (#15688 A/B): a
        COMPLETE sibling function in the same cell makes the cell-level
        ``_body_computes_result`` True, but the ``result = None  # TODO
        etudiant`` placeholder is a real exercise -- the composed
        ``<name> = None`` gate must not consult the cell-level
        body-computes signal (measured: gating on it un-counted three real
        exercises)."""
        source = (
            "def similarite(a, b):\n"
            "    mots_a = set(a.split())\n"
            "    mots_b = set(b.split())\n"
            "    return len(mots_a & mots_b) / max(1, len(mots_a | mots_b))\n"
            "\n"
            "\n"
            "def selectionner(codes):\n"
            "    codes_selectionnes = [c for c in codes if garde(c)]\n"
            "    seuil = calcule(codes_selectionnes)\n"
            "    result = None  # TODO etudiant\n"
            "    return codes_selectionnes, seuil\n"
        )
        assert _is_stub_code(source) is True, source

    def test_header_does_not_pair_to_none_init_demo_issue_15713(self, tmp_path):
        """Kokoro-01-5 layout (Hermes demand 2b): the ``Exercice 3`` header is
        followed FIRST by the Inflect-Nano demo cell, which merely initializes
        ``inflect_samples = None``. The demo must not steal the pairing: the
        header finds no stub in its window and is dropped, and the real
        Exercice 3 stub (after the demo, outside the window) is counted by the
        code-cell pass -- the notebook keeps exactly its 3 exercises, not 4."""
        nb = _write_nb(
            tmp_path / "kokoro_like.ipynb",
            [
                _md("# Kokoro TTS local\n"),
                _md("## Exercice 1 : premier rendu\n"),
                _code(
                    "# Exercice 1 : premier rendu\n"
                    "rendu = None  # TODO etudiant\n"
                    "return rendu\n"
                ),
                _md("## Exercice 2 : voix multiples\n"),
                _code(
                    "# Exercice 2 : voix multiples\n"
                    "comparaison = None  # TODO etudiant\n"
                    "return comparaison\n"
                ),
                _md("## Exercice 3 : dialogue multi-voix\n"),
                _code(
                    "# Demonstration Inflect-Nano-v1 : TTS ultra-leger\n"
                    "print('INFLECT-NANO-V1 - TTS ULTRA-LEGER')\n"
                    "inflect_loaded = False\n"
                    "inflect_samples = None\n"
                    "try:\n"
                    "    inflect_samples = vmodel(mel).numpy()\n"
                    "    inflect_samples = np.clip(inflect_samples, -1.0, 1.0)\n"
                    "except Exception as exc:\n"
                    "    print('modele absent :', exc)\n"
                ),
                _md("Duree estimee : 15-20 minutes. Objectif : alterner les voix.\n"),
                _code(
                    "# Exercice 3 : dialogue multi-voix\n"
                    "dialogue = None  # TODO etudiant\n"
                    "return dialogue\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            f"expected 3 exercises (the demo must not steal the Exercice 3 "
            f"pairing), got {result.count}"
        )


class TestD01UnpairedHeaders:
    def test_headers_with_no_code_cell_are_declared_instances(self, tmp_path):
        """CSK (01-GitHub-Copilot-SDK-Binding) holds three exercise headings whose
        `csharp` blocks live INSIDE markdown -- no code cell exists to write in.
        The counter must report them as declared-but-empty, distinct from a
        notebook with genuinely no exercise (R05b demo), which renders 0 with no
        declared instances (#15080 D01, acceptance 3).
        """
        nb = _write_nb(
            tmp_path / "csk_detached.ipynb",
            [
                _md("# Titre CSK"),
                _md("## Exercice 1 : utiliser le binding\n```csharp\n// sk\n```"),
                _md("## Exercice 2 : ...\n```csharp\n// ...\n```"),
                _md("## Exercice 3 : ...\n```csharp\n// ...\n```"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 0
        assert result.unpaired_markdown_instances == 3, (
            "Three exercise headings with no code cell below them are declared "
            "subjects with no write-space (got %d)" % result.unpaired_markdown_instances
        )

    def test_no_exercise_notebook_has_zero_declared_instances(self, tmp_path):
        """R05b (05b-Stockage-Vectoriel-Serveur) has no exercise word at all --
        a demonstration of method. It must render 0 count AND 0 declared
        instances, so it is distinguishable from the CSK detached-headings case.
        """
        nb = _write_nb(
            tmp_path / "demo.ipynb",
            [
                _md("# Demo de methode"),
                _md("## Methode"),
                _code("x = 1\nprint(x)"),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 0
        assert result.unpaired_markdown_instances == 0


# ---------------------------------------------------------------------------
# #18146 -- scaffolded stubs swallowed by the "_body_computes_result" gate,
# bold (non-ATX) exercise titles, and pairing refinements. Each fixture
# reproduces the measured shape of a cited notebook cell.
# ---------------------------------------------------------------------------

class TestScaffoldedStubShapes:
    """Mechanism 1: the leftover-TODO gate must not swallow scaffolded stubs."""

    def test_docstring_stub_with_scaffold_return_is_stub(self):
        """GameTheory-07 c29: a long docstring + `# TODO etudiant` Etapes +
        one scaffolding constructor + `return game`. The docstring prose used
        to carry the cell over the three-effective-line threshold and the
        single-assignment `return game` read as derived."""
        src = (
            'def build_three_player_entry_game():\n'
            '    """Construit l\'arbre de jeu a 3 firmes sequentielles.\n'
            "\n"
            "    Structure :\n"
            "      - Firme A (joueur 1, racine) decide Entree ou Reste_dehors\n"
            "      - Firme B (joueur 2) observe A et decide Entree ou Reste_dehors\n"
            "      - Firme C (joueur 3) observe A et B et decide Entree ou Reste_dehors\n"
            '    """\n'
            "    # TODO etudiant : implementer l'arbre complet\n"
            "    # Etape 1 : creer le jeu avec num_players=3\n"
            "    # Etape 2 : creer les 8 noeuds terminaux\n"
            '    game = ExtensiveFormGame("3-Player Entry Game", num_players=3)\n'
            "    return game\n"
        )
        assert _is_stub_code(src) is True, (
            "A scaffolded stub (docstring + TODO + one constructor + return) "
            "must stay a stub"
        )

    def test_template_dict_return_is_stub(self):
        """GameTheory-07 c27/c31: `return {` over placeholder values (0, [],
        False, a TODO string) under a `# TODO etudiant : remplacer` marker."""
        src = (
            "def solve_ultimatum(offers=None, total=10):\n"
            "    # TODO etudiant : completer le solveur\n"
            "    return {\n"
            "        'spe_offer': 0,\n"
            "        'j1_payoff': 0,\n"
            "        'j2_payoff': 0,\n"
            "        'j2_accepts': [],\n"
            "    }  # TODO etudiant : remplacer par le vrai calcul SPE\n"
        )
        assert _is_stub_code(src) is True, (
            "A returned dict whose every value is a placeholder is a template"
        )

    def test_dict_return_with_computed_value_stays_a_solution(self):
        """Negative control on the template rule: a dict that carries at
        least one computed value is a real answer, leftover TODO or not."""
        src = (
            "def solve(grid):\n"
            "    # TODO etudiant (residuel de la correction)\n"
            "    best = max(candidates, key=score)\n"
            "    return {\n"
            "        'best': best,\n"
            "        'score': score(best),\n"
            "    }\n"
        )
        assert _is_stub_code(src) is False

    def test_csharp_return_zero_with_tail_todo_is_stub(self):
        """GameTheory-13 c22: `return 0.0;   // TODO etudiant` -- the C#
        line-tail comment slashes used to satisfy the binary-operator regex
        and mark the return as derived."""
        src = (
            "// Exercice 1 : Leduc Poker (2 tours, 6 cartes).\n"
            "// TODO etudiant : modeliser Leduc + lancer CFR.\n"
            "static double SolveLeduc()\n"
            "{\n"
            "    // Indice : nouvelle classe Leduc avec IsTerminal/GetPayoff.\n"
            "    return 0.0;   // TODO etudiant\n"
            "}\n"
            "\n"
            '"Exercice a completer".Display();\n'
        )
        assert _is_stub_code(src) is True

    def test_csharp_return_null_with_tail_todo_is_stub(self):
        """Z3-01 c15: `return null;  // TODO etudiant : remplacer par ...` --
        C# null + tail comment, both formerly read as a computed return."""
        src = (
            "// EXERCICE 1 : Trouver un triplet pythagoricien avec Z3.\n"
            "// Etape 1 : declarer les variables a, b, c\n"
            "(long A, long B, long C)? TrouverTripletPythagoricien(int borneMax = 20)\n"
            "{\n"
            "    // TODO etudiant : implementez la resolution avec un Solver Z3\n"
            "    return null;  // TODO etudiant : remplacer par le triplet trouve\n"
            "}\n"
            "\n"
            "var triplet = TrouverTripletPythagoricien(20);\n"
            'Console.WriteLine("Triplet : " + (triplet.HasValue ? triplet.ToString() : "(a completer)"));\n'
        )
        assert _is_stub_code(src) is True


class TestBoldTitlesAndPairing:
    """Mechanism 2: bold (non-ATX) exercise statements + pairing refinements."""

    def test_bold_statement_after_stub_counts(self, tmp_path):
        """PT_13 cells 40-45: stub i, bold `**Exercice N -- ...**` statement
        at i+1. Bold titles are not ATX headers, so the notebook used to
        render count=0 while carrying three exercises."""
        cells = []
        for n, sujet in ((1, "std"), (2, "token"), (3, "eps")):
            cells.append(_code(
                f"# TODO etudiant : mesurer {sujet} sur les 5 seeds.\n"
                "pass  # (a completer - C.1)\n"
            ))
            cells.append(_md(
                f"**Exercice {n} - Reintroduire {sujet} dans Dr. GRPO.** Reprendre\n"
                'make_cfg("dr"), re-poser le parametre et comparer la dispersion.\n'
            ))
        nb = _write_nb(tmp_path / "pt13_bold.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "A bold `**Exercice N ...**` statement following its stub must "
            "count (got %d)" % result.count
        )

    def test_bold_prose_leadin_is_not_a_second_instance(self, tmp_path):
        """1.2-Manipulation_de_Donnees_avec_NumPy c27: the ATX header
        `### Exercice 1 : ...` followed by the prose lead-in
        `**Pourquoi cet exercice est fondamental** : ...`. The bold opener is
        a sentence, not a title -- without the starts-with-word guard the
        cell's instances doubled (corpus: 6->12)."""
        cells = [
            _md(
                "### Exercice 1 : vectorisez une boucle\n"
                "\n"
                "**Pourquoi cet exercice est fondamental** : la vectorisation est *la*\n"
                "difference entre un script Python et un script NumPy.\n"
            ),
            _code("valeurs = [1, 2, 3]\n# TODO etudiant : vectoriser\ncarres = None  # TODO\n"),
        ]
        nb = _write_nb(tmp_path / "numpy_bold_prose.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "A prose bold opener must not double the instance count (got %d)"
            % result.count
        )

    def test_correction_header_does_not_steal_next_stub(self, tmp_path):
        """rl_1c cells 45-56: after each exercise's stub comes the worked
        correction `### Exemple guide : correction de l'exercice N`, then the
        next exercise's header. The correction title used to forward-pair the
        NEXT exercise's stub and double the count (8 for 4 exercises)."""
        cells = []
        for n in (1, 2):
            cells.append(_md(f"### Exercice {n} : DAgger avec le teacher T\n"))
            cells.append(_code(f"# TODO etudiant : exercice {n}\nresultat = None\n"))
            cells.append(_md(f"### Exemple guide : correction de l'exercice {n}\n"))
            cells.append(_code(
                f"# correction de l'exercice {n} -- solution complete\n"
                f"moyenne = sum(resultats) / len(resultats)\n"
                f"print('exercice {n} corrige :', moyenne)\n"
            ))
        nb = _write_nb(tmp_path / "rl1c_corrections.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        assert result.count == 2, (
            "A correction title must not steal the next exercise's stub (got %d)"
            % result.count
        )

    def test_lean_stub_with_number_pairs_own_header(self, tmp_path):
        """Lean-29 cells 5-8: an undescribing worked-example code cell, then
        `### Exercice 1`, then the Lean stub `-- Exercice 1 : ...`. The
        greedy backward absorb used to pair the header with the EXAMPLE,
        leaving the stub double-counted by pass 2 (12 for 6)."""
        cells = [
            _code(
                "-- Les briques : la matrice triangulaire et ses valeurs.\n"
                "-- TODO etudiant (exemple guide residuel)\n"
                "theorem briques : True := by trivial\n"
            ),
            _md("### Lecture : valeurs et determinants\n"),
            _md("### Exercice 1 - lire la valeur d'un representant\n"),
            _code(
                "-- Exercice 1 : la valeur explicite du representant.\n"
                "-- TODO etudiant : a completer (indice dans la cellule precedente).\n"
                "example : True := by trivial\n"
            ),
        ]
        nb = _write_nb(tmp_path / "lean29_number_pair.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        assert result.count == 1, (
            "A stub that names its exercise number pairs its own header, not "
            "a preceding example cell (got %d)" % result.count
        )

    def test_plural_toc_section_restatement_not_double_counted(self, tmp_path):
        """PT_10 cells 19-24: a `## 10. Exercices` section cell whose bold
        `**Exercice A/B/C**` sub-mentions restate the subjects of the three
        individual `## Exercice X : ...` cells below. Both used to push and
        the notebook rendered 6 for three exercises."""
        cells = [
            _md(
                "## 10. Exercices (3 stubs C.1 - pas d'erreur volontaire)\n"
                "\n"
                "**Exercice A** : ajouter un 4e estimateur GAE-AVG.\n"
                "\n"
                "**Exercice B** : mesurer l'effet du sweep lambda.\n"
                "\n"
                "**Exercice C** : variance inter-seed des avantages.\n"
            ),
        ]
        for lettre, sujet in (("A", "GAE-AVG"), ("B", "sweep lambda"), ("C", "variance")):
            cells.append(_md(f"## Exercice {lettre} : {sujet} (stub C.1)\n"))
            cells.append(_code(f"# TODO etudiant : exercice {lettre}\nresultat = None\n"))
        nb = _write_nb(tmp_path / "pt10_toc.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "A plural-first TOC section must not double-count the exercises "
            "it restates (got %d)" % result.count
        )

    def test_numberless_conservative_survives_blocked_window(self, tmp_path):
        """Video 03-2 cells 16-24: two adjacent numberless exercise
        statements, stubs far below the pairing window. The numberless
        conservative count (stub outside the window) must survive a nearer
        header cell cutting the forward scan."""
        cells = [
            _md("## Exercice : Pipeline Personnalise\n\n**Duree :** 40 minutes\n"),
            _md("## Exercice Avance : Optimisation Batch\n"),
            _md("### Criteres de succes - Optimisation Batch\n"),
            _code("# benchmark realise sur 3 configurations\n"
                  "timings = {'seq': 1.2, 'par': 0.4}\n"
                  "print(timings)\n"),
            _code("# TODO: Implementer un pipeline batch optimise\nresultat = None\n"),
            _md("## Exercice : Gestion d'Erreurs et Recovery\n"),
            _code("# TODO: Implementer le systeme de checkpointing\nresultat = None\n"),
        ]
        nb = _write_nb(tmp_path / "video032_numberless.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "Numberless statements with stubs outside the window keep the "
            "conservative count (got %d)" % result.count
        )


# ---------------------------------------------------------------------------
# Accented print marker + pure-import guard (#18741 PR A)
# ---------------------------------------------------------------------------

class TestAccentedPrintMarkerAndImportGuard:
    """Two false-negative causes measured on 2026-10-05 (diagnostic on #18741):

    - the print stub pattern required the UNACCENTED spelling ``a completer``
      while the comment/sentinel patterns accept ``a compl[eé]ter`` / ``à
      compléter`` -- PT_09 (3 real skeleton cells marked by accented prints)
      rendered 1/3;
    - a PURE import cell read as a stub (its imports are stripped from the
      effective-line count, so ``0 <= 1``), and the backward header pairing
      (#18146) absorbed it in place of the real stub below the header --
      PT_11c counted Exercice 1 twice and Exercices 2/3 zero times (2/3).
    """

    @pytest.mark.parametrize(
        "marker",
        [
            'print("Exercice 2 a completer : ...")',
            'print("Exercice 2 a compléter : ...")',
            'print("Exercice 2 à completer : ...")',
            'print("Exercice 2 à compléter : ...")',
        ],
    )
    def test_accented_print_marker_flags_multi_line_skeleton(self, marker):
        # Two effective code lines: the line-count rule cannot rescue the cell,
        # so ONLY the print pattern decides -- the exact PT_09 shape.
        source = marker + "\ntrajectoire = collecte_rollout(env, policy)\n"
        assert _is_stub_code(source) is True, (
            "the print stub marker must accept the accented francophone forms"
        )

    def test_accented_print_notebook_counts_three(self, tmp_path):
        """PT_09 layout: three numbered headers, each followed by a 2-line
        skeleton whose only stub marker is an accented print. Unfixed, all
        three headers pair with nothing and a numbered header with no stub is
        silently dropped -> 0."""
        nb = _write_nb(
            tmp_path / "accented_prints.ipynb",
            [
                _md("# Titre"),
                _md("### Exercice 1 : boucle de rollout"),
                _code(
                    'print("Exercice 1 à compléter : la boucle de rollout")\n'
                    "trajectoire = collecte_rollout(env, policy)\n"
                ),
                _md("### Exercice 2 : calcul des avantages"),
                _code(
                    'print("Exercice 2 à compléter : les avantages GAE")\n'
                    "avantages = calcule_avantages(rewards)\n"
                ),
                _md("### Exercice 3 : mise a jour"),
                _code(
                    'print("Exercice 3 à compléter : la mise a jour")\n'
                    "nouvelle_politique = maj_politique(politique)\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "accented print markers must pair their headers (got %d)"
            % result.count
        )

    def test_pure_import_cell_is_not_a_stub(self):
        assert _is_stub_code("import re\nfrom typing import Optional") is False
        assert _is_stub_code("import numpy as np") is False
        assert _is_stub_code("using System;\nusing System.Linq;") is False

    def test_import_plus_code_is_untouched_by_the_guard(self):
        # The guard only covers cells whose effective lines are ALL imports: a
        # 1-code-line import cell keeps the historical `<= 1` verdict.
        assert _is_stub_code("import numpy as np\nresultat = None") is True

    def test_header_does_not_absorb_preceding_import_block(self, tmp_path):
        """PT_11c layout (measured on the real notebook): an import block sits
        directly above the Exercice 1 header, its real stub uses a plain TODO
        marker, and the Exercices 2/3 stubs use ACCENTED print markers with a
        prose cell between each stub and the next header.

        Unfixed: header 1 absorbs the import block (backward undescribing),
        its real stub counts standalone, and headers 2/3 pair nothing -> 2.
        Accent fix alone: headers 2/3 pair their stubs but the import
        absorption keeps the double-count -> 4 (the measured over-count).
        Both fixes: each header pairs its own stub -> 3."""
        nb = _write_nb(
            tmp_path / "import_guard.ipynb",
            [
                _md("# Titre"),
                _code("import re\nfrom typing import Optional"),
                _md("### Exercice 1 : classement"),
                _code("# TODO etudiant : classifier\nverdict = None"),
                _md("On evalue maintenant la recompense."),
                _md("### Exercice 2 : recompense"),
                _code(
                    'print("Exercice 2 à compléter : la fonction de recompense")\n'
                    "recompense = calcule_recompense(trajectoire)\n"
                ),
                _md("Enfin, la penalite."),
                _md("### Exercice 3 : penalite"),
                _code(
                    'print("Exercice 3 à compléter : la penalite")\n'
                    "penalite = calcule_penalite(ecarts)\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "an import block is not a stub: headers must pair their own "
            "stubs (got %d)" % result.count
        )


# ---------------------------------------------------------------------------
# Placeholder body vs computing body (#18741 PR B -- cause 3)
# ---------------------------------------------------------------------------

class TestBodyPlaceholderVsComputing:
    """Three under-count shapes + one over-count shape, measured cell by cell
    on 2026-10-05 (#18741 diagnostic): a cell carries EXPLICIT stub markers
    (# TODO / # Indice) but ``_body_computes_result`` reads its placeholder
    body as a computation, gating the markers away; and PT_11c c7 -- the
    converse -- a complete worked verifier whose fallback ``pass`` /
    ``return None`` fire the unconditional executable markers.
    """

    def test_string_return_with_placeholder_tail_is_a_stub(self):
        """OWUI 05 c17: ``return "api"  # placeholder - a affiner`` -- the
        returned string self-declares as provisional in its line-tail
        comment. The string-literal branch read any returned string as a
        solved value, the # TODO marker was gated away -> under-count."""
        source = (
            "def approche_du_scenario(scenario: str) -> str:\n"
            '    # TODO : renvoyer "api" ou "navigateur" selon le scenario.\n'
            "    # Indice : donnees/comparer -> api ; rendu/visuel -> navigateur.\n"
            '    return "api"  # placeholder — a affiner\n'
            "\n"
            'for s in ["Verifier l isolation des tenants",\n'
            '          "Verifier le rendu d un bloc de code"]:\n'
            '    print(f"  {approche_du_scenario(s):12} : {s}")\n'
        )
        assert _is_stub_code(source) is True

    def test_bare_name_return_of_empty_container_is_a_stub(self):
        """Video 02-6 c16: ``trouvees = []`` ... ``return trouvees`` -- the
        bare-name branch counted the EMPTY-list assignment as a computed
        value, so the # Indice / # TODO etudiant markers were gated away."""
        source = (
            "def detecte_restriction_territoriale(texte_licence: str) -> list:\n"
            '    entites_connues = [\n'
            '        "European Union", "United Kingdom", "France",\n'
            '    ]\n'
            "    trouvees = []\n"
            "    # Indice : chercher l'amorce, puis scanner les N caracteres suivants.\n"
            "    # TODO etudiant\n"
            "    return trouvees\n"
        )
        assert _is_stub_code(source) is True

    def test_none_dict_with_provided_checker_is_a_stub(self):
        """Texte 09b c30: the student part is a dict of None (``reponses``);
        the cell also carries the instructor's ``verifier_classification``
        helper whose derived ``return ok`` testified for the whole cell, and
        the TODO markers were gated away."""
        source = (
            "# Exercice 2 : classifier les attaques (stub etudiant)\n"
            "# TODO etudiant : remplir le dictionnaire\n"
            "\n"
            "reponses = {\n"
            '    "P1": None,  # TODO etudiant : "directe" / "indirecte" / "jailbreak"\n'
            '    "P2": None,  # TODO etudiant\n'
            '    "P3": None,  # TODO etudiant\n'
            "}\n"
            "\n"
            "def verifier_classification(reponses):\n"
            '    ok = (reponses.get("P1") == "directe"\n'
            '          and reponses.get("P2") == "indirecte"\n'
            '          and reponses.get("P3") == "jailbreak")\n'
            '    print("Classification correcte :", ok)\n'
            "    return ok\n"
            "verifier_classification(reponses)\n"
        )
        assert _is_stub_code(source) is True

    def test_computing_body_with_fallback_markers_is_not_a_stub(self):
        """PT_11c c7 (the converse direction): a COMPLETE worked verifier
        whose fallback ``pass`` / ``return None`` fired the unconditional
        executable markers. The header absorbed it and the real stub below
        counted standalone -> over-count (PT_11c 4/3)."""
        source = (
            "import re\n"
            "from typing import Optional\n"
            "\n"
            "def extract_answer_sympy(completion: str) -> Optional[float]:\n"
            '    """Extrait la derniere valeur numerique d\'une completion."""\n'
            r'    boxed = re.findall(r"\boxed\{([^}]+)\}", completion)' + "\n"
            "    if boxed:\n"
            "        try:\n"
            "            return float(boxed[-1])\n"
            "        except ValueError:\n"
            "            pass\n"
            "    return None\n"
            "\n"
            'tests = [("2+2 ?", 4.0), ("5*3 ?", 15.0)]\n'
            "for completion, gt in tests:\n"
            "    r = extract_answer_sympy(completion)\n"
            '    print(f"  reward({completion!r} vs {gt}) = {r}")\n'
        )
        assert _is_stub_code(source) is False

    def test_canonical_return_none_stub_stays_a_stub(self):
        # The executable-marker gate must not touch the canonical C.1 shape:
        # no derived return anywhere, the body never computes.
        assert _is_stub_code("def extraire(texte):\n    # TODO etudiant\n    return None") is True
        assert _is_stub_code("class Analyseur:\n    def mesure(self, x):\n        pass") is True

    def test_annotated_pass_keeps_stub_verdict_on_computing_body(self):
        """Wan 02-3 c28 (measured): a computing function whose ``pass`` names
        the write-hole (``# Exercice: ...`` directly above) keeps its stub
        verdict -- the gate targets INCIDENTAL fallbacks, not annotated
        write-holes."""
        source = (
            "def test_camera_movements(base_scene, movements):\n"
            '    templates = {"pan": f"a pan across {base_scene}"}\n'
            "    results = {}\n"
            "    for movement in movements:\n"
            "        prompt = templates.get(movement, base_scene)\n"
            "        # Exercice: Generer avec le mouvement\n"
            "        pass\n"
            "        results[movement] = {\"prompt\": prompt}\n"
            "    return results\n"
        )
        assert _is_stub_code(source) is True

    def test_unannotated_fallback_return_none_stays_gated(self):
        """Sudoku-17 c28 (measured, trimmed): a worked CoT solver class whose
        ``parse_assignment`` ends in a ``return None`` fallback. No student
        vocabulary sits beside the fallback -- gated even though it is a
        pattern-2 match."""
        source = (
            "# Exemple resolu : Solveur LLM avec Chain-of-Thought\n"
            "class ChainOfThoughtSudokuSolver:\n"
            "    def build_prompt(self, partial):\n"
            '        prompt = "You are an expert at solving sudoku.\\n"\n'
            "        for i in range(len(partial)):\n"
            "            for j in range(len(partial[0])):\n"
            '                prompt += f"({i},{j}) = {partial[i][j]}\\n"\n'
            "        return prompt\n"
            "\n"
            "    def parse_assignment(self, llm_response):\n"
            '        cleaned = llm_response.replace(" ", "")\n'
            "        match = re.findall(r'([0-8],[0-8]=[1-9])', cleaned)\n"
            "        if match:\n"
            "            puzzle_str = match[-1]\n"
            "            return (int(puzzle_str[1]), int(puzzle_str[3]))\n"
            "        return None\n"
        )
        assert _is_stub_code(source) is False

    def test_scalar_placeholder_with_student_tail_is_a_stub(self):
        """differencier-les-assistants c27 (measured): the student write-space
        is a scalar placeholder assignment (``= ""  # A vous : ...``); the
        computing helper that shares the cell is the instructor's."""
        source = (
            'ASSISTANT_A_REECRIRE = ""   # A vous : le nom, tel qu\'il figure dans PERSONAS.\n'
            "\n"
            "\n"
            "def remesurer(nom_assistant, nouveau_prompt):\n"
            "    if nom_assistant not in PERSONAS or not nouveau_prompt.strip():\n"
            "        return None\n"
            "    nouvelles = dict(reponses)\n"
            "    return sum(1 for _ in nouvelles) / len(nouvelles)\n"
            "\n"
            "resultat = remesurer(ASSISTANT_A_REECRIRE, \"\")\n"
        )
        assert _is_stub_code(source) is True

    def test_scalar_placeholder_without_student_tail_is_not_a_stub(self):
        """The vocabulary tail is the discriminator: a bare initializer or a
        seeded container of a computing body (D01 c30) must not read as a
        hole."""
        source = (
            "def mur(dims):\n"
            "    rows = []  # accumulateur des mesures\n"
            "    for n in dims:\n"
            "        rows.append(n)\n"
            "    return rows\n"
        )
        assert _is_stub_code(source) is False

    def test_pt11c_mini_notebook_counts_three(self, tmp_path):
        """End-to-end on the PT_11c geometry: import block above the Exercice
        1 header, worked verifier falsely read as stub, real stubs below each
        header. Expected: exactly 3 (was 4 with PR A alone)."""
        nb = _write_nb(
            tmp_path / "pt11c_mini.ipynb",
            [
                _md("# Titre"),
                _code(
                    "import re\n"
                    "from typing import Optional\n"
                    "\n"
                    "def extract_answer_sympy(completion: str) -> Optional[float]:\n"
                    r'    boxed = re.findall(r"\d+", completion)' + "\n"
                    "    if boxed:\n"
                    "        return float(boxed[-1])\n"
                    "    return None\n"
                ),
                _md("### Exercice 1 : etendre le parser"),
                _code(
                    "def extract_answer_sci(completion: str) -> Optional[float]:\n"
                    '    """TODO etudiant : notation scientifique."""\n'
                    "    sci_pattern = None  # TODO etudiant : regex\n"
                    "    return None  # TODO etudiant : retourner le nombre\n"
                    '    print("Exercice à compléter : notation scientifique")\n'
                ),
                _md("On evalue maintenant la recompense."),
                _md("### Exercice 2 : recompense"),
                _code(
                    'print("Exercice 2 à compléter : la fonction de recompense")\n'
                    "recompense = calcule_recompense(trajectoire)\n"
                ),
                _md("Enfin, la penalite."),
                _md("### Exercice 3 : penalite"),
                _code(
                    'print("Exercice 3 à compléter : la penalite")\n'
                    "penalite = calcule_penalite(ecarts)\n"
                ),
            ],
        )
        result = count_exercises_in_notebook(nb)
        assert result.count == 3, (
            "the worked verifier must stop reading as a stub so header 1 "
            "pairs its real stub (got %d)" % result.count
        )
