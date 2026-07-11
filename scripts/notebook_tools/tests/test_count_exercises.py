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

from count_exercises import (
    _is_stub_code,
    count_exercises_in_notebook,
    iter_pedagogical_notebooks,
)


def _write_nb(path: Path, cells: list[dict]) -> Path:
    """Write a minimal notebook with the given cells to path."""
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
        (tmp_path / "Lab1-Real.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "Lab1-Real_output.ipynb").write_text("{}", encoding="utf-8")
        result = iter_pedagogical_notebooks(tmp_path)
        names = sorted(p.name for p in result)
        assert names == ["Lab1-Real.ipynb"]

    def test_excludes_checkpoint_dir(self, tmp_path):
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "x-checkpoint.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "y.ipynb").write_text("{}", encoding="utf-8")
        result = iter_pedagogical_notebooks(tmp_path)
        assert [p.name for p in result] == ["y.ipynb"]

    def test_excludes_research_archive(self, tmp_path):
        for d in ("research", "archive", "_output"):
            sub = tmp_path / d
            sub.mkdir()
            (sub / "skip.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "keep.ipynb").write_text("{}", encoding="utf-8")
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
