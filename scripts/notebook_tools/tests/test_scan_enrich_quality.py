"""Tests for scripts/notebook_tools/scan_enrich_quality.py.

Lock in the calibration of the enrich-wave defect scanner (CoursIA #13410,
roo-extensions #3374): every check reproduces a defect class documented in
the 2026-09-01 NanoClaw aggregate, and the legitimate patterns it must NOT
flag (accent gains, code-index anchors, scaffolding fences, quoted outputs,
tails of longer sums) stay silent.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_enrich_quality import (  # noqa: E402
    scan_anchors,
    scan_arithmetic,
    scan_diacritics,
    scan_href,
    scan_numbers,
    scan_phantom,
    scan_solution_leak,
    scan_survival,
)
import enrich_quality_ci  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source: str, outputs: list[dict] | None = None) -> dict:
    return {"cell_type": "code", "source": [source], "execution_count": 1,
            "outputs": outputs or []}


def _out_text(text: str) -> dict:
    return {"output_type": "stream", "name": "stdout", "text": [text]}


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _cats(findings: list[dict]) -> set[str]:
    return {f["category"] for f in findings}


# ---------------------------------------------------------------------------
# Class (f): anchors
# ---------------------------------------------------------------------------

class TestAnchors:
    def test_oor_anchor_fires_high(self):
        # 2 code cells; code[5] cannot exist in any space.
        cells = [_md("# Titre"), _code("1+1"), _md("Interpretation code[5]")]
        assert _cats(scan_anchors(cells)) == {"ANCHOR_OOR"}
        assert scan_anchors(cells)[0]["severity"] == "HIGH"

    def test_absolute_landing_on_markdown_fires_med(self):
        # code[4] is in code-index range (5 code cells) but resolves far from
        # this markdown AND absolute cell 4 is an inserted markdown cell --
        # the #14161 signature.
        cells = [_md("# Titre"), _code("a"), _md("interp de code[4]"),
                 _md("inseree"), _md("inseree"), _code("b"), _code("c"),
                 _code("d"), _code("e")]
        f = scan_anchors(cells)
        assert "ANCHOR_ABS_MD" in _cats(f)
        assert all(x["severity"] == "MED" for x in f if x["category"] == "ANCHOR_ABS_MD")

    def test_correct_code_index_anchor_is_silent(self):
        # code[0] = the code cell right before this markdown: healthy under
        # the imposed convention, even though absolute cell 0 is the title.
        cells = [_md("# Titre"), _code("a"), _md("interp de code[0]")]
        assert scan_anchors(cells) == []


# ---------------------------------------------------------------------------
# Class (c): diacritics
# ---------------------------------------------------------------------------

class TestDiacritics:
    def test_massive_loss_fires_high(self):
        base = [_md("La théorie de l'apprentissage pédagogique était mesurée. " * 4)]
        head = [_md("La theorie de l'apprentissage pedagogique etait mesuree. " * 4)]
        f = scan_diacritics(head, base)
        assert _cats(f) == {"DIACRITICS_LOSS"} and f[0]["severity"] == "HIGH"

    def test_gain_is_silent(self):
        base = [_md("theorie mesuree")]
        head = [_md("théorie mesurée élégamment")]
        assert scan_diacritics(head, base) == []

    def test_small_base_is_silent(self):
        base = [_md("théorie")]
        head = [_md("theorie")]
        assert scan_diacritics(head, base) == []


# ---------------------------------------------------------------------------
# Class (b): survival
# ---------------------------------------------------------------------------

class TestSurvival:
    def test_rewrite_fires_high(self):
        line = "Cette ligne originale substantielle doit survivre."
        base = [_md("\n".join([line] * 10))]
        head = [_md("Texte entierement reecrit sans rapport avec l'original. " * 5)]
        f = scan_survival(head, base)
        assert _cats(f) == {"MD_REWRITE"} and f[0]["severity"] == "HIGH"

    def test_extension_is_silent(self):
        line = "Cette ligne originale substantielle doit survivre."
        base = [_md("\n".join([line] * 6))]
        head = [_md("\n".join([line] * 6 + ["Nouvelle interpretation ajoutee par l'enrichissement."]))]
        assert scan_survival(head, base) == []


# ---------------------------------------------------------------------------
# Class (e): hrefs
# ---------------------------------------------------------------------------

class TestHrefs:
    def test_broken_relative_href_fires(self, tmp_path):
        (tmp_path / "Series").mkdir()
        nb = tmp_path / "Series" / "nb.ipynb"
        cells = [_md("Voir [l'annexe](../Other/target.ipynb) pour la suite.")]
        f = scan_href(nb, cells, tmp_path)
        assert _cats(f) == {"HREF_MISSING"} and f[0]["severity"] == "HIGH"

    def test_existing_relative_href_is_silent(self, tmp_path):
        (tmp_path / "Series").mkdir()
        (tmp_path / "Other").mkdir()
        (tmp_path / "Other" / "target.ipynb").write_text("{}", encoding="utf-8")
        nb = tmp_path / "Series" / "nb.ipynb"
        cells = [_md("Voir [l'annexe](../Other/target.ipynb) pour la suite.")]
        assert scan_href(nb, cells, tmp_path) == []

    def test_http_and_anchor_links_skipped(self, tmp_path):
        (tmp_path / "Series").mkdir()
        nb = tmp_path / "Series" / "nb.ipynb"
        cells = [_md("[site](https://example.com/x.ipynb) et [section](#ancre)")]
        assert scan_href(nb, cells, tmp_path) == []


# ---------------------------------------------------------------------------
# Class (h): solution leaks
# ---------------------------------------------------------------------------

LEAN_TODO = (
    "theorem exo1_self_zero :\n"
    "    PacLearning.trueError Dcoin (fun _ => true) (fun _ => true) = 0 := by\n"
    "  -- TODO etudiant\n"
    "  sorry"
)

class TestSolutionLeak:
    def test_worked_proof_before_todo_fires(self):
        cells = [
            _md("### Exercice 1\nProuvez le théorème.\n"
                "```lean\ntheorem exo1_self_zero :\n"
                "    PacLearning.trueError Dcoin (fun _ => true) (fun _ => true) = 0 := by\n"
                "  exact PacLearning.trueError_self Dcoin (fun _ => true)\n```"),
            _code(LEAN_TODO),
        ]
        f = scan_solution_leak(cells)
        assert _cats(f) == {"SOLUTION_LEAK"} and f[0]["severity"] == "HIGH"
        assert "trueError_self" in f[0]["message"] or "exo1_self_zero" in f[0]["message"]

    def test_skeleton_fence_with_sorry_is_silent(self):
        cells = [
            _md("### Exercice 1\nLe squelette :\n"
                "```lean\ntheorem exo1_self_zero :\n"
                "  -- TODO etudiant\n  sorry\n```"),
            _code(LEAN_TODO),
        ]
        assert scan_solution_leak(cells) == []

    def test_given_data_fence_is_silent(self):
        # Scaffolding: the md shows the data the exercise works on (#CSP-4).
        cells = [
            _md("Les donnees :\n```csharp\njobs_data = [\n    (1, 4, 20),\n]\n```"),
            _code("var model = build(jobs_data); // TODO etudiant\n"),
        ]
        assert scan_solution_leak(cells) == []


# ---------------------------------------------------------------------------
# Class (d): arithmetic
# ---------------------------------------------------------------------------

class TestArithmetic:
    def test_false_multiplication_fires(self):
        f = scan_arithmetic([_md("On obtient 30 × 4 = 150 runs au total.")])
        assert _cats(f) == {"ARITH_WRONG"} and f[0]["severity"] == "HIGH"

    def test_true_multiplication_is_silent(self):
        assert scan_arithmetic([_md("30 compositions × 5 graines = 150 runs.")]) == []

    def test_tail_of_longer_sum_is_silent(self):
        # "2 x 7 x 3 = 42" -- the tail "7 x 3 = 42" must not fire.
        assert scan_arithmetic([_md("(2 × 7 × 3 = 42)")]) == []
        assert scan_arithmetic([_md("20×5 + 25×3 + 40×2 = 375cm")]) == []


# ---------------------------------------------------------------------------
# Class (g): phantoms
# ---------------------------------------------------------------------------

class TestPhantom:
    def test_phantom_entity_fires(self):
        # #14166: the md shows `Race` as a combinator; the code defines Switch.
        cells = [
            _md("Le generateur :\n```python\ncombinator = rng.choice([\"Seq\", \"Parallel\", \"Race\"])\nresult = Race(op1, op2)\n```"),
            _md("Autre exemple :\n```python\nchosen = Race(x, y)\n```"),
            _code("class Switch:\n    pass\nrng.choice([\"Seq\", \"Switch\"])",
                  [_out_text("4 combinateurs : Seq, Switch, Repeat, Parallel")]),
        ]
        f = scan_phantom(cells)
        assert "PHANTOM_IN_FENCE" in _cats(f)
        assert any("Race" in x["message"] for x in f)

    def test_real_entity_is_silent(self):
        cells = [
            _md("Le combinateur :\n```python\ncombinator = Switch(op1, op2)\nchoisi = Switch(a, b)\n```"),
            _code("class Switch:\n    pass"),
        ]
        assert scan_phantom(cells) == []

    def test_french_trailing_comments_are_silent(self):
        # Lean fences carry French trailing comments (#14161) whose words are
        # not entities.
        cells = [
            _md("```lean\nweight := fun _ => 1 / 2    -- chaque poids vaut 1/2\n"
                "sum_one := by simp              -- la somme des poids vaut 1\n```"),
            _md("```lean\nautre := poids (x) -- la somme des poids vaut 1\n```"),
            _code("def weight := 1 / 2"),
        ]
        assert scan_phantom(cells) == []

    def test_prose_line_in_fence_is_silent(self):
        # Simulated output lines are not code (#14164).
        cells = [
            _md("Sortie :\n```\nPlanning realisable avec B : duree = 4.5h\n```\n"
                "Autre :\n```\nPlanning realisable sans B : duree = 4.0h\n```\n"),
            _code("var planning = Solve();"),
        ]
        assert scan_phantom(cells) == []

    def test_base64_image_not_counted_as_existence(self):
        # A bare `Race` inside an image/png payload is coincidence.
        png = {"output_type": "display_data", "data": {"image/png": "aEVJRaceU5N"}}
        cells = [
            _md("```python\ncombinateur = Race(a, b)\n```"),
            _md("```python\nchoix = Race(c, d)\n```"),
            _code("class Switch:\n    pass", [png]),
        ]
        assert "PHANTOM_IN_FENCE" in _cats(scan_phantom(cells))


# ---------------------------------------------------------------------------
# Class (a): ungrounded numbers
# ---------------------------------------------------------------------------

class TestNumbers:
    def test_fabricated_decimal_fires_low(self):
        cells = [
            _md("La mediane atteint 0.9953 selon code[0]."),
            _code("print(0.9950)", [_out_text("0.9950")]),
        ]
        f = scan_numbers(cells)
        assert _cats(f) == {"UNGROUNDED_NUMBER"} and f[0]["severity"] == "LOW"

    def test_grounded_decimal_is_silent(self):
        cells = [
            _md("La mediane atteint 0.9953 selon code[0]."),
            _code("print(0.9953)", [_out_text("0.9953")]),
        ]
        assert scan_numbers(cells) == []

    def test_short_bounds_are_silent(self):
        cells = [_md("Avec delta = 0.05 et code[0]."), _code("pass")]
        assert scan_numbers(cells) == []


# ---------------------------------------------------------------------------
# CI wrapper: regression semantics
# ---------------------------------------------------------------------------

def _nb_file(path: Path, cells: list[dict]) -> Path:
    path.write_text(json.dumps({"cells": cells, "metadata": {}, "nbformat": 4}), encoding="utf-8")
    return path


class TestCiGate:
    def test_new_high_finding_is_a_regression(self, tmp_path):
        base = _nb_file(tmp_path / "base.ipynb",
                        [_md("# Titre"), _code("1+1"), _md("interp")])
        head = _nb_file(tmp_path / "head.ipynb",
                        [_md("# Titre"), _code("1+1"), _md("interp de code[9]")])
        new = enrich_quality_ci.regressions(str(base), str(head), tmp_path)
        assert any(c == "ANCHOR_OOR" for c, _ in new)
        assert enrich_quality_ci.main(["--base", str(base), "--head", str(head),
                                       "--repo-root", str(tmp_path)]) == 1

    def test_pre_existing_finding_does_not_block(self, tmp_path):
        bad_md = "interp de code[9]"
        base = _nb_file(tmp_path / "base.ipynb",
                        [_md("# Titre"), _code("1+1"), _md(bad_md)])
        head = _nb_file(tmp_path / "head.ipynb",
                        [_md("# Titre"), _code("1+1"), _md(bad_md),
                         _md("Ajout inoffensif sans defaut.")])
        assert enrich_quality_ci.regressions(str(base), str(head), tmp_path) == []
        assert enrich_quality_ci.main(["--base", str(base), "--head", str(head),
                                       "--repo-root", str(tmp_path)]) == 0

    def test_no_base_every_high_counts(self, tmp_path):
        head = _nb_file(tmp_path / "head.ipynb",
                        [_md("# Titre"), _code("1+1"), _md("interp de code[9]")])
        assert enrich_quality_ci.main(["--base", "NONE", "--head", str(head),
                                       "--repo-root", str(tmp_path)]) == 1
