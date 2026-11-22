"""Tests for numbering_holes.py (organe #26707, tranche 0).

Couvre la logique de mesure PURE (parse + trous + lettres orphelines) sur des
listes de chemins synthétiques — jamais l'état git live, pour que le test reste
stable en CI. Les contrôles réels (racine GameTheory positive, racine Sudoku
négative) sont joués à la main sur `origin/main` dans le body de PR : un
self-test qui dépendrait de l'état du dépôt casserait dès que les fournées
bouchent les trous.
"""
import sys
from pathlib import Path

import pytest  # noqa: F401  (marque le fichier comme suite pytest)

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import numbering_holes as nh  # noqa: E402


class TestMeasurePaths:
    def test_holes_and_orphan_letter(self):
        m = nh.measure_paths([
            "S/S-01-A-Python.ipynb", "S/S-02-B-Python.ipynb",
            "S/S-04-C-Python.ipynb", "S/S-03c-D-Python.ipynb"])
        assert (m["prefix"], m["max"], m["holes"], m["orphan_letters"]) == (
            "S", 4, [3], ["3c"])

    def test_hole_free(self):
        m = nh.measure_paths([
            "S/S-01-A-Python.ipynb", "S/S-02-B-Python.ipynb",
            "S/S-03-C-Python.ipynb"])
        assert m["max"] == 3 and m["holes"] == [] and m["orphan_letters"] == []

    def test_zero_preliminaries_excluded(self):
        # `0a`/`0b` sont un choix de structure : ni trous ni lettres orphelines.
        m = nh.measure_paths([
            "S/S-0a-P1.ipynb", "S/S-0b-P2.ipynb",
            "S/S-01-A-Python.ipynb", "S/S-02-B-Python.ipynb"])
        assert m["max"] == 2 and m["holes"] == [] and m["orphan_letters"] == []

    def test_csharp_twin_does_not_double_count(self):
        m = nh.measure_paths([
            "S/S-01-A-Python.ipynb", "S/S-01-A-CSharp.ipynb",
            "S/S-02-B-Python.ipynb"])
        assert m["max"] == 2 and m["holes"] == [] and m["matched"] == 3

    def test_cross_subfolder_single_series(self):
        # Numérotation continue d'un sous-dossier à l'autre : une seule série.
        m = nh.measure_paths([
            "S/d1/SC-01-A-Python.ipynb", "S/d2/SC-02-B-Python.ipynb",
            "S/d3/SC-04-C-Python.ipynb"])
        assert (m["prefix"], m["max"], m["holes"]) == ("SC", 4, [3])

    def test_letter_with_bare_present_not_orphan(self):
        m = nh.measure_paths([
            "S/S-01-A-Python.ipynb", "S/S-01b-A2-Python.ipynb",
            "S/S-02-B-Python.ipynb"])
        assert m["orphan_letters"] == [] and m["holes"] == []

    def test_no_alpha_prefix_out_of_scope(self):
        m = nh.measure_paths(["S/01-Freeform.ipynb", "S/02-Other.ipynb"])
        assert m["prefix"] is None and m["max"] is None and m["holes"] == []

    def test_documented_palier_excluded_from_holes_and_orphans(self):
        # Un palier (nu scindé en accrétions 07a/07b, le nu n'a jamais existé)
        # est hors mesure : ni trou 7, ni 07a/07b orphelines.
        m = nh.measure_paths(
            ["T/T-07a-C-Python.ipynb", "T/T-07b-D-Python.ipynb",
             "T/T-01-A-Python.ipynb", "T/T-08-E-Python.ipynb"],
            palier_exceptions=frozenset({7}))
        assert 7 not in m["holes"]
        assert m["orphan_letters"] == []

    def test_explicit_prefix_overrides_dominant(self):
        paths = ["S/S-01-A-Python.ipynb", "S/S-02-B-Python.ipynb",
                 "S/T-01-X-Python.ipynb"]
        auto = nh.measure_paths(paths)
        forced = nh.measure_paths(paths, prefix="T")
        assert auto["prefix"] == "S" and forced["prefix"] == "T"
        assert forced["max"] == 1 and forced["holes"] == []


class TestCompressRuns:
    def test_consecutive_run(self):
        assert nh.compress_runs([18, 19, 20, 24, 25, 26]) == "18-20, 24-26"

    def test_single(self):
        assert nh.compress_runs([2]) == "2"

    def test_empty(self):
        assert nh.compress_runs([]) == ""

    def test_isolated_plus_run(self):
        assert nh.compress_runs([41, 44, 45]) == "41, 44-45"


class TestMeasureRoot:
    def test_filters_to_root_subtree(self):
        all_ipynb = [
            "MyIA.AI.Notebooks/Sudoku/Sudoku-01-A.ipynb",
            "MyIA.AI.Notebooks/Sudoku/Sudoku-02-B.ipynb",
            "MyIA.AI.Notebooks/Sudoku/Sub/Sudoku-03-C.ipynb",
            "MyIA.AI.Notebooks/Sudoku2/Sudoku2-01-X.ipynb",  # hors arborescence
        ]
        m = nh.measure_root(all_ipynb, "MyIA.AI.Notebooks/Sudoku")
        assert m["root"] == "MyIA.AI.Notebooks/Sudoku"
        assert m["max"] == 3 and m["holes"] == []
        assert m["notebook_count"] == 3  # le Sudoku2 (collision de préfixe) est exclu

    def test_tweety_palier_07_excluded_via_root_lookup(self):
        # measure_root applique PALIER_EXCEPTIONS[racine] : le palier 07 de
        # Tweety (07a/07b, nu jamais existé) ne rend ni trou 7 ni orphelines.
        all_ipynb = [
            "MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-01-A.ipynb",
            "MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-06-B.ipynb",
            "MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-07a-C.ipynb",
            "MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-07b-D.ipynb",
            "MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-08-E.ipynb",
        ]
        m = nh.measure_root(
            all_ipynb, "MyIA.AI.Notebooks/SymbolicAI/Tweety")
        assert 7 not in m["holes"]
        assert m["orphan_letters"] == []


class TestOutputArtifact:
    def test_output_suffix_excluded(self):
        assert nh._is_output_artifact("S/S-01-A-Python_output.ipynb") is True

    def test_output_dir_excluded(self):
        assert nh._is_output_artifact("S/_output/S-01-A-Python.ipynb") is True

    def test_normal_kept(self):
        assert nh._is_output_artifact("S/S-01-A-Python.ipynb") is False
