"""Tests pour scripts/notebook_tools/scan_code_cell_counters.py.

Verrouille les COMPORTEMENTS DOCUMENTES du scanner de compteurs dans les
commentaires de cellules code (issue #18493, classe distincte de la prose
markdown visee par check_prose_quantitative_claims.py) :

  - Le scanner detecte les 4 formes de quantitatif documentaire :
    1. Tilde + nombre + unite  (`~1500 fichiers`)
    2. Parenthese + nombre + unite (`(60 lignes)`)
    3. Nombre + unite documentaire directe (`109 fichiers`)
    4. Approximation superieure (`>50 lignes`)

  - Le scanner Epargne les faux positifs pedagogiques :
    - Comparaisons logiques (`if x > 30`, `return min(1.0, x > 0.5)`)
    - Commentaires normaux sans quantitatif
    - Strings dans cellules markdown
    - Sorties de cellules (jamais scannees)

  - La classification KEEP / REVIEW fonctionne :
    - KEEP pour snapshots dates et references documentaires
    - REVIEW uniquement si la ligne est ambigue (defaut conservateur)

  - Le scan respecte les exclusions (archives, Papermill artifacts).

Pattern herite de ``test_check_prose_quantitative_claims.py`` : sys.path
module-level, fixtures synthetiques.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import scan_code_cell_counters as scc  # noqa: E402


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #


def _make_notebook(path: Path, code_cells: list[str]) -> None:
    """Cree un notebook minimaliste avec les cellules code donnees."""
    nb = {
        "cells": [{"cell_type": "code", "source": [c], "metadata": {}, "outputs": []} for c in code_cells],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False)


# --------------------------------------------------------------------------- #
# Tests des patterns
# --------------------------------------------------------------------------- #


class TestPatterns:
    def test_approximatif_detecte(self):
        assert scc.has_counter("# NOTE: ~1500 fichiers de la stdlib") is True

    def test_paren_detecte(self):
        assert scc.has_counter("# Code source : (302 lignes)") is True

    def test_nombre_unite_detecte(self):
        assert scc.has_counter("# 109 fichiers Lean / 44 297 LOC / 2079 sorry") is True

    def test_gt_detecte(self):
        assert scc.has_counter("# fonctions trop longues (>50 lignes)") is True

    def test_faux_positif_comparaison_logique(self):
        # "if x > 30" : pas un commentaire, ignore par is_counter_comment
        assert scc.has_counter("if x > 30:") is False

    def test_faux_positif_texte_sans_nombre(self):
        assert scc.has_counter("# Etape 1 : Verifier la grille") is False

    def test_faux_positif_test_numero(self):
        # "# Cas test 2" : "test" matche, mais le pattern N_UNIT exige nombre
        # directement suivi de l'unite -- "test 2" n'est pas N lignes.
        # Verifier que "test 1" n'est pas confondu avec un compteur.
        assert scc.has_counter("# Cas test 1 : Patient normal") is False


# --------------------------------------------------------------------------- #
# Tests de classification
# --------------------------------------------------------------------------- #


class TestClassification:
    def test_snapshot_date_est_keep(self):
        line = "# au 2026-08-11) : 109 fichiers Lean / 44 297 LOC / 2079 sorry"
        assert scc.classify_counter(line) == "KEEP"

    def test_approximatif_est_keep(self):
        assert scc.classify_counter("# ~60 lignes de FT-00a") == "KEEP"

    def test_paren_est_keep(self):
        assert scc.classify_counter("# Code source : (302 lignes)") == "KEEP"


# --------------------------------------------------------------------------- #
# Tests d'integration sur notebook synthetique
# --------------------------------------------------------------------------- #


class TestScanNotebook:
    def test_scan_compteurs_multiples(self, tmp_path: Path):
        nb_path = tmp_path / "subdir" / "test.ipynb"
        _make_notebook(
            nb_path,
            code_cells=[
                "# NOTE: ~1500 fichiers de la stdlib",
                "import os",
                "# Code source : (302 lignes)",
                "# if x > 30 : pas un compteur",
                "x = 42",
                "# Cas test 2 : Patient normal",
            ],
        )
        findings = scc.scan_notebook(nb_path)
        # 2 commentaires avec compteur (lignes 1 et 3)
        assert len(findings) == 2
        assert all(f["class"] == "KEEP" for f in findings)
        # La ligne 5 n'est pas un commentaire, donc pas scannee
        assert all(f["line_no"] in (1, 3) for f in findings)

    def test_scan_exclut_markdown(self, tmp_path: Path):
        nb_path = tmp_path / "test.ipynb"
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["# 1427 notebooks dans le depot"], "metadata": {}, "outputs": []},
                {"cell_type": "code", "source": ["import pandas"], "metadata": {}, "outputs": []},
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        with open(nb_path, "w", encoding="utf-8") as f:
            json.dump(nb, f, ensure_ascii=False)
        findings = scc.scan_notebook(nb_path)
        assert findings == []

    def test_scan_exclut_outputs(self, tmp_path: Path):
        nb_path = tmp_path / "test.ipynb"
        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "source": ["print(42)"],
                    "metadata": {},
                    "outputs": [{"output_type": "stream", "name": "stdout", "text": ["1427 notebooks trouves"]}],
                },
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        with open(nb_path, "w", encoding="utf-8") as f:
            json.dump(nb, f, ensure_ascii=False)
        findings = scc.scan_notebook(nb_path)
        assert findings == []


# --------------------------------------------------------------------------- #
# Tests de collect
# --------------------------------------------------------------------------- #


class TestCollect:
    def test_exclut_archives(self, tmp_path: Path):
        # Creer deux notebooks : un normal, un archive
        _make_notebook(tmp_path / "normal.ipynb", ["x = 1"])
        _make_notebook(tmp_path / "_archive_obsoletes" / "old.ipynb", ["x = 1"])
        nbs = scc.collect_notebooks(tmp_path)
        paths = [str(p) for p in nbs]
        assert any("normal.ipynb" in p for p in paths)
        assert not any("_archive_obsoletes" in p for p in paths)

    def test_exclut_papermill_artifacts(self, tmp_path: Path):
        _make_notebook(tmp_path / "real.ipynb", ["x = 1"])
        _make_notebook(tmp_path / "real_output.ipynb", ["x = 1"])
        nbs = scc.collect_notebooks(tmp_path)
        names = [p.name for p in nbs]
        assert "real.ipynb" in names
        assert "real_output.ipynb" not in names