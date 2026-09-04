"""Tests du module fallacy_coverage_matrix (#14110).

Les fixtures sont de vrais notebooks (squelettes réalistes de la série
FallacyDetection) écrits en mémoire : le module ne lit que du JSON, aucune
dépendance réseau ou jupyter n'est requise.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.notebook_tools.fallacy_coverage_matrix import (
    _inventory_lengths,
    _row,
    build_matrix,
    heatmap_payload,
    markdown_table,
)


def _nb(*code_cells):
    """Construit un notebook minimal dont chaque param est un tuple
    (source, executed_exec_count, kind) où kind sterne le type de sortie."""
    cells = []
    for i, (src, exec_count, outs) in enumerate(code_cells):
        cell = {
            "cell_type": "code",
            "execution_count": exec_count,
            "metadata": {},
            "outputs": [],
            "source": src.split("\n"),
            "id": f"test-{i}",
        }
        for kind in outs:
            if kind == "png":
                cell["outputs"].append(
                    {"output_type": "display_data", "data": {"image/png": "AAA"}}
                )
            elif kind == "error":
                cell["outputs"].append({"output_type": "error", "ename": "X"})
            else:
                cell["outputs"].append(
                    {"output_type": "stream", "name": "stdout", "text": ["ok"]}
                )
        cells.append(cell)
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


@pytest.fixture()
def series(tmp_path: Path):
    """Série FallacyDetection réaliste : 3 notebooks + le 04 de synthèse."""
    Path(tmp_path).mkdir(parents=True, exist_ok=True)
    (tmp_path / "01_taxonomy_intro.ipynb").write_text(
        json.dumps(
            _nb(
                (
                    '# Exemple. attendu = {"E1": ("formel", "ad hominem"),\n'
                    '           "E2": ("informel", "faux dilemme"),\n'
                    '           "E3": ("formel", "ad hominem")}\n'
                    'for k, txt in exemples.items(): print(cat, t)',
                    1,
                    ["stream"],
                ),
                ("# Exercice 1 — étiqueter", None, []),
                ("print('formel et informel')", 3, ["stream"]),
            )
        ),
        encoding="utf-8",
    )
    (tmp_path / "02_fallacy_datasets_landscape.ipynb").write_text(
        json.dumps(
            _nb(
                (
                    'import requests\n'
                    'S = requests.Session()\n'
                    'sc, meta = http_get("https://github.com/causalNLP/logical-fallacy")\n'
                    'sc2 = http_get("https://huggingface.co/api/datasets?search=cmv")',
                    1,
                    ["stream", "stream"],
                ),
                ("# Exercice 1 — Argotario", None, []),
            )
        ),
        encoding="utf-8",
    )
    (tmp_path / "03_taxonomy_coverage_gap.ipynb").write_text(
        json.dumps(
            _nb(
                (
                    'LOGIC_13 = ["Appeal to authority", "Appeal to emotion",\n'
                    '            "Bandwagon", "False causality", "Hasty generalization",\n'
                    '            "Straw man", "Ad hominem", "False dilemma",\n'
                    '            "Slippery slope", "Begging the question",\n'
                    '            "Appeal to ignorance", "Circular reasoning",\n'
                    '            "Red herring"]\n'
                    "academic_count = len(LOGIC_13)\n"
                    "print(academic_count)",
                    5,
                    ["stream"],
                ),
                ("# Exercice 2 — Walton", None, []),
            )
        ),
        encoding="utf-8",
    )
    (tmp_path / "04_coverage_matrix.ipynb").write_text(
        json.dumps(_nb(("import fallacy_coverage_matrix as fcm\nprint(fcm)" , 1, ["stream"]))),
        encoding="utf-8",
    )
    return tmp_path


class TestInventoryLengths:
    def test_variable_listera_inventaire(self):
        code = 'LOGIC_13 = ["a", "b", "c"]'
        assert _inventory_lengths(code) == [3]

    def test_variable_sans_indice_ignoree(self):
        code = 'exemples = ["a", "b", "c"]'
        assert _inventory_lengths(code) == []

    def test_dict_de_tuples_repere_types(self):
        code = 'attendu = {"E1": ("formel", "ad hominem"), "E2": ("informel", "faux dilemme")}'
        assert _inventory_lengths(code) == []


class TestRow:
    def test_compte_exercices_types_formalismes(self, series: Path):
        row = _row(series / "01_taxonomy_intro.ipynb")
        assert row["exercises"] == 1
        assert row["sophismes"] == 2  # ad hominem + faux dilemme (dédupliqués)
        assert row["formalismes"] == 2  # cellule attendu + print('formel et informel')
        assert row["domaines"] == 0

    def test_domaines_externes_distincts(self, series: Path):
        row = _row(series / "02_fallacy_datasets_landscape.ipynb")
        assert row["domaines"] == 2  # github.com + huggingface.co, uniques

    def test_inventaire_logique_13(self, series: Path):
        row = _row(series / "03_taxonomy_coverage_gap.ipynb")
        assert row["sophismes"] == 13

    def test_preuve_execution_et_png(self, series: Path):
        row = _row(series / "01_taxonomy_intro.ipynb")
        assert row["executed"] == 2
        assert row["ratio"] == pytest.approx(2 / 3, abs=0.01)
        assert row["errors"] == 0

    def test_exercice_avec_output_vide_compete(self, series: Path):
        row = _row(series / "01_taxonomy_intro.ipynb")
        assert row["outputs"] >= 1


class TestBuildMatrix:
    def test_quatre_notebooks(self, series: Path):
        rows = build_matrix(series)
        assert [r["notebook"] for r in rows] == [
            "01_taxonomy_intro.ipynb",
            "02_fallacy_datasets_landscape.ipynb",
            "03_taxonomy_coverage_gap.ipynb",
            "04_coverage_matrix.ipynb",
        ]

    def test_markdown_contient_totaux(self, series: Path):
        rows = build_matrix(series)
        md = markdown_table(rows)
        assert "**Série**" in md
        assert "Sophismes" in md

    def test_heatmap_payload_dims(self, series: Path):
        rows = build_matrix(series)
        labels, grid = heatmap_payload(rows)
        assert len(labels) == len(grid) == 6
        assert all(len(g) == len(rows) for g in grid)


if __name__ == "__main__":
    raise SystemExit(pytest.main(["-q", __file__]))