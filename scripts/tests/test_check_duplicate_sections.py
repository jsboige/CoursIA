#!/usr/bin/env python3
"""Tests de ``check_duplicate_sections`` -- controles positifs ET negatifs.

Le controle NEGATIF est le plus important des deux : un detecteur de
duplication qui rougit sur un notebook sain transformerait la campagne de
redressement en fabrique de faux travail, exactement le defaut que la
campagne repare.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_duplicate_sections import (  # noqa: E402
    analyse_notebook,
    excess_count,
    main,
    normalise,
)


def write_notebook(tmp_path: Path, cells: list, name: str = "nb.ipynb") -> Path:
    payload = {
        "cells": [
            {"cell_type": kind, "source": source, "metadata": {}}
            if kind == "markdown"
            else {
                "cell_type": kind,
                "source": source,
                "metadata": {},
                "outputs": [],
                "execution_count": 1,
            }
            for kind, source in cells
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path = tmp_path / name
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


# --------------------------------------------------------------------------
# normalisation
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("raw", "expected"),
    [
        ("## Résumé", "resume"),
        ("### **Résumé**", "resume"),
        ("## 3. Résumé", "resume"),
        ("####   Synthèse   ", "synthese"),
        ("## Interprétation", "interpretation"),
    ],
)
def test_normalise_collapses_emphasis_numbering_and_accents(raw, expected):
    assert normalise(raw) == expected


# --------------------------------------------------------------------------
# controles NEGATIFS -- un notebook sain ne doit rien rendre
# --------------------------------------------------------------------------


def test_healthy_notebook_has_no_finding(tmp_path):
    path = write_notebook(
        tmp_path,
        [
            ("markdown", "# Titre\n\nIntroduction du notebook."),
            ("code", "print(1)"),
            ("markdown", "### Lecture du résultat\n\nLa sortie vaut 1."),
            ("code", "print(2)"),
            ("markdown", "### Analyse de la convergence\n\nElle est rapide."),
            ("markdown", "## Résumé\n\nCe notebook a montré une chose."),
        ],
    )
    record = analyse_notebook(path, tmp_path)
    assert record["findings"] == []


def test_distinct_reading_titles_are_not_duplicates(tmp_path):
    """Deux lectures DIFFERENTES sur deux cellules differentes = legitime."""
    path = write_notebook(
        tmp_path,
        [
            ("code", "a()"),
            ("markdown", "### Lecture du résultat de la régression"),
            ("code", "b()"),
            ("markdown", "### Lecture du résultat de la classification"),
        ],
    )
    assert analyse_notebook(path, tmp_path)["findings"] == []


def test_single_closing_in_tail_raises_no_advisory(tmp_path):
    path = write_notebook(
        tmp_path,
        [("code", "x()"), ("code", "y()"), ("markdown", "## Conclusion\n\nFin.")],
    )
    assert analyse_notebook(path, tmp_path)["advisory"] == []


# --------------------------------------------------------------------------
# controles POSITIFS -- le defaut nomme par le user
# --------------------------------------------------------------------------


def test_doubled_summary_is_caught(tmp_path):
    """Le defaut verbatim : « un résumé en double »."""
    path = write_notebook(
        tmp_path,
        [
            ("markdown", "# Titre"),
            ("code", "run()"),
            ("markdown", "## Résumé\n\nPremière version du résumé."),
            ("markdown", "## Résumé\n\nSeconde version, ajoutée par une tranche."),
        ],
    )
    findings = analyse_notebook(path, tmp_path)["findings"]
    assert [f["kind"] for f in findings] == ["dup_closing"]
    assert findings[0]["title"] == "resume"
    assert findings[0]["occurrences"] == 2
    assert findings[0]["cells"] == [2, 3]


def test_doubled_summary_caught_through_emphasis_and_numbering(tmp_path):
    """« ## Résumé » et « ### **3. Résumé** » sont le MEME titre."""
    path = write_notebook(
        tmp_path,
        [
            ("markdown", "## Résumé\n\nA."),
            ("markdown", "### **3. Résumé**\n\nB."),
        ],
    )
    findings = analyse_notebook(path, tmp_path)["findings"]
    assert findings and findings[0]["occurrences"] == 2


def test_stacked_interpretations_are_caught(tmp_path):
    """L'empilement de lectures : trois « Interprétation » dans le notebook."""
    path = write_notebook(
        tmp_path,
        [
            ("markdown", "### Interprétation\n\nUne."),
            ("code", "z()"),
            ("markdown", "### Interprétation\n\nDeux."),
            ("code", "w()"),
            ("markdown", "### Interprétation\n\nTrois."),
        ],
    )
    findings = analyse_notebook(path, tmp_path)["findings"]
    assert [f["kind"] for f in findings] == ["dup_reading"]
    assert findings[0]["occurrences"] == 3
    assert excess_count(analyse_notebook(path, tmp_path)) == 2


def test_multi_closing_in_tail_is_advisory_not_finding(tmp_path):
    """Deux clotures DISTINCTES : signal faible, jamais bloquant."""
    path = write_notebook(
        tmp_path,
        [
            ("code", "a()"),
            ("code", "b()"),
            ("markdown", "## Résumé\n\nR."),
            ("markdown", "## Ce qu'il faut retenir\n\nC."),
        ],
    )
    record = analyse_notebook(path, tmp_path)
    assert record["findings"] == []
    assert record["advisory"] and record["advisory"][0]["kind"] == "multi_closing"


# --------------------------------------------------------------------------
# robustesse : un JSON corrompu ne doit PAS interrompre le balayage
# --------------------------------------------------------------------------


def test_unreadable_notebook_is_reported_not_raised(tmp_path):
    path = tmp_path / "broken.ipynb"
    path.write_text('{"cells": [', encoding="utf-8")
    record = analyse_notebook(path, tmp_path)
    assert [f["kind"] for f in record["findings"]] == ["unreadable"]


def test_scan_continues_past_a_corrupt_notebook(tmp_path, capsys):
    """Lecon #17044 : un scanner qui s'arrete au premier corrompu ment."""
    (tmp_path / "broken.ipynb").write_text("{ nope", encoding="utf-8")
    write_notebook(
        tmp_path,
        [("markdown", "## Résumé\n\nA."), ("markdown", "## Résumé\n\nB.")],
        name="zz_after.ipynb",
    )
    rc = main(["--json", "--root", str(tmp_path), str(tmp_path)])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["scanned"] == 2
    assert payload["unreadable"] == 1
    assert payload["carriers"] == 1  # le notebook APRES le corrompu est bien vu


# --------------------------------------------------------------------------
# contrat CLI
# --------------------------------------------------------------------------


def test_fail_on_findings_returns_2(tmp_path):
    write_notebook(
        tmp_path, [("markdown", "## Résumé\n\nA."), ("markdown", "## Résumé\n\nB.")]
    )
    assert main(["--fail-on-findings", "--root", str(tmp_path), str(tmp_path)]) == 2


def test_clean_tree_returns_0_even_with_fail_flag(tmp_path):
    write_notebook(tmp_path, [("markdown", "## Résumé\n\nSeul.")])
    assert main(["--fail-on-findings", "--root", str(tmp_path), str(tmp_path)]) == 0


def test_json_carries_the_not_an_acceptance_criterion_warning(tmp_path, capsys):
    """Le rappel du mandat user vit DANS la sortie machine, pas seulement
    dans la docstring : un consommateur qui branche un gate dessus le lit."""
    write_notebook(
        tmp_path, [("markdown", "## Résumé\n\nA."), ("markdown", "## Résumé\n\nB.")]
    )
    main(["--json", "--root", str(tmp_path), str(tmp_path)])
    payload = json.loads(capsys.readouterr().out)
    assert "NECESSAIRE" in payload["not_an_acceptance_criterion"]
    assert "SUFFISANT" in payload["not_an_acceptance_criterion"]
