#!/usr/bin/env python3
"""Confrontation du compteur d'exercices et de l'organe de lecture (#23398).

Deux organes du depot traitent la meme notion -- « une cellule de code est-elle
un exercice ? » -- et le compteur NE REDEVINAIT pas la convention de
l'exemple : sa docstring annoncait « un titre markdown Exemple suivi de code
est un exemple », sans que l'ATTRIBUTION (ce qui fait qu'un exemple guide
existe) soit prise en compte.

Or la digestion des travaux etudiants (#15042) conserve le code de l'etudiant
VERBATIM sous un en-tete d'exemple guide CREDITE, en-tete d'origine
« # Exercice N » compris : le compteur y comptait un exercice inexistant.

Ces tests confrontent les DEUX organes sur la meme cellule -- controles
POSITIF et NEGATIF -- comme le demande l'acceptance de #23398 :

  * controle NEGATIF (l'exemple SANS attribution) : l'en-tete ne dit rien du
    role du code, le CONTENU tranche -> les deux organes doivent dire
    « exercice » ;
  * controle POSITIF (l'exemple CREDITE) : l'attribution tranche -> les deux
    organes doivent dire « pas un exercice » ;
  * controle POSITIF complementaire : un en-tete d'exercice suivi d'un exemple
    CREDITE ne doit pas apparier le code de l'exemple (il n'a pas de stub).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

from check_credited_examples import is_credited_example_header  # noqa: E402
from check_split_reading_cells import (  # noqa: E402
    is_credited_example_code,
    is_exercise_cell,
)
from count_exercises import (  # noqa: E402
    _is_stub_code,
    count_exercises_in_notebook,
)

STUDENT_CODE = (
    "# Exercice 2 : code verbatim de l'etudiant\n"
    "# TODO etudiant\n"
    "pass\n"
)


def _split_source(source: str) -> list[str]:
    """Split a source string into nbformat's list-of-lines form (newlines kept)."""
    if not source:
        return []
    return source.splitlines(keepends=True)


def _md(source: str) -> dict:
    return {
        "cell_type": "markdown",
        "source": _split_source(source),
        "metadata": {},
    }


def _code(source: str) -> dict:
    return {
        "cell_type": "code",
        "source": _split_source(source),
        "metadata": {},
        "execution_count": None,
        "outputs": [],
    }


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _reader_says_exercise(cells: list[dict], idx: int) -> bool:
    """Verdict de l'ORGANE DE LECTURE sur la cellule de code `idx`.

    L'organe tranche par le CONTENU (``is_exercise_cell``), moins le carve-out
    d'exemple guide credite (``is_credited_example_code``) -- c'est la
    convention que le carve-out #23378 a donnee au proprietaire
    ``check_credited_examples``.
    """
    if not is_exercise_cell(cells[idx]):
        return False
    return not is_credited_example_code(cells, idx)


def _counter_exercised_code_indices(result, cells: list[dict]) -> set[int]:
    """Cellules de CODE que le compteur rattache a un exercice.

    Un hit markdown (l'en-tete « Exercice N ») et le stub qu'il apparie ne
    comptent qu'UNE fois, et le hit porte sur l'en-tete : le stub apparie est
    la cellule de code la plus proche de l'en-tete. On la restitue ici pour
    pouvoir confronter le compteur a l'organe de lecture CELLULE PAR CELLULE.
    """
    out: set[int] = set()
    for hit in result.exercises:
        if hit.cell_type == "code":
            out.add(hit.cell_index)
            continue
        for direction in (-1, 1):
            j = hit.cell_index + direction
            while 0 <= j < len(cells):
                if cells[j]["cell_type"] == "code":
                    source = "".join(cells[j]["source"])
                    if _is_stub_code(source):
                        out.add(j)
                    break
                j += direction
    return out


def _corpus_cells() -> list[dict]:
    """Carnet de test : un exercice, un exemple CREDITE, un exemple nu."""
    return [
        _md("### Exercice 1 : premiere tache\n"),
        _code("# Exercice 1\n# TODO etudiant\npass\n"),
        _md("### Exemple guide (credite #1234)\n"),
        _code(STUDENT_CODE),
        _md("### Exemple sans attribution\n"),
        _code("# Exercice 3\n# TODO etudiant\npass\n"),
    ]


class TestCountExercisesExamples:
    def test_exemple_credite_nest_pas_compte(self, tmp_path):
        """Le code verbatim d'un exemple guide CREDITE n'est pas un exercice."""
        cells = _corpus_cells()
        nb = _write_nb(tmp_path / "credite.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        counted = {hit.cell_index for hit in result.exercises}
        assert 3 not in counted, (
            "le code d'un exemple guide CREDITE ne doit pas etre compte "
            "comme un exercice (convention consommee chez son proprietaire)"
        )

    def test_exemple_sans_attribution_reste_exercice(self, tmp_path):
        """Sans attribution, l'en-tete ne dit rien : le CONTENU tranche."""
        cells = _corpus_cells()
        nb = _write_nb(tmp_path / "nu.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        counted = {hit.cell_index for hit in result.exercises}
        assert 5 in counted, (
            "un stub sous un exemple SANS attribution reste un exercice : "
            "l'en-tete ne dit rien du role du code"
        )

    def test_compte_attendu(self, tmp_path):
        """Deux exercices comptables : l'exercice nu et le stub sans credit."""
        cells = _corpus_cells()
        nb = _write_nb(tmp_path / "total.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        assert result.count == 2
        assert _counter_exercised_code_indices(result, cells) == {1, 5}

    def test_confrontation_des_deux_organes(self, tmp_path):
        """Les deux organes disent la MEME chose sur la MEME cellule."""
        cells = _corpus_cells()
        nb = _write_nb(tmp_path / "confrontation.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        exercised = _counter_exercised_code_indices(result, cells)
        for idx, cell in enumerate(cells):
            if cell["cell_type"] != "code":
                continue
            assert (idx in exercised) == _reader_says_exercise(cells, idx), (
                f"divergence compteur / organe de lecture sur la cellule {idx}"
            )

    def test_en_tete_exercice_ne_paire_pas_un_exemple_credite(self, tmp_path):
        """Un en-tete d'exercice suivi d'un exemple CREDITE n'a pas de stub."""
        cells = [
            _md("### Exercice 1 : apres un exemple\n"),
            _md("### Exemple guide (credite #2345)\n"),
            _code(STUDENT_CODE),
        ]
        nb = _write_nb(tmp_path / "bloque.ipynb", cells)
        result = count_exercises_in_notebook(nb)
        counted = {hit.cell_index for hit in result.exercises}
        assert counted == set()
        assert result.unpaired_markdown_instances == 0

    def test_convention_attribuee_a_un_seul_module(self):
        """Le proprietaire de la convention reconnait l'attribution, lui seul."""
        credited = _md("### Exemple guide (credite #1234)\n")
        nu = _md("### Exemple sans attribution\n")
        assert is_credited_example_header(credited) is True
        assert is_credited_example_header(nu) is False
