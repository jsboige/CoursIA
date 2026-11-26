"""Tests de ``tv.loc`` -- designation des carnets par index et famille de noyau.

Issue #28587 (etape R1) : une cellule de code ne doit plus citer un carnet de la
serie par son nom de fichier. Le carnet se designe par son index (``TV-00a``)
et sa famille de noyau ; le fichier se resout sur ``metadata.kernelspec.name``.
"""
import json
import sys
from pathlib import Path

import pytest

_SERIE = (Path(__file__).resolve().parents[2]
          / "MyIA.AI.Notebooks" / "GenAI" / "Texte" / "TransformerVariants")
if str(_SERIE) not in sys.path:
    sys.path.insert(0, str(_SERIE))

from tv import loc  # noqa: E402


def _ecrire(repertoire: Path, nom: str, noyau: str, lignes=("x = 1",)) -> Path:
    """Ecrit un carnet minimal dont la famille se lit au noyau declare."""
    carnet = {
        "cells": [{"cell_type": "code", "metadata": {}, "source": list(lignes),
                   "execution_count": 1, "outputs": []}],
        "metadata": {"kernelspec": {"name": noyau, "language": "python"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    chemin = repertoire / nom
    chemin.write_text(json.dumps(carnet), encoding="utf-8")
    return chemin


def test_selection_par_noyau_pas_par_nom(tmp_path):
    """Un index porte un carnet Python et son pendant C# : le noyau tranche."""
    _ecrire(tmp_path, "TV-00a-RoPE-from-scratch.ipynb", "python3")
    _ecrire(tmp_path, "TV-00a-RoPE-from-scratch-CSharp.ipynb", ".net-csharp")

    assert loc.carnet_index("TV-00a", base=tmp_path) == 1
    assert loc.carnet_index("TV-00a", famille="csharp", base=tmp_path) == 1


def test_invariance_au_suffixe_de_noyau(tmp_path):
    """Renommer le carnet (chantier A) ne change pas la valeur mesuree."""
    _ecrire(tmp_path, "TV-01-Attention-Variants-SOTA.ipynb", "python3")
    avant = loc.carnet_index("TV-01", base=tmp_path)

    (tmp_path / "TV-01-Attention-Variants-SOTA.ipynb").rename(
        tmp_path / "TV-01-Attention-Variants-SOTA-Python.ipynb")

    assert loc.carnet_index("TV-01", base=tmp_path) == avant


def test_sans_candidat_leve_en_nommant_les_vus(tmp_path):
    """Fail-closed : aucune famille ne correspond -> erreur, jamais un zero."""
    _ecrire(tmp_path, "TV-02-MoE-SOTA.ipynb", ".net-csharp")

    with pytest.raises(FileNotFoundError) as exc:
        loc.carnet_index("TV-02", base=tmp_path)
    assert "TV-02-MoE-SOTA.ipynb" in str(exc.value)
    assert ".net-csharp" in str(exc.value)


def test_deux_candidats_de_la_meme_famille_levent(tmp_path):
    """Deux carnets du meme index et de la meme famille : ambigu, il leve."""
    _ecrire(tmp_path, "TV-03-CoT.ipynb", "python3")
    _ecrire(tmp_path, "TV-03-CoT-bis.ipynb", "python3")

    with pytest.raises(RuntimeError) as exc:
        loc.carnet_index("TV-03", base=tmp_path)
    assert "TV-03-CoT.ipynb" in str(exc.value)
    assert "TV-03-CoT-bis.ipynb" in str(exc.value)


def test_sorties_papermill_ignorees(tmp_path):
    """Le carnet ``*_output.ipynb`` d'une execution ne cree pas d'ambiguite."""
    _ecrire(tmp_path, "TV-04-DiscoLoop.ipynb", "python3")
    _ecrire(tmp_path, "TV-04-DiscoLoop_output.ipynb", "python3")

    assert loc.carnet_index("TV-04", base=tmp_path) == 1


def test_famille_inconnue_refusee(tmp_path):
    """Une famille hors du registre est une faute d'appel, pas une absence."""
    _ecrire(tmp_path, "TV-00d-Encodeurs.ipynb", "python3")

    with pytest.raises(ValueError) as exc:
        loc.carnet_index("TV-00d", famille="julia", base=tmp_path)
    assert "julia" in str(exc.value)


def test_carnet_nomme_reste_exporte():
    """``carnet()`` survit a R1 : la cellule 33 de TV-02 s'en sert (R2)."""
    assert callable(loc.carnet)
    assert callable(loc.carnet_index)
