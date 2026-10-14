"""Tests pour scripts/notebook_tools/check_series_finish.py.

Issue #19478 : (1) docstring l.14-15 ne refletait pas le comportement
recursif reel -- corrigee. (2) l'exclusion `_output` ne portait que
sur les dossiers ; un fichier `X_output.ipynb` isole etait comptabilise
comme carnet de la serie -- corrige par exclusion de suffixe de fichier.
"""
import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))

import check_series_finish  # noqa: E402


def _write_nb(path: Path, md_blocks: list[str]) -> None:
    """Ecrit un notebook minimal avec les blocs markdown donnes."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": [
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": [b + "\n" for b in md_blocks],
            },
            {
                "cell_type": "code",
                "metadata": {},
                "source": ["print('x')\n"],
                "outputs": [],
                "execution_count": 1,
            },
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")


# Le bloc canonique minimum qu'un carnet fini doit porter
CANONICAL_BLOCKS = ["## A retenir", "## Verifiez votre comprehension", "## Pour aller plus loin"]


class TestListSeriesNotebooks:
    """Issue #19478 (2) : exclusion par suffixe de fichier `*_output.ipynb`."""

    def test_excludes_file_with_output_suffix(self, tmp_path, monkeypatch):
        """Un fichier `X_output.ipynb` isole (hors dossier `_output`) est exclu."""
        # Repertoire de la serie
        series = "ML"
        sdir = tmp_path / "MyIA.AI.Notebooks" / series
        sdir.mkdir(parents=True)
        # Carnet normal
        _write_nb(sdir / "01-carnet-normal.ipynb", CANONICAL_BLOCKS)
        # Carnet avec suffixe _output (isole, hors dossier)
        _write_nb(sdir / "draft_output.ipynb", CANONICAL_BLOCKS)
        monkeypatch.setattr(check_series_finish, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
        result = check_series_finish.list_series_notebooks(series)
        names = [Path(p).name for p in result]
        assert "01-carnet-normal.ipynb" in names
        assert "draft_output.ipynb" not in names

    def test_does_not_exclude_carnet_with_output_in_middle_of_name(self, tmp_path, monkeypatch):
        """`output` au milieu du nom (pas en suffixe) n'est pas exclu -- seul `_output.ipynb` l'est."""
        sdir = tmp_path / "MyIA.AI.Notebooks" / "ML"
        sdir.mkdir(parents=True)
        _write_nb(sdir / "01-carnet.ipynb", CANONICAL_BLOCKS)
        # Nom avec `output` au milieu (pas suffixe) : carnet legitime
        _write_nb(sdir / "02-output-monitoring.ipynb", CANONICAL_BLOCKS)
        monkeypatch.setattr(check_series_finish, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
        result = check_series_finish.list_series_notebooks("ML")
        names = [Path(p).name for p in result]
        assert "01-carnet.ipynb" in names
        assert "02-output-monitoring.ipynb" in names

    def test_excludes_output_directory_recursively(self, tmp_path, monkeypatch):
        """Le dossier `_output/` reste exclu recursivement (pas de regression sur l'existant)."""
        sdir = tmp_path / "MyIA.AI.Notebooks" / "ML"
        sdir.mkdir(parents=True)
        # Carnet normal au top-level
        _write_nb(sdir / "01.ipynb", CANONICAL_BLOCKS)
        # Dossier _output/ avec carnet dedans
        _write_nb(sdir / "_output" / "00-archive.ipynb", CANONICAL_BLOCKS)
        monkeypatch.setattr(check_series_finish, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
        result = check_series_finish.list_series_notebooks("ML")
        names = [Path(p).name for p in result]
        assert "01.ipynb" in names
        assert "00-archive.ipynb" not in names

    def test_excludes_archive_and_checkpoints_segments(self, tmp_path, monkeypatch):
        """`_archive/` et `.ipynb_checkpoints/` toujours exclus."""
        sdir = tmp_path / "MyIA.AI.Notebooks" / "ML"
        sdir.mkdir(parents=True)
        _write_nb(sdir / "01.ipynb", CANONICAL_BLOCKS)
        _write_nb(sdir / "_archive" / "old.ipynb", CANONICAL_BLOCKS)
        _write_nb(sdir / ".ipynb_checkpoints" / "ckpt.ipynb", CANONICAL_BLOCKS)
        monkeypatch.setattr(check_series_finish, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
        result = check_series_finish.list_series_notebooks("ML")
        names = [Path(p).name for p in result]
        assert "01.ipynb" in names
        assert "old.ipynb" not in names
        assert "ckpt.ipynb" not in names

    def test_recursive_deep_subdirectory_is_included(self, tmp_path, monkeypatch):
        """Le chemin principal est recursif (cf finition-de-serie.md) : un carnet dans un sous-dossier non exclu est inclus."""
        sdir = tmp_path / "MyIA.AI.Notebooks" / "ML"
        sdir.mkdir(parents=True)
        # Carnet au top-level
        _write_nb(sdir / "01.ipynb", CANONICAL_BLOCKS)
        # Carnet dans sous-dossier non exclu
        _write_nb(sdir / "subdir" / "02.ipynb", CANONICAL_BLOCKS)
        monkeypatch.setattr(check_series_finish, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
        result = check_series_finish.list_series_notebooks("ML")
        names = [Path(p).name for p in result]
        assert "01.ipynb" in names
        assert "02.ipynb" in names
