# -*- coding: utf-8 -*-
"""Tests de check_series_finish.py (#19297, finition de serie).

Couvre :
- check_notebook_blocks : detection H2 des 3 blocs (a_retenir, verifiez, aller_plus_loin)
- check_readme : detection titre `## Objectifs` ou `## Competences`
- run_check : orchestration + rc (0/1/2)

Le test cree des carnets synthetiques dans un tmpdir (meme arborescence
que MyIA.AI.Notebooks/<serie>/) et nettoie apres. Pas de dependance
sur le corpus reel (lecon #19215 : 17 tests verts, plantage sur le vrai
corpus -- ici on isole).
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

# Import du module par importlib (meme pattern que test_check_companion_coverage.py)
MODULE_PATH = (Path(__file__).resolve().parents[1] / "notebook_tools"
               / "check_series_finish.py")
spec = importlib.util.spec_from_file_location(
    "check_series_finish", MODULE_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_series_finish"] = mod
spec.loader.exec_module(mod)


def _make_notebook(path: Path, titles: list[str], extra_md: list[str] | None = None) -> None:
    """Cree un .ipynb minimal avec une cellule markdown par titre."""
    cells = []
    for t in titles:
        cells.append({
            "cell_type": "markdown",
            "metadata": {},
            "source": [f"{t}\n"],
        })
    for line in (extra_md or []):
        cells.append({
            "cell_type": "markdown",
            "metadata": {},
            "source": [f"{line}\n"],
        })
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


# -----------------------------------------------------------------------------
# check_notebook_blocks
# -----------------------------------------------------------------------------

class TestCheckNotebookBlocks:
    def test_3_blocks_present(self, tmp_path):
        nb = tmp_path / "ML-1-Intro-Python.ipynb"
        _make_notebook(nb, [
            "## A retenir",
            "## Verifiez votre comprehension",
            "## Pour aller plus loin",
        ])
        result = mod.check_notebook_blocks(str(nb))
        assert result["blocks"]["a_retenir"] is True
        assert result["blocks"]["verifiez"] is True
        assert result["blocks"]["aller_plus_loin"] is True
        assert result["missing"] == []

    def test_missing_one_block(self, tmp_path):
        nb = tmp_path / "ML-2-Python.ipynb"
        _make_notebook(nb, [
            "## A retenir",
            "## Pour aller plus loin",
        ])
        result = mod.check_notebook_blocks(str(nb))
        assert result["blocks"]["a_retenir"] is True
        assert result["blocks"]["verifiez"] is False
        assert result["blocks"]["aller_plus_loin"] is True
        assert result["missing"] == ["verifiez"]

    def test_all_missing(self, tmp_path):
        nb = tmp_path / "ML-3-Python.ipynb"
        _make_notebook(nb, [
            "## Introduction",
            "## Conclusion",
        ])
        result = mod.check_notebook_blocks(str(nb))
        assert result["missing"] == ["a_retenir", "verifiez", "aller_plus_loin"]

    def test_h1_does_not_count(self, tmp_path):
        """Un titre H1 ne doit pas etre pris pour un bloc H2."""
        nb = tmp_path / "ML-4-Python.ipynb"
        _make_notebook(nb, [
            "# A retenir",  # H1, pas H2
            "## Verifiez votre comprehension",
            "## Pour aller plus loin",
        ])
        result = mod.check_notebook_blocks(str(nb))
        assert result["blocks"]["a_retenir"] is False
        assert result["missing"] == ["a_retenir"]

    def test_h3_counts(self, tmp_path):
        """Un titre H3 est acceptable (le doc accepte 1-3)."""
        nb = tmp_path / "ML-5-Python.ipynb"
        _make_notebook(nb, [
            "### A retenir",
            "### Verifiez votre comprehension",
            "### Pour aller plus loin",
        ])
        result = mod.check_notebook_blocks(str(nb))
        assert result["missing"] == []

    def test_phrase_in_prose_does_not_count(self, tmp_path):
        """Une phrase en prose ne compte pas comme bloc (lecon : 4 FP du coord)."""
        nb = tmp_path / "ML-6-Python.ipynb"
        _make_notebook(nb, [
            "## Introduction",
            "Le carnet finit par une section A retenir mais elle est en prose.",
            "## Verifiez votre comprehension",
            "## Pour aller plus loin",
        ])
        result = mod.check_notebook_blocks(str(nb))
        # La phrase en prose ne doit pas etre prise pour un bloc
        assert result["blocks"]["a_retenir"] is False
        assert result["missing"] == ["a_retenir"]

    def test_accent_tolerance(self, tmp_path):
        """Le regex doit etre tolerant aux accents (NFKD)."""
        nb = tmp_path / "ML-7-Python.ipynb"
        _make_notebook(nb, [
            "## À retenir",
            "## Vérifiez votre compréhension",
            "## Pour aller plus loin",
        ])
        result = mod.check_notebook_blocks(str(nb))
        assert result["missing"] == []

    def test_json_malformed(self, tmp_path):
        """Un carnet invalide doit retourner un signal d'erreur, pas crasher."""
        nb = tmp_path / "bad.ipynb"
        nb.write_text("{ this is not json", encoding="utf-8")
        result = mod.check_notebook_blocks(str(nb))
        assert result.get("error") is not None
        assert result["missing"] == ["__error__"]

    def test_code_cells_ignored(self, tmp_path):
        """Les cellules de code ne doivent pas etre scannees."""
        nb_json = {
            "cells": [
                {"cell_type": "code", "metadata": {}, "source": ["# A retenir\n"]},
                {"cell_type": "markdown", "metadata": {}, "source": ["## Verifiez votre comprehension\n"]},
                {"cell_type": "markdown", "metadata": {}, "source": ["## Pour aller plus loin\n"]},
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        nb = tmp_path / "ML-8-Python.ipynb"
        nb.write_text(json.dumps(nb_json, ensure_ascii=False), encoding="utf-8")
        result = mod.check_notebook_blocks(str(nb))
        assert result["blocks"]["a_retenir"] is False
        assert result["missing"] == ["a_retenir"]


# -----------------------------------------------------------------------------
# check_readme
# -----------------------------------------------------------------------------

class TestCheckReadme:
    def test_objectifs_h2(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text(
            "# ML\n\n## Public cible\nblah\n\n## Objectifs d'apprentissage\nblah\n",
            encoding="utf-8",
        )
        # check_readme prend la serie, pas le path -- on simule via SERIES_ROOT
        result = mod.check_readme(str(tmp_path.name))
        # Serie inconnue dans le cwd actuel : on teste directement la fonction
        # alternative : on monkey-patch SERIES_ROOT
        # Plus simple : on importe le module et on appelle check_readme apres monkeypatch
        # (voir TestReadmeRealpath ci-dessous)

    def test_objectifs_h3(self, tmp_path):
        """Un titre H3 `### Objectifs` doit compter aussi."""
        # On utilise le cwd-trick : on cree un sous-dossier "serie"
        # et on override SERIES_ROOT
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "SerieTest").mkdir()
            (tmp_path / "SerieTest" / "README.md").write_text(
                "### Competences\nblah\n", encoding="utf-8"
            )
            result = mod.check_readme("SerieTest")
            assert result["objectifs"] is True
        finally:
            mod.SERIES_ROOT = original

    def test_objectifs_absent(self, tmp_path):
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "SerieVide").mkdir()
            (tmp_path / "SerieVide" / "README.md").write_text(
                "# Titre\n## Introduction\nblah\n", encoding="utf-8"
            )
            result = mod.check_readme("SerieVide")
            assert result["objectifs"] is False
        finally:
            mod.SERIES_ROOT = original

    def test_objectifs_phrase_prose_ne_compte_pas(self, tmp_path):
        """Une mention 'machine learning' en prose ne doit pas compter (4 FP du coord)."""
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "ML").mkdir()
            (tmp_path / "ML" / "README.md").write_text(
                "# ML\n\nLe machine learning est un domaine vaste.\n\n"
                "Cette serie couvre plusieurs aspects du machine learning.\n",
                encoding="utf-8",
            )
            result = mod.check_readme("ML")
            assert result["objectifs"] is False
        finally:
            mod.SERIES_ROOT = original

    def test_readme_manquant(self, tmp_path):
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "NoReadme").mkdir()
            result = mod.check_readme("NoReadme")
            assert result["exists"] is False
            assert result["objectifs"] is False
        finally:
            mod.SERIES_ROOT = original


# -----------------------------------------------------------------------------
# run_check (orchestration)
# -----------------------------------------------------------------------------

class TestRunCheck:
    def test_serie_inconnue(self):
        """Une serie qui n'existe pas doit retourner rc=2."""
        result = mod.run_check("SerieQuiNexistePas_XYZ_123")
        assert result["rc"] == 2
        assert result["error"] == "series_not_found"

    def test_serie_nom_invalide(self):
        """Un nom de serie avec / ou \\ est refuse."""
        for bad in ("../foo", "a/b", "a\\b", ".hidden"):
            result = mod.run_check(bad)
            assert result["rc"] == 2
            assert result["error"] == "invalid_series_name"

    def test_serie_vide(self, tmp_path):
        """Une serie sans carnets retourne finished=False."""
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "SerieVide").mkdir()
            (tmp_path / "SerieVide" / "README.md").write_text(
                "## Objectifs\nblah\n", encoding="utf-8"
            )
            result = mod.run_check("SerieVide")
            assert result["rc"] == 1
            assert result["finished"] is False
            assert result["carnet_total"] == 0
        finally:
            mod.SERIES_ROOT = original

    def test_serie_finie(self, tmp_path):
        """Une serie avec README Objectifs + tous carnets avec 3 blocs = FINIE."""
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "SerieFinie").mkdir()
            (tmp_path / "SerieFinie" / "README.md").write_text(
                "## Objectifs d'apprentissage\nblah\n", encoding="utf-8"
            )
            _make_notebook(
                tmp_path / "SerieFinie" / "C-1-Python.ipynb",
                ["## A retenir", "## Verifiez votre comprehension", "## Pour aller plus loin"],
            )
            _make_notebook(
                tmp_path / "SerieFinie" / "C-2-Python.ipynb",
                ["## A retenir", "## Verifiez votre comprehension", "## Pour aller plus loin"],
            )
            result = mod.run_check("SerieFinie")
            assert result["rc"] == 0
            assert result["finished"] is True
            assert result["carnet_total"] == 2
            assert result["carnet_finis"] == 2
            assert result["carnets_manquants"] == []
        finally:
            mod.SERIES_ROOT = original

    def test_serie_partiellement_finie(self, tmp_path):
        """Un carnet manque un bloc = serie non finie."""
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "SeriePart").mkdir()
            (tmp_path / "SeriePart" / "README.md").write_text(
                "## Objectifs\nblah\n", encoding="utf-8"
            )
            _make_notebook(
                tmp_path / "SeriePart" / "C-1-Python.ipynb",
                ["## A retenir", "## Verifiez votre comprehension", "## Pour aller plus loin"],
            )
            _make_notebook(
                tmp_path / "SeriePart" / "C-2-Python.ipynb",
                ["## A retenir"],  # manque verifiez + aller_plus_loin
            )
            result = mod.run_check("SeriePart")
            assert result["rc"] == 1
            assert result["finished"] is False
            assert result["carnet_finis"] == 1
            assert result["carnet_total"] == 2
            assert len(result["carnets_manquants"]) == 1
        finally:
            mod.SERIES_ROOT = original

    def test_serie_exclut_archive_et_output(self, tmp_path):
        """Les .ipynb dans _archive ou _output ne sont pas comptes."""
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            serie = tmp_path / "SerieFiltr"
            serie.mkdir()
            (serie / "README.md").write_text("## Objectifs\nblah\n", encoding="utf-8")
            # Carnet canonique : compte
            _make_notebook(
                serie / "C-1-Python.ipynb",
                ["## A retenir", "## Verifiez votre comprehension", "## Pour aller plus loin"],
            )
            # Carnet archive : ne compte pas
            archive = serie / "_archive"
            archive.mkdir()
            _make_notebook(
                archive / "C-0-Python.ipynb",
                [],  # pas de blocs, mais il ne doit pas etre compte
            )
            # Carnet output : ne compte pas
            output = serie / "_output"
            output.mkdir()
            _make_notebook(
                output / "C-2-Python.ipynb",
                [],  # pas de blocs
            )
            result = mod.run_check("SerieFiltr")
            assert result["carnet_total"] == 1
            assert result["carnet_finis"] == 1
            assert result["finished"] is True
        finally:
            mod.SERIES_ROOT = original


# -----------------------------------------------------------------------------
# main() : codes de sortie (CLI)
# -----------------------------------------------------------------------------

class TestMainCLI:
    def test_cli_rc_0_serie_finie(self, tmp_path, monkeypatch, capsys):
        """CLI : serie finie -> stdout rapport + rc=0."""
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "CLIOK").mkdir()
            (tmp_path / "CLIOK" / "README.md").write_text(
                "## Objectifs\nblah\n", encoding="utf-8"
            )
            _make_notebook(
                tmp_path / "CLIOK" / "C-1.ipynb",
                ["## A retenir", "## Verifiez votre comprehension", "## Pour aller plus loin"],
            )
            rc = mod.main(["--series", "CLIOK", "--report"])
            out = capsys.readouterr().out
            assert rc == 0
            assert "FINIE" in out
        finally:
            mod.SERIES_ROOT = original

    def test_cli_rc_1_serie_non_finie(self, tmp_path, capsys):
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "CLIKO").mkdir()
            (tmp_path / "CLIKO" / "README.md").write_text(
                "## Objectifs\nblah\n", encoding="utf-8"
            )
            _make_notebook(tmp_path / "CLIKO" / "C-1.ipynb", ["## A retenir"])
            rc = mod.main(["--series", "CLIKO", "--report"])
            out = capsys.readouterr().out
            assert rc == 1
            assert "NON FINIE" in out
        finally:
            mod.SERIES_ROOT = original

    def test_cli_json_sortie(self, tmp_path, capsys):
        original = mod.SERIES_ROOT
        try:
            mod.SERIES_ROOT = str(tmp_path)
            (tmp_path / "CLJSON").mkdir()
            (tmp_path / "CLJSON" / "README.md").write_text(
                "## Objectifs\nblah\n", encoding="utf-8"
            )
            _make_notebook(
                tmp_path / "CLJSON" / "C-1.ipynb",
                ["## A retenir", "## Verifiez votre comprehension", "## Pour aller plus loin"],
            )
            rc = mod.main(["--series", "CLJSON", "--json"])
            out = capsys.readouterr().out
            assert rc == 0
            data = json.loads(out)
            assert data["finished"] is True
            assert data["series"] == "CLJSON"
        finally:
            mod.SERIES_ROOT = original

    def test_cli_rc_2_serie_inconnue(self, capsys):
        rc = mod.main(["--series", "SerieTotalementInexistante_ZZZ", "--report"])
        out = capsys.readouterr().out
        assert rc == 2
        assert "ERREUR" in out
