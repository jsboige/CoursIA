"""Tests for scripts/notebook_tools/pyodide_eligibility.py — critere et classification.

Quatre comportements a verrouiller, chacun ne d'une correction mesuree sur le
census initial :

1. la famille Python se lit sur ``language_info.name`` d'abord (le nom du
   ``kernelspec`` nomme un environnement, pas une langue : 94 carnets Python
   etaient exclus par le test sur le nom du noyau) ;
2. un paquet local (dossier a ``__init__.py``) est un module local embarquable,
   pas un import absent ;
3. le cache des sondes PyPI rend la colonne « roues pures » reproductible hors
   reseau : sans sonde, aucun acces reseau n'est fait ;
4. la **suffisance** au bundle (#27583) : le bundle publie des fichiers et
   n'installe rien, donc une roue pure que le carnet n'installe pas lui-meme,
   un module d'une autre serie, ou une dependance absente de la distribution
   ne sont pas fournis -- le carnet est alors refuse.

Issue #27549, alignement #27583.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from pyodide_eligibility import (  # noqa: E402
    analyse_notebook,
    is_python_notebook,
)
from pyodide_eligibility_report import sanitize_verdict  # noqa: E402

STDLIB = set(sys.stdlib_module_names)


def _nb(cells_sources, kernel="python3", language="python"):
    """Notebook minimal : cellules de code + metadonnees de noyau."""
    return {
        "cells": [
            {"cell_type": "code", "source": [src], "metadata": {}, "outputs": [],
             "execution_count": 1}
            for src in cells_sources
        ],
        "metadata": {
            "kernelspec": {"name": kernel, "display_name": kernel},
            "language_info": {"name": language},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write(root: Path, rel: str, nb: dict) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _verdict(root: Path, rel: str, nb: dict, pyodide=None, cache=None, probe=False):
    _write(root, rel, nb)
    return analyse_notebook(root, rel, pyodide or {}, cache or {}, STDLIB, probe)


class TestFamillePython:
    """La famille Python se lit sur la langue declaree, pas le nom d'env."""

    def test_noyau_non_python_mais_langue_python(self, tmp_path):
        """`coursia-ml-training` est un noyau Python : le carnet compte."""
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["print(1)"], kernel="coursia-ml-training"))
        assert is_python_notebook(v) is True

    def test_noyau_python_sans_langue_declaree(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["print(1)"], language=""))
        assert is_python_notebook(v) is True

    def test_langue_non_python_exclue(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["print(1)"], kernel="gamma", language="c#"))
        assert is_python_notebook(v) is False

    def test_aucun_marqueur_exclu_sans_supposition(self, tmp_path):
        """Ni langue ni noyau : le census ne suppose pas Python par defaut."""
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["print(1)"], kernel="", language=""))
        assert is_python_notebook(v) is False


class TestPaquetLocal:
    """Un dossier a ``__init__.py`` a cote du carnet est embarquable."""

    def test_paquet_local_compte_comme_module_local(self, tmp_path):
        pkg = tmp_path / "MyIA.AI.Notebooks" / "S" / "monoutil"
        pkg.mkdir(parents=True)
        (pkg / "__init__.py").write_text("", encoding="utf-8")
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import monoutil"]))
        assert v.eligible is True
        assert v.local_count == 1
        assert "import_absent" not in v.motifs

    def test_module_hors_serie_signale_sans_refuser(self, tmp_path):
        """Un module du depot hors serie est signale, puis refuse (suffisance).

        Le bundle ne livre que la serie du carnet : un module d'une autre
        serie n'est pas fourni -- l'alignement (#27583) refuse donc le
        carnet, sur le motif `suffisance`, en gardant la trace du module
        signale comme hors serie.
        """
        helper = tmp_path / "Outils" / "helper.py"
        helper.parent.mkdir(parents=True)
        helper.write_text("", encoding="utf-8")
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import helper"]))
        assert v.local_hors_serie == ["helper"]
        assert "suffisance" in v.motifs
        assert v.eligible is False
        assert [p["classe"] for p in v.to_dict()["problemes"]] == ["hors_serie"]


class TestCriteres:
    def test_eligible_stdlib_seule(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import json\nprint(json.dumps({}))"]))
        assert v.eligible is True
        assert v.motifs == []

    def test_gpu_refuse(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import torch"]))
        assert v.eligible is False
        assert "gpu" in v.motifs
        assert v.gpu_detail == ["torch"]

    def test_cle_api_refusee(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import os\nk = os.getenv('OPENAI_API_KEY')"]))
        assert v.eligible is False
        assert "cle" in v.motifs

    def test_url_citee_sans_appel_ne_refuse_pas(self, tmp_path):
        """Une URL de documentation citee n'est pas un service reseau."""
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(['"""Voir https://docs.python.org/3/library/json.html"""']))
        assert "reseau" not in v.motifs

    def test_url_appellee_refusee(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import requests\nr = requests.get('https://api.exemple.fr/v1')"]))
        assert v.eligible is False
        assert "reseau" in v.motifs

    def test_import_absent_sans_sonde_ni_reseau(self, tmp_path):
        """Sans --probe-pypi, un paquet inconnu est refuse sans acces reseau."""
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import paquetquinexistepas"]), probe=False)
        assert v.eligible is False
        assert v.missing_imports == ["paquetquinexistepas"]

    def test_roue_pure_connue_par_le_cache(self, tmp_path):
        """Le cache versionne suffit : aucune sonde reseau n'est faite.

        La roue pure reste signalee comme telle, mais le carnet est refuse :
        le bundle ne l'installe pas, et le carnet ne l'installe pas
        lui-meme (alignement #27583, motif `suffisance`).
        """
        cache = {"paquetroue": {"pure_wheel": True, "version": "1.0"}}
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import paquetroue"]), cache=cache, probe=False)
        assert v.pure_wheels == ["paquetroue"]
        assert "suffisance" in v.motifs
        assert v.eligible is False

    def test_le_carnet_installe_la_roue_pure(self, tmp_path):
        """Une roue pure que le carnet installe lui-meme est fournie."""
        cache = {"paquetroue": {"pure_wheel": True, "version": "1.0"}}
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import micropip\nmicropip.install('paquetroue')",
                          "import paquetroue"]), pyodide={"micropip": "0.10.0"},
                     cache=cache, probe=False)
        assert v.eligible is True
        assert v.motifs == []


class TestNePasPublierLesNoms:
    def test_sanitize_masque_les_noms(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import os\nk = os.getenv('OPENAI_API_KEY')"]))
        data = sanitize_verdict(v.to_dict())
        assert data["key_detail"] == []
        assert data["cle_n"] == 1

    def test_sanitize_avec_detail_cle_explicite(self, tmp_path):
        v = _verdict(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                     _nb(["import os\nk = os.getenv('OPENAI_API_KEY')"]))
        data = sanitize_verdict(v.to_dict(), with_key_names=True)
        assert data["key_detail"] == ["OPENAI_API_KEY"]
