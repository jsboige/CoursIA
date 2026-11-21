"""Tests for scripts/notebook_tools/pyodide_suffisance.py -- suffisance du bundle.

Le bundle JupyterLite publie des **fichiers** et n'installe rien. Un import
n'est donc satisfait que dans trois cas : la distribution (verrou Pyodide), le
carnet qui l'installe lui-meme, ou un module de la serie livre avec le carnet.
Cette suite verrouille les trois, et les trois classes d'ecart qui en
resultent.

Les tests sont ecrits sur des carnets minimaux : ils verrouillent la
**semantique**, pas les chiffres du census.

Issue #27583.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from pyodide_eligibility import analyse_notebook  # noqa: E402
from pyodide_suffisance import (  # noqa: E402
    CLASSES,
    normalise,
    paquets_installes_par_le_carnet,
    suffisance_carnet,
)

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


def _module(root: Path, rel: str, contenu: str) -> None:
    """Ecrit un module Python dans le depot de test."""
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contenu, encoding="utf-8")


#: Le verrou minimal des tests : `micropip` est un outil du **runtime**
#: Pyodide (il est dans le lock commite), pas un paquet a installer.
LOCK_MINIMAL = {"micropip": "0.10.0"}


def _suffisance(root: Path, rel: str, nb: dict, pyodide=None, roue_pure=False):
    """La suffisance d'un carnet minimal, telle que le critere la demande."""
    _write(root, rel, nb)
    return suffisance_carnet(
        root, rel, pyodide if pyodide is not None else LOCK_MINIMAL, STDLIB,
        sources=nb["cells"][0]["source"] + [
            "".join(c["source"]) for c in nb["cells"][1:]],
        est_roie_pure=lambda _pack: roue_pure)


def _classes(suff) -> set:
    return {p.classe for p in suff.problemes}


class TestLesTroisVoiesDeSatisfaction:
    """Les trois cas ou un import est fourni au carnet dans le bundle."""

    def test_distribution(self, tmp_path):
        """Un paquet du verrou Pyodide est fourni : rien a signaler."""
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["import numpy"]), pyodide={"numpy": "2.0"})
        assert suff.problemes == []

    def test_le_carnet_installe_lui_meme(self, tmp_path):
        """`micropip.install` rend le paquet disponible a l'execution."""
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["import micropip\nmicropip.install('pandas')", "import pandas"]))
        assert suff.problemes == []
        assert "pandas" in suff.installs

    def test_pip_magique_depuis_une_cellule(self, tmp_path):
        """`%pip install` et `!pip install` sont des installations aussi."""
        assert "scikit_learn" in paquets_installes_par_le_carnet(
            ["%pip install scikit-learn"])
        assert "requests" in paquets_installes_par_le_carnet(
            ["!pip install requests"])
        assert "flask" in paquets_installes_par_le_carnet(
            ["%pip install flask==3.0"])

    def test_module_de_la_serie_satisfait(self, tmp_path):
        """Un module livre avec le carnet, dont les imports sont satisfaits."""
        _module(tmp_path, "MyIA.AI.Notebooks/S/monoutil.py",
                 "import json\n")
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["import monoutil"]))
        assert suff.problemes == []
        assert [m[0] for m in suff.modules] == ["monoutil"]


class TestLesClassesDEcart:
    """Les trois classes d'ecart entre le critere et ce que le bundle livre."""

    def test_dependance_locale(self, tmp_path):
        """Un module de la serie a une dependance absente de la distribution."""
        _module(tmp_path, "MyIA.AI.Notebooks/S/monoutil.py",
                 "import dowhy_iv_organs\n")
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["import monoutil"]))
        assert _classes(suff) == {"dependance_locale"}
        assert "dowhy_iv_organs" in suff.problemes[0].detail

    def test_hors_serie(self, tmp_path):
        """Un module d'une autre serie n'est pas livre par le bundle."""
        _module(tmp_path, "Outils/helper.py", "x = 1\n")
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["import helper"]))
        assert _classes(suff) == {"hors_serie"}

    def test_absent_distribution(self, tmp_path):
        """Une roue pure que le carnet n'installe pas n'est pas fournie."""
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["import pandas"]), roue_pure=True)
        assert _classes(suff) == {"absent_distribution"}

    def test_une_rooue_pure_non_installee_est_refusee(self, tmp_path):
        """Le carnet qui installe la roue ne subit pas l'ecart."""
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["import micropip\nmicropip.install('pandas')", "import pandas"]),
            roue_pure=True)
        assert suff.problemes == []


class TestNormalisation:
    def test_pyPI_et_python(self):
        assert normalise("scikit-learn") == "scikit_learn"

    def test_le_prefixe_pypi_ne_compte_pas_comme_un_import(self, tmp_path):
        """`from sklearn.model_selection import ...` donne `sklearn`."""
        suff = _suffisance(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
            _nb(["from sklearn.model_selection import train_test_split"]))
        assert suff.problemes  # pas de lock, pas d'installation : un ecart
        assert suff.problemes[0].chaine == ("sklearn.model_selection",)
        assert suff.problemes[0].detail.startswith("sklearn")


class TestCablageDuCritere:
    """Le critere porte la suffisance : un verdict et un motif."""

    def test_le_verdict_signale_les_problemes(self, tmp_path):
        """Une roue pure que le carnet n'installe pas : refus `suffisance`."""
        _write(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
               _nb(["import pandas"]))
        v = analyse_notebook(
            tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb", LOCK_MINIMAL,
            {"pandas": {"pure_wheel": True, "version": "2.2"}}, STDLIB, False)
        assert "suffisance" in v.motifs
        assert "import_absent" not in v.motifs
        assert v.eligible is False
        assert [p["classe"] for p in v.to_dict()["problemes"]] == ["absent_distribution"]

    def test_un_carnet_satisfait_neporte_pas_le_motif(self, tmp_path):
        _write(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
               _nb(["import json\nprint(json.dumps({}))"]))
        v = analyse_notebook(tmp_path, "MyIA.AI.Notebooks/S/Test-01.ipynb",
                             LOCK_MINIMAL, {}, STDLIB, False)
        assert v.motifs == []
        assert v.eligible is True

    def test_les_classes_sont_fermees(self):
        assert CLASSES == ("dependance_locale", "hors_serie", "absent_distribution")


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
