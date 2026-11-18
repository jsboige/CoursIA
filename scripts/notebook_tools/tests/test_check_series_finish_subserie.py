"""Tests de la ligne 3 de #26973 : `check_series_finish.py` accepte une
**sous-serie** `A/B`, confinee sous `SERIES_ROOT`.

Le depot compte des sous-series reelles (`MyIA.AI.Notebooks/CaseStudies/
Diagnostic-Medical`, ...) ; l'organe les refusait tous, faute de pouvoir les
nommer : la verification de finition etait structurellement impossible sur une
sous-serie.

Ce qui est verifie :

- une sous-serie `A/B` est verifiee comme une serie ;
- une serie plate continue de l'etre (non-regression) ;
- le confinement tient : `..`, chemin absolu, lettre de lecteur, segment vide
  et segment cache sont refuses ;
- une sous-serie sans README n'est pas « finie » (verdict honnete, pas un
  crash) ;
- une sous-serie inexistante donne `series_not_found` (et non un verdict vide).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))

import check_series_finish as csf  # noqa: E402


CANONICAL_BLOCKS = [
    "## A retenir",
    "## Verifiez votre comprehension",
    "## Pour aller plus loin",
]


def _write_nb(path: Path, blocks: list[str] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": [
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": [b + "\n" for b in (blocks or CANONICAL_BLOCKS)],
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


def _racine(tmp_path: Path, monkeypatch) -> Path:
    racine = tmp_path / "MyIA.AI.Notebooks"
    racine.mkdir(parents=True, exist_ok=True)
    monkeypatch.setattr(csf, "SERIES_ROOT", str(racine))
    return racine


def _sous_serie(racine: Path, nom: str, avec_readme: bool = True) -> None:
    dossier = racine / nom
    _write_nb(dossier / "01-carnet.ipynb")
    if avec_readme:
        (dossier / "README.md").write_text(
            "# Serie\n\n## Objectifs d'apprentissage\n\n- un objectif\n",
            encoding="utf-8",
        )


# ---------------------------------------------------------------------------
# la sous-serie est acceptee
# ---------------------------------------------------------------------------

def test_une_sous_serie_est_verifiee_comme_une_serie(tmp_path, monkeypatch):
    racine = _racine(tmp_path, monkeypatch)
    _sous_serie(racine, "A/B")
    verdict = csf.run_check("A/B")
    assert verdict.get("error") is None
    assert verdict["rc"] == 0
    assert verdict["finished"] is True
    assert verdict["carnet_total"] == 1


def test_une_serie_plate_reste_acceptee(tmp_path, monkeypatch):
    racine = _racine(tmp_path, monkeypatch)
    _sous_serie(racine, "ML")
    verdict = csf.run_check("ML")
    assert verdict.get("error") is None
    assert verdict["rc"] == 0


def test_une_sous_serie_sans_readme_nest_pas_finie(tmp_path, monkeypatch):
    racine = _racine(tmp_path, monkeypatch)
    _sous_serie(racine, "A/B", avec_readme=False)
    verdict = csf.run_check("A/B")
    assert verdict.get("error") is None
    assert verdict["rc"] == 1
    assert verdict["finished"] is False


def test_une_sous_serie_inexistante_donne_series_not_found(tmp_path, monkeypatch):
    _racine(tmp_path, monkeypatch)
    verdict = csf.run_check("A/Pas-la")
    assert verdict["error"] == "series_not_found"
    assert verdict["rc"] == 2


# ---------------------------------------------------------------------------
# le confinement
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "nom",
    [
        "A/../B",        # remontee d'arborescence
        "../B",          # sortie de la racine
        "/etc",          # chemin absolu
        "C:/Windows",    # lettre de lecteur
        "A//B",          # segment vide
        "A/./B",         # segment « . »
        ".git",          # segment cache
        "A/.ipynb_checkpoints",
    ],
)
def test_un_nom_qui_sort_de_la_racine_est_refuse(nom, tmp_path, monkeypatch):
    racine = _racine(tmp_path, monkeypatch)
    _sous_serie(racine, "A/B")
    verdict = csf.run_check(nom)
    assert verdict["error"] == "invalid_series_name"
    assert verdict["rc"] == 2


def test_un_nom_vide_est_refuse(tmp_path, monkeypatch):
    _racine(tmp_path, monkeypatch)
    verdict = csf.run_check("")
    assert verdict["error"] == "invalid_series_name"


def test_le_normaliseur_rend_la_forme_posix():
    assert csf.normalize_series_path("A\\B") == "A/B"
    assert csf.normalize_series_path(" A/B ") == "A/B"
    assert csf.normalize_series_path("A/../B") is None


def test_le_refus_textuel_de_remontee_et_de_lecteur_est_tue_par_test():
    """La PREMIERE couche de defense a son propre test qui la tue SEUL.

    Le refus de `..` et de la lettre de lecteur est TEXTUEL : il vit dans
    `normalize_series_path`. Sans ces assertions, retirer ces deux gardes
    laisse la suite verte -- la defense RESOLUE (`_confine_sous_series_root`)
    couvre alors seule le cas, et le mutant passe. Ce test ferme la premiere
    couche, pas seulement la seconde.
    """
    assert csf.normalize_series_path("../x") is None
    assert csf.normalize_series_path("C:/x") is None


def test_une_serie_plate_ne_bascule_pas_en_sous_serie():
    """Une serie simple ne doit pas devenir un chemin de deux segments."""
    assert csf.normalize_series_path("ML") == "ML"
    assert "/" not in csf.normalize_series_path("ML")


def test_un_lien_symbolique_hors_de_la_racine_est_refuse(tmp_path, monkeypatch):
    """Defense en profondeur : un lien symbolique vers l'exterieur est refuse.

    La normalisation refuse deja `..` et les chemins absolus, mais un lien
    symbolique dans l'arbre pourrait designer un dossier hors de
    `SERIES_ROOT`. Le controle est fait sur le chemin **resolu**.

    Le test est **sauté** sur un poste ou la creation de lien symbolique est
    reservee (Windows sans mode developpeur) : l'absence de symlink n'est
    pas une preuve de confinement.
    """
    import os

    racine = _racine(tmp_path, monkeypatch)
    exterieur = tmp_path / "ailleurs"
    exterieur.mkdir()
    try:
        os.symlink(str(exterieur), str(racine / "Lien"), target_is_directory=True)
    except OSError as exc:  # Windows sans privilege de lien symbolique
        pytest.skip("creation de lien symbolique refusee sur ce poste : {}".format(exc))
    verdict = csf.run_check("Lien")
    assert verdict["error"] == "invalid_series_name"
    assert verdict["rc"] == 2


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
