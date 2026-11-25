#!/usr/bin/env python3
"""Tests du generateur de la table « Statut de maturite » (#17545).

Le defaut que ce fichier surveille : la table etait une copie manuelle dont
AUCUNE colonne ne suivait une unite stable (sur 18 lignes echantillonnees,
la colonne « Cellules » matchait `cells_total` 5 fois, `cells_code` 5 fois).
Le generateur en fait l'image generee de la table de description, avec deux
colonnes mesurees (`Cellules (code)`, `Exercices`) et une colonne Statut
preservere verbatim.

Usage :
    python -m pytest scripts/lean/tests/test_lean_series_maturity.py -q
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]


def _load_module():
    """Charge l'organe par son chemin (le script vit hors du paquet)."""
    path = REPO_ROOT / "scripts" / "lean" / "lean_series_maturity.py"
    spec = importlib.util.spec_from_file_location("lean_series_maturity", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["lean_series_maturity"] = module
    spec.loader.exec_module(module)
    return module


mod = _load_module()


def _nb(cells_code: int, exercise_headings: list[str], kernel="python3"):
    """Un carnet synthetique : N cellules code + des headings d'exercice."""
    cells = [{"cell_type": "code", "source": ["x = 1"], "outputs": [],
              "execution_count": 1} for _ in range(cells_code)]
    for h in exercise_headings:
        cells.append({"cell_type": "markdown",
                      "source": ["%s titre\n\n prose" % h]})
    cells.append({"cell_type": "markdown", "source": ["## Intro"]})
    return {"cells": cells,
            "metadata": {"kernelspec": {"name": kernel}}}


@pytest.fixture()
def serie(tmp_path):
    """Un README fixture : description a 3 carnets + maturite a 1 ligne."""
    (tmp_path / "a.ipynb").write_text(json.dumps(_nb(4, ["### Exercice 1"])),
                                      encoding="utf-8")
    (tmp_path / "b.ipynb").write_text(
        json.dumps(_nb(7, ["### Exercice 1", "#### Exercice 2"],
                      kernel="lean4-wsl")), encoding="utf-8")
    (tmp_path / "c_output.ipynb").write_text(json.dumps(_nb(99, [])),
                                             encoding="utf-8")
    (tmp_path / "c.ipynb").write_text(json.dumps(_nb(2, [])), encoding="utf-8")
    readme = tmp_path / "README.md"
    readme.write_text(
        "# Serie\n\n"
        "| # | Carnet | Description | Duree |\n"
        "|---|--------|-------------|-------|\n"
        "| 1 | [a](a.ipynb) | premier | 10 min |\n"
        "| 2 | [b](b.ipynb) | deuxieme | 10 min |\n"
        "| 3 | [c](c_output.ipynb) et [vrai c](c.ipynb) | troisieme | 10 min |\n"
        "\n## Statut de maturité\n\n"
        "| # | Notebook | Cellules | Exercices | Solutions | Statut |\n"
        "|---|----------|----------|-----------|-----------|--------|\n"
        "| 1 | a | ~99 | 9 | 9 | **COMPLET** |\n"
        "\nProse sous la table.\n", encoding="utf-8")
    return readme


def test_la_description_ne_se_reparse_pas_elle_meme(serie):
    """Regression : la table regeneree a la meme forme de ligne que la
    description -- sans borne, le parse doublait l'image a chaque passage
    (mesure : 170 lignes attendues au 2e --check)."""
    lines = serie.read_text(encoding="utf-8").splitlines()
    # premier passage : regenere
    mod.PAGE = serie
    assert mod.main(["--write"]) == 0
    # le parse de la page REGENEREE ne doit toujours voir que 3 carnets
    assert len(mod.parse_description(
        serie.read_text(encoding="utf-8").splitlines())) == 3


def test_la_description_ignore_les_artefacts_d_execution(serie):
    rows = mod.parse_description(serie.read_text(encoding="utf-8")
                                 .splitlines())
    assert [r[0] for r in rows] == ["1", "2", "3"]
    # le premier lien de la ligne 3 est c_output.ipynb (artefact) : la ligne
    # doit retomber sur le lien reel suivant, pas disparaitre.
    assert rows[2] == ("3", "vrai c", "c.ipynb")


def test_write_puis_check_vert(serie, monkeypatch):
    monkeypatch.setattr(mod, "PAGE", serie)
    rc_check = mod.main(["--check"])
    assert rc_check == 1, "la table d'origine (~99/9/9) doit diverger"
    assert mod.main(["--write"]) == 0
    assert mod.main(["--check"]) == 0


def test_les_mesures_et_le_statut_herite(serie, monkeypatch):
    monkeypatch.setattr(mod, "PAGE", serie)
    mod.main(["--write"])
    body = serie.read_text(encoding="utf-8").splitlines()
    start = next(i for i, l in enumerate(body)
                 if l.strip() == mod.SECTION_HEADING)
    table = [l for l in body[start:] if l.startswith("|")]
    # statut editorial preserve verbatim pour l'id existant
    assert any(l == "| 1 | [a](a.ipynb) | 4 | 1 | **COMPLET** |"
               for l in table), table
    # nouvel id : statut NOUVEAU avec le kernel MESURE
    assert any(l.startswith("| 2 | [b](b.ipynb) | 7 | 2 | **NOUVEAU** "
                           "(kernel `lean4-wsl`) |") for l in table), table


def test_carnet_illisible_rien_n_est_ecrit(serie, monkeypatch):
    """Un lien mort rend la mesure impossible : rc=2, page intacte."""
    ligne = serie.read_text(encoding="utf-8")
    serie.write_text(ligne.replace("[b](b.ipynb)", "[b](absent.ipynb)"),
                     encoding="utf-8")
    avant = serie.read_text(encoding="utf-8")
    monkeypatch.setattr(mod, "PAGE", serie)
    assert mod.main(["--check"]) == mod.UNMEASURABLE_RC
    assert mod.main(["--write"]) == mod.UNMEASURABLE_RC
    assert serie.read_text(encoding="utf-8") == avant


def test_le_compte_d_exercices_ne_voit_que_le_markdown(serie, monkeypatch):
    """Un « Exercice » dans du code n'est pas un exercice."""
    monkeypatch.setattr(mod, "PAGE", serie)
    nb = _nb(1, ["### Exercice 1"])
    nb["cells"][0]["source"] = ["# Exercice en commentaire"]
    (serie.parent / "d.ipynb").write_text(json.dumps(nb), encoding="utf-8")
    m = mod._measure("d", "d", "d.ipynb")
    assert m.exercises == 1  # le heading markdown, pas le commentaire


def test_la_veritable_table_du_depot_est_conforme():
    """Controle positif sur le vrai README : le contrat du generateur."""
    assert mod.PAGE.exists()
    rc = mod.main(["--check"])
    assert rc == 0, ("la table commitee doit etre l'image de la table de "
                     "description -- regenerer par --write si ce test rougit")
