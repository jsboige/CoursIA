"""Tests de l'organe des boutons de lancement (pli 2.3, #27551).

L'organe est verifie sur un depot et un site **synthetiques** : aucune page
reelle du site n'est necessaire, et chaque condition d'eligibilite est
exercee dans les deux sens (presente -> bouton emis, absente -> bouton
absent).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import launch_buttons as lb  # noqa: E402

CARNET_PYTHON = {
    "cells": [],
    "metadata": {
        "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
        "language_info": {"name": "python"},
    },
    "nbformat": 4,
    "nbformat_minor": 5,
}

CARNET_CSHARP = {
    "cells": [],
    "metadata": {
        "kernelspec": {"display_name": ".NET (C#)", "language": "csharp", "name": ".net-csharp"},
        "language_info": {"name": "csharp"},
    },
    "nbformat": 4,
    "nbformat_minor": 5,
}

PAGE_NOTEBOOK = """<!DOCTYPE html>
<html><head><title>Carnet</title></head>
<body class="page">
<div id="quarto-document-content" class="content">
<main class="quarto-document">
<h1 class="title">Carnet</h1>
</main>
</div>
</body></html>
"""

PAGE_README = """<!DOCTYPE html>
<html><head><title>Serie</title></head>
<body class="page">
<div id="quarto-document-content" class="content">
<main class="quarto-document"><h1 class="title">Serie</h1></main>
</div>
</body></html>
"""


def _ecrire_carnet(racine: Path, rel: str, contenu: dict) -> Path:
    chemin = racine / rel
    chemin.parent.mkdir(parents=True, exist_ok=True)
    chemin.write_text(json.dumps(contenu), encoding="utf-8")
    return chemin


def _ecrire_page(site: Path, rel: str, contenu: str) -> Path:
    chemin = site / rel
    chemin.parent.mkdir(parents=True, exist_ok=True)
    chemin.write_text(contenu, encoding="utf-8")
    return chemin


def _depot(tmp_path: Path, avec_devcontainer: bool = True) -> Path:
    racine = tmp_path / "depot"
    racine.mkdir()
    if avec_devcontainer:
        (racine / ".devcontainer").mkdir()
        (racine / lb.CHEMIN_DEVCONTAINER).write_text("{}", encoding="utf-8")
    return racine


def _manifeste(entrees: dict) -> dict:
    return {"carnets": [{"chemin": rel, "lab": lab} for rel, lab in entrees.items()]}


# --------------------------------------------------------------------------
# Le noyau
# --------------------------------------------------------------------------

def test_langage_du_carnet_python(tmp_path):
    chemin = _ecrire_carnet(tmp_path, "A.ipynb", CARNET_PYTHON)
    langage = lb.langage_du_carnet(chemin)
    assert langage.language == "python"
    assert lb.est_python(langage)


def test_langage_du_carnet_csharp(tmp_path):
    chemin = _ecrire_carnet(tmp_path, "A.ipynb", CARNET_CSHARP)
    langage = lb.langage_du_carnet(chemin)
    assert langage.language == "csharp"
    assert not lb.est_python(langage)


def test_langage_illisible_ne_ment_pas(tmp_path):
    chemin = tmp_path / "A.ipynb"
    chemin.write_text("pas du json", encoding="utf-8")
    assert lb.langage_du_carnet(chemin) == lb.Langage()


def test_le_nom_du_noyau_ne_decide_pas_seul():
    """Un noyau dont le nom ne commence pas par « python » peut porter Python.

    C'est la regle du critere (pli 2.1) : ``language_info.name`` fait foi, le
    nom du kernelspec n'est qu'un repli.
    """
    assert lb.est_python(lb.Langage(language="python", kernel="ict-py313"))
    assert lb.est_python(lb.Langage(language="", kernel="python3"))
    assert not lb.est_python(lb.Langage(language="polyglot-notebook",
                                         kernel=".net-csharp"))
    assert not lb.est_python(lb.Langage())


def test_la_regle_python_est_celle_du_critere():
    """Comparaison mecanique avec l'organe natif (pli 2.1).

    Le critere decide de la famille Python par ``language_info.name`` puis, en
    repli, par le nom du kernelspec ; le premier marqueur non vide tranche.
    L'organe des boutons applique **la meme regle** : le test compare les deux
    lectures sur un echantillon de carnets reels du depot.
    """
    racine = Path(__file__).resolve().parents[3]
    module = racine / "scripts" / "notebook_tools" / "pyodide_eligibility.py"
    if not module.is_file():
        pytest.skip("critere d'eligibilite absent de cet arbre")
    sys.path.insert(0, str(module.parent))
    import pyodide_eligibility as pe  # noqa: E402
    import subprocess  # noqa: E402

    listing = subprocess.run(["git", "ls-files", "*.ipynb"], cwd=str(racine),
                              capture_output=True, text=True, encoding="utf-8",
                              errors="replace").stdout.splitlines()
    assert listing, "aucun carnet suivi dans cet arbre"
    echantillon = listing[::max(1, len(listing) // 12)][:12]
    for rel in echantillon:
        langage = lb.langage_du_carnet(racine / rel)
        natif = pe.is_python_notebook(type("V", (), {
            "language": langage.language, "kernel": langage.kernel})())
        assert lb.est_python(langage) == natif, rel


# --------------------------------------------------------------------------
# L'eligibilite
# --------------------------------------------------------------------------

def test_trois_boutons_quand_tout_convient(tmp_path):
    racine = _depot(tmp_path)
    chemin = _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_PYTHON)
    entrees = {"Serie/A.ipynb": {"lab": "/CoursIA/jupyterlite/lab/index.html?path=A.ipynb"}}
    boutons = lb.boutons_pour_carnet("Serie/A.ipynb", chemin, entrees, racine)
    assert [b.genre for b in boutons] == ["codespaces", "colab", "jupyterlite"]
    assert boutons[2].url == ("https://jsboige.github.io/CoursIA/jupyterlite/"
                              "lab/index.html?path=A.ipynb")


def test_bouton_jupyterlite_absent_hors_manifeste(tmp_path):
    """Un carnet eligible mais non publie n'a PAS de bouton JupyterLite."""
    racine = _depot(tmp_path)
    chemin = _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_PYTHON)
    boutons = lb.boutons_pour_carnet("Serie/A.ipynb", chemin, {}, racine)
    assert [b.genre for b in boutons] == ["codespaces", "colab"]


def test_bouton_colab_absent_pour_un_carnet_non_python(tmp_path):
    racine = _depot(tmp_path)
    chemin = _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_CSHARP)
    entrees = {"Serie/A.ipynb": {"lab": "/CoursIA/jupyterlite/lab/index.html?path=A.ipynb"}}
    boutons = lb.boutons_pour_carnet("Serie/A.ipynb", chemin, entrees, racine)
    assert [b.genre for b in boutons] == ["codespaces", "jupyterlite"]


def test_bouton_codespaces_absent_sans_devcontainer(tmp_path):
    racine = _depot(tmp_path, avec_devcontainer=False)
    chemin = _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_PYTHON)
    boutons = lb.boutons_pour_carnet("Serie/A.ipynb", chemin, {}, racine)
    assert [b.genre for b in boutons] == ["colab"]


def test_aucun_bouton_nest_grise(tmp_path):
    """Un carnet sans droit ne porte aucun bouton -- pas de bouton desactive."""
    racine = _depot(tmp_path, avec_devcontainer=False)
    chemin = _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_CSHARP)
    boutons = lb.boutons_pour_carnet("Serie/A.ipynb", chemin, {}, racine)
    assert boutons == []


# --------------------------------------------------------------------------
# Les URL
# --------------------------------------------------------------------------

def test_url_colab_a_la_forme_canonique():
    url = lb.url_colab("MyIA.AI.Notebooks/Serie/A.ipynb")
    assert url == ("https://colab.research.google.com/github/jsboige/CoursIA/"
                   "blob/main/MyIA.AI.Notebooks/Serie/A.ipynb")


def test_url_colab_est_lue_par_l_organe_des_liens():
    """La forme produite est celle que l'organe des liens externes sait lire."""
    racine = Path(__file__).resolve().parents[3]
    module = racine / "scripts" / "notebook_tools" / "check_external_consumer_links.py"
    if not module.is_file():
        pytest.skip("organe des liens absent de cet arbre")
    sys.path.insert(0, str(module.parent))
    import check_external_consumer_links as cel  # noqa: E402
    analyse = cel._parse_url(lb.url_colab("MyIA.AI.Notebooks/Serie/A.ipynb"), "jsboige/coursia/")
    assert analyse is not None
    kind, branche, chemin = analyse
    assert kind == "colab"
    assert chemin == "MyIA.AI.Notebooks/Serie/A.ipynb"


def test_url_codespaces_porte_le_devcontainer():
    url = lb.url_codespaces()
    assert "codespaces/new" in url
    assert "devcontainer_path=.devcontainer%2Fdevcontainer.json" in url


# --------------------------------------------------------------------------
# L'injection
# --------------------------------------------------------------------------

def test_injection_apres_l_ancre_de_contenu():
    html, boutons = PAGE_NOTEBOOK, [lb.Bouton("colab", "Colab", "https://x/", "c")]
    resultat = lb.injecter(html, boutons)
    assert resultat is not None
    # les boutons se placent SOUS le titre
    assert resultat.index("coursia-launch-buttons") > resultat.index("<h1")
    assert resultat.index("coursia-launch-buttons") < resultat.index("</main>")
    assert 'href="https://x/"' in resultat


def test_injection_est_idempotente():
    boutons = [lb.Bouton("colab", "Colab", "https://x/", "c")]
    une = lb.injecter(PAGE_NOTEBOOK, boutons)
    assert une is not None
    assert lb.injecter(une, boutons) is None


def test_injection_replie_sur_le_body():
    html = "<html><body><p>pas d'ancre de contenu</p></body></html>"
    resultat = lb.injecter(html, [lb.Bouton("colab", "Colab", "https://x/", "c")])
    assert resultat is not None
    assert "coursia-launch-buttons" in resultat


def test_page_sans_ancre_est_signalee():
    html = "<html><p>rien</p></html>"
    assert lb.injecter(html, [lb.Bouton("colab", "Colab", "https://x/", "c")]) is None


def test_aucun_bouton_ne_produit_pas_de_bloc():
    assert lb.injecter(PAGE_NOTEBOOK, []) is None


# --------------------------------------------------------------------------
# La passe
# --------------------------------------------------------------------------

def test_la_passe_ne_touche_que_les_pages_de_carnets(tmp_path):
    racine = _depot(tmp_path)
    site = tmp_path / "site"
    _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_PYTHON)
    page = _ecrire_page(site, "Serie/A.html", PAGE_NOTEBOOK)
    readme = _ecrire_page(site, "Serie/README.html", PAGE_README)
    rapport = lb.passer(site, racine, {})
    assert rapport.injectees == 1
    assert "coursia-launch-buttons" in page.read_text(encoding="utf-8")
    assert "coursia-launch-buttons" not in readme.read_text(encoding="utf-8")


def test_la_passe_ignore_une_page_sans_carnet(tmp_path):
    racine = _depot(tmp_path)
    site = tmp_path / "site"
    page = _ecrire_page(site, "Serie/A.html", PAGE_NOTEBOOK)
    rapport = lb.passer(site, racine, {})
    assert rapport.pages_carnet == 0
    assert rapport.injectees == 0
    assert "coursia-launch-buttons" not in page.read_text(encoding="utf-8")


def test_la_passe_est_idempotente(tmp_path):
    racine = _depot(tmp_path)
    site = tmp_path / "site"
    _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_PYTHON)
    page = _ecrire_page(site, "Serie/A.html", PAGE_NOTEBOOK)
    lb.passer(site, racine, {})
    rapport = lb.passer(site, racine, {})
    assert rapport.injectees == 0
    assert rapport.deja_injectees == 1
    assert page.read_text(encoding="utf-8").count('data-coursia-launch-buttons="1"') == 1


def test_check_rc1_puis_rc0(tmp_path):
    racine = _depot(tmp_path)
    site = tmp_path / "site"
    _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_PYTHON)
    _ecrire_page(site, "Serie/A.html", PAGE_NOTEBOOK)
    rc = lb.main(["--site-dir", str(site), "--repo-root", str(racine), "--check"])
    assert rc == lb.EXIT_PENDING
    rc = lb.main(["--site-dir", str(site), "--repo-root", str(racine)])
    assert rc == lb.EXIT_OK
    rc = lb.main(["--site-dir", str(site), "--repo-root", str(racine), "--check"])
    assert rc == lb.EXIT_OK


def test_site_absent_rc2(tmp_path):
    rc = lb.main(["--site-dir", str(tmp_path / "rien"), "--repo-root", str(tmp_path)])
    assert rc == lb.EXIT_INSTRUMENT


def test_manifeste_illisible_rc2(tmp_path):
    racine = _depot(tmp_path)
    site = tmp_path / "site"
    site.mkdir()
    (site / "jupyterlite").mkdir()
    (site / "jupyterlite" / "manifest.json").write_text("{pas du json", encoding="utf-8")
    rc = lb.main(["--site-dir", str(site), "--repo-root", str(racine)])
    assert rc == lb.EXIT_INSTRUMENT


def test_manifeste_publie_donne_le_bouton(tmp_path):
    """Le bouton JupyterLite suit le manifeste publie du bundle."""
    racine = _depot(tmp_path)
    site = tmp_path / "site"
    _ecrire_carnet(racine, "Serie/A.ipynb", CARNET_PYTHON)
    _ecrire_page(site, "Serie/A.html", PAGE_NOTEBOOK)
    (site / "jupyterlite").mkdir(parents=True)
    (site / "jupyterlite" / "manifest.json").write_text(
        json.dumps(_manifeste({"Serie/A.ipynb":
                               "/CoursIA/jupyterlite/lab/index.html?path=A.ipynb"})),
        encoding="utf-8")
    rc = lb.main(["--site-dir", str(site), "--repo-root", str(racine)])
    assert rc == lb.EXIT_OK
    html = (site / "Serie" / "A.html").read_text(encoding="utf-8")
    assert "https://jsboige.github.io/CoursIA/jupyterlite/lab/index.html?path=A.ipynb" in html
