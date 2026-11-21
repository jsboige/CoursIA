#!/usr/bin/env python3
"""Fonctions pures de `pyodide_browser_run.py` : chemin, journal, synthese.

Ce que ce fichier garde
-----------------------
Le pilote Pyodide produit une preuve **publique** (`docs/reference/pyodide-executions/`).
Deux etats de la machine s'y glisseaient : le chemin absolu du site construit
hors du depot, et le journal brut du navigateur (port du serveur local,
identifiant de noyau). La revue coordinateur les a refuses (reserve 1 de la
review du 20/11 22:26Z) : le script doit ecrire un chemin relatif au depot et
ne garder du journal que ce qui sert la preuve.

Ce test fixe donc les trois fonctions qui portent cette exigence :
`chemin_relatif` (le chemin), `filtrer_console` (le journal) et `agreger`
(la synthese par carnet, qui alimente le rapport ET le JSON). Elles sont
pures : aucun navigateur, aucun site, aucune ecriture.

Un test qui ne verrait qu'un seul de ces deux cas passerait a cote
------------------------------------------------------------------
- un chemin absolu qui slipserait ne serait vu que par le test de chemin ;
- un journal complet qui reviendrait ne serait vu que par le test de journal.

Les deux sont donc explicites, et le test de synthese verifie que le rapport
Markdown consomme la meme fonction que le JSON : une synthese qui diverge
entre les deux preuves serait indetectable autrement.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

from pyodide_browser_run import (  # noqa: E402
    agreger,
    chemin_relatif,
    filtrer_console,
    lire_lot,
    render_markdown,
    url_de_page,
)


def test_chemin_relatif_exprime_le_site_par_rapport_au_depot(tmp_path):
    racine = tmp_path / "CoursIA"
    site = racine / ".tmp" / "lite-site" / "_output"
    site.mkdir(parents=True)
    assert chemin_relatif(site, racine) == ".tmp/lite-site/_output"


def test_chemin_relatif_hors_du_depot_ne_garde_que_le_nom_du_dossier(tmp_path):
    racine = tmp_path / "CoursIA"
    racine.mkdir()
    site = tmp_path / "ailleurs" / "lite-site" / "_output"
    site.mkdir(parents=True)
    relatif = chemin_relatif(site, racine)
    assert relatif == "_output"
    # aucun caractere de chemin absolu, aucune lettre de lecteur
    assert ":" not in relatif
    assert "\\" not in relatif
    assert str(tmp_path) not in relatif


def test_filtrer_console_ne_garde_que_erreurs_et_avertissements():
    journal = [
        "log: chargement de lab/index.html",
        "info: kernel ready",
        "debug: websocket ping",
        "error: echec du tracage",
        "warning: numpy depreciated",
    ]
    garde = filtrer_console(journal)
    assert garde == ["error: echec du tracage", "warning: numpy depreciated"]


def test_filtrer_console_redige_port_et_identifiant_de_noyau():
    journal = [
        "error: impossible de joindre http://127.0.0.1:52455/lab/index.html",
        "error: noyau ws://127.0.0.1:52455/api/kernels/"
        "3f7c1b2a-9d4e-4a1b-8c2f-0e5a6b7c8d9e indisponible",
    ]
    garde = filtrer_console(journal)
    texte = "\n".join(garde)
    assert "52455" not in texte
    assert "3f7c1b2a-9d4e-4a1b-8c2f-0e5a6b7c8d9e" not in texte
    assert "<hote-local>" in texte
    assert "<id>" in texte


def test_url_de_page_est_relative_au_site():
    assert url_de_page("10-SIG-3D-Tiles-Python.ipynb") == (
        "/lab/index.html?path=10-SIG-3D-Tiles-Python.ipynb"
    )
    assert "127.0.0.1" not in url_de_page("a.ipynb")


def test_lire_lot_rend_les_carnets_dans_lordre(tmp_path):
    lot = {
        "carnets": [
            {"path": "MyIA.AI.Notebooks/GenAI/3D/10-SIG-3D-Tiles-Python.ipynb",
             "series": "3D"},
            {"path": "MyIA.AI.Notebooks/Audio/06-3-AudioDiffusion.ipynb",
             "series": "Audio"},
        ]
    }
    fichier = tmp_path / "lot.json"
    fichier.write_text(json.dumps(lot), encoding="utf-8")
    carnets = lire_lot(fichier)
    assert [Path(c["path"]).name for c in carnets] == [
        "10-SIG-3D-Tiles-Python.ipynb",
        "06-3-AudioDiffusion.ipynb",
    ]


def test_agreger_compte_par_carnet():
    resultats = [
        {
            "carnet": "a.ipynb",
            "cellules_code": 6,
            "cellules_executees": 6,
            "cellules_avec_sortie": 5,
            "erreurs": [],
            "duree_s": 53.6,
            "temps_premier_resultat_s": 6.8,
            "succes": True,
        },
        {
            "carnet": "b.ipynb",
            "cellules_code": 3,
            "cellules_executees": 1,
            "cellules_avec_sortie": 0,
            "erreurs": ["traceback"],
            "duree_s": 12.0,
            "temps_premier_resultat_s": None,
            "succes": False,
        },
    ]
    lignes = agreger(resultats)
    assert lignes[0]["cellules_code"] == 6
    assert lignes[0]["erreurs"] == 0
    assert lignes[0]["succes"] is True
    assert lignes[1]["cellules_executees"] == 1
    assert lignes[1]["erreurs"] == 1
    assert lignes[1]["succes"] is False


def test_le_rapport_et_la_synthese_ont_la_meme_source():
    """Le Markdown et le JSON doivent porter la meme synthese par carnet."""
    resultats = [
        {
            "carnet": "a.ipynb",
            "cellules_code": 6,
            "cellules_executees": 6,
            "cellules_avec_sortie": 6,
            "erreurs": [],
            "duree_s": 53.6,
            "temps_premier_resultat_s": 6.8,
            "succes": True,
            "cellules": [],
        }
    ]
    rapport = render_markdown(resultats)
    ligne = agreger(resultats)[0]
    assert "| `%s` | %s | %s | %s | %s | %s | %s | **succes** |" % (
        ligne["carnet"], ligne["cellules_code"], ligne["cellules_executees"],
        ligne["cellules_avec_sortie"], ligne["erreurs"], ligne["duree_s"],
        ligne["temps_premier_resultat_s"],
    ) in rapport


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
