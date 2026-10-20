"""Tests du crosswalk A1 dans le catalogue bibliographique (#21631, A5).

Quand le gisement detient la **version publiee** d'un preprint, ni le nom de
fichier ni la premiere page ne portent l'identifiant arXiv cite par la serie
(cas mesure : `2401.05375` -> Adaptive Behavior 2025, PDF porte par le seul
DOI). Les CSVs de resolution A1 portent alors la colonne `chemin_gisement` :
c'est l'autorite qui relie l'identifiant au fichier. Sans ce crosswalk, le
controle « l'avons-nous deja ? » echoue sur ces cas, et l'acquisition fabrique
un doublon.

Ces tests ciblent `appliquer_crosswalk_a1()` : le crosswalk n'est emis que si
le fichier existe, et jamais en double.
"""
from __future__ import annotations

import csv
import importlib.util
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
MODULE_PATH = REPO_ROOT / "scripts" / "build_bibliography_identifier_catalog.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("build_biblio_catalogue", MODULE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules["build_biblio_catalogue"] = module
    spec.loader.exec_module(module)
    return module


bcc = _load_module()


def _write_a1(tmp_path: Path, rows: list[dict], name: str = "a1.csv") -> Path:
    path = tmp_path / name
    champs = ["id", "verdict", "titre_api", "chemin_gisement"]
    with open(path, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=champs)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)
    return path


def _catalogue(rows: list[dict] | None = None) -> list[dict]:
    return list(rows or [])


def test_crosswalk_links_a_cited_identifier_to_its_published_file(tmp_path):
    """Le cas mesure : l'identifiant cite est relie au fichier canonique."""
    pdf = tmp_path / "Automata" / "2025 - zhang-et-al.pdf"
    pdf.parent.mkdir(parents=True)
    pdf.write_bytes(b"%PDF-1.4\n")
    a1 = _write_a1(tmp_path, [{
        "id": "2401.05375", "verdict": "DETENU", "titre_api": "Classical Sorting...",
        "chemin_gisement": "Automata/2025 - zhang-et-al.pdf",
    }])

    catalogue = _catalogue()
    stats = bcc.appliquer_crosswalk_a1(catalogue, [str(a1)], tmp_path)

    assert stats["appliques"] == 1
    assert stats["par_type"]["arxiv"] == 1
    assert len(catalogue) == 1
    ligne = catalogue[0]
    assert ligne["type_id"] == "arxiv"
    assert ligne["id"] == "2401.05375"
    assert ligne["chemin_gisement"] == "Automata/2025 - zhang-et-al.pdf"
    assert ligne["source"] == bcc.SOURCE_CROSSWALK
    assert ligne["confiance"] == "elevee"


def test_crosswalk_normalises_windows_separators(tmp_path):
    """Les CSVs A1 melangent `\\` et `/` ; le catalogue est en posix."""
    pdf = tmp_path / "Symbolic" / "2018 - Evans.pdf"
    pdf.parent.mkdir(parents=True)
    pdf.write_bytes(b"%PDF-1.4\n")
    a1 = _write_a1(tmp_path, [{
        "id": "1711.04574", "verdict": "DETENU", "titre_api": "Learning Explanatory Rules...",
        "chemin_gisement": "Symbolic\\2018 - Evans.pdf",
    }])

    catalogue = _catalogue()
    bcc.appliquer_crosswalk_a1(catalogue, [str(a1)], tmp_path)

    assert catalogue[0]["chemin_gisement"] == "Symbolic/2018 - Evans.pdf"


def test_crosswalk_refuses_a_path_that_does_not_exist(tmp_path):
    """On ne relie jamais un identifiant a un fichier absent du gisement."""
    a1 = _write_a1(tmp_path, [{
        "id": "9999.99999", "verdict": "DETENU", "titre_api": "Absent",
        "chemin_gisement": "MachineLearning/2099 - Absent.pdf",
    }])

    catalogue = _catalogue()
    stats = bcc.appliquer_crosswalk_a1(catalogue, [str(a1)], tmp_path)

    assert stats["appliques"] == 0
    assert stats["sans_fichier"] == 1
    assert catalogue == []


def test_crosswalk_never_duplicates_an_identifier_already_in_catalogue(tmp_path):
    """Un identifiant deja relie (meme a un autre chemin) ne produit pas de
    second chemin : deux chemins pour un identifiant, ce serait un doublon."""
    pdf = tmp_path / "MachineLearning" / "2011 - Pedregosa.pdf"
    pdf.parent.mkdir(parents=True)
    pdf.write_bytes(b"%PDF-1.4\n")
    a1 = _write_a1(tmp_path, [{
        "id": "1201.0490", "verdict": "DETENU", "titre_api": "Scikit-learn",
        "chemin_gisement": "MachineLearning/2011 - Pedregosa.pdf",
    }])
    deja = {"chemin_gisement": "Autre/2011 - Pedregosa.pdf", "type_id": "arxiv",
            "id": "1201.0490", "source": "nom_fichier", "confiance": "elevee",
            "contexte": "x"}

    catalogue = _catalogue([deja])
    stats = bcc.appliquer_crosswalk_a1(catalogue, [str(a1)], tmp_path)

    assert stats["appliques"] == 0
    assert stats["deja_presents"] == 1
    assert len(catalogue) == 1


def test_crosswalk_without_a_path_column_is_a_no_op(tmp_path):
    """Un CSV A1 sans colonne `chemin_gisement` ne fait rien, sans planter."""
    path = tmp_path / "a1_sans_chemin.csv"
    with open(path, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=["id", "verdict"])
        writer.writeheader()
        writer.writerow({"id": "2401.05375", "verdict": "DETENU"})

    catalogue = _catalogue()
    stats = bcc.appliquer_crosswalk_a1(catalogue, [str(path)], tmp_path)

    assert stats["appliques"] == 0
    assert stats["sans_chemin"] == 1
    assert catalogue == []


def test_after_the_crosswalk_the_a1_join_resolves_the_identifier(tmp_path):
    """Le round trip : le cas que le controle « l'avons-nous deja ? » echouait
    a resoudre devient resolu (criterе d'acceptation « observation alias +
    fold » transpose au catalogue)."""
    pdf = tmp_path / "Automata" / "2025 - zhang-et-al.pdf"
    pdf.parent.mkdir(parents=True)
    pdf.write_bytes(b"%PDF-1.4\n")
    a1 = _write_a1(tmp_path, [{
        "id": "2401.05375", "verdict": "DETENU", "titre_api": "Classical Sorting...",
        "chemin_gisement": "Automata/2025 - zhang-et-al.pdf",
    }])

    avant = _catalogue()
    jointure_avant = bcc.joindre_a1(avant, [str(a1)])["a1"][0]
    assert jointure_avant["resolus"] == 0
    assert jointure_avant["non_resolus"] == 1

    apres = _catalogue()
    bcc.appliquer_crosswalk_a1(apres, [str(a1)], tmp_path)
    jointure_apres = bcc.joindre_a1(apres, [str(a1)])["a1"][0]
    assert jointure_apres["resolus"] == 1
    assert jointure_apres["non_resolus"] == 0


def test_lire_catalogue_round_trips_the_written_csv(tmp_path):
    """Le rechargement d'un catalogue existant garde les memes champs."""
    catalogue = [{"chemin_gisement": "Automata/x.pdf", "type_id": "arxiv",
                   "id": "2401.05375", "source": bcc.SOURCE_CROSSWALK,
                   "confiance": "elevee", "contexte": "c"}]
    sortie = tmp_path / "cat.csv"
    bcc.ecrire_csv(catalogue, sortie)

    relu = bcc.lire_catalogue(sortie)
    assert relu == catalogue
