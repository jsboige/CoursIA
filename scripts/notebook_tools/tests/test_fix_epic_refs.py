"""Tests de l'organe de la phase 3 de l'EPIC #20250 (`fix_epic_refs.py`).

Le contrat verifie ici est triple :

- le **retrait** de la clause de coordination est **chirurgical** (le reste de
  la cellule d'en-tete est byte-identique) ;
- l'ecriture est **refusee** quand le retrait laisse un residu (parenthese
  vide) ou quand le carnet n'est pas canonique (round-trip non
  byte-identique) ;
- la note de pied est **deposee** en derniere cellule markdown.

Un carnet non canonique est refuse meme si rien n'est a changer : c'est
l'invariant qui garantit qu'un carnet ne subit pas de churn.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import fix_epic_refs as fer  # noqa: E402


def _notebook(header: str, tail: str = "## Conclusion\n\nUn bilan.\n") -> dict:
    return {
        "cells": [
            {"cell_type": "markdown", "id": "aaaa0001", "metadata": {}, "source": header},
            {"cell_type": "code", "id": "aaaa0002", "metadata": {}, "source": ["x = 1\n"], "outputs": [], "execution_count": 3},
            {"cell_type": "markdown", "id": "aaaa0003", "metadata": {}, "source": tail},
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write(path: Path, nb: dict) -> None:
    path.write_bytes((json.dumps(nb, ensure_ascii=False, indent=1) + "\n").encode("utf-8"))


def test_retrait_chirurgical_et_note_de_pied(tmp_path: Path) -> None:
    path = tmp_path / "n.ipynb"
    header = (
        "# Titre\n"
        "Une phrase qui explique.\n"
        "> Port pyz3 du notebook C# [`13_X.ipynb`](../Z3-Linq2Z3/13_X.ipynb) (Microsoft.Z3 brut). "
        "EPIC #1206, Prong B."
    )
    _write(path, _notebook(header))
    outcome = fer.apply_one(path, dry_run=False)
    assert "en-tete nettoye (#1206)" in outcome
    nb = json.loads(path.read_text(encoding="utf-8"))
    assert "EPIC" not in "".join(nb["cells"][0]["source"])
    assert "Prong" not in "".join(nb["cells"][0]["source"])
    # Le reste de l'en-tete est intact.
    assert "# Titre" in nb["cells"][0]["source"]
    assert "Port pyz3 du notebook C#" in nb["cells"][0]["source"]
    # La note de pied est dans la derniere cellule markdown.
    assert "> Carnet issu de l'EPIC #1206." in "".join(nb["cells"][2]["source"])
    # La cellule de code et ses sorties sont intactes.
    assert nb["cells"][1]["source"] == ["x = 1\n"]
    assert nb["cells"][1]["execution_count"] == 3


def test_refus_si_parenthese_vide(tmp_path: Path) -> None:
    """Une clause retiree au milieu d'une parenthese laisse « ( » : refus."""
    path = tmp_path / "n.ipynb"
    header = "# Titre\n\nCloture du bloc (Epic #4677, jambe Python-large du planificateur #1206).\n"
    _write(path, _notebook(header))
    outcome = fer.apply_one(path, dry_run=False)
    assert "refus" in outcome
    # Le carnet n'a pas ete touche.
    assert "Epic #4677" in path.read_text(encoding="utf-8")


def test_parenthese_dont_le_contenu_est_la_clause(tmp_path: Path) -> None:
    """Un groupe parenthese dont le contenu est exactement la clause part avec.

    C'est la forme mesuree sur la serie ArgumentAnalysis :
    « de la convention `fallacy_rules.py` (epic #4960), ». Le retrait emporte
    les parentheses -- sinon il laisserait « () ».
    """
    path = tmp_path / "n.ipynb"
    header = (
        "# Titre\n"
        "| **Rung** | 0-init |\n"
        "\n"
        "Ce carnet suit la convention `fallacy_rules.py` (epic #4960), "
        "et montre le graphe.\n"
    )
    _write(path, _notebook(header))
    outcome = fer.apply_one(path, dry_run=False)
    assert "en-tete nettoye (#4960)" in outcome
    nb = json.loads(path.read_text(encoding="utf-8"))
    header_after = nb["cells"][0]["source"]
    assert "fallacy_rules.py`," in header_after
    assert "()" not in header_after
    assert "EPIC" not in header_after


def test_espace_apres_parenthese_ouverte_nettoye(tmp_path: Path) -> None:
    """« (Epic #2137 Phase 2) » doit devenir « (Phase 2) », pas « ( Phase 2) ».

    L'espace residuel apres la parenthese ouvrante est un artefact du
    retrait : il est nettoye localement, la couture reste surgically.
    """
    path = tmp_path / "n.ipynb"
    header = (
        "# Titre\n"
        "| **Rung** | 0-init (Epic #2137 Phase 2, setup environnement) |\n"
    )
    _write(path, _notebook(header))
    outcome = fer.apply_one(path, dry_run=False)
    assert "en-tete nettoye (#2137)" in outcome
    nb = json.loads(path.read_text(encoding="utf-8"))
    header_after = nb["cells"][0]["source"]
    assert "(Phase 2, setup environnement)" in header_after
    assert "( Phase" not in header_after
    assert "EPIC" not in header_after


def test_structure_de_la_source_preservee(tmp_path: Path) -> None:
    """Le retrait ne re-serialise pas la liste de lignes de la cellule.

    Une cellule dont un element contient un saut de ligne vide (« ## Source\\n\\n… »)
    garderait cette forme si l'outil re-serialisait la source : le diff
    montrerait alors un churn de lignes sans changement de texte.
    """
    path = tmp_path / "n.ipynb"
    nb = _notebook("# Titre\n")
    nb["cells"][0]["source"] = [
        "# Titre\n",
        "\n",
        "## Source\n\nCe carnet s'inscrit dans la serie.",
        " EPIC #1206, Prong B.",
    ]
    _write(path, nb)
    outcome = fer.apply_one(path, dry_run=False)
    assert "en-tete nettoye (#1206)" in outcome
    after = json.loads(path.read_text(encoding="utf-8"))
    source = after["cells"][0]["source"]
    assert len(source) == 4
    assert source[3] == ""


def test_refus_si_parentheses_desequilibrees(tmp_path: Path) -> None:
    """Un retrait qui laisse une parenthese orpheline est refuse."""
    path = tmp_path / "n.ipynb"
    header = "# Titre\n\nBloc ((epic #4677)) de la distillation.\n"
    _write(path, _notebook(header))
    outcome = fer.apply_one(path, dry_run=False)
    assert "refus" in outcome
    assert "epic #4677" in path.read_text(encoding="utf-8")


def test_refus_si_carnet_non_canonique(tmp_path: Path) -> None:
    """Un carnet dont le round-trip n'est pas byte-identique n'est pas reecrit."""
    path = tmp_path / "n.ipynb"
    header = "# Titre\n\n> Port. EPIC #1206, Prong B."
    _write(path, _notebook(header))
    # Changer la forme du fichier sans toucher au contenu des cellules.
    raw = path.read_text(encoding="utf-8").replace('"x = 1\\n"', '"x = 1\\n"   ')
    path.write_text(raw, encoding="utf-8")
    outcome = fer.apply_one(path, dry_run=False)
    assert "byte-identique" in outcome
    assert "EPIC #1206" in path.read_text(encoding="utf-8")


def test_scan_signale_les_refus_sans_ecrire(tmp_path: Path) -> None:
    path = tmp_path / "n.ipynb"
    header = "# Titre\n\nCloture du bloc (Epic #4677, jambe Python-large du planificateur #1206).\n"
    _write(path, _notebook(header))
    info = fer.analyse(path)
    assert info["refs"] == ["4677"]
    assert info["refused"]


def test_scan_et_apply_refusent_le_meme_carnet_non_canonique(tmp_path: Path) -> None:
    """Un carnet non canonique est refuse par le scan ET par l'application.

    Le scan annoncait « repariable » (la reference etait trouvee, aucun refus
    enregistre) alors que l'application repondait « round-trip non
    byte-identique » : le decompte « avant/apres » d'une fournee ne voulait
    donc rien dire. Le predicat d'eligibilite est desormais UNIQUE : les deux
    portes rendent le MEME motif de refus.
    """
    path = tmp_path / "n.ipynb"
    header = "# Titre\n\n> Port. EPIC #1206, Prong B."
    _write(path, _notebook(header))
    # Changer la forme du fichier sans toucher au contenu des cellules.
    raw = path.read_text(encoding="utf-8").replace('"x = 1\\n"', '"x = 1\\n"   ')
    path.write_text(raw, encoding="utf-8")

    info = fer.analyse(path)
    assert info["refs"] == ["1206"]
    assert info["refused"]
    outcome = fer.apply_one(path, dry_run=True)
    assert outcome == info["refused"]
    assert "byte-identique" in outcome
    # Le carnet n'a pas ete touche.
    assert "EPIC #1206" in path.read_text(encoding="utf-8")


def test_le_scan_compte_un_carnet_non_canonique_comme_refuse(tmp_path: Path,
                                                            capsys) -> None:
    """Le decompte du scan classe un carnet non canonique en « refuse ».

    C'est la consequence comptable du predicat unique : un carnet que
    l'application refuse ne peut plus etre annonce comme « repariable » par
    le scan.
    """
    path = tmp_path / "n.ipynb"
    header = "# Titre\n\n> Port. EPIC #1206, Prong B."
    _write(path, _notebook(header))
    raw = path.read_text(encoding="utf-8").replace('"x = 1\\n"', '"x = 1\\n"   ')
    path.write_text(raw, encoding="utf-8")

    rc = fer.main(["--scan", str(tmp_path)])
    out = capsys.readouterr().out
    assert rc == 0
    assert "repairables : 0" in out
    assert "(refuses) : 1" in out


def test_scan_et_apply_refusent_le_meme_reference_non_couverte(tmp_path: Path) -> None:
    """Une reference citee mais non retirable est refusee par les deux portes.

    L'en-tete porte la reference coupee sur deux elements de la source
    (['Intro. EP', 'IC #1206.']) : le scan la voyait ('EPIC #1206' sur le texte
    joint), mais aucune clause n'est retirable element par element -- et
    l'application repondait « aucune reference d'EPIC en en-tete » sans que le
    scan le sache.
    """
    path = tmp_path / "n.ipynb"
    nb = _notebook("# Titre\n")
    nb["cells"][0]["source"] = ["Intro. EP", "IC #1206."]
    _write(path, nb)

    info = fer.analyse(path)
    assert info["refs"] == ["1206"]
    assert info["refused"]
    outcome = fer.apply_one(path, dry_run=True)
    assert outcome == info["refused"]
    assert "non couverte" in outcome
    # Le carnet n'a pas ete touche.
    assert "IC #1206." in path.read_text(encoding="utf-8")


def test_scan_et_apply_refusent_le_meme_carnet_a_une_seule_cellule_markdown(tmp_path: Path) -> None:
    """Un carnet d'une seule cellule markdown n'a pas de pied distinct.

    Ces deux controles de DESTINATION vivaient dans `apply_one` : le scan
    annoncait « repariable » la ou l'application refusait d'ecrire. Ils sont
    desormais dans `_plan`, donc les deux portes rendent le MEME motif.
    """
    path = tmp_path / "n.ipynb"
    nb = {
        "cells": [{"cell_type": "markdown", "id": "aaaa0001", "metadata": {},
                   "source": "# Titre\n\nEPIC #1206."}],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    _write(path, nb)

    info = fer.analyse(path)
    assert info["refs"] == ["1206"]
    assert info["refused"]
    outcome = fer.apply_one(path, dry_run=True)
    assert outcome == info["refused"]
    assert "une seule cellule markdown" in outcome
    # Le carnet n'a pas ete touche.
    assert "EPIC #1206." in path.read_text(encoding="utf-8")


def test_scan_et_apply_refusent_le_meme_carnet_a_note_de_pied_deja_presente(tmp_path: Path) -> None:
    """Une note de pied deja deposee rend le carnet non eligible.

    Deuxieme forme du meme residu : le scan annoncait « repariable » la ou
    l'application refusait d'ecrire une seconde fois.
    """
    path = tmp_path / "n.ipynb"
    nb = _notebook("# Titre\n\nEPIC #1206.\n",
                   tail="> Carnet issu de l'EPIC #1206.\n")
    _write(path, nb)

    info = fer.analyse(path)
    assert info["refs"] == ["1206"]
    assert info["refused"]
    outcome = fer.apply_one(path, dry_run=True)
    assert outcome == info["refused"]
    assert "note de pied deja presente" in outcome
    # Le carnet n'a pas ete touche : une seule note de pied.
    assert path.read_text(encoding="utf-8").count("Carnet issu de l'EPIC") == 1
