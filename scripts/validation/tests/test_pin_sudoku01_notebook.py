"""Temoin du controle positif #25510 : ce test lit un carnet par chemin construit.

La delegation hors table de ``changed_scripts_tests`` (#25510) selectionne,
pour les chemins hors aires de veille, les suites que l'organe natif
``select_tests`` rattache au changement : celles qui citent le fichier (R3)
ou parcourent le depot (R4). Ce fichier ne fait ni l'un ni l'autre -- le nom
du carnet y est construit par concatenation, aucun motif de parcours n'y
figure -- donc sa suite reste EXCLUE de la selection restreinte du profil
marathon (carnets + ``twin_pairs.d/``), alors qu'elle figure dans la liste
complete du workflow, jouee par le lot quatre fois par jour (P3,
``slow-lane.yml``).

Le temoin : une PR qui retire la ligne de navigation de la premiere cellule
du carnet et touche un ``twin_pairs.d/`` passe la selection restreinte VERT
et le lot ROUGE -- ce fichier est ce rouge, volontairement hors selection.
Si ce test rougit au lot sans rougir au restreint, le filet fonctionne.
"""
from __future__ import annotations

import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]

# Noms construits, jamais ecrits en entier : la concatenation evite la
# citation textuelle (R3) qui ramenerait cette suite dans la selection du
# carnet -- et celle du lien d'index, que tout fichier d'index de serie
# changerait (review #26253 : R3 compare le nom de base, n'importe quel
# fichier de ce nom modifie selectionnait ce temoin).
_CARNET = "Sudoku-01-Backtracking" + "-Python.ipynb"
CHEMIN = REPO_ROOT / "MyIA.AI.Notebooks" / "Sudoku" / _CARNET
_LIEN_INDEX = "](" + "READ" + "ME" + ".md" + ")"


def _carnet() -> dict:
    return json.loads(CHEMIN.read_text(encoding="utf-8"))


def test_le_carnet_pin_garde_sa_structure_executee() -> None:
    """Le carnet reste un carnet sain : cellules nombreuses, code execute.

    Un temoin structurel : une casse structurelle du carnet (cellules
    supprimees, sorties retirees) rougit ici, hors selection restreinte.
    """
    data = _carnet()
    cells = data["cells"]
    assert len(cells) >= 30, f"carnet amaigri : {len(cells)} cellules"
    code = [c for c in cells if c.get("cell_type") == "code"]
    assert len(code) >= 10, f"code amaigri : {len(code)} cellules"
    sans_execution = [c for c in code if c.get("execution_count") is None]
    assert not sans_execution, (
        f"{len(sans_execution)} cellule(s) code sans execution_count"
    )


def test_le_carnet_pin_garde_sa_ligne_de_navigation() -> None:
    """La premiere cellule porte la navigation de serie de ce carnet.

    C'est le point de rupture vise par la PR temoin : retirer cette ligne
    (edition markdown seule) ne casse NI les suites selectionnees NI
    l'execution du carnet -- seulement ce test, hors selection.
    """
    data = _carnet()
    tete = next(
        (c for c in data["cells"] if c.get("cell_type") == "markdown"), None
    )
    assert tete is not None, "pas de cellule markdown en tete"
    texte = "".join(tete.get("source", []))
    assert "Navigation" in texte, "ligne de navigation absente"
    assert _LIEN_INDEX in texte, "lien index absent"
    assert texte.count(".ipynb)") >= 2, (
        "liens voisin gauche / voisin droit absents"
    )
