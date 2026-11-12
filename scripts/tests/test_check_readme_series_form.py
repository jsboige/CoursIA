#!/usr/bin/env python3
"""Tests de la regle V2 de `check_readme_series_form.py` (doctrine #3973).

La mesure fondatrice (2026-11-12, `origin/main`) : sur les 132 READMEs de
series inspectes par l'organe, 9 portaient `lettres_dans_parcours_principal`
— et les 9 etaient des **faux positifs**. Aucune de leurs lignes ne commence
par une lettre ; chaque lien lettre siege dans la **derniere colonne**
(« Pour approfondir »), la forme que la doctrine autorise explicitement.

L'organe comptait `LETTER_LINK.search(row)` sur la ligne entiere, donc la
forme autorisee etait exactement celle qu'il sanctionnait. Un organe qui
rougit la conformite ne peut pas servir de critere de review : c'est le
defaut que ces tests verrouillent.

Chaque controle positif est double d'un controle negatif : la regle doit
rester mordante sur les trois formes qui sont de vrais defauts.
"""

from __future__ import annotations

import importlib.util
import os

import pytest

_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "notebook_tools",
    "check_readme_series_form.py",
)

_spec = importlib.util.spec_from_file_location("check_readme_series_form", _PATH)
form = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(form)


HEADER = "| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |"
SEPARATOR = "|---|---|---|---|---|"


def _readme(main_rows: list[str], approfond_rows: list[str] | None = None) -> str:
    """Assemble un README minimal portant les trois marqueurs V1."""
    lines = [
        "# Serie de test",
        "",
        "## Comment lire ce README",
        "",
        "Vous decouvrez : lisez le parcours principal.",
        "",
        "## Structure",
        "",
        "### Parcours principal",
        "",
        HEADER,
        SEPARATOR,
        *main_rows,
        "",
    ]
    if approfond_rows is not None:
        lines += [
            "### Approfondissements",
            "",
            "#### Autour de 01",
            "",
            "| # | Notebook | Ce qu'il ajoute |",
            "|---|---|---|",
            *approfond_rows,
            "",
        ]
    return "\n".join(lines)


def _inspect(main_rows: list[str], approfond_rows: list[str] | None = None) -> dict:
    return form.inspect_text("Serie/README.md", _readme(main_rows, approfond_rows))


# --- Controle positif de la mesure fondatrice : la forme autorisee est conforme


@pytest.mark.parametrize(
    "row",
    [
        # Lien court dans la derniere colonne : la forme que la doctrine autorise.
        "| 01 | [Shannon-Fano](Compression-01-ShannonFano-Prefixe-Python.ipynb) "
        "| Construire un arbre de code | Decouverte | [01b - preuves Lean](#autour-de-01) |",
        # Plusieurs liens lettres dans la derniere colonne.
        "| 02 | [Huffman](Compression-02-Huffman-Python.ipynb) "
        "| Reconstruire les mots de code | Decouverte | [02b - codecs](#a), [02c - fronts](#b) |",
        # Ligne sans aucun lien lettre.
        "| 03 | [LZ77](Compression-03-LZ77-Python.ipynb) "
        "| Remplacer une repetition par une reference | Intermediaire | - |",
    ],
)
def test_derniere_colonne_est_conforme(row: str) -> None:
    item = _inspect([row], ["| 01b | [Preuves Lean](P.ipynb) | Certificats |"])
    assert "lettres_dans_parcours_principal" not in item["extra"], item
    assert item["conforming"] is True


def test_ligne_entete_et_separateur_ne_sont_pas_des_defauts() -> None:
    item = _inspect(
        ["| 01 | [A](a.ipynb) | Apprendre | Decouverte | - |"],
        ["| 01b | [B](b.ipynb) | Approfondir |"],
    )
    assert item["extra"] == []


# --- Controles negatifs : les trois formes qui sont de vrais defauts


def test_lettre_en_premiere_cellule_est_un_defaut() -> None:
    """Un palier deguise en etape du parcours."""
    item = _inspect(
        ["| 01b | [Preuves Lean](p.ipynb) | Certificats | Avance | - |"],
        ["| 01b | [Preuves Lean](p.ipynb) | Certificats |"],
    )
    assert "lettres_dans_parcours_principal" in item["extra"], item
    assert item["conforming"] is False


def test_lien_lettre_en_colonne_intermediaire_est_un_defaut() -> None:
    """Le palier est cite au milieu de la ligne, donc presente comme une etape."""
    item = _inspect(
        ["| 01 | [A](a.ipynb) | Voir aussi [01b - Lean](#x) | Decouverte | - |"],
        ["| 01b | [B](b.ipynb) | Approfondir |"],
    )
    assert "lettres_dans_parcours_principal" in item["extra"], item


def test_lettre_absente_des_approfondissements_est_un_defaut() -> None:
    """Le palier figure dans le parcours et nulle part sous Approfondissements."""
    item = _inspect(
        ["| 01b | [A](a.ipynb) | Apprendre | Decouverte | - |"],
        ["| 01 | [A](a.ipynb) | Parcours |"],
    )
    assert "lettres_absentes_d_Approfondissements" in item["extra"], item


# --- Le decoupage en cellules respecte les pipes echappes


def test_pipe_echappe_ne_coupe_pas_la_cellule() -> None:
    row = "| 01 | [A](a.ipynb) | Un `a \\| b` dans le texte | Decouverte | [01b - Lean](#x) |"
    assert form._cells(row) == [
        " 01 ",
        " [A](a.ipynb) ",
        " Un `a \\| b` dans le texte ",
        " Decouverte ",
        " [01b - Lean](#x) ",
    ]
    item = _inspect([row], ["| 01b | [B](b.ipynb) | Approfondir |"])
    assert "lettres_dans_parcours_principal" not in item["extra"], item