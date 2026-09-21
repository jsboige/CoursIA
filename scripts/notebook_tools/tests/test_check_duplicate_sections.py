# -*- coding: utf-8 -*-
"""Tests du garde des sections dupliquees par accretion.

Les deux premiers tests sont les **controles positifs** : un garde qui ne peut
pas echouer ne prouve rien quand il rend vert. Le troisieme est le controle
NEGATIF qui porte tout l'interet de cet organe -- un gabarit par exercice
repete legitimement ses titres, et ne doit pas etre accuse.
"""
import json
import sys

from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_duplicate_sections import (  # noqa: E402
    accretions,
    excess_of,
    headings,
    main,
    normalize,
)


def md(text):
    return {"cell_type": "markdown", "source": [text]}


def code(text):
    return {"cell_type": "code", "source": [text], "outputs": [], "execution_count": 1}


# --- controles positifs : le garde DOIT mordre ---------------------------------

def test_mord_sur_deux_resumes_colles_sous_le_meme_parent():
    """Le cas canonique signale par le user sur SW-4 : « Resume » deux fois,
    cellules voisines, sous la meme section."""
    cells = [md("## 5. Conclusion"), md("### Resume\nPremiere redaction."),
             md("### Resume\nSeconde redaction.")]
    found = accretions(cells)
    assert len(found) == 1
    assert found[0]["title"] == "Resume"
    assert found[0]["count"] == 2
    assert found[0]["excess"] == 1
    assert found[0]["cells"] == [1, 2]
    assert found[0]["parent"] == ["5. Conclusion"]


def test_mord_sur_interpretations_accretees_dans_une_meme_partie():
    """Le defaut de la campagne de densification : chaque tranche rajoute son
    « Interpretation » sous la meme partie, sans consolider."""
    cells = [md("## Partie 2 : Setup"),
             code("x = 1"), md("### Interpretation\nA."),
             code("y = 2"), md("### Interpretation\nB."),
             code("z = 3"), md("### Interpretation\nC.")]
    found = accretions(cells)
    assert len(found) == 1
    assert found[0]["count"] == 3
    assert excess_of(cells) == 2


# --- controle NEGATIF : le discriminant hierarchique ---------------------------

def test_un_gabarit_par_exercice_n_est_pas_une_accretion():
    """Cinq exercices, chacun avec son « Objectif » : structure legitime.

    C'est ce controle qui separe cet organe d'un simple comptage de titres --
    lequel accusait 274 notebooks la ou 80 portent le defaut.
    """
    cells = []
    for n in range(1, 6):
        cells.append(md("## Exercice %d" % n))
        cells.append(md("### Objectif\nBut de l'exercice %d." % n))
        cells.append(md("### Instructions\nMarche a suivre."))
    assert accretions(cells) == []
    assert excess_of(cells) == 0


def test_le_meme_titre_sous_deux_parents_differents_reste_innocent():
    cells = [md("## Partie 1"), md("### Lecture du resultat\nA."),
             md("## Partie 2"), md("### Lecture du resultat\nB.")]
    assert accretions(cells) == []


def test_un_notebook_sain_ne_declenche_rien():
    cells = [md("# Titre"), md("## Introduction"), code("x = 1"),
             md("### Lecture du resultat\nA."), md("## Conclusion")]
    assert accretions(cells) == []
    assert excess_of(cells) == 0


# --- normalisation et extraction ----------------------------------------------

def test_l_emphase_ne_masque_pas_un_doublon():
    """Une seconde redaction reprend rarement la graisse de la premiere."""
    cells = [md("## Bilan"), md("### **Resume**\nA."), md("### Resume\nB.")]
    found = accretions(cells)
    assert len(found) == 1
    assert found[0]["title"] == "Resume"


def test_normalize_replie_les_espaces_et_retire_l_emphase():
    assert normalize("**Lecture   du  resultat**") == "Lecture du resultat"
    assert normalize("`Cout` computationnel") == "Cout computationnel"


def test_les_titres_en_conteneur_sont_ignores():
    """« - # Indice : ... » est un defaut de RENDU (fix_hint_headings.py), pas
    une section. Deux indices identiques ne sont pas une accretion."""
    cells = [md("## Exercice"), md("- # Indice : cout = a * b"),
             md("- # Indice : cout = a * b")]
    assert headings(cells) == [(2, "Exercice", 0)]
    assert accretions(cells) == []


def test_le_source_en_chaine_est_lu_comme_le_source_en_liste():
    """nbformat autorise les deux ; en lire un seul rend un faux zero."""
    cells = [{"cell_type": "markdown", "source": "## Bilan"},
             {"cell_type": "markdown", "source": "### Resume\nA."},
             {"cell_type": "markdown", "source": "### Resume\nB."}]
    assert excess_of(cells) == 1


def test_un_titre_de_niveau_superieur_ferme_la_section_precedente():
    """Deux « Resume » separes par une remontee de niveau ont des parents
    differents : la pile doit se depiler, sinon le garde sur-accuse."""
    cells = [md("# Chapitre A"), md("## Resume\nA."),
             md("# Chapitre B"), md("## Resume\nB.")]
    assert accretions(cells) == []


def test_un_notebook_sans_cellule_markdown_ne_casse_pas():
    assert accretions([code("x = 1"), code("y = 2")]) == []


# --- fail-closed : une mesure impossible n'est pas une mesure a zero -----------

def test_un_notebook_illisible_rend_2_et_jamais_0(tmp_path, capsys):
    """Un `rc=0` sur un fichier que l'organe n'a pas pu ouvrir le ferait passer
    pour sain. C'est le fail-open que les gardes de ce depot existent pour
    empecher : l'etat est INCONNU, et le code de sortie doit le dire."""
    assert main([str(tmp_path / "absent.ipynb")]) == 2
    assert "INCONNU" in capsys.readouterr().out


def test_un_notebook_illisible_masque_pas_un_defaut_reel(tmp_path):
    """Melange d'un porteur et d'un illisible : le refus prime, et le defaut
    reste imprime."""
    good = tmp_path / "dup.ipynb"
    good.write_text(json.dumps({"cells": [
        {"cell_type": "markdown", "source": "## Bilan"},
        {"cell_type": "markdown", "source": "### Resume\nA."},
        {"cell_type": "markdown", "source": "### Resume\nB."},
    ]}), encoding="utf-8")
    assert main([str(good)]) == 1
    assert main([str(good), str(tmp_path / "absent.ipynb")]) == 2
