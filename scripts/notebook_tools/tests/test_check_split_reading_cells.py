# -*- coding: utf-8 -*-
"""Tests de l'organe de recensement des lectures scindees (STOP #13410).

Contexte : #17077. L'organe `check_split_reading_cells.py` (merge #16786) est la
**base de preuve** de la campagne densite (#13410 / #16762) et du cliquet #17044 ;
il est livre sans suite de tests. Une retouche de l'heuristique (Jaccard +
containment sur mots rares) peut donc changer silencieusement un verdict
`generic_pair` / `separated_by_code` / `named_split` dans les bodies deja postes.
Cette suite epingle les verdicts ET les seuils.

Trois blocs :

  1. **Controles positifs** -- les 4 verdicts : le detecteur DOIT mordre.
  2. **Controles negatifs** -- prose ordinaire, paire separee par du code mais
     non nommee, carnet clean : un detecteur qui mord partout ne prouve rien.
  3. **Seuils epingles** (`MAX_DF`, Jaccard, containment, `cell_title`) et
     interface CLI (codes de retour 0 / 1 / 2).

Les bornes connues du detecteur sont epinglees en `xfail(strict=True)` : la suite
reste verte, le defaut reste visible, et le jour du fix le test passe en XPASS
(donc en echec) -- ce qui force a retirer le marqueur au lieu de le laisser
pourrir. Cf #17134.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_split_reading_cells import (  # noqa: E402
    MAX_DF,
    cell_title,
    detect,
    is_interpretation_title,
    is_named_second,
    main,
    overlap_metrics,
)


def md(text):
    return {"cell_type": "markdown", "source": [text], "metadata": {}}


def code(text):
    return {"cell_type": "code", "source": [text], "outputs": [], "execution_count": 1}


def nb(*cells):
    return {"cells": list(cells), "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# --- 1. Controles positifs : le detecteur DOIT mordre -------------------------


def test_mord_sur_named_split():
    """« Lecture ... » puis « Lecture chiffree ... » : le defaut nomme par le user (#16554)."""
    findings = detect(nb(
        md("### Lecture du resultat\nConvergence nette vers l'optimum."),
        md("### Lecture chiffree du resultat\nLe score atteint 0.94 en 40 iterations."),
    ))
    assert [f["type"] for f in findings] == ["named_split"]
    assert findings[0]["cells"] == [0, 1]


def test_mord_sur_generic_pair():
    """Deux cellules de lecture consecutives, donc sur la MEME sortie amont (aucun code entre).

    En-tetes differents mais tous deux d'interpretation : c'est le cas generique,
    celui qui n'est pas nomme « chiffree ».
    """
    findings = detect(nb(
        md("### Lecture du resultat\nConvergence nette vers l'optimum."),
        md("### Analyse de la sortie\nLe score atteint 0.94 en 40 iterations."),
    ))
    assert [f["type"] for f in findings] == ["generic_pair"]
    assert findings[0]["cells"] == [0, 1]


def test_mord_sur_separated_by_code():
    """Variante secondaire : le couple est separe par UNE cellule de code."""
    findings = detect(nb(
        md("### Lecture du resultat\nConvergence nette."),
        code("print(solve())"),
        md("### Lecture chiffree du resultat\nLe score atteint 0.94."),
    ))
    assert [f["type"] for f in findings] == ["separated_by_code"]
    assert findings[0]["cells"] == [0, 2]


def test_les_findings_portent_les_metriques_de_recouvrement():
    """Chaque finding porte Jaccard + containment : le recensement mesure, il ne juge pas.

    Les deux cellules sont ici **identiques** (titre et prose) : le recouvrement est
    maximal. Le cas ou les en-tetes different -- donc ou le Jaccard est < 1 sans que
    le containment le soit -- est couvert par `test_mord_sur_generic_pair`.
    """
    (f,) = detect(nb(
        md("### Analyse de la sortie\nConvergence nette du solveur."),
        md("### Analyse de la sortie\nConvergence nette du solveur."),
    ))
    assert f["type"] == "generic_pair"
    assert f["jaccard"] == 1.0
    assert f["rare_containment"] == 1.0
    assert f["shared_rare_words"] > 0
    assert isinstance(f["shared_rare_sample"], list)


# --- 2. Controles negatifs : le detecteur ne doit PAS mordre ------------------


def test_ne_mord_pas_sur_prose_ordinaire_consecutive():
    """Controle negatif : deux paragraphes de prose consecutifs ne sont pas une paire de lectures."""
    assert detect(nb(
        md("### Introduction\nLe probleme du voyageur de commerce."),
        md("### Mise en place du modele\nOn definit les variables de decision."),
    )) == []


def test_ne_mord_pas_sur_lectures_separees_par_code_non_nommees():
    """La seconde lecture n'est pas nommee « chiffree » : rien a signaler.

    Les deux cellules interpretent des sorties DIFFERENTES (le code les separe) :
    c'est legal. Ni la regle consecutive (du code les separe) ni la regle
    `separated_by_code` (qui exige un second en-tete « Lecture chiffree ») ne
    s'appliquent.
    """
    assert detect(nb(
        md("### Lecture du premier essai\nConvergence en 40 iterations."),
        code("print(solve(seed=1))"),
        md("### Analyse du second essai\nLe bruit domine l'ecart."),
    )) == []


def test_ne_mord_pas_sur_carnet_clean():
    assert detect(nb(
        code("print(1)"),
        md("### Lecture du resultat\nUne seule lecture, rien a fusionner."),
    )) == []


def test_trois_lectures_consecutives_donnent_deux_paires_et_rien_a_deux_pas():
    """La fenetre [i, i+2] n'est PAS une paire : sans code au milieu, rien a signaler a deux pas."""
    findings = detect(nb(
        md("### Lecture premiere\nConvergence."),
        md("### Analyse seconde\nLe score atteint 0.94."),
        md("### Analyse troisieme\nLe score atteint 0.98."),
    ))
    assert [f["cells"] for f in findings] == [[0, 1], [1, 2]]


def test_ne_mord_pas_si_deux_cellules_de_code_separent():
    """`separated_by_code` exige UNE cellule de code, pas deux."""
    assert detect(nb(
        md("### Lecture du resultat\nConvergence."),
        code("print(1)"),
        code("print(2)"),
        md("### Lecture chiffree du resultat\nLe score atteint 0.94."),
    )) == []


# --- 3. Seuils epingles ------------------------------------------------------


def test_max_df_est_epingle():
    """Le seuil de rarete est une constante publique : le figer ici le rend visible au refactor."""
    assert MAX_DF == 4


def test_seuil_max_df_ecarte_un_mot_devenu_repandu():
    """Le MEME couple, mesure deux fois : seul le seuil de rarete change le verdict.

    Le seul mot partage (`zalgo`) est rare et unique quand il n'apparait que dans
    ces deux cellules : containment 0.5. En ajoutant trois cellules qui le
    reprennent, il depasse MAX_DF, cesse d'etre « rare », et le containment tombe
    a 0 -- tandis que le Jaccard, qui ne depend pas du seuil, ne bouge pas. C'est
    le seuil qui est mesure, pas la formule.
    """
    pair = [md("alpha zalgo"), md("beta zalgo")]

    rare = overlap_metrics({"cells": pair}, 0, 1)
    assert rare["shared_rare_words"] == 1
    assert rare["rare_containment"] == 0.5
    assert rare["jaccard"] == 0.333

    repandu = overlap_metrics(
        {"cells": pair + [md("zalgo gamma"), md("zalgo delta"), md("zalgo epsilon")]}, 0, 1
    )
    assert repandu["shared_rare_words"] == 0
    assert repandu["rare_containment"] == 0.0
    assert repandu["jaccard"] == 0.333


def test_recouvrement_nul_sur_vocabulaires_disjoints():
    metrics = overlap_metrics({"cells": [md("alpha zalgo"), md("beta quux")]}, 0, 1)
    assert metrics["jaccard"] == 0.0
    assert metrics["rare_containment"] == 0.0


def test_recouvrement_vide_ne_divise_pas_par_zero():
    """Deux cellules markdown sans mot plein : 0.0, pas une ZeroDivisionError."""
    metrics = overlap_metrics({"cells": [md("### Lecture"), md("### Analyse")]}, 0, 1)
    assert metrics["jaccard"] == 0.0
    assert metrics["rare_containment"] == 0.0


def test_cell_title_nettoie_les_marques_markdown():
    assert cell_title("## Lecture du resultat\nsuite") == "Lecture du resultat"
    assert cell_title("###  Analyse des resultats") == "Analyse des resultats"
    assert cell_title("\n\n### Lecture\nsuite") == "Lecture"


@pytest.mark.parametrize("title", [
    "### Lecture du resultat",
    "### Lecture chiffree du resultat",
    "### Analyse des resultats",
    "### Analyse",
])
def test_racines_d_interpretation_reconnues(title):
    assert is_interpretation_title(cell_title(title + "\nune lecture."))


@pytest.mark.parametrize("title", [
    "### Introduction",
    "### Mise en place du modele",
    "### Resultats",
    "### Discussion",
    "### Exercice 1",
])
def test_titres_non_interpretatifs_non_reconnus(title):
    assert not is_interpretation_title(cell_title(title + "\nune lecture."))


def test_named_second_cible_la_forme_chiffree():
    assert is_named_second(cell_title("### Lecture chiffree du resultat"))
    assert not is_named_second(cell_title("### Lecture du resultat"))


# --- 3 bis. Bornes connues, epinglees en xfail strict ------------------------


@pytest.mark.xfail(
    strict=True,
    reason=(
        "#17134 : le `\\b` place apres `interpre` fait echouer la reconnaissance de "
        "« Interpretation » -- le titre d'interpretation dominant du corpus "
        "(133 paires invisibles dans 78 carnets, mesure 2026-09-21)."
    ),
)
def test_borne_connue_interpretation_nue_est_invisible():
    """`### Interpretation` est un en-tete d'interpretation au sens de la docstring de l'organe.

    Ce test ECHOUE aujourd'hui. Il rend le defaut visible sans rougir la suite, et
    passera en XPASS (donc en echec) le jour du fix #17134 : retirer le marqueur
    alors, pas l'ajuster.
    """
    assert is_interpretation_title(cell_title("### Interpretation\nconvergence nette."))
    assert detect(nb(
        md("### Interpretation\nConvergence nette vers l'optimum."),
        md("### Interpretation\nLe score atteint 0.94."),
    )) == [{"placeholder": True}]


@pytest.mark.xfail(
    strict=True,
    reason=(
        "Borne connue (meme famille que #17134) : `cell_title` s'arrete sur la premiere "
        "ligne non vide, donc une cellule qui ouvre sur la ligne de separation `***` rend "
        "un titre vide -- elle est invisible au detecteur meme si son en-tete est une lecture. "
        "Cas rencontre a chaque repli de conclusion de la campagne #17066."
    ),
)
def test_borne_connue_cellule_ouvrant_sur_separateur_est_invisible():
    assert cell_title("***\n\n## Lecture du resultat") == "Lecture du resultat"


# --- 4. Interface CLI : 0 = clean, 1 = fichier illisible, 2 = findings --------


def _write(path, notebook):
    path.write_text(json.dumps(notebook, ensure_ascii=False), encoding="utf-8")
    return path


def test_cli_fichier_clean_rc0_et_affiche_clean(tmp_path, capsys):
    target = _write(tmp_path / "clean.ipynb", nb(
        code("print(1)"), md("### Lecture du resultat\nUne seule lecture.")))
    assert main([str(target)]) == 0
    assert capsys.readouterr().out.strip() == "clean"


def test_cli_le_recensement_ne_bloque_pas_mais_le_cliquet_bloque(tmp_path):
    """Sans `--fail-on-findings` l'organe recense (rc 0) ; avec, il bloque (rc 2)."""
    target = _write(tmp_path / "sale.ipynb", nb(
        md("### Lecture du resultat\nConvergence."),
        md("### Analyse de la sortie\nLe score atteint 0.94."),
    ))
    assert main([str(target)]) == 0
    assert main([str(target), "--fail-on-findings"]) == 2


def test_cli_json_rend_les_findings_structures(tmp_path, capsys):
    target = _write(tmp_path / "sale.ipynb", nb(
        md("### Lecture du resultat\nConvergence."),
        md("### Analyse de la sortie\nLe score atteint 0.94."),
    ))
    assert main([str(target), "--json"]) == 0
    rows = json.loads(capsys.readouterr().out)
    assert [r["type"] for r in rows] == ["generic_pair"]
    assert rows[0]["cells"] == [0, 1]
    assert "jaccard" in rows[0] and "rare_containment" in rows[0]


def test_cli_chemin_introuvable_rc1(tmp_path, capsys):
    assert main([str(tmp_path / "absent.ipynb")]) == 1
    assert "introuvable" in capsys.readouterr().err


DIRTY_PAIR = (md("### Lecture du resultat\nConvergence."),
              md("### Analyse de la sortie\nLe score atteint 0.94."))


def test_cli_dossier_compte_les_carnets_et_ignore_les_dossiers_exclus(tmp_path, capsys):
    """Les cinq dossiers exclus sont exclus -- et les carnets qu'ils contiennent AURAIENT mordu.

    Sans l'exclusion le total serait 6 : le chiffre mesure donc bien l'exclusion, pas
    une absence de finding.
    """
    _write(tmp_path / "ok.ipynb", nb(*DIRTY_PAIR))
    for excluded in (".ipynb_checkpoints", "_output", ".lake", "node_modules", "_peters"):
        dossier = tmp_path / excluded
        dossier.mkdir()
        _write(dossier / "sale.ipynb", nb(*DIRTY_PAIR))

    assert main([str(tmp_path)]) == 0
    out = capsys.readouterr().out
    assert "Total : 1" in out
    assert "Total : 6" not in out


def test_cli_dossier_avec_fail_on_findings_rc2(tmp_path):
    _write(tmp_path / "sale.ipynb", nb(*DIRTY_PAIR))
    assert main([str(tmp_path), "--fail-on-findings"]) == 2
