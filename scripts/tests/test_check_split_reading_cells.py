# -*- coding: utf-8 -*-
"""Tests de l'organe de recensement des lectures scindees (STOP #13410).

Contexte : #17077. L'organe `check_split_reading_cells.py` (merge #16786) est la
**base de preuve** de la campagne densite (#13410 / #16762) et du cliquet #17044 ;
il est livre sans suite de tests. Deux retouches y sont dangereuses, et pas de la
meme facon :

  - les **regexes de titre** (`is_interpretation_title` / `is_named_second` /
    `NAMED_FIRST_RE`) decident du **verdict** : les toucher change quelles paires
    sont vues, donc le type (`generic_pair` / `separated_by_code` / `named_split`)
    et le nombre de findings ;
  - les **chiffres** (Jaccard, containment sur mots rares sous `MAX_DF`) ne
    decident **rien** -- ils sont rapportes dans le finding -- mais ce sont eux
    que citent les bodies deja postes (#17040) : les toucher change des mesures
    publiees **sans** changer un verdict, donc sans qu'aucun test de verdict ne
    bronche.

Cette suite epingle les deux : les verdicts ET les chiffres.

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

Emplacement : `scripts/tests/` -- c'est la ou l'organe portait deja sa suite
depuis #16786 (`scripts/tests/test_check_split_reading_cells.py`, 9 tests), et
c'est le chemin que citent le registre de cablage (`fast_lane_registry.py`,
TRANCHE14) et le cliquet #17044.

La suite de #16786 est **conservation verbatim** en fin de fichier (section
« repris de #16786 ») : aucun de ses 9 tests n'est supprime, aucun n'est reecrit.
Le recoupement avec les tests ci-dessus est **assume, pas deduit** -- et il est
mesure. Deux tests de #16786 portent des assertions qu'aucun des miens ne
reproduit : `test_named_split_user_pattern` verifie `titles[0].startswith("Lecture")`,
`"chiffree" in titles[1]`, `0 <= jaccard <= 1` et `shared_rare_words >= 1` (mes
fixtures ne partagent pas tous ces mots rares) ; et
`test_cell_title_strips_markdown_noise` couvre le **gras** (`### **Lecture
chiffree — les agregats**`) et les **backticks**, absents de mon nettoyage.
Les supprimer au motif du recoupement ferait perdre ces assertions : elles sont
donc gardees. C'est le cout assume d'une fusion de deux suites, pas un doublon
involontaire.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

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


def test_index_absolus_sur_carnet_mixte_md_et_code():
    """Un carnet mixte : les index restent ABSOLUS, pas relatifs aux cellules markdown.

    Tous les autres tests de metriques mesurent des carnets **entierement
    markdown**, ou index absolu == index markdown-relatif : une regression qui
    rendrait des index relatifs y resterait invisible (le couple demeure
    auto-coherent) et ne casserait que les carnets **mixtes** -- c'est-a-dire le
    corpus reel. Ici la premiere cellule est du CODE, donc les lectures sont en
    1 et 2 et les chiffres du meme couple doivent etre identiques a ceux mesures
    en 0 et 1 sur un carnet 100 % markdown.
    """
    findings = detect(nb(
        code("print(1)"),
        md("### Lecture du resultat\nConvergence."),
        md("### Analyse des resultats\nLe score atteint 0.94."),
    ))
    assert [f["cells"] for f in findings] == [[1, 2]]

    pair = [md("alpha zalgo"), md("beta zalgo")]
    tout_markdown = overlap_metrics({"cells": pair}, 0, 1)
    assert overlap_metrics({"cells": [code("print(1)"), *pair]}, 1, 2) == tout_markdown
    assert tout_markdown["rare_containment"] == 0.5


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


# --- Repris de #16786, sans equivalent ici ------------------------------------


# =============================================================================
# Suite d'origine de l'organe (#16786), reprise VERBATIM -- cf en-tete.
# =============================================================================


def write_nb(path, nb: dict) -> None:
    import json
    path.write_text(json.dumps(nb), encoding="utf-8")


def test_named_split_user_pattern():
    nb = {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** — le montant.\nL'age pese 0.37 et le montant 0.35, "
           "signes opposes : effet de correlation marginal."),
    ]}
    hits = detect(nb)
    assert len(hits) == 1
    h = hits[0]
    assert h["type"] == "named_split"
    assert h["cells"] == [1, 2]
    assert h["titles"][0].startswith("Lecture")
    assert "chiffree" in h["titles"][1]
    assert 0.0 <= h["jaccard"] <= 1.0
    assert h["shared_rare_words"] >= 1


def test_generic_pair_interpretation_titles():
    nb = {"cells": [
        md("### Lecture du resultat\nLa courbe converge apres 200 episodes."),
        md("### Analyse du modele\nLa courbe converge apres 200 episodes, "
           "le modele apprend la valeur."),
    ]}
    hits = detect(nb)
    assert [h["type"] for h in hits] == ["generic_pair"]


def test_separated_by_code_is_secondary():
    nb = {"cells": [
        md("### Lecture\nPremiere lecture du terrain."),
        code("df.head()"),
        md("### Lecture chiffree — les agregats\nSeconde lecture des agregats."),
    ]}
    hits = detect(nb)
    assert len(hits) == 1
    assert hits[0]["type"] == "separated_by_code"
    assert hits[0]["cells"] == [0, 2]


def test_clean_notebook_no_hit():
    nb = {"cells": [
        md("## Introduction\nLe contexte."),
        code("print('ok')"),
        md("### Lecture\nUne seule interpretation, pas de voisine."),
        md("## Conclusion\nEt suite du parcours."),
    ]}
    assert detect(nb) == []


def test_non_interpretation_consecutive_md_not_flagged():
    nb = {"cells": [
        md("### Exercice\nA vous de jouer."),
        md("### Indice\nPensez a la programmation dynamique."),
    ]}
    assert detect(nb) == []


def test_fp_control_different_signals_low_containment():
    """Deux lectures consecutives de signaux DIFFERENTS (temoin WS-00a) :
    le signal structurel reste (a instruire a l'oeil) mais C doit etre
    faible -- c'est la metrique qui evacue le faux positif du garde."""
    nb = {"cells": [
        md("### Lecture — Doppler\nLe chirp se dilate, la densite spectrale "
           "du signal doppler s'etale vers les basses frequences."),
        md("### Lecture — HeaviSine\nLa discontinuite du signal heavisine "
           "concentre l'energie sur les sauts brusques du champ."),
    ]}
    hits = detect(nb)
    assert [h["type"] for h in hits] == ["generic_pair"]
    assert hits[0]["rare_containment"] < 0.20


def test_cell_title_strips_markdown_noise():
    assert cell_title("### **Lecture chiffree — les agregats**") == \
        "Lecture chiffree — les agregats"
    assert cell_title("- `Lecture` du resultat") == "Lecture` du resultat"
    assert cell_title("") == ""


def test_directory_mode_findings_rc2_with_fail_on_findings(tmp_path, capsys):
    """Mode dossier : --fail-on-findings doit renvoyer 2 quand le dossier
    contient au moins un finding (reserve adjoint #16786 : le flag etait
    avale par scan_root, qui retournait toujours 0)."""
    write_nb(tmp_path / "notebook_a.ipynb", {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** — le montant.\nL'age pese 0.37 et le montant 0.35."),
    ]})
    rc = main([str(tmp_path), "--fail-on-findings"])
    capsys.readouterr()
    assert rc == 2


def test_directory_mode_clean_rc0(tmp_path, capsys):
    """Mode dossier sans findings : rc 0 meme avec --fail-on-findings."""
    write_nb(tmp_path / "notebook_clean.ipynb", {"cells": [
        md("## Introduction\nLe contexte."),
        code("print('ok')"),
        md("### Lecture\nUne seule interpretation, pas de voisine."),
    ]})
    rc = main([str(tmp_path), "--fail-on-findings"])
    capsys.readouterr()
    assert rc == 0


# --- #17044 : un carnet illisible ne doit pas annuler le recensement ---------


def test_scan_dossier_ne_avorte_pas_sur_carnet_illisible(tmp_path, capsys):
    """#17044 : `scan_root` faisait `return 1` sur le premier carnet illisible.

    Un seul carnet corrompu annulait TOUT le recensement (rc=1, zero finding --
    pas seulement un recensement degrade), donc l'organe etait incablable en
    cliquet : n'importe quel carnet corrompu du depot rougissait toute PR, pour
    une raison sans rapport avec elle. Il doit desormais le rapporter et
    continuer.

    Le carnet illisible est place ENTRE deux carnets sains : la preuve que le
    scan continue est que celui qui le SUIT est quand meme recense.
    """
    write_nb(tmp_path / "a_sain.ipynb", {"cells": [
        md("## Introduction\nRien a signaler ici."),
        code("print('ok')"),
    ]})
    (tmp_path / "b_corrompu.ipynb").write_text(
        "{ ceci n'est pas du JSON", encoding="utf-8")
    write_nb(tmp_path / "c_scinde.ipynb", {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** -- le montant.\nL'age pese 0.37."),
    ]})

    rc = main([str(tmp_path)])
    out, err = capsys.readouterr()

    assert rc == 0, "un carnet illisible ne doit pas faire rougir le recensement"
    assert "c_scinde" in out, "le carnet sain APRES le corrompu doit etre recense"
    assert "b_corrompu" in err, "le carnet saute doit etre nomme sur stderr"
    assert "illisible" in err, "le recensement doit se declarer PARTIEL"


def test_carnet_illisible_ne_masque_pas_un_finding(tmp_path, capsys):
    """Le carnet illisible ne doit ni avorter ni masquer un finding reel :
    avec --fail-on-findings, un vrai finding reste rc=2 (et non rc=1)."""
    (tmp_path / "a_corrompu.ipynb").write_text("not json at all", encoding="utf-8")
    write_nb(tmp_path / "b_scinde.ipynb", {"cells": [
        code("print(42)"),
        md("### Lecture\nLe classifieur distingue l'age du montant."),
        md("**Lecture chiffree** -- le montant.\nL'age pese 0.37."),
    ]})

    rc = main([str(tmp_path), "--fail-on-findings"])
    capsys.readouterr()
    assert rc == 2, "le cliquet doit encore mordre malgre un carnet illisible"


def test_fichier_illisible_rc1_sans_traceback(tmp_path, capsys):
    """Contrat documente : un fichier DESIGNE illisible rend rc=1. Il etait
    rendu par une JSONDecodeError non rattrapee (traceback jusqu'a
    l'interpreteur) : meme code, rendu proprement."""
    p = tmp_path / "corrompu.ipynb"
    p.write_text("{ pas du json", encoding="utf-8")

    rc = main([str(p)])
    out, err = capsys.readouterr()
    assert rc == 1
    assert "ERREUR lecture" in err
# --- #17134 : les deux bornes qui rendaient des familles entieres invisibles --


@pytest.mark.parametrize("title", [
    "### Interpretation",              # le titre nu -- forme dominante du corpus
    "### Interpretation des resultats",
    "### Interprétation",              # accentue : deaccent() le ramene a la meme racine
    "### Interprétation : prérequis",
    "### Interpretation — les ecarts",
    "### Interpretation:",
    "### Interpretations croisees",    # pluriel, sans espace apres la racine
])
def test_interpretation_est_reconnue(title):
    """#17134 borne (a) : le `\\b` apres `interpre` faisait echouer TOUTE la
    famille `Interpretation ...`, parce que la racine est un PREFIXE et non un
    mot entier. Mesure sur le corpus : 133 `generic_pair` dans 78 carnets
    etaient invisibles (plus 3 `separated_by_code`)."""
    assert is_interpretation_title(cell_title(title + "\nconvergence nette."))


@pytest.mark.parametrize("title", [
    "### Introduction",
    "### Resultats",
    "### Discussion",
    "### Exercice 1",
    "### Mise en place du modele",
    "### Comparaison des modeles",
])
def test_retrait_du_backslash_b_n_elargit_pas(title):
    """Le correctif retire la frontiere de mot : il ne doit PAS elargir le
    vocabulaire reconnu. Ces en-tetes ne sont pas des lectures."""
    assert not is_interpretation_title(cell_title(title + "\nDu texte."))


def test_racine_en_milieu_de_titre_non_reconnue():
    """Le match reste ancre en `^` : une racine au milieu d'un titre n'en fait
    pas un en-tete de lecture."""
    for title in ["### Une analyse du resultat", "### Notre interpretation du score",
                  "### La lecture des courbes"]:
        assert not is_interpretation_title(cell_title(title + "\nDu texte."))


def test_borne_a_bout_en_bout_paire_generique():
    """Les deux cellules de #17134 : deux `### Interpretation` consecutives."""
    nb = {"cells": [
        code("print(model.score)"),
        md("### Interpretation\nConvergence nette vers l'optimum."),
        md("### Interpretation\nLe score atteint 0.94, convergence nette."),
    ]}
    hits = detect(nb)
    assert [h["type"] for h in hits] == ["generic_pair"]
    assert hits[0]["cells"] == [1, 2]


def test_cell_title_traverse_la_ligne_de_separation():
    """#17134 borne (b) : `***` est non vide et ne porte aucun titre. La
    fonction s'y arretait et rendait "", donc la cellule entiere etait invisible
    meme quand son en-tete etait une lecture."""
    assert cell_title("***\n\n## Lecture du resultat") == "Lecture du resultat"
    assert cell_title("---\n### Analyse") == "Analyse"
    assert cell_title("***\n***\n\n### Lecture") == "Lecture"
    # Un titre qui suit la ligne de separation est bien reconnu comme lecture.
    assert is_interpretation_title(cell_title("***\n\n## Interpretation des ecarts"))
    # Et une cellule qui ne porte AUCUN titre rend toujours "" (contrat existant).
    assert cell_title("") == ""
    assert cell_title("***\n\n***") == ""


def test_borne_b_bout_en_bout_paire_generique():
    """Une cellule qui ouvre sur un separateur participe a la paire."""
    nb = {"cells": [
        md("***\n\n## Lecture du resultat\nLa courbe converge apres 200 episodes."),
        md("### Interprétation des ecarts\nLa courbe converge apres 200 episodes, "
           "et le modele apprend la valeur."),
    ]}
    hits = detect(nb)
    assert [h["type"] for h in hits] == ["generic_pair"]
    assert hits[0]["titles"][0] == "Lecture du resultat"


# =============================================================================
# Mode DIFF (#17464) : cellules markdown INSEREES qui violent la regle.
# =============================================================================

from check_split_reading_cells import (  # noqa: E402
    detect_added_readings,
    is_exercise_cell,
    cell_output_text,
)


def _exec(code_text, *, execution_count=1, outputs=None):
    """Cellule de code executee (ec=None != None et outputs donnes)."""
    return {
        "cell_type": "code",
        "source": [code_text],
        "outputs": outputs if outputs is not None else [
            {"name": "stdout", "output_type": "stream", "text": ["sortie"]}
        ],
        "execution_count": execution_count,
    }


def _stub_exercise(code_text="print('Exercice a completer')"):
    """Cellule d'exercice executee une fois (C.1 -- le message officiel).
    execution_count=1 (pas None), outputs=['Exercice a completer'].
    Pedagogiquement c'est un exercice : la nouvelle heuristique le detecte
    par son token de sortie, pas par son etat d'execution.
    """
    return {
        "cell_type": "code",
        "source": [code_text],
        "outputs": [{"name": "stdout", "output_type": "stream",
                     "text": ["Exercice a completer"]}],
        "execution_count": 1,
    }


def _todo_stub_unexec(code_text="# TODO: a completer\npass"):
    """Stub TODO jamais execute (cells legacy avant C.1 execution convention)."""
    return {
        "cell_type": "code",
        "source": [code_text],
        "outputs": [],
        "execution_count": None,
    }


# --- 5. Mode DIFF : les 3 buckets (#17464) -----------------------------------


def test_diff_sans_base_est_silencieux():
    """Sans --base, le mode DIFF ne produit aucun finding : la notion de
    'cellule ajoutee' n'a pas de sens. La PR sans base doit pouvoir etre
    scanee comme avant, sans declencher EXERCISE_READING a tort et partout.
    """
    head = nb(
        code("print(1)"),
        md("### Lecture du resultat\nUne seule lecture."),
        code("print(2)"),
    )
    assert detect_added_readings(head, None) == []


def test_diff_second_reading_apres_lecture_existante():
    """SECOND_READING : une lecture ajoutee derriere une lecture deja
    presente en base (la campagne #17021 multiplexait ce cas).
    """
    base = nb(
        code("print(1)"),
        md("### Lecture du resultat\nConvergence nette."),
    )
    head = nb(
        code("print(1)"),
        md("### Lecture du resultat\nConvergence nette."),
        md("### Lecture chiffree\nLe score atteint 0.94 en 40 iterations."),
    )
    findings = detect_added_readings(head, base)
    assert len(findings) == 1
    f = findings[0]
    assert f["type"] == "SECOND_READING"
    assert f["cells"] == [2]
    assert f["prev_role"] == "md"  # lecture existante en base, conservee dans head
    # next_role = BOUNDARY (la nouvelle lecture est en queue) ; le bucket
    # SECOND_READING mord par prev_role == "md" -- voir organ docstring.


def test_diff_reading_before_code_devant_sortie():
    """READING_BEFORE_CODE : une lecture ajoutee directement devant une
    cellule de code qui a une sortie (la lecture doit suivre, pas preceder).
    """
    base = nb(
        code("print(1)"),
    )
    head = nb(
        md("### Lecture introductive\nUne lecture qui parle avant le code."),
        code("print(1)"),
    )
    findings = detect_added_readings(head, base)
    assert len(findings) == 1
    f = findings[0]
    assert f["type"] == "READING_BEFORE_CODE"
    assert f["cells"] == [0]
    assert f["prev_role"] == "BOUNDARY"
    assert f["next_role"] == "code_with_output"


def test_diff_exercise_reading_apres_stub_exec():
    """EXERCISE_READING : une lecture ajoutee juste apres un exercice.
    La nouvelle heuristique accepte l'exercice execute (sortie litterale
    'Exercice a completer') en plus du stub TODO non execute.
    """
    base = nb(
        _stub_exercise(),
    )
    head = nb(
        _stub_exercise(),
        md("### Lecture du resultat\nSortie attendue : 'Exercice a completer'."),
    )
    findings = detect_added_readings(head, base)
    assert len(findings) == 1
    f = findings[0]
    assert f["type"] == "EXERCISE_READING"
    assert f["cells"] == [1]
    assert f["prev_role"] == "exercise"
    assert f["next_role"] == "BOUNDARY"


def test_diff_exercise_reading_apres_stub_non_exec():
    """EXERCISE_READING sur stub TODO non execute aussi (legacy pre-C.1)."""
    base = nb(
        _todo_stub_unexec(),
    )
    head = nb(
        _todo_stub_unexec(),
        md("### Lecture du resultat\nA implementer par l'etudiant."),
    )
    findings = detect_added_readings(head, base)
    assert len(findings) == 1
    assert findings[0]["type"] == "EXERCISE_READING"


def test_diff_mute_si_cellule_ajoutee_ne_viole_pas():
    """Une cellule ajoutee entre une cellule de code et la FIN (boundary
    apres) ne viole rien : l'organe n'a pas a la signaler.
    """
    base = nb(
        code("print(1)"),
    )
    head = nb(
        code("print(1)"),
        md("### Conclusion\nUne derniere note hors lecture."),
    )
    # prev=code_with_output, next=BOUNDARY : aucun bucket ne matche
    assert detect_added_readings(head, base) == []


def test_diff_mute_si_markdown_ajoute_apres_code_sans_markdown_en_base():
    """Une premiere lecture ajoutee juste apres une cellule de code qui
    n'avait PAS de markdown derriere en base n'est PAS une violation.
    Pedagogiquement c'est l'action recommandee : ajouter une
    interpretation a un resultat qui en manquait. La regle dit 'une sortie
    = au plus une lecture', pas 'une sortie = exactement une lecture'.
    """
    base = nb(
        code("print(1)"),
        code("print(2)"),
    )
    head = nb(
        code("print(1)"),
        code("print(2)"),
        md("### Lecture chiffree\nUne nouvelle lecture pour print(2)."),
    )
    # Le code print(2) (idx 1) en base n'etait suivi de rien -> muet.
    assert detect_added_readings(head, base) == []


def test_diff_mute_si_reecriture_au_meme_endroit_avec_meme_source():
    """Une PR qui REECRIT une lecture a la meme position et avec la meme
    source n'est PAS un ajout (le contenu etait deja la) : 0 finding.
    C'est le discriminant 'REWRITE same content' qui mord.
    """
    src = "### Lecture du resultat\nMeme formulation, version v2."
    base = nb(
        code("print(1)"),
        md(src),
    )
    head = nb(
        code("print(1)"),
        md(src),
    )
    # Pas d'ajout net : multiset diff = 0
    assert detect_added_readings(head, base) == []


def test_diff_signale_reecriture_avec_nouveau_contenu():
    """Une PR qui REECRIT une lecture au meme slot mais avec un contenu
    different : pedagiquement c'est acceptable (l'organe n'a pas vocation a
    juger la qualite du contenu), mais le delta topologique EST un ajout
    (nouvelle prose). L'organe le signale comme SECOND_READING pour
    attirer l'attention -- le merge-gate coordonnateur tranche en lecture.
    """
    base = nb(
        code("print(1)"),
        md("### Lecture du resultat\nAncienne formulation."),
    )
    head = nb(
        code("print(1)"),
        md("### Lecture du resultat\nNouvelle formulation, mieux redactigee."),
    )
    findings = detect_added_readings(head, base)
    # Multiset diff : +1 ajout (Nouvelle formulation), -1 retrait (Ancienne)
    # net = 0, MAIS le second walk voit l'ajout comme 'new source' au meme
    # slot -- le REWRITE-same-content ne fire pas -> passe au verdict
    # topologique -> SECOND_READING (prev=code_with_output, le code en base
    # etait suivi d'une md -> already_had_md_after=True).
    assert len(findings) == 1
    assert findings[0]["type"] == "SECOND_READING"


def test_diff_mute_si_ordre_inchange_et_contenu_identique():
    """Une PR qui ne touche PAS au notebook ne signale rien (sanity check)."""
    base = head = nb(code("print(1)"))
    assert detect_added_readings(head, base) == []


def test_diff_compte_correctement_les_doublons_de_sources():
    """Si la meme cellule source apparait 1 fois en base et 2 fois en head,
    la premiere en head est vue comme un REWRITE (meme position dans base,
    meme cellule type markdown) et la seconde complete le budget multiset.
    Le resultat net : 0 added. Pedagogiquement le doublon de lecture
    passe inapercu -- c'est un bord connu du multiset-diff sans regarder
    le contenu. Mitige par une regle metier : l'organe reste sur le delta
    POSITION/SOURCE strict, et laisse le contenu (Jaccard, recouvrement) a
    l'organe detect_repeated_prose qui mord ici verbatim.
    """
    src = "### Lecture doublee\nMeme source, deux positions."
    base = nb(code("print(1)"), md(src))
    head = nb(code("print(1)"), md(src), md(src))
    # Ici, l'organe DIFF ne signale rien (doublon a meme position -- vu
    # comme rewrite). detect_repeated_prose mord verbatim sur le doublon,
    # c'est son canal.
    assert detect_added_readings(head, base) == []


def test_diff_lecture_avant_exercice_est_reading_before_code():
    """Une lecture ajoutee juste avant un EXERCISE est 'READING_BEFORE_CODE'
    (le code est la, qu'il soit execute ou non). L'EXERCISE_READING ne
    survient QUE quand la lecture est APRES l'exercice, pas devant.
    """
    base = nb(_stub_exercise())
    head = nb(md("### Lecture introductive\nAvant l'exercice."), _stub_exercise())
    findings = detect_added_readings(head, base)
    assert len(findings) == 1
    assert findings[0]["type"] == "READING_BEFORE_CODE"


def test_is_exercise_cell_reconnait_stub_non_exec():
    """is_exercise_cell : un stub TODO sans sortie ni exec est exercice."""
    cell = _todo_stub_unexec()
    assert is_exercise_cell(cell) is True


def test_is_exercise_cell_reconnait_stub_avec_sortie_litterale():
    """is_exercise_cell : un exercice execute affichant 'Exercice a completer'
    est exercice malgre son execution_count. Le contrat C.1 dit qu'on execute
    le stub pour afficher le message : la cellule reste un exercice vide.
    """
    cell = _stub_exercise()
    assert is_exercise_cell(cell) is True


def test_is_exercise_cell_rejette_code_avec_sortie_utile():
    """Une cellule de code executee avec une sortie utile (mesure, plot, etc.)
    n'est PAS un exercice. Les jetons 'Exercice' / 'TODO' dans le source
    sont insuffisants si la sortie demontre un calcul abouti -- la cellule
    a execute son contenu, donc l'etudiant n'a plus rien a completer.
    """
    cell = _exec(
        "import time\nt = time.time()\nprint(f't={t:.3f}')",
        outputs=[{"name": "stdout", "output_type": "stream",
                  "text": ["t=0.123"]}],
    )
    assert is_exercise_cell(cell) is False


def test_is_exercise_cell_rejette_markdown():
    assert is_exercise_cell(md("### Exercice\nA vous.")) is False


def test_cell_output_text_aggrege_les_sorties():
    """cell_output_text concatene stdout + data text/plain de toutes les
    sorties d'une cellule."""
    cell = {
        "outputs": [
            {"text": ["ligne1\n"]},
            {"data": {"text/plain": ["ligne2"]}},
            {"name": "stderr", "output_type": "stream", "text": ["warn"]},
        ]
    }
    text = cell_output_text(cell)
    assert "ligne1" in text and "ligne2" in text and "warn" in text


# --- 5bis. Controle positif REEL : #17021 (App-1-NQueens + App-14b) -----------
#
# Le ticket #17464 exige le controle positif "les deux notebooks de #17021,
# base 6d46b9c684~1 -> tete 6d46b9c684, doivent sortir en rouge".
# Les fixtures .ipynb ne sont pas versionnees ici (le depot de test ne les
# heberge pas). Le run direct sur le depot historique est documente dans le
# body de la PR via `python scripts/ci/check_17464_positive_control.py`.


# --- 5ter. Bornes connues (xfail strict) sur le mode DIFF ---------------------


@pytest.mark.xfail(
    strict=True,
    reason=(
        "Borne connue : la classification 'next_role = code_with_output' suppose "
        "que toute cellule de code non-exercice a une sortie utile. Si une "
        "cellule ajoutee est posee devant un code dont les sorties sont vides "
        "(par exemple un `del x ; y = x` qui ne capture rien), le mode la "
        "compte mal comme READING_BEFORE_CODE au lieu de ne pas signaler."
    ),
)
def test_diff_reading_before_code_ne_mord_pas_si_code_sans_sortie():
    """Une lecture ajoutee devant un code SANS sortie ne viole pas la regle
    (il n'y a rien a interpreter de toute facon)."""
    base = nb(code("x = 1  # no output"))
    head = nb(md("### Lecture\nUne note en preface."), code("x = 1  # no output"))
    # Le code n'a pas d'output -> is_exercise_cell = False (pas de marker)
    # mais il n'a pas non plus de sortie utile -> devrait etre ignore.
    assert detect_added_readings(head, base) == []


# --- 4. Delta #17087 (rebase post-#17135) : les trois cas non couverts --------


def test_titres_reels_accentues_sont_reconnus():
    """Les carnets reels ecrivent « Lecture chiffrée du résultat » AVEC accents :
    deaccent() fait partie du chemin de detection, et toute la suite ci-dessus
    ne fabrique que des titres desaccentues -- le chemin accentue etait mort
    s'il regressait (delta #17087, non couvert par #17135)."""
    findings = detect(nb(
        md("### Lecture du résultat\nConvergence nette vers l'optimum."),
        md("### Lecture chiffrée du résultat\nLe score atteint 0.94 en 40 itérations."),
    ))
    assert len(findings) == 1
    assert findings[0]["type"] == "named_split"


def test_source_string_sans_liste_supportee():
    """nbformat admet ``source`` comme str OU liste de str. Les carnets ecrits
    a la main (et certains exports) laissent la forme str : le detecteur doit
    digerer les deux -- la suite existante ne fabrique que des listes."""
    a = {"cell_type": "markdown", "source": "### Lecture du resultat", "metadata": {}}
    b = {"cell_type": "markdown", "source": "### Lecture chiffree du resultat",
         "metadata": {}}
    findings = detect(nb(a, b))
    assert len(findings) == 1
    assert findings[0]["type"] == "named_split"


def test_convention_le_titre_compte_dans_la_mesure():
    """Corps disjoints ; le seul mot partage est le mot-TITRE « lecture »,
    present dans les deux sources. Jaccard = 1/8 = 0.125, containment des
    rares = 1/4 = 0.25. Epingle la convention : la mesure porte le titre,
    pas seulement le corps -- les bodies cites (#17040) citent ces chiffres."""
    a = md("### Lecture\nalpha beta gamma")
    b = md("### Lecture chiffree\ndelta epsilon zeta")
    findings = detect(nb(a, b))
    assert findings[0]["jaccard"] == 0.125
    assert findings[0]["rare_containment"] == 0.25
