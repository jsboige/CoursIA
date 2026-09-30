#!/usr/bin/env python3
"""Tests de check_lecture_anchor (#16695).

Controles exigés par l'issue :
- Controle NEGATIF : forme #16619 c32 (`## Conclusion` de cloture apres un stub
  avec 23 o de sortie) => OK.
- Controle POSITIF : une vraie lecture posee sur une ancre sans output =>
  refuse (anchor_no_output), et sur un stub execute (output < 200 o) =>
  refuse (anchor_stub_output).

Run : python scripts/notebook_tools/test_check_lecture_anchor.py
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from check_lecture_anchor import (  # noqa: E402
    CLOSURE_RE, LECTURE_RE, STUB_RE, is_exempt, scan_cells,
)

STUB_SRC = ["# Exercice 3\n", "pass\n", 'print("Exercice a completer")\n']


def code_cell(outputs=None, source=None):
    return {"cell_type": "code", "execution_count": 1, "metadata": {},
            "source": source or STUB_SRC, "outputs": outputs or []}


def md_cell(source):
    return {"cell_type": "markdown", "metadata": {}, "source": source}


def plain_output(text, nbytes):
    return {"output_type": "execute_result", "execution_count": 1,
            "data": {"text/plain": [text * max(1, nbytes // max(1, len(text)))]},
            "metadata": {}}


def rules(findings):
    return {f["rule"] for f in findings}


def test_regexes():
    assert LECTURE_RE.search("### Lecture du resultat : le pli")
    assert LECTURE_RE.search("On observe une montee des precursseurs")
    assert LECTURE_RE.search("Ce que montre la sortie")
    assert not LECTURE_RE.search("## Mise en place du banc")
    assert CLOSURE_RE.match("## Conclusion")
    assert CLOSURE_RE.match("## 7. Conclusion")
    assert CLOSURE_RE.match("### Synthese des trois familles")
    assert not CLOSURE_RE.match("## Construction du modele")
    assert STUB_RE.search("".join(STUB_SRC))
    print("OK regexes")


def test_exemptions():
    # cloture numerotee ou non, synthese, en-resume
    assert is_exempt(md_cell(["## Conclusion\n", "On observe tout et rien."]))
    assert is_exempt(md_cell(["## 7. Conclusion\n", "On lit trois familles."]))
    assert is_exempt(md_cell(["### Synthese\n", "resultat: ok"]))
    assert is_exempt(md_cell(["## En resume\n"]))
    # ouverture de section (titre non-lecture en tete) = transition, pas lecture
    assert is_exempt(md_cell(["## 4. Analyse des sorties\n", "On observera ici."]))
    # forme GRAS : remarque d'extension (pin FP Pyro_RSA_Hyperbole cell#39)
    assert is_exempt(md_cell(["**Remarque** : Ironie et affect plus complexe\n",
                              "L'etude de Kao et Goodman (2015)..."]))
    # mais **Note** n'est PAS exempte (trop generique : peut lire un output)
    assert not is_exempt(md_cell(["**Note** : on observe le pli."]))
    # enonce d'exercice (pin FP PyMC-17 c16) : instruit, ne lit pas une sortie
    assert is_exempt(md_cell(["### Exercice 2 -- Etat vectoriel\n",
                              "Le filtre ci-dessus suit une position scalaire."]))
    # regle horizontale puis titre de transition (pin FP Infer-4 c17)
    assert is_exempt(md_cell(["***\n", "\n", "### Vers l'inference conditionnelle\n",
                              "Les marginales nous donnent les probabilites a priori."]))
    # PAS exempt : titre de lecture, ou corps sans titre de section
    assert not is_exempt(md_cell(["### Lecture du resultat\n"]))
    assert not is_exempt(md_cell(["On observe une montee."]))
    print("OK exemptions")


def test_positive_controls():
    # lecture sur stub NON execute (output vide) -> refuse
    cells = [code_cell(), md_cell(["### Lecture du resultat : ", "on observe le pli."])]
    assert rules(scan_cells(cells)) == {"anchor_no_output"}
    # lecture sur stub EXECUTE (23 o de sortie) -> refuse (controle positif #16695)
    cells = [code_cell(outputs=[plain_output("Exercice a completer\n", 23)]),
             md_cell(["On observe trois familles dans la sortie."])]
    assert rules(scan_cells(cells)) == {"anchor_stub_output"}
    # lecture sans AUCUN code amont -> refuse
    cells = [md_cell(["### Lecture du resultat\n"]), md_cell(["resultat: on lit X"])]
    assert rules(scan_cells(cells)) == {"no_anchor"}
    print("OK controles positifs")


def test_negative_controls():
    # CONTROLE NEGATIF mesure #16619 c32 : ## Conclusion apres stub 23 o => OK
    cells = [code_cell(outputs=[plain_output("Exercice a completer\n", 23)]),
             md_cell(["## Conclusion\n", "Ce que montre ce notebook : SHAP, LIME, DiCE "
                      "composent trois familles d'explicabilite."])]
    assert scan_cells(cells) == []
    # lecture ancoree sur un VRAI output (500 o) => OK
    cells = [code_cell(outputs=[plain_output("phi=2.622\n", 500)]),
             md_cell(["### Lecture du resultat : ", "on observe le pli."])]
    assert scan_cells(cells) == []
    # stub executé avec GROSSE sortie (>= 200 o) : ce n'est plus un stub muet
    cells = [code_cell(outputs=[plain_output("Exercice a completer\n", 250)]),
             md_cell(["On observe une montee."])]
    assert scan_cells(cells) == []
    print("OK controles negatifs")


def test_added_indices_scope():
    # mode PR : seule la cellule AJOUTEE est examinee
    cells = [code_cell(), md_cell(["On observe (dette historique, pas ajoutee)."])]
    assert scan_cells(cells, added_indices=set()) == []
    cells = [code_cell(), md_cell(["On observe (cellule ajoutee par la PR)."])]
    assert rules(scan_cells(cells, added_indices={1})) == {"anchor_no_output"}
    print("OK perimetre added_indices")


if __name__ == "__main__":
    test_regexes()
    test_exemptions()
    test_positive_controls()
    test_negative_controls()
    test_added_indices_scope()
    print("ALL PASS")
