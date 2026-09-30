# -*- coding: utf-8 -*-
"""Tests du garde d'ancrage de lecture (#16695).

Controles exiges par l'issue : le contre-exemple #16619 c32 (Conclusion apres
stub) doit PASSER (exemption de cloture), et un cas construit de lecture sur
ancre sans output doit etre REFUSE (controle positif -- un organe qui ne dit
jamais rien est indiscernable d'un organe debranche, lecon #11685).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_reading_anchor as cra  # noqa: E402


def code(src, outputs=None, exec_count=None):
    return {"cell_type": "code", "metadata": {}, "execution_count": exec_count,
            "outputs": outputs or [], "source": src}


def md(src):
    return {"cell_type": "markdown", "metadata": {}, "source": src}


def out(text):
    return {"output_type": "stream", "name": "stdout", "text": text}


def test_lecture_sur_code_sans_output_refusee():
    head = [code("m = sum(v) / len(v)\n"),
            md("### Lecture du resultat\n\nOn observe que la moyenne vaut 42.")]
    f = cra.analyze(head, [])
    assert len(f) == 1
    assert f[0]["kind"] == "ANCRE_SANS_OUTPUT"
    assert f[0]["anchor"] == 0


def test_lecture_sur_stub_executee_spoiler_refusee():
    stub = code("# TODO etudiant\npass\n",
                outputs=[out("Exercice a completer\n")], exec_count=1)
    head = [stub, md("On constate que le resultat attendu est 0.75.")]
    f = cra.analyze(head, [])
    assert [x["kind"] for x in f] == ["ANCRE_STUB"]


def test_cellule_ouverture_avant_tout_code_exemptee():
    """FP mesure #16656 : titres/navigation de tete de notebook (avant TOUT code,
    reference a un companion externe) -- zone d'ouverture, la classe
    « lecture sans ancre amont » est retiree (0 vrai positif sur 18 PRs)."""
    head = [md("# Lean-15c : companion formel natif\n\nOn observe la preuve dans le lake.")]
    assert cra.analyze(head, []) == []


def test_lecture_dans_le_corps_avec_code_amont_tire():
    """Une lecture situee APRES du code (mais sans output sur l'ancre) reste
    refusee : c'est le vrai defaut vise par #16619."""
    head = [code("valeurs = [1, 2]\n"),
            md("Ce que montre l'experience : 3 axes.")]
    f = cra.analyze(head, [])
    assert [x["kind"] for x in f] == ["ANCRE_SANS_OUTPUT"]


def test_conclusion_apres_stub_passe_contre_exemple_16619():
    """Le FP fondateur du prototype : une cloture suit legitimement un stub."""
    stub = code("# Exercice : votre code\npass\n",
                outputs=[out("Exercice a completer")], exec_count=7)
    c32 = ("## Conclusion\n\nCe qu'il faut retenir : on observe trois familles, "
           "et le resultat de chacune merite une lecture attentive.")
    assert cra.analyze([stub, md(c32)], []) == []


def test_transitions_et_intros_de_section_exemptees():
    stub = code("# TODO etudiant\npass\n", outputs=[out("Exercice a completer")])
    for src in (
        "## Synthese\n\nOn observe trois familles.",
        "## Resume\n\nLe resultat attendu tient en une ligne.",
        "## Exercice 3\n\nOn constate ici qu'il faut lire les donnees.",
        "## Partie 2 -- Interpretation avancee\n\nCe que montre la section 1.",
    ):
        assert cra.analyze([stub, md(src)], []) == [], src[:40]


def test_lecture_sur_output_reel_passe():
    real = code("print(t)", outputs=[out("phi = 0.62\n")], exec_count=3)
    head = [real, md("Lecture du resultat : on lit un phi moyen de 0.62.")]
    assert cra.analyze(head, []) == []


def test_cellule_heritee_non_ajoutee_ignoree():
    real = code("print(t)\n")  # sans output
    lect = md("On observe un phi de 0.62.")
    assert cra.analyze([real, lect], [real, lect]) == []


def test_cellule_sans_motif_lecture_ignoree():
    real = code("pass\n")  # stub sans output
    assert cra.analyze([real, md("## Contexte\n\nSuite du traitement.")], []) == []


def test_lecture_de_titre_non_exemptee():
    """`### Lecture du resultat` N'EST pas un en-tete exempte : il doit tirer."""
    head = [code("pass\n"), md("### Lecture du resultat\n\nOn observe 42.")]
    assert [x["kind"] for x in cra.analyze(head, [])] == ["ANCRE_SANS_OUTPUT"]
