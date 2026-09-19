"""Tests du recensement des cellules de lecture scindees (#16762).

Fixtures synthetiques reproduisant les formes mesurees sur main :
pattern nominal user (« Lecture » puis « Lecture chiffree » consecutifs),
paire generique, paire separee par une cellule de code, temoins negatifs,
et le controle FP (deux lectures de signaux differents empilees ->
hit structurel mais recouvrement faible, le garde doit se fier a C, pas
a la seule structure).
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_split_reading_cells import cell_title, detect  # noqa: E402


def md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source, "metadata": {}}


def code(source: str = "1 + 1") -> dict:
    return {"cell_type": "code", "source": source, "metadata": {}, "outputs": []}


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
