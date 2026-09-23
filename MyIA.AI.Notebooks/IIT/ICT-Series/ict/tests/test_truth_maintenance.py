"""Tests du module :mod:`ict.truth_maintenance` (strate 6, issue #17319, Epic #4588).

Chaque gate valide une propriete falsifiable du port JTMS/ATMS de la
distillation EPITA ``1.4.1-JTMS`` (issues EPITA #1961 phase 4). Les valeurs
attendues sont FIGEES depuis une execution differentielle contre le code
source EPITA original (tete ``487210fb``, 2026-09-22) : corpora
``simple_beliefs.json`` / ``no_justification.json`` reproduits en litteraux,
cas cycle et ATMS construits pour l'occasion. Pattern herite de
``test_argumentation.py`` : bootstrap ``sys.path`` module-level, sans
fixtures.
"""

from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import truth_maintenance as tms  # noqa: E402


# --------------------------------------------------------------------------- #
#  Gate 1 : corpus simple, premisse A posee (differential EPITA identique)     #
# --------------------------------------------------------------------------- #

SIMPLE_BELIEFS = [
    {"in": ["A"], "out": [], "conclusion": "B"},
    {"in": ["B"], "out": ["C"], "conclusion": "D"},
    {"in": ["A"], "out": [], "conclusion": "C"},
    {"in": [], "out": ["B"], "conclusion": "C"},
    {"in": [], "out": ["A"], "conclusion": "B"},
]


def _build_simple(initial):
    t = tms.JTMS(strict=False)
    for j in SIMPLE_BELIEFS:
        t.add_justification(j["in"], j["out"], j["conclusion"])
    for prem in initial:
        t.set_belief_validity(prem, True)
    return t


def test_gate1_corpus_simple_avec_premisse():
    t = _build_simple(["A"])
    assert t.status_table() == {"A": True, "B": True, "C": True, "D": None}


# --------------------------------------------------------------------------- #
#  Gate 2 : premisse retiree -> negation-as-failure (quirk mesure de la source)#
# --------------------------------------------------------------------------- #


def test_gate2_premisse_inconnue_negation_as_failure():
    t = _build_simple([])
    assert t.status_table() == {"A": None, "B": True, "C": None, "D": True}


def test_gate2b_retrait_propage_leffondrement():
    t = _build_simple(["A"])
    assert t.status_table()["D"] is None
    t.set_belief_validity("A", None)
    # A inconnu : B survit via la clause out "not-A", C tombe, D remonte
    assert t.status_table() == {"A": None, "B": True, "C": None, "D": True}


# --------------------------------------------------------------------------- #
#  Gate 3 : boucle de justifications -> refus de mesurer (SCC non triviale)     #
# --------------------------------------------------------------------------- #


def test_gate3_cycle_marque_non_monotonic():
    t = tms.JTMS(strict=False)
    t.add_justification(["B"], [], "A")
    t.add_justification(["A"], [], "B")
    t.add_belief("C")
    t.set_belief_validity("C", True)
    table = t.status_table()
    assert table == {"A": None, "B": None, "C": True}
    assert t.beliefs["A"].non_monotonic is True
    assert t.beliefs["B"].non_monotonic is True
    assert t.beliefs["C"].non_monotonic is False


# --------------------------------------------------------------------------- #
#  Gate 4 : corpus no_justification (croyance sans justification)              #
# --------------------------------------------------------------------------- #


def test_gate4_justification_vide_soutien_inconditionnel():
    # Corpus no_justification.json de la source : {in: [], out: [], conclusion: A}.
    # Quirk mesure (EPITA identique, differential tete 487210fb) : une
    # justification VIDE est satisfaite par vacuite (all([]) == True) -> la
    # conclusion est valide sans aucune premisse. Support inconditionnel,
    # pas une absence de justification. Documente dans le carnet.
    t = tms.JTMS(strict=False)
    t.add_justification([], [], "A")
    assert t.status_table() == {"A": True}


# --------------------------------------------------------------------------- #
#  Gate 5 : ATMS -- environnements, nogood, purge retroactive                  #
# --------------------------------------------------------------------------- #

PERP = "⊥"


def _atms_instance():
    a = tms.ATMS()
    a.add_assumption("p")
    a.add_assumption("q")
    for n in ("x", "y", "z"):
        a.add_node(n)
    a.add_justification(["p"], [], "x")
    a.add_justification(["q", "x"], [], "y")
    a.add_justification(["p", "q"], [], PERP)
    a.add_justification(["p"], ["q"], "z")
    return a


def _labels(a):
    return {
        n: sorted(tuple(sorted(e)) for e in nd.label) for n, nd in a.nodes.items()
    }


def test_gate5_atms_environnements_et_nogood():
    a = _atms_instance()
    labels = _labels(a)
    assert labels["p"] == [("p",)]
    assert labels["q"] == [("q",)]
    assert labels["x"] == [("p",)]
    # {p, q} est nogood : y n'a plus aucun environnement valide
    assert labels["y"] == []
    # blocage out : l'environnement {p} de z ne contient pas {q}
    assert labels["z"] == [("p",)]


def test_gate5b_atms_purge_retroactive():
    a = tms.ATMS()
    a.add_assumption("p")
    a.add_assumption("q")
    a.add_node("y")
    a.add_justification(["q", "p"], [], "y")  # y tient sous {p, q}
    a.add_justification(["p", "q"], [], PERP)  # ... qui devient nogood
    assert _labels(a)["y"] == []


def test_gate5c_atms_nogood_non_persistant_quirk_source():
    # Quirk mesure de la source (et conserve par le port) : le purge retire
    # le nogood de l'etiquette du noeud contradiction LUI-MEME. Un
    # environnement rejetant la contradiction apres coup n'est donc plus
    # bloque par is_consistent. Documente dans le carnet (honnête, pas corrige).
    a = _atms_instance()
    assert _labels(a)[PERP] == []
    assert a.is_consistent(frozenset({"p", "q"})) is True


# --------------------------------------------------------------------------- #
#  Gate 6 : pont Dung -- une attaque est une justification de rejet            #
# --------------------------------------------------------------------------- #


def test_gate6_attaque_comme_justification_out():
    # AF de Dung : 0 attaque 1 (Tweety vole / ne vole pas), 2 soutient 0.
    # Un attack (a, b) se lit : justification "in [a] -> rejet de b", et le
    # rejet de b se represente par une croyance miroir "non-b" valide si a
    # l'est. Si 0 est premise, non-1 doit etre valide.
    t = tms.JTMS(strict=False)
    t.add_justification(["arg0"], [], "non-arg1")
    t.set_belief_validity("arg0", True)
    assert t.status_table()["non-arg1"] is True
    # reciproque : sans la premisse, rien n'est soutenu
    t2 = tms.JTMS(strict=False)
    t2.add_justification(["arg0"], [], "non-arg1")
    assert t2.status_table()["non-arg1"] is None


def test_gate6b_coherence_avec_grounded_de_lorgane():
    # Croisement avec l'organe natif ict.argumentation : sur l'AF Tweety,
    # un argument "in" au sens grounded correspond a une croyance valide
    # quand ses attaquants sont tous rejetes.
    from ict import argumentation as arg

    af = arg.tweety_bird()
    labeling = arg.grounded_labeling(af)
    t = tms.JTMS(strict=False)
    for a, b in af.attacks:
        t.add_justification([f"arg{a}"], [], f"non-arg{b}")
    # pose en premisse chaque argument in au sens grounded
    for i, lab in labeling.items():
        if lab == "in":
            t.add_belief(f"arg{i}")
            t.set_belief_validity(f"arg{i}", True)
    # tout argument "in" du grounded a son double "non-cible" soutenu
    for a, b in af.attacks:
        if labeling[a] == "in":
            assert t.status_table()[f"non-arg{b}"] is True
