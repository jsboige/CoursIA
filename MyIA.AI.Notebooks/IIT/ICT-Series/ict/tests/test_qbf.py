"""Tests du port QBF (grain #17339) - litteraux figes contre la source EPITA.

Comme ``test_truth_maintenance`` (grain #17319) : les valeurs ci-dessous ont
ete mesurees par execution differentielle contre la source EPITA
``argumentation_analysis/agents/core/logic/qbf_native.py`` (tete ``a5ac1a5d``,
2026-09-22, ne au commit ``0d2ac1b0`` / PR EPITA #167), puis FIGEES. Les
surfaces copiees fidelement (``check_qbf``, ``analyze_qbf``,
``credulous_acceptance_qbf``) ont ete rejouees cote a cote sur le corpus de
reference ; l'acceptabilite SCEPTIQUE consomme l'organe natif
``ict.argumentation`` (divergence declaree 1 du module) -- sa justesse est
portee par les litteraux de la section organe ci-dessous.

Aucune dependance externe : le test tourne sans le clone EPITA (c'est le
caractere FIGE des litteraux qui preserve la preuve differentielle).
"""

from __future__ import annotations

import os
import sys

import pytest

# Pattern herite de ``test_argumentation.py`` : bootstrap sys.path
# module-level (cf. ``ict/tests/pytest.ini`` pour le pourquoi).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import argumentation as arg  # noqa: E402
from ict import qbf  # noqa: E402


# --------------------------------------------------------------------------- #
#  1. Solveur QBF - litteraux differentiels (source : VALID/INVALID, msgs)     #
# --------------------------------------------------------------------------- #


def test_tautologie_forall():
    ok, msg = qbf.check_qbf([{"type": "forall", "vars": ["x"]}], "x | !x")
    assert ok is True
    assert msg == "QBF VALID: x | !x"


def test_contradiction_exists():
    ok, msg = qbf.check_qbf([{"type": "exists", "vars": ["x"]}], "x & !x")
    assert ok is False
    assert msg == "QBF INVALID: x & !x"


def test_alternance_valide():
    # forall x. exists y. (x => y) : pour tout x, choisir y = Vrai.
    ok, _ = qbf.check_qbf(
        [{"type": "forall", "vars": ["x"]}, {"type": "exists", "vars": ["y"]}],
        "x => y",
    )
    assert ok is True


def test_alternance_invalide():
    # forall x. exists y. (x & !y) : pour x = Faux, aucune valeur de y ne sauve.
    ok, _ = qbf.check_qbf(
        [{"type": "forall", "vars": ["x"]}, {"type": "exists", "vars": ["y"]}],
        "x & !y",
    )
    assert ok is False


def test_exists_forall_valide():
    # exists x. forall y. (x | !y) : choisir x = Vrai, la matrice est tautologie.
    ok, _ = qbf.check_qbf(
        [{"type": "exists", "vars": ["x"]}, {"type": "forall", "vars": ["y"]}],
        "x | !y",
    )
    assert ok is True


def test_ordre_des_quantificateurs_compte():
    """exists x. forall y. != forall y. exists x. sur la meme matrice
    d'equivalence : l'ordre n'est pas commutatif."""
    matrix = "x & y | !x & !y"  # x == y
    ex_for = qbf.check_qbf(
        [{"type": "exists", "vars": ["x"]}, {"type": "forall", "vars": ["y"]}],
        matrix,
    )[0]
    for_ex = qbf.check_qbf(
        [{"type": "forall", "vars": ["y"]}, {"type": "exists", "vars": ["x"]}],
        matrix,
    )[0]
    assert ex_for is False  # y reste libre de varier apres le choix de x
    assert for_ex is True  # pour tout y, choisir x = y


def test_alternance_triple_quantificateurs():
    """Corpus differentiel 3 blocs : exists a. forall b. exists c. sur une
    matrice a trois clauses. Mesure source (tete a5ac1a5d) : VALID -- le
    temoin est a=Vrai puis c=Vrai si b=Faux (c repond a b : c'est le sens
    de l'alternance, le quantificateur interne joue apres le median)."""
    ok, msg = qbf.check_qbf(
        [
            {"type": "exists", "vars": ["a"]},
            {"type": "forall", "vars": ["b"]},
            {"type": "exists", "vars": ["c"]},
        ],
        "a & b | !b & c | !a & !c",
    )
    assert ok is True
    assert msg.startswith("QBF VALID")


def test_deux_blocs_forall_sur_equivalence():
    # forall a, b. (a == b) : invalide -- differentiel source identique.
    ok, _ = qbf.check_qbf(
        [{"type": "forall", "vars": ["a", "b"]}], "a & b | !a & !b"
    )
    assert ok is False
    # exists a, b. (a == b) : valide.
    ok2, _ = qbf.check_qbf(
        [{"type": "exists", "vars": ["a", "b"]}], "a & b | !a & !b"
    )
    assert ok2 is True


def test_parseur_precedences_sans_parentheses():
    """Limite declaree heritee de la source : pas de parentheses, la
    conjonction lie plus fort que la disjonction, l'implication est la plus
    faible. Le piege est epingle par le repr."""
    f = qbf.parse_formula("a & b | c")
    assert isinstance(f, qbf.Or)
    assert isinstance(f.left, qbf.And)
    rep = repr(qbf.parse_formula("a => b & c"))
    assert rep == "(a => (b & c))"


def test_analyze_qbf_statistiques():
    r = qbf.analyze_qbf(
        [{"type": "forall", "vars": ["x", "y"]}, {"type": "exists", "vars": ["z"]}],
        "x & y & z",
    )
    assert r["valid"] is False
    stats = r["statistics"]
    assert stats["variable_count"] == 3
    assert stats["search_space"] == 8
    assert stats["quantifier_count"] == 2
    assert stats["reasoner"] == "naive_enumeration"
    assert stats["handler"] == "ict.qbf"  # divergence declaree (source : qbf_native)


def test_exemples_canoniques():
    assert qbf.example_simple_validity()["valid"] is True
    assert qbf.example_simple_satisfiability()["valid"] is False
    assert qbf.example_mixed_quantifiers()["valid"] is True
    acc = qbf.example_argumentation_acceptance()
    assert acc["accepted"] is True
    assert acc["witness_extension"] == ["a"]


# --------------------------------------------------------------------------- #
#  2. Organe : admissible / extensions preferees (ajoutees par ce grain)       #
# --------------------------------------------------------------------------- #


def test_est_admissible_cas_limites():
    nixon = arg.nixon_diamond()
    assert arg.est_admissible(nixon, set()) is True
    assert arg.est_admissible(nixon, {0}) is True
    assert arg.est_admissible(nixon, {0, 1}) is False  # conflit interne


def test_est_admissible_defense():
    # 0 attaque 1, 2 attaque 1 : {0} se defend seul ; {2} aussi ; {1} non.
    af = arg.DungAF([0, 1, 2], [(0, 1), (2, 1)])
    assert arg.est_admissible(af, {0}) is True
    assert arg.est_admissible(af, {2}) is True
    assert arg.est_admissible(af, {1}) is False


def test_preferred_nixon():
    exts = arg.preferred_extensions(arg.nixon_diamond())
    assert [sorted(e) for e in exts] == [[0], [1]]


def test_preferred_tweety():
    exts = arg.preferred_extensions(arg.tweety_bird())
    assert [sorted(e) for e in exts] == [[0, 2]]


def test_preferred_refuse_grands_cadres():
    gros = arg.DungAF(list(range(16)), [])
    with pytest.raises(ValueError):
        arg.preferred_extensions(gros)


def test_theoreme_containment_grounded_dans_chaque_preferee():
    """Theoreme de Dung 1995 : l'extension grounded est incluse dans CHAQUE
    extension preferee. C'est le temoin negatif du carnet (section pont) :
    il echoue si l'organe ou le port derive."""
    cas = [
        arg.nixon_diamond(),
        arg.tweety_bird(),
        arg.DungAF([0, 1], [(0, 1)]),
        arg.DungAF([0, 1, 2], [(0, 1), (2, 1), (1, 2)]),
    ]
    for af in cas:
        lab = arg.grounded_labeling(af)
        grounded_in = {a for a, s in lab.items() if s == "in"}
        for ext in arg.preferred_extensions(af):
            assert grounded_in <= ext, (af.attacks, grounded_in, ext)


# --------------------------------------------------------------------------- #
#  3. Acceptabilite argumentative (port) - litteraux differentiels            #
# --------------------------------------------------------------------------- #


NIXON_STR = (["a", "b", "c"], [["a", "b"], ["b", "a"]])


def test_credule_nixon_a_et_c():
    args, attacks = NIXON_STR
    ra = qbf.credulous_acceptance_qbf(args, attacks, "a")
    assert ra["accepted"] is True
    assert ra["witness_extension"] == ["a"]
    rc = qbf.credulous_acceptance_qbf(args, attacks, "c")
    assert rc["accepted"] is True
    assert rc["witness_extension"] == ["c"]


def test_credule_chaine_longue():
    """Corpus differentiel source (mesure, tete a5ac1a5d) : d attaque par b,
    b attaque par a et c. Le temoin source est ['a', 'd'] -- a defend d contre
    b, l'extension {a, d} est admissible. Le littéral est FIGE sur la mesure,
    pas sur l'intuition."""
    r = qbf.credulous_acceptance_qbf(
        ["a", "b", "c", "d"],
        [["a", "b"], ["c", "b"], ["b", "d"]],
        "d",
    )
    assert r["accepted"] is True
    assert r["witness_extension"] == ["a", "d"]


def test_credule_cycle_impair():
    """Cycle d'attaque a -> b -> c -> a : aucun argument n'est credulement
    accepte (aucun admissible non vide ne contient un membre du cycle ;
    source identique)."""
    r = qbf.credulous_acceptance_qbf(
        ["a", "b", "c"], [["a", "b"], ["b", "c"], ["c", "a"]], "a"
    )
    assert r["accepted"] is False


def test_credule_cible_absente():
    args, attacks = NIXON_STR
    r = qbf.credulous_acceptance_qbf(args, attacks, "z")
    assert r["accepted"] is False
    assert "not in framework" in r["reason"]


def test_credule_borne_15():
    r = qbf.credulous_acceptance_qbf([f"x{i}" for i in range(16)], [], "x0")
    assert r["accepted"] is None
    assert "too large" in r["reason"]


def test_sceptique_nixon():
    args, attacks = NIXON_STR
    ra = qbf.skeptical_acceptance_qbf(args, attacks, "a")
    assert ra["accepted"] is False
    # Preferred du Nixon a 3 arguments : {a, c} et {b, c} (les singletons ne
    # sont pas maximaux -- c non attaque les complete tous les deux).
    assert sorted(ra["preferred_extensions"]) == [["a", "c"], ["b", "c"]]
    rc = qbf.skeptical_acceptance_qbf(args, attacks, "c")
    assert rc["accepted"] is True


def test_sceptique_tweety():
    r = qbf.skeptical_acceptance_qbf(
        ["a", "b", "c"], [["a", "b"], ["b", "a"], ["c", "b"]], "a"
    )
    assert r["accepted"] is True
    assert sorted(r["preferred_extensions"]) == [["a", "c"]]


def test_sceptique_cible_absente_et_borne():
    r = qbf.skeptical_acceptance_qbf(["a"], [], "z")
    assert r["accepted"] is False
    gros = qbf.skeptical_acceptance_qbf([f"x{i}" for i in range(16)], [], "x0")
    assert gros["accepted"] is None  # refus uniformise (divergence 2)
