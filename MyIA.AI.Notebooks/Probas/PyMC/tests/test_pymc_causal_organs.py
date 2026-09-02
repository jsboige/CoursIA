"""Tests pytest pour pymc_causal_organs.py — seconde moitie de l'acceptance 1 de #14051.

Issue #14051 §1 acceptance : « Les deux modules existent, sont importables,
et sont testes (le test compare la sortie du module a la valeur attendue
du notebook) ».

Strategie de test : execution reelle des estimateurs (pas de mock, H.1).

Difference nette avec le module frere ``causal_organs.py`` : ``enumerate_scm``
n'utilise **aucun RNG** (somme exhaustive sur ``2**n`` configurations), donc
la sortie est une fonction pure de ses arguments. L'egalite **byte-identique
stricte** avec la cellule native est atteignable, et c'est elle qu'on teste
(``==`` exact, pas ``approx``) — la ou les tests de ``causal_organs.py``
doivent se rabattre sur des grandeurs agregees.

Le SCM front-door et les quantites de reference sont re-derives ici depuis
les CPT de la cellule 20, puis compares au module. Aucune valeur n'est
recopiee a la main depuis une sortie : les constantes numeriques presentes
ci-dessous sont les CPT du notebook (ses ENTREES), pas ses resultats.
"""

from __future__ import annotations

import itertools
import math
import sys
from pathlib import Path

import pytest

# Permettre l'import direct sans packaging : on ajoute le dossier parent
# (Probas/PyMC/) au sys.path — meme convention que test_causal_organs.py.
_PARENT_DIR = Path(__file__).resolve().parent.parent
if str(_PARENT_DIR) not in sys.path:
    sys.path.insert(0, str(_PARENT_DIR))

import pymc_causal_organs as pco


# ---------------------------------------------------------------------------
# Reference locale : reimplementation independante de l'enumeration, ecrite
# depuis la definition mathematique et NON importee du module teste. Sert de
# controle croise (si le module derive, ce temoin ne derive pas avec lui).
# ---------------------------------------------------------------------------

def _reference_enumerate(nodes, query, evidence=None, do_vars=None):
    evidence = evidence or {}
    do_vars = do_vars or {}
    names = [n for n, _ in nodes]
    num = den = 0.0
    for bits in itertools.product([False, True], repeat=len(names)):
        assign = dict(zip(names, bits))
        if any(assign[k] != v for k, v in do_vars.items()):
            continue
        if any(assign[k] != v for k, v in evidence.items()):
            continue
        p = 1.0
        for name, fn in nodes:
            if name in do_vars:
                continue
            pt = fn(assign)
            p *= pt if assign[name] else (1.0 - pt)
        den += p
        if assign[query]:
            num += p
    return num / den if den > 0 else float("nan")


# CPT de la cellule 20 (les ENTREES du notebook, pas ses sorties).
_FRONT_SCM_LOCAL = [
    ("u",      lambda a: 0.20),
    ("smoke",  lambda a: 0.80 if a["u"] else 0.30),
    ("tar",    lambda a: 0.90 if a["smoke"] else 0.10),
    ("cancer", lambda a: (0.95 if a["u"] else 0.70) if a["tar"]
                          else (0.50 if a["u"] else 0.05)),
]


# ---------------------------------------------------------------------------
# T1-T3 : enumerate_scm — les trois niveaux de l'echelle de Pearl
# ---------------------------------------------------------------------------

def test_marginal_matches_reference_exactly():
    """T1 — niveau 0 (marginal) : egalite EXACTE avec le temoin independant."""
    got = pco.enumerate_scm(pco.FRONT_SCM, "smoke")
    expected = _reference_enumerate(_FRONT_SCM_LOCAL, "smoke")
    assert got == expected
    # P(X) = P(u)*0.80 + P(not u)*0.30, derive des CPT de la cellule.
    assert got == pytest.approx(0.20 * 0.80 + 0.80 * 0.30)


def test_conditioning_matches_reference_exactly():
    """T2 — niveau 1 (voir) : conditionnement sur une observation."""
    for xval in (True, False):
        got = pco.enumerate_scm(pco.FRONT_SCM, "tar", evidence={"smoke": xval})
        expected = _reference_enumerate(_FRONT_SCM_LOCAL, "tar", evidence={"smoke": xval})
        assert got == expected
    # P(M=1|X=1) est la CPT elle-meme : tar ne depend que de smoke.
    assert pco.enumerate_scm(pco.FRONT_SCM, "tar", evidence={"smoke": True}) == pytest.approx(0.90)


def test_intervention_differs_from_conditioning():
    """T3 — niveau 2 (faire) : do(X) != P(Y|X) en presence du confondant U.

    Gate falsifiable : si la mutilation cessait de couper l'arc U -> smoke,
    do() collapserait sur le conditionnement et ce test rougirait.
    """
    do1 = pco.enumerate_scm(pco.FRONT_SCM, "cancer", do_vars={"smoke": True})
    obs1 = pco.enumerate_scm(pco.FRONT_SCM, "cancer", evidence={"smoke": True})
    assert do1 == _reference_enumerate(_FRONT_SCM_LOCAL, "cancer", do_vars={"smoke": True})
    assert do1 != obs1, "do(X=1) doit differer de P(Y|X=1) : U confond X et Y"
    # Le conditionnement SURESTIME l'effet (U pousse a la fois smoke et cancer).
    assert obs1 > do1


# ---------------------------------------------------------------------------
# T4-T5 : p_y_given_m_x
# ---------------------------------------------------------------------------

def test_p_y_given_m_x_matches_reference_on_four_combinations():
    """T4 — les 4 combinaisons (M, X), egalite EXACTE avec le temoin."""
    for mval in (True, False):
        for xval in (True, False):
            got = pco.p_y_given_m_x(mval, xval)
            expected = _reference_enumerate(
                _FRONT_SCM_LOCAL, "cancer", evidence={"tar": mval, "smoke": xval}
            )
            assert got == expected, f"divergence sur (M={mval}, X={xval})"


def test_p_y_given_m_x_accepts_an_alternative_scm():
    """T5 — la parametrisation `scm=` est effective (la cellule native, elle,
    capturait `front_scm` par cloture et ne pouvait pas etre reutilisee)."""
    # SCM ou le genotype est certain : P(u)=1.0 change les quantites.
    alt = list(_FRONT_SCM_LOCAL)
    alt[0] = ("u", lambda a: 1.0)
    got = pco.p_y_given_m_x(True, True, scm=alt)
    assert got == _reference_enumerate(alt, "cancer", evidence={"tar": True, "smoke": True})
    assert got != pco.p_y_given_m_x(True, True), "un SCM different doit donner une valeur differente"


# ---------------------------------------------------------------------------
# T6 : l'identite front-door — la propriete que le notebook demontre
# ---------------------------------------------------------------------------

def test_front_door_identity_recovers_the_interventional_effect():
    """T6 — l'ajustement front-door, calcule SANS jamais lire U, restitue
    exactement ``P(Y | do(X))`` obtenu par mutilation directe (U connu).

    C'est la propriete que la cellule 20 demontre. Gate falsifiable : toute
    derive de `enumerate_scm` sur le conditionnement OU sur la mutilation
    casse l'egalite.
    """
    p_x1 = pco.enumerate_scm(pco.FRONT_SCM, "smoke")
    p_m1_given_x1 = pco.enumerate_scm(pco.FRONT_SCM, "tar", evidence={"smoke": True})
    p_m0_given_x1 = 1 - p_m1_given_x1

    inner_m1 = pco.p_y_given_m_x(True, True) * p_x1 + pco.p_y_given_m_x(True, False) * (1 - p_x1)
    inner_m0 = pco.p_y_given_m_x(False, True) * p_x1 + pco.p_y_given_m_x(False, False) * (1 - p_x1)
    front_door = p_m1_given_x1 * inner_m1 + p_m0_given_x1 * inner_m0

    do_direct = pco.enumerate_scm(pco.FRONT_SCM, "cancer", do_vars={"smoke": True})

    # Egalite a la precision flottante : les deux chemins somment les memes
    # produits de CPT dans un ordre different.
    assert front_door == pytest.approx(do_direct, abs=1e-12)


# ---------------------------------------------------------------------------
# T7 : convention de retour sur evidence de masse nulle
# ---------------------------------------------------------------------------

def test_impossible_evidence_returns_nan():
    """T7 — la cellule 5 rend ``nan`` quand la masse de l'evidence est nulle.

    On construit une evidence impossible : un noeud deterministe force a
    contredire sa CPT.
    """
    impossible = [("a", lambda s: 1.0)]  # P(a=True) = 1 -> P(a=False) = 0
    got = pco.enumerate_scm(impossible, "a", evidence={"a": False})
    assert math.isnan(got)


# ---------------------------------------------------------------------------
# T8 : purete / determinisme — ce qui distingue ce module de son frere
# ---------------------------------------------------------------------------

def test_repeated_calls_are_bit_identical():
    """T8 — aucun RNG : deux appels successifs rendent le MEME flottant.

    C'est la propriete qui autorise les assertions `==` exactes ci-dessus,
    la ou ``causal_organs.py`` (DiD/IV aleatoires) doit tester des agregats.
    """
    first = [pco.enumerate_scm(pco.FRONT_SCM, "cancer", do_vars={"smoke": True}) for _ in range(5)]
    assert len(set(first)) == 1, "enumerate_scm doit etre deterministe"
    assert pco.p_y_given_m_x(True, True) == pco.p_y_given_m_x(True, True)
