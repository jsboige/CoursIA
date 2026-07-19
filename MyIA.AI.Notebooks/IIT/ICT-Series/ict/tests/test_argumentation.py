"""Tests du module :mod:`ict.argumentation` (ICT-7289 Phase A, Epic #4588).

Chaque test valide une propriete falsifiable du substrat argumentation,
numerote par *gate*. Pattern herite de ``test_time_arrow.py`` /
``test_reversibility_budget.py`` : bootstrap ``sys.path`` module-level, sans
fixtures, tolerances commentees.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import argumentation as arg  # noqa: E402


# --------------------------------------------------------------------------- #
#  Gate 1 : semantique grounded sur un AF simple (in / out)                   #
# --------------------------------------------------------------------------- #


def test_grounded_simple_in_out():
    """Un argument non attaque est ``in`` ; celui qu'il attaque est ``out``.

    AF : 0 -> 1 (0 attaque 1). Pas d'autre attaque.
    Labeling grounded attendu : 0 = in, 1 = out.
    """
    af = arg.DungAF([0, 1], [(0, 1)])
    lab = arg.grounded_labeling(af)
    assert lab[0] == "in", f"0 non attaque doit etre in, recu {lab[0]}"
    assert lab[1] == "out", f"1 attaque par 0 (in) doit etre out, recu {lab[1]}"


# --------------------------------------------------------------------------- #
#  Gate 2 : Nixon diamond -> les deux undec (cas test canonique)              #
# --------------------------------------------------------------------------- #


def test_grounded_nixon_diamond_undec():
    """Le Nixon diamond (cycle d'attaque mutuelle) -> les deux ``undec``.

    AF : 0 -> 1 et 1 -> 0 (attaque mutuelle, aucun attaquant externe).
    La semantique grounded ne peut trancher : ni 0 ni 1 n'a tous ses
    attaquants ``out`` -> les deux restent ``undec``.
    """
    af = arg.nixon_diamond()
    lab = arg.grounded_labeling(af)
    assert lab[0] == "undec" and lab[1] == "undec", (
        f"Nixon diamond : les deux doivent etre undec, recu {lab}"
    )


# --------------------------------------------------------------------------- #
#  Gate 3 : chaine lineaire -> alternance in/out                              #
# --------------------------------------------------------------------------- #


def test_grounded_chain_alternance():
    """Chaine 0 -> 1 -> 2 -> 3 : alternance in/out (0=in, 1=out, 2=in, 3=out)."""
    af = arg.controversial_chain(4)
    lab = arg.grounded_labeling(af)
    expected = {0: "in", 1: "out", 2: "in", 3: "out"}
    for a, exp in expected.items():
        assert lab[a] == exp, f"chaine : {a} doit etre {exp}, recu {lab[a]}"


# --------------------------------------------------------------------------- #
#  Gate 4 : trajectoire de croyance (arrivee sequentielle)                    #
# --------------------------------------------------------------------------- #


def test_belief_trajectory_length_and_evolution():
    """L'arrivee sequentielle produit une trajectoire de longueur n, et le
    labeling evolue (le dernier pas porte tous les arguments)."""
    af = arg.controversial_chain(3)
    traj = arg.belief_trajectory(af, order=[0, 1, 2])
    assert len(traj) == 3, f"trajectoire de longueur 3 attendue, {len(traj)}"
    # Au pas 1 : seul l'arg 0, non attaque -> in.
    assert traj[0] == {0: "in"}
    # Au pas 3 : tous presents, chaine complete.
    assert set(traj[2].keys()) == {0, 1, 2}


def test_belief_trajectory_include_empty():
    """``include_empty=True`` ajoute l'etat vide en tete (etat initial)."""
    af = arg.nixon_diamond()
    traj = arg.belief_trajectory(af, order=[0, 1], include_empty=True)
    assert len(traj) == 3
    assert traj[0] == {}, f"etat initial vide attendu, recu {traj[0]}"


# --------------------------------------------------------------------------- #
#  Gate 5 : resume d'etat (n_in, n_out, n_undec)                              #
# --------------------------------------------------------------------------- #


def test_belief_summary_counts():
    """Le resume compte correctement in/out/undec."""
    labeling = {0: "in", 1: "out", 2: "undec", 3: "in"}
    assert arg.belief_summary(labeling) == (2, 1, 1)


# --------------------------------------------------------------------------- #
#  Gate 6 : signature complete base-3 (identite preservee)                    #
# --------------------------------------------------------------------------- #


def test_state_signature_base3_with_placeholder():
    """La signature encode out=0, undec=1, in=2, et -1 pour les non-arrives."""
    labeling = {0: "in", 2: "out"}  # arg 1 non arrive
    sig = arg.state_signature(labeling, n_args=3)
    assert sig == (2, -1, 0), f"signature base-3 attendue (2,-1,0), recu {sig}"


def test_state_signature_distinguishes_identity():
    """Deux labelings avec meme compte mais identite differente -> signatures
    differentes (critere pour la dette d'irreversibilite en Phase B)."""
    lab_a = {0: "in", 1: "out"}
    lab_b = {0: "out", 1: "in"}
    # Memes comptes (1 in, 1 out) mais identites differentes.
    assert arg.belief_summary(lab_a) == arg.belief_summary(lab_b)
    assert arg.state_signature(lab_a, n_args=2) != arg.state_signature(lab_b, n_args=2)


# --------------------------------------------------------------------------- #
#  Gate 7 : TPM ligne-stochastique depuis une trajectoire                     #
# --------------------------------------------------------------------------- #


def test_belief_transition_matrix_row_stochastic():
    """La TPM est carree et ligne-stochastique (chaque ligne somme a 1)."""
    af = arg.controversial_chain(5)
    P, mapping = arg.belief_transition_matrix(af, order=[0, 1, 2, 3, 4])
    n = P.shape[0]
    assert P.shape == (n, n), "TPM carree attendue"
    row_sums = P.sum(axis=1)
    assert np.allclose(row_sums, 1.0), (
        f"lignes de TPM doivent sommer a 1, recu {row_sums}"
    )


def test_belief_transition_matrix_encoding_signature():
    """L'encodage ``signature`` produit une TPM valide (etats distincts)."""
    af = arg.nixon_diamond()
    P, mapping = arg.belief_transition_matrix(
        af, order=[0, 1], encoding="signature"
    )
    assert P.shape[0] >= 1
    assert np.allclose(P.sum(axis=1), 1.0)


# --------------------------------------------------------------------------- #
#  Gate 8 : fleche du temps du discours (sigma >= 0)                          #
# --------------------------------------------------------------------------- #


def test_discourse_irreversibility_nonneg_and_stationary():
    """``discourse_irreversibility`` renvoie sigma >= 0 et pi stochastique."""
    af = arg.controversial_chain(6)
    P, _ = arg.belief_transition_matrix(af, order=list(range(6)))
    diag = arg.discourse_irreversibility(P)
    assert diag["sigma"] >= 0.0, f"sigma doit etre >= 0, recu {diag['sigma']}"
    assert np.allclose(diag["pi"].sum(), 1.0), "pi doit sommer a 1"
    assert diag["P_rev_distance"] >= 0.0


def test_discourse_irreversibility_reversible_zero():
    """Une TPM symetrique (detailed balance) a sigma ~ 0 (discours reversible)."""
    P_sym = np.array([[0.5, 0.5], [0.5, 0.5]])
    diag = arg.discourse_irreversibility(P_sym)
    assert diag["sigma"] < 1e-9, f"TPM reversible : sigma ~ 0, recu {diag['sigma']}"


def test_discourse_irreversibility_asymmetric_positive():
    """Une TPM bidirectionnelle ASYMETRIQUE a sigma > 0 (fleche du temps reelle).

    Honnetete : sur un debat deterministe a ordre fixe (gate 8 precedent),
    sigma = 0 (pas de cycle de flux). Mais l'instrument DOIT distinguer un
    regime bidirectionnel asymetrique (bascules de croyance preferentiellement
    dans un sens) -> sigma strictement positif. Sans ce test, l'instrument
    pourrait etre accuse de 'rendre toujours 0'.
    """
    # TPM 2x2 asymetrique : transition 0->1 plus probable que 1->0.
    P_asym = np.array([[0.3, 0.7], [0.9, 0.1]])
    diag = arg.discourse_irreversibility(P_asym)
    assert diag["sigma"] > 0.0, (
        f"TPM asymetrique : sigma > 0 attendu, recu {diag['sigma']}"
    )


# --------------------------------------------------------------------------- #
#  Gate 9 : sous-AF induit (induced)                                          #
# --------------------------------------------------------------------------- #


def test_induced_subgraph_keeps_internal_attacks_only():
    """Le sous-AF induit ne garde que les attaques dont les deux extremites
    sont dans le sous-ensemble."""
    af = arg.DungAF([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)])
    sub = af.induced([0, 1, 3])  # arg 2 retire
    # (1,2) et (2,3) disparaissent (2 absent) ; seul (0,1) reste.
    assert sub.attacks == [(0, 1)]
    assert sub.n() == 3


# --------------------------------------------------------------------------- #
#  Gate 10 : PASS Phase A — TPM derivee d'un AF canonique (verdict)           #
# --------------------------------------------------------------------------- #


def test_phase_a_verdict_tpm_derivable():
    """GATE de Phase A : une TPM exploitable est derivable d'un AF reel.

    Preuve : on derive une TPM ligne-stochastique non triviale (au moins 2
    etats distincts) depuis l'AF canonique *Nixon diamond* (documente dans la
    serie Tweety). Si la TPM etait triviale (1 etat), le substrat serait
    inexploitable -> verdict d'impossibilite. Ici : PASS.
    """
    af = arg.nixon_diamond()
    P, mapping = arg.belief_transition_matrix(af, order=[0, 1])
    n_states = len(mapping)
    assert n_states >= 2, (
        f"Phase A : la TPM doit avoir >= 2 etats, recu {n_states} -> FAIL"
    )
    assert np.allclose(P.sum(axis=1), 1.0)
