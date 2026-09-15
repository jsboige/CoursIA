"""Tests de la primitive mixed-state presentation (MSP) via BFS.

La MSP d'un POMDP est l'ensemble des croyances distinctes atteignables
sur l'arbre des sequences d'observations possibles (arXiv:2405.15943 §2.2).

Ces tests verifient que :
- la MSP du banc :class:`Mess3Canonical` (non-Dirac) croit en 3^k
  croyances distinctes jusqu'a profondeur k=3 (1, 3, 9, 27),
- la MSP du banc :class:`RRXOR` plafonne a 2 croyances (alphabet binaire,
  observation deterministe y = a XOR b),
- les invariants canoniques (somme=1 par ligne, entropie non-croissante
  par profondeur, concordance avec la filtration forward) tiennent.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.bench_factorise import Mess3Canonical, RRXOR
from ict.mixed_state import (
    MixedStatePresentation,
    build_msp,
    msp_mess3,
    msp_rrxor,
    _round_belief,
)


class TestMSPMess3Canonical:
    """Spec : Marzen & Crutchfield 2017 — la MSP du Mess3 a 3^k croyances
    distinctes jusqu'a profondeur k (alphabet ternaire)."""

    def test_depth0_single_prior(self):
        msp = msp_mess3(max_depth=1)
        assert msp.depth == 1
        assert msp.n_distinct(0) == 1

    def test_growth_is_3_to_the_k(self):
        """1 -> 3 -> 9 -> 27 sur profondeurs 0, 1, 2, 3."""
        msp = msp_mess3(max_depth=4)
        assert msp.n_distinct(0) == 1
        assert msp.n_distinct(1) == 3
        assert msp.n_distinct(2) == 9
        assert msp.n_distinct(3) == 27


class TestMSPRRXOR:
    """RRXOR : alphabet binaire (y = XOR de 2 bits) -> 2 croyances
    distinctes apres la premiere observation. La MSP ne croît pas avec k."""

    def test_two_beliefs_per_depth_after_first(self):
        msp = msp_rrxor(max_depth=5)
        assert msp.n_distinct(0) == 1
        for d in range(1, 5):
            assert msp.n_distinct(d) == 2, f"depth {d} != 2"


class TestMSPInvariants:
    """Les 3 invariants canoniques : somme, filtration forward, entropie."""

    def test_sum_per_node_is_one(self):
        """Invariant 1 : chaque croyance de la MSP somme a 1.0."""
        msp = msp_mess3(max_depth=4)
        for d in range(msp.depth):
            for i, b in enumerate(msp.nodes[d]):
                assert abs(b.sum() - 1.0) < 1e-6, (
                    f"depth {d}, node {i}: sum={b.sum():.8f} != 1.0"
                )

    def test_concordance_with_forward_filtration(self):
        """Invariant 2 : la MSP inclut la croyance exacte retournee par la
        filtration forward du generateur (chemin reconstruit par BFS gauche)."""
        msp = msp_mess3(max_depth=4)

        def forward_factory(obs):
            return Mess3Canonical().beliefs(obs)

        ok, failures = msp.verify_invariants(forward_factory)
        assert ok, f"invariants failed: {failures}"

    def test_concordance_with_forward_filtration_rrxor(self):
        msp = msp_rrxor(max_depth=4)

        def forward_factory(obs):
            return RRXOR().beliefs(obs)

        ok, failures = msp.verify_invariants(forward_factory)
        assert ok, f"invariants failed: {failures}"


class TestBuildMSPErrors:
    def test_max_depth_at_least_one(self):
        with pytest.raises(Exception):  # ProcessError ou ValueError
            build_msp(
                generator=Mess3Canonical(),
                max_depth=0,
                obs_alphabet=(0, 1, 2),
                prior=np.array([1 / 3, 1 / 3, 1 / 3]),
                transition=np.eye(3),
                emission=np.eye(3),
            )

    def test_zero_likelihood_raises(self):
        """Une vraisemblance nulle (ligne d'emission toute 0) doit lever,
        sinon la normalisation est impossible. Cas pathologique : prior
        stationnaire uniforme + matrice d'emission singuliere."""
        prior = np.array([1 / 3, 1 / 3, 1 / 3])
        T = np.array([[0.95, 0.05, 0.0], [0.0, 0.95, 0.05], [0.05, 0.0, 0.95]])
        E = np.zeros((3, 3))  # singuliere
        with pytest.raises(Exception):
            build_msp(
                generator=Mess3Canonical(),
                max_depth=2,
                obs_alphabet=(0, 1, 2),
                prior=prior,
                transition=T,
                emission=E,
            )


class TestRoundBelief:
    def test_round_belief_tuple(self):
        b = np.array([0.333333333, 0.333333334, 0.333333333])
        key = _round_belief(b, decimals=6)
        expected = (round(1 / 3, 6),) * 3
        assert key == expected
        assert key == (0.333333,) * 3

    def test_round_belief_distinguishes_far_but_collapses_near(self):
        """Deux croyances a 1e-9 d'ecart sont confondues (utile pour la dedup)
        mais 1e-3 different reste distinct."""
        b1 = np.array([1.0, 0.0, 0.0])
        b2 = np.array([1.0 - 1e-3, 1e-3, 0.0])
        assert _round_belief(b1) != _round_belief(b2)

        b3 = np.array([1.0 - 1e-9, 1e-9, 0.0])
        assert _round_belief(b1) == _round_belief(b3)
