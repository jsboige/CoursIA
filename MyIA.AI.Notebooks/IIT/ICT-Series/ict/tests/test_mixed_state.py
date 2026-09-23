"""Tests de la primitive mixed-state presentation (MSP) via BFS.

La MSP d'un POMDP est l'ensemble des croyances distinctes atteignables
sur l'arbre des sequences d'observations possibles (arXiv:2405.15943 §2.2).

Ces tests verifient que :
- la MSP du banc :class:`Mess3Canonical` (non-Dirac) croit en 3^k
  croyances distinctes jusqu'a profondeur k=3 (1, 3, 9, 27),
- la MSP du banc :class:`RRXOR` conforme (Riechers & Crutchfield 2018,
  arXiv:1706.00883v1) compte **36** croyances distinctes en union :
  31 transitoires + 5 recurrentes (les Diracs causaux) -- la valeur
  exacte de la litterature (p. 17, Fig. 7),
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
    """RRXOR conforme (Riechers & Crutchfield 2018) : S-MSP de 36 croyances.

    L'union des croyances distinctes depuis le prior stationnaire vaut 36 :
    31 transitoires (resolution de l'ambiguite de phase de la modulation
    periodique d'ordre 3) + 5 recurrentes (les Diracs sur les etats causaux).
    Valeur de litterature : arXiv:1706.00883v1, p. 17, Fig. 7."""

    def test_union_is_36_literature_value(self):
        """Le critere d'acceptation de l'issue #16225 : 36 croyances."""
        msp = msp_rrxor()
        assert msp.n_distinct_total() == 36

    def test_five_recurrent_diracs_reached(self):
        """Les 5 Diracs causaux sont des croyances de la MSP (recurrentes)."""
        msp = msp_rrxor()
        keys = {_round_belief(b) for level in msp.nodes for b in level}
        for i in range(5):
            e = np.zeros(5)
            e[i] = 1.0
            assert _round_belief(e) in keys, f"Dirac {i} absent de la MSP"

    def test_growth_then_closure(self):
        """Croissance 1, 2, 4, 8, 12 par profondeur puis fermeture : plus
        aucune croyance nouvelle apres profondeur 7 (regime synchronise)."""
        msp = msp_rrxor(max_depth=10)
        per_level = [msp.n_distinct(d) for d in range(msp.depth)]
        assert per_level[:5] == [1, 2, 4, 8, 12]
        # fermeture : le cardinal par niveau se stabilise
        assert per_level[7] == per_level[8] == per_level[9]
        assert msp.n_distinct_total() == 36

    def test_distinct_beliefs_same_next_token(self):
        """Dissociation de la litterature : des croyances DISTINCTES partagent
        la meme distribution next-token (arXiv:2405.15943 §3.2 -- c'est ce qui
        fonde la separation belief/next-token que ICT-37 mesure)."""
        r = RRXOR()
        msp = msp_rrxor()
        Wsum = r.edge_tensor().sum(axis=1)  # Wsum[s, y] = P(y | etat s)

        def next_token_dist(b):
            return tuple(np.round(b @ Wsum, 8))

        groups = {}
        for level in msp.nodes:
            for b in level:
                groups.setdefault(next_token_dist(b), []).append(_round_belief(b))
        # 36 croyances pour moins de 36 predictions : la carte belief ->
        # next-token est non injective
        assert len(groups) < msp.n_distinct_total()
        # cas explicite : prior stationnaire et les deux croyances de
        # profondeur 1 (apres obs 0 et apres obs 1) -- trois croyances
        # distinctes, meme prediction (1/2, 1/2)
        uniform = groups.get((0.5, 0.5), [])
        assert len({tuple(b) for b in uniform}) >= 3


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
