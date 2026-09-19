"""Conformite du banc Mess3 canonique aux specs de Marzen & Crutchfield 2017.

Le banc :class:`ict.bench_factorise.Mess3Canonical` doit repondre aux specs
de la geometrie de croyance du papier 2405.15943 §2.2 :
- 3 etats caches en cycle, persistance p_stay,
- emissions ternaires DISCRETES (non gaussiennes couplees),
- la matrice d'emission est stochastique (somme par ligne = 1),
- la filtration forward produit des croyances NON-Dirac
  (le banc Mess3_ObsCoupled legacy, lui, produit des Dirac car les
  emissions gaussiennes a 4 sigma couplent obs~etat).

Ces tests sont le contrat ferme : ils refusent un banc qui degenererait
en Dirac (l'erreur commise par la version legacy). Voir
:class:`Mess3_ObsCoupled` qui reste disponible pour les comparaisons
de probe lineaire sur signaux continus.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.bench_factorise import (
    Mess3,
    Mess3Canonical,
    Mess3_ObsCoupled,
    ProcessError,
    RRXOR,
)


class TestMess3CanonicalEmission:
    def test_emission_matrix_is_stochastic(self):
        """Chaque ligne de E somme a 1.0 (matrice stochastique)."""
        m = Mess3Canonical()
        E = m.emission_matrix()
        assert E.shape == (3, 3)
        np.testing.assert_allclose(E.sum(axis=1), np.ones(3), atol=1e-10)

    def test_emission_diag_dominates_but_not_obs(self):
        """La diagonale est emission_diag (0.5) ; hors diag : (1-0.5)/(3-1) = 0.25.
        La diagonale domine (50% que obs = etat) sans etre obs=etat (sinon Dirac)."""
        m = Mess3Canonical(emission_diag=0.5)
        E = m.emission_matrix()
        np.testing.assert_allclose(np.diag(E), [0.5, 0.5, 0.5], atol=1e-10)
        off = E[0, 1]
        np.testing.assert_allclose(off, (1.0 - 0.5) / 2.0, atol=1e-10)  # 0.25

    def test_emission_diag_in_open_interval(self):
        """emission_diag doit etre dans (1/n, 1) — sinon Dirac ou uniforme."""
        with pytest.raises(ProcessError):
            Mess3Canonical(emission_diag=1.0)  # Dirac
        with pytest.raises(ProcessError):
            Mess3Canonical(emission_diag=1.0 / 3.0)  # uniforme == pas d'info
        with pytest.raises(ProcessError):
            Mess3Canonical(emission_diag=0.0)

    def test_transition_matrix_is_stochastic(self):
        m = Mess3Canonical(stay=0.95)
        T = m.transition_matrix()
        np.testing.assert_allclose(T.sum(axis=1), np.ones(3), atol=1e-10)
        # diagonale = 0.95, slip = 0.05 reparti vers le successeur du cycle
        assert T[0, 0] == pytest.approx(0.95)
        assert T[0, 1] == pytest.approx(0.05)
        assert T[0, 2] == pytest.approx(0.0)

    def test_stationary_is_uniform_on_cycle(self):
        """Cycle symetrique 0->1->2->0 a persistance p>0.5 : stationnaire = uniforme."""
        m = Mess3Canonical(stay=0.95)
        s = m.stationary()
        np.testing.assert_allclose(s, np.full(3, 1.0 / 3.0), atol=1e-10)


class TestMess3CanonicalSampling:
    def test_sample_returns_states_and_obs(self):
        m = Mess3Canonical()
        states, obs = m.sample(200, seed=42)
        assert states.shape == (200,)
        assert obs.shape == (200,)
        assert set(states.tolist()).issubset({0, 1, 2})
        assert set(obs.tolist()).issubset({0, 1, 2})

    def test_sample_obs_is_not_always_state(self):
        """Avec emission_diag=0.5, la majorite des obs different des etats.
        Si toutes les obs etaient egales aux etats, le banc degenererait
        en Dirac (H3 fail). Marzen & Crutchfield 2017 specifie un banc
        non-Dirac."""
        m = Mess3Canonical(emission_diag=0.5)
        states, obs = m.sample(1000, seed=7)
        mismatch_frac = (states != obs).mean()
        # Au moins 30% de mismatch (50% theorique moins marges)
        assert mismatch_frac > 0.30, (
            f"taux de mismatch obs!=etat trop bas ({mismatch_frac:.3f}) "
            "— le banc degenererait en Dirac, non conforme"
        )


class TestMess3CanonicalBeliefs:
    def test_beliefs_sum_to_one(self):
        """Invariant : P(s_k | o_{0..k}) est une distribution (somme = 1)."""
        m = Mess3Canonical()
        _, obs = m.sample(50, seed=42)
        b = m.beliefs(obs)
        np.testing.assert_allclose(b.sum(axis=1), np.ones(50), atol=1e-8)

    def test_beliefs_not_dirac_in_canonical_regime(self):
        """Le contrat distinctif : la filtration forward ne s'effondre pas
        en Dirac sur une trajectoire typique. C'est l'echec specifique du
        banc Mess3_ObsCoupled legacy que :class:`Mess3Canonical` corrige."""
        m = Mess3Canonical(emission_diag=0.5)
        rng = np.random.default_rng(42)
        n_traj = 50
        max_per_row = []
        for _ in range(n_traj):
            _, obs = m.sample(40, seed=int(rng.integers(0, 1_000_000)))
            b = m.beliefs(obs)
            max_per_row.append(b.max(axis=1).mean())
        overall_max = float(np.mean(max_per_row))
        # Si Dirac, max par ligne = 1.0 ; en regime canonique, max < 0.85
        assert overall_max < 0.85, (
            f"max belief moyen {overall_max:.3f} trop proche de 1.0 — "
            "filtration forward Dirac, banc non conforme"
        )

    def test_beliefs_reject_bad_alphabet(self):
        m = Mess3Canonical()
        with pytest.raises(ProcessError):
            m.beliefs(np.array([5, 5, 5]))  # hors {0,1,2}


class TestMess3AliasToLegacy:
    """Conservation de l'ancien nom :class:`Mess3` comme alias de
    :class:`Mess3_ObsCoupled` (gaussien couple). Documenter le piege
    pour les imports existants."""

    def test_mess3_alias_is_obs_coupled(self):
        """L'ancien nom ``Mess3`` renvoie aujourd'hui a la version gaussienne
        legacy (obs couplee a l'etat). C'est un alias de compatibilite ;
        le banc NON-Dirac est :class:`Mess3Canonical` (DEPRECIE pour
        la geometrie de croyance)."""
        assert Mess3 is Mess3_ObsCoupled


class TestRRXOR:
    def test_emission_matrix_is_deterministic(self):
        """RRXOR : y = b_{t-1} XOR b_t est deterministe.
        La matrice d'emission E[i, y] = 1.0 si y = a XOR b (etat i = 2a+b)."""
        r = RRXOR()
        E = r.emission_matrix()
        assert E.shape == (4, 2)
        # etat 00 -> y=0 ; etat 01 -> y=1 ; etat 10 -> y=1 ; etat 11 -> y=0
        np.testing.assert_allclose(E[0], [1.0, 0.0], atol=1e-10)
        np.testing.assert_allclose(E[1], [0.0, 1.0], atol=1e-10)
        np.testing.assert_allclose(E[2], [0.0, 1.0], atol=1e-10)
        np.testing.assert_allclose(E[3], [1.0, 0.0], atol=1e-10)

    def test_stationary_is_uniform(self):
        r = RRXOR()
        s = r.stationary()
        np.testing.assert_allclose(s, np.full(4, 0.25), atol=1e-10)

    def test_beliefs_sum_to_one(self):
        r = RRXOR()
        obs = np.array([0, 1, 0, 1, 1])
        b = r.beliefs(obs)
        np.testing.assert_allclose(b.sum(axis=1), np.ones(5), atol=1e-8)
