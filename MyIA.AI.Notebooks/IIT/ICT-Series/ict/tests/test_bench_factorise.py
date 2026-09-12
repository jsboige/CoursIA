"""Tests CPU deterministes du banc factorise (issue #15480, tranche 1).

Contre-verification majeure : les beliefs exacts sont confrontes a une
enumeration brute de toutes les sequences d'etats sur n court — le forward
ne se valide pas par lui-meme.
"""

from __future__ import annotations

import itertools
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np
import pytest

from ict.bench_factorise import (
    FactoredBench,
    Mess3,
    ProcessError,
    RRXOR,
    belief_simplex_coords,
)


# ---------------------------------------------------------------------------
# Mess3 : structure, generation, beliefs
# ---------------------------------------------------------------------------


def test_mess3_transition_lignes_stochastiques_cycle():
    m = Mess3()
    t = m.transition_matrix()
    assert np.allclose(t.sum(axis=1), 1.0)
    # cycle : depuis chaque etat, soit rester, soit avancer au suivant
    for i in range(3):
        j = (i + 1) % 3
        assert t[i, i] == pytest.approx(0.95)
        assert t[i, j] == pytest.approx(0.05)
        assert t[i, 3 - i - j] == 0.0


def test_mess3_stationnaire_uniforme():
    m = Mess3()
    assert np.allclose(m.stationary(), [1 / 3] * 3)


def test_mess3_sample_reproductible_et_formes():
    m = Mess3()
    s1, o1 = m.sample(50, seed=7)
    s2, o2 = m.sample(50, seed=7)
    assert np.array_equal(s1, s2) and np.array_equal(o1, o2)
    assert s1.shape == (50,) and o1.shape == (50,)
    assert set(np.unique(s1)) <= {0, 1, 2}


def test_mess3_parametrage_invalide_rejete():
    with pytest.raises(ProcessError):
        Mess3(stay=1.5)
    with pytest.raises(ProcessError):
        Mess3(std=0.0)
    with pytest.raises(ProcessError):
        Mess3(means=(0.0, 1.0))


def _mess3_bruteforce_beliefs(m: Mess3, obs: np.ndarray) -> np.ndarray:
    """Enumeration exacte (independante du forward) : pour chaque sequence
    complete d'etats, poids joint = prior * prod(transitions) * prod(likelihoods),
    puis marginalisation en P(s_k | o_{0..n-1}) — beliefs lisses, a comparer
    au forward apres troncature des observations au meme prefixe."""
    n = len(obs)
    means = np.asarray(m.means)
    prior = m.stationary()
    t = m.transition_matrix()

    def lik(o: float, s: int) -> float:
        return math.exp(-0.5 * ((o - means[s]) / m.std) ** 2)

    weights = np.zeros(m.n_states)
    for seq in itertools.product(range(m.n_states), repeat=n):
        w = prior[seq[0]] * lik(obs[0], seq[0])
        for k in range(1, n):
            w *= t[seq[k - 1], seq[k]] * lik(obs[k], seq[k])
        weights[seq[n - 1]] += w
    return weights / weights.sum()


def test_mess3_beliefs_vs_enumeration_brute():
    m = Mess3(means=(-0.15, 0.0, 0.15), std=0.05, stay=0.9)
    _, obs = m.sample(8, seed=42)
    fast_last = m.beliefs(obs)[-1]
    brute_last = _mess3_bruteforce_beliefs(m, obs)
    assert fast_last.shape == (3,)
    assert np.allclose(fast_last, brute_last, atol=1e-10)
    # et sur prefixes successifs : le forward au pas k = enumeration tronquee a k+1
    for cut in (3, 5, 8):
        assert np.allclose(
            m.beliefs(obs[:cut])[-1], _mess3_bruteforce_beliefs(m, obs[:cut]), atol=1e-10
        )


def test_mess3_beliefs_somment_a_un_et_modes_lisibles():
    m = Mess3()
    states, obs = m.sample(500, seed=3)
    b = m.beliefs(obs)
    assert np.allclose(b.sum(axis=1), 1.0, atol=1e-12)
    # modes bien separees : argmax du belief = etat emis la plupart du temps
    acc = (b.argmax(axis=1) == states).mean()
    assert acc > 0.95, f"modes mal separees, accuracy={acc}"


def test_mess3_beliefs_rejette_2d():
    with pytest.raises(ProcessError):
        Mess3().beliefs(np.zeros((3, 2)))


# ---------------------------------------------------------------------------
# RRXOR : invariants, beliefs
# ---------------------------------------------------------------------------


def test_rrxor_invariant_xor_et_etats():
    r = RRXOR()
    states, obs = r.sample(200, seed=11)
    # y_t = a XOR b avec etat = 2a + b
    a, b = states // 2, states % 2
    assert np.array_equal(a ^ b, obs)
    assert set(np.unique(states)) <= {0, 1, 2, 3}


def test_rrxor_transition_stationnaire():
    r = RRXOR()
    t = r.transition_matrix()
    assert np.allclose(t.sum(axis=1), 1.0)
    assert np.allclose(t @ r.stationary(), r.stationary())
    # chaque etat a exactement 2 successeurs equiprobables
    assert np.all((t > 0).sum(axis=1) == 2)
    assert np.allclose(t[t > 0], 0.5)


def test_rrxor_beliefs_sur_2_etats_coherents():
    r = RRXOR()
    states, obs = r.sample(100, seed=5)
    b = r.beliefs(obs)
    assert np.allclose(b.sum(axis=1), 1.0, atol=1e-12)
    e = r.emission_matrix()
    for k in range(len(obs)):
        coherent = e[:, int(obs[k])] > 0
        assert coherent.sum() == 2
        assert b[k, coherent] == pytest.approx(0.5)
        assert b[k, ~coherent] == pytest.approx(0.0, abs=1e-15)


def test_rrxor_beliefs_rejette_non_binaire():
    with pytest.raises(ProcessError):
        RRXOR().beliefs(np.array([0, 2, 1]))


# ---------------------------------------------------------------------------
# Banc factorise : produit, independance, vary-one
# ---------------------------------------------------------------------------


def test_bench_observation_jointe_et_beliefs_produit():
    bench = FactoredBench(Mess3(), RRXOR())
    run = bench.sample(30, seed_a=1, seed_b=2)
    assert run["obs_joint"].shape == (30, 2)
    assert np.array_equal(run["obs_joint"][:, 0], run["obs_a"])
    bel = bench.beliefs(run["obs_a"], run["obs_b"])
    na, nb = 3, 4
    assert bel["belief_joint"].shape == (30, na * nb)
    recompose = bel["belief_joint"].reshape(30, na, nb)
    assert np.allclose(recompose, bel["belief_a"][:, :, None] * bel["belief_b"][:, None, :])
    assert np.allclose(bel["belief_joint"].sum(axis=1), 1.0, atol=1e-12)


def test_bench_deux_mess3_independants():
    """L'option « deux Mess3 independants » de l'issue : meme architecture, facteurs homogenes."""
    bench = FactoredBench(Mess3(means=(-0.15, 0.0, 0.15)), Mess3(means=(1.0, 1.2, 1.4), name="mess3_b"))
    run = bench.sample(20, seed_a=0, seed_b=9)
    bel = bench.beliefs(run["obs_a"], run["obs_b"])
    assert bel["belief_joint"].shape == (20, 9)
    # independance : la trajectory de B ne change pas le belief de A
    run2 = bench.sample(20, seed_a=0, seed_b=10)
    bel2 = bench.beliefs(run2["obs_a"], run2["obs_b"])
    assert np.allclose(bel["belief_a"], bel2["belief_a"])


def test_bench_vary_one_facteur_gele_identique_libre_different():
    bench = FactoredBench(Mess3(), RRXOR())
    vy = bench.vary_one(40, frozen="a", seed_frozen=77, seeds_varying=[1, 2, 3])
    reps = np.stack(vy["varying_obs"])
    # le facteur gele ne depend PAS des seeds libres : meme trajectoire gelee
    # quand on change la liste des seeds qui varient. Sans cette mesure, la
    # propriete ne reposait que sur la construction du code (un seul appel a
    # sample(n, seed_frozen)), ce qu'aucune assertion ne verifiait.
    vy_autres_seeds = bench.vary_one(40, frozen="a", seed_frozen=77, seeds_varying=[4, 5])
    assert np.array_equal(vy["fixed_obs"], vy_autres_seeds["fixed_obs"])
    assert not np.array_equal(reps[0], reps[1])
    assert not np.array_equal(reps[1], reps[2])
    # gele : meme trajectoire reconstruite par le meme seed
    s_again, o_again = bench.factor_a.sample(40, 77)
    assert np.array_equal(vy["fixed_obs"], o_again)
    with pytest.raises(ProcessError):
        bench.vary_one(5, frozen="z", seed_frozen=0, seeds_varying=[1])


def test_bench_generateurs_incompatibles_rejetes():
    class PasUnGenerateur:
        pass

    with pytest.raises(ProcessError):
        FactoredBench(Mess3(), PasUnGenerateur())


def test_belief_simplex_coords_dans_le_triangle():
    m = Mess3()
    _, obs = m.sample(100, seed=13)
    xy = belief_simplex_coords(m.beliefs(obs))
    assert xy.shape == (100, 2)
    # tout point barycentrique du triangle est dans l'enveloppe convexe des sommets
    assert xy[:, 0].min() >= -1e-12 and xy[:, 0].max() <= 1.0 + 1e-12
    assert xy[:, 1].min() >= -1e-12 and xy[:, 1].max() <= np.sqrt(3) / 2 + 1e-12
    with pytest.raises(ProcessError):
        belief_simplex_coords(np.ones((2, 4)) / 4)
