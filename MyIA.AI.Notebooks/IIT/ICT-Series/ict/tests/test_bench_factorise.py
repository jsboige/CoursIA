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
    Mess3Canonical,
    Mess3_ObsCoupled,
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
    # Mess3 = Mess3Canonical (alias #16225) : validation de stay/emission_diag
    with pytest.raises(ProcessError):
        Mess3(stay=1.5)
    with pytest.raises(ProcessError):
        Mess3(emission_diag=0.2)  # <= 1/n : ne domine plus, casse le regime
    # Le banc gaussien historique garde sa propre validation (signaux continus)
    with pytest.raises(ProcessError):
        Mess3_ObsCoupled(std=0.0)
    with pytest.raises(ProcessError):
        Mess3_ObsCoupled(means=(0.0, 1.0))


def _mess3_bruteforce_beliefs(m, obs: np.ndarray) -> np.ndarray:
    """Enumeration exacte (independante du forward) : pour chaque sequence
    complete d'etats, poids joint = prior * prod(transitions) * prod(likelihoods),
    puis marginalisation en P(s_k | o_{0..n-1}) — beliefs lisses, a comparer
    au forward apres troncature des observations au meme prefixe.

    Generique : chemin discret via ``emission_matrix`` (Mess3Canonical),
    chemin gaussien via ``means``/``std`` (Mess3_ObsCoupled)."""
    n = len(obs)
    prior = m.stationary()
    t = m.transition_matrix()
    if hasattr(m, "emission_matrix") and not hasattr(m, "means"):
        e = m.emission_matrix()

        def lik(o, s: int) -> float:
            return float(e[s, int(o)])
    else:
        means = np.asarray(m.means)

        def lik(o, s: int) -> float:
            return math.exp(-0.5 * ((o - means[s]) / m.std) ** 2)

    weights = np.zeros(m.n_states)
    for seq in itertools.product(range(m.n_states), repeat=n):
        w = prior[seq[0]] * lik(obs[0], seq[0])
        for k in range(1, n):
            w *= t[seq[k - 1], seq[k]] * lik(obs[k], seq[k])
        weights[seq[n - 1]] += w
    return weights / weights.sum()


def test_mess3_beliefs_vs_enumeration_brute():
    m = Mess3(stay=0.9)
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


def test_mess3_obscoupled_beliefs_vs_enumeration_brute():
    """Le banc gaussien historique garde sa contre-verification bruteforce."""
    m = Mess3_ObsCoupled(means=(-0.15, 0.0, 0.15), std=0.05, stay=0.9)
    _, obs = m.sample(8, seed=42)
    assert np.allclose(m.beliefs(obs)[-1], _mess3_bruteforce_beliefs(m, obs), atol=1e-10)


def test_mess3_beliefs_somment_a_un_et_non_dirac():
    """Sur le banc canonique (#16225), le belief vit dans le simplexe SANS
    s'effondrer en Dirac : c'est la propriete que l'ancien banc obs = etat
    detruisait (accuracy tautologique 1.000)."""
    m = Mess3()
    states, obs = m.sample(500, seed=3)
    b = m.beliefs(obs)
    assert np.allclose(b.sum(axis=1), 1.0, atol=1e-12)
    max_probs = b.max(axis=1)
    # non-Dirac : jamais certain a 100%, mais informes : au-dessus du hasard 1/3
    assert max_probs.max() < 0.999, "le belief canonique ne doit pas etre un Dirac"
    assert max_probs.mean() > 1.0 / 3.0, "le belief canonique doit rester informatif"


def test_mess3_obscoupled_modes_lisibles():
    """Le banc gaussien historique conserve ses modes bien separees (comparateur)."""
    m = Mess3_ObsCoupled()
    states, obs = m.sample(500, seed=3)
    b = m.beliefs(obs)
    acc = (b.argmax(axis=1) == states).mean()
    assert acc > 0.95, f"modes mal separees, accuracy={acc}"


def test_mess3_beliefs_rejette_2d():
    with pytest.raises(ProcessError):
        Mess3().beliefs(np.zeros((3, 2)))


# ---------------------------------------------------------------------------
# RRXOR : conformite litterature (Riechers & Crutchfield 2018, 1706.00883)
# ---------------------------------------------------------------------------


def test_rrxor_triplets_xor_alignes():
    """Le processus repete (r1, r2, r1 XOR r2) : le 3e symbole de chaque
    triplet est le XOR des deux precedents -- sur toute trajectoire."""
    r = RRXOR()
    states, obs = r.sample(300, seed=11)
    k = (len(obs) // 3) * 3
    assert np.array_equal(obs[2:k:3], obs[0:k:3] ^ obs[1:k:3])
    assert set(np.unique(states)) <= {0, 1, 2, 3, 4}


def test_rrxor_correlations_par_paires_nulles():
    """Propriete litterature : correlations par paires nulles (spectre plat)
    -- toute la structure vit dans la contrainte de triplet."""
    r = RRXOR()
    _, obs = r.sample(60000, seed=42)
    p1 = obs[1:]
    p0 = obs[:-1]
    corr = np.corrcoef(p0.astype(float), p1.astype(float))[0, 1]
    assert abs(corr) < 0.02
    # ... mais le triplet, lui, est deterministe : structure masquee
    k = (len(obs) // 3) * 3
    assert np.array_equal(obs[2:k:3], obs[0:k:3] ^ obs[1:k:3])


def test_rrxor_transition_stationnaire():
    r = RRXOR()
    t = r.transition_matrix()
    assert np.allclose(t.sum(axis=1), 1.0)
    assert np.allclose(r.stationary() @ t, r.stationary())
    # G et A ont 2 successeurs equiprobables ; X est deterministe vers G
    for s in (0, 1, 2):
        assert (t[s] > 0).sum() == 2
        np.testing.assert_allclose(t[s][t[s] > 0], 0.5, atol=1e-12)
    np.testing.assert_allclose(t[3, 0], 1.0, atol=1e-12)
    np.testing.assert_allclose(t[4, 0], 1.0, atol=1e-12)


def test_rrxor_beliefs_filtration_aretes():
    """La filtration forward Mealy : b' = normaliser(b @ W[:, :, y]).
    Controle sur sequence (0, 0) : la croyance doit coder l'alignement de
    phase -- prediction suivante P(y=0) = 2/3, pas 1/2."""
    r = RRXOR()
    b = r.beliefs(np.array([0, 0]))
    assert np.allclose(b.sum(axis=1), 1.0, atol=1e-12)
    W = r.edge_tensor()
    p0 = float((b[-1] @ W[:, :, 0]).sum())
    assert p0 == pytest.approx(2.0 / 3.0, abs=1e-10)
    # les etats incompatibles avec le chemin sont exclus
    assert b[-1][2] == pytest.approx(0.0, abs=1e-12)  # A1 exclu par r1 = 0


def test_rrxor_beliefs_synchronise_vers_dirac():
    """Depuis le prior stationnaire, un long prefix suffit a synchroniser :
    la croyance converge vers un Dirac sur un etat causal (5 etats
    recurrents de la S-MSP, cf. litterature p. 17)."""
    r = RRXOR()
    _, obs = r.sample(300, seed=7)
    b = r.beliefs(obs)
    entropie_finale = float(-(b[-1] * np.log(np.clip(b[-1], 1e-12, 1))).sum())
    assert entropie_finale < 1e-6


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
    na, nb = 3, 5
    assert bel["belief_joint"].shape == (30, na * nb)
    recompose = bel["belief_joint"].reshape(30, na, nb)
    assert np.allclose(recompose, bel["belief_a"][:, :, None] * bel["belief_b"][:, None, :])
    assert np.allclose(bel["belief_joint"].sum(axis=1), 1.0, atol=1e-12)


def test_bench_deux_mess3_independants():
    """L'option « deux Mess3 independants » de l'issue : meme architecture, facteurs homogenes."""
    bench = FactoredBench(Mess3_ObsCoupled(means=(-0.15, 0.0, 0.15)), Mess3_ObsCoupled(means=(1.0, 1.2, 1.4), name="mess3_b"))
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
