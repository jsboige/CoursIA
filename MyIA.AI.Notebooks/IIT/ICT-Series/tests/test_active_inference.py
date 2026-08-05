"""Tests du banc d'inférence active (module ICT-14b).

Vérifient :
* la croyance Beta sur grille (normalisation, moyenne = espérance) ;
* le terme épistémique (grand pour bras incertain, ~0 pour bras piqué) ;
* le terme pragmatique = moyenne a posteriori ;
* le **null adverse** : l'agent C (epistémique ablaté, gamma=0) se comporte
  ≡ l'agent B (glouton) — condition sine qua non qui crédite le banc ;
* la reproductibilité déterministe sous seed ;
* la récupération post-bascule est un nombre dans [0, 1].

Numpy + pytest. Le module ne dépend que de numpy.
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import active_inference as ai  # noqa: E402


# --------------------------------------------------------------------------- #
#  Croyance Beta sur grille                                                    #
# --------------------------------------------------------------------------- #
def test_belief_pdf_normalized():
    b = ai.BetaBelief(n_arms=3)
    assert b.pdf.shape == (3, ai._GRID_N)
    np.testing.assert_allclose(b.pdf.sum(axis=1), 1.0, atol=1e-9)


def test_belief_mean_matches_uniform_prior():
    # Prior Beta(1,1) = Uniforme -> moyenne = 0.5 pour tout bras.
    b = ai.BetaBelief(n_arms=4)
    np.testing.assert_allclose(b.mean(), 0.5, atol=1e-2)


def test_belief_update_shifts_mean_up_on_success():
    b = ai.BetaBelief(n_arms=2)
    for _ in range(20):
        b.update(0, 1.0)  # que des succès sur le bras 0
    assert b.mean()[0] > 0.8
    assert b.mean()[1] == pytest.approx(0.5, abs=1e-2)


# --------------------------------------------------------------------------- #
#  Les deux termes de l'EFE                                                    #
# --------------------------------------------------------------------------- #
def test_epistemic_value_high_for_uncertain_arm_low_for_certain():
    b = ai.BetaBelief(n_arms=2)
    # Bras 0 : on le pince 30 fois (~certain) ; bras 1 : jamais (incertain).
    for _ in range(30):
        b.update(0, 1.0)
    epi = ai.epistemic_value(b)
    # Le bras incertain a un gain d'info espéré strictement supérieur au bras
    # quasi-certain (qui est déjà piqué près de 1). On teste l'ordre (robuste)
    # plutôt qu'un seuil absolu, dépendant de la grille.
    assert epi[1] > epi[0]
    assert epi[0] < epi[1] / 5.0  # bras certain >> 5x moins informatif


def test_epistemic_value_nonnegative():
    b = ai.BetaBelief(n_arms=3)
    epi = ai.epistemic_value(b)
    assert np.all(epi >= -1e-9)  # une KL espérée est >= 0


def test_expected_reward_equals_posterior_mean():
    b = ai.BetaBelief(n_arms=3)
    np.testing.assert_allclose(ai.expected_reward(b), b.mean(), atol=1e-9)


def test_pragmatic_value_monotone_increasing_in_mean():
    # Le terme pragmatique (nats = E[ln P(o|C)]) est strictement croissant en
    # la moyenne a posteriori pour c > 0.5 -> argmax = politique gloutonne.
    b = ai.BetaBelief(n_arms=3)
    b.update(0, 1.0); b.update(0, 1.0)  # bras 0 tiré vers le haut
    pra = ai.pragmatic_value(b, c=ai.DEFAULT_C)
    assert pra[0] > pra[1]  # bras de moyenne plus haute => pragmatique plus grand
    assert np.all(pra <= 0.0)  # log-vraisemblance <= 0


# --------------------------------------------------------------------------- #
#  Null adverse : C (lam=0, épistémique ablaté) ≡ B (glouton)                   #
# --------------------------------------------------------------------------- #
def test_agent_C_equals_agent_B_null_adversarial():
    """Le null adverse (acceptance #9532) : ablater le terme épistémique
    (lam=0) doit redonner la politique gloutonne (B) — l'agent C ne tire
    jamais un bras de moyenne strictement inférieure au max. On le vérifie
    sur deux environnements en contrôlant qu'à chaque pas post-warmup le
    bras choisi par C est un bras de moyenne maximale (propriété gloutonne,
    robuste au bruit de tie-break). C'est la condition qui crédite le banc.
    """
    for seed in (0, 7, 42):
        env = ai.NonStationaryBandit(n_arms=3, horizon=200, seed=seed)
        tr_C = ai.run_episode(env, lam=0.0, warmup=True)
        # Reconstruction indépendante de la croyance (mêmes updates + oubli).
        b = ai.BetaBelief(env.n_arms, forget=ai.DEFAULT_FORGET)
        for t in range(env.horizon):
            arm = int(tr_C["actions"][t])
            mean = b.mean()
            if t >= env.n_arms:  # post-warmup : le bras choisi doit être greedy
                assert mean[arm] >= mean.max() - 1e-9, (
                    f"Null adverse rompu au seed {seed}, t={t}: C a tiré le bras "
                    f"{arm} (mean={mean[arm]:.4f}) alors que max={mean.max():.4f}"
                )
            b.update(arm, env.reward(t, arm))


def test_agent_C_actions_deterministic_equal_B_under_same_seed():
    """Comple'ment du null : C et B (tous deux lam=0) produisent des trajectoires
    identiques sous même seed — l'ablation est structurellement reproductible."""
    for seed in (3, 11):
        env = ai.NonStationaryBandit(n_arms=3, horizon=150, seed=seed)
        tr_B = ai.run_episode(env, lam=0.0)
        tr_C = ai.run_episode(env, lam=0.0)
        np.testing.assert_array_equal(tr_B["actions"], tr_C["actions"])


# --------------------------------------------------------------------------- #
#  Reproductibilité + métriques                                                #
# --------------------------------------------------------------------------- #
def test_episode_deterministic_under_seed():
    env1 = ai.NonStationaryBandit(n_arms=3, horizon=100, seed=11)
    env2 = ai.NonStationaryBandit(n_arms=3, horizon=100, seed=11)
    tr1 = ai.run_episode(env1, lam=1.0)
    tr2 = ai.run_episode(env2, lam=1.0)
    np.testing.assert_array_equal(tr1["actions"], tr2["actions"])
    np.testing.assert_allclose(tr1["F"], tr2["F"])


def test_recovery_rate_in_unit_interval():
    env = ai.NonStationaryBandit(n_arms=3, horizon=200, seed=3)
    tr = ai.run_episode(env, lam=1.0)
    rr = ai.recovery_rate(tr["actions"], env)
    assert 0.0 <= rr <= 1.0


def test_free_energy_step_positive():
    b = ai.BetaBelief(n_arms=2)
    # Surprise d'une issue improbable sous une croyance à 0.5 -> finie > 0.
    F = ai.free_energy_step(b, arm=0, reward=1.0)
    assert np.isfinite(F) and F > 0.0


def test_stationary_env_no_best_arm_change():
    env = ai.NonStationaryBandit(n_arms=3, horizon=100, stationary=True, seed=0)
    before = env.true_best_arm(10)
    after = env.true_best_arm(90)
    assert before == after
