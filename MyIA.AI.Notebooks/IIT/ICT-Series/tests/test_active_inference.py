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


# --------------------------------------------------------------------------- #
#  Dynamique non-stationnaire + métriques non couvertes                        #
# --------------------------------------------------------------------------- #
def test_bandit_regime_switches_optimal_arm_at_switch_t():
    """La bascule de régime inverse le bras optimal exactement à switch_t.

    Miroir non-stationnaire du test ci-dessus : par défaut probs_pre est
    décroissante (bras 0 = 0.8 optimal) et probs_post l'inverse (dernier
    bras = 0.8 optimal). Le bras vrai optimal bascule donc 0 -> K-1 à
    switch_t — c'est le cœur de la non-stationnarité qui motive tout le banc."""
    env = ai.NonStationaryBandit(n_arms=3, horizon=100, seed=0)
    s = env.switch_t
    assert env.true_best_arm(0) == 0               # début : bras 0 (p=0.8)
    assert env.true_best_arm(s - 1) == 0           # juste avant bascule
    assert env.true_best_arm(s) == 2               # à la bascule : dernier bras
    assert env.true_best_arm(env.horizon - 1) == 2  # fin : dernier bras


def test_optimal_reward_rate_equals_max_true_prob():
    """optimal_reward_rate(t) = proba vraie maximale à l'instant t (borne de regret)."""
    env = ai.NonStationaryBandit(n_arms=3, horizon=60, seed=0)
    for t in (0, 5, env.switch_t, env.switch_t + 1, env.horizon - 1):
        assert env.optimal_reward_rate(t) == pytest.approx(float(env._probs_t[t].max()))


def test_cumulative_regret_equals_sum_and_nonneg():
    """cumulative_regret(trace) = somme des regrets instantanés, et >= 0.

    Le regret instantané = optimal_reward_rate(t) - p_vraie(arm choisi) =
    max - p, donc toujours >= 0 ; la somme aussi. La fonction publique
    cumulative_regret n'était pas exercée jusqu'ici."""
    env = ai.NonStationaryBandit(n_arms=3, horizon=100, seed=0)
    tr = ai.run_episode(env, lam=1.0)
    assert ai.cumulative_regret(tr) == pytest.approx(float(tr["regret"].sum()))
    assert ai.cumulative_regret(tr) >= 0.0
    # Chaque pas est non négatif (max des probas - proba du bras tiré).
    assert (tr["regret"] >= -1e-12).all()


def test_recovery_rate_window_limit_and_empty_returns_nan():
    """window limite la fenêtre post-bascule ; fenêtre vide (window=0) -> nan.

    Exerce la branche ``end <= s`` (retour nan) du garde, non couverte par
    test_recovery_rate_in_unit_interval qui n'utilise pas l'argument window."""
    env = ai.NonStationaryBandit(n_arms=3, horizon=100, seed=3)
    tr = ai.run_episode(env, lam=1.0)
    # Fenêtre limitée : valeur dans [0, 1], évaluée sur moins de pas.
    half = ai.recovery_rate(tr["actions"], env, window=10)
    assert 0.0 <= half <= 1.0
    # Fenêtre vide -> nan (branche de garde end <= s).
    assert np.isnan(ai.recovery_rate(tr["actions"], env, window=0))


def test_choose_greedy_lam_zero_picks_highest_mean():
    """choose(lam=0) = politique gloutonne pure -> argmax(moyenne a posteriori).

    Le terme pragmatique est strictement croissant en p_k pour c > 0.5,
    donc lam=0 (epistémique ablaté) sélectionne le bras de moyenne la plus
    haute. Vérifie la réduction greedy du choix indépendamment du tirage
    aléatoire (l'écart net de moyenne l'emporte sur le bris d'égalité 1e-12)."""
    b = ai.BetaBelief(n_arms=3)
    for _ in range(20):
        b.update(0, 1.0)  # bras 0 : que des succès -> moyenne ~0.95
    rng = np.random.default_rng(0)
    assert b.mean()[0] > b.mean()[1]  # prémisse : écart net
    assert ai.choose(b, lam=0.0, rng=rng) == 0
