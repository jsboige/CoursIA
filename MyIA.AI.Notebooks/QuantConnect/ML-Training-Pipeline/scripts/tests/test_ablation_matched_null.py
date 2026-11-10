"""Temoin apparie en exposition de l'ablation RTG (#21187, tranche 3).

Le temoin de la tranche 2 (``run_condition_c``) etait apparie a A en
changements de position, pas en exposition. Le temoin de la tranche 3 permute
les longueurs des periodes longues entre elles et celles des periodes a plat
entre elles : chaque tirage a exactement l'exposition et le nombre de
changements de position de la condition, seul le calendrier change.

- ``permute_runs`` garde l'exposition, les changements de position, l'etat de
  depart et l'alternance ;
- ``matched_null`` note la condition par le meme calcul que ses tirages, qui
  est celui de ``simulate_dt_portfolio`` ;
- un calendrier parfait (long exactement sur les hausses) sort du temoin
  (temoin positif), un calendrier sans information y reste (calibration) ;
- ``symbol_null_test`` et ``skill_verdict`` appliquent le protocole publie sur
  #21187 avant toute mesure ;
- la ligne C (``null_condition_row``) ne porte que le ``hit_rate`` du temoin,
  calcule comme celui de A et B sur la position tenue : sa cle ``auc`` est
  vide, le temoin n'ayant pas d'etiquettes d'action.
"""

import sys
from pathlib import Path

import numpy as np
import pandas  # noqa: F401  -- avant torch, cf. test_dt_causal_eval.py
import pytest

pytest.importorskip("torch")

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ablation_rtg_leak import (  # noqa: E402
    compute_sharpe, count_trades, held_positions, matched_null,
    null_condition_row, null_p_value, permute_runs, position_returns,
    row_sharpes, score_actions, simulate_dt_portfolio, skill_verdict,
    symbol_null_test,
)

COMMISSION_BPS = 5.0


def _random_actions(rng, n, flip_prob=0.1):
    """Actions aleatoires : bascule de position avec ``flip_prob``, sinon garder."""
    actions = np.zeros(n, dtype=np.int64)
    position = 0
    for i in range(n):
        if rng.random() < flip_prob:
            position = 1 - position
            actions[i] = 1 if position else 2
    return actions


def _runs(positions):
    starts = np.concatenate([[0], np.flatnonzero(np.diff(positions) != 0) + 1])
    lengths = np.diff(np.concatenate([starts, [len(positions)]]))
    return positions[starts], lengths


@pytest.mark.parametrize("seed", range(20))
def test_permute_runs_keeps_exposure_and_position_changes(seed):
    rng = np.random.default_rng(seed)
    positions = held_positions(_random_actions(rng, 150, flip_prob=0.15))
    draw = permute_runs(positions, rng)
    assert len(draw) == len(positions)
    assert draw.sum() == positions.sum()  # exposition exacte
    # Changements de position comptes comme ``count_trades`` (a plat avant).
    changes = lambda p: int(np.sum(np.diff(np.concatenate([[0.0], p])) != 0))
    assert changes(draw) == changes(positions)
    assert changes(positions) == count_trades(np.where(positions > 0, 1, 2))
    # Meme etat de depart, meme alternance, memes longueurs a permutation pres.
    states, lengths = _runs(positions)
    draw_states, draw_lengths = _runs(draw)
    np.testing.assert_array_equal(draw_states, states)
    for mask in (states > 0, states == 0):
        assert sorted(draw_lengths[mask]) == sorted(lengths[mask])


def test_permute_runs_moves_the_entries():
    rng = np.random.default_rng(0)
    positions = held_positions(_random_actions(rng, 300, flip_prob=0.1))
    draws = [permute_runs(positions, rng) for _ in range(20)]
    # Le temoin change le calendrier : la plupart des tirages different.
    assert sum(not np.array_equal(d, positions) for d in draws) >= 18


def test_permute_runs_is_deterministic_by_seed():
    positions = held_positions(_random_actions(np.random.default_rng(1), 200))
    first = permute_runs(positions, np.random.default_rng([42, 3, 0]))
    again = permute_runs(positions, np.random.default_rng([42, 3, 0]))
    np.testing.assert_array_equal(first, again)


def test_position_returns_match_simulate_dt_portfolio():
    rng = np.random.default_rng(2)
    returns = rng.normal(0.0, 0.01, 120)
    rows = [_random_actions(rng, 120, flip_prob=0.2) for _ in range(5)]
    out = position_returns(np.stack([held_positions(a) for a in rows]), returns,
                           commission_bps=COMMISSION_BPS)
    for actions, row in zip(rows, out):
        np.testing.assert_allclose(
            row, simulate_dt_portfolio(actions, returns, commission_bps=COMMISSION_BPS))


def test_row_sharpes_match_compute_sharpe():
    rng = np.random.default_rng(3)
    port = rng.normal(0.0005, 0.01, (4, 80))
    port[2] = 0.0  # ecart-type nul : 0, comme compute_sharpe
    np.testing.assert_allclose(row_sharpes(port), [compute_sharpe(r) for r in port])
    assert np.all(row_sharpes(port[:, :9]) == 0.0)  # moins de 10 rendements


def test_matched_null_scores_the_condition_like_the_portfolio():
    rng = np.random.default_rng(4)
    returns = rng.normal(0.0, 0.01, 160)
    actions = _random_actions(rng, 160)
    res = matched_null(actions, returns, n_draws=50, commission_bps=COMMISSION_BPS,
                       rng=np.random.default_rng(0))
    expected = compute_sharpe(
        simulate_dt_portfolio(actions, returns, commission_bps=COMMISSION_BPS))
    assert res["sharpe"] == pytest.approx(expected, abs=1e-12)
    assert res["null"].shape == (50,)
    again = matched_null(actions, returns, n_draws=50, commission_bps=COMMISSION_BPS,
                         rng=np.random.default_rng(0))
    np.testing.assert_array_equal(res["null"], again["null"])


def test_perfect_timing_leaves_the_null():
    # Temoin positif : long exactement sur les hausses, meme exposition et
    # memes changements de position dans chaque tirage, mais pas le calendrier.
    returns = np.random.default_rng(5).normal(0.0, 0.01, 160)
    actions = np.where(returns > 0, 1, 2)
    res = matched_null(actions, returns, n_draws=999, commission_bps=COMMISSION_BPS,
                       rng=np.random.default_rng(1))
    assert null_p_value(res["sharpe"], res["null"]) == pytest.approx(1 / 1000)


@pytest.mark.parametrize("actions", [np.full(100, 2), np.full(100, 1), np.zeros(100)])
def test_a_single_run_ties_with_every_draw(actions):
    # Toujours a plat ou toujours long : chaque tirage est la condition elle-meme.
    returns = np.random.default_rng(6).normal(0.0, 0.01, 100)
    res = matched_null(actions.astype(np.int64), returns, n_draws=99,
                       commission_bps=COMMISSION_BPS, rng=np.random.default_rng(2))
    assert null_p_value(res["sharpe"], res["null"]) == 1.0


def test_hit_rate_is_the_same_measure_for_conditions_and_null():
    # Positions tenues : long, long, a plat, long ; rendements +, -, +, +.
    returns = np.array([0.01, -0.02, 0.04, 0.01])
    res = score_actions(np.array([1, 0, 2, 1]), returns, commission_bps=COMMISSION_BPS)
    assert res["hit_rate"] == pytest.approx(0.5)
    assert res["auc"] == pytest.approx(0.75)  # etiquette d'achat, pas la position
    # Une seule periode : chaque tirage est la condition, meme hit_rate.
    flat_long = np.full(50, 1)
    rets = np.random.default_rng(8).normal(0.0, 0.01, 50)
    null = matched_null(flat_long, rets, n_draws=20, commission_bps=COMMISSION_BPS,
                        rng=np.random.default_rng(3))
    scored = score_actions(flat_long, rets, commission_bps=COMMISSION_BPS)
    assert null["hit_rate"] == pytest.approx(scored["hit_rate"])


def test_condition_c_row_has_no_label_accuracy():
    res_a = {"sharpe_bh": 0.8, "n_trades": 6, "exposure": 0.7, "n_preds": 250}
    null_a = {"null": np.array([0.5, 0.7, 0.9]), "hit_rate": 0.51234}
    row = null_condition_row(res_a, null_a)
    assert row["auc"] is None
    assert row["hit_rate"] == 0.5123
    assert row["sharpe_dt"] == pytest.approx(0.7)
    assert row["delta_sharpe"] == pytest.approx(-0.1)
    assert (row["n_trades"], row["exposure"], row["n_preds"]) == (6, 0.7, 250)


def test_uninformed_timing_is_calibrated():
    # Calibration : un calendrier tire sans information sur les rendements.
    rng = np.random.default_rng(7)
    p_values = []
    for _ in range(200):
        returns = rng.normal(0.0003, 0.01, 150)
        res = matched_null(_random_actions(rng, 150, flip_prob=0.1), returns,
                           n_draws=199, commission_bps=COMMISSION_BPS, rng=rng)
        p_values.append(null_p_value(res["sharpe"], res["null"]))
    # Binomiale(200, 0,05) : moyenne 10, ecart-type ~3,1.
    assert 2 <= sum(p < 0.05 for p in p_values) <= 22
    assert 0.4 < np.mean(p_values) < 0.6


def test_symbol_null_test_averages_seeds_per_fold():
    null_a = np.linspace(-1.0, 1.0, 9)
    null_b = np.linspace(-0.5, 1.5, 9)
    per_seed = [
        {0: (0.9, null_a), 1: (0.0, null_a)},
        {0: (1.1, null_b)},  # le fold 1 manque pour cette graine
    ]
    res = symbol_null_test(per_seed)
    fold0, fold1 = res["folds"]
    assert (fold0["n_seeds"], fold1["n_seeds"]) == (2, 1)
    assert fold0["sharpe"] == pytest.approx(1.0)
    mean_null = (null_a + null_b) / 2  # tirage j moyenne sur les graines
    assert fold0["p"] == pytest.approx(null_p_value(1.0, mean_null))
    assert fold1["p"] == pytest.approx(null_p_value(0.0, null_a))
    # Fisher : -2 somme ln p suit un khi-deux a 2k degres de liberte.
    from scipy.stats import chi2
    stat = -2 * np.log([fold0["p"], fold1["p"]]).sum()
    assert res["fisher_p"] == pytest.approx(chi2.sf(stat, 4))


@pytest.mark.parametrize("n_below, expected", [
    (6, "SKILL-CONFIRMED"),
    (4, "SKILL-CONFIRMED"),
    (3, "INCONCLUSIVE"),
    (1, "INCONCLUSIVE"),
    (0, "NO SKILL"),
])
def test_skill_verdict_on_six_symbols(n_below, expected):
    symbols = ["SPY", "XLF", "XLK", "IEF", "GLD", "USO"]
    p_holm = {s: (0.01 if i < n_below else 0.4) for i, s in enumerate(symbols)}
    verdict, skilled = skill_verdict(p_holm)
    assert verdict == expected
    assert len(skilled) == n_below
