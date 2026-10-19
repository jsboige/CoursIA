"""Non-anticipation de l'ablation RTG et de ``evaluate_dt`` (#21187, tranche 2).

Meme protocole que test_dt_causal_eval.py : deux series identiques jusqu'a la
ligne m, divergentes ensuite. Une chaine causale rend les memes logits pour
toute decision qui ne doit rien lire au-dela de m.

- ``ablation_rtg_leak`` : la condition B (G fixe) doit etre causale ; la
  condition A (RTG realise) garde la fuite par le RTG, et seulement elle,
  puisque les deux conditions partagent l'alignement. A sert de temoin negatif.
- ``train_rl_dt.evaluate_dt`` : avec ``rtg_per_step``, le RTG d'entree est un
  calendrier fixe ; sans lui, le RTG realise du test fuit (temoin negatif).
"""

import sys
from pathlib import Path

import numpy as np
import pandas  # noqa: F401  -- avant torch, cf. test_dt_causal_eval.py
import pytest

torch = pytest.importorskip("torch")

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ablation_rtg_leak import (  # noqa: E402
    causal_condition_actions, causal_eval_returns, count_trades,
    realized_rtg_rows, run_condition_c, score_actions, simulate_dt_portfolio,
)
from train_rl_dt import (  # noqa: E402
    DecisionTransformerModel, build_trajectories, evaluate_dt,
)
from validate_xrp_dt import dt_causal_positions  # noqa: E402

W = 20
C = 20
N = 200
N_FEAT = 4
COMMISSION_BPS = 10.0


class _Recorder(torch.nn.Module):
    """Delegue au modele et garde les logits de chaque appel, dans l'ordre."""

    def __init__(self, model):
        super().__init__()
        self.model = model
        self.calls = []

    def forward(self, states, actions, rtg, attention_mask=None):
        out = self.model(states, actions, rtg, attention_mask=attention_mask)
        self.calls.append((out.detach().cpu().numpy(),
                           attention_mask.detach().cpu().numpy()))
        return out


def _series(seed: int = 0):
    rng = np.random.default_rng(seed)
    prices = (100.0 * np.exp(np.cumsum(rng.normal(0.0, 0.02, N)))).astype(np.float32)
    feats = rng.normal(size=(N, N_FEAT)).astype(np.float32)
    return prices, feats


def _diverge(prices, feats, m: int, seed: int = 1):
    """Copie identique jusqu'a la ligne m incluse, differente au-dela."""
    rng = np.random.default_rng(seed)
    p2, f2 = prices.copy(), feats.copy()
    p2[m + 1:] *= np.exp(rng.normal(0.0, 0.2, N - m - 1)).astype(np.float32)
    f2[m + 1:] += rng.normal(0.0, 3.0, (N - m - 1, N_FEAT)).astype(np.float32)
    return p2, f2


def _model():
    torch.manual_seed(0)
    model = DecisionTransformerModel(state_dim=W * N_FEAT, d_model=32, nhead=4,
                                     num_layers=2, context_length=C)
    model.eval()
    return model


def _condition_logits(model, prices, feats, rtg_rows):
    """Logits de la decision qui pilote chaque rendement, chemin de l'ablation."""
    rec = _Recorder(model)
    _, first_k = dt_causal_positions(rec, prices, feats, W, C, 0.0,
                                     batch_size=64, device="cpu",
                                     rtg_rows=rtg_rows)
    last = np.concatenate([out[:, -1, :] for out, _ in rec.calls])
    logits = np.full((N - 1, 3), np.nan)
    logits[first_k:first_k + len(last)] = last
    return logits, first_k


def _fixed_g(prices):
    return np.full(len(prices), 0.05, dtype=np.float32)


def _realized(prices, feats):
    return realized_rtg_rows(prices, feats, window=W, commission_bps=COMMISSION_BPS)


@pytest.mark.parametrize("m", [4, 59, 149])
def test_condition_b_ignores_rows_after_its_return(m):
    model = _model()
    prices, feats = _series()
    p2, f2 = _diverge(prices, feats, m)
    a, first_k = _condition_logits(model, prices, feats, _fixed_g(prices))
    b, _ = _condition_logits(model, p2, f2, _fixed_g(p2))
    decided = np.arange(first_k, min(m + 1, N - 1))
    np.testing.assert_array_equal(a[decided], b[decided])
    # Controle positif : la perturbation atteint les decisions posterieures.
    later = np.arange(max(m + 3, first_k), N - 1)
    assert not np.allclose(a[later], b[later])


def test_condition_a_leaks_through_the_rtg_only():
    """Temoin negatif : le RTG realise transporte le futur, l'alignement non."""
    m = 149
    model = _model()
    prices, feats = _series()
    p2, f2 = _diverge(prices, feats, m)
    a, first_k = _condition_logits(model, prices, feats, _realized(prices, feats))
    b, _ = _condition_logits(model, p2, f2, _realized(p2, f2))
    decided = np.arange(first_k, m + 1)
    moved = int((np.abs(a[decided] - b[decided]).max(axis=1) > 0).sum())
    assert moved == len(decided)


def test_realized_rtg_rows_match_trajectories():
    prices, feats = _series()
    trajs = build_trajectories(prices, feats, window=W, context_length=C,
                               commission=COMMISSION_BPS / 10000.0)
    expected = np.asarray(trajs["rtg"], dtype=np.float32).reshape(-1)
    rows = _realized(prices, feats)
    assert len(rows) == N
    assert not rows[:W].any()
    np.testing.assert_allclose(rows[W:W + len(expected)], expected, rtol=1e-6)


def test_condition_actions_align_on_driven_returns():
    model = _model()
    prices, feats = _series()
    actions = causal_condition_actions(model, prices, feats, _fixed_g(prices),
                                       context_length=C, window=W)
    returns = causal_eval_returns(prices, W, C)
    assert len(actions) == len(returns) == N - 1 - (W + C)
    assert set(np.unique(actions)) <= {0, 1, 2}
    # Le rendement 0 de la serie est celui de la ligne W + C vers W + C + 1.
    expected = (prices[W + C + 1] - prices[W + C]) / (prices[W + C] + 1e-8)
    assert returns[0] == pytest.approx(float(expected))


def test_simulate_dt_portfolio_holds_the_position_it_sets():
    returns = np.array([0.01, -0.02, 0.04, 0.01])
    actions = np.array([1, 0, 2, 1])
    out = simulate_dt_portfolio(actions, returns, commission_bps=COMMISSION_BPS)
    # Positions tenues : 1, 1 (garder), 0 (a plat), 1 ; 10 pb par changement.
    np.testing.assert_allclose(out, [0.009, -0.02, -0.001, 0.009])
    with pytest.raises(ValueError):
        simulate_dt_portfolio(actions[:3], returns, commission_bps=COMMISSION_BPS)


def test_score_actions_counts_on_the_same_returns():
    returns = np.array([0.01, -0.02, 0.04, 0.01])
    res = score_actions(np.array([1, 0, 2, 1]), returns,
                        commission_bps=COMMISSION_BPS)
    assert res["n_trades"] == 3
    assert res["n_preds"] == 4
    assert res["auc"] == pytest.approx(0.75)
    assert res["exposure"] == pytest.approx(0.75)  # long, long, a plat, long


def test_condition_c_scores_the_returns_it_is_given():
    returns = np.random.default_rng(3).normal(0.0, 0.01, 159)
    first = run_condition_c(returns, n_trades_target=20,
                            commission_bps=COMMISSION_BPS, seed=7)
    again = run_condition_c(returns, n_trades_target=20,
                            commission_bps=COMMISSION_BPS, seed=7)
    assert first == again
    assert first["n_preds"] == len(returns)


@pytest.mark.parametrize("actions, expected", [
    ([0, 1, 0, 0], 1),      # un achat isole entre deux attentes : 1 changement
    ([1, 1, 1, 0], 1),      # achats repetes en position longue : rien de plus
    ([2, 0, 2, 0], 0),      # deja a plat : aucune commission
    ([1, 0, 2, 1], 3),      # entree, sortie, re-entree
])
def test_count_trades_counts_position_changes(actions, expected):
    actions = np.array(actions)
    assert count_trades(actions) == expected
    # Une commission par changement de position, pas par etiquette.
    out = simulate_dt_portfolio(actions, np.zeros(len(actions)),
                                commission_bps=COMMISSION_BPS)
    assert -out.sum() == pytest.approx(expected * COMMISSION_BPS / 10000.0)


def test_condition_c_matches_the_target_in_position_changes():
    returns = np.random.default_rng(5).normal(0.0, 0.01, 2000)
    counts = [run_condition_c(returns, n_trades_target=100,
                              commission_bps=COMMISSION_BPS, seed=s)["n_trades"]
              for s in range(8)]
    # Binomiale(2000, 0.05) : moyenne 100, ecart-type ~9,7.
    assert abs(np.mean(counts) - 100) < 10


def _eval_logits(model, prices, feats, rtg_per_step):
    """Logits de chaque fenetre d'``evaluate_dt``, a plat, dans l'ordre."""
    trajs = build_trajectories(prices, feats, window=W, context_length=C,
                               commission=COMMISSION_BPS / 10000.0)
    rec = _Recorder(model)
    metrics = evaluate_dt(rec, trajs, context_length=C, batch_size=64,
                          device="cpu", rtg_per_step=rtg_per_step)
    windows = np.concatenate([out for out, _ in rec.calls])
    return windows, metrics


def test_evaluate_dt_fixed_rtg_ignores_later_rows():
    m = 149
    model = _model()
    prices, feats = _series()
    p2, f2 = _diverge(prices, feats, m)
    a, metrics = _eval_logits(model, prices, feats, 0.002)
    b, _ = _eval_logits(model, p2, f2, 0.002)
    assert metrics["rtg_mode"] == "fixed-schedule"
    # La fenetre i lit les lignes W + i a W + i + C - 1 (etats et actions).
    early = np.arange(0, m - W - C + 2)
    np.testing.assert_array_equal(a[early], b[early])
    assert not np.allclose(a[early[-1] + 5:], b[early[-1] + 5:])


def test_evaluate_dt_realized_rtg_leaks():
    """Temoin negatif : le comportement historique fait bouger les memes fenetres."""
    m = 149
    model = _model()
    prices, feats = _series()
    p2, f2 = _diverge(prices, feats, m)
    a, metrics = _eval_logits(model, prices, feats, None)
    b, _ = _eval_logits(model, p2, f2, None)
    assert metrics["rtg_mode"] == "realized"
    early = np.arange(0, m - W - C + 2)
    assert not np.allclose(a[early], b[early])
