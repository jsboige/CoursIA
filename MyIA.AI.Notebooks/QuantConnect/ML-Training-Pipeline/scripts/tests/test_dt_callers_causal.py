"""Appelants de ``evaluate_dt`` sous le protocole causal (#21187, tranche 4).

``eval_rl_dt.py``, ``sweep_l4_decision_transformer.py`` et
``train_dt_multiseed.py`` notaient le DT avec le RTG realise du test (somme
des recompenses futures) et des positions mal alignees sur les rendements.
Ces tests fixent le contrat apres migration : metriques des decisions du
modele, cout compte une fois, protocole declare dans les sorties.
"""

from __future__ import annotations

from pathlib import Path

import numpy as np
import pandas  # noqa: F401  -- avant torch (crash Windows sinon)
import pytest
import torch

from eval_rl_dt import dt_trading_metrics, run_dry_run
from validate_xrp_dt import CAUSAL_EVAL_PROTOCOL, causal_eval_series

SCRIPTS = Path(__file__).resolve().parents[1]
WINDOW, CTX, COMMISSION = 5, 4, 0.001


class _Const(torch.nn.Module):
    """Modele factice : toujours la meme action (0 hold, 1 buy, 2 sell)."""

    def __init__(self, action: int):
        super().__init__()
        self.action = action

    def forward(self, states, actions, rtg, attention_mask=None):
        logits = torch.zeros(states.shape[0], states.shape[1], 3)
        logits[..., self.action] = 1.0
        return logits


def _series(n: int = 120, seed: int = 0):
    rng = np.random.default_rng(seed)
    prices = (100 * np.exp(np.cumsum(rng.normal(0, 0.01, n)))).astype(np.float32)
    feats = rng.normal(0, 1, (n, 3)).astype(np.float32)
    return prices, feats


def _returns(prices):
    first_k = WINDOW + CTX
    _, _, _, rets = causal_eval_series(prices, np.zeros(len(prices) - 1), first_k, WINDOW)
    return rets


def test_always_buy_pays_one_entry():
    prices, feats = _series()
    m = dt_trading_metrics(_Const(1), prices, feats, WINDOW, CTX, 0.0, COMMISSION)
    rets = _returns(prices)
    assert m["n_returns"] == len(rets)
    assert m["exposure"] == 1.0
    assert m["n_trades"] == 1
    # Un seul changement de position (entree) : la commission est comptee une fois.
    assert m["total_commission"] == pytest.approx(COMMISSION, abs=1e-4)
    assert m["cost_drag_bps"] == pytest.approx(COMMISSION * 10_000, abs=1e-2)
    assert m["gross_return"] == pytest.approx(float(np.sum(rets)), abs=1e-4)
    # Toujours long = buy-and-hold sur la meme fenetre, au cout pres.
    assert m["gross_sharpe"] == pytest.approx(m["bh_sharpe"], abs=1e-4)


def test_always_hold_is_flat():
    prices, feats = _series()
    m = dt_trading_metrics(_Const(0), prices, feats, WINDOW, CTX, 0.0, COMMISSION)
    assert m["exposure"] == 0.0
    assert m["n_trades"] == 0
    assert m["total_commission"] == 0.0
    assert m["sharpe"] == 0.0


def test_always_sell_is_short():
    prices, feats = _series()
    m = dt_trading_metrics(_Const(2), prices, feats, WINDOW, CTX, 0.0, COMMISSION)
    assert m["exposure"] == 1.0
    assert m["gross_return"] == pytest.approx(-float(np.sum(_returns(prices))), abs=1e-4)


def test_dry_run_declares_causal_protocol():
    result = run_dry_run()
    assert result["eval_protocol"] == CAUSAL_EVAL_PROTOCOL
    assert result["rtg_mode"] == "fixed-schedule"
    for key in ("sharpe", "max_drawdown", "exposure", "n_trades", "bh_sharpe"):
        assert np.isfinite(result[key])


@pytest.mark.parametrize("script", [
    "eval_rl_dt.py", "sweep_l4_decision_transformer.py", "train_dt_multiseed.py",
])
def test_callers_no_longer_feed_realized_rtg(script):
    src = (SCRIPTS / script).read_text(encoding="utf-8")
    # Le chemin realise lisait batch["rtg"] (RTG du test) ; les appelants
    # passent desormais rtg_per_step, appris sur le fold d'entrainement.
    assert 'batch["rtg"]' not in src
    assert "train_rtg_per_step(" in src
    assert "rtg_per_step=rtg_step" in src
