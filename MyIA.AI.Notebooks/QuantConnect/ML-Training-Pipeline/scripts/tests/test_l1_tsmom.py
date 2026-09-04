"""Unit tests for L1_tsmom — Time-Series Momentum baseline (reference).

L1 (Moskowitz-Ooi-Pedersen 2012 style TSMOM) is the *reference baseline* of the
Curriculum-V3 trading epic (#1409): every long-horizon strategy is compared
against it. It is a production script (455 lines) yet had ZERO dedicated tests.

This suite covers the three pure functions that carry the baseline's logic:

- ``compute_tsmom_signal``: sign(past return) — the TSMOM long/short signal
- ``compute_vol_scale``: target-vol position sizing, clipped to [0.1, 3.0]
- ``compute_verdict``: BEATS / NO BEATS / INCONCLUSIVE gate

It also pins a **methodology property** (see ``TestComputeVerdict``):
``compute_verdict`` maps zero cross-seed dispersion to ``t_stat = 0`` and
therefore can never return BEATS on identical Sharpes. That state was the
nominal behavior of L1 until #14470: the seed loop built an rng that was
never consumed, so the 4 seeds ran byte-identical computations. Since #14470
the seeds are LIVE (``draw_seed_view``: sub-basket 80% without replacement +
origin offset 0-40 business days, same view for model and baseline), so real
runs produce non-zero dispersion and the gate measures something — the
integration tests in ``TestLiveSeeds`` pin exactly that.

All fixtures are deterministic synthetic series — no network, no GPU, no data
files. Runs in well under a second on CPU.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from L1_tsmom import (  # noqa: E402
    MAX_ORIGIN_OFFSET,
    SUBBASKET_SHARE,
    TARGET_VOL,
    compute_tsmom_signal,
    compute_verdict,
    compute_vol_scale,
    draw_seed_view,
    run_buyhold_baseline,
    run_tsmom_single_lookback,
)
from panier_loader import get_panier_symbols  # noqa: E402


def _closes(n: int = 200, drift: float = 0.0, vol: float = 0.01, seed: int = 0) -> pd.Series:
    """Deterministic synthetic close-price series."""
    rng = np.random.default_rng(seed)
    rets = drift + rng.standard_normal(n) * vol
    return pd.Series(100 * np.exp(np.cumsum(rets)), name="close")


# ── compute_tsmom_signal ────────────────────────────────────────────────────

class TestComputeTsmomSignal:
    def test_uptrend_yields_plus_one(self) -> None:
        # Strictly rising prices -> every past return (after lookback) positive.
        closes = pd.Series(np.arange(100, dtype=float) * 0.1 + 100)
        sig = compute_tsmom_signal(closes, lookback=5)
        # First `lookback` are NaN -> sign 0; rest must be +1.
        assert (sig.iloc[5:] == 1.0).all()
        assert (sig.iloc[:5].isna() | (sig.iloc[:5] == 0)).all()

    def test_downtrend_yields_minus_one(self) -> None:
        closes = pd.Series(np.arange(100, dtype=float)[::-1] * 0.1 + 100)  # descending
        sig = compute_tsmom_signal(closes, lookback=5)
        assert (sig.iloc[5:] == -1.0).all()

    def test_values_in_valid_set(self) -> None:
        sig = compute_tsmom_signal(_closes(150), lookback=21)
        valid = sig.dropna()
        assert valid.isin({-1.0, 0.0, 1.0}).all()

    def test_lookback_controls_warmup_nan_count(self) -> None:
        # pct_change(lookback) yields `lookback` leading NaNs.
        closes = _closes(120)
        for lb in (5, 21, 63):
            sig = compute_tsmom_signal(closes, lookback=lb)
            assert int(sig.isna().sum()) == lb


# ── compute_vol_scale ───────────────────────────────────────────────────────

class TestComputeVolScale:
    def test_clipped_to_valid_range(self) -> None:
        vs = compute_vol_scale(_closes(200, vol=0.02), lookback=21)
        valid = vs.dropna()
        assert (valid >= 0.1 - 1e-9).all()
        assert (valid <= 3.0 + 1e-9).all()

    def test_higher_vol_yields_lower_scale(self) -> None:
        # Inverse relationship: a more volatile series gets a smaller position.
        low_vol = compute_vol_scale(_closes(200, vol=0.005, seed=1), lookback=21).dropna()
        high_vol = compute_vol_scale(_closes(200, vol=0.05, seed=1), lookback=21).dropna()
        assert low_vol.median() > high_vol.median()

    def test_constant_prices_hit_upper_clip(self) -> None:
        # Zero variance -> daily_vol 0 -> annual_vol floored at 0.01 ->
        # scale = TARGET_VOL / 0.01 = 15 -> clipped to 3.0.
        flat = pd.Series(np.full(100, 100.0))
        vs = compute_vol_scale(flat, lookback=21).dropna()
        np.testing.assert_allclose(vs.values, 3.0)

    def test_default_target_vol_constant_used(self) -> None:
        # Smoke-check the module default (TARGET_VOL=0.15) is wired in:
        # a series whose annual vol is exactly 0.15 should give scale ~1.0.
        # Construct daily returns whose rolling-21 std annualizes near 0.15.
        rng = np.random.default_rng(7)
        n = 300
        daily_sigma = 0.15 / np.sqrt(252)
        rets = rng.standard_normal(n) * daily_sigma
        closes = pd.Series(100 * np.exp(np.cumsum(rets)))
        vs = compute_vol_scale(closes, lookback=63, target_vol=TARGET_VOL).dropna()
        # Median scale should be near 1.0 (within a loose band; rolling-std is noisy).
        assert 0.4 < vs.median() < 2.5


# ── compute_verdict ─────────────────────────────────────────────────────────

def _tsmom_results(sharpes: list[float]) -> dict:
    return {"seeds": [{"net_sharpe": s} for s in sharpes]}


def _bh_results(sharpes: list[float]) -> dict:
    return {"seeds": [{"sharpe": s} for s in sharpes]}


class TestComputeVerdict:
    def test_clear_beats(self) -> None:
        # Variability across seeds -> non-zero std -> t_stat well above 2.0,
        # delta > 0.10, all 4 seeds beat bh+0.10 -> BEATS.
        out = compute_verdict(
            _tsmom_results([1.0, 1.2, 1.1, 1.3]),
            _bh_results([0.5, 0.5, 0.5, 0.5]),
        )
        assert out["verdict"] == "BEATS"
        assert out["mean_tsmom_net_sharpe"] == pytest.approx(1.15)
        assert out["delta_sharpe"] == pytest.approx(0.65)
        assert out["t_stat"] >= 2.0
        assert out["seeds_positive_delta"] == 4

    def test_no_beats_when_delta_negative(self) -> None:
        out = compute_verdict(
            _tsmom_results([0.3, 0.3, 0.3, 0.3]),
            _bh_results([0.5, 0.5, 0.5, 0.5]),
        )
        assert out["verdict"] == "NO BEATS"
        assert out["delta_sharpe"] <= 0

    def test_inconclusive_when_edge_below_gate(self) -> None:
        # Positive delta but small + high variance -> t_stat < 2 -> INCONCLUSIVE.
        out = compute_verdict(
            _tsmom_results([0.9, 0.4, 0.85, 0.45]),  # mean ~0.65, high spread
            _bh_results([0.5, 0.5, 0.5, 0.5]),
        )
        assert out["verdict"] == "INCONCLUSIVE"

    def test_returns_full_metric_structure(self) -> None:
        out = compute_verdict(
            _tsmom_results([1.0, 1.1]),
            _bh_results([0.5, 0.5]),
        )
        for key in ("verdict", "mean_tsmom_net_sharpe", "std_tsmom_net_sharpe",
                    "mean_bh_sharpe", "std_bh_sharpe", "delta_sharpe",
                    "t_stat", "seeds_positive_delta", "n_seeds"):
            assert key in out
        assert out["n_seeds"] == 2

    def test_deterministic_identical_sharpes_yield_zero_t_stat(self) -> None:
        """★ Methodology finding (pinned, not fixed).

        TSMOM and buy-and-hold are *deterministic* — there is no stochastic
        training, so the 4 seeds (0/1/7/42) produce byte-identical Sharpes.
        Consequently the cross-seed std is 0, ``delta_std = sqrt(0+0) = 0``,
        and ``compute_verdict`` guards the division (``delta_std > 1e-10``)
        by setting ``t_stat = 0.0``. The ``t_stat >= 2.0`` BEATS gate is
        therefore structurally unreachable for this class of strategy, even
        when TSMOM genuinely outperforms buy-and-hold by a wide margin.

        This test pins that behavior. A future methodology fix (e.g. a paired
        t-test on daily return differences, which IS meaningful for
        deterministic strategies) should make this assertion fail — that is
        the signal the fix landed. The fix is out of scope here because it
        changes how a KEEPER's verdict is computed (needs a methodology
        decision, not a unilateral edit).
        """
        # Identical TSMOM sharpes (a zero-dispersion input),
        # a large positive delta, every seed beats bh+0.10 — yet NOT BEATS.
        out = compute_verdict(
            _tsmom_results([1.5, 1.5, 1.5, 1.5]),
            _bh_results([0.5, 0.5, 0.5, 0.5]),
        )
        assert out["delta_sharpe"] == pytest.approx(1.0)  # large edge
        assert out["t_stat"] == 0.0  # structurally zero (std collapsed)
        assert out["verdict"] == "INCONCLUSIVE"  # BEATS unreachable despite the edge

    def test_verdict_reachable_with_live_dispersion(self) -> None:
        """Mirror of the zero-dispersion pin: with the dispersion that live
        seeds produce (#14470), the same large edge DOES reach BEATS."""
        out = compute_verdict(
            _tsmom_results([1.4, 1.5, 1.45, 1.55]),
            _bh_results([0.5, 0.5, 0.5, 0.5]),
        )
        assert out["t_stat"] >= 2.0
        assert out["verdict"] == "BEATS"


# ── live seeds (#14470) ─────────────────────────────────────────────────────

_SYMBOLS = get_panier_symbols()


def _synthetic_closes(n_rows: int = 900, n_syms: int = 10, seed: int = 5) -> pd.DataFrame:
    """Synthetic closes on REAL panier column names (run_tsmom_single_lookback
    filters columns against ALL_SYMBOLS, so synthetic names would be dropped)."""
    rng = np.random.default_rng(seed)
    idx = pd.bdate_range("2015-01-01", periods=n_rows)
    rets = rng.standard_normal((n_rows, n_syms)) * 0.01
    cols = _SYMBOLS[:n_syms]
    return pd.DataFrame(100 * np.exp(np.cumsum(rets, axis=0)), index=idx, columns=cols)


class TestDrawSeedView:
    def test_subset_share_and_offset_range(self) -> None:
        n = len(_SYMBOLS)
        expected_sub = max(2, int(round(SUBBASKET_SHARE * n)))
        for seed in range(20):
            subset, offset = draw_seed_view(np.random.default_rng(seed), _SYMBOLS)
            assert len(subset) == expected_sub  # 21 of 26
            assert set(subset) <= set(_SYMBOLS)
            assert len(subset) == len(set(subset))  # without replacement
            assert 0 <= offset <= MAX_ORIGIN_OFFSET

    def test_small_symbol_list_is_not_emptied(self) -> None:
        subset, _ = draw_seed_view(np.random.default_rng(0), _SYMBOLS[:3])
        # round(0.8 * 3) = 2, floored at max(2, ...) and capped by len
        assert len(subset) == 2
        assert set(subset) <= set(_SYMBOLS[:3])

    def test_same_seed_same_view_for_model_and_baseline(self) -> None:
        """Pairing contract: identically-seeded draws give the identical view,
        so the model and its B&H baseline are compared on the same slice."""
        for seed in (0, 1, 7, 42):
            v_model = draw_seed_view(np.random.default_rng(seed), _SYMBOLS)
            v_bh = draw_seed_view(np.random.default_rng(seed), _SYMBOLS)
            assert v_model == v_bh

    def test_different_seeds_draw_different_views(self) -> None:
        views = {(tuple(sub), off)
                 for sub, off in (draw_seed_view(np.random.default_rng(s), _SYMBOLS)
                                  for s in range(8))}
        assert len(views) > 1


class TestLiveSeeds:
    def test_cross_seed_dispersion_is_nonzero(self) -> None:
        """The #14470 defect 1, written as a test: before the fix, the rng
        was never consumed and the 4 seeds produced EXACTLY the same Sharpe
        (std = 0.0000000000). With live views, dispersion must be > 0."""
        closes = _synthetic_closes()
        res = run_tsmom_single_lookback(closes, lookback=63, seeds=[0, 1, 7, 42],
                                        n_splits=4, gap=10)
        sharpes = [s["net_sharpe"] for s in res["seeds"]]
        assert len(sharpes) == 4
        assert float(np.std(sharpes)) > 0.0
        # the per-seed views actually differ and are recorded
        views = [(s["view_n_symbols"], s["view_offset"]) for s in res["seeds"]]
        assert len(set(views)) > 1

    def test_baseline_uses_the_same_views_as_the_model(self) -> None:
        closes = _synthetic_closes()
        seeds = [0, 1, 7, 42]
        res = run_tsmom_single_lookback(closes, lookback=63, seeds=seeds,
                                        n_splits=4, gap=10)
        bh = run_buyhold_baseline(closes, seeds=seeds, n_splits=4, gap=10)
        model_views = {(s["seed"], s["view_n_symbols"], s["view_offset"])
                       for s in res["seeds"]}
        bh_views = {(s["seed"], s["view_n_symbols"], s["view_offset"])
                    for s in bh["seeds"]}
        assert model_views == bh_views  # paired comparison
        assert len(bh_views) > 1  # baseline is no longer seed-blind either


class TestTurnoverCosts:
    def test_l1_convention_diagnostic_column_present(self) -> None:
        closes = _synthetic_closes()
        res = run_tsmom_single_lookback(closes, lookback=63, seeds=[0, 1],
                                        n_splits=3, gap=10)
        for s in res["seeds"]:
            assert "net_sharpe_l1_convention" in s
            assert "avg_daily_turnover" in s
            # turnover-proportional costs are strictly lower than the legacy
            # full round-trip per moving line (which overstates rebalancing)
            assert s["net_sharpe"] >= s["net_sharpe_l1_convention"] - 1e-9

    def test_turnover_metric_is_within_notional_bounds(self) -> None:
        closes = _synthetic_closes()
        res = run_tsmom_single_lookback(closes, lookback=63, seeds=[0],
                                        n_splits=3, gap=10)
        s = res["seeds"][0]
        # position weights are vol-scaled in [0.1, 3.0] per asset; daily total
        # notionnel moved stays bounded by n_assets * max_scale * 2
        assert 0.0 <= s["avg_daily_turnover"] <= s["view_n_symbols"] * 3.0 * 2 + 1e-9
