"""Unit tests for m12_har_rv_j — HAR-RV-J jump decomposition (Andersen et al. 2007).

These cover the *jump-specific* logic that distinguishes HAR-RV-J from the plain
HAR baseline (the latter is already covered by test_har_model.py):

- ``daily_jump_component``: J_t = max(RV_t - mu * BPV_t, 0) (Huang-Tauchen)
- ``har_rv_j_lag_features``: 6 regressors (log RV d/w/m + raw jump d/w/m)
- ``HARRVJModel``: OLS fit + iterated h-step forecast
- ``walk_forward_har_rv_j``: expanding-window walk-forward evaluation
- ``_sharpe_ann``: annualized Sharpe (sqrt(365), ddof=1)
- cluster contract (M16 seven-asset transposition): ``_canonical_dm_verdict``,
  ``aggregate_unit_rows`` / ``cluster_verdict`` (coin-level strict-majority
  collapse + exact one-sided binomial) and ``validate_sweep_contract``
  (fail-closed on missing/duplicate couples, seed controls, fold proofs and
  finite key metrics)
- ``evaluate_one_combo`` fail-closed paths (``UnitEvaluationError``)
- determinism attestation (bit-identical OLS refits, no stochastic input)

All fixtures are deterministic synthetic series — no network, no GPU, no data
files. The whole module runs in well under a second on CPU.
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

from m12_har_rv_j import (  # noqa: E402
    CLUSTER_ASSETS,
    COINS,
    HORIZONS,
    MU_HUANG_TAUCHEN,
    HARRVJModel,
    UnitEvaluationError,
    _canonical_dm_verdict,
    _csv_int_list,
    _csv_list,
    _fit_har_rv_j_with_train_calibration,
    _sharpe_ann,
    aggregate_unit_rows,
    cluster_verdict,
    daily_jump_component,
    evaluate_one_combo,
    har_rv_j_lag_features,
    validate_sweep_contract,
    walk_forward_har_rv_j,
)
import m12_har_rv_j  # noqa: E402  (module handle for monkeypatch targets)
from realized_variance import (  # noqa: E402
    daily_bipower_variation,
    daily_realized_variance,
    realized_variance_to_log,
)


# ── Fixtures ────────────────────────────────────────────────────────────────

def _hourly_log_returns(n_days: int = 120, hours_per_day: int = 8, seed: int = 0) -> pd.Series:
    """Deterministic synthetic hourly log-returns with a DatetimeIndex.

    ~8 obs/day keeps per-day RV/BPV well-defined (>= min_obs_per_day=6 default).
    """
    rng = np.random.default_rng(seed)
    n = n_days * hours_per_day
    idx = pd.date_range("2020-01-01", periods=n, freq="3h", name="timestamp")
    return pd.Series(rng.standard_normal(n) * 0.01, index=idx, name="r")


def _rv_series(n: int, base: float = 1e-4, seed: int = 1) -> pd.Series:
    """A positive daily-RV series (date index) for feature/model tests."""
    rng = np.random.default_rng(seed)
    idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
    return pd.Series(np.abs(rng.standard_normal(n)) * base + 1e-6, index=idx, name="RV")


@pytest.fixture
def hourly() -> pd.Series:
    return _hourly_log_returns()


@pytest.fixture
def rv(hourly: pd.Series) -> pd.Series:
    return daily_realized_variance(hourly)


@pytest.fixture
def jumps(hourly: pd.Series) -> pd.Series:
    return daily_jump_component(hourly)


# ── daily_jump_component ────────────────────────────────────────────────────

class TestDailyJumpComponent:
    def test_jumps_non_negative(self, jumps: pd.Series) -> None:
        # J_t = max(RV - mu*BPV, 0) >= 0 by construction.
        assert (jumps.dropna() >= 0).all()

    def test_formula_holds_elementwise(self, hourly: pd.Series) -> None:
        rv = daily_realized_variance(hourly)
        bpv = daily_bipower_variation(hourly)
        aligned = pd.concat([rv.rename("rv"), bpv.rename("bpv")], axis=1).dropna()
        expected = np.maximum(aligned["rv"] - MU_HUANG_TAUCHEN * aligned["bpv"], 0.0)
        got = daily_jump_component(hourly).reindex(aligned.index).fillna(0.0)
        np.testing.assert_allclose(got.values, expected.values, rtol=1e-9, atol=1e-15)

    def test_mu_zero_recovers_rv(self, hourly: pd.Series) -> None:
        # With mu=0, J_t = max(RV, 0) = RV (RV >= 0 always).
        rv = daily_realized_variance(hourly)
        j = daily_jump_component(hourly, mu=0.0)
        common = rv.index.intersection(j.index)
        np.testing.assert_allclose(j.loc[common].values, rv.loc[common].values, rtol=1e-9)

    def test_higher_mu_shrinks_jumps(self, hourly: pd.Series) -> None:
        # Larger mu -> RV - mu*BPV smaller -> fewer/smaller jumps.
        j_low = daily_jump_component(hourly, mu=0.3)
        j_high = daily_jump_component(hourly, mu=2.0)
        common = j_low.index.intersection(j_high.index)
        assert j_high.loc[common].sum() <= j_low.loc[common].sum() + 1e-15

    def test_index_is_normalized_dates(self, jumps: pd.Series) -> None:
        assert jumps.index.name == "date"
        assert jumps.index.is_normalized  # daily, no intraday duplicates


# ── har_rv_j_lag_features ───────────────────────────────────────────────────

class TestHarRvJLagFeatures:
    def test_six_regressors_present(self, rv: pd.Series, jumps: pd.Series) -> None:
        feats = har_rv_j_lag_features(rv, jumps)
        assert set(feats.columns) == {"rv_d", "rv_w", "rv_m", "j_d", "j_w", "j_m"}

    def test_jump_lag_is_shift1_no_lookahead(self, rv: pd.Series, jumps: pd.Series) -> None:
        # j_d = jumps.shift(1): today's feature uses yesterday's jump (no leak).
        feats = har_rv_j_lag_features(rv, jumps)
        expected = jumps.shift(1)
        common = feats.index.intersection(expected.index)
        np.testing.assert_allclose(
            feats["j_d"].loc[common].values,
            expected.loc[common].values,
            rtol=1e-9, atol=1e-15,
            err_msg="j_d must equal jumps.shift(1) (no look-ahead)",
        )

    def test_jumps_on_raw_scale_can_be_zero(self) -> None:
        # Jumps are NOT logged (can be exactly zero); a zero-jump series must
        # stay exactly zero in every jump lag feature.
        n = 40
        rv = _rv_series(n)
        zeros = pd.Series(np.zeros(n), index=rv.index)
        feats = har_rv_j_lag_features(rv, zeros)
        jump_cols = feats[["j_d", "j_w", "j_m"]].dropna()
        assert (jump_cols == 0.0).all().all()

    def test_rv_features_on_log_scale(self, rv: pd.Series, jumps: pd.Series) -> None:
        # rv_d/w/m are log-scale (realized_variance_to_log applied to raw lags).
        feats = har_rv_j_lag_features(rv, jumps)
        log_rv_d = realized_variance_to_log(rv).shift(1)
        common = feats.index.intersection(log_rv_d.index)
        np.testing.assert_allclose(
            feats["rv_d"].loc[common].values, log_rv_d.loc[common].values, rtol=1e-9
        )

    def test_j_w_is_rolling5_mean(self, rv: pd.Series, jumps: pd.Series) -> None:
        feats = har_rv_j_lag_features(rv, jumps)
        expected = jumps.shift(1).rolling(window=5, min_periods=5).mean()
        common = feats.index.intersection(expected.index)
        np.testing.assert_allclose(
            feats["j_w"].loc[common].values,
            expected.loc[common].values,
            rtol=1e-9, atol=1e-15,
        )


# ── HARRVJModel ─────────────────────────────────────────────────────────────

class TestHARRVJModel:
    def test_fit_requires_min_30_obs(self) -> None:
        # Fewer than 30 aligned rows after dropna (rv_m needs 22 lags) -> ValueError.
        n = 25
        rv = _rv_series(n)
        jumps = pd.Series(np.zeros(n), index=rv.index)
        with pytest.raises(ValueError):
            HARRVJModel().fit(rv, jumps)

    def test_predict_horizon_must_be_positive(self, rv: pd.Series, jumps: pd.Series) -> None:
        model = HARRVJModel().fit(rv, jumps)
        with pytest.raises(ValueError):
            model.predict_h_step(rv.iloc[-30:], jumps.iloc[-30:], horizon=0)

    def test_predict_returns_finite_float(self, rv: pd.Series, jumps: pd.Series) -> None:
        model = HARRVJModel().fit(rv, jumps)
        out = model.predict_h_step(rv.iloc[-30:], jumps.iloc[-30:], horizon=3)
        assert isinstance(out, float)
        assert np.isfinite(out)

    def test_fit_coef_shape(self, rv: pd.Series, jumps: pd.Series) -> None:
        model = HARRVJModel().fit(rv, jumps)
        # intercept + 6 features = 7 coefficients.
        assert model.coef_.shape == (7,)
        assert model.n_train_ >= 30

    def test_predict_constant_rv_recovers_log(self) -> None:
        # rv = constant C, jumps = 0 -> log(rv[t]) = log(C) for all t, so every
        # feature collapses (rv_d=rv_w=rv_m=log(C), jumps=0) and the iterated
        # h-step forecast must return ~ log(C). Exercises fit + predict_h_step.
        n = 60
        c = 1e-4
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        rv_const = pd.Series(np.full(n, c), index=idx)
        jumps_const = pd.Series(np.zeros(n), index=idx)
        model = HARRVJModel().fit(rv_const, jumps_const)
        log_c = float(np.log(c))
        pred = model.predict_h_step(rv_const, jumps_const, horizon=5)
        assert abs(pred - log_c) < 1e-6

    def test_lstsq_design_matrix_recovery(self) -> None:
        # The model fits log(RV) = X @ beta via np.linalg.lstsq on a 7-column
        # design matrix (intercept + 6 features). Verify that construction +
        # solver recover known coefficients on a noise-free linear DGP. This
        # pins the design-matrix column order used by HARRVJModel.fit.
        rng = np.random.default_rng(7)
        n = 400
        rv = pd.Series(np.abs(rng.standard_normal(n)) * 0.01 + 1e-5,
                       index=pd.date_range("2020-01-01", periods=n, freq="D"))
        jumps = pd.Series(np.abs(rng.standard_normal(n)) * 0.005, index=rv.index)
        feats = har_rv_j_lag_features(rv, jumps).dropna()
        true_beta = np.array([0.1, 0.5, 0.2, 0.1, 0.3, -0.1, 0.05])  # b0,d,w,m,dj,wj,mj
        x = np.column_stack([
            np.ones(len(feats)),
            feats["rv_d"], feats["rv_w"], feats["rv_m"],
            feats["j_d"], feats["j_w"], feats["j_m"],
        ])
        y = x @ true_beta
        coef, *_ = np.linalg.lstsq(x, y, rcond=None)
        np.testing.assert_allclose(coef, true_beta, atol=1e-8)


# ── walk_forward_har_rv_j ───────────────────────────────────────────────────

class TestWalkForwardHarRvJ:
    def test_raises_on_short_series(self) -> None:
        n = 150  # < 200 -> ValueError
        rv = _rv_series(n)
        jumps = pd.Series(np.zeros(n), index=rv.index)
        with pytest.raises(ValueError):
            walk_forward_har_rv_j(rv, jumps, n_splits=5)

    def test_returns_expected_structure(self) -> None:
        n = 420  # fold_size = 420//6 = 70 >= 60 (min train) for all 5 folds
        rv = _rv_series(n, seed=2)
        rng = np.random.default_rng(3)
        jumps = pd.Series(np.abs(rng.standard_normal(n)) * 1e-5, index=rv.index)
        out = walk_forward_har_rv_j(rv, jumps, horizon=1, n_splits=5)
        assert out["horizon"] == 1
        assert out["n_splits"] == 5
        for key in ("n_total_preds", "aggregate_mse_logrv", "fold_results",
                    "forecasts", "targets"):
            assert key in out, f"missing key {key}"
        assert out["aggregate_mse_logrv"] >= 0.0
        fc, tg = out["forecasts"], out["targets"]
        assert isinstance(fc, pd.Series)
        assert isinstance(tg, pd.Series)
        assert len(fc) == len(tg)
        assert out["n_total_preds"] == len(fc)
        # forecast / target indices must be perfectly aligned.
        np.testing.assert_array_equal(fc.index.values, tg.index.values)
        # every fold produced a finite MSE (fold_results populated).
        assert len(out["fold_results"]) >= 1
        for fr in out["fold_results"]:
            assert np.isfinite(fr["mse_logrv"])

    def test_higher_horizon_reduces_per_fold_test_count(self) -> None:
        # horizon trims the test window (range(... test_end - horizon)); a
        # larger horizon yields fewer predictions per fold.
        n = 420
        rv = _rv_series(n, seed=5)
        rng = np.random.default_rng(6)
        jumps = pd.Series(np.abs(rng.standard_normal(n)) * 1e-5, index=rv.index)
        out_h1 = walk_forward_har_rv_j(rv, jumps, horizon=1, n_splits=5)
        out_h5 = walk_forward_har_rv_j(rv, jumps, horizon=5, n_splits=5)
        assert out_h5["n_total_preds"] < out_h1["n_total_preds"]

    def test_calibration_is_train_tail_only(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        n = 160
        rv = _rv_series(n, seed=8)
        jumps = pd.Series(np.zeros(n), index=rv.index)

        def predict_constant(
            self: HARRVJModel,
            rv_history: pd.Series,
            jumps_history: pd.Series,
            horizon: int,
        ) -> float:
            del self, jumps_history, horizon
            return float(np.log(rv_history.iloc[-1])) + 0.25

        monkeypatch.setattr(HARRVJModel, "predict_h_step", predict_constant)
        _, bias = _fit_har_rv_j_with_train_calibration(
            rv, jumps, horizon=1, calibration_size=40
        )
        expected = []
        log_rv = np.log(rv)
        for i in range(120, 159):
            expected.append(float(log_rv.iloc[i - 1] + 0.25 - log_rv.iloc[i]))
        assert bias == pytest.approx(float(np.mean(expected)))

    def test_calibrated_walk_forward_records_biases(self) -> None:
        n = 420
        rv = _rv_series(n, seed=9)
        rng = np.random.default_rng(10)
        jumps = pd.Series(np.abs(rng.normal(size=n)) * 1e-5, index=rv.index)
        out = walk_forward_har_rv_j(
            rv,
            jumps,
            horizon=1,
            n_splits=5,
            calibrate_bias=True,
            calibration_size=40,
        )
        assert out["calibrate_bias"] is True
        assert out["calibration_size"] == 40
        assert len(out["initial_calibration_bias_by_fold"]) == 5
        assert np.isfinite(out["initial_calibration_bias_by_fold"]).all()


# ── helpers ─────────────────────────────────────────────────────────────────

class TestHelpers:
    def test_sharpe_ann_too_short_is_nan(self) -> None:
        assert np.isnan(_sharpe_ann(np.array([0.1] * 9)))  # < 10 -> nan

    def test_sharpe_ann_known_value(self) -> None:
        rng = np.random.default_rng(0)
        r = rng.standard_normal(100) * 0.01
        expected = (r.mean() / r.std(ddof=1)) * np.sqrt(365)
        np.testing.assert_allclose(_sharpe_ann(r), expected, rtol=1e-12)

    def test_sharpe_ann_zero_sigma_is_nan(self) -> None:
        # constant returns -> sigma=0 -> nan (no division by zero).
        assert np.isnan(_sharpe_ann(np.array([0.001] * 100)))

    def test_csv_parsers(self) -> None:
        assert _csv_list("a, b ,c") == ["a", "b", "c"]
        assert _csv_int_list("1, 7, 42") == [1, 7, 42]
        assert _csv_list("") == []
        assert _csv_int_list("") == []


# ── Cluster contract (M16 seven-asset transposition) ─────────────────────────

CLUSTER = [
    "BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD",
]
SEED_LABELS = [0, 7, 42, 99]
FIVE_FOLDS = [
    {"fold": i, "n_test": 30, "mse_logrv": 0.5, "mean_resid": -0.02}
    for i in range(5)
]


def _combo_row(coin: str, horizon: int, verdict: str = "INCONCLUSIVE", **overrides):
    """One synthetic sweep row carrying every field aggregate/validate read."""
    row = {
        "coin": coin,
        "horizon": horizon,
        "seed": 0,
        "n_folds_har": 5,
        "n_folds_har_debiased": 5,
        "n_folds_hrj": 5,
        "har_fold_summaries": [dict(f) for f in FIVE_FOLDS],
        "har_debiased_fold_summaries": [dict(f) for f in FIVE_FOLDS],
        "hrj_fold_summaries": [dict(f) for f in FIVE_FOLDS],
        "data_window_start": "2020-01-01 00:00:00",
        "data_window_end": "2021-12-01 00:00:00",
        "n_hourly_obs": 17_000,
        "n_rv_days": 700,
        "verdict": verdict,
        "dm_mse_pvalue": 0.42,
        "dm_mse_stat": -0.8,
        "dm_mse_mean_loss_diff": -0.01,
        "delta_sharpe_hrj_vs_har_debiased": 0.05,
        "mse_har": 1.2,
        "mse_har_debiased": 1.1,
        "mse_hrj": 1.0,
        "mse_reduction_pct_vs_debiased_har": 9.0,
        "har_bias_oos": 0.01,
        "har_debiased_bias_oos": 0.005,
        "hrj_debiased_bias_oos": 0.004,
    }
    row.update(overrides)
    return row


def _sweep(verdict_fn) -> list[dict]:
    """21 synthetic combo rows: verdict_fn(coin, horizon) -> verdict."""
    return [
        _combo_row(coin, horizon, verdict_fn(coin, horizon))
        for coin in CLUSTER
        for horizon in (1, 5, 10)
    ]


def _aggregate(combos: list[dict]) -> list[dict]:
    return aggregate_unit_rows(combos, SEED_LABELS)


class TestCanonicalDmVerdict:
    def test_mapping(self) -> None:
        assert _canonical_dm_verdict("BEATS baseline") == "BEATS"
        assert _canonical_dm_verdict("BEATEN BY baseline") == "NO BEATS"
        assert _canonical_dm_verdict("INCONCLUSIVE") == "INCONCLUSIVE"

    def test_unknown_string_is_inconclusive(self) -> None:
        assert _canonical_dm_verdict("something else") == "INCONCLUSIVE"


class TestClusterVerdict:
    def test_all_beats_seven_coins(self) -> None:
        combos = _sweep(lambda coin, h: "BEATS")
        cluster = cluster_verdict(_aggregate(combos))
        assert cluster["verdict"] == "BEATS"
        assert cluster["primary_coin_level"]["n_effective"] == 7
        assert cluster["primary_coin_level"]["n_beats"] == 7
        # Exact binomial: p(7/7, one-sided) = 0.5**7.
        from scipy.stats import binomtest
        expected_p = float(binomtest(7, 7, 0.5, alternative="greater").pvalue)
        assert cluster["primary_coin_level"]["p_value"] == pytest.approx(
            expected_p
        )
        assert cluster["primary_coin_level"]["p_value"] == pytest.approx(0.5 ** 7)

    def test_strict_majority_beats_overrides_one_no_beats_horizon(self) -> None:
        # M16 collapse rule: 2 BEATS out of 3 horizons = strict majority, so
        # the coin is BEATS even though the third horizon is NO BEATS.
        combos = _sweep(lambda coin, h: "BEATS" if h != 10 else "NO BEATS")
        cluster = cluster_verdict(_aggregate(combos))
        assert cluster["verdict"] == "BEATS"
        for coin_row in cluster["primary_coin_level"]["coin_verdicts"]:
            assert coin_row["verdict"] == "BEATS"
            assert coin_row["n_beats"] == 2
            assert coin_row["n_no_beats"] == 1

    def test_any_no_beats_without_strict_majority_is_no_beats(self) -> None:
        # 1 BEATS + 1 NO BEATS + 1 INCONCLUSIVE per coin: no strict majority,
        # at least one NO BEATS -> coin NO BEATS -> 0/7 -> cluster NO BEATS.
        def verdict(coin: str, h: int) -> str:
            return {1: "BEATS", 5: "NO BEATS", 10: "INCONCLUSIVE"}[h]

        cluster = cluster_verdict(_aggregate(_sweep(verdict)))
        assert cluster["primary_coin_level"]["n_beats"] == 0
        assert cluster["primary_coin_level"]["p_value"] == pytest.approx(1.0)
        assert cluster["verdict"] == "NO BEATS"

    def test_four_of_seven_is_inconclusive_with_exact_p(self) -> None:
        # 4 coins BEATS (2 BEATS + 1 INCONCLUSIVE), 3 coins all INCONCLUSIVE.
        # p = P(X>=4 | Binom(7, 0.5)) = 64/128 = 0.5 exactly -> not < alpha,
        # and 4 > 3.5 -> INCONCLUSIVE (majority without significance).
        beaters = set(CLUSTER[:4])

        def verdict(coin: str, h: int) -> str:
            return "BEATS" if coin in beaters and h != 10 else "INCONCLUSIVE"

        cluster = cluster_verdict(_aggregate(_sweep(verdict)))
        assert cluster["primary_coin_level"]["n_beats"] == 4
        assert cluster["primary_coin_level"]["p_value"] == pytest.approx(0.5)
        assert cluster["verdict"] == "INCONCLUSIVE"

    def test_five_of_seven_is_inconclusive_exact_p(self) -> None:
        # Acceptance case: 5 coins BEATS is NOT enough. p = P(X>=5 | Binom(7,
        # 0.5)) = 29/128 = 0.2265625 exactly -> not < 0.05, and 5 > 3.5 ->
        # INCONCLUSIVE (majority without significance).
        beaters = set(CLUSTER[:5])

        def verdict(coin: str, h: int) -> str:
            return "BEATS" if coin in beaters and h != 10 else "INCONCLUSIVE"

        cluster = cluster_verdict(_aggregate(_sweep(verdict)))
        assert cluster["primary_coin_level"]["n_beats"] == 5
        assert cluster["primary_coin_level"]["p_value"] == pytest.approx(
            29 / 128
        )
        assert cluster["primary_coin_level"]["p_value"] == pytest.approx(
            0.2265625
        )
        assert cluster["verdict"] == "INCONCLUSIVE"

    def test_six_of_seven_is_inconclusive_exact_p(self) -> None:
        # p = P(X>=6 | Binom(7, 0.5)) = 8/128 = 0.0625 -> still not < 0.05.
        beaters = set(CLUSTER[:6])

        def verdict(coin: str, h: int) -> str:
            return "BEATS" if coin in beaters and h != 10 else "INCONCLUSIVE"

        cluster = cluster_verdict(_aggregate(_sweep(verdict)))
        assert cluster["primary_coin_level"]["n_beats"] == 6
        assert cluster["primary_coin_level"]["p_value"] == pytest.approx(0.0625)
        assert cluster["verdict"] == "INCONCLUSIVE"

    def test_cluster_invariant_to_seed_labels(self) -> None:
        # Direct invariance proof: replacing the four requested seed labels
        # with ANY other labels leaves the cluster result bit-identical —
        # the labels are controls, never observations. There are always 21
        # config rows, never 84 statistical rows.
        combos = _sweep(lambda coin, h: "BEATS" if h != 10 else "NO BEATS")
        cluster_a = cluster_verdict(aggregate_unit_rows(combos, [0, 7, 42, 99]))
        cluster_b = cluster_verdict(aggregate_unit_rows(combos, [1, 2, 3, 4]))
        assert cluster_a == cluster_b
        assert (
            cluster_a["primary_coin_level"]["p_value"]
            == cluster_b["primary_coin_level"]["p_value"]
        )
        rows_a = aggregate_unit_rows(combos, [0, 7, 42, 99])
        rows_b = aggregate_unit_rows(combos, [1, 2, 3, 4])
        assert len(rows_a) == len(rows_b) == 21
        assert all(r["n_seeds_effective"] == 1 for r in rows_a + rows_b)

    def test_all_inconclusive(self) -> None:
        cluster = cluster_verdict(_aggregate(_sweep(lambda coin, h: "INCONCLUSIVE")))
        assert cluster["verdict"] == "NO BEATS"

    def test_config_level_is_descriptive_only(self) -> None:
        combos = _sweep(lambda coin, h: "BEATS")
        cluster = cluster_verdict(_aggregate(combos))
        assert cluster["config_level"]["role"] == "descriptive_only"
        assert cluster["config_level"]["n_effective"] == 21
        assert "dépendants" in cluster["config_level"]["dependence_caveat"]

    def test_seed_control_not_effective_one_raises(self) -> None:
        aggregated = _aggregate(_sweep(lambda coin, h: "BEATS"))
        aggregated[3]["n_seeds_effective"] = 2
        with pytest.raises(ValueError, match="deterministic seed controls"):
            cluster_verdict(aggregated)

    def test_seed_control_not_stable_raises(self) -> None:
        aggregated = _aggregate(_sweep(lambda coin, h: "BEATS"))
        aggregated[3]["seed_stable"] = False
        with pytest.raises(ValueError, match="deterministic seed controls"):
            cluster_verdict(aggregated)

    def test_empty_raises(self) -> None:
        with pytest.raises(ValueError, match="at least one configuration"):
            cluster_verdict([])


class TestValidateSweepContract:
    def _validate(self, combos: list[dict]) -> None:
        aggregated = _aggregate(combos)
        validate_sweep_contract(
            rows=aggregated,
            aggregated=aggregated,
            requested=CLUSTER,
            horizons=[1, 5, 10],
            seeds=SEED_LABELS,
            n_splits=5,
        )

    def test_complete_sweep_passes(self) -> None:
        self._validate(_sweep(lambda coin, h: "INCONCLUSIVE"))

    def test_missing_config_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos.pop()  # drop DOT-USD/h=10 -> 20 rows
        with pytest.raises(ValueError, match="incomplete sweep configurations"):
            self._validate(combos)

    def test_duplicate_row_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos.append(dict(combos[0]))  # 22 rows, same 21 configs
        with pytest.raises(ValueError, match="duplicate sweep rows"):
            self._validate(combos)

    def test_fold_count_mismatch_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos[0]["n_folds_hrj"] = 4
        with pytest.raises(ValueError, match="did not produce 5 folds"):
            self._validate(combos)

    def test_fold_summary_count_mismatch_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos[0]["hrj_fold_summaries"] = combos[0]["hrj_fold_summaries"][:4]
        with pytest.raises(ValueError, match="fold summaries, expected 5"):
            self._validate(combos)

    def test_fold_summary_zero_test_count_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos[0]["har_debiased_fold_summaries"][2]["n_test"] = 0
        with pytest.raises(ValueError, match="n_test=0"):
            self._validate(combos)

    def test_fold_summary_non_finite_mse_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos[0]["hrj_fold_summaries"][1]["mse_logrv"] = float("nan")
        with pytest.raises(ValueError, match="non-finite MSE"):
            self._validate(combos)

    def test_fold_summary_non_finite_mean_resid_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos[0]["har_fold_summaries"][3]["mean_resid"] = float("nan")
        with pytest.raises(ValueError, match="non-finite mean_resid"):
            self._validate(combos)

    def test_raw_har_summary_count_mismatch_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos[0]["har_fold_summaries"] = combos[0]["har_fold_summaries"][:3]
        with pytest.raises(ValueError, match="fold summaries, expected 5"):
            self._validate(combos)

    def test_non_finite_key_metric_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        combos[5]["dm_mse_pvalue"] = float("nan")
        with pytest.raises(ValueError, match="non-finite key"):
            self._validate(combos)

    def test_seed_label_mismatch_raises(self) -> None:
        combos = _sweep(lambda coin, h: "INCONCLUSIVE")
        aggregated = _aggregate(combos)
        aggregated[0]["seed_values_requested"] = [0, 7]
        with pytest.raises(ValueError, match="seed control attestation broken"):
            validate_sweep_contract(
                rows=aggregated,
                aggregated=aggregated,
                requested=CLUSTER,
                horizons=[1, 5, 10],
                seeds=SEED_LABELS,
                n_splits=5,
            )


class TestUnitFailClosed:
    def test_short_hourly_series_raises_with_reason(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        short = pd.Series(
            np.zeros(500),
            index=pd.date_range("2020-01-01", periods=500, freq="h"),
        )
        monkeypatch.setattr(m12_har_rv_j, "_load_one_coin", lambda coin: short)
        with pytest.raises(UnitEvaluationError, match="too short"):
            evaluate_one_combo("BTC-USD", 1, 0)

    def test_loader_failure_wrapped_as_unit_error(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        def broken_loader(coin: str) -> pd.Series:
            raise FileNotFoundError("missing.csv")

        monkeypatch.setattr(m12_har_rv_j, "_load_one_coin", broken_loader)
        with pytest.raises(UnitEvaluationError, match="data loader failed"):
            evaluate_one_combo("SOL-USD", 5, 0)

    def test_walk_forward_failure_wrapped_with_cause(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        # 320 calendar days x 8 obs/day: passes the length gates, then the
        # (monkeypatched) HAR walk-forward raises -> wrapped, never skipped.
        hourly = _hourly_log_returns(n_days=320, hours_per_day=24, seed=3)
        monkeypatch.setattr(m12_har_rv_j, "_load_one_coin", lambda coin: hourly)

        def boom(*args, **kwargs):
            raise ValueError("boom")

        monkeypatch.setattr(m12_har_rv_j, "walk_forward_har", boom)
        with pytest.raises(UnitEvaluationError) as excinfo:
            evaluate_one_combo("ETH-USD", 1, 0)
        assert "HAR walk-forward failed" in str(excinfo.value)
        assert "ValueError: boom" in str(excinfo.value)


class TestClusterDefaults:
    def test_cluster_assets_are_seven_in_m16_order(self) -> None:
        assert list(CLUSTER_ASSETS) == CLUSTER
        assert COINS == list(CLUSTER_ASSETS)
        assert len(COINS) == 7
        assert HORIZONS == [1, 5, 10]

    def test_calibration_size_constant_exists(self) -> None:
        assert m12_har_rv_j.CALIBRATION_SIZE == 60


class TestDataManifest:
    def test_manifest_loaded_and_missing(self) -> None:
        from m12_har_rv_j import _build_data_manifest

        loaded = [c for c in CLUSTER if c != "DOT-USD"]
        combos = [
            _combo_row(coin, h, "INCONCLUSIVE")
            for coin in loaded
            for h in (1, 5, 10)
        ]
        failures = [
            {"coin": "DOT-USD", "horizon": h, "reason": "loader failed"}
            for h in (1, 5, 10)
        ]
        manifest = _build_data_manifest(
            CLUSTER, [1, 5, 10], combos, failures, None
        )
        assert manifest["coins_requested"] == CLUSTER
        assert manifest["coins_loaded"] == loaded
        assert manifest["coins_missing_or_failed"] == ["DOT-USD"]
        assert manifest["oos_strict_year"] is None
        btc = manifest["per_coin"]["BTC-USD"]
        assert btc["status"] == "loaded"
        assert btc["n_units_ok"] == 3
        assert btc["n_units_failed"] == 0
        assert btc["n_rv_days"] == 700
        assert btc["data_window_start"] == "2020-01-01 00:00:00"
        dot = manifest["per_coin"]["DOT-USD"]
        assert dot["status"] == "missing_or_failed"
        assert dot["n_units_ok"] == 0
        assert dot["n_units_failed"] == 3
        assert dot["n_rv_days"] is None


class TestDeterminismAttestation:
    """Pins the n_seeds_effective=1 claim: the OLS path has no stochastic
    input, so identical inputs produce BIT-identical fits and forecasts."""

    def _rv_jumps(self, n: int = 420) -> tuple[pd.Series, pd.Series]:
        rv = _rv_series(n, seed=21)
        rng = np.random.default_rng(22)
        jumps = pd.Series(np.abs(rng.normal(size=n)) * 1e-5, index=rv.index)
        return rv, jumps

    def test_refit_bit_identical_coefficients(self) -> None:
        rv, jumps = self._rv_jumps()
        model_a = HARRVJModel().fit(rv, jumps)
        model_b = HARRVJModel().fit(rv, jumps)
        np.testing.assert_array_equal(model_a.coef_, model_b.coef_)

    def test_walk_forward_bit_identical_forecasts(self) -> None:
        rv, jumps = self._rv_jumps()
        out_a = walk_forward_har_rv_j(
            rv, jumps, horizon=1, n_splits=5, calibrate_bias=True,
            calibration_size=60,
        )
        out_b = walk_forward_har_rv_j(
            rv, jumps, horizon=1, n_splits=5, calibrate_bias=True,
            calibration_size=60,
        )
        np.testing.assert_array_equal(
            out_a["forecasts"].values, out_b["forecasts"].values
        )
        np.testing.assert_array_equal(
            out_a["targets"].values, out_b["targets"].values
        )
        assert out_a["fold_results"] == out_b["fold_results"]

    def test_aggregate_carries_determinism_attestation(self) -> None:
        aggregated = _aggregate(_sweep(lambda coin, h: "INCONCLUSIVE"))
        assert all(row["n_seeds_effective"] == 1 for row in aggregated)
        assert all(row["seed_stable"] is True for row in aggregated)
        assert all(row["seed_replication"] == "deterministic-ols" for row in aggregated)
        assert all(
            row["seed_values_requested"] == SEED_LABELS for row in aggregated
        )
