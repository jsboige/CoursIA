# region imports
from AlgorithmImports import *
import numpy as np
from collections import deque

# Pure-numpy breadth multiplier (REPAIR-8 c.1115). Imported here so the
# CarverThirteen class and the unit tests share the same canonical formula
# without forcing the tests to pull in AlgorithmImports (which requires
# QC Cloud). See breadth_multiplier.py for the rationale.
from breadth_multiplier import breadth_multiplier as _breadth_multiplier_pure
# endregion


# Carver #13 (Carver 2023, *Advanced Futures Trading Strategies*, Harriman House,
# ISBN 9780857199683) — six EWMAC horizons + volatility-regime multiplier
# [0.5, 2] + breadth multiplier + cap +/-20.
# Reference article: QuantConnect #15989 (Derek Melchin, 2026-01-02). The article
# reports Sharpe 0.944 vs 0.749 benchmark over a 3-year favourable window
# (2020-07 -> 2023-07); we deliberately do NOT pre-commit to that result. We
# reproduce the strategy with identical parameters and let QC Cloud produce a
# verdict on a >= 2016-2026 window.
#
# Differences vs the v3.1 ETF baseline (main.py):
# - True continuous futures (19 instruments) instead of 6 ETF proxies.
# - Six EWMAC horizons (Carver pairs: 8/32, 16/64, 32/128, 64/256, 16/48, 32/96)
#   with per-horizon scalar normalisation (c.1063), not a single Donchian 20/10.
# - Carry factor: DISABLED on this port (c.1107 REPAIR ADJOINT, see
#   `_carry_forecast` docstring + the carry stub in `_rebalance`). The
#   blend is trend-only (mean of six EWMAC forecasts, capped at +/-20).
#   Re-introduction of carry requires the QC Cloud `Future` chain API
#   for a real front/deferred ratio (acceptance #15549 follow-up).
# - Volatility regime multiplier cap in [0.5, 2].
# - Breadth multiplier (formerly labelled FDM, c.1109 + c.1111 REPAIR-5 +
#   c.1113 REPAIR-7): we apply the Carver-style gross-leverage adjustment
#   honestly labelled as an *effective breadth of absolute magnitudes*
#   (inverse concentration), clip [1, 2] — see _breadth_multiplier
#   for the rationale. REPAIR-7 is semantic: the formula `sum(|f|)/sqrt(sum(f^2))`
#   ranges 1 → sqrt(N), where 1 = one magnitude dominates, sqrt(N) = all
#   |f_i| equal; this is the *breadth* of the absolute magnitudes
#   (inverse concentration), NOT a measure of concentration.
# - Cap forecasts in [-20, +20] per Carver rule (system layer, not per instrument).
# - Position sizing: risk-targeted (vol-scaled), not fixed 33%; retarget
#   the delta directly, liquidate only when sign change or target ~ 0
#   (c.1109 REPAIR — no fabricated round-trip cost).
#
# Co-existence with main.py: this file is additive — main.py v3.1 stays intact as
# the ETF baseline against which Carver #13 will be compared on a >= 2016-2026
# window per issue #15549 acceptance.

CARVER_EWMAC_PAIRS = (
    (8, 32),
    (16, 64),
    (32, 128),
    (64, 256),
    (16, 48),
    (32, 96),
)

# Carver rule of thumb (chap. 7): the EWMAC forecast scalar should be
# proportional to sqrt(slow) so that the variance of the EWMAC forecast
# is comparable across horizons. Anchoring at slow=32 (canonical Carver
# pair) gives a baseline scalar of 10; per-horizon scalars scale by
# sqrt(slow/32). See _carver_scalar below.
CARVER_FORECAST_SCALAR_BASE = 10.0
CARVER_FORECAST_SCALAR_REFERENCE_SLOW = 32


def _carver_scalar(slow: int) -> float:
    """Per-horizon EWMAC forecast scalar, normalised against slow=32.

    Carver rule (chap. 7) recommends per-horizon scaling so a 1%/day
    trend maps to ~10 (half the cap) regardless of horizon length.
    Anchoring at slow=32 → scalar=10; faster pairs scale down, slower
    pairs scale up by sqrt(slow/32).
    """
    return CARVER_FORECAST_SCALAR_BASE * np.sqrt(
        slow / CARVER_FORECAST_SCALAR_REFERENCE_SLOW
    )


# Blend weights (Carver rule 60/40 trend + carry).
# c.1063 increment over the c.1107 REPAIR: neutralise CARRY_WEIGHT too so
# the constant matches the inline blend (`blended = trend_component`).
# The substitution point is in `_carry_forecast` — the chain-API hook on
# the QC-equipped lane (po-2026) re-introduces 0.4 with a real
# front/deferred ratio.
CARVER_TREND_WEIGHT = 0.6
CARVER_CARRY_WEIGHT = 0.0
CARRY_PROXY_FALLBACK_USED = False  # set True only if a non-zero proxy is reintroduced

# Per-forecast cap (Carver rule): raw forecasts bounded at +/-20 before
# normalisation, since the scaling step is downstream.
CARVER_FORECAST_CAP = 20.0

# Volatility regime multiplier bounds (Carver 2023 chap. 11).
CARVER_VOL_MULT_MIN = 0.5
CARVER_VOL_MULT_MAX = 2.0

# Average volatility target (annualised) used as the anchor for vol scaling.
# Carver uses ~10-25% depending on instrument class; 0.15 = 15% ann. is a
# neutral starting point that the regime multiplier adjusts.
CARVER_TARGET_VOL_ANNUAL = 0.15


def _ewma(values, span):
    """Exponentially weighted moving average with the specified span.

    Carver uses standard EWM with alpha = 2 / (span + 1).
    """
    if len(values) == 0:
        return float("nan")
    alpha = 2.0 / (span + 1.0)
    out = float(values[0])
    for v in values[1:]:
        out = alpha * float(v) + (1.0 - alpha) * out
    return out


def _annualised_vol(daily_returns, periods_per_year=252):
    """Annualised volatility from a sequence of arithmetic daily returns."""
    arr = np.asarray(daily_returns, dtype=float)
    if arr.size < 2:
        return float("nan")
    return float(np.std(arr, ddof=1) * np.sqrt(periods_per_year))


class CarverThirteen(QCAlgorithm):
    """Carver strategy #13 — EWMAC + regime multiplier + breadth + cap.

    Workflow per instrument, per daily bar:
    1. Compute six EWMAC forecasts (fast - slow EWM of price, scaled per
       horizon via _carver_scalar).
    2. Carry forecast DISABLED on this port (see module docstring); the
       blend is trend-only: forecast = mean(EWMAC).
    3. Cap forecast in [-20, +20].
    4. Compute vol multiplier in [0.5, 2] from realised vs target vol.
    5. Apply breadth multiplier at the portfolio level after collecting
       all per-instrument forecasts (see _breadth_multiplier).
    6. Convert forecast to target weight via vol-scaled position sizing;
       retarget the delta directly — liquidate only on sign change or
       target ~ 0.
    """

    def initialize(self):
        # REPAIR-9 c.1117 instrumentation: counters + snapshot log emitted
        # at end-of-algorithm so the QC backtest output carries the actual
        # reason for 0 orders — was it warming-up, empty history bulk, all
        # instruments skipped, all forecasts zero, or something else?
        # Adjoint po-2025 preflight `msg-20260911T131252-ezr0s6` reported
        # 0 orders + Sharpe 0 / 2762 dates historical head 195d317; this
        # instrumentation discriminates H1 (history bulk vide/sans
        # symboles) from H2 (schedule ancré future ne tire pas) by
        # counting each early-return branch and logging the bulk shape.
        self._rebalance_call_count = 0
        self._rebalance_early_returns = {
            "warming_up": 0,
            "bulk_empty": 0,
            "no_raw_forecasts": 0,
            "abs_sum_zero": 0,
            "completed_no_order": 0,
            "completed_with_orders": 0,
        }
        self._last_bulk_shape = None  # (rows, n_unique_symbols) or None
        self._first_rebalance_logged = False

        # Window: 2016-01-01 -> 2026-12-31 per issue #15549 acceptance. The
        # v3.1 baseline ran 2015-2024; we re-anchor the window to 2016-2026
        # to match Carver's request for >= 2016 OOS.
        self.set_start_date(2016, 1, 1)
        self.set_end_date(2026, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # 19 liquid continuous futures, diversified across asset classes.
        # Mirrors Carver's handbook + the article #15989 universe (slight
        # adjustments to use QC-mapped canonical symbols).
        self.futures_universe = [
            # Equity indices
            "ES",   # S&P 500 e-mini
            "NQ",   # Nasdaq 100 e-mini
            "YM",   # Dow Jones e-mini
            # Rates
            "ZN",   # 10y T-Note
            "ZB",   # 30y T-Bond
            "ZF",   # 5y T-Note
            # Currencies
            "6E",   # Euro FX
            "6B",   # British Pound
            "6J",   # Japanese Yen
            # Energies
            "CL",   # Crude oil WTI
            "NG",   # Natural gas
            "RB",   # RBOB gasoline
            # Metals
            "GC",   # Gold
            "SI",   # Silver
            "HG",   # Copper
            # Grains
            "ZC",   # Corn
            "ZW",   # Wheat
            "ZS",   # Soybeans
            # Softs
            "SB",   # Sugar
        ]
        assert len(self.futures_universe) == 19, (
            f"Carver #13 universe must have 19 instruments, got "
            f"{len(self.futures_universe)}"
        )

        # Add continuous futures contracts (front-month mapped).
        self.symbols = {}
        for ticker in self.futures_universe:
            # Each ticker is mapped to its front-month future. We request a
            # 90-day rolling window of historical data per instrument, which
            # supports the longest EWMAC span (256 days) plus warmup.
            future = self.add_future(
                ticker,
                Resolution.DAILY,
                data_normalization_mode=DataNormalizationMode.BACKWARDS_RATIO,
                data_mapping_mode=DataMappingMode.OPEN_INTEREST,
                contract_depth_offset=0,
            )
            future.set_filter(timedelta(days=0), timedelta(days=90))
            self.symbols[ticker] = future.symbol

        # EWMAC parameters as 6 (fast, slow) Carver pairs.
        self.ewmac_pairs = CARVER_EWMAC_PAIRS
        # Slowest horizon dictates required warmup.
        self.max_slow = max(s for _, s in self.ewmac_pairs)
        self.max_fast = max(f for f, _ in self.ewmac_pairs)

        # Daily returns buffer per instrument for the realised-vol estimator.
        # We keep a 60-day rolling window (Carver uses ~3-month EWMA, but a
        # 60-day std is a tractable, well-documented proxy that the regime
        # multiplier can scale against).
        self.vol_lookback = 60
        self.return_history = {t: deque(maxlen=self.vol_lookback) for t in self.futures_universe}

        # Per-instrument state: latest forecast, latest scaled weight.
        self.forecasts = {t: 0.0 for t in self.futures_universe}

        # Warmup: 2x the slowest EWMAC span (avoids seed-bias on the 256-day
        # slow EWMA — alpha = 2/(256+1) ≈ 0.0078, half-life ~88 bars, so 1x
        # max_slow leaves a non-trivial residual; 2x reaches ~99% mass).
        # Plus vol lookback + a small buffer for chain/exchange calendars.
        warmup = 2 * self.max_slow + self.vol_lookback + 20
        self.set_warm_up(warmup, Resolution.DAILY)

        # Daily rebalance just after market open.
        self.schedule.on(
            self.date_rules.every_day(self.symbols["ES"]),
            self.time_rules.after_market_open(self.symbols["ES"], 30),
            self._rebalance,
        )

        self.set_benchmark("SPY")

    # ----- signal helpers -------------------------------------------------

    def _ewmac_forecast(self, prices, fast, slow):
        """One EWMAC forecast = scaled (fast_ewm - slow_ewm) / slow_ewm.

        Carver rule: forecast = scalar(slow) * (fast - slow) / slow, with the
        scalar per-horizon (see _carver_scalar) so a strong trend yields ~10
        (half of the cap) regardless of horizon length. Returns 0.0
        if there is insufficient data.
        """
        if len(prices) < slow + 2:
            return 0.0
        price_arr = np.asarray(prices, dtype=float)
        fast_ewm = _ewma(price_arr, fast)
        slow_ewm = _ewma(price_arr, slow)
        if not np.isfinite(slow_ewm) or slow_ewm <= 0.0:
            return 0.0
        raw = (fast_ewm - slow_ewm) / slow_ewm
        scaled = raw * _carver_scalar(slow)
        # Apply per-forecast cap.
        return float(np.clip(scaled, -CARVER_FORECAST_CAP, CARVER_FORECAST_CAP))

    def _carry_forecast(self, front_close, deferred_close):
        """Carry = annualised slope of the term structure (front vs deferred).

        NOT CALLED on this port (c.1107 + c.1109 REPAIR): the inline
        blend in `_rebalance` is trend-only (mean of six EWMAC forecasts),
        and `CARVER_CARRY_WEIGHT = 0.0`. Re-introduction of carry
        requires the QC Cloud `Future` chain API for a real front/deferred
        ratio (acceptance #15549 follow-up). This stub is preserved as
        the call site for the QC-equipped lane (po-2026) so the Carver
        60/40 blend can be re-introduced byte-for-byte.

        Returns 0.0 if either series is unavailable.
        """
        if front_close is None or deferred_close is None:
            return 0.0
        if front_close <= 0.0 or deferred_close <= 0.0:
            return 0.0
        # Ratio of deferred to front > 1 implies contango (negative carry).
        ratio = deferred_close / front_close
        # Annualise assuming 12-month deferred minus front horizon; we use a
        # mild annualisation factor so a 5% term-structure gap maps to ~10
        # (half-cap), mirroring the EWMAC calibration.
        annualised = (ratio - 1.0) * 4.0
        return float(np.clip(annualised, -CARVER_FORECAST_CAP, CARVER_FORECAST_CAP))

    def _vol_multiplier(self, realised_vol_annual):
        """Regime vol multiplier in [0.5, 2].

        Carver rule: if realised vol is high, scale positions down; if low,
        scale up. Anchored on the target vol of 15% annualised.
        """
        if not np.isfinite(realised_vol_annual) or realised_vol_annual <= 0.0:
            return 1.0
        raw_mult = CARVER_TARGET_VOL_ANNUAL / realised_vol_annual
        return float(np.clip(raw_mult, CARVER_VOL_MULT_MIN, CARVER_VOL_MULT_MAX))

    def _breadth_multiplier(self, forecasts):
        """Effective breadth multiplier — inverse concentration, sign-invariant
        (Tell c.1069 strict, REPAIR-3 c.1109 + REPAIR-5 c.1111 + REPAIR-7
        c.1113 + REPAIR-8 c.1115 — successive honesty requalifications after
        adjoint po-2025 preflights `msg-20260911T043805-i7tl0g`,
        `msg-20260911T053342-rwwap4`, `msg-20260911T063424-qnc0q9`,
        `msg-20260911T095727-s5n3kl`).

        REPAIR-8 c.1115 — the formula is delegated to the pure-numpy
        helper `breadth_multiplier` (in `breadth_multiplier.py`) so that
        `tests/test_breadth_multiplier.py` and the production code path
        share a single canonical implementation. Earlier iterations kept
        a duplicate `_breadth_multiplier_standalone` in the test file;
        that duplication is removed in REPAIR-8 (see commit). The method
        below is now a thin wrapper preserving the CarverThirteen API
        surface for any caller that holds a reference.

        Formula (instantaneous cross-sectional effective breadth of
        absolute magnitudes — INVERSE concentration):
            breadth = sum(|f_i|) / sqrt(sum(f_i^2))

        Reading (REPAIR-7 c.1113, semantic correction by adjoint po-2025
        habilité n°3 Tell c.15069 strict): the ratio ranges from **1.0
        (one |f_i| dominates, the rest are zero — MINIMUM effective
        breadth, MAXIMUM concentration)** to **sqrt(N) (all |f_i| equal
        — MAXIMUM effective breadth, ZERO concentration)**. This is the
        *inverse* of a concentration measure: 1 = maximally concentrated,
        sqrt(N) = maximally spread. Calling this a "magnitude
        concentration" multiplier in earlier iterations inverted the
        semantic — it is an **effective breadth of absolute magnitudes**.

        Sign-invariance (REPAIR-5 c.1111): `abs()` removes the sign at
        the input, so `[10, 10]` and `[10, -10]` yield the same breadth
        (sqrt(2)). This is verified by `tests/test_breadth_multiplier.py`
        (executable CPU test, no QC Cloud required). The final
        portfolio weight `forecast / abs_sum` (in `_rebalance`) preserves
        the sign; only this multiplier is sign-invariant.

        Relationship to Carver FDM (chap. 9): the Carver FDM penalises
        cross-sectional concentration by scaling down gross leverage when
        forecasts are correlated; it requires an exogenous correlation
        estimate. The instantaneous formula above **cannot** supply that
        estimate — it is a different quantity. Hence this multiplier is
        labelled *breadth*, not *FDM*, and is clipped to [1.0, 2.0] as a
        **soft cap on gross leverage** (when one magnitude dominates,
        leverage is capped at 1x; when magnitudes are spread, leverage
        is amplified up to 2x). The clip is asymmetric on intent:
        magnitudes spread → trust the signal; one magnitude dominates
        → don't trust it more than the baseline.
        """
        return _breadth_multiplier_pure(forecasts)

    # ----- main daily entrypoint ------------------------------------------

    def _rebalance(self):
        self._rebalance_call_count += 1

        if self.is_warming_up:
            self._rebalance_early_returns["warming_up"] += 1
            return

        # Bulk history: one call for all 19 instruments rather than 19
        # individual `history()` calls (point 3 of the review, c.1063).
        n_bars = 2 * self.max_slow + self.vol_lookback + 20
        sym_list = list(self.symbols.values())
        bulk = self.history(sym_list, n_bars, Resolution.DAILY)
        if bulk.empty:
            self._rebalance_early_returns["bulk_empty"] += 1
            # Snapshot the bulk shape on the first empty bulk so the
            # post-mortem can distinguish H1.0 (truly empty DataFrame)
            # from H1.1 (empty after index slice).
            if self._last_bulk_shape is None:
                self._last_bulk_shape = (0, 0)
            return

        # Snapshot the bulk shape on the first non-empty call so the
        # post-mortem can confirm 19 symbols / >= 612 rows reached the
        # slice. Subsequent calls do not overwrite (the shape is stable
        # in steady state).
        if self._last_bulk_shape is None:
            try:
                lvl0 = bulk.index.get_level_values(0)
                n_unique = int(lvl0.unique().size) if hasattr(lvl0, "unique") else 0
            except Exception:
                n_unique = 0
            self._last_bulk_shape = (int(bulk.shape[0]), n_unique)

        raw_forecasts = {}
        for ticker, sym in self.symbols.items():
            if sym not in bulk.index.get_level_values(0):
                continue
            hist = bulk.loc[sym]
            closes = hist["close"].values if "close" in hist.columns else np.array([])
            # REPAIR-9 c.1117 guard tightening: require max_slow + 2 bars
            # before even attempting the slowest EWMAC(64, 256). The
            # EWMA(256) alpha = 2/(256+1) ≈ 0.0078 has a half-life of ~88
            # bars, and the seed `out = values[0]` is non-trivially distant
            # from the steady-state value for ~5 half-lives. Bound by
            # max_slow + 2 (= 258) so the slowest pair has at least 2
            # extra bars of EWMA burn-in before the forecast is read.
            # Tell c.1069 strict: this is a tightening of the guard, not
            # a speculative fix; the rationale is grounded in the EWMA
            # half-life arithmetic documented above.
            if len(closes) < self.max_slow + 2:
                continue

            # Carry disabled in this implementation (issue #15549 cycle
            # c.1107, REPAIR ADJOINT po-2025 `msg-20260911T040615-4c08xy`):
            # the front-only proxy previously used here reduced to the
            # EWMA(8,32) slope on the same close series, which is
            # bit-identical to the EWMAC(8,32) signal already in the trend
            # mean, producing a 100%-trend forecast weighted 0.4 on a
            # duplicate. Rather than ship that, this port ships trend-only
            # (six EWMAC horizons, vol-regime multiplier, breadth bonus, cap).
            #
            # `_carry_forecast(front, deferred)` is preserved as a callable
            # awaiting the QC Cloud `Future` chain API for a real
            # front/deferred ratio. The Carver 2023 chap. 8 carry signal is
            # distinct from any EWMAC slope on a single contract and must
            # not be approximated by it. See the deferred follow-up in
            # issue #15549 acceptance.
            carry_val = 0.0

            # EWMAC forecasts across all six Carver pairs.
            ewmac_vals = [
                self._ewmac_forecast(closes, fast, slow)
                for fast, slow in self.ewmac_pairs
            ]
            trend_component = float(np.mean(ewmac_vals)) if ewmac_vals else 0.0

            # Trend-only blend on this implementation (carry disabled,
            # CARVER_CARRY_WEIGHT = 0.0). The 60/40 trend+carry Carver
            # blend is documented but not applied — see the carry stub
            # above for the chain-API hook.
            blended = trend_component
            raw_forecasts[ticker] = float(
                np.clip(blended, -CARVER_FORECAST_CAP, CARVER_FORECAST_CAP)
            )

            # Vol regime multiplier: realised vol of daily returns.
            if len(closes) >= self.vol_lookback:
                window = closes[-self.vol_lookback:]
                daily_rets = np.diff(window) / window[:-1]
                for r in daily_rets:
                    self.return_history[ticker].append(float(r))
                realised_vol = _annualised_vol(list(self.return_history[ticker]))
            else:
                realised_vol = float("nan")
            self.forecasts[ticker] = raw_forecasts[ticker] * self._vol_multiplier(realised_vol)

        if not raw_forecasts:
            self._rebalance_early_returns["no_raw_forecasts"] += 1
            return

        # Apply breadth multiplier at portfolio level.
        breadth = self._breadth_multiplier(list(self.forecasts.values()))

        # Position sizing: forecast -> weight via inverse-vol scaling.
        abs_sum = sum(abs(v) for v in self.forecasts.values())
        if abs_sum <= 0.0:
            self._rebalance_early_returns["abs_sum_zero"] += 1
            return

        target_value = self.portfolio.total_portfolio_value * breadth
        # REPAIR-9 c.1117: track whether this call actually submits any
        # set_holdings. `set_holdings_issued_this_call` flips True the
        # first time we call set_holdings (sign-change or same-side
        # re-target); it stays False if all forecasts zero (after clip) or
        # all |target_weight| below 0.01 (Carver dead-band).
        set_holdings_issued_this_call = False
        for ticker, sym in self.symbols.items():
            forecast = self.forecasts.get(ticker, 0.0)
            target_weight = 0.0
            if forecast != 0.0:
                # Carver-style proportional weighting: each forecast's
                # share of the absolute sum scales the gross exposure.
                weight = (abs(forecast) / abs_sum) * target_value
                target_weight = np.sign(forecast) * weight / self.portfolio.total_portfolio_value
                target_weight = float(np.clip(target_weight, -1.0, 1.0))
                if abs(target_weight) < 0.01:
                    target_weight = 0.0

            # Retarget the delta directly to avoid fabricated round-trip
            # costs (Tell c.1069 strict, REPAIR-3 c.1109 adjoint po-2025
            # preflight `msg-20260911T043805-i7tl0g`):
            # - liquidate only when sign change (long -> short or vice versa)
            #   OR when target_weight ~ 0;
            # - otherwise `set_holdings` is idempotent on the target
            #   weight (the broker adjusts to the new absolute target, no
            #   synthetic commission on the existing leg).
            current_holding = self.portfolio[sym].quantity
            current_weight = (
                self.portfolio[sym].holdings_value / self.portfolio.total_portfolio_value
                if self.portfolio.total_portfolio_value > 0
                else 0.0
            )
            sign_change = (current_holding > 0 and target_weight < 0) or (
                current_holding < 0 and target_weight > 0
            )
            if target_weight == 0.0 or sign_change:
                # Either we want flat or the side flipped — liquidate first.
                if self.portfolio[sym].invested:
                    self.liquidate(sym)
                if target_weight != 0.0:
                    self.set_holdings(sym, target_weight)
                    set_holdings_issued_this_call = True
            else:
                # Same-side re-target: idempotent set_holdings on the new
                # absolute weight; no fabricated round-trip.
                self.set_holdings(sym, target_weight)
                set_holdings_issued_this_call = True

        # REPAIR-9 c.1117: tally at the bottom of _rebalance so the
        # end-of-algorithm log discriminates "ran fine but no signal"
        # from "skipped before order placement".
        if set_holdings_issued_this_call:
            self._rebalance_early_returns["completed_with_orders"] += 1
        else:
            self._rebalance_early_returns["completed_no_order"] += 1

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        # REPAIR-9 c.1117: log the instrumentation tally so the QC backtest
        # output carries the diagnostic discriminators that allow the
        # adjoint to truncate H1 vs H2 without re-running the backtest.
        # `bulk_shape` is None only if _rebalance never reached the bulk
        # snapshot (all calls were warming_up returns, which would itself
        # be a signal).
        bulk_shape = self._last_bulk_shape
        bulk_str = (
            f"rows={bulk_shape[0]}, unique_syms={bulk_shape[1]}"
            if bulk_shape is not None
            else "never_reached"
        )
        n_inv = self._rebalance_call_count
        er = self._rebalance_early_returns
        completed = er["completed_with_orders"] + er["completed_no_order"]
        self.log(
            f"CARVER13: Final=${final:,.2f}, "
            f"Return={(final - 100000) / 100000:.2%}, "
            f"Breadth-multiplied forecasts={len(self.forecasts)} "
            f"| REPAIR-9 INSTRUMENTATION: "
            f"rebalance_calls={n_inv}, "
            f"completed_calls={completed} (with_orders={er['completed_with_orders']}, "
            f"no_order={er['completed_no_order']}), "
            f"early_returns={er['warming_up']}+{er['bulk_empty']}+"
            f"{er['no_raw_forecasts']}+{er['abs_sum_zero']} "
            f"(warming_up/bulk_empty/no_forecasts/abs_sum_zero), "
            f"bulk_shape={bulk_str}"
        )
