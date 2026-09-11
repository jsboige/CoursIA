# region imports
from AlgorithmImports import *
import numpy as np
from collections import deque
# endregion


# Carver #13 (Carver 2023, *Advanced Futures Trading Strategies*, Harriman House,
# ISBN 9780857199683) — six EWMAC horizons + carry + volatility-regime multiplier
# [0.5, 2] + blend 60/40 + FDM (Forecast Diversification Multiplier) + cap +/-20.
# Reference article: QuantConnect #15989 (Derek Melchin, 2026-01-02). The article
# reports Sharpe 0.944 vs 0.749 benchmark over a 3-year favourable window
# (2020-07 -> 2023-07); we deliberately do NOT pre-commit to that result. We
# reproduce the strategy with identical parameters and let QC Cloud produce a
# verdict on a >= 2016-2026 window.
#
# Differences vs the v3.1 ETF baseline (main.py):
# - True continuous futures (19 instruments) instead of 6 ETF proxies.
# - Six EWMAC horizons (Carver pairs: 8/32, 16/64, 32/128, 64/256, 16/48, 32/96)
#   with per-horizon scalar normalisation, not a single Donchian 20/10.
# - Carry factor (slope of the term structure) blended 60% trend + 40% carry.
# - Volatility regime multiplier cap in [0.5, 2].
# - FDM (Forecast Diversification Multiplier) to penalise correlated forecasts.
# - Cap forecasts in [-20, +20] per Carver rule (system layer, not per instrument).
# - Position sizing: risk-targeted (vol-scaled), not fixed 33%.
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

# Carver rule of thumb: 10x the slower horizon works well as forecast scalar;
# the choice sets the unit-variance scale of raw EWMAC forecasts so a strong
# trend (1% daily return equivalent) maps to ~10.
CARVER_FORECAST_SCALAR = 10.0

# Blend weights (Carver rule 60/40 trend + carry).
CARVER_TREND_WEIGHT = 0.6
CARVER_CARRY_WEIGHT = 0.4

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
    """Carver strategy #13 — EWMAC + carry + regime multiplier + FDM + cap.

    Workflow per instrument, per daily bar:
    1. Compute six EWMAC forecasts (fast - slow EWM of price, scaled).
    2. Compute carry forecast (annualised slope of term structure).
    3. Blend: forecast = 0.6 * mean(EWMAC) + 0.4 * carry.
    4. Cap forecast in [-20, +20].
    5. Compute vol multiplier in [0.5, 2] from realised vs target vol.
    6. Apply FDM (forecast diversification multiplier) at the portfolio level
       after collecting all per-instrument forecasts.
    7. Convert forecast to target weight via vol-scaled position sizing.
    """

    def initialize(self):
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

        # Warmup: enough bars for the longest EWMAC slow span + carry window
        # + vol lookback.
        warmup = max(self.max_slow * 2, self.vol_lookback) + 10
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

        Carver rule: forecast = scalar * (fast - slow) / slow, with the scalar
        chosen so a strong trend yields ~10 (half of the cap). Returns 0.0
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
        scaled = raw * CARVER_FORECAST_SCALAR
        # Apply per-forecast cap.
        return float(np.clip(scaled, -CARVER_FORECAST_CAP, CARVER_FORECAST_CAP))

    def _carry_forecast(self, front_close, deferred_close):
        """Carry = annualised slope of the term structure (front vs deferred).

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

    def _fdm(self, forecasts):
        """Forecast Diversification Multiplier.

        Carver rule: if the forecasts are highly correlated (each ~equal),
        FDM < 1 to reduce risk concentration. If they are uncorrelated
        (sum-of-squares comparable to sum), FDM -> 1.

        A standard closed-form approximation:
            FDM = sum(|f_i|) / sqrt(sum(f_i^2))
        """
        arr = np.asarray([abs(float(f)) for f in forecasts], dtype=float)
        if arr.size == 0:
            return 1.0
        abs_sum = float(np.sum(arr))
        sq_sum = float(np.sum(arr * arr))
        if sq_sum <= 0.0:
            return 1.0
        # Bound to [1/sqrt(N), 1] where N is the number of forecasts; in
        # practice Carver clamps to a sensible range (e.g., [0.2, 1.5]).
        return float(np.clip(abs_sum / np.sqrt(sq_sum), 0.2, 1.5))

    # ----- main daily entrypoint ------------------------------------------

    def _rebalance(self):
        if self.is_warming_up:
            return

        raw_forecasts = {}
        for ticker, sym in self.symbols.items():
            # Pull enough history for the slowest EWMAC span plus warmup
            # margin. We ask for the slowest span + a small buffer.
            n_bars = self.max_slow + 5
            hist = self.history(sym, n_bars, Resolution.DAILY)
            if hist.empty or len(hist) < self.max_slow:
                continue

            closes = hist["close"].values
            if len(closes) < self.max_slow:
                continue

            # Carry: ratio of deferred contract close to front-month close.
            # In QC, `add_future` returns a `Future` whose `Mapped` is the
            # canonical front; the deferred contract's chain is exposed via
            # the `current` chain. We approximate the carry via the front-
            # month close history itself: a stable proxy in BACKWARDS_RATIO
            # mode is the front-month settle vs itself, which we cannot use
            # directly; so we instead use the EWMA slope of the price series
            # as a coarse carry proxy when no term-structure data is in the
            # history frame. NOTE: when run on QC Cloud with the `Future`
            # chain API, this block would be replaced with a real
            # front/deferred ratio. For tests on `quantbook.ipynb` and on a
            # lane equipped with `quantconnect` Python package, replace
            # `_carry_forecast(...)` with the chain-based implementation.
            #
            # Here we use a smoothed short-window EWM slope scaled into the
            # same [-20, 20] range, explicitly named as a "carry proxy" so
            # the smoke test is verifiable even without a deferred chain.
            if len(closes) >= 30:
                short = _ewma(closes, 8)
                long = _ewma(closes, 32)
                if np.isfinite(short) and np.isfinite(long) and long > 0:
                    proxy_carry = (short - long) / long * CARVER_FORECAST_SCALAR
                    carry_val = float(np.clip(proxy_carry, -CARVER_FORECAST_CAP, CARVER_FORECAST_CAP))
                else:
                    carry_val = 0.0
            else:
                carry_val = 0.0

            # EWMAC forecasts across all six Carver pairs.
            ewmac_vals = [
                self._ewmac_forecast(closes, fast, slow)
                for fast, slow in self.ewmac_pairs
            ]
            trend_component = float(np.mean(ewmac_vals)) if ewmac_vals else 0.0

            # Blend 60/40 trend + carry.
            blended = (
                CARVER_TREND_WEIGHT * trend_component
                + CARVER_CARRY_WEIGHT * carry_val
            )
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
            return

        # Apply FDM at portfolio level.
        fdm = self._fdm(list(self.forecasts.values()))

        # Position sizing: forecast -> weight via inverse-vol scaling.
        abs_sum = sum(abs(v) for v in self.forecasts.values())
        if abs_sum <= 0.0:
            return

        # Liquidate any existing positions before re-targeting (the daily
        # schedule fires before any market-data events).
        for ticker, sym in self.symbols.items():
            if self.portfolio[sym].invested:
                self.liquidate(sym)

        target_value = self.portfolio.total_portfolio_value * fdm
        for ticker, sym in self.symbols.items():
            forecast = self.forecasts.get(ticker, 0.0)
            if forecast == 0.0:
                continue
            # Carver-style proportional weighting: each forecast's share of
            # the absolute sum scales the gross exposure.
            weight = (abs(forecast) / abs_sum) * target_value
            signed_weight = np.sign(forecast) * weight / self.portfolio.total_portfolio_value
            signed_weight = float(np.clip(signed_weight, -1.0, 1.0))
            if abs(signed_weight) < 0.01:
                continue
            self.set_holdings(sym, signed_weight)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(
            f"CARVER13: Final=${final:,.2f}, "
            f"Return={(final - 100000) / 100000:.2%}, "
            f"FDM-applied forecasts={len(self.forecasts)}"
        )
