# region imports
from AlgorithmImports import *
import numpy as np
import time
from collections import deque

# Pure-numpy breadth multiplier (REPAIR-8 c.1115). Imported here so the
# CarverThirteen class and the unit tests share the same canonical formula
# without forcing the tests to pull in AlgorithmImports (which requires
# QC Cloud). See breadth_multiplier.py for the rationale.
from breadth_multiplier import breadth_multiplier as _breadth_multiplier_pure
# Pure-numpy Carver #11 carry leg (semis #17320, tranche 2). Same pattern:
# the stub below and tests/test_carry_forecast.py share the canonical
# annualised-carry formula (article #16001) without AlgorithmImports.
from carry_forecast import annualized_raw_carry as _annualized_raw_carry_pure
from carry_forecast import blend_forecasts as _blend_forecasts_pure
from carry_forecast import CARRY_HISTORY_MAX
from carry_forecast import CARRY_SMOOTHING_SPANS
from carry_forecast import carry_forecasts as _carry_forecasts_pure
from carry_forecast import risk_adjusted_carry as _risk_adjusted_carry_pure
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
# - True continuous futures (18 instruments) instead of 6 ETF proxies.
# - Six EWMAC horizons (Carver pairs: 8/32, 16/64, 32/128, 64/256, 16/48, 32/96)
#   with per-horizon scalar normalisation (c.1063), not a single Donchian 20/10.
# - Carry factor: ACTIVE since semis #17320 tranche 3 (`CARVER_CARRY_WEIGHT
#   = 0.4`, the article #16001 60/40 blend). The c.1107 front-only proxy
#   (trend-duplicate, disabled) is replaced by the exact Carver #11 formula:
#   annualised near/further term-structure carry, risk-adjusted, EWMA-smoothed
#   (spans 5/20/60/120, scalar 30, cap 20) — accumulated daily in `on_data`
#   from the QC Cloud `Future` chain (near + further contracts), pure-numpy
#   canon in `carry_forecast.py`, unit-tested on CPU.
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


# Blend weights (Carver rule 60/40 trend + carry). Tranche 3 (semis #17320)
# re-introduces the 0.4 carry weight on the REAL term-structure signal
# (article #16001 formula in carry_forecast.py) — not the c.1107 proxy,
# which duplicated the EWMAC(8,32) trend and is gone. When no carry span
# has enough history, blend_forecasts renormalises onto the trend leg.
CARVER_TREND_WEIGHT = 0.6
CARVER_CARRY_WEIGHT = 0.4
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
    # Iterating a numpy array boxes one np.float64 per bar; iterating native
    # floats runs the identical arithmetic in the identical order, so the
    # result is bit-identical by construction -- verified over 24,000 random
    # arrays across all 8 spans CARVER_EWMAC_PAIRS reaches -- at 1.5x the
    # speed. Measured #16073: this loop is ~596k entries and ~3% of a
    # 2016-2026 backtest, so the rest of the duration is elsewhere. Hygiene,
    # not a speedup.
    seq = values.tolist() if hasattr(values, "tolist") else values
    out = float(seq[0])
    for v in seq[1:]:
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
        # 15992 defect 2 instrumentation: the order path discriminates
        # "set_holdings called and a contract was named" (mapped_resolved)
        # from "no contract currently mapped, nothing tradeable"
        # (unmapped_skipped). Measured before this fix: set_holdings was
        # called 2759/2759 post-warmup calls at $2M and materialised ZERO
        # orders, because the target was the CONTINUOUS canonical symbol.
        self._order_path = {
            "mapped_resolved": 0,
            "unmapped_skipped": 0,
        }

        # Window: 2016-01-01 -> 2026-12-31 per issue #15549 acceptance. The
        # v3.1 baseline ran 2015-2024; we re-anchor the window to 2016-2026
        # to match Carver's request for >= 2016 OOS.
        # Tranche 4 (semis #17320): the window is parameter-aware so the
        # dev/OOS split backtests run from the SAME compiled code — pass
        # parameters {"start": "YYYYMMDD", "end": "YYYYMMDD"} at backtest
        # creation (QC Cloud), defaults keep the acceptance window intact.
        start_param = self.get_parameter("start")
        end_param = self.get_parameter("end")

        def _as_date(value, fallback):
            if not value:
                return fallback
            return (int(value[0:4]), int(value[4:6]), int(value[6:8]))

        start_y, start_m, start_d = _as_date(start_param, (2016, 1, 1))
        end_y, end_m, end_d = _as_date(end_param, (2026, 12, 31))
        self.set_start_date(start_y, start_m, start_d)
        self.set_end_date(end_y, end_m, end_d)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # 18 liquid continuous futures, diversified across asset classes.
        # Mirrors Carver's handbook + the article #15989 universe (slight
        # adjustments to use QC-mapped canonical symbols).
        #
        # Sugar ("SB") is deliberately absent. Measured 2026-09-14 (#16064):
        # this account's dataset serves no SB data at all -- over 386
        # ES-anchored calls SB reported has_data=0 and Mapped=None every time,
        # while all 18 instruments below reported has_data=386/386. The cause
        # is data absence, not the calendar and not the 90-day filter, and no
        # softs substitute (KC/CC/CT/OJ) is served either. Re-adding SB only
        # re-creates a silent 18/19 universe on every rebalance.
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
        ]
        assert len(self.futures_universe) == 18, (
            f"Carver #13 universe must have 18 instruments, got "
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
            # 0-200 days (was 0-90 pre-tranche-3): the carry leg needs BOTH
            # the near contract AND the next one after it subscribed. On
            # quarterly schedules (ES/ZB/GC-style) consecutive expiries sit
            # ~90 days apart, so a 90-day filter excludes the further leg.
            future.set_filter(timedelta(days=0), timedelta(days=200))
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

        # Carry leg state (semis #17320, tranche 3). One bounded history of
        # daily risk-adjusted carry observations per ticker, fed by on_data
        # from the future chains (near/further closes + expiries), consumed
        # by _rebalance via _carry_forecast. CARRY_HISTORY_MAX = 130 lets
        # the slowest smoothing span (120) reach min_periods with margin.
        self._carry_history = {
            t: deque(maxlen=CARRY_HISTORY_MAX) for t in self.futures_universe
        }
        # Instrumentation (REPAIR-9 idiom): every on_data chain pass counts
        # its outcome so the post-backtest log discriminates "chains never
        # populate at daily resolution" (no_chain dominating) from "chains
        # fine but bars/pairs missing" (no_pair/no_bars) from the healthy
        # path (updates). This is the diagnostic that validates or kills
        # the daily-resolution chain design without a second backtest.
        self._carry_stats = {
            "chain_passes": 0,
            "no_chain": 0,
            "no_pair": 0,
            "no_bars": 0,
            "updates": 0,
            "formula_none": 0,
        }

        # 16076 rollover-aware sliding windows. Under BACKWARDS_RATIO the
        # WHOLE past of a continuous series is re-scaled when the mapped
        # contract changes, so a window fed by on_data is only identical
        # to history() while the mapping is stable. Windows are seeded by
        # ONE bulk history() call, extended by each closed daily bar in
        # on_data, and re-fetched (grouped) whenever a ticker's mapped
        # contract differs from the one memoised at its last fetch. The
        # downstream forecast loop is re-executed verbatim on every call,
        # so identical windows imply identical orders by construction.
        n_bars = 2 * self.max_slow + self.vol_lookback + 20
        self._roll_cache = {
            t: {"closes": deque(maxlen=n_bars), "primed": False, "mapped": None}
            for t in self.futures_universe
        }
        # 3-way clock (hist / fc / wall) + fetch-vs-cache counters, same
        # definitions as the #16073 acceptance measurement the 650.9 s /
        # 694.0 s / 236 ms-per-call reference came from.
        self._history_calls = 0
        self._cache_served = 0
        self._cache_seeded = False
        self._hist_s = 0.0
        self._fc_s = 0.0
        self._wall_s = 0.0

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

    def _annualized_carry(self, near_price, further_price, near_expiry, further_expiry):
        """Annualised raw carry between consecutive contracts (Carver #11).

        Delegates to the pure-numpy formula in `carry_forecast.py`
        (semis #17320, tranche 2): `(near - further) / |expiry gap in
        years|`, gap in months = `round((further_exp - near_exp).days/30)`.
        Returns None on a zero expiry gap or invalid prices — the caller
        treats None as "no carry observation today".
        """
        return _annualized_raw_carry_pure(
            near_price, further_price, near_expiry, further_expiry
        )

    def _carry_forecast(self, carry_forecast_history):
        """Carver #11 carry forecast — annualised term-structure carry, smoothed.

        Called from `_rebalance` since tranche 3 (semis #17320) on the
        history accumulated by `_update_carry_histories` (daily
        risk-adjusted near/further observations from the `Future` chains).
        The c.1107 proxy (front/deferred ratio, x4 "mild annualisation")
        is REPLACED by the exact article #16001 formula, implemented and
        unit-tested in `carry_forecast.py`: annualise the near/further
        price gap by the expiry distance, risk-adjust, EWMA-smooth over
        spans 5/20/60/120, scale by the Carver scalar 30 (p.216), cap at
        +/-20.

        Parameters
        ----------
        carry_forecast_history : sequence of float
            Daily risk-adjusted carry values (annualised raw carry divided
            by annualised price risk), oldest first — accumulated by
            `_update_carry_histories` from the chain near/further closes
            and expiries.

        Returns
        -------
        float
            Equal-weight mean of the per-span capped forecasts (article
            aggregation), 0.0 when no span has enough history.
        """
        forecasts = _carry_forecasts_pure(carry_forecast_history)
        if not forecasts:
            return 0.0
        return float(np.mean(forecasts))

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

    def _mapped_contract(self, continuous):
        """Tradeable front contract for a continuous future, else None.

        #15992 defect 2. `add_future(ticker)` yields the CANONICAL continuous
        `symbol` (sentinel expiry 1899-12-30), which is what `_rebalance`
        used as the `set_holdings` target. Measured on the dedicated
        project 36488678 with the bulk-index defect already fixed (run
        `0b4b9d52`, $2M): `set_holdings` is emitted on every post-warmup
        call (`with_orders=2759/2759`) and materialises **zero** orders,
        while `calculate_order_quantity` on the same call returns 1 (NQ).
        A continuous symbol is not a tradeable contract -- the order must
        name the MAPPED contract.

        Returns None when no contract is currently mapped. Never falls
        back to the continuous symbol: that fallback IS the defect.
        """
        try:
            security = self.securities[continuous]
        except Exception:
            return None
        mapped = getattr(security, "Mapped", None)
        if mapped is None or mapped == continuous:
            return None
        return mapped

    # ----- 16076 sliding windows -------------------------------------------

    def on_data(self, data):
        # Carry leg first (semis #17320, tranche 3): one risk-adjusted
        # near/further observation per ticker per slice, from the chains.
        # Deliberately BEFORE the 16076 warmup guard: if the engine does
        # serve warmup slices, every warmup observation shortens the
        # post-warmup wait for the slowest carry span (120 days), and the
        # roll-cache guard below keeps its own semantics untouched.
        self._update_carry_histories(data)
        # 16076: extend each window with the closed daily bar of its
        # continuous canonical series. Only runs once the cache is seeded:
        # bars received before the seed are covered by the seed fetch
        # itself (history() reads the whole past). During warmup on_data
        # is not called by the engine for algorithm use anyway; the guard
        # keeps the intent explicit.
        if self._roll_cache is None or self.is_warming_up:
            return
        for ticker, sym in self.symbols.items():
            if data.bars.contains_key(sym):
                self._roll_cache[ticker]["closes"].append(
                    float(data.bars[sym].close)
                )

    def _update_carry_histories(self, data):
        """One daily risk-adjusted carry observation per ticker (tranche 3).

        For each continuous symbol: read the future chain from the slice,
        order the contracts by expiry, take the near/further pair, price
        both from the daily bars, annualise the term-structure gap (pure
        `annualized_raw_carry`), risk-adjust against the ticker's
        continuous close window (`risk_adjusted_carry`), append to
        `_carry_history`. Any missing piece skips the ticker for the day
        (the EWMA history simply continues from the previous observation)
        and tallies a reason in `_carry_stats` so the post-backtest log
        discriminates a daily-resolution chain failure (no_chain
        dominating) from missing pairs/bars from the healthy path.
        """
        for ticker, sym in self.symbols.items():
            self._carry_stats["chain_passes"] += 1
            try:
                if not data.future_chains.contains_key(sym):
                    self._carry_stats["no_chain"] += 1
                    continue
                chain = data.future_chains[sym]
            except Exception:
                # Defensive by design: the chains accessor raising at daily
                # resolution is exactly what this instrumentation surfaces.
                self._carry_stats["no_chain"] += 1
                continue
            contracts = sorted(chain, key=lambda s: s.id.date)
            if len(contracts) < 2:
                self._carry_stats["no_pair"] += 1
                continue
            near, further = contracts[0], contracts[1]
            if not (
                data.bars.contains_key(near)
                and data.bars.contains_key(further)
            ):
                self._carry_stats["no_bars"] += 1
                continue
            raw_carry = self._annualized_carry(
                float(data.bars[near].close),
                float(data.bars[further].close),
                float(near.id.date.toordinal()),
                float(further.id.date.toordinal()),
            )
            closes = (
                list(self._roll_cache[ticker]["closes"])
                if self._roll_cache is not None
                else []
            )
            # Include today's continuous close when the slice carries it, so
            # the risk estimate sees the same bar the roll cache will keep.
            # Throwaway list: the 16076 cache append happens under its own
            # guard below, never here.
            if data.bars.contains_key(sym):
                closes.append(float(data.bars[sym].close))
            adjusted = _risk_adjusted_carry_pure(raw_carry, closes)
            if adjusted is None:
                self._carry_stats["formula_none"] += 1
                continue
            self._carry_history[ticker].append(adjusted)
            self._carry_stats["updates"] += 1

    def _stale_tickers(self):
        """Tickers whose window is not guaranteed identical to history().

        Returns None when the cache has never been seeded (first call:
        fetch everything). Otherwise returns the tickers whose mapped
        contract differs from the one memoised at their last fetch, plus
        tickers that gained on_data bars without ever having been seeded.
        A not-primed ticker with an empty window is NOT stale: it has no
        data at all, exactly like a ticker absent from the bulk today.
        """
        if not self._cache_seeded:
            return None
        stale = []
        for ticker, sym in self.symbols.items():
            w = self._roll_cache[ticker]
            if not w["primed"]:
                if len(w["closes"]) > 0:
                    stale.append(ticker)
                continue
            if self._mapped_contract(sym) != w["mapped"]:
                stale.append(ticker)
        return stale

    def _seed_windows(self, bulk):
        """Fill the sliding windows (and the bulk-shape snapshot) from a
        bulk history() frame. Called on the seed fetch and on every
        rollover-triggered re-fetch. The deque maxlen keeps the last
        n_bars closes exactly as history() would return them."""
        sym_level = "symbol" if "symbol" in bulk.index.names else 0
        present_syms = set(bulk.index.get_level_values(sym_level))
        for ticker, sym in self.symbols.items():
            w = self._roll_cache[ticker]
            if sym in present_syms:
                hist = (
                    bulk.xs(sym, level="symbol")
                    if sym_level == "symbol"
                    else bulk.loc[sym]
                )
                closes = (
                    hist["close"].values if "close" in hist.columns else np.array([])
                )
                w["closes"].clear()
                for c in closes:
                    w["closes"].append(float(c))
                w["primed"] = True
                w["mapped"] = self._mapped_contract(sym)
                self._cache_seeded = True
        if self._last_bulk_shape is None:
            try:
                n_unique = int(
                    bulk.index.get_level_values(sym_level).unique().size
                )
            except Exception:
                n_unique = 0
            self._last_bulk_shape = (int(bulk.shape[0]), n_unique)

    # ----- main daily entrypoint ------------------------------------------

    def _rebalance(self):
        t_wall_start = time.perf_counter()
        self._rebalance_call_count += 1

        if self.is_warming_up:
            self._rebalance_early_returns["warming_up"] += 1
            self._wall_s += time.perf_counter() - t_wall_start
            return

        # 16076: serve the forecast loop from the rollover-aware sliding
        # windows when they are guaranteed identical to a fresh bulk
        # (mapping stable since the last fetch), and re-fetch only the
        # stale tickers otherwise. One bulk call on the first post-warmup
        # rebalance, then one grouped call per day where at least one
        # mapped contract changed.
        stale = self._stale_tickers()
        if stale is None or stale:
            t_hist = time.perf_counter()
            fetch_syms = (
                list(self.symbols.values())
                if stale is None
                else [self.symbols[t] for t in stale]
            )
            bulk = self.history(fetch_syms, 2 * self.max_slow + self.vol_lookback + 20, Resolution.DAILY)
            self._hist_s += time.perf_counter() - t_hist
            self._history_calls += 1
            if bulk.empty and stale is None:
                # Seed fetch empty: nothing has ever been served, behave
                # exactly like the pre-16076 code. A stale-only fetch that
                # comes back empty leaves the windows as they are and will
                # be retried next call (the mapping memo is only updated
                # on a successful seed).
                self._rebalance_early_returns["bulk_empty"] += 1
                # Snapshot the bulk shape on the first empty bulk so the
                # post-mortem can distinguish H1.0 (truly empty DataFrame)
                # from H1.1 (empty after index slice).
                if self._last_bulk_shape is None:
                    self._last_bulk_shape = (0, 0)
                self._wall_s += time.perf_counter() - t_wall_start
                return
            self._seed_windows(bulk)
        else:
            self._cache_served += 1

        t_fc = time.perf_counter()
        raw_forecasts = {}
        # 16076: closes now come from the sliding windows, which carry the
        # same bars history() would return (seeded by it, extended by the
        # same daily feed). A ticker with an empty window is exactly a
        # ticker absent from today's bulk under the pre-16076 code.
        closes_by_ticker = {
            t: np.array(w["closes"], dtype=float)
            for t, w in self._roll_cache.items()
            if len(w["closes"]) > 0
        }
        for ticker in self.futures_universe:
            closes = closes_by_ticker.get(ticker)
            if closes is None:
                continue
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

            # Carry leg (semis #17320, tranche 3). The c.1107 REPAIR
            # disabled a front-only proxy that reduced to the EWMAC(8,32)
            # slope — a trend duplicate (history in carry_forecast.py's
            # header). Tranche 3 replaces it with the real Carver #11
            # term-structure signal: the daily risk-adjusted near/further
            # observations accumulated by _update_carry_histories. The leg
            # contributes only once at least one smoothing span has
            # min_periods of history; before that, blend_forecasts
            # renormalises onto the trend leg (documented renormalisation,
            # not a silent 0.6x dampening of the trend).
            carry_hist = self._carry_history.get(ticker)
            carry_val = (
                self._carry_forecast(list(carry_hist))
                if carry_hist is not None
                and len(carry_hist) >= min(CARRY_SMOOTHING_SPANS)
                else None
            )

            # EWMAC forecasts across all six Carver pairs.
            ewmac_vals = [
                self._ewmac_forecast(closes, fast, slow)
                for fast, slow in self.ewmac_pairs
            ]
            trend_component = float(np.mean(ewmac_vals)) if ewmac_vals else 0.0

            # Carver #11 60/40 trend+carry blend (pure, unit-tested helper).
            blended = _blend_forecasts_pure(
                trend_component, carry_val, CARVER_CARRY_WEIGHT
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
            self._rebalance_early_returns["no_raw_forecasts"] += 1
            self._fc_s += time.perf_counter() - t_fc
            self._wall_s += time.perf_counter() - t_wall_start
            return

        # Apply breadth multiplier at portfolio level.
        breadth = self._breadth_multiplier(list(self.forecasts.values()))

        # Position sizing: forecast -> weight via inverse-vol scaling.
        abs_sum = sum(abs(v) for v in self.forecasts.values())
        if abs_sum <= 0.0:
            self._rebalance_early_returns["abs_sum_zero"] += 1
            self._fc_s += time.perf_counter() - t_fc
            self._wall_s += time.perf_counter() - t_wall_start
            return

        target_value = self.portfolio.total_portfolio_value * breadth
        # REPAIR-9 c.1117: track whether this call actually submits any
        # set_holdings. `set_holdings_issued_this_call` flips True the
        # first time we call set_holdings (sign-change or same-side
        # re-target); it stays False if all forecasts zero (after clip) or
        # all |target_weight| below 0.01 (Carver dead-band).
        set_holdings_issued_this_call = False
        for ticker, sym in self.symbols.items():
            # 15992 defect 2: the order must name the MAPPED contract, and
            # the holding lookup below must name the SAME symbol. The
            # position lives on the contract, not on the continuous
            # canonical (see the measured note on the gate).
            order_sym = self._mapped_contract(sym)
            if order_sym is None:
                self._order_path["unmapped_skipped"] += 1
                continue
            self._order_path["mapped_resolved"] += 1
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
            # 15992 defect 2: the holding lookup must name the SAME symbol as
            # the order. Measured (probe 2, project 36488678, run
            # 3e555d8608): after a fill of 100 NQ on the mapped contract,
            # the CONTINUOUS entry still reports quantity=0.0 /
            # invested=False -- `portfolio[canonical]` does NOT aggregate
            # the future's contracts, it returns an empty holding. A gate
            # read on the continuous symbol therefore never fires:
            # `liquidate` is never reached and the position is never
            # closed, and the re-target branch never sees a sign change.
            # (The unused `current_weight` this replaces was computed from
            # the same entry and read nowhere.)
            holding = self.portfolio[order_sym]
            current_holding = holding.quantity
            sign_change = (current_holding > 0 and target_weight < 0) or (
                current_holding < 0 and target_weight > 0
            )
            if target_weight == 0.0 or sign_change:
                # Either we want flat or the side flipped — liquidate first.
                if holding.invested:
                    self.liquidate(order_sym)
                if target_weight != 0.0:
                    self.set_holdings(order_sym, target_weight)
                    set_holdings_issued_this_call = True
            else:
                # Same-side re-target: idempotent set_holdings on the new
                # absolute weight; no fabricated round-trip.
                self.set_holdings(order_sym, target_weight)
                set_holdings_issued_this_call = True

        # REPAIR-9 c.1117: tally at the bottom of _rebalance so the
        # end-of-algorithm log discriminates "ran fine but no signal"
        # from "skipped before order placement".
        if set_holdings_issued_this_call:
            self._rebalance_early_returns["completed_with_orders"] += 1
        else:
            self._rebalance_early_returns["completed_no_order"] += 1
        self._fc_s += time.perf_counter() - t_fc
        self._wall_s += time.perf_counter() - t_wall_start

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
            f"bulk_shape={bulk_str}, "
            f"ORDER-PATH: mapped_resolved={self._order_path['mapped_resolved']} "
            f"unmapped_skipped={self._order_path['unmapped_skipped']} "
            f"| 16076 CLOCKS: hist={self._hist_s:.1f}s fc={self._fc_s:.1f}s "
            f"wall={self._wall_s:.1f}s "
            f"history_calls={self._history_calls} "
            f"cache_served={self._cache_served} "
            f"| 17320 CARRY-LEG: updates={self._carry_stats['updates']} "
            f"no_chain={self._carry_stats['no_chain']} "
            f"no_pair={self._carry_stats['no_pair']} "
            f"no_bars={self._carry_stats['no_bars']} "
            f"formula_none={self._carry_stats['formula_none']} "
            f"chain_passes={self._carry_stats['chain_passes']} "
            f"histories_filled={sum(1 for h in self._carry_history.values() if len(h) >= min(CARRY_SMOOTHING_SPANS))}"
        )
