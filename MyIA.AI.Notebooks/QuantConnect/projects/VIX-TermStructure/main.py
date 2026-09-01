# region imports
from AlgorithmImports import *
from collections import deque
import numpy as np
# endregion


class VIXTermStructureStrategy(QCAlgorithm):
    """
    VIX Term Structure Strategy v6.0 - Dual-Signal VRP (eVRP + term structure)

    Consolidation of QuantConnect research article #21143 "Harvesting the
    Volatility Risk Premium with a Dual VIX Signal" (Melchin, 2026-08) into
    the existing VIX-TermStructure project. Replaces the single-signal SVXY
    mechanism (v2-v5.1, project-documented ceiling Sharpe ~0.05-0.10) with the
    dual-signal volatility-risk-premium harvest of Zarattini/Aziz/Mele.

    SIGNAL 1 - eVRP (expected volatility risk premium):
        eVRP = VIX - eRV30, where eRV30 = rolling std of the last N SPY daily
        returns (N=10), annualized (sqrt(252) * 100). eVRP > 0 means implied
        vol overprices realized vol -> short-vol premium available.

    SIGNAL 2 - VIX term structure:
        VIX < VIX3M = contango (normal regime), VIX > VIX3M = backwardation
        (stress regime).

    4-state target weight on VIXY (magnitude scales with VIX level):
        eVRP > 0 + contango   -> short vol full (-VIX/100)
        eVRP < 0 + contango   -> short vol half (-VIX/100 * 0.5)
        eVRP < 0 + backward.  -> long vol      (+VIX/100)
        eVRP > 0 + backward.  -> cash (conflicting signals)

    Remaining capital goes to SPY during short-volatility states only.
    Execution: 16 minutes before close. Rebalance skipped unless the vol
    weight changes sign or moves more than 2%.

    Article claim (2016-01..2026-07, blog): Sharpe 0.729 vs SPY 0.582;
    parameter grid (window 6-14d, eVRP threshold 1-5%) all beat benchmark
    (0.713-0.773). v6.0 measures that claim on our own harness, dev window
    2016-2021 and OOS window 2022-2026 reported separately.

    Iteration history:
    v2.0: Sharpe -0.97 (VIXY + SVXY, complex rules)
    v3.1: Sharpe -0.27 (SVXY only, VIX level filter)
    v4.0: Sharpe -0.65 (ratio + double-SMA declining filter, too restrictive)
    v4.1: Sharpe +0.05 (ratio + SMA10 calm filter, 2015 start)
    v4.2: Sharpe -0.23 (VIX<18 too tight, too few entries)
    v4.3: Sharpe +0.03 (dynamic sizing, higher MaxDD)
    v5.0: Sharpe -0.10 (SHY 70% + stop 7%, too diluted)
    v5.1: Sharpe -0.13 (position 25%, cash drag kills Sharpe in high-rate env)
    v6.0: dual-signal eVRP + term structure, VIXY vol-scaled weight (this version)

    Ref: Zarattini, C., Aziz, A., & Mele, A. (2025). "The Volatility Edge: A
    Dual Approach for VIX ETNs Trading". Swiss Finance Institute Research
    Paper No. 25-91, SSRN 5316487 (primary source, author order verified
    firsthand); Melchin, D. (2026) quantconnect.com/research/21143;
    Simon & Campasano (2014), Whaley (2009) - prior project refs.
    """

    def initialize(self):
        start = self.get_parameter("start", "2016-01-01")
        end = self.get_parameter("end", "2026-06-30")
        sy, sm, sd = (int(x) for x in start.split("-"))
        ey, em, ed = (int(x) for x in end.split("-"))
        self.set_start_date(sy, sm, sd)
        self.set_end_date(ey, em, ed)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # VIX index (30-day implied vol) and VIX3M (93-day) - term structure signal
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol
        self.vix3m = self.add_data(CBOE, "VIX3M", Resolution.DAILY).symbol

        # VIXY = short-term VIX futures ETN (long-vol instrument, shorted when harvesting)
        self.vixy = self.add_equity("VIXY", Resolution.DAILY).symbol
        # SPY = eRV30 input + equity overlay for remaining capital
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Dual-signal parameters (article base: 10-day window, sign-only eVRP)
        self.rv_window = int(self.get_parameter("rv_window", "10"))
        self.evrp_threshold = float(self.get_parameter("evrp_threshold", "0.0"))
        self.rebalance_band = 0.02

        self.spy_closes = deque(maxlen=self.rv_window + 1)
        self._prev_vol_weight = 0.0

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.before_market_close("SPY", 16),
            self._rebalance
        )

        self.set_benchmark("SPY")
        self.set_warm_up(self.rv_window + 5, Resolution.DAILY)

    def on_data(self, data: Slice):
        if data.bars.contains_key(self.spy):
            self.spy_closes.append(data.bars[self.spy].close)

    def _rebalance(self):
        if self.is_warming_up:
            return
        if len(self.spy_closes) < self.rv_window + 1:
            return

        vix_price = self.securities[self.vix].price
        vix3m_price = self.securities[self.vix3m].price
        if vix_price <= 0 or vix3m_price <= 0:
            return

        # Signal 1: eVRP = VIX - annualized forecast of 30d realized vol
        closes = list(self.spy_closes)
        rets = [closes[i] / closes[i - 1] - 1.0 for i in range(1, len(closes))]
        erv30 = float(np.std(rets, ddof=1)) * np.sqrt(252.0) * 100.0
        evrp = vix_price - erv30

        # Signal 2: term structure regime
        contango = vix_price < vix3m_price

        # 4-state target vol weight
        if evrp > self.evrp_threshold and contango:
            vol_weight = -vix_price / 100.0
        elif evrp < -self.evrp_threshold and contango:
            vol_weight = -vix_price / 100.0 * 0.5
        elif evrp < -self.evrp_threshold and not contango:
            vol_weight = vix_price / 100.0
        else:
            vol_weight = 0.0

        # Rebalance filter: act only on sign change or > 2% weight move
        same_sign = np.sign(vol_weight) == np.sign(self._prev_vol_weight)
        if same_sign and abs(vol_weight - self._prev_vol_weight) <= self.rebalance_band:
            return

        # SPY overlay only during short-volatility states
        spy_weight = 1.0 + vol_weight if vol_weight < 0 else 0.0

        if abs(vol_weight) > 0:
            self.set_holdings(self.vixy, vol_weight)
        else:
            self.liquidate(self.vixy)
        if spy_weight > 0:
            self.set_holdings(self.spy, spy_weight)
        else:
            self.liquidate(self.spy)

        self._prev_vol_weight = vol_weight
        self.log(f"REBAL eVRP={evrp:.2f} eRV30={erv30:.2f} VIX={vix_price:.1f} "
                 f"VIX3M={vix3m_price:.1f} contango={contango} "
                 f"vol_w={vol_weight:.3f} spy_w={spy_weight:.3f}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"VIX v6.0 FINAL: ${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
