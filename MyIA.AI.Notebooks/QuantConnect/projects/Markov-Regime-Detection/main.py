# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class MarkovRegimeDetection(QCAlgorithm):
    """
    Markov Regime Detection Strategy
    Reference: Hands-On AI Trading, Example 04 (HMM Regimes)

    Detects high/low volatility regimes using a rolling volatility
    threshold and switches between SPY (risk-on) and TLT (risk-off).

    Simplified version without statsmodels dependency:
    Uses rolling realized volatility as regime proxy.
    High vol regime -> TLT (bonds), Low vol regime -> SPY (equities)

    QC Cloud Results (2015-2025):
    - Sharpe: 0.408
    - CAGR: 9.6%
    - MaxDD: 37.6% (needs improvement)
    - Net Profit: 175%

    QC Project ID: 29398512 (Researcher org)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 12, 31)
        self.set_cash(100000)

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol

        # Regime detection parameters
        self.vol_lookback = 21  # 1 month realized vol
        self.vol_threshold_lookback = 252  # 1 year for threshold calibration
        self.vol_percentile = 60  # Above 60th percentile = high vol regime

        self.current_regime = None  # 'high_vol' or 'low_vol'

        self.set_warm_up(self.vol_threshold_lookback + 10, Resolution.DAILY)

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._check_regime
        )

        self.set_benchmark("SPY")

    def _check_regime(self):
        if self.is_warming_up:
            return

        # Get historical returns for regime detection
        hist = self.history(self.spy, self.vol_threshold_lookback + 5, Resolution.DAILY)
        if hist.empty or len(hist) < self.vol_threshold_lookback:
            return

        closes = hist['close'].values
        returns = np.diff(np.log(closes))

        # Current realized volatility (annualized)
        current_vol = np.std(returns[-self.vol_lookback:]) * np.sqrt(252)

        # Rolling vol series for threshold calibration
        vol_series = []
        for i in range(self.vol_lookback, len(returns)):
            rv = np.std(returns[i - self.vol_lookback:i]) * np.sqrt(252)
            vol_series.append(rv)

        vol_threshold = np.percentile(vol_series, self.vol_percentile)

        # Determine regime
        new_regime = 'high_vol' if current_vol > vol_threshold else 'low_vol'

        if new_regime != self.current_regime:
            self.current_regime = new_regime

            if new_regime == 'low_vol':
                # Risk-on: SPY
                self.set_holdings(self.tlt, 0)
                self.set_holdings(self.spy, 1.0)
                self.log(f"REGIME LOW_VOL: Long SPY (vol={current_vol:.3f}, threshold={vol_threshold:.3f})")
            else:
                # Risk-off: TLT
                self.set_holdings(self.spy, 0)
                self.set_holdings(self.tlt, 1.0)
                self.log(f"REGIME HIGH_VOL: Long TLT (vol={current_vol:.3f}, threshold={vol_threshold:.3f})")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MARKOV REGIME: Final=${final:,.2f}, Return={(final - 100000) / 100000:.2%}")
