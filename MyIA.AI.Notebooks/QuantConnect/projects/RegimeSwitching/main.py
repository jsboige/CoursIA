# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class RegimeSwitching(QCAlgorithm):
    """
    Regime-Switching Strategy (Mean-Reversion <-> Momentum)
    ========================================================
    Edge: Apply momentum in bull markets, mean-reversion in bear/sideways
    Reference: Price Action Lab (2024), Regime-Switching Factor Models

    iter2 improvements:
    - Monthly rebalancing + regime-change trigger (was daily -> 3428 trades)
    - IEF instead of TLT (TLT destroys value 2015-2026)
    - Risk-adjusted momentum (return/vol) instead of raw return
    - Trailing stop-loss -10% on equity positions
    - Reduced equity in sideways (30% vs 40%)

    Universe: SPY, QQQ, IEF, GLD
    Backtest: 2008-2026
    """

    def initialize(self):
        self.set_start_date(2008, 1, 1)
        self.set_cash(100000)

        # Universe (IEF replaces TLT - better risk-off 2015-2026)
        self.risky = ["SPY", "QQQ"]
        self.defensive = ["IEF", "GLD"]
        self.all_tickers = self.risky + self.defensive

        self.symbols = {}
        for ticker in self.all_tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.set_data_normalization_mode(DataNormalizationMode.ADJUSTED)
            self.symbols[ticker] = equity.symbol

        # Regime detection indicators (on SPY as market proxy)
        spy_symbol = self.symbols["SPY"]
        self.sma50 = self.sma(spy_symbol, 50, Resolution.DAILY)
        self.sma200 = self.sma(spy_symbol, 200, Resolution.DAILY)

        # RSI for mean-reversion signals
        self.rsi_indicators = {}
        for ticker in self.risky:
            indicator = RelativeStrengthIndex(14, MovingAverageType.WILDERS)
            self.register_indicator(self.symbols[ticker], indicator, Resolution.DAILY)
            self.rsi_indicators[ticker] = indicator

        # Parameters
        self.momentum_lookback = 63   # 3-month momentum
        self.vol_lookback = 63        # 3-month volatility for risk-adjusted momentum
        self.rsi_oversold = 30
        self.rsi_exit = 50
        self.stop_loss_pct = -0.10    # Trailing stop-loss -10%

        # State
        self.current_regime = None
        self.last_rebalance = self.start_date
        self.equity_high_water = {}   # For trailing stop

        # Monthly rebalance
        self.schedule.on(
            self.date_rules.month_start("SPY", 1),
            self.time_rules.after_market_open("SPY", 30),
            self.monthly_rebalance
        )

        # Daily regime check (only triggers rebalance on regime change)
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 31),
            self.check_regime_change
        )

        # Daily stop-loss check
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 45),
            self.check_stop_loss
        )

        self.set_warmup(210, Resolution.DAILY)

    def detect_regime(self):
        if not self.sma50.is_ready or not self.sma200.is_ready:
            return "unknown"

        spy_price = self.securities[self.symbols["SPY"]].price
        sma50_val = self.sma50.current.value
        sma200_val = self.sma200.current.value

        if spy_price > sma200_val and sma50_val > sma200_val:
            return "bull"
        elif spy_price < sma200_val and sma50_val < sma200_val:
            return "bear"
        else:
            return "sideways"

    def check_regime_change(self):
        if self.is_warming_up:
            return

        regime = self.detect_regime()
        if regime == "unknown":
            return

        # Only rebalance on regime CHANGE (not every day)
        if regime != self.current_regime and self.current_regime is not None:
            self.debug(f"Regime change: {self.current_regime} -> {regime}")
            self.current_regime = regime
            self.execute_strategy(regime)

        if self.current_regime is None:
            self.current_regime = regime

    def monthly_rebalance(self):
        if self.is_warming_up:
            return

        regime = self.detect_regime()
        if regime == "unknown":
            return

        self.current_regime = regime
        self.execute_strategy(regime)

    def execute_strategy(self, regime):
        if regime == "bull":
            self.apply_momentum_strategy()
        else:
            self.apply_mean_reversion_strategy(regime)

        # Reset high-water marks after rebalance
        for ticker in self.risky:
            sym = self.symbols[ticker]
            if self.portfolio[sym].invested:
                self.equity_high_water[ticker] = self.securities[sym].price

    def apply_momentum_strategy(self):
        history = self.history(
            [self.symbols[t] for t in self.risky],
            self.momentum_lookback + 5,
            Resolution.DAILY
        )

        if history.empty:
            return

        # Risk-adjusted momentum: return / volatility
        risk_adj_mom = {}
        for ticker in self.risky:
            try:
                prices = history.loc[self.symbols[ticker]]["close"]
                if len(prices) >= self.momentum_lookback:
                    raw_return = prices.iloc[-1] / prices.iloc[-self.momentum_lookback] - 1
                    daily_returns = prices.pct_change().dropna()
                    vol = daily_returns.std() * np.sqrt(252)
                    if vol > 0.01:
                        risk_adj_mom[ticker] = raw_return / vol
                    else:
                        risk_adj_mom[ticker] = raw_return
            except (KeyError, TypeError):
                continue

        if not risk_adj_mom:
            return

        best = max(risk_adj_mom, key=risk_adj_mom.get)
        other = [t for t in self.risky if t != best]

        # Liquidate defensive positions
        for ticker in self.defensive:
            if self.portfolio[self.symbols[ticker]].invested:
                self.liquidate(self.symbols[ticker])

        self.set_holdings(self.symbols[best], 0.70)
        if other:
            self.set_holdings(self.symbols[other[0]], 0.30)

    def apply_mean_reversion_strategy(self, regime):
        oversold = []
        for ticker in self.risky:
            if ticker in self.rsi_indicators and self.rsi_indicators[ticker].is_ready:
                rsi_val = self.rsi_indicators[ticker].current.value
                if rsi_val < self.rsi_oversold:
                    oversold.append(ticker)

        if oversold:
            weight_per_asset = 0.3 / len(oversold)
            for ticker in oversold:
                self.set_holdings(self.symbols[ticker], weight_per_asset)

            remaining = 0.7
            self.set_holdings(self.symbols["GLD"], remaining * 0.5)
            self.set_holdings(self.symbols["IEF"], remaining * 0.5)
        else:
            # Exit risky if RSI recovered above exit threshold
            for ticker in self.risky:
                if ticker in self.rsi_indicators and self.rsi_indicators[ticker].is_ready:
                    if self.rsi_indicators[ticker].current.value > self.rsi_exit:
                        if self.portfolio[self.symbols[ticker]].invested:
                            self.liquidate(self.symbols[ticker])

            if regime == "bear":
                self.set_holdings(self.symbols["GLD"], 0.50)
                self.set_holdings(self.symbols["IEF"], 0.50)
            else:
                # Sideways: reduced equity (30% vs previous 40%)
                self.set_holdings(self.symbols["GLD"], 0.35)
                self.set_holdings(self.symbols["IEF"], 0.35)
                self.set_holdings(self.symbols["SPY"], 0.30)

    def check_stop_loss(self):
        if self.is_warming_up:
            return

        for ticker in self.risky:
            sym = self.symbols[ticker]
            if not self.portfolio[sym].invested:
                continue

            current_price = self.securities[sym].price

            # Update high-water mark
            if ticker not in self.equity_high_water:
                self.equity_high_water[ticker] = current_price
            else:
                self.equity_high_water[ticker] = max(
                    self.equity_high_water[ticker], current_price
                )

            # Check trailing stop
            drawdown = (current_price / self.equity_high_water[ticker]) - 1
            if drawdown < self.stop_loss_pct:
                self.liquidate(sym)
                self.debug(f"STOP-LOSS {ticker}: {drawdown:.2%} from high")
                del self.equity_high_water[ticker]

    def on_data(self, data):
        pass
