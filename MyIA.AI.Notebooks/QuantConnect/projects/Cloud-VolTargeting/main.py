# Cloud-VolTargeting - Volatility Targeting Strategy
# Educational notebook Cloud-06: Three variants of volatility targeting

from AlgorithmImports import *

class VolTargetingAlgorithm(QCAlgorithm):
    """
    Volatility Targeting Strategy with three variants:
    - v1: Single asset (SPY) with vol targeting
    - v2: Multi-asset equal risk contribution
    - v3: Multi-asset with momentum filter
    """

    def initialize(self):
        self.set_cash(100000)
        self.set_start_date(2014, 1, 1)
        self.set_end_date(2025, 1, 1)

        self.version = self.get_parameter("version", "1")

        self.target_vol = 0.12 if self.version == "1" else 0.10
        self.lookback = 21
        self.min_allocation = 0.30 if self.version == "1" else 0.0
        self.max_allocation = 1.50 if self.version == "1" else 0.50

        if self.version == "1":
            self.tickers = ["SPY"]
        else:
            self.tickers = ["SPY", "QQQ", "IEF", "GLD"]

        for ticker in self.tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.schedule.on(
            self.date_rules.month_start(),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

    def rebalance(self):
        if self.version == "1":
            self.rebalance_v1()
        elif self.version == "2":
            self.rebalance_v2()
        elif self.version == "3":
            self.rebalance_v3()

    def _get_closes(self, symbol, period):
        """Get close prices as numpy array from QC history API."""
        hist = self.history(symbol, period, Resolution.DAILY)
        if hist.empty or len(hist) < period:
            return None
        return hist['close'].values

    def rebalance_v1(self):
        spy = self.symbol("SPY")
        closes = self._get_closes(spy, self.lookback)
        if closes is None:
            self.debug("Not enough history for vol calculation")
            return

        realized_vol = self.calculate_realized_vol(closes)

        if realized_vol == 0:
            allocation = self.min_allocation
        else:
            allocation = self.target_vol / realized_vol
            allocation = max(self.min_allocation, min(allocation, self.max_allocation))

        self.debug(f"v1 - Realized vol: {realized_vol:.4f}, Target allocation: {allocation:.2f}")
        self.set_holdings(spy, allocation)

    def rebalance_v2(self):
        target_vol_per_asset = self.target_vol / len(self.tickers)
        portfolio_targets = {}

        for ticker in self.tickers:
            symbol = self.symbol(ticker)
            closes = self._get_closes(symbol, self.lookback)
            if closes is None:
                self.debug(f"Not enough history for {ticker}")
                continue

            realized_vol = self.calculate_realized_vol(closes)
            if realized_vol == 0:
                self.debug(f"Realized vol is zero for {ticker}")
                continue

            allocation = target_vol_per_asset / realized_vol
            allocation = max(0.0, min(allocation, self.max_allocation))
            portfolio_targets[symbol] = allocation
            self.debug(f"v2 - {ticker}: vol={realized_vol:.4f}, alloc={allocation:.2f}")

        if portfolio_targets:
            total_alloc = sum(portfolio_targets.values())
            if total_alloc > 1.0:
                scale_factor = 1.0 / total_alloc
                portfolio_targets = {k: v * scale_factor for k, v in portfolio_targets.items()}
            for symbol, weight in portfolio_targets.items():
                self.set_holdings(symbol, weight)

    def rebalance_v3(self):
        target_vol_per_asset = self.target_vol / len(self.tickers)
        momentum_period = 126
        portfolio_targets = {}

        for ticker in self.tickers:
            symbol = self.symbol(ticker)
            period = max(self.lookback, momentum_period)
            closes = self._get_closes(symbol, period)
            if closes is None or len(closes) < momentum_period:
                self.debug(f"Not enough history for {ticker}")
                continue

            momentum = (closes[-1] - closes[-momentum_period]) / closes[-momentum_period]
            if momentum <= 0:
                self.debug(f"v3 - {ticker}: momentum={momentum:.4f} (negative, skipped)")
                continue

            vol_closes = closes[-self.lookback:]
            realized_vol = self.calculate_realized_vol(vol_closes)
            if realized_vol == 0:
                self.debug(f"Realized vol is zero for {ticker}")
                continue

            allocation = target_vol_per_asset / realized_vol
            allocation = max(0.0, min(allocation, self.max_allocation))
            portfolio_targets[symbol] = allocation
            self.debug(f"v3 - {ticker}: momentum={momentum:.4f}, vol={realized_vol:.4f}, alloc={allocation:.2f}")

        if not portfolio_targets:
            self.debug("v3 - No asset with positive momentum, going 100% IEF")
            ief_symbol = self.symbol("IEF")
            self.set_holdings(ief_symbol, 1.0)
            return

        total_alloc = sum(portfolio_targets.values())
        if total_alloc > 1.0:
            scale_factor = 1.0 / total_alloc
            portfolio_targets = {k: v * scale_factor for k, v in portfolio_targets.items()}
        for symbol, weight in portfolio_targets.items():
            self.set_holdings(symbol, weight)

    def calculate_realized_vol(self, closes):
        if len(closes) < 2:
            return 0.0
        log_returns = np.log(closes[1:] / closes[:-1])
        if len(log_returns) < 2:
            return 0.0
        realized_vol = np.std(log_returns) * np.sqrt(252)
        return realized_vol
