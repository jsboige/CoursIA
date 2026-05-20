# region imports
from AlgorithmImports import *
# endregion


class CloudMeanReversionSectors(QCAlgorithm):
    """
    Mean Reversion on Sector ETFs — Cloud-04

    Three variants controlled by 'version' parameter:
    - v1: Pure RSI mean reversion (no regime filter)
    - v2: RSI + SMA200 regime filter (bear = exit all)
    - v3: RSI + SMA200 + stop-loss + tighter RSI

    Universe: 11 GICS sector ETFs.
    Signal: RSI(14) < oversold threshold -> buy, exit when RSI > exit threshold.
    """

    def initialize(self):
        self.set_start_date(2014, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        version = self.get_parameter("version", "v1")

        self.sector_etfs = [
            "XLK", "XLF", "XLE", "XLV", "XLI",
            "XLY", "XLP", "XLU", "XLB", "XLRE", "XLC"
        ]
        self.symbols = {}
        self.rsi_indicators = {}

        for etf in self.sector_etfs:
            equity = self.add_equity(etf, Resolution.DAILY)
            self.symbols[etf] = equity.symbol
            self.rsi_indicators[etf] = self.rsi(equity.symbol, 14)

        # SPY for regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        if version == "v1":
            self.rsi_oversold = 35
            self.rsi_exit = 55
            self.num_positions = 3
            self.holding_period = 20
            self.stop_loss_pct = 999  # no stop loss
            self.use_regime_filter = False
        elif version == "v2":
            self.rsi_oversold = 40
            self.rsi_exit = 60
            self.num_positions = 4
            self.holding_period = 15
            self.stop_loss_pct = 999  # no stop loss
            self.use_regime_filter = True
        elif version == "v3":
            self.rsi_oversold = 40
            self.rsi_exit = 60
            self.num_positions = 4
            self.holding_period = 15
            self.stop_loss_pct = 0.08
            self.use_regime_filter = True

        self.position_weight = 1.0 / self.num_positions
        self.entry_days = {}
        self.entry_prices = {}
        self.day_count = 0

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._daily_scan
        )

        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

    def _daily_scan(self):
        if self.is_warming_up:
            return

        self.day_count += 1

        # Regime filter
        if self.use_regime_filter and self.spy_sma.is_ready:
            spy_price = self.securities[self.spy].price
            if spy_price < self.spy_sma.current.value:
                if self.portfolio.invested:
                    self.liquidate()
                    self.entry_days.clear()
                    self.entry_prices.clear()
                return

        # Check exits
        to_exit = []
        for etf in list(self.entry_days.keys()):
            days_held = self.day_count - self.entry_days[etf]
            rsi_val = self.rsi_indicators[etf].current.value
            current_price = self.securities[self.symbols[etf]].price

            if self.stop_loss_pct < 1 and etf in self.entry_prices:
                dd = (current_price - self.entry_prices[etf]) / self.entry_prices[etf]
                if dd < -self.stop_loss_pct:
                    to_exit.append(etf)
                    continue

            if days_held >= self.holding_period or rsi_val > self.rsi_exit:
                to_exit.append(etf)

        for etf in to_exit:
            self.liquidate(self.symbols[etf])
            self.entry_days.pop(etf, None)
            self.entry_prices.pop(etf, None)

        # Entries
        candidates = []
        for etf in self.sector_etfs:
            if etf in self.entry_days:
                continue
            rsi = self.rsi_indicators[etf]
            if not rsi.is_ready:
                continue
            rsi_val = rsi.current.value
            if rsi_val < self.rsi_oversold:
                candidates.append((etf, rsi_val))

        candidates.sort(key=lambda x: x[1])

        available = self.num_positions - len(self.entry_days)
        for etf, rsi_val in candidates[:available]:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, self.position_weight)
            self.entry_days[etf] = self.day_count
            self.entry_prices[etf] = self.securities[symbol].price

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MEAN REV: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
