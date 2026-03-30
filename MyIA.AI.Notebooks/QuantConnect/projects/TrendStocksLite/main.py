from AlgorithmImports import *

class TrendStocksLite(QCAlgorithm):
    """
    Trend Stocks Lite v1.0

    Simple trend-following on 15 diversified large-cap stocks.
    Equal weight among stocks with confirmed uptrend.

    Rules:
    - Per stock: Price > SMA200 AND EMA20 > EMA50 -> bullish
    - Long all bullish stocks with equal weight
    - Cash for stocks not in uptrend

    Differentiator vs EMA-Cross-Stocks: 15 stocks across 5 sectors
    instead of 5 tech stocks. More diversified.

    Reference: Simple trend-following, Faber (2007) TAA concept
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",  # Tech
            "JPM", "V", "MA",                            # Financials
            "UNH", "JNJ",                                # Healthcare
            "XOM", "CVX",                                # Energy
            "HD", "PG", "KO"                             # Consumer
        ]

        self.symbols = {}
        self.sma200 = {}
        self.ema20 = {}
        self.ema50 = {}

        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            sym = equity.symbol
            self.symbols[ticker] = sym
            self.sma200[ticker] = self.sma(sym, 200, Resolution.DAILY)
            self.ema20[ticker] = self.ema(sym, 20, Resolution.DAILY)
            self.ema50[ticker] = self.ema(sym, 50, Resolution.DAILY)

        self.set_benchmark("SPY")
        self.add_equity("SPY", Resolution.DAILY)

        # Weekly rebalance to avoid excessive trading
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.set_warm_up(200, Resolution.DAILY)

    def rebalance(self):
        if self.is_warming_up:
            return

        # Find bullish stocks
        bullish = []
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if not self.sma200[ticker].is_ready:
                continue

            price = self.securities[sym].price
            if price <= 0:
                continue

            in_uptrend = (
                price > self.sma200[ticker].current.value and
                self.ema20[ticker].current.value > self.ema50[ticker].current.value
            )

            if in_uptrend:
                bullish.append(ticker)

        if not bullish:
            if self.portfolio.invested:
                self.liquidate()
                self.log("ALL CASH: No stocks in uptrend")
            return

        # Equal weight
        weight = 1.0 / len(bullish)

        # Liquidate non-bullish
        for ticker in self.tickers:
            if ticker not in bullish:
                sym = self.symbols[ticker]
                if self.portfolio[sym].invested:
                    self.liquidate(sym)

        # Set positions
        for ticker in bullish:
            self.set_holdings(self.symbols[ticker], weight)

        self.log(f"REBAL: {len(bullish)}/{len(self.tickers)} bullish: {bullish}")

    def on_data(self, data):
        pass

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"TREND STOCKS LITE: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
