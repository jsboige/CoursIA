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
        # Measurement against held references (#21594, protocol of #21329):
        # `strategy` (default) keeps the code's decision; `spy` (SPY held) and
        # `6040` (SPY 60 %, BND 40 %) are the two references of the verdict;
        # `ew15` (the 15 stocks of the universe at equal weight) is a diagnostic.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "ew15"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} (strategy | spy | 6040 | ew15)"
            )

        # The start_date and end_date parameters (%Y%m%d) open the measurement
        # after the coded window; without them, the window stays as coded below.
        start_date_param = self._parse_date_param("start_date")
        end_date_param = self._parse_date_param("end_date")
        if start_date_param is not None:
            self.set_start_date(start_date_param)
        else:
            self.set_start_date(2015, 1, 1)
        if end_date_param is not None:
            self.set_end_date(end_date_param)
        else:
            self.set_end_date(2024, 12, 31)
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
        spy = self.add_equity("SPY", Resolution.DAILY).symbol
        # BND is subscribed in the `6040` mode only, so that the `strategy`
        # mode keeps the subscriptions of the original code.
        self._bnd = (
            self.add_equity("BND", Resolution.DAILY).symbol
            if self._mode == "6040"
            else None
        )
        self._spy = spy

        # Weekly rebalance to avoid excessive trading
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.set_warm_up(200, Resolution.DAILY)
        if self._mode != "strategy":
            self.settings.seed_initial_prices = True

        # References: no strategy decision (rebalance exits at once),
        # rebalanced at the start of each month.
        if self._mode != "strategy":
            self.schedule.on(
                self.date_rules.month_start(spy),
                self.time_rules.after_market_open(spy, 1),
                self._rebalance_reference,
            )

        # Daily `shadow` trace (contract #18923): portfolio value at the open of
        # each SPY session, spread over e0..e4. All modes take it at the same
        # instant, on the previous close.
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day(spy),
            self.time_rules.after_market_open(spy, 0),
            self._trace,
        )

    def _parse_date_param(self, name):
        raw = self.get_parameter(name)
        if raw is None or str(raw).strip() == "":
            return None
        return datetime.strptime(str(raw).strip(), "%Y%m%d")

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._mode == "spy":
            self.set_holdings([PortfolioTarget(self._spy, 1.0)])
        elif self._mode == "6040":
            self.set_holdings([
                PortfolioTarget(self._spy, 0.6),
                PortfolioTarget(self._bnd, 0.4),
            ])
        else:
            weight = 1.0 / len(self.tickers)
            self.set_holdings([PortfolioTarget(self.symbols[ticker], weight)
                               for ticker in self.tickers])

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def rebalance(self):
        if self.is_warming_up or self._mode != "strategy":
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
