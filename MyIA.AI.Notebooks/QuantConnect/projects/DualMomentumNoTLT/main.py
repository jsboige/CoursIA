from AlgorithmImports import *
import numpy as np

class DualMomentumNoTLT(QCAlgorithm):
    """
    Dual Momentum No TLT v1.0

    Multi-asset momentum rotation without long-duration bonds.

    Rules:
    - Universe: SPY, QQQ, IEF, GLD, XLP
    - Monthly rebalance
    - Absolute momentum: 12M return > 0
    - Relative momentum: top 2 by 12M return
    - Cash if nothing passes absolute filter

    Key insight: TLT lost ~40% during 2020-2023 rate hikes.
    Using IEF (intermediate bonds), GLD, XLP as alternatives.

    Reference: Antonacci (2012), lessons from AllWeather optimization
    """

    def initialize(self):
        # Measurement against held references (#21669, protocol of #21329):
        # `strategy` (default) keeps the code's decision; `spy` (SPY held) and
        # `6040` (SPY 60 %, BND 40 %) are the two references of the verdict;
        # `ew5` (the 5 ETFs of the universe at equal weight) is a diagnostic.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "ew5"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} (strategy | spy | 6040 | ew5)"
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

        self.tickers = ["SPY", "QQQ", "IEF", "GLD", "XLP"]
        self.symbols = {}
        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        self.set_benchmark("SPY")
        spy = self.symbols["SPY"]
        # BND is subscribed in the `6040` mode only, so that the `strategy`
        # mode keeps the subscriptions of the original code.
        self._bnd = (
            self.add_equity("BND", Resolution.DAILY).symbol
            if self._mode == "6040"
            else None
        )
        self.lookback = 252  # 12 months
        self.num_holdings = 2
        self.rebalance_month = -1

        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.set_warm_up(self.lookback + 10, Resolution.DAILY)
        if self._mode != "strategy":
            self.settings.seed_initial_prices = True

        # References: no strategy decision (on_data exits at once),
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
            self.set_holdings([PortfolioTarget(self.symbols["SPY"], 1.0)])
        elif self._mode == "6040":
            self.set_holdings([
                PortfolioTarget(self.symbols["SPY"], 0.6),
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

    def on_data(self, data):
        if self.is_warming_up or self._mode != "strategy":
            return

        # Monthly rebalance
        if self.time.month == self.rebalance_month:
            return
        # A dividend notice arrives alone in a midnight slice, with no bar (#20264):
        # it must not consume the month's rebalance.
        if not any(data.bars.contains_key(s) for s in self.symbols.values()):
            return
        self.rebalance_month = self.time.month

        # Compute 12M momentum for each asset
        scores = {}
        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            # On the 13:00 close slice of a US half-session, a daily history request
            # by bar count comes back about 21 bars short (measured in #20286). Ask
            # for twice the bars and keep the most recent ones.
            history = self.history(symbol, 2 * (self.lookback + 5), Resolution.DAILY)
            history = history.iloc[-(self.lookback + 5):]
            if len(history) < self.lookback:
                continue

            closes = history['close']
            mom_12m = (closes.iloc[-1] / closes.iloc[-self.lookback]) - 1
            scores[ticker] = mom_12m

        if not scores:
            return

        # Absolute momentum filter: only positive
        passing = {t: s for t, s in scores.items() if s > 0}

        if not passing:
            # All negative: go to cash
            if self.portfolio.invested:
                self.liquidate()
                self.log("ALL CASH: No positive 12M momentum")
            return

        # Relative momentum: top N
        sorted_assets = sorted(passing.items(), key=lambda x: x[1], reverse=True)
        selected = [t for t, s in sorted_assets[:self.num_holdings]]
        weight = 1.0 / len(selected)

        # Liquidate non-selected
        for ticker, symbol in self.symbols.items():
            if ticker not in selected and self.portfolio[symbol].invested:
                self.liquidate(symbol)

        # Set positions
        for ticker in selected:
            self.set_holdings(self.symbols[ticker], weight)

        scores_str = ", ".join(f"{t}:{s:.1%}" for t, s in sorted_assets)
        self.log(f"REBAL: Selected={selected}, [{scores_str}]")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"DUAL MOM NoTLT: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
