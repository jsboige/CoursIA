# region imports
from AlgorithmImports import *
# endregion


class RiskParity(QCAlgorithm):
    """
    Risk Parity v4: Trend Filter + Rank-based Risk Parity + BND (BEST)
    ==================================================================
    Best variant: Sharpe 0.515, CAGR 10.04%, MaxDD 20.1%

    Combines inverse-volatility weighting with trend filtering.
    BND safe haven when <2 assets trending.

    Iteration results:
    v1: Sharpe 0.395, CAGR 7.84%, MaxDD 20.9% (baseline risk parity)
    v2: Sharpe 0.436, CAGR 8.64%, MaxDD 20.7% (+ trend filter + BND)
    v3: Sharpe 0.480, CAGR 9.26%, MaxDD 19.8% (+ momentum tilt)
    v4: Sharpe 0.515, CAGR 10.04%, MaxDD 20.1% (+ rank-based RP) <-- BEST
    v5: Sharpe 0.488, CAGR 10.03%, MaxDD 17.1% (equal RP - worse Sharpe)

    Reference: Asness/Frazzini 2012, Bridgewater Risk Parity
    """

    TICKERS = ["SPY", "EFA", "GLD", "DBC", "TLT"]
    SAFE_TICKER = "BND"
    VOL_LOOKBACK = 60
    MOM_LOOKBACK = 252
    WARMUP_DAYS = 280
    MIN_TRENDING = 2

    def initialize(self):
        # Measurement against held references (#21420, protocol of #21329):
        # `strategy` (default) keeps the code's decision; `spy` (SPY held) and
        # `6040` (SPY 60 %, BND 40 %) are the two references.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} (strategy | spy | 6040)"
            )

        # The start_date and end_date parameters (%Y%m%d) open the out-of-sample
        # measurement; without them, the window stays as coded below.
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
        self.set_cash(100_000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        if self._mode != "strategy":
            self.settings.seed_initial_prices = True
        self.set_benchmark("SPY")

        self.all_tickers = self.TICKERS + [self.SAFE_TICKER]
        self.symbols = {}
        self.sma_ind = {}
        self.std_indicators = {}

        for ticker in self.TICKERS:
            security = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = security.symbol
            self.sma_ind[ticker] = self.sma(security.symbol, 200, Resolution.DAILY)
            self.std_indicators[ticker] = self.STD(security.symbol, self.VOL_LOOKBACK, Resolution.DAILY)

        safe = self.add_equity(self.SAFE_TICKER, Resolution.DAILY)
        self.symbols[self.SAFE_TICKER] = safe.symbol

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance,
        )

        # Daily data: every order fills at the close, so a buy is checked before
        # the sells of the same rebalance free any margin. A refused buy is
        # re-sent at the next session, once those sells have filled (#20523).
        self._targets = {}
        self._refused = {}
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._resend_refused,
        )

        self.set_warm_up(timedelta(days=self.WARMUP_DAYS))

        # References: same subscriptions, indicators and warm-up, no strategy
        # decision (rebalance and the re-send exit at once), rebalanced at the
        # start of each month.
        if self._mode != "strategy":
            self.schedule.on(
                self.date_rules.month_start("SPY"),
                self.time_rules.after_market_open("SPY", 1),
                self._rebalance_reference,
            )

        # Daily `shadow` trace (contract #18923): portfolio value at the open of
        # each SPY session, spread over e0..e4. The three modes take it at the
        # same instant, on the previous close.
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 0),
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
        spy = self.symbols["SPY"]
        if self._mode == "spy":
            self.set_holdings([PortfolioTarget(spy, 1.0)])
        else:
            self.set_holdings([
                PortfolioTarget(spy, 0.6),
                PortfolioTarget(self.symbols[self.SAFE_TICKER], 0.4),
            ])

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def rebalance(self):
        if self.is_warming_up or self._mode != "strategy":
            return

        trending = {}
        for ticker in self.TICKERS:
            ind = self.sma_ind[ticker]
            if not ind.is_ready:
                continue
            sym = self.symbols[ticker]
            close = self.securities[sym].close
            if close <= ind.current.value:
                continue
            hist = self.history(sym, self.MOM_LOOKBACK + 5, Resolution.DAILY)
            if len(hist) < self.MOM_LOOKBACK * 0.8:
                continue
            ret_12m = hist["close"].iloc[-1] / hist["close"].iloc[-self.MOM_LOOKBACK] - 1

            std_ind = self.std_indicators[ticker]
            if not std_ind.is_ready:
                continue
            std_val = std_ind.current.value
            if close > 0 and std_val > 0:
                inv_vol = close / std_val
            else:
                inv_vol = 1.0

            trending[ticker] = (inv_vol, ret_12m)

        targets = {}
        if len(trending) >= self.MIN_TRENDING:
            sorted_trending = sorted(trending.items(), key=lambda x: x[1][1], reverse=True)
            n = len(sorted_trending)
            raw_weights = []
            for i, (ticker, (inv_vol, _)) in enumerate(sorted_trending):
                rank_score = (n - i) / n
                raw_weights.append((ticker, rank_score * inv_vol))
            total = sum(w for _, w in raw_weights)
            for ticker, w in raw_weights:
                targets[ticker] = w / total
        elif len(trending) > 0:
            risky_weight = len(trending) * 0.25
            per_asset = risky_weight / len(trending)
            for ticker in trending:
                targets[ticker] = per_asset
            targets[self.SAFE_TICKER] = 1.0 - risky_weight
        else:
            targets[self.SAFE_TICKER] = 1.0

        trending_str = ", ".join(
            f"{t}:{r:.1%}" for t, (_, r) in sorted(
                trending.items(), key=lambda x: x[1][1], reverse=True
            )
        )
        self.log(f"Trending ({len(trending)}/{len(self.TICKERS)}): [{trending_str}]")

        self._targets = targets
        self._refused.clear()
        for ticker in self.all_tickers:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_order_event(self, order_event: OrderEvent):
        if order_event.status == OrderStatus.INVALID:
            self._refused[order_event.symbol] = self.time.date()

    def _resend_refused(self):
        if self.is_warming_up or self._mode != "strategy" or not self._refused:
            return
        today = self.time.date()
        for sym, day in list(self._refused.items()):
            if day >= today:
                continue
            del self._refused[sym]
            weight = self._targets.get(sym.value, 0.0)
            self.log(f"RETRY {sym.value} target={weight:.1%} refused={day}")
            self.set_holdings(sym, weight)

    def on_data(self, data: Slice):
        pass
