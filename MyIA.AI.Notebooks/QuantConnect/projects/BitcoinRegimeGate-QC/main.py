#region imports
from AlgorithmImports import *
#endregion
# https://www.quantconnect.com/research/21195/bitcoin-regime-signal-for-growth-equities/
# Bitcoin Regime Signal for Growth Equities by Derek Melchin (QC Research, published Aug 2026)
# Distilled per issue #18576 (re-evaluation of #12748: sources Faber 2007 SSRN 962461,
# Liu & Tsyvinski 2021 RFS 34(6), Iyer 2022 IMF GFSN 2022/001 -- BTC spillovers drive
# 14-18% of equity vol variation, S&P 500 ~17%).
# Rule: hold QQQ when (BTC > SMA50 BTC) AND (ROC20 BTC > 0), else hold SHY.
# Rebalance weekly on the first trading day at 8:00 ET (before the US equity open),
# reading the BTC regime from a 24/7 market (no halts, circuit breakers, or closing bell).
# Author-reported reference (2014-2026): Sharpe 0.838 vs QQQ 0.682 / SPY 0.564.


class BitcoinRegimeGate(QCAlgorithm):

    def initialize(self):
        # Dates are overridable via backtest parameters (start-year/start-month/
        # end-year/end-month) so one compile serves both the IS and OOS runs.
        self.set_start_date(int(self.get_parameter("start-year", 2016)),
                            int(self.get_parameter("start-month", 1)), 1)
        self.set_end_date(int(self.get_parameter("end-year", 2026)),
                          int(self.get_parameter("end-month", 6)), 30)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.qqq = self.add_equity("QQQ", Resolution.DAILY).symbol
        self.shy = self.add_equity("SHY", Resolution.DAILY).symbol

        # Bitcoin trades 24/7: the regime source never sleeps through an equity crash.
        self.btc = self.add_crypto("BTCUSD", Resolution.DAILY, market=Market.BITFINEX).symbol

        self.sma50 = self.sma(self.btc, 50, Resolution.DAILY)
        self.roc20 = self.roc(self.btc, 20, Resolution.DAILY)

        # mode: "gate" (default, the distilled strategy), "hold-qqq" (buy-and-hold benchmark).
        self.mode = self.get_parameter("mode", "gate")

        # Weekly check on the first trading day, 8:00 ET, before the equity open.
        self.schedule.on(
            self.date_rules.week_start(self.qqq),
            self.time_rules.at(8, 0),
            self.rebalance,
        )

        self.set_warm_up(timedelta(60))

    def on_warmup_finished(self):
        self.debug(f"Warmup done: SMA50 ready={self.sma50.is_ready}, ROC20 ready={self.roc20.is_ready}")

    def rebalance(self) -> None:
        if self.is_warming_up or not self.sma50.is_ready or not self.roc20.is_ready:
            return

        if self.mode == "hold-qqq":
            if not self.portfolio[self.qqq].invested:
                self.set_holdings(self.qqq, 1.0)
            return

        btc_price = self.securities[self.btc].price
        risk_on = btc_price > self.sma50.current.value and self.roc20.current.value > 0
        target = self.qqq if risk_on else self.shy

        current = [h.symbol for h in self.portfolio.values() if h.invested]
        if current == [target]:
            return

        self.liquidate()
        self.set_holdings(target, 1.0)
        self.debug(f"{self.time:%Y-%m-%d} BTC={btc_price:,.0f} SMA50={self.sma50.current.value:,.0f} "
                   f"ROC20={self.roc20.current.value:+.3f} -> {'QQQ' if risk_on else 'SHY'}")
