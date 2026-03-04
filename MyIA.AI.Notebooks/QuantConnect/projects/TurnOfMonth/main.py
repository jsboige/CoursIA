# region imports
from AlgorithmImports import *
# endregion


class TurnOfMonthEffect(QCAlgorithm):
    """
    Turn of the Month Effect v3.0 - SPY Parking

    Key change: hold SPY (1x) during non-ToM windows instead of cash.
    During ToM window: leverage up to 1.5x (SPY+QQQ).
    Captures equity returns year-round plus ToM alpha.

    History:
    v1.0: Sharpe -0.243, CAGR 1.5%, MaxDD 13.2%
    v2.0: Sharpe 0.127, CAGR 4.8%, MaxDD 23.7%, Net +69.5%
    v3.0: Sharpe 0.536, CAGR 14.9%, Net +371.5%, MaxDD 38.7%
         Alpha +0.007, Info Ratio +0.278 (beats SPY)

    Ref: Ariel (1987), Lakonishok & Smidt (1988), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.qqq = self.add_equity("QQQ", Resolution.DAILY).symbol

        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        self.trading_day_of_month = 0
        self.current_month = -1

        # Parameters
        self.entry_days_before_eom = 4
        self.hold_days_after_bom = 4
        self.tom_leverage = 1.5          # 1.5x during ToM
        self.spy_parking = 0.95          # 95% SPY during non-ToM

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._check_calendar
        )

        self.in_tom = False
        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

    def _check_calendar(self):
        if self.is_warming_up:
            return

        if self.time.month != self.current_month:
            self.current_month = self.time.month
            self.trading_day_of_month = 1
        else:
            self.trading_day_of_month += 1

        import calendar
        _, days_in_month = calendar.monthrange(self.time.year, self.time.month)
        calendar_days_remaining = days_in_month - self.time.day
        trading_days_remaining = int(calendar_days_remaining * 0.7)

        in_tom_window = (trading_days_remaining <= self.entry_days_before_eom or
                         self.trading_day_of_month <= self.hold_days_after_bom)

        # Regime filter
        spy_above_sma = True
        if self.spy_sma.is_ready:
            spy_above_sma = self.securities[self.spy].price > self.spy_sma.current.value

        if not spy_above_sma:
            # Risk off: full SPY parking (no leverage)
            if self.in_tom or not self.portfolio[self.spy].invested:
                self.liquidate(self.qqq)
                self.set_holdings(self.spy, self.spy_parking)
                self.in_tom = False
            return

        if in_tom_window and not self.in_tom:
            # Enter ToM window: leverage up
            weight = self.tom_leverage / 2.0
            self.set_holdings(self.spy, weight)
            self.set_holdings(self.qqq, weight)
            self.in_tom = True

        elif not in_tom_window and self.in_tom:
            # Exit ToM window: park in SPY (1x)
            self.liquidate(self.qqq)
            self.set_holdings(self.spy, self.spy_parking)
            self.in_tom = False

        elif not in_tom_window and not self.in_tom and not self.portfolio[self.spy].invested:
            # Safety: always be invested
            self.set_holdings(self.spy, self.spy_parking)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"TOM v3.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
