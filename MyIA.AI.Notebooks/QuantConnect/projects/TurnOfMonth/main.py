# region imports
from AlgorithmImports import *
# endregion


class TurnOfMonthEffect(QCAlgorithm):
    """
    Turn of the Month Effect v2

    Achete SPY les derniers 4 jours de trading du mois + premiers 4 jours.
    Utilise levier 1.5x car on est investi seulement ~40% du temps.
    Filtre regime SMA200.

    Ref: Ariel (1987), Lakonishok & Smidt (1988)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.qqq = self.add_equity("QQQ", Resolution.DAILY).symbol

        # SMA200 regime filter
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Trading day tracking
        self.trading_day_of_month = 0
        self.current_month = -1
        self.trading_days_in_month = []

        # Parametres
        self.entry_days_before_eom = 4   # Last 4 trading days
        self.hold_days_after_bom = 4     # First 4 trading days
        self.leverage = 1.5              # 1.5x leverage

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._check_calendar
        )

        self.is_invested = False
        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

    def _check_calendar(self):
        if self.is_warming_up:
            return

        # Track trading days in month
        if self.time.month != self.current_month:
            self.current_month = self.time.month
            self.trading_day_of_month = 1
        else:
            self.trading_day_of_month += 1

        # Estimate trading days remaining via calendar
        import calendar
        _, days_in_month = calendar.monthrange(self.time.year, self.time.month)
        calendar_days_remaining = days_in_month - self.time.day
        # Approx: ~70% of calendar days are trading days
        trading_days_remaining = int(calendar_days_remaining * 0.7)

        # Entry: last N trading days OR first N trading days
        in_tom_window = (trading_days_remaining <= self.entry_days_before_eom or
                         self.trading_day_of_month <= self.hold_days_after_bom)

        # Regime filter
        spy_above_sma = True
        if self.spy_sma.is_ready:
            spy_above_sma = self.securities[self.spy].price > self.spy_sma.current.value

        if in_tom_window and spy_above_sma and not self.is_invested:
            weight = self.leverage / 2.0  # Split between SPY and QQQ
            self.set_holdings(self.spy, weight)
            self.set_holdings(self.qqq, weight)
            self.is_invested = True

        elif (not in_tom_window or not spy_above_sma) and self.is_invested:
            self.liquidate(self.spy)
            self.liquidate(self.qqq)
            self.is_invested = False

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"TOM v2: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
