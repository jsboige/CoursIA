# region imports
from AlgorithmImports import *

from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression
import pandas as pd
# endregion


class MarkovRegimeEquityOptions(QCAlgorithm):
    """
    Markov regime detection traded with a SPY option straddle.

    Port of example 06/04/02 of "Hands-On AI Trading with Python,
    QuantConnect, and AWS" (Jared Broad et al., Wiley, 2025), repository
    QuantConnect/HandsOnAITradingBook at commit e025f21.

    The book's 06/04/01 rotates SPY and TLT; this variant keeps the same
    regime model but expresses the view in options: a LOW volatility regime
    opens a SHORT straddle (sell the move), a HIGH volatility regime opens a
    LONG straddle (buy the move).

    Faithfulness
    ------------
    Model, regime mapping, expiry filter, straddle construction and the
    assignment handler are the book's. Four deviations are declared, all of
    them guards the book leaves implicit -- the book is teaching code and
    lets several calls throw:

    1. Guard on the trailing series length before fitting (the book fits
       whatever it has; below ~100 samples the fit diverges or raises).
    2. Guard on an empty expiry list before min()/max() (the book raises
       ValueError when the filter returns nothing).
    3. try/except around the fit, with a counter, instead of letting the
       scheduled handler die for the day.
    4. Parameters start_year/end_year/cash/lookback_years, whose defaults
       are the book's own values (2019, 2024, 100 000, 3), so that the book
       window replays exactly and a distinct out-of-sample window needs no
       code fork.

    How it works
    ------------
    1. Collect trailing daily returns of SPY through a 1-day RateOfChange
       indicator fed by warm-up history, trimmed to the lookback window.
    2. Fit MarkovRegression(k_regimes=2, switching_variance=True) and read
       the last smoothed probability argmax.
    3. On a regime change -- or whenever the portfolio is flat -- close the
       live straddle and open a new one:
         - low volatility (regime 0) -> short straddle, nearest expiry
         - high volatility (regime 1) -> long straddle, furthest expiry
       Both legs sit at the strike closest to the underlying price.
    4. If a leg is assigned and the underlying ends up held, liquidate the
       underlying and every live leg.

    Parameters
    ----------
    start_year, end_year : book window by default (2019-2024)
    cash                 : starting cash, the book's 100 000 by default
    lookback_years       : trailing window for the regime fit (book: 3)
    min_expiry           : book's 180 days
    max_expiry           : book's 365 days
    min_hold_period      : book's 7 days
    quantity             : straddle size, the book's 1 by default
    """

    def initialize(self):
        self.set_start_date(int(self.get_parameter('start_year', 2019)), 1, 1)
        self.set_end_date(int(self.get_parameter('end_year', 2024)), 1, 1)
        self.set_cash(int(self.get_parameter('cash', 100_000)))
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        # RAW normalization: an option straddle is priced off the raw
        # underlying, not off an adjusted series.
        self._equity = self.add_equity(
            "SPY", data_normalization_mode=DataNormalizationMode.RAW
        )
        self._equity.hedge_contracts = []
        self.set_benchmark(self._equity.symbol)

        self._min_expiry = timedelta(self.get_parameter('min_expiry', 180))
        self._max_expiry = timedelta(self.get_parameter('max_expiry', 365))
        self._min_hold_period = timedelta(self.get_parameter('min_hold_period', 7))
        self._quantity = int(self.get_parameter('quantity', 1))

        option = self.add_option(self._equity.symbol)
        option.set_filter(
            -1, 1, self._min_expiry + self._min_hold_period, self._max_expiry
        )
        self._option_symbol = option.symbol
        self._equity.contract_multiplier = option.symbol_properties.contract_multiplier

        self._lookback_period = timedelta(
            self.get_parameter('lookback_years', 3) * 365
        )

        # Trailing daily returns series.
        self._daily_returns = pd.Series(dtype=float)
        roc = self.roc(self._equity.symbol, 1, Resolution.DAILY)
        roc.updated += self._update_event_handler
        history = self.history[TradeBar](
            self._equity.symbol, self._lookback_period + timedelta(7),
            Resolution.DAILY
        )
        for bar in history:
            roc.update(bar.end_time, bar.close)

        self.schedule.on(
            self.date_rules.every_day(self._equity.symbol),
            self.time_rules.after_market_open(self._equity.symbol, 1),
            self._trade
        )
        self._previous_regime = None

        # Diagnostics, published as runtime statistics.
        self._regime_flips = 0
        self._short_straddles = 0
        self._long_straddles = 0
        self._fit_failures = 0
        self._empty_chains = 0
        self._assignments = 0

    def _update_event_handler(self, indicator, indicator_data_point):
        """Accumulate the trailing return series, trimmed to the lookback."""
        if not indicator.is_ready:
            return
        t = indicator_data_point.end_time
        self._daily_returns.loc[t] = indicator_data_point.value
        self._daily_returns = self._daily_returns[
            t - self._daily_returns.index <= self._lookback_period
        ]

    def _current_regime(self):
        """Last smoothed low/high volatility regime, or None when unfittable."""
        if len(self._daily_returns) < 100:
            return None
        try:
            model = MarkovRegression(
                self._daily_returns, k_regimes=2, switching_variance=True
            )
            return int(
                model.fit().smoothed_marginal_probabilities.values.argmax(axis=1)[-1]
            )
        except Exception as e:
            self._fit_failures += 1
            self.log(f"Markov fit failed ({self._fit_failures}): {e}")
            return None

    def _trade(self):
        regime = self._current_regime()
        if regime is None:
            return
        self.plot('Regime', 'Volatility Class', regime)

        # Rebalance on a regime change, or when we are not invested.
        if regime == self._previous_regime and self.portfolio.invested:
            return
        if regime != self._previous_regime and self._previous_regime is not None:
            self._regime_flips += 1

        # Close the live straddle, if any.
        for symbol in self._equity.hedge_contracts:
            self.liquidate(symbol)
        self._equity.hedge_contracts = []

        chain = self.current_slice.option_chains.get(self._option_symbol)
        if chain is None:
            self._empty_chains += 1
            return

        min_expiry_date = self.time + self._min_expiry + self._min_hold_period
        expiries = [c.expiry for c in chain if c.expiry >= min_expiry_date]
        if not expiries:
            self._empty_chains += 1
            return

        # Low volatility -> short straddle, nearest expiry.
        # High volatility -> long straddle, furthest expiry.
        if regime == 0:
            option_type = OptionStrategies.short_straddle
            expiry = min(expiries)
            self._short_straddles += 1
        else:
            option_type = OptionStrategies.straddle
            expiry = max(expiries)
            self._long_straddles += 1

        # At-the-money strike: closest to the underlying price.
        strike = sorted(
            [c for c in chain if c.expiry == expiry],
            key=lambda c: abs(chain.underlying.price - c.strike)
        )[0].strike

        tickets = self.buy(option_type(self._option_symbol, strike, expiry), self._quantity)
        self._equity.hedge_contracts = [t.symbol for t in tickets]
        self._previous_regime = regime
        self.log(
            f"regime={regime} {'SHORT' if regime == 0 else 'LONG'} straddle "
            f"strike={strike} expiry={expiry}"
        )

    def on_order_event(self, order_event):
        """A leg was assigned: liquidate the underlying and every live leg."""
        if (order_event.status == OrderStatus.FILLED and
                self._equity.invested and
                self._equity.hedge_contracts):
            self._assignments += 1
            self.liquidate(self._equity.symbol)
            for symbol in self._equity.hedge_contracts:
                self.liquidate(symbol)
            self._equity.hedge_contracts = []

    def on_end_of_algorithm(self):
        self.set_runtime_statistic('Regime flips', str(self._regime_flips))
        self.set_runtime_statistic('Short straddles', str(self._short_straddles))
        self.set_runtime_statistic('Long straddles', str(self._long_straddles))
        self.set_runtime_statistic('Fit failures', str(self._fit_failures))
        self.set_runtime_statistic('Empty chains', str(self._empty_chains))
        self.set_runtime_statistic('Assignments', str(self._assignments))
        self.log(
            f"EquityOptions summary: flips={self._regime_flips}, "
            f"short={self._short_straddles}, long={self._long_straddles}, "
            f"fit_failures={self._fit_failures}, empty_chains={self._empty_chains}, "
            f"assignments={self._assignments}, "
            f"final=${self.portfolio.total_portfolio_value:,.0f}"
        )
