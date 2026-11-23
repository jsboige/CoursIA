#region imports
from AlgorithmImports import *

from statistics import median

from sklearn.linear_model import Ridge
# endregion

# Parameters (measurement #23630):
#   fix=off  original sizing, orders unchanged: the weight is divided by the
#            contract multiplier, then set_holdings sizes a futures position
#            by initial margin. Passive counters added.
#   fix=on   same signal and same share (1/vol) / sum(1/vol), sized by
#            notional: each contract receives share x portfolio value, capped
#            at max_position_pct; quantity = notional / (price x multiplier),
#            rounded to whole contracts; fully collateralized (gross notional
#            1.0); contracts outside the target are liquidated.
#   ref=spy  reference arm: SPY held over the same window, no futures.
#   universe=fixed (default, #23638)  the two roots that never got a
#            prediction are repaired: Brent is subscribed as BZ (NYMEX Brent
#            Last Day Financial; B is ICE Brent, which receives no contract on
#            QC), and a contract without any open-interest row (the VIX
#            futures on QC) is fitted on the two price factors only.
#   universe=book  original universe: B, and a contract without open
#            interest gets no prediction (ten roots out of twelve).
#   start, end (YYYY-MM-DD): measurement window.
# Counters published as runtime statistics: gross_median, gross_max (gross
# notional / portfolio value at the daily check), held_median (contracts held
# at the daily check), predicted_median (contracts with a positive prediction
# at the rebalance), predicted_roots, rebalances, invalid_orders.
# Diagnostic #23638, also passive: exit_reasons counts, per root and per
# rebalance, why the root got a prediction or not (no_contract,
# no_open_interest, no_indicators, factors_empty, few_dates, nonpositive,
# predicted); added_roots counts the contracts added per root and the range of
# warm-up daily bars they received; price_only_roots counts, per root, the
# rebalances fitted without open interest (universe=fixed).


class InverseVolatilityRankAlgorithm(QCAlgorithm):
    """
    Inverse Volatility Rank and Allocate to Future Contracts.

    This strategy uses Ridge regression to forecast future volatility and
    allocates portfolio weights inversely proportional to expected volatility
    across a basket of futures contracts.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 11

    How it works:
    1. Subscribe to a basket of 12 futures contracts (indices, energy, grains)
    2. Track factors: std of returns, ATR, open interest
    3. Train Ridge regression to predict future volatility
    4. Allocate inverse-volatility weights (lower vol = higher weight)
    5. Rebalance weekly

    Factors (per contract):
    - Standard deviation of daily close returns (60-day)
    - Average True Range (60-day)
    - Open interest

    Label: Standard deviation of open price returns over next 6 days

    Parameters:
    - std_months: Months for std indicator (default: 3)
    - atr_months: Months for ATR indicator (default: 3)
    - training_set_duration: Days of training data (default: 365)
    - weight_multiplier: Leverage of the original sizing, fix=off only
      (default: 2.0)
    - max_position_pct: Max weight per contract (default: 0.15 = 15%)
    - stop_loss_pct: Stop-loss per position (default: 0.08 = 8%)
    - fix, ref, universe, start, end: see the comment above the class
    """

    def initialize(self):
        self._fix = self.get_parameter("fix", "on").strip().lower()
        self._ref = self.get_parameter("ref", "none").strip().lower()
        self._universe = self.get_parameter("universe", "fixed").strip().lower()
        self.set_start_date(self._parse_date(self.get_parameter("start", "2015-01-01")))
        self.set_end_date(self._parse_date(self.get_parameter("end", "2024-04-01")))
        self.set_cash(100_000_000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self._gross = []
        self._held = []
        self._predicted = []
        self._predicted_roots = {}
        self._invalid_orders = 0
        # Diagnostic #23638 (passive): why a root gets no prediction.
        self._roots = []
        self._exit_reasons = {}
        self._added_roots = {}
        self._warmup_bars = {}
        self._price_only = {}

        if self._ref == "spy":
            self._spy = self.add_equity("SPY", Resolution.DAILY).symbol
            return

        self._std_period = self.get_parameter('std_months', 3) * 26
        self._atr_period = self.get_parameter('atr_months', 3) * 26
        self._training_set_duration = timedelta(
            self.get_parameter('training_set_duration', 365)
        )
        self._future_std_period = 6
        self._weight_multiplier = float(
            self.get_parameter('weight_multiplier', 2.0)
        )
        self._max_position_pct = float(
            self.get_parameter('max_position_pct', 0.15)
        )
        self._stop_loss_pct = float(
            self.get_parameter('stop_loss_pct', 0.08)
        )
        self._entry_prices = {}

        self._contracts = []

        # Subscribe to 12 futures contracts across asset classes
        brent = (Futures.Energy.BRENT_CRUDE if self._universe == "book"
                 else Futures.Energy.BRENT_LAST_DAY_FINANCIAL)
        tickers = [
            Futures.Indices.VIX,
            Futures.Indices.SP_500_E_MINI,
            Futures.Indices.NASDAQ_100_E_MINI,
            Futures.Indices.DOW_30_E_MINI,
            brent,
            Futures.Energy.GASOLINE,
            Futures.Energy.HEATING_OIL,
            Futures.Energy.NATURAL_GAS,
            Futures.Grains.CORN,
            Futures.Grains.OATS,
            Futures.Grains.SOYBEANS,
            Futures.Grains.WHEAT,
        ]
        for ticker in tickers:
            future = self.add_future(ticker, extended_market_hours=True)
            future.set_filter(lambda universe: universe.front_month())
            self._roots.append(future.symbol.id.symbol)

        # Weekly rebalancing schedule
        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        self.schedule.on(
            self.date_rules.week_start(schedule_symbol),
            self.time_rules.after_market_open(schedule_symbol, 1),
            self._trade
        )

        # Daily stop-loss check
        self.schedule.on(
            self.date_rules.every_day(schedule_symbol),
            self.time_rules.after_market_open(schedule_symbol, 30),
            self._check_stop_loss
        )

    @staticmethod
    def _parse_date(text):
        year, month, day = (int(part) for part in text.strip().split("-"))
        return datetime(year, month, day)

    def on_data(self, slice):
        if self._ref == "spy" and not self.portfolio[self._spy].invested:
            self.set_holdings(self._spy, 1.0)

    def on_order_event(self, order_event):
        if order_event.status == OrderStatus.INVALID:
            self._invalid_orders += 1

    def on_end_of_algorithm(self):
        def med(values):
            return f"{median(values):.3f}" if values else "n/a"
        self.set_runtime_statistic("gross_median", med(self._gross))
        self.set_runtime_statistic(
            "gross_max", f"{max(self._gross):.3f}" if self._gross else "n/a"
        )
        self.set_runtime_statistic("held_median", med(self._held))
        self.set_runtime_statistic("predicted_median", med(self._predicted))
        self.set_runtime_statistic("rebalances", str(len(self._predicted)))
        roots = ",".join(
            f"{root}:{count}"
            for root, count in sorted(self._predicted_roots.items())
        )
        self.set_runtime_statistic("predicted_roots", roots or "none")
        self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))
        if not self._roots:
            return
        reasons = ";".join(
            f"{root}:" + ",".join(
                f"{reason}={count}"
                for reason, count in sorted(self._exit_reasons.get(root, {}).items())
            )
            for root in sorted(self._roots)
        )
        self.set_runtime_statistic("exit_reasons", reasons)
        added = ";".join(
            f"{root}:{self._added_roots.get(root, 0)}"
            + (f"/bars{min(self._warmup_bars[root])}-{max(self._warmup_bars[root])}"
               if self._warmup_bars.get(root) else "")
            for root in sorted(self._roots)
        )
        self.set_runtime_statistic("added_roots", added)
        price_only = ",".join(
            f"{root}:{count}"
            for root, count in sorted(self._price_only.items())
        )
        self.set_runtime_statistic("price_only_roots", price_only or "none")

    def _count_exit(self, root, reason):
        """Passive counter #23638: exit reason of a root at a rebalance."""
        by_reason = self._exit_reasons.setdefault(root, {})
        by_reason[reason] = by_reason.get(reason, 0) + 1

    def _measure(self):
        """Passive counter: gross notional / value and contracts held."""
        value = self.portfolio.total_portfolio_value
        if value <= 0:
            return
        held = [h for h in self.portfolio.values() if h.invested]
        gross = 0.0
        for holding in held:
            security = self.securities[holding.symbol]
            gross += (abs(holding.quantity) * security.price
                      * security.symbol_properties.contract_multiplier)
        self._gross.append(float(gross / value))
        self._held.append(len(held))

    def _trade(self):
        """Predict volatility and rebalance with inverse-vol weights."""
        # Get open interest data for factor
        open_interest = self.history(
            OpenInterest,
            [c.symbol for c in self._contracts],
            self._training_set_duration,
            fill_forward=False
        )
        open_interest.index = open_interest.index.droplevel(0)

        present = {c.symbol.id.symbol for c in self._contracts}
        for root in self._roots:
            if root not in present:
                self._count_exit(root, "no_contract")

        # Predict next-week volatility for each contract
        expected_volatility_by_security = {}
        for security in self._contracts:
            symbol = security.symbol
            root = symbol.id.symbol
            if symbol in open_interest.index:
                # Combine indicator history with open interest
                factors = pd.concat(
                    [
                        security.indicator_history,
                        open_interest.loc[symbol]
                    ],
                    axis=1
                ).ffill().loc[security.indicator_history.index].dropna()
            elif self._universe == "book":
                self._count_exit(root, "no_open_interest")
                continue
            else:
                # No open-interest row on QC for this contract (the VIX
                # futures, #23638): fit on the two price factors only.
                factors = security.indicator_history.dropna()
                self._price_only[root] = self._price_only.get(root, 0) + 1
            if factors.empty:
                self._count_exit(
                    root,
                    "no_indicators" if security.indicator_history.empty
                    else "factors_empty"
                )
                continue

            label = security.label_history

            # Align factors and labels
            idx = sorted(
                list(
                    set(factors.index).intersection(set(label.index))
                )
            )
            if len(idx) < 20:
                self._count_exit(root, "few_dates")
                continue

            # Train Ridge regression
            model = Ridge()
            model.fit(
                factors.loc[idx].values, label.loc[idx].values
            )

            # Predict volatility
            prediction = model.predict(
                [factors.iloc[-1].values]
            )[0]
            if prediction > 0:
                expected_volatility_by_security[security] = prediction
                self._count_exit(root, "predicted")
            else:
                self._count_exit(root, "nonpositive")
            self.plot(
                "Predictions",
                security.symbol.canonical.value,
                prediction
            )

        self._predicted.append(len(expected_volatility_by_security))
        for security in expected_volatility_by_security:
            root = security.symbol.id.symbol
            self._predicted_roots[root] = self._predicted_roots.get(root, 0) + 1

        # Compute inverse-volatility portfolio weights
        portfolio_targets = []
        std_sum = sum(
            1 / vol
            for vol in expected_volatility_by_security.values()
        )
        if self._fix == "on":
            self._rebalance_notional(expected_volatility_by_security, std_sum)
            return

        for security, expected_vol in (
            expected_volatility_by_security.items()
        ):
            raw_weight = (
                self._weight_multiplier
                / expected_vol
                / std_sum
                / security.symbol_properties.contract_multiplier
            )
            # Cap individual position size
            weight = min(raw_weight, self._max_position_pct)
            portfolio_targets.append(
                PortfolioTarget(security.symbol, weight)
            )
            # Track entry price for stop-loss
            if security.symbol not in self._entry_prices:
                self._entry_prices[security.symbol] = security.price
        self.set_holdings(portfolio_targets, True)

    def _rebalance_notional(self, expected_volatility_by_security, std_sum):
        """fix=on: inverse-vol shares sized by notional, whole contracts."""
        value = self.portfolio.total_portfolio_value
        targets = {}
        for security, expected_vol in (
            expected_volatility_by_security.items()
        ):
            share = min(1 / expected_vol / std_sum, self._max_position_pct)
            unit = (security.price
                    * security.symbol_properties.contract_multiplier)
            if unit <= 0:
                continue
            targets[security.symbol] = int(round(share * value / unit))
            # Track entry price for stop-loss
            if security.symbol not in self._entry_prices:
                self._entry_prices[security.symbol] = security.price
        for holding in self.portfolio.values():
            if holding.invested and holding.symbol not in targets:
                self.liquidate(holding.symbol)
        for symbol, quantity in targets.items():
            delta = quantity - self.portfolio[symbol].quantity
            if delta != 0:
                self.market_order(symbol, delta)

    def _check_stop_loss(self):
        """Liquidate positions that exceeded stop-loss threshold."""
        self._measure()
        for security in list(self._contracts):
            symbol = security.symbol
            if symbol not in self._entry_prices:
                continue
            if not self.portfolio.ContainsKey(symbol):
                continue
            holding = self.portfolio[symbol]
            if holding.quantity == 0:
                self._entry_prices.pop(symbol, None)
                continue
            entry = self._entry_prices[symbol]
            if entry == 0:
                continue
            pnl_pct = (security.price - entry) / entry
            # For short positions, invert PnL
            if holding.quantity < 0:
                pnl_pct = -pnl_pct
            if pnl_pct < -self._stop_loss_pct:
                self.liquidate(symbol)
                self._entry_prices.pop(symbol, None)
                self.plot("Risk", "StopLoss", -self._stop_loss_pct)

    def on_securities_changed(self, changes):
        """Handle futures contract rollovers."""
        if self._ref == "spy":
            return
        for security in changes.added_securities:
            if security.symbol.is_canonical():
                continue  # Skip continuous contracts

            # Create indicators
            security.close_roc = RateOfChange(1)
            security.std_of_close_returns = IndicatorExtensions.of(
                StandardDeviation(self._std_period),
                security.close_roc
            )
            security.atr = AverageTrueRange(self._atr_period)
            security.open_roc = RateOfChange(1)
            security.std_of_open_returns = IndicatorExtensions.of(
                StandardDeviation(self._future_std_period),
                security.open_roc
            )

            # Storage for ML training data
            security.indicator_history = pd.DataFrame()
            security.label_history = pd.Series()

            # Daily consolidator for indicators
            security.consolidator = self.consolidate(
                security.symbol, Resolution.DAILY,
                self._consolidation_handler
            )

            # Warm up with historical data
            warm_up_length = (
                max(self._std_period + 1, self._atr_period)
                + self._training_set_duration.days
            )
            bars = list(self.history[TradeBar](
                security.symbol, warm_up_length, Resolution.DAILY
            ))
            for bar in bars:
                security.consolidator.update(bar)

            self._contracts.append(security)
            root = security.symbol.id.symbol
            self._added_roots[root] = self._added_roots.get(root, 0) + 1
            self._warmup_bars.setdefault(root, []).append(len(bars))

        for security in changes.removed_securities:
            self.subscription_manager.remove_consolidator(
                security.symbol, security.consolidator
            )
            security.close_roc.reset()
            security.std_of_close_returns.reset()
            security.atr.reset()
            security.open_roc.reset()
            security.std_of_open_returns.reset()
            if security in self._contracts:
                self._contracts.remove(security)

    def _consolidation_handler(self, consolidated_bar):
        """Update indicators and track training labels."""
        security = self.securities[consolidated_bar.symbol]
        t = consolidated_bar.end_time

        # Update indicators
        if security.atr.update(consolidated_bar):
            security.indicator_history.loc[t, 'atr'] = (
                security.atr.current.value
            )
        security.close_roc.update(t, consolidated_bar.close)
        if security.std_of_close_returns.is_ready:
            security.indicator_history.loc[
                t, 'std_of_close_returns'
            ] = security.std_of_close_returns.current.value
        security.open_roc.update(t, consolidated_bar.open)

        # Update label: future std of open returns
        if (security.std_of_open_returns.is_ready and
                len(security.indicator_history.index) >
                self._future_std_period):
            security.label_history.loc[
                security.indicator_history.index[
                    -self._future_std_period - 1
                ]
            ] = security.std_of_open_returns.current.value

        # Trim to training window
        security.indicator_history = security.indicator_history[
            security.indicator_history.index >=
            self.time - self._training_set_duration
        ]
        security.label_history = security.label_history[
            security.label_history.index >=
            self.time - self._training_set_duration
        ]
