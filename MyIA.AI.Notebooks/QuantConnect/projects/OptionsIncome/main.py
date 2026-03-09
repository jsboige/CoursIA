# region imports
from AlgorithmImports import *
from datetime import timedelta
# endregion


class CoveredCallStrategy(QCAlgorithm):
    """
    Covered Call Strategy v7.0 - Extended Period

    v6.0 (2023-2024): Sharpe 0.791, CAGR 15.9%, MaxDD 7.5%
    v7.0: Extended to 2018-2026 for multi-regime validation
    (includes 2018 vol spike, 2020 COVID, 2022 rate hikes, 2023-25 recovery)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        equity = self.add_equity("SPY", Resolution.MINUTE)
        self.underlying = equity.symbol

        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        option = self.add_option("SPY", Resolution.MINUTE)
        self.option_symbol = option.symbol

        option.set_filter(
            min_strike=-5,
            max_strike=15,
            min_expiry=timedelta(days=20),
            max_expiry=timedelta(days=45)
        )

        self.target_delta = 0.20
        self.days_to_roll = 10
        self.num_contracts = 2
        self.shares_per_contract = 100
        self.vix_min = 15
        self.vix_max = 35
        self.profit_target = 0.50
        self.defensive_drop = 0.03

        self.current_call = None
        self.call_entry_price = 0.0
        self.premium_collected = 0
        self.trades_count = 0
        self.profit_closes = 0
        self.defensive_closes = 0
        self.prior_spy_close = None

        self.schedule.on(
            self.date_rules.every_day(self.underlying),
            self.time_rules.after_market_open(self.underlying, 30),
            self._manage_position
        )
        self.set_benchmark("SPY")

    def on_end_of_day(self, symbol):
        if symbol == self.underlying:
            self.prior_spy_close = self.securities[self.underlying].price

    def on_data(self, data):
        pass

    def _manage_position(self):
        target_shares = self.shares_per_contract * self.num_contracts
        current_shares = self.portfolio[self.underlying].quantity
        if current_shares < target_shares:
            self.market_order(self.underlying, target_shares - current_shares)
            return

        if self.current_call is None:
            self._sell_call()
            return

        if self._check_early_close():
            return

        self._check_roll()

    def _check_early_close(self):
        if self.current_call not in self.securities:
            self.current_call = None
            return True

        option = self.securities[self.current_call]
        current_price = option.price

        if self.call_entry_price > 0 and current_price <= self.call_entry_price * (1 - self.profit_target):
            self.market_order(self.current_call, self.num_contracts)
            self.log(f"PROFIT TARGET: Closed at {current_price:.2f} (entry {self.call_entry_price:.2f})")
            self.current_call = None
            self.call_entry_price = 0.0
            self.profit_closes += 1
            return True

        if self.prior_spy_close is not None and self.prior_spy_close > 0:
            spy_price = self.securities[self.underlying].price
            daily_return = (spy_price - self.prior_spy_close) / self.prior_spy_close
            if daily_return < -self.defensive_drop:
                self.market_order(self.current_call, self.num_contracts)
                self.log(f"DEFENSIVE CLOSE: SPY {daily_return:.1%}")
                self.current_call = None
                self.call_entry_price = 0.0
                self.defensive_closes += 1
                return True

        return False

    def _sell_call(self):
        vix_price = self.securities[self.vix].price
        if vix_price > 0:
            if vix_price < self.vix_min or vix_price > self.vix_max:
                return

        chain = self.current_slice.option_chains.get(self.option_symbol, None)
        if chain is None:
            return

        calls = [x for x in chain if x.right == OptionRight.CALL]
        if len(calls) == 0:
            return

        underlying_price = self.securities[self.underlying].price
        otm_calls = [x for x in calls if x.strike > underlying_price]
        if len(otm_calls) == 0:
            return

        best_call = None
        best_delta_diff = float('inf')
        for call in otm_calls:
            if call.greeks.delta != 0:
                delta_diff = abs(call.greeks.delta - self.target_delta)
                if delta_diff < best_delta_diff:
                    best_delta_diff = delta_diff
                    best_call = call

        if best_call is None:
            target_expiry = self.time + timedelta(days=30)
            sorted_calls = sorted(otm_calls,
                                  key=lambda x: abs((x.expiry - target_expiry).days))
            if len(sorted_calls) > 0:
                target_strike = underlying_price * 1.03
                best_call = min(sorted_calls[:5],
                                key=lambda x: abs(x.strike - target_strike))

        if best_call is None:
            return

        entry_price = best_call.last_price
        if entry_price <= 0:
            entry_price = best_call.bid_price

        self.market_order(best_call.symbol, -self.num_contracts)
        self.current_call = best_call.symbol
        self.call_entry_price = entry_price
        premium = entry_price * self.shares_per_contract * self.num_contracts
        self.premium_collected += premium
        self.trades_count += 1
        self.log(
            f"SOLD {self.num_contracts}x CALL: Strike={best_call.strike}, "
            f"DTE={(best_call.expiry - self.time).days}, "
            f"Delta={best_call.greeks.delta:.2f}, "
            f"Premium=${premium:.2f}, VIX={vix_price:.1f}"
        )

    def _check_roll(self):
        if self.current_call is None or self.current_call not in self.securities:
            self.current_call = None
            return

        option = self.securities[self.current_call]
        days_to_expiry = (option.expiry - self.time).days
        underlying_price = self.securities[self.underlying].price
        is_deep_itm = option.strike_price < underlying_price * 0.97

        if days_to_expiry <= self.days_to_roll or is_deep_itm:
            self.market_order(self.current_call, self.num_contracts)
            self.log(f"ROLL: DTE={days_to_expiry}, DeepITM={is_deep_itm}")
            self.current_call = None
            self.call_entry_price = 0.0

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(
            f"CC v7.0: Final=${final:,.2f}, "
            f"Return={(final-100000)/100000:.2%}, "
            f"Premium=${self.premium_collected:,.2f}, "
            f"Trades={self.trades_count}, "
            f"ProfitCloses={self.profit_closes}, "
            f"DefensiveCloses={self.defensive_closes}"
        )
