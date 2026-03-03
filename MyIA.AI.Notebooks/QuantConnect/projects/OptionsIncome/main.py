# region imports
from AlgorithmImports import *
from datetime import timedelta
# endregion


class CoveredCallStrategy(QCAlgorithm):
    """
    Covered Call Strategy sur SPY v4 (Minute, 1 year only)

    Achete le sous-jacent et vend des calls OTM pour generer du premium.
    - Detenir 100 actions SPY
    - Vendre un call OTM (~2% OTM) a expiration ~30 jours
    - Roll avant expiration (7 jours ou si ITM profond)
    """

    def initialize(self):
        self.set_start_date(2024, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # Minute resolution required for options chain
        equity = self.add_equity("SPY", Resolution.MINUTE)
        self.underlying = equity.symbol

        option = self.add_option("SPY", Resolution.MINUTE)
        self.option_symbol = option.symbol

        option.set_filter(
            min_strike=-5,
            max_strike=10,
            min_expiry=timedelta(days=20),
            max_expiry=timedelta(days=45)
        )

        self.target_delta = 0.30
        self.days_to_roll = 7
        self.shares_per_contract = 100

        self.current_call = None
        self.premium_collected = 0
        self.trades_count = 0

        self.schedule.on(
            self.date_rules.every_day(self.underlying),
            self.time_rules.after_market_open(self.underlying, 30),
            self.manage_position
        )
        self.set_benchmark("SPY")

    def on_data(self, data):
        pass

    def manage_position(self):
        if not self.portfolio[self.underlying].invested:
            self.market_order(self.underlying, self.shares_per_contract)
            return

        if self.current_call is None:
            self._sell_call()
            return
        self._check_roll()

    def _sell_call(self):
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

        # Try to find by delta first
        best_call = None
        best_delta_diff = float('inf')
        for call in otm_calls:
            if call.greeks.delta != 0:
                delta_diff = abs(call.greeks.delta - self.target_delta)
                if delta_diff < best_delta_diff:
                    best_delta_diff = delta_diff
                    best_call = call

        # Fallback: ~2% OTM with ~30 days to expiry
        if best_call is None:
            target_expiry = self.time + timedelta(days=30)
            sorted_calls = sorted(otm_calls,
                                  key=lambda x: abs((x.expiry - target_expiry).days))
            if len(sorted_calls) > 0:
                target_strike = underlying_price * 1.02
                best_call = min(sorted_calls[:5],
                                key=lambda x: abs(x.strike - target_strike))

        if best_call is None:
            return

        self.market_order(best_call.symbol, -1)
        self.current_call = best_call.symbol
        premium = best_call.last_price * self.shares_per_contract
        self.premium_collected += premium
        self.trades_count += 1
        self.log(f"SOLD CALL: Strike={best_call.strike}, Premium=${premium:.2f}")

    def _check_roll(self):
        if self.current_call is None or self.current_call not in self.securities:
            self.current_call = None
            return

        option = self.securities[self.current_call]
        days_to_expiry = (option.expiry - self.time).days
        underlying_price = self.securities[self.underlying].price
        is_deep_itm = option.strike_price < underlying_price * 0.98

        if days_to_expiry <= self.days_to_roll or is_deep_itm:
            self.market_order(self.current_call, 1)
            self.log(f"ROLL: Closed {self.current_call}")
            self.current_call = None

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"COVERED CALL v4: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}, Premium=${self.premium_collected:,.2f}, Trades={self.trades_count}")
