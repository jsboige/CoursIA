# region imports
from AlgorithmImports import *
from datetime import timedelta
# endregion


class CoveredCallStrategy(QCAlgorithm):
    """
    Covered Call Strategy v5.0 - VIX-Filtered

    Improvements over v4:
    - Lower delta (0.20) for higher win rate (50% vs 43%)
    - VIX filter: only sell calls when VIX > 15
    - Wider OTM fallback (3% instead of 2%)
    - Earlier roll (10 days instead of 7)
    - 2 contracts (200 shares) for more premium

    Backtest results (2024):
    v4: Sharpe 0.288, CAGR 9.6%, MaxDD 4.0%, Win 43%
    v5.0: Sharpe 0.747, CAGR 17.3%, MaxDD 8.3%, Win 50%

    Note: 1 year only (MINUTE resolution), single-year bias possible.

    Ref: CBOE BXM methodology, research.ipynb
    """

    def initialize(self):
        self.set_start_date(2024, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # Minute resolution required for options chain
        equity = self.add_equity("SPY", Resolution.MINUTE)
        self.underlying = equity.symbol

        # VIX for premium filter
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        option = self.add_option("SPY", Resolution.MINUTE)
        self.option_symbol = option.symbol

        option.set_filter(
            min_strike=-5,
            max_strike=15,
            min_expiry=timedelta(days=20),
            max_expiry=timedelta(days=45)
        )

        # Optimized parameters
        self.target_delta = 0.20       # Lower delta = higher win rate
        self.days_to_roll = 10         # Earlier roll
        self.num_contracts = 2         # 200 shares
        self.shares_per_contract = 100
        self.vix_threshold = 15        # Only sell when VIX > 15

        self.current_call = None
        self.premium_collected = 0
        self.trades_count = 0

        self.schedule.on(
            self.date_rules.every_day(self.underlying),
            self.time_rules.after_market_open(self.underlying, 30),
            self._manage_position
        )
        self.set_benchmark("SPY")

    def on_data(self, data):
        pass

    def _manage_position(self):
        # Ensure underlying position
        target_shares = self.shares_per_contract * self.num_contracts
        current_shares = self.portfolio[self.underlying].quantity
        if current_shares < target_shares:
            self.market_order(self.underlying, target_shares - current_shares)
            return

        if self.current_call is None:
            self._sell_call()
            return
        self._check_roll()

    def _sell_call(self):
        # VIX filter: skip if VIX too low (not enough premium)
        vix_price = self.securities[self.vix].price
        if vix_price > 0 and vix_price < self.vix_threshold:
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

        # Find by delta
        best_call = None
        best_delta_diff = float('inf')
        for call in otm_calls:
            if call.greeks.delta != 0:
                delta_diff = abs(call.greeks.delta - self.target_delta)
                if delta_diff < best_delta_diff:
                    best_delta_diff = delta_diff
                    best_call = call

        # Fallback: ~3% OTM with ~30 days to expiry
        if best_call is None:
            target_expiry = self.time + timedelta(days=30)
            sorted_calls = sorted(otm_calls,
                                  key=lambda x: abs((x.expiry - target_expiry).days))
            if len(sorted_calls) > 0:
                target_strike = underlying_price * 1.03  # 3% OTM
                best_call = min(sorted_calls[:5],
                                key=lambda x: abs(x.strike - target_strike))

        if best_call is None:
            return

        self.market_order(best_call.symbol, -self.num_contracts)
        self.current_call = best_call.symbol
        premium = best_call.last_price * self.shares_per_contract * self.num_contracts
        self.premium_collected += premium
        self.trades_count += 1
        self.log(f"SOLD {self.num_contracts}x CALL: Strike={best_call.strike}, Premium=${premium:.2f}, VIX={vix_price:.1f}")

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
            self.log(f"ROLL: Closed {self.current_call}, DTE={days_to_expiry}")
            self.current_call = None

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"CC v5.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}, Premium=${self.premium_collected:,.2f}, Trades={self.trades_count}")
