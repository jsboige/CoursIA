# region imports
from AlgorithmImports import *
# endregion


class DynamicOptionsWheel(QCAlgorithm):
    """
    Dynamic Delta/Skew Options Wheel Strategy.

    Extends the basic Option-Wheel with dynamic strike selection:
    - IV percentile-based OTM targeting: sell closer ATM in low IV,
      further OTM in high IV environments
    - 25-delta put-call skew adjustment: shift OTM targets when
      skew indicates bearish sentiment
    - Rolling IV regime classification (252-day lookback)
    - Greeks-based selection when available, OTM fallback otherwise

    Instead of always selling 5% OTM (like Option-Wheel), this strategy
    adjusts the target OTM percentage based on the current IV regime:
    - Low IV (below 30th percentile): 2.5% OTM (closer ATM, more premium)
    - Normal IV (30-70th percentile): linear interpolation 2.5% -> 7.5%
    - High IV (above 70th percentile): 7.5% OTM (further OTM, safety)

    When 25-delta skew is elevated (put IV >> call IV), the strategy
    sells puts even further OTM (adds 2.5% to OTM target) to account
    for the bearish sentiment embedded in the skew.

    Source: ECE student project (Asseli, Gr01 H.5), adapted for ESGF pool.
    Issue #238 - Integrate ECE student concepts into QC strategies.

    Universe: SPY
    Benchmark: Option-Wheel (fixed 5% OTM, VIX filter)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE,
                                 AccountType.CASH)

        # Equity underlying (raw prices required for options)
        self._equity = self.add_equity(
            "SPY", Resolution.MINUTE,
            data_normalization_mode=DataNormalizationMode.RAW
        )
        self.set_benchmark("SPY")

        # Option chain with pricing model for Greeks
        option = self.add_option("SPY", Resolution.MINUTE)
        option.set_filter(-10, 10, timedelta(15), timedelta(45))
        # Enable Greeks computation via Black-Scholes pricing model
        option.price_model = OptionPriceModels.black_scholes()
        self._option_symbol = option.symbol

        # VIX (optional, for supplementary regime info)
        try:
            self._vix = self.add_index("VIX", Resolution.DAILY).symbol
        except Exception:
            self._vix = None

        # --- OTM targeting parameters (primary method) ---
        self.iv_lookback = 252      # 1 year for IV percentile
        self.target_dte = 21        # Target days to expiry
        self.min_dte = 15           # Minimum DTE for contract selection
        self.max_dte = 45           # Maximum DTE

        # OTM targets by IV regime (replaces fixed 5% OTM)
        self.otm_low_iv = 0.025     # Low IV: sell closer ATM (2.5% OTM)
        self.otm_high_iv = 0.075    # High IV: sell further OTM (7.5% OTM)

        # Delta targets by IV regime (fallback when Greeks available)
        self.delta_low_iv = 0.40    # Low IV: sell closer ATM for premium
        self.delta_high_iv = 0.20   # High IV: sell further OTM for safety

        # IV percentile thresholds
        self.iv_pct_low = 30        # Below 30th pctile = low IV regime
        self.iv_pct_high = 70       # Above 70th pctile = high IV regime

        # Skew parameters
        self.skew_threshold = 0.15  # 15% skew = bearish signal
        self.skew_otm_adj = 0.025   # Add 2.5% OTM when skew high
        self.skew_delta_adj = 0.05  # Reduce delta by 5% when skew high

        # Position limits
        self.max_exposure_frac = 0.80
        self.min_iv_data = 20       # Need 20 days before trading

        # --- State tracking ---
        self._iv_history = []
        self._iv_percentile = 50.0
        self._skew = 0.0
        self._traded_today = False

        # Daily reset at market open
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.at(9, 31),
            self._reset_daily
        )

    def _reset_daily(self):
        """Reset daily trading flag at market open."""
        self._traded_today = False

    def _update_iv_metrics(self, chain):
        """
        Compute IV percentile and 25-delta skew from option chain.

        IV percentile: rank of current ATM IV within 252-day history.
        Skew: (25-delta put IV - 25-delta call IV) / ATM IV.
        """
        if chain is None:
            return

        spot = self.securities["SPY"].price
        best_dist = float('inf')
        atm_iv = None

        # Find ATM IV (contract with strike closest to spot)
        for c in chain:
            d = abs(c.strike - spot)
            if d < best_dist and c.implied_volatility > 0:
                best_dist = d
                atm_iv = c.implied_volatility

        # Update rolling IV history and percentile
        if atm_iv is not None:
            self._iv_history.append(atm_iv)
            if len(self._iv_history) > self.iv_lookback:
                self._iv_history = self._iv_history[-self.iv_lookback:]

            if len(self._iv_history) >= self.min_iv_data:
                sorted_ivs = sorted(self._iv_history)
                rank = sum(1 for iv in sorted_ivs if iv <= atm_iv)
                self._iv_percentile = rank / len(sorted_ivs) * 100.0

        # 25-delta skew measurement (only when Greeks available)
        put_25d = []
        call_25d = []

        for c in chain:
            if c.greeks is None:
                continue
            delta = abs(c.greeks.delta)
            if c.right == OptionRight.PUT and 0.20 <= delta <= 0.30:
                put_25d.append((abs(delta - 0.25), c.implied_volatility))
            elif c.right == OptionRight.CALL and 0.20 <= delta <= 0.30:
                call_25d.append((abs(delta - 0.25), c.implied_volatility))

        if put_25d and call_25d and atm_iv and atm_iv > 0:
            put_iv = min(put_25d, key=lambda x: x[0])[1]
            call_iv = min(call_25d, key=lambda x: x[0])[1]
            self._skew = (put_iv - call_iv) / atm_iv

    def _get_target_otm(self, right):
        """
        Determine target OTM percentage based on IV regime and skew.

        Higher IV -> more OTM (sell further from spot).
        High skew -> more OTM for puts (bearish protection).

        Returns:
            float: Target OTM percentage (0.01 to 0.12 range).
        """
        pct = self._iv_percentile

        if pct < self.iv_pct_low:
            otm = self.otm_low_iv
        elif pct > self.iv_pct_high:
            otm = self.otm_high_iv
        else:
            frac = ((pct - self.iv_pct_low) /
                    max(1, self.iv_pct_high - self.iv_pct_low))
            otm = self.otm_low_iv + frac * (self.otm_high_iv -
                                             self.otm_low_iv)

        # Skew adjustment: high skew = bearish, sell puts further OTM
        if right == OptionRight.PUT and self._skew > self.skew_threshold:
            otm += self.skew_otm_adj

        return max(0.01, min(0.12, otm))

    def _get_target_delta(self, right):
        """
        Determine target delta based on IV regime and skew.

        Higher IV -> lower delta (sell further OTM).
        High skew -> reduce put delta further (bearish protection).

        Returns:
            float: Target delta (0.10 to 0.45 range).
        """
        pct = self._iv_percentile

        if pct < self.iv_pct_low:
            delta = self.delta_low_iv
        elif pct > self.iv_pct_high:
            delta = self.delta_high_iv
        else:
            frac = ((pct - self.iv_pct_low) /
                    max(1, self.iv_pct_high - self.iv_pct_low))
            delta = self.delta_low_iv + frac * (self.delta_high_iv -
                                                 self.delta_low_iv)

        # Skew adjustment: high skew = bearish, sell puts further OTM
        if right == OptionRight.PUT and self._skew > self.skew_threshold:
            delta -= self.skew_delta_adj

        return max(0.10, min(0.45, delta))

    def _find_contract_by_delta(self, chain, right, target_delta):
        """
        Find option contract closest to target delta within DTE range.

        Scoring: delta distance (2x weight) + DTE distance from target.

        Returns:
            OptionContract or None.
        """
        candidates = []

        for c in chain:
            if c.right != right:
                continue
            dte = (c.expiry - self.time).days
            if dte < self.min_dte or dte > self.max_dte:
                continue
            if c.greeks is None or c.greeks.delta == 0:
                continue

            delta = abs(c.greeks.delta)
            delta_dist = abs(delta - target_delta)
            dte_dist = abs(dte - self.target_dte) / self.target_dte
            score = delta_dist * 2.0 + dte_dist
            candidates.append((score, c))

        if not candidates:
            return None

        candidates.sort(key=lambda x: x[0])
        return candidates[0][1]

    def _find_contract_by_otm(self, chain, right, target_otm):
        """
        Find option contract closest to target OTM within DTE range.

        Fallback when Greeks are not available in the option chain.

        Returns:
            OptionContract or None.
        """
        spot = self.securities["SPY"].price
        if right == OptionRight.PUT:
            target_price = spot * (1 - target_otm)
        else:
            target_price = spot * (1 + target_otm)

        candidates = []

        for c in chain:
            if c.right != right:
                continue
            dte = (c.expiry - self.time).days
            if dte < self.min_dte or dte > self.max_dte:
                continue

            # Filter by OTM direction
            if right == OptionRight.PUT and c.strike > target_price:
                continue
            if right == OptionRight.CALL and c.strike < target_price:
                continue

            otm_dist = abs(c.strike - target_price) / spot
            dte_dist = abs(dte - self.target_dte) / self.target_dte
            score = otm_dist * 2.0 + dte_dist
            candidates.append((score, c))

        if not candidates:
            return None

        candidates.sort(key=lambda x: x[0])
        return candidates[0][1]

    def _find_contract(self, chain, right):
        """
        Find contract using delta-based selection (preferred) or OTM fallback.

        Returns:
            tuple: (OptionContract or None, str method used)
        """
        target_delta = self._get_target_delta(right)
        contract = self._find_contract_by_delta(chain, right, target_delta)
        if contract is not None:
            return contract, "delta"

        # Fallback: OTM percentage when Greeks unavailable
        target_otm = self._get_target_otm(right)
        contract = self._find_contract_by_otm(chain, right, target_otm)
        if contract is not None:
            return contract, "otm"

        return None, "none"

    def _has_option_position(self):
        """Check if we have any open option positions."""
        for kvp in self.portfolio:
            holding = kvp.value
            if holding.type == SecurityType.OPTION and holding.invested:
                return True
        return False

    def _has_equity_position(self):
        """Check if we hold the underlying equity."""
        return self.securities["SPY"].holdings.quantity > 0

    def on_data(self, data):
        """Main trading logic: wheel with dynamic delta/OTM targeting."""
        if self._traded_today:
            return

        # Need sufficient IV data before trading
        if len(self._iv_history) < self.min_iv_data:
            # Still build IV history from chain data even before trading
            chain = data.option_chains.get(self._option_symbol)
            if chain is not None:
                self._update_iv_metrics(chain)
            return

        chain = data.option_chains.get(self._option_symbol)
        if chain is None:
            return

        # Update IV metrics for regime classification
        self._update_iv_metrics(chain)

        # Don't open new position if we already have an option
        if self._has_option_position():
            return

        # Wheel logic: no equity -> sell put, have equity -> sell call
        if not self._has_equity_position():
            self._sell_put(chain)
        else:
            self._sell_call(chain)

    def _sell_put(self, chain):
        """Sell cash-secured put with dynamic delta/OTM targeting."""
        contract, method = self._find_contract(chain, OptionRight.PUT)

        if contract is None:
            return

        # Risk check: ensure we have capital for assignment
        required = contract.strike * 100
        if required > self.portfolio.total_portfolio_value * self.max_exposure_frac:
            return

        qty = max(1, int(self.portfolio.cash / required))
        if qty > 0:
            self.market_order(contract.symbol, -qty)
            self._traded_today = True

            delta_info = ""
            if contract.greeks is not None and contract.greeks.delta != 0:
                delta_info = (f"delta_tgt={self._get_target_delta(OptionRight.PUT):.2f} "
                              f"delta_act={abs(contract.greeks.delta):.2f} ")

            self.log(f"SELL PUT [{method}]: {contract.symbol.value} "
                     f"{delta_info}"
                     f"strike={contract.strike:.2f} "
                     f"spot={self.securities['SPY'].price:.2f} "
                     f"IV_pct={self._iv_percentile:.0f} "
                     f"skew={self._skew:.2f}")

    def _sell_call(self, chain):
        """Sell covered call with dynamic delta/OTM targeting."""
        qty_shares = self.securities["SPY"].holdings.quantity
        if qty_shares < 100:
            return

        contract, method = self._find_contract(chain, OptionRight.CALL)

        if contract is None:
            return

        qty = qty_shares // 100
        if qty > 0:
            self.market_order(contract.symbol, -qty)
            self._traded_today = True

            delta_info = ""
            if contract.greeks is not None and contract.greeks.delta != 0:
                delta_info = (f"delta_tgt={self._get_target_delta(OptionRight.CALL):.2f} "
                              f"delta_act={abs(contract.greeks.delta):.2f} ")

            self.log(f"SELL CALL [{method}]: {contract.symbol.value} "
                     f"{delta_info}"
                     f"strike={contract.strike:.2f} "
                     f"spot={self.securities['SPY'].price:.2f} "
                     f"IV_pct={self._iv_percentile:.0f} "
                     f"skew={self._skew:.2f}")

    def on_end_of_algorithm(self):
        """Log final statistics."""
        self.log("=== Dynamic Options Wheel - Final Stats ===")
        self.log(f"IV Percentile: {self._iv_percentile:.1f}")
        self.log(f"Current Skew: {self._skew:.3f}")
        self.log(f"IV History: {len(self._iv_history)} data points")
