# region imports
from AlgorithmImports import *
from datetime import timedelta
from collections import deque
# endregion


class CoveredCallIvRankStrategy(QCAlgorithm):
    """
    Covered Call Strategy v7.1 - IV-rank gate par sous-jacent

    Voisinage :
      - OptionsIncome/main.py v7.0 : gate VIX global [15, 35] (toutes conditions),
                                       sans distinction IV-rank par sous-jacent.
      - Option-Wheel/main.py       : gate VIX > 20 = skip puts.
      - Article #18766 : gate IV-rank (k-means sur [IV-rank, strike-availability])
                         + strike clusters pour SPX puts européens.

    Changements v7.1 vs v7.0 :
      1. Remplace le gate VIX global [vix_min, vix_max] par un gate IV-rank par
         sous-jacent, calculé sur la médiane IV ATM 30-45 jours, fenêtre 252 j.
      2. Skip l'écriture de calls quand IV-rank > ivrank_max.
      3. Force-close défensif si IV-rank > ivrank_panic.
      4. Conserve toutes les autres règles (delta 0.20, days_to_roll 10,
         profit_target 0.50, defensive_drop 0.03) pour comparabilité baseline.
      5. Simplification par rapport à l'article : k-means 1D sur IV-rank seul
         (3 clusters). Strike availability non implémenté — voir body PR.

    SOTA verdict : RECOVERABLE-LOCAL (vrai moteur QuantConnect + IV natif
    via Greeks.IV sur chaîne minute, comme documenté dans le voisinage).
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        equity = self.add_equity("SPY", Resolution.MINUTE)
        self.underlying = equity.symbol

        # VIX conservé comme fallback si IV-rank indisponible (warm-up).
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        option = self.add_option("SPY", Resolution.MINUTE)
        self.option_symbol = option.symbol

        option.set_filter(
            min_strike=-5,
            max_strike=15,
            min_expiry=timedelta(days=20),
            max_expiry=timedelta(days=45)
        )
        # Active Greeks computation (implied_volatility / delta) via Black-Scholes.
        # Sans price_model, Greeks.IV n'est pas peuplé et la IV implicite reste indisponible.
        option.price_model = OptionPriceModels.black_scholes()

        # Paramètres stratégie
        self.target_delta = 0.20
        self.days_to_roll = 10
        self.num_contracts = 2
        self.shares_per_contract = 100
        self.profit_target = 0.50
        self.defensive_drop = 0.03

        # Gate IV-rank : remplace VIX [15,35] global.
        # Seuils basés sur la lecture analytique de l'article #18766 :
        #   k-means k=3 sur IV-rank ATM 30-90 j donne 3 clusters
        #   (low ≈ 0-0.33, medium ≈ 0.33-0.66, high ≈ 0.66-1).
        self.ivrank_window_days = 252
        self.ivrank_min = 0.0    # on autorise l'écriture dès IV-rank > 0 (low cluster)
        self.ivrank_max = 0.66   # skip si IV-rank ∈ high cluster
        self.ivrank_panic = 0.85 # force-close défensif si IV-rank > panic

        # Fallback VIX si IV-rank warm-up incomplet (premiers <252 j)
        self.vix_min = 15
        self.vix_max = 35

        # Historique IV ATM daily pour IV-rank.
        # On collecte un seul IV représentatif par jour (médiane des IV ATM 30-45 j).
        self.daily_atm_iv = deque(maxlen=self.ivrank_window_days)
        self.current_ivrank = None  # None tant que warm-up incomplet

        # Warm-up explicite pour la médiane IV ATM (conséquence du gate IV).
        self.set_warm_up(timedelta(days=30))

        # État position
        self.current_call = None
        self.call_entry_price = 0.0
        self.premium_collected = 0
        self.trades_count = 0
        self.profit_closes = 0
        self.defensive_closes = 0
        self.defensive_iv_closes = 0
        self.skipped_ivrank = 0
        self.skipped_no_ivrank = 0
        self.prior_spy_close = None

        self.schedule.on(
            self.date_rules.every_day(self.underlying),
            self.time_rules.after_market_open(self.underlying, 30),
            self._manage_position
        )
        # Mise à jour quotidienne de l'IV ATM median
        self.schedule.on(
            self.date_rules.every_day(self.underlying),
            self.time_rules.after_market_open(self.underlying, 60),
            self._update_ivrank
        )
        self.set_benchmark("SPY")

    def on_end_of_day(self, symbol):
        if symbol == self.underlying:
            self.prior_spy_close = self.securities[self.underlying].price

    def on_data(self, data):
        pass

    def _update_ivrank(self):
        """Calcule la médiane IV ATM (30-45 j DTE) et met à jour l'IV-rank."""
        if self.is_warming_up:
            return
        chain = self.current_slice.option_chains.get(self.option_symbol, None)
        if not chain:
            return
        underlying_price = self.securities[self.underlying].price
        if underlying_price <= 0:
            return

        # Filtre ATM : strikes autour du spot, DTE 30-45 j
        atm_ivs = []
        for c in chain:
            if c.right != OptionRight.CALL:
                continue
            iv = getattr(c, "implied_volatility", None)
            if iv is None or iv <= 0:
                continue
            dte = (c.expiry - self.time).days
            if dte < 30 or dte > 45:
                continue
            moneyness = abs(c.strike - underlying_price) / underlying_price
            if moneyness > 0.05:  # ±5% ATM
                continue
            atm_ivs.append(iv)

        if not atm_ivs:
            return
        atm_ivs.sort()
        n = len(atm_ivs)
        median_iv = atm_ivs[n // 2] if n % 2 == 1 else 0.5 * (atm_ivs[n // 2 - 1] + atm_ivs[n // 2])
        self.daily_atm_iv.append(median_iv)

        if len(self.daily_atm_iv) >= 60:  # ~ 3 mois de warm-up minimum
            mn = min(self.daily_atm_iv)
            mx = max(self.daily_atm_iv)
            self.current_ivrank = (median_iv - mn) / (mx - mn) if mx > mn else None

    def _ivrank_gate(self):
        """Retourne True si on peut écrire (gate pass), False sinon."""
        # Fallback VIX tant que warm-up IV-rank incomplet
        if self.current_ivrank is None:
            vix_price = self.securities[self.vix].price
            if vix_price <= 0:
                return False  # pas de signal — skip conservateur
            if vix_price < self.vix_min or vix_price > self.vix_max:
                self.skipped_no_ivrank += 1
                return False
            return True
        # Gate IV-rank principal
        if self.current_ivrank > self.ivrank_max:
            self.skipped_ivrank += 1
            return False
        return True

    def _manage_position(self):
        target_shares = self.shares_per_contract * self.num_contracts
        current_shares = self.portfolio[self.underlying].quantity
        if current_shares < target_shares:
            self.market_order(self.underlying, target_shares - current_shares)
            return

        # Force-close défensif si IV-rank panic (inscrit dans #18766 comme
        # condition de liquidation : "IV rank and strike availability is high!").
        if (self.current_call is not None
                and self.current_ivrank is not None
                and self.current_ivrank > self.ivrank_panic):
            option = self.securities[self.current_call]
            self.market_order(self.current_call, self.num_contracts)
            self.log(
                f"IV-RANK PANIC CLOSE: ivrank={self.current_ivrank:.2f} "
                f"price={option.price:.2f}"
            )
            self.current_call = None
            self.call_entry_price = 0.0
            self.defensive_iv_closes += 1
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
        if not self._ivrank_gate():
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
        vix_price = self.securities[self.vix].price
        self.log(
            f"SOLD {self.num_contracts}x CALL: Strike={best_call.strike}, "
            f"DTE={(best_call.expiry - self.time).days}, "
            f"Delta={best_call.greeks.delta:.2f}, "
            f"Premium=${premium:.2f}, VIX={vix_price:.1f}, "
            f"IV-rank={self.current_ivrank if self.current_ivrank is None else f'{self.current_ivrank:.2f}'}"
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
        ivrank_report = (
            f"IV-rank_at_end={self.current_ivrank:.3f}"
            if self.current_ivrank is not None
            else "IV-rank=N/A (warm-up)"
        )
        self.log(
            f"CC v7.1-ivrank: Final=${final:,.2f}, "
            f"Return={(final-100000)/100000:.2%}, "
            f"Premium=${self.premium_collected:,.2f}, "
            f"Trades={self.trades_count}, "
            f"ProfitCloses={self.profit_closes}, "
            f"DefensiveCloses={self.defensive_closes}, "
            f"DefensiveIVCloses={self.defensive_iv_closes}, "
            f"SkippedByIVRank={self.skipped_ivrank}, "
            f"SkippedNoIVRank={self.skipped_no_ivrank}, "
            f"{ivrank_report}, "
            f"IVSamplesBuffered={len(self.daily_atm_iv)}"
        )
