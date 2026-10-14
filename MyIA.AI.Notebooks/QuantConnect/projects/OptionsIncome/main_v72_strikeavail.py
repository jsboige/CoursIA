# region imports
from AlgorithmImports import *
from datetime import timedelta
from collections import deque
# endregion


class CoveredCallStrikeAvailStrategy(QCAlgorithm):
    """
    Covered Call Strategy v7.2 - gate strike-availability (2e facteur de l'article #18766)

    Voisinage :
      - OptionsIncome/main.py v7.0      : gate VIX global [15, 35].
      - OptionsIncome/main_v71_ivrank.py : gate IV-rank par sous-jacent -> NO-BEATS (#15801).
      - Option-Wheel/main.py            : gate VIX > 20 = skip puts.
      - Article QC #18766               : gate a deux facteurs (IV-rank + strike-availability)
                                          k-means, liquide quand les DEUX sont "high".

    Ce que ce fichier teste (le facteur que #15801 n'a pas porte) :
      le facteur strike-availability de l'article = (nombre de strikes distincts
      disponibles / prix du sous-jacent), avec son rate-of-change en entree du
      clustering. L'article le clusterise en 3 classes par k-means ; les centroides
      ne sont PAS publies numeriquement, donc l'equivalent parametre-free retenu ici
      est le rang percentile du RoC dans sa distribution trailing 252 j (preterciles
      0.33/0.66 = memes bornes que celles utilisees pour v7.1). On n'ecrit que si
      label < 0.66 (pas de bande haute), symetrique du gate IV-rank de v7.1.

      L'article sort quand les DEUX facteurs sont hauts ; une variante mono-facteur
      ne peut pas porter cette regle de sortie conjointe -> ce fichier n'ajoute
      AUCUN force-close (la regle de sortie de l'article n'est pas applicable).

    Portabilite du facteur — reserve explicite :
      L'article mesure la disponibilite sur l'univers NON borne de SPX
      (`strikes(-1, 1)`), ou la densite de listing varie avec les conditions de
      marche. Ici l'univers est celui de la famille, borne (-5, +15 strikes), donc
      le compte de strikes varie surtout avec le NOMBRE D'EXPIRATIONS dans la
      fenetre DTE (cycle hebdomadaire), pas avec la densite de listing du marche.
      Le test mesure donc « le facteur tel qu'il peut exister dans ce regime de
      souscription », pas « le facteur de l'article sur SPX ». Le compte et le RoC
      sont logges au rapport final pour que la degenerescence eventuelle soit
      mesuree, pas affirmee.

    Tout le reste est identique a v7.1/v7.0 pour comparabilite : delta 0.20,
    days_to_roll 10, profit_target 0.50, defensive_drop 0.03, warm-up 30 j,
    fenetre 2015-01-01 -> 2024-12-31, capital 100 000.

    SOTA verdict : SOTA-OK — le backtest a tourne sur le moteur reel QC Cloud
    (projet 36473886, backtest 92125e3965f2852fadb506e467b3ea12, LEAN master
    v18124, fenetre 2015-01-01 -> 2024-12-31, 546,8 M de points de donnees) et
    le couple mesure contre la baseline v7.0 et la variante v7.1 (#15801) est
    publie dans le body de la PR et le notebook de recherche
    (research/research_iv_rank_strike_clusters.ipynb). Verdict mesure : NO BEATS
    (Sharpe 0.264 vs 0.281 baseline ; CAGR 5.400 % vs 5.536 % ; MaxDD 17.9 %
    vs 17.4 %). Aucune sortie n'est affirmee qui n'ait ete mesuree.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        equity = self.add_equity("SPY", Resolution.MINUTE)
        self.underlying = equity.symbol

        # VIX conserve comme fallback tant que l'historique de disponibilite est trop court.
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        option = self.add_option("SPY", Resolution.MINUTE)
        self.option_symbol = option.symbol

        option.set_filter(
            min_strike=-5,
            max_strike=15,
            min_expiry=timedelta(days=20),
            max_expiry=timedelta(days=45)
        )

        # Parametres strategie — identiques a v7.0/v7.1.
        self.target_delta = 0.20
        self.days_to_roll = 10
        self.num_contracts = 2
        self.shares_per_contract = 100
        self.profit_target = 0.50
        self.defensive_drop = 0.03

        # Gate strike-availability.
        # Fenetre du rate-of-change : 21 seances (1 mois de trading, choix documente ;
        # l'article ne publie pas la fenetre exacte de son RoC).
        self.avail_roc_lookback = 21
        # Seuil du label : pretercile haut (memes bornes 0.33/0.66 que v7.1).
        self.avail_label_max = 0.66
        # Fenetre de la distribution du label : 252 seances (1 an, comme v7.1).
        self.avail_window_days = 252

        self.vix_min = 15
        self.vix_max = 35

        # Historiques : disponibilite brute (strikes distincts / spot) et RoC.
        self.availability_history = deque(maxlen=self.avail_window_days)
        self.avail_roc_history = deque(maxlen=self.avail_window_days)
        self.current_avail_label = None  # None tant que le label n'est pas calculable

        # Diagnostic : echantillons manquants et sessions en repli VIX.
        self.avail_starve_days = 0
        self.avail_starve_warned = False
        self.fallback_vix_sessions = 0

        # Statistiques de degenerescence (rapport final).
        self.avail_values_seen = []
        self.roc_values_seen = []

        # Warm-up explicite (consequence du gate sur historique).
        self.set_warm_up(timedelta(days=30))

        # Etat position.
        self.current_call = None
        self.call_entry_price = 0.0
        self.premium_collected = 0
        self.trades_count = 0
        self.profit_closes = 0
        self.defensive_closes = 0
        self.skipped_avail = 0
        self.skipped_no_avail = 0
        self.prior_spy_close = None

        self.schedule.on(
            self.date_rules.every_day(self.underlying),
            self.time_rules.after_market_open(self.underlying, 30),
            self._manage_position
        )
        # Mise a jour quotidienne de la disponibilite des strikes.
        self.schedule.on(
            self.date_rules.every_day(self.underlying),
            self.time_rules.after_market_open(self.underlying, 60),
            self._update_availability
        )
        self.set_benchmark("SPY")

    def on_end_of_day(self, symbol):
        if symbol == self.underlying:
            self.prior_spy_close = self.securities[self.underlying].price

    def on_data(self, data):
        pass

    def _update_availability(self):
        """Compte les strikes distincts du chain / spot, met a jour le label percentile."""
        if self.is_warming_up:
            return
        if self.current_avail_label is None:
            self.fallback_vix_sessions += 1

        chain = self.current_slice.option_chains.get(self.option_symbol, None)
        if not chain:
            self.avail_starve_days += 1
            return
        underlying_price = self.securities[self.underlying].price
        if underlying_price <= 0:
            return

        distinct_strikes = len({c.strike for c in chain})
        if distinct_strikes == 0:
            self.avail_starve_days += 1
            return

        availability = distinct_strikes / underlying_price
        self.availability_history.append(availability)
        self.avail_values_seen.append(availability)

        # RoC sur la fenetre parametree.
        if len(self.availability_history) > self.avail_roc_lookback:
            past = self.availability_history[-(self.avail_roc_lookback + 1)]
            if past > 0:
                roc = availability / past - 1.0
                self.avail_roc_history.append(roc)
                self.roc_values_seen.append(roc)

                # Label = rang percentile du RoC courant dans la distribution trailing.
                if len(self.avail_roc_history) >= 60:
                    below = sum(1 for r in self.avail_roc_history if r <= roc)
                    self.current_avail_label = below / len(self.avail_roc_history)

        if (not self.avail_starve_warned
                and self.current_avail_label is None
                and self.avail_starve_days >= 60):
            self.avail_starve_warned = True
            self.log(
                f"AVAILABILITY STARVED: aucun echantillon de strikes depuis "
                f"{self.avail_starve_days} jours de trading — le gate VIX "
                f"[{self.vix_min}, {self.vix_max}] assure le repli pour tout le run."
            )

    def _availability_gate(self):
        """Retourne True si on peut ecrire (gate pass), False sinon."""
        if self.current_avail_label is None:
            vix_price = self.securities[self.vix].price
            if vix_price <= 0:
                return False
            if vix_price < self.vix_min or vix_price > self.vix_max:
                self.skipped_no_avail += 1
                return False
            return True
        # Gate strike-availability : bande haute du label = pas d'ecriture.
        if self.current_avail_label >= self.avail_label_max:
            self.skipped_avail += 1
            return False
        return True

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
        if not self._availability_gate():
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
            f"avail-label={self.current_avail_label if self.current_avail_label is None else f'{self.current_avail_label:.2f}'}"
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

        def stats(values):
            if not values:
                return "n=0"
            n = len(values)
            mean = sum(values) / n
            lo, hi = min(values), max(values)
            var = sum((v - mean) ** 2 for v in values) / n
            std = var ** 0.5
            return f"n={n}, mean={mean:.5f}, std={std:.5f}, min={lo:.5f}, max={hi:.5f}"

        avail_label = (
            f"avail-label_at_end={self.current_avail_label:.3f}"
            if self.current_avail_label is not None
            else "avail-label=N/A (warm-up)"
        )
        self.log(
            f"CC v7.2-strikeavail: Final=${final:,.2f}, "
            f"Return={(final-100000)/100000:.2%}, "
            f"Premium=${self.premium_collected:,.2f}, "
            f"Trades={self.trades_count}, "
            f"ProfitCloses={self.profit_closes}, "
            f"DefensiveCloses={self.defensive_closes}, "
            f"SkippedByAvail={self.skipped_avail}, "
            f"SkippedNoAvail={self.skipped_no_avail}, "
            f"FallbackVIXSessions={self.fallback_vix_sessions}, "
            f"{avail_label}, "
            f"Availability[{stats(self.avail_values_seen)}], "
            f"RoC[{stats(self.roc_values_seen)}]"
        )