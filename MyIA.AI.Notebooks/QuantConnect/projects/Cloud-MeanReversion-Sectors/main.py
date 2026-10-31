# region imports
from AlgorithmImports import *
# endregion


class CloudMeanReversionSectors(QCAlgorithm):
    """
    Mean Reversion on Sector ETFs — Cloud-04

    Three variants controlled by 'version' parameter:
    - v1: Pure RSI mean reversion (no regime filter)
    - v2: RSI + SMA200 regime filter (bear = exit all)
    - v3: RSI + SMA200 + stop-loss + tighter RSI

    Universe: 11 GICS sector ETFs.
    Signal: RSI(14) < oversold threshold -> buy, exit when RSI > exit threshold.
    """

    def initialize(self):
        # Protocole #23257 : `mode` choisit la strategie (defaut, decision
        # inchangee), une reference detenue (spy : SPY 100 % ; 6040 : SPY 60 %
        # / BND 40 %) ou le diagnostic ew11 (les ETF sectoriels a poids egal).
        # `fix` : on (defaut, correctif #23257) ou off (code d'origine).
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "ew11"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} "
                "(strategy | spy | 6040 | ew11)"
            )
        self._fix = self.get_parameter("fix", "on").lower()
        if self._fix not in ("on", "off"):
            raise ValueError(f"unknown fix parameter: {self._fix} (on | off)")
        # Aligned baseline period 2018-2025 (#1630). Original start was 2014;
        # standardized to 2018-01-01 for cross-strategy comparison.
        start = self.get_parameter("start_date", "2018-01-01")
        end = self.get_parameter("end_date", "2025-01-01")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        version = self.get_parameter("version", "v1")

        self.sector_etfs = [
            "XLK", "XLF", "XLE", "XLV", "XLI",
            "XLY", "XLP", "XLU", "XLB", "XLRE", "XLC"
        ]
        self.symbols = {}
        self.rsi_indicators = {}

        for etf in self.sector_etfs:
            equity = self.add_equity(etf, Resolution.DAILY)
            self.symbols[etf] = equity.symbol
            self.rsi_indicators[etf] = self.rsi(equity.symbol, 14)

        # SPY for regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        if version == "v1":
            self.rsi_oversold = 35
            self.rsi_exit = 55
            self.num_positions = 3
            self.holding_period = 20
            self.stop_loss_pct = 999  # no stop loss
            self.use_regime_filter = False
        elif version == "v2":
            self.rsi_oversold = 40
            self.rsi_exit = 60
            self.num_positions = 4
            self.holding_period = 15
            self.stop_loss_pct = 999  # no stop loss
            self.use_regime_filter = True
        elif version == "v3":
            self.rsi_oversold = 40
            self.rsi_exit = 60
            self.num_positions = 4
            self.holding_period = 15
            self.stop_loss_pct = 0.08
            self.use_regime_filter = True

        self.position_weight = 1.0 / self.num_positions
        self.entry_days = {}
        self.entry_prices = {}
        self.day_count = 0

        # Statistiques d'execution (#23257), lues a l'ouverture.
        self._reentries = 0
        self._short_days = 0
        self._max_gross = 0.0

        # BND n'est pas dans l'univers de la strategie : seul le mode 6040 l'abonne.
        self.bnd = (self.add_equity("BND", Resolution.DAILY).symbol
                    if self._mode == "6040" else None)

        if self._mode == "strategy":
            self.schedule.on(
                self.date_rules.every_day("SPY"),
                self.time_rules.after_market_open("SPY", 30),
                self._daily_scan
            )
        else:
            # References : premier jour de bourse du mois, meme heure que le scan.
            self.schedule.on(
                self.date_rules.month_start("SPY"),
                self.time_rules.after_market_open("SPY", 30),
                self._rebalance_reference
            )

        # Trace `shadow` (#18923) : valeur du portefeuille a l'ouverture de
        # chaque seance de SPY, hors prechauffage, dans e0..e4.
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 0),
            self._trace
        )

        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

    def _daily_scan(self):
        if self.is_warming_up:
            return

        self.day_count += 1

        # Regime filter
        if self.use_regime_filter and self.spy_sma.is_ready:
            spy_price = self.securities[self.spy].price
            if spy_price < self.spy_sma.current.value:
                if self.portfolio.invested:
                    self.liquidate()
                    self.entry_days.clear()
                    self.entry_prices.clear()
                return

        # Check exits
        to_exit = []
        stopped = set()
        for etf in list(self.entry_days.keys()):
            days_held = self.day_count - self.entry_days[etf]
            rsi_val = self.rsi_indicators[etf].current.value
            current_price = self.securities[self.symbols[etf]].price

            if self.stop_loss_pct < 1 and etf in self.entry_prices:
                dd = (current_price - self.entry_prices[etf]) / self.entry_prices[etf]
                if dd < -self.stop_loss_pct:
                    stopped.add(etf)
                    to_exit.append(etf)
                    continue

            if days_held >= self.holding_period or rsi_val > self.rsi_exit:
                to_exit.append(etf)

        for etf in to_exit:
            if self._fix == "off":
                self.liquidate(self.symbols[etf])
            self.entry_days.pop(etf, None)
            self.entry_prices.pop(etf, None)

        # Entries
        candidates = []
        for etf in self.sector_etfs:
            if etf in self.entry_days:
                continue
            # Une sortie sur stop doit solder la ligne, sans rachat le meme jour.
            if self._fix == "on" and etf in stopped:
                continue
            rsi = self.rsi_indicators[etf]
            if not rsi.is_ready:
                continue
            rsi_val = rsi.current.value
            if rsi_val < self.rsi_oversold:
                candidates.append((etf, rsi_val))

        candidates.sort(key=lambda x: x[1])

        available = self.num_positions - len(self.entry_days)
        selected = candidates[:available]

        # Correctif #23257 : les sorties sont liquidees une fois les entrees
        # connues. En resolution journaliere, liquidate() puis set_holdings() sur
        # le meme ETF se remplissent tous deux a la cloture, et set_holdings,
        # calcule contre la position pas encore vendue, n'envoie que l'ecart : la
        # ligne finissait a quelques parts, ou courte. Un ETF re-selectionne le
        # jour de sa sortie ne recoit donc que set_holdings(symbol, w).
        reentered = {etf for etf, _ in selected} & set(to_exit)
        self._reentries += len(reentered)
        if self._fix == "on":
            for etf in to_exit:
                if etf not in reentered:
                    self.liquidate(self.symbols[etf])

        for etf, rsi_val in selected:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, self.position_weight)
            self.entry_days[etf] = self.day_count
            self.entry_prices[etf] = self.securities[symbol].price

    def _trace(self):
        if self.is_warming_up:
            return
        tpv = self.portfolio.total_portfolio_value
        self.plot("shadow", f"e{self._closes % 5}", tpv)
        self._closes += 1
        gross = sum(abs(h.holdings_value) for h in self.portfolio.values())
        if tpv > 0:
            self._max_gross = max(self._max_gross, gross / tpv)
        if any(h.quantity < 0 for h in self.portfolio.values()):
            self._short_days += 1

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._mode == "spy":
            targets = {self.spy: 1.0}
        elif self._mode == "6040":
            targets = {self.spy: 0.6, self.bnd: 0.4}
        else:
            # ew11 : les ETF sectoriels qui cotent deja (XLC depuis 2018-06),
            # a poids egal.
            live = [s for s in self.symbols.values()
                    if self.securities[s].has_data and self.securities[s].price > 0]
            targets = {s: 1.0 / len(live) for s in live}
        # Un seul set_holdings multi-cibles, ordres en attente retires d'abord :
        # les quantites se calculent sur la position finale.
        self.transactions.cancel_open_orders()
        self.set_holdings([PortfolioTarget(s, w) for s, w in targets.items()],
                          liquidate_existing_holdings=True)

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("reentries", str(self._reentries))
        self.set_runtime_statistic("short_days", str(self._short_days))
        self.set_runtime_statistic("max_gross", f"{self._max_gross:.3f}")
        final = self.portfolio.total_portfolio_value
        self.log(f"MEAN REV: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
