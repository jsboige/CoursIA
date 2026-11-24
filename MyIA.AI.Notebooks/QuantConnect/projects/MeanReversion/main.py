# region imports
from AlgorithmImports import *
# endregion


class ShortTermMeanReversion(QCAlgorithm):
    """
    Sector ETF Mean Reversion Strategy v5.2 (BEST)
    ==========================================
    v4.2: Sharpe 0.413, CAGR 8.76%, MaxDD 26.4%
    v5.0: Sharpe 0.598, CAGR 6.07%, MaxDD 4.7% (RS > SPY, too few trades)
    v5.1: Sharpe 0.596, CAGR 7.73%, MaxDD 8.5% (relaxed RS -0.10)
    v5.2: Sharpe 0.810, CAGR 10.04%, MaxDD 7.5% (RSI65/stop10 BEST)
    v5.3: Sharpe 0.677, CAGR 8.91%, MaxDD 11.1% (hold20 - too long)
    v5.4: Sharpe 0.743, CAGR 7.45%, MaxDD 4.3% (RSI35 - fewer trades)

    RSI(14) oversold entries on 11 sector ETFs, filtered by relative strength.
    Only enter oversold sectors with 3m return >= SPY return - 10%.
    Half weight (12.5%) in bear market (SPY < SMA200), full weight (25%) in bull.
    Exit: RSI > 65, 15-day holding period, 10% stop-loss.

    Ref: research.ipynb, Jegadeesh (1990), De Bondt & Thaler (1985)
    """

    def initialize(self):
        # Protocole #23199 : `mode` choisit la strategie (defaut, decision
        # inchangee), une reference detenue (spy : SPY 100 % ; 6040 : SPY 60 %
        # / BND 40 %) ou le diagnostic ew11 (les ETF sectoriels a poids egal).
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "ew11"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} "
                "(strategy | spy | 6040 | ew11)"
            )
        start = self.get_parameter("start_date", "2015-01-01")
        end = self.get_parameter("end_date", "2024-12-31")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

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

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        self.rsi_oversold = 40
        self.rsi_exit = 65
        self.num_positions = 4
        self.holding_period = 15
        self.stop_loss_pct = 0.10
        self.bull_weight = 0.25
        self.bear_weight = 0.125
        self.rs_lookback = 63  # 3-month relative strength

        self.entry_days = {}
        self.entry_prices = {}
        self.day_count = 0
        self._reentries = 0

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

    def _get_3m_return(self, symbol):
        # Fenetre double (#20286) : sur une demi-seance, history() rend moins de
        # barres que demandees et le retour 3 mois valait 0.0 pour tous les titres.
        # On demande le double ; iloc[-1] et iloc[-rs_lookback] sont inchanges.
        hist = self.history(symbol, 2 * (self.rs_lookback + 5), Resolution.DAILY)
        # Garde a rs_lookback barres, pas 0,8 x rs_lookback : un ETF jeune (XLC en 2018,
        # XLRE en 2015) a entre 51 et 62 barres, passait l'ancienne garde et sortait de
        # l'index sur iloc[-rs_lookback] (#20346). Historique court : 0.0, comme avant.
        if len(hist) < self.rs_lookback:
            return 0.0
        return float(hist["close"].iloc[-1] / hist["close"].iloc[-self.rs_lookback] - 1)

    def _daily_scan(self):
        if self.is_warming_up:
            return

        self.day_count += 1

        bear_market = False
        if self.spy_sma.is_ready:
            spy_price = self.securities[self.spy].price
            bear_market = spy_price < self.spy_sma.current.value

        position_weight = self.bear_weight if bear_market else self.bull_weight

        # Check exits: stop-loss, RSI exit, holding period
        to_exit = []
        for etf in list(self.entry_days.keys()):
            days_held = self.day_count - self.entry_days[etf]
            rsi_val = self.rsi_indicators[etf].current.value
            current_price = self.securities[self.symbols[etf]].price

            if etf in self.entry_prices:
                drawdown = (current_price - self.entry_prices[etf]) / self.entry_prices[etf]
                if drawdown < -self.stop_loss_pct:
                    to_exit.append(etf)
                    self.log(f"STOP-LOSS: {etf}, drawdown={drawdown:.1%}")
                    continue

            if days_held >= self.holding_period or rsi_val > self.rsi_exit:
                to_exit.append(etf)

        for etf in to_exit:
            self.entry_days.pop(etf, None)
            self.entry_prices.pop(etf, None)

        spy_ret_3m = self._get_3m_return(self.spy)

        candidates = []
        for etf in self.sector_etfs:
            if etf in self.entry_days:
                continue
            rsi = self.rsi_indicators[etf]
            if not rsi.is_ready:
                continue
            rsi_val = rsi.current.value
            if rsi_val < self.rsi_oversold:
                etf_ret_3m = self._get_3m_return(self.symbols[etf])
                if etf_ret_3m >= spy_ret_3m - 0.10:
                    candidates.append((etf, rsi_val))

        candidates.sort(key=lambda x: x[1])

        available = self.num_positions - len(self.entry_days)
        selected = candidates[:available]

        # Les sorties sont liquidees une fois les entrees connues (#23199). En
        # resolution journaliere, liquidate() puis set_holdings() sur le meme ETF
        # se remplissent tous deux a la cloture, et set_holdings, calcule contre
        # la position pas encore vendue, n'envoie que l'ecart : la ligne finissait
        # a quelques parts, ou courte. Un ETF re-selectionne le jour de sa sortie
        # ne recoit donc que set_holdings(symbol, w), qui le porte a w.
        reentered = {etf for etf, _ in selected} & set(to_exit)
        self._reentries += len(reentered)
        for etf in to_exit:
            if etf not in reentered:
                self.liquidate(self.symbols[etf])

        for etf, rsi_val in selected:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, position_weight)
            self.entry_days[etf] = self.day_count
            self.entry_prices[etf] = self.securities[symbol].price
            regime = "BEAR" if bear_market else "BULL"
            self.log(f"ENTER: {etf}, RSI={rsi_val:.1f}, {regime}, wt={position_weight:.3f}")

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}",
                  self.portfolio.total_portfolio_value)
        self._closes += 1

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._mode == "spy":
            targets = {self.spy: 1.0}
        elif self._mode == "6040":
            targets = {self.spy: 0.6, self.bnd: 0.4}
        else:
            # ew11 : les ETF sectoriels qui cotent deja (XLRE depuis 2015-10,
            # XLC depuis 2018-06), a poids egal.
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
        final = self.portfolio.total_portfolio_value
        self.log(f"MEAN REV v5.2: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
