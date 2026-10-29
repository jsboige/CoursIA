# region imports
from AlgorithmImports import *
from datetime import datetime
# endregion


class GlobalMacroRegime(QCAlgorithm):
    """
    Global Macro Regime v3 BEST: Rank-based Risk Parity + Regime Switch
    =====================================================================
    v1: Sharpe 0.499, CAGR 9.87%, MaxDD 18.0% (equal defensive)
    v2: Sharpe 0.583, CAGR 11.55%, MaxDD 21.6% (RP defensive + 6m filter)
    v3: Sharpe 0.607, CAGR 11.62%, MaxDD 23.6% (rank * inv_vol in risky) BEST
    v4: Sharpe 0.603, CAGR 11.53%, MaxDD 23.5% (+ vol targeting - no improvement)
    v4-v6: no improvement

    Reference: Bridgewater Risk Parity, Antonacci (2014)
    """

    RISKY_TICKERS = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
    DEFENSIVE_TICKERS = ["BND", "TLT", "GLD"]
    ALL_TICKERS = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC", "BND"]
    MOM_12M = 252
    MOM_6M = 126
    MIN_TRENDING = 2

    def initialize(self):
        # Mesure contre références détenues (#22869, protocole de #21594) :
        # `strategy` (défaut) garde la décision du code ; `spy` (SPY détenu) et
        # `6040` (SPY 60 %, BND 40 %) sont les deux références du verdict ;
        # `ew7` (les 7 ETFs à poids égal) et `noregime` (la même règle, toujours
        # dans la branche haussière) sont deux diagnostics.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "ew7", "noregime"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} (strategy | spy | 6040 | ew7 | noregime)"
            )

        # Aligned baseline period 2018-2025 (#1630). Original start was 2015;
        # standardized to 2018-01-01 for cross-strategy comparison.
        # Dates paramétrables (backtests QC Cloud) ; les défauts sont les dates codées.
        start = self.get_parameter("start_date", "2018-01-01")
        end = self.get_parameter("end_date", "2025-01-01")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100_000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.set_benchmark("SPY")

        self.symbols = {}
        self.sma_ind = {}
        self.std_ind = {}
        for ticker in self.RISKY_TICKERS:
            security = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = security.symbol
            self.sma_ind[ticker] = self.sma(security.symbol, 200, Resolution.DAILY)
            self.std_ind[ticker] = self.STD(security.symbol, 60, Resolution.DAILY)

        for ticker in ["BND"]:
            if ticker not in self.symbols:
                security = self.add_equity(ticker, Resolution.DAILY)
                self.symbols[ticker] = security.symbol

        self.spy_sym = self.symbols["SPY"]
        self.spy_sma = self.sma(self.spy_sym, 200, Resolution.DAILY)

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance,
        )

        self.set_warm_up(timedelta(days=300))

        # Références : aucune décision de stratégie (`rebalance` sort aussitôt),
        # rééquilibrage au début de chaque mois, une minute après l'ouverture.
        # Les 7 ETFs, BND compris, sont déjà abonnés : aucun mode n'en ajoute.
        if self._mode in ("spy", "6040", "ew7"):
            self.schedule.on(
                self.date_rules.month_start(self.spy_sym),
                self.time_rules.after_market_open(self.spy_sym, 1),
                self._rebalance_reference,
            )

        # Trace journalière `shadow` (contrat #18923) : valeur du portefeuille à
        # l'ouverture de chaque séance de SPY, hors préchauffage, répartie sur
        # e0..e4. Tous les modes la prennent au même instant.
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day(self.spy_sym),
            self.time_rules.after_market_open(self.spy_sym, 0),
            self._trace,
        )

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._mode == "spy":
            self.set_holdings([PortfolioTarget(self.spy_sym, 1.0)])
        elif self._mode == "6040":
            self.set_holdings([
                PortfolioTarget(self.spy_sym, 0.6),
                PortfolioTarget(self.symbols["BND"], 0.4),
            ])
        else:
            weight = 1.0 / len(self.ALL_TICKERS)
            self.set_holdings([PortfolioTarget(self.symbols[ticker], weight)
                               for ticker in self.ALL_TICKERS])

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def _is_bull_regime(self):
        if not self.spy_sma.is_ready:
            return True
        spy_price = self.securities[self.spy_sym].close
        if spy_price <= self.spy_sma.current.value:
            return False
        hist = self.history(self.spy_sym, self.MOM_6M + 5, Resolution.DAILY)
        if len(hist) < self.MOM_6M * 0.8:
            return True
        ret_6m = hist["close"].iloc[-1] / hist["close"].iloc[-self.MOM_6M] - 1
        return ret_6m > 0

    def _get_inv_vol(self, ticker):
        sym = self.symbols[ticker]
        std_ind = self.std_ind.get(ticker)
        if std_ind and std_ind.is_ready and std_ind.current.value > 0:
            price = self.securities[sym].price
            if price > 0:
                return price / std_ind.current.value
        return 1.0

    def _risk_parity_weights(self, tickers):
        inv_vols = {t: self._get_inv_vol(t) for t in tickers}
        total = sum(inv_vols.values())
        if total > 0:
            return {t: v / total for t, v in inv_vols.items()}
        return {t: 1.0 / len(tickers) for t in tickers}

    def rebalance(self):
        if self.is_warming_up:
            return
        if self._mode not in ("strategy", "noregime"):
            return

        # Le mode `noregime` (diagnostic #22869) reste dans la branche haussière,
        # repli défensif compris.
        bull = True if self._mode == "noregime" else self._is_bull_regime()
        targets = {}

        if bull:
            trending = {}
            for ticker in self.RISKY_TICKERS:
                ind = self.sma_ind.get(ticker)
                if not ind or not ind.is_ready:
                    continue
                sym = self.symbols[ticker]
                close = self.securities[sym].close
                if close <= ind.current.value:
                    continue
                hist_6m = self.history(sym, self.MOM_6M + 5, Resolution.DAILY)
                if len(hist_6m) < self.MOM_6M * 0.8:
                    continue
                ret_6m = hist_6m["close"].iloc[-1] / hist_6m["close"].iloc[-self.MOM_6M] - 1
                if ret_6m <= 0:
                    continue
                hist_12m = self.history(sym, self.MOM_12M + 5, Resolution.DAILY)
                if len(hist_12m) < self.MOM_12M * 0.8:
                    ret_12m = ret_6m
                else:
                    ret_12m = hist_12m["close"].iloc[-1] / hist_12m["close"].iloc[-self.MOM_12M] - 1
                trending[ticker] = ret_12m

            sorted_trending = sorted(trending.items(), key=lambda x: x[1], reverse=True)
            if len(sorted_trending) >= self.MIN_TRENDING:
                n = len(sorted_trending)
                raw_weights = []
                for i, (ticker, _) in enumerate(sorted_trending):
                    rank_score = (n - i) / n
                    inv_vol = self._get_inv_vol(ticker)
                    raw_weights.append((ticker, rank_score * inv_vol))
                total = sum(w for _, w in raw_weights)
                for ticker, w in raw_weights:
                    targets[ticker] = w / total
            else:
                targets = self._risk_parity_weights(self.DEFENSIVE_TICKERS)
        else:
            targets = self._risk_parity_weights(self.DEFENSIVE_TICKERS)

        regime = "BULL" if bull else "BEAR"
        tgt_str = ", ".join(f"{t}:{w:.1%}" for t, w in sorted(targets.items()))
        self.log(f"{regime} | {tgt_str}")

        for ticker in self.ALL_TICKERS:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_data(self, data: Slice):
        pass
