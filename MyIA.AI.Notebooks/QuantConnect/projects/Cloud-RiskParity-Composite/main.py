# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class RiskParityComposite(QCAlgorithm):
    """
    Risk Parity Composite v4 — Cloud-native QuantBook

    Multi-asset tactical rotation using SMA200 + 6m momentum dual filter.
    Equal weight among trend-positive assets, monthly rebalance.
    Based on AQR Trend-Following methodology (Hurst, Ooi, Pedersen 2014).
    """

    def initialize(self):
        # Mesure contre references detenues (#21534, protocole de #21329) :
        # `strategy` (defaut) garde la decision du code ; `spy` (SPY detenu) et
        # `6040` (SPY 60 %, BND 40 %) sont les deux references.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040"):
            raise ValueError(
                f"parametre mode inconnu : {self._mode} (strategy | spy | 6040)"
            )

        # Aligned baseline period 2018-2025 (#1630). Original start was 2014;
        # standardized to 2018-01-01 for cross-strategy comparison.
        # Les parametres start_date et end_date (%Y%m%d) ouvrent la mesure hors
        # echantillon ; sans eux, la fenetre reste celle-ci.
        start_date_param = self._parse_date_param("start_date")
        end_date_param = self._parse_date_param("end_date")
        if start_date_param is not None:
            self.set_start_date(start_date_param)
        else:
            self.set_start_date(2018, 1, 1)
        if end_date_param is not None:
            self.set_end_date(end_date_param)
        else:
            self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE,
            AccountType.MARGIN
        )
        if self._mode != "strategy":
            self.settings.seed_initial_prices = True

        self.tickers = ["SPY", "TLT", "GLD", "EFA", "EEM", "DBC"]
        self.symbols = {}
        self.sma200 = {}
        for ticker in self.tickers:
            sec = self.add_equity(ticker, Resolution.DAILY)
            sec.set_leverage(2.0)
            self.symbols[ticker] = sec.symbol
            self.sma200[ticker] = self.SMA(sec.symbol, 200, Resolution.DAILY)

        self.rebalance_days = int(self.get_parameter("rebalance_days", 30))
        self.last_rebalance = self.time

        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)

        spy = self.symbols["SPY"]
        # References : memes abonnements et meme prechauffage, aucune decision
        # (on_data sort tout de suite), reequilibrage au debut de chaque mois.
        # BND n'est abonne qu'en mode reference : le mode `strategy` reste le
        # code d'origine.
        if self._mode != "strategy":
            self._ref_bnd = (
                self.add_equity("BND", Resolution.DAILY).symbol
                if self._mode == "6040"
                else None
            )
            self.schedule.on(
                self.date_rules.month_start(spy),
                self.time_rules.after_market_open(spy, 1),
                self._rebalance_reference,
            )

        # Trace journaliere `shadow` (contrat #18923) : valeur du portefeuille a
        # l'ouverture de chaque seance de SPY, repartie sur e0..e4. Les trois
        # modes la prennent au meme instant, sur la cloture de la veille.
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day(spy),
            self.time_rules.after_market_open(spy, 0),
            self._trace,
        )

    def _parse_date_param(self, name):
        raw = self.get_parameter(name)
        if raw is None or str(raw).strip() == "":
            return None
        return datetime.strptime(str(raw).strip(), "%Y%m%d")

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        spy = self.symbols["SPY"]
        if self._ref_bnd is None:
            self.set_holdings([PortfolioTarget(spy, 1.0)])
        else:
            self.set_holdings([
                PortfolioTarget(spy, 0.6),
                PortfolioTarget(self._ref_bnd, 0.4),
            ])

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def on_data(self, data):
        if self.is_warming_up or self._mode != "strategy":
            return

        # A dividend notice arrives alone in a midnight slice, with no bar (#20264):
        # it must not trigger the rebalance.
        if not any(data.bars.contains_key(s) for s in self.symbols.values()):
            return

        if (self.time - self.last_rebalance).days < self.rebalance_days:
            return

        # Dual filter: SMA200 + 6m momentum
        long_set = set()
        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            sma = self.sma200[ticker]
            if not sma.is_ready:
                continue

            price = self.securities[symbol].price
            if price <= sma.current.value:
                continue

            # 6m momentum check
            try:
                history = self.history(symbol, 126, Resolution.DAILY)
                if len(history) < 30:
                    continue
                closes = history['close']
                mom_6m = (closes.iloc[-1] / closes.iloc[0]) - 1
                if mom_6m > 0:
                    long_set.add(ticker)
            except Exception:
                continue

        if not long_set:
            # All cash if no asset qualifies
            for ticker in self.tickers:
                self.set_holdings(self.symbols[ticker], 0)
            self.last_rebalance = self.time
            return

        # Equal weight allocation
        weight = 1.0 / len(long_set)
        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            if ticker in long_set:
                self.set_holdings(symbol, weight)
            else:
                self.set_holdings(symbol, 0)

        self.last_rebalance = self.time

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"RISK PARITY v4: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
