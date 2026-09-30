# region imports
from AlgorithmImports import *
# endregion

# qc-research #16372 : Copying Congress Trades (Melchin, QC research 17886).
# Copie les achats d'actions des membres du Congres US (dataset Quiver
# Quantitative US Congress Trading, disclosures STOCK Act <= 45 jours) :
# univers = actions recemment ACHETEES, rebalancement hebdomadaire (lundi,
# 30 min apres l'open SPY), pondervation inverse-volatilite (vol quotidienne
# trailing ~6 mois), levier cible 1.5x, cap 10 % par actif anti-concentration.
# L'article divulgue Sharpe algo 0.934 vs SPY 0.7 mais PAS la periode, le
# drawdown, le turnover ni la robustesse (levier/cap/fenetre) : ce port
# parametre ces axes et ajoute une jambe OOS distincte.
# Fix d'une friction documentee dans les commentaires de l'article :
# `self._universe.selected` retourne None en certains contextes (live) --
# la selection est cachee par le selecteur lui-meme.
# Verdict attendu honnete : a mesurer -- la contre-evidence (Thian Seong Yee)
# dit "returns similar to buy and hold SPY, lower drawdown, better Sharpe".
# Verdict SOTA etabli : RECOVERABLE-USER-HAND -- l'org QC n'a pas
# l'entitlement du dataset Quiver Congress : l'univers ne selectionne jamais
# (mesure probe4, 0 ordres sur Q1-2019, code doc-exact, coverage 2016+).
# Le port est complet et compile (BuildSuccess) ; les backtests tournent des
# que l'org souscrit le dataset.


class CongressTradesCopyAlgorithm(QCAlgorithm):

    def initialize(self) -> None:
        # Dates par defaut : baseline 2019-2024. Overridables par parametre
        # (jambe OOS 2025-2026H1 et sensibilites sans recompilation).
        self.set_start_date(self._param_year("start", 2019), 1, 1)
        self.set_end_date(self._param_year("end", 2024), 12, 31)
        self.set_cash(100_000)
        self.set_benchmark("SPY")

        self.universe_settings.resolution = Resolution.DAILY

        self._leverage = float(self.get_parameter("leverage", "1.5"))
        self._cap = float(self.get_parameter("cap", "0.10"))
        self._vol_window_days = int(self.get_parameter("vol-window", "180"))

        # Cache maintenu par le selecteur : evite `universe.selected` (None
        # rapporte en live par L. Raducu, commentaires de l'article).
        self._selected = []

        self._universe = self.add_universe(
            QuiverQuantCongressUniverse, self._select_congress_buys)

        spy = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)
        self.schedule.on(
            self.date_rules.week_start(spy),
            self.time_rules.after_market_open(spy, 30),
            self._trade)

    def _param_year(self, name: str, default: int) -> int:
        raw = self.get_parameter(name)
        return int(raw) if raw else default

    def _select_congress_buys(self, constituents) -> list:
        """Univers = uniquement les achats (pas de signal SELL symetrique)."""
        selected = [
            c.symbol for c in constituents
            if c.transaction == OrderDirection.BUY]
        self._selected = selected
        return selected

    def on_end_of_algorithm(self) -> None:
        # Temoin de turnover pour le rapport de recherche.
        self.log(
            "congress-trades-copy: trades executés="
            f"{len(self.transactions.transaction_record)}")

    def _trade(self) -> None:
        symbols = list(self._selected)
        if len(symbols) == 0:
            return
        closes = self.history(
            symbols, self._vol_window_days + 1, Resolution.DAILY)["close"]
        if closes is None or closes.empty:
            return
        daily_returns = closes.unstack(0).pct_change().iloc[1:]
        vol = daily_returns.std()
        inv_vol = 1.0 / vol
        inv_vol = inv_vol.dropna()
        if inv_vol.sum() == 0:
            return
        targets = [
            PortfolioTarget(
                symbol,
                min(self._cap, self._leverage * (weight / inv_vol.sum())))
            for symbol, weight in inv_vol.items()
        ]
        self.set_holdings(targets, True)
