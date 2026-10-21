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
#
# Consolidation #20465 (Melchin, QC research 21469 « Following the Stock
# Purchases of Senators », verdict CONSOLIDATION) : l'article 21469 ajoute une
# deuxieme construction sur le MEME dataset -- Senate seulement, fenetre de
# 30 jours sur la date de RAPPORT (pas la date de transaction), actions
# communes US uniquement (ni ADR ni REIT), equal-weight, rebalancement
# quotidien 8 h ET seulement a l'entree/sortie de la fenetre, warm-up de la
# fenetre. Annonce : Sharpe 1.054 vs SPY 0.363 (2021-09 -> 2026-09), sweep
# 20-40 j robuste (21/21 > benchmark), pic 1.264 a 24 j mais falaise 22 -> 23 j
# (0.988 -> 1.260) = artefact d'echantillon selon l'auteur lui-meme. Ancrage
# academique : Lazzaretto (2024, SSRN 4816497 -- >90 bps/mois post-disclosure,
# ~9 bps/jour sur les trades speculatifs, verifie sur l'abstract SSRN) ;
# Fishman & Hagerty (1995, RFS 8(3)) -- la divulgation deplace les prix meme
# pour un insider non informe. Mode `rebalance=window` ci-dessous.
#
# Verdict attendu honnete : a mesurer -- la contre-evidence (Thian Seong Yee)
# dit "returns similar to buy and hold SPY, lower drawdown, better Sharpe" ;
# la litterature adverse (Eggers & Hainmueller, « Capitol Losses », JOP) dit
# la performance congressionnelle globale mediocre -- Lazzaretto est le
# contre-pied sur le sous-echantillon speculatif.
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
        # #20465 : filtre de chambre (all = comportement 17886 inchangé).
        self._house = str(self.get_parameter("house", "all")).lower()
        # #20465 : seconde construction 21469 (fenetre 30 j sur date de
        # rapport, equal-weight, quotidien 8 h).
        self._rebalance_mode = str(
            self.get_parameter("rebalance", "weekly")).lower()
        self._holding_days = int(self.get_parameter("holding-days", "30"))

        # Cache maintenu par le selecteur : evite `universe.selected` (None
        # rapporte en live par L. Raducu, commentaires de l'article).
        self._selected = []
        self._last_report_date_by_symbol = {}
        self._needs_rebalance = False

        spy = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)

        if self._rebalance_mode == "window":
            # Construction 21469 : l'univers Congres ENREGISTRE les
            # disclosures (UNIVERSE.UNCHANGED, aucun titre ajoute), un second
            # univers fondamental selectionne les actions communes US de la
            # fenetre, le rebalancement a lieu a l'entree/sortie seulement.
            self.set_warm_up(timedelta(self._holding_days))
            self.add_universe(
                QuiverQuantCongressUniverse, self._record_disclosures)
            self.add_universe(self._select_window_assets)
            self.schedule.on(
                self.date_rules.every_day("SPY"),
                self.time_rules.at(8, 0),
                self._rebalance_window)
        else:
            # Construction 17886 (inchangee) : l'univers Congres selectionne
            # directement les achats, rebalancement hebdomadaire.
            self.add_universe(
                QuiverQuantCongressUniverse, self._select_congress_buys)
            self.schedule.on(
                self.date_rules.week_start(spy),
                self.time_rules.after_market_open(spy, 30),
                self._trade)

    def _param_year(self, name: str, default: int) -> int:
        raw = self.get_parameter(name)
        return int(raw) if raw else default

    def _house_matches(self, constituent) -> bool:
        """Filtre de chambre (#20465) : all | senate | house."""
        if self._house == "all":
            return True
        house = getattr(constituent, "house", None)
        if self._house == "senate":
            return house == Congress.SENATE
        if self._house == "house":
            return house == Congress.HOUSE
        return True

    def _select_congress_buys(self, constituents) -> list:
        """Univers 17886 = uniquement les achats (pas de signal SELL)."""
        selected = [
            c.symbol for c in constituents
            if self._house_matches(c)
            and c.transaction == OrderDirection.BUY]
        self._selected = selected
        return selected

    def _record_disclosures(self, data) -> list:
        """Univers Congres 21469 : enregistre, ne selectionne pas.

        Garde la date de rapport la plus recente par titre achete (chambre
        filtree), expurge les disclosures sorties de la fenêtre, et signale
        le besoin de rebalancement. Renvoie UNCHANGED : cet univers n'ajoute
        aucun titre a l'algorithme.
        """
        for d in data:
            if (self._house_matches(d)
                    and d.transaction == OrderDirection.BUY):
                self._last_report_date_by_symbol[d.symbol] = d.report_date
                self._needs_rebalance = True
        cutoff = self.time - timedelta(self._holding_days)
        for symbol in [s for s, date
                       in self._last_report_date_by_symbol.items()
                       if date < cutoff]:
            self._last_report_date_by_symbol.pop(symbol)
            self._needs_rebalance = True
        return Universe.UNCHANGED

    def _select_window_assets(self, fundamentals: List[Fundamental]) -> list:
        """Univers fondamental 21469 : actions communes US de la fenetre.

        Exclut ADR et REIT (idiome doc-exact de l'article). Le cache
        `_selected` remplace toute lecture de `universe.selected` (friction
        L. Raducu, cf #16813).
        """
        if self.is_warming_up:
            self._selected = []
            return []
        selected = [
            f.symbol for f in fundamentals
            if f.symbol in self._last_report_date_by_symbol
            and f.company_reference.country_id == "USA"
            and f.security_reference.security_type == "ST00000001"
            and not f.security_reference.is_depositary_receipt
            and not f.company_reference.is_reit]
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

    def _rebalance_window(self) -> None:
        """Rebalancement 21469 : equal-weight, seulement si la fenetre a bouge."""
        if not self._needs_rebalance or self.is_warming_up:
            return
        self._needs_rebalance = False
        symbols = list(self._selected)
        if len(symbols) == 0:
            return
        targets = [
            PortfolioTarget(symbol, 1.0 / len(symbols))
            for symbol in symbols]
        self.set_holdings(targets, True)
