# region imports
from AlgorithmImports import *

# endregion
# https://www.quantconnect.com/research/9031/ichimoku-clouds-in-the-energy-sector/
# Ichimoku Clouds In The Energy Sector (Derek Melchin, QC research 9031,
# draft/pending review) -- portage fidele sous frais de courtier IBKR.
# See #19678 (semis + acceptance), EPIC #11698 (moissonnage QC-research).
#
# Adaptations documentees (detail et mesure dans README.md) :
#   a1  Fenetre et capital ne sont pas dans le code de l'article (rendus dans
#       sa prose) : parametres `start`/`end` en YYYYMMDD (defauts = fenetre de
#       l'article 20150101 -> 20200816), cash 1 M, brokerage IBKR marge et
#       `seed_initial_prices` (convention du depot pour la verification sous
#       frais courtier, campagne #1630).
#   a2  Parametre `mode` : `strategy` (defaut -- le portage de l'article) ou
#       `xle_hold` (XLE buy-and-hold sur le meme harnais frais IBKR). La table
#       de l'article confronte le Sharpe/ASD de la strategie a ceux du
#       benchmark XLE calcules sur des fenetres identiques ; le comparateur
#       vit dans le meme projet pour garantir le meme harnais.
#   a3  L'article declare `symbol_data_by_symbol` comme attribut de CLASSE de
#       l'AlphaModel (dictionnaire partage entre instances -- latent). Porte
#       en attribut d'instance dans __init__.
#   a4  L'article ne montre pas la gestion des retraits d'univers : le
#       SymbolData retire est supprime du dictionnaire de l'AlphaModel
#       (completion minimale, sans elle les titres sortis continueraient
#       d'emettre des insights sur donnees absentes).
#   a5  `benchmark` explicite : set_benchmark("XLE") pour les deux modes,
#       comme l'etude (benchmark ETF secteur energie XLE).
#   a6  Le warm-up de l'article construit des TradeBar depuis l'historique
#       pandas (`row.volume`, Runtime Error mesure au premier run : la Series
#       rendue par `.loc[symbol]` n'a plus d'attribut `volume` sur LEAN
#       courant). Remplace par l'enumeration typee `history[TradeBar]` --
#       memes barres quotidiennes, meme sequence is_ready/update.


class IchimokuEnergySectorAlgorithm(QCAlgorithm):

    def initialize(self):
        # a1 : fenetre parametree, defaut = fenetre de l'article
        start = self.get_parameter("start", "20150101")
        end = self.get_parameter("end", "20200816")
        self.set_start_date(int(start[:4]), int(start[4:6]), int(start[6:]))
        self.set_end_date(int(end[:4]), int(end[4:6]), int(end[6:]))
        self.set_cash(1000000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.settings.seed_initial_prices = True  # a1
        self.set_benchmark("XLE")  # a5

        mode = self.get_parameter("mode", "strategy")
        if mode == "xle_hold":  # a2
            self.add_equity("XLE", Resolution.DAILY)
            return

        self.universe_settings.resolution = Resolution.DAILY
        self.universe_settings.data_normalization_mode = DataNormalizationMode.ADJUSTED
        self.add_alpha(IchimokuCloudCrossOverAlphaModel())
        self.set_portfolio_construction(EqualWeightingPortfolioConstructionModel())
        self.set_execution(ImmediateExecutionModel())
        self.add_universe_selection(EnergyTopTenUniverseSelectionModel())

    def on_data(self, data):
        # mode xle_hold : achat integral unique du benchmark (a2)
        if self.securities.contains_key("XLE") and not self.portfolio.invested:
            self.set_holdings("XLE", 1)


class EnergyTopTenUniverseSelectionModel(FineFundamentalUniverseSelectionModel):
    """Univers mensuelle : 10 plus grandes capitalisations du secteur energie.

    Porte fidelement de l'article (select_coarse/select_fine) -- elimine le
    look-ahead bias de la selection de Gurrib (2020), constituee sur les
    poids de la fin de periode.
    """

    def __init__(self, fine_size=10):
        self.fine_size = fine_size
        self.month = -1

    def select_coarse(self, algorithm, coarse):
        if algorithm.time.month == self.month:
            return Universe.UNCHANGED
        return [x.symbol for x in coarse if x.has_fundamental_data]

    def select_fine(self, algorithm, fine):
        self.month = algorithm.time.month

        energy_stocks = [
            f for f in fine
            if f.asset_classification.morningstar_sector_code == MorningstarSectorCode.ENERGY
        ]
        sorted_by_market_cap = sorted(energy_stocks, key=lambda x: x.market_cap, reverse=True)
        return [x.symbol for x in sorted_by_market_cap[:self.fine_size]]


class IchimokuCloudCrossOverAlphaModel(AlphaModel):
    """Long quand Chikou croise le haut du nuage par le bas, short quand elle
    croise le bas du nuage par le haut. Insights quotidiens de duree 1 jour
    pour maintenir la position entre deux croisements (porte de l'article).
    """

    def __init__(self):
        self.symbol_data_by_symbol = {}  # a3 : instance, pas classe

    def update(self, algorithm, data):
        insights = []

        for symbol, symbol_data in self.symbol_data_by_symbol.items():
            if not data.contains_key(symbol) or data[symbol] is None:
                continue

            symbol_data.ichimoku.update(data[symbol])

            current_location = symbol_data.get_location()
            if symbol_data.previous_location is not None:  # indicateur pret
                if symbol_data.previous_location != 1 and current_location == 1:
                    symbol_data.direction = InsightDirection.UP
                if symbol_data.previous_location != -1 and current_location == -1:
                    symbol_data.direction = InsightDirection.DOWN

            symbol_data.previous_location = current_location

            if symbol_data.direction:
                insights.append(Insight.price(symbol, timedelta(days=1), symbol_data.direction))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for added in changes.added_securities:
            self.symbol_data_by_symbol[added.symbol] = SymbolData(added.symbol, algorithm)
        for removed in changes.removed_securities:  # a4
            self.symbol_data_by_symbol.pop(removed.symbol, None)


class SymbolData:
    """Enveloppe de l'indicateur IchimokuKinkoHyo par symbole (porte de
    l'article) : warm-up par historique quotidien, puis localisation de la
    ligne Chikou par rapport au nuage (Senkou A/B).
    """

    def __init__(self, symbol, algorithm):
        self.symbol = symbol
        self.previous_location = None
        self.direction = None

        self.ichimoku = IchimokuKinkoHyo()

        bars = algorithm.history[TradeBar](symbol, self.ichimoku.warm_up_period + 1, Resolution.DAILY)  # a6
        for tradebar in bars:
            if self.ichimoku.is_ready:
                self.previous_location = self.get_location()

            self.ichimoku.update(tradebar)

    def get_location(self):
        chikou = self.ichimoku.chikou.current.value

        senkou_span_a = self.ichimoku.senkou_a.current.value
        senkou_span_b = self.ichimoku.senkou_b.current.value
        cloud_top = max(senkou_span_a, senkou_span_b)
        cloud_bottom = min(senkou_span_a, senkou_span_b)

        if chikou > cloud_top:
            return 1    # au-dessus du nuage
        if chikou < cloud_bottom:
            return -1   # sous le nuage
        return 0        # dans le nuage
