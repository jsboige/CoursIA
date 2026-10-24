# MAXEffect-VIXLeverage-QC -- distillation de l'article QC Research 20886
# "The MAX Effect with VIX-Based Leverage Scaling" (Derek Melchin, 2026-06-12).
# Source : https://www.quantconnect.com/research/20886/the-max-effect-with-vix-based-leverage-scaling/
# Issue #22290 / EPIC #11698 (moissonnage quantconnect.com/research).
#
# Facteur MAX(5) de Bali-Cakici-Whitelaw (2011) : moyenne des 5 plus forts
# rendements quotidiens des 21 dernieres seances. Cote long uniquement :
# decile inferieur (plafond 25 titres), equi-pondere, rebalancement mensuel
# (premier jour de bourse du mois, 8 h ET). Overlay de levier pilote par le
# VIX : 1.5x quand VIX <= 15, decroissant lineairement vers 1.0x a VIX >= 30,
# reajuste en continu entre les rebalancements.
#
# mode :
#   max-vix -- le candidat (facteur + overlay de levier VIX)
#   max-only -- ablation : facteur seul, levier fixe 1.0x
#   spy -- reference detenue : SPY buy-and-hold
#
# Convention lag (defaut, cf #19825/#19837) : la ligne VIX du jour D n'est
# livree qu'a D+1 (CBOE.lag_days = 1) -- lire la cloture du VIX du jour meme
# au rebalancement est un lookahead, mesure sur les projets voisins.
# Le VIX est charge via la classe CBOE(PythonData) locale (CSV public CDN
# CBOE) : le namespace .NET QuantConnect.Data.Custom.CBOE n'est pas importable
# depuis un algorithme Python sur QC Cloud (erreur "No module named").

from AlgorithmImports import *


class MAXEffectVIXLeverage(QCAlgorithm):

    MODES = ("max-vix", "max-only", "spy")

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2026, 6, 30)
        self.SetCash(100_000)
        self.SetBenchmark("SPY")

        self.mode = self.GetParameter("mode") or "max-vix"
        if self.mode not in self.MODES:
            raise ValueError(f"mode inconnu : {self.mode}")

        # Parametres de l'article (valeurs par defaut de son optimiseur).
        self.top_returns = int(self.GetParameter("top_returns") or 5)
        self.max_portfolio_size = int(self.GetParameter("max_portfolio_size") or 25)
        self.period = int(self.GetParameter("period") or 21)
        self.low_vix = float(self.GetParameter("low_vix") or 15)
        self.high_vix = float(self.GetParameter("high_vix") or 30)
        self.low_leverage = float(self.GetParameter("low_leverage") or 1.5)
        self.high_leverage = float(self.GetParameter("high_leverage") or 1.0)

        if self.mode == "spy":
            self.spy = self.AddEquity("SPY", Resolution.Daily).Symbol
            return

        CBOE.lag_days = 1  # cloture VIX de D livree a D+1 (anti-lookahead)
        self.vix = self.AddData(CBOE, "VIX", Resolution.Daily).Symbol
        self.current_leverage = self.high_leverage

        self._universe = self.AddUniverse(self.SelectAssets)
        self.selection_data = {}

        # Premier jour de bourse du mois (shift 0 ; le shift 1 tire le
        # J+1 du premier jour -- mesure v3, evenement du 2015-02-03).
        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.At(8, 0),
            self.Rebalance,
        )

    # --- univers : filtres de l'article (actions US liquides) --------------

    def SelectAssets(self, fundamentals):
        selected = []
        for f in fundamentals:
            if (f.company_reference.is_reit
                    or f.security_reference.is_depositary_receipt
                    or not f.has_fundamental_data
                    or f.price < 5
                    or f.market_cap < 1_000_000_000):
                continue
            data = self.selection_data.setdefault(
                f.symbol, SelectionData(self.period))
            data.update(f)
            # Le facteur n'est calculable qu'avec un historique complet ;
            # le filtre de liquidite (5 M$/j en moyenne) s'applique au
            # rebalancement, pas a la selection.
            if data.is_ready:
                selected.append(f.symbol)
        return selected

    # --- facteur MAX : cf classe SelectionData au niveau module ------------
    # (une classe interne n'est PAS visible depuis les methodes : le corps de
    # classe n'entre pas dans la chaine de resolution lexicale de Python --
    # mesure v2 du backtest, "name 'SelectionData' is not defined".)

    # --- rebalancement mensuel ---------------------------------------------

    def Rebalance(self):
        factor_by_weight = {}
        for symbol in self._universe.selected:
            data = self.selection_data.get(symbol)
            security = self.securities.get(symbol)
            if data is None or security is None:
                continue
            if security.price and data.dollar_volume_sma.current.value >= 5_000_000:
                factor_by_weight[symbol] = data.factor(self.top_returns)

        if not factor_by_weight:
            return

        sorted_by_factor = sorted(factor_by_weight, key=factor_by_weight.get)
        selection_size = min(
            self.max_portfolio_size, max(1, len(sorted_by_factor) // 10))
        selected = sorted_by_factor[:selection_size]
        weight = 1.0 / len(selected)

        leverage = (self.current_leverage if self.mode == "max-vix"
                    else self.high_leverage)
        # Liquidation manuelle des noms sortis du decile + SetHoldings liste
        # positionnel (patron eprouve ML-RandomForest) : le kwarg
        # liquidate_existing_holdings casse la resolution d'overload Python
        # (mesure v3, "argument 1 ('symbol') expected Symbol, got list").
        kept = set(selected)
        for s in self.portfolio.values():
            if s.invested and s.symbol not in kept:
                self.Liquidate(s.symbol)
        targets = [PortfolioTarget(s, float(leverage * weight)) for s in selected]
        self.SetHoldings(targets)

    # --- overlay VIX : levier continu entre les rebalancements -------------

    def LeverageFromVix(self, vix):
        if not vix or vix >= self.high_vix:
            return self.high_leverage
        if vix <= self.low_vix:
            return self.low_leverage
        span = self.high_vix - self.low_vix
        step = (vix - self.low_vix) / span
        return self.low_leverage + step * (self.high_leverage - self.low_leverage)

    def OnData(self, data):
        if self.mode == "spy":
            if not self.portfolio.invested and data.contains_key(self.spy):
                self.SetHoldings(self.spy, 1.0)
            return
        if self.mode != "max-vix":
            return
        if not data.contains_key(self.vix):
            return
        # .Value = cloture posee par CBOE.Reader (data[4] du CSV).
        vix = data[self.vix].Value
        leverage = self.LeverageFromVix(vix)
        if abs(leverage - self.current_leverage) < 1e-6:
            return
        self.current_leverage = leverage
        # Rescale : la somme des poids cibles vaut exactement le levier
        # demande, donc l'exposition resultante = levier x equity, quel que
        # soit l'etat precedent. Le denominateur est la SOMME DES POSITIONS
        # DETENUES, pas total_portfolio_value : avec ce dernier, le poids de
        # chaque ligne se calcule sur l'exposition courante (deja rescalee la
        # fois precedente) et l'exposition se COMPOSE a chaque changement de
        # levier (simulation Hermes : 1.50 -> 1.45 -> 2.17 ; revue #22330).
        # La quantite vit sur le holding du portfolio (SecurityHolding :
        # .symbol/.quantity/.invested) et le prix sur la Security
        # (self.securities[symbol].price) -- ni portfolio.values() ni
        # securities.values() ne portent les deux (mesures v4 et v5 :
        # "EquityHolding has no attribute 'holding'", puis "Equity object has
        # no attribute 'holding'"). SetHoldings par symbole : pas d'overload
        # de liste a resoudre.
        invested = sum(
            float(h.quantity) * self.securities[h.symbol].price
            for h in self.portfolio.values()
            if h.invested and self.securities[h.symbol].price)
        if invested <= 0:
            return
        for holding in list(self.portfolio.values()):
            if not holding.invested:
                continue
            price = self.securities[holding.symbol].price
            if not price:
                continue
            weight = leverage * float(holding.quantity) * price / invested
            self.SetHoldings(holding.symbol, float(weight))


class SelectionData:
    """Facteur MAX(5) sur 21 seances : moyenne des n plus forts rendements
    quotidiens. Niveau module (pattern canonique du tutoriel QC) : une classe
    interne n'est pas visible depuis les methodes de l'algorithme."""

    def __init__(self, period):
        self.dollar_volume_sma = SimpleMovingAverage(period)
        self.daily_return = RateOfChange(1)
        # RollingWindow pose a la main : RateOfChange n'expose pas de fenetre
        # redimensionnable directement.
        self.window = RollingWindow[float](period)

    def update(self, f):
        self.dollar_volume_sma.update(f.end_time, f.dollar_volume)
        self.daily_return.update(f.end_time, f.adjusted_price)
        self.window.add(self.daily_return.current.value)

    @property
    def is_ready(self):
        return (self.window.is_ready
                and self.dollar_volume_sma.is_ready)

    def factor(self, top_n):
        values = sorted(self.window)
        return float(np.mean(values[-top_n:]))


class CBOE(PythonData):
    # Jours de decalage entre le jour de bourse d'une ligne et sa livraison
    # (1 par defaut ici, fixe par Initialize avant AddData -- convention lag
    # du depôt, cf #19825/#19837). Patron repris de DynamicVIXSpyRegime-QC.
    lag_days = 1

    def GetSource(self, config, date, isLive):
        return SubscriptionDataSource(
            "https://cdn.cboe.com/api/global/us_indices/daily_prices/VIX_History.csv",
            SubscriptionTransportMedium.RemoteFile
        )

    def Reader(self, config, line, date, isLive):
        if not (line.strip() and line[0].isdigit()):
            return None

        row = line.split(',')

        try:
            index = CBOE()
            index.Symbol = config.Symbol
            tradeday = datetime.strptime(row[0], "%m/%d/%Y")
            index.Time = tradeday + timedelta(days=CBOE.lag_days)
            index.Value = float(row[4])
            index["close"] = float(row[4])
            return index
        except:
            return None
