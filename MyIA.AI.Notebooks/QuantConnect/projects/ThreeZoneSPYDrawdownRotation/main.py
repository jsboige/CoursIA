# Three-Zone SPY Drawdown Rotation (fiche Strategy Explorer 781, v1.0.0,
# auteur affiche : Viliam Balara) -- reimplementation declaree.
#
# Le projet source (37135744) n'est pas lisible par le compte de la flotte :
# cette implementation suit la description publique de la fiche. Les seuils
# exacts des zones vivent dans le code inaccessible de l'auteur ; la grille
# de robustesse (issue #18905, point 4) balaie ces seuils.
#
# Regles (description publiee) :
#   - trois zones definies par la baisse du SPY depuis son plus haut 52 semaines ;
#   - selon la zone, rotation entre le SPY et un portefeuille d'actions a dividende ;
#   - filtres dividende : rendement >= 3 %, taux de distribution 5-80 %,
#     historique de dividende sur 10 ans, au plus 20 titres ;
#   - revue hebdomadaire.
#
# Parametres (grille fixee AVANT calcul, cf issue #18905) :
#   zone1_dd, zone2_dd : seuils de drawdown des zones (defauts 0.05 / 0.10)
#   top_n : taille du portefeuille dividende (defaut 20)
#   min_yield, payout_min, payout_max, div_hist_years : filtres dividende
#   fee_mult : multiplicateur des frais IBKR (defaut 1.0 = identite ;
#     2.0 = test de sensibilite du point 4 du protocole)
#   start_date, end_date : fenetre (defauts 2018-01-01 / 2026-09-25)

from AlgorithmImports import *


class _ScaledFeeModel(FeeModel):
    """Frais IBKR mis a l'echelle (test de sensibilite, point 4 du protocole).

    A multiplicateur 1.0, le fee de base est retourne tel quel (identite
    stricte : la comparabilite avec le run de base et les runs OAT est
    preservee).
    """

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class ThreeZoneSPYDrawdownRotation(QCAlgorithm):

    def initialize(self):
        start = self.get_parameter("start_date", "2018-01-01").split("-")
        end = self.get_parameter("end_date", "2026-09-25").split("-")
        self.set_start_date(int(start[0]), int(start[1]), int(start[2]))
        self.set_end_date(int(end[0]), int(end[1]), int(end[2]))
        self.set_cash(100000)

        # Modele de frais Interactive Brokers (protocole issue #18905, point 2).
        self.set_security_initializer(self._ibkr_fees)

        # Parametres de la grille, fixes avant tout calcul.
        self.zone1_dd = float(self.get_parameter("zone1_dd", "0.05"))
        self.zone2_dd = float(self.get_parameter("zone2_dd", "0.10"))
        self.top_n = int(self.get_parameter("top_n", "20"))
        self.min_yield = float(self.get_parameter("min_yield", "0.03"))
        self.payout_min = float(self.get_parameter("payout_min", "0.05"))
        self.payout_max = float(self.get_parameter("payout_max", "0.80"))
        self.div_hist_years = int(self.get_parameter("div_hist_years", "10"))
        # Multiplicateur de frais (sensibilite point 4, defaut = identite).
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Memoire de la derniere selection fine (alimente le rebalancement).
        self._fine_selected = []

        # Cache de l'historique de dividende, revere au premier rebalancement
        # de chaque mois (peu volatil a cette echelle).
        self._div_cache = {}
        self._div_cache_month = None

        self.universe_settings.resolution = Resolution.DAILY
        self.add_universe(self._select_coarse, self._select_fine)

        # Revue hebdomadaire : lundi, 30 minutes apres l'ouverture.
        self.schedule.on(
            self.date_rules.week_start(self.spy),
            self.time_rules.after_market_open(self.spy, 30),
            self._rebalance,
        )

        self._zone = None

    def _ibkr_fees(self, security):
        security.set_fee_model(_ScaledFeeModel(self.fee_mult))

    # --- Univers -------------------------------------------------------------

    def _select_coarse(self, coarse):
        # Liquidite minimale : prix et dollar volume pour ecarter les micro-caps.
        ranked = sorted(
            [c for c in coarse if c.price > 5 and c.dollar_volume > 20e6],
            key=lambda c: c.dollar_volume,
            reverse=True,
        )
        return [c.symbol for c in ranked[:200]]

    def _select_fine(self, fine):
        picked = []
        for f in fine:
            dy = f.valuation_ratios.trailing_dividend_yield
            pe = f.valuation_ratios.pe_ratio
            if not dy or dy < self.min_yield:
                continue
            # Taux de distribution approxime par rendement x P/E (equivalent
            # de DY/EY, champs garantis ; PE negatif = pertes -> rejete).
            if not pe or pe <= 0:
                continue
            payout = dy * pe
            if not (self.payout_min <= payout <= self.payout_max):
                continue
            if f.market_cap < 2e9:
                continue
            picked.append((f.symbol, dy))
        # Pre-selection par rendement decroissant ; l'historique de dividende
        # (verifie au rebalancement) tranche les derniers admis.
        picked.sort(key=lambda x: x[1], reverse=True)
        self._fine_selected = [s for s, _ in picked[:40]]
        return self._fine_selected

    # --- Historique de dividende ----------------------------------------------

    def _dividend_history_ok(self, symbol):
        if symbol in self._div_cache:
            return self._div_cache[symbol]
        try:
            df = self.history(
                self.dividends, symbol,
                timedelta(days=365 * (self.div_hist_years + 1)),
            )
        except Exception as exc:
            # Donnees manquantes : on n'admet pas le titre.
            self.debug(f"dividend history error {symbol}: {exc}")
            self._div_cache[symbol] = False
            return False
        if df is None or df.empty:
            self._div_cache[symbol] = False
            return False
        index = df.index
        if hasattr(index, "levels"):  # MultiIndex : le temps est le dernier niveau
            times = index.get_level_values(-1)
        else:
            times = index
        years = {t.year for t in times}
        this_year = self.time.year
        span = {y for y in years
                if this_year - self.div_hist_years <= y < this_year}
        # Tolerance de 2 annees manquantes sur la fenetre exigee.
        ok = len(span) >= self.div_hist_years - 2
        self._div_cache[symbol] = ok
        return ok

    def _refresh_div_cache_monthly(self):
        key = (self.time.year, self.time.month)
        if key != self._div_cache_month:
            self._div_cache_month = key
            self._div_cache = {}

    # --- Rotation -------------------------------------------------------------

    def _spy_drawdown(self):
        closes = self.history(self.spy, 253, Resolution.DAILY)["close"]
        if closes is None or len(closes) < 30:
            return 0.0
        return float(1.0 - closes.iloc[-1] / closes.max())

    def _rebalance(self):
        dd = self._spy_drawdown()
        if dd < self.zone1_dd:
            zone, budget = "verte", 0.0
            weights = {self.spy: 1.0}
        elif dd < self.zone2_dd:
            zone, budget = "jaune", 0.5
            weights = {self.spy: 0.5}
        else:
            zone, budget = "rouge", 1.0
            weights = {}

        if budget > 0:
            self._refresh_div_cache_monthly()
            picks = [s for s in self._fine_selected
                     if self._dividend_history_ok(s)][: self.top_n]
            if picks:
                per = budget / len(picks)
                for s in picks:
                    weights[s] = per

        if zone != self._zone:
            self.debug(f"{self.time} dd={dd:.3f} zone {self._zone} -> {zone}")
            self._zone = zone

        # Cibles explicites : poids nul pour toute position non visee
        # (set_holdings ne liquide pas ce qu'on ne liste pas).
        targets = [PortfolioTarget(s, 0.0)
                   for s, h in self.portfolio.items()
                   if h.invested and s not in weights]
        targets += [PortfolioTarget(s, w) for s, w in weights.items()]
        if targets:
            self.set_holdings(targets, True)

    def on_securities_changed(self, changes):
        # Un titre qui quitte l'univers de selection ne peut plus etre cible :
        # solde immediat pour ne pas laisser de position orpheline.
        for r in changes.removed_securities:
            if r.symbol != self.spy and self.portfolio[r.symbol].invested:
                self.liquidate(r.symbol)
