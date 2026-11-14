# region imports
from AlgorithmImports import *
# endregion

# Exposition BTC pilotee par la volatilite (#21143, ligue #19821).
#
# Hypothese pre-enregistree (issue #21143, fixee avant tout backtest) : pas d'edge
# directionnel -- le vol targeting lisse le risque d'un actif volatil sans en predire
# la direction, et livre au panier une poche au profil de pertes borne, faiblement
# correelee au coeur actions. La volatilite realisee pilote la TAILLE de la position
# BTC, jamais son sens.
#
# Regle (mode "base", defauts) :
# - sigma_hat : EWMA des rendements journaliers BTC, span 30 barres, annualisee en
#   racine de 365 (le BTC cote tous les jours) ;
# - cible w = clip(sigma_etoile / sigma_hat, 0, 1), sigma_etoile = 30 % -- jamais de
#   levier ; le reste du portefeuille reste en liquidites ;
# - bande de trading : ordre seulement si |w_cible - w_courant| >= 0,05 ;
# - execution : ordre au marche a la barre suivante ; la quantite d'achat est bornee
#   par les liquidites disponibles APRES prise en compte des sorties -- aucun achat
#   ne peut etre refuse pour pouvoir d'achat insuffisant (mecanisme mesure en #20388).
# Si sigma_hat <= 0 (prix plats), la cible precedente est conservee.
#
# Parametres, tous optionnels :
# - start / end : dates AAAA-MM-JJ (defaut 2016-01-01 -> 2026-09-30) ;
# - mode : "base" (defaut), "hold-btc" (BTC detenu, meme instrumentation), "spy"
#   (SPY detenu), "sixty40" (60/40 SPY/IEF, rebalance le premier jour de bourse du
#   mois) ;
# - fee_mult : multiplie les frais du modele de courtier (1 = identite) ;
# - sigma_etoile / vol_span / trade_band : parametres de la regle (defauts 30 / 30 /
#   0,05), points de grille du protocole.
# Graphique "shadow" : une valeur par barre journaliere, tracee avant toute decision
# dans e0..e4 (valeur du portefeuille), plus les couts `fees` (frais cumules / valeur
# de depart) et `turnover` (montants executes cumules, en fraction du portefeuille) --
# contrat du rejeu en ombre #18923. La premiere version tracait aussi la cloture
# BTCUSD (b0..b4), qu'aucun lecteur n'utilise : QC ne garde que dix series tracees par
# backtest, tous graphiques confondus, et les douze series faisaient perdre e0 et b0,
# les dernieres creees (mesure du 2026-11-10, #24153).
#
# BTCUSD est souscrit sans remplissage vers l'avant : une barre recopiee n'apporte
# aucune cloture, et le rejeu en ombre lance avant minuit UTC en recevait une pour la
# date de passage elle-meme (cloture de la veille repetee, point refuse par le
# harnais car il depasse `tradeableDates`, #24153).
#
# Prechauffage : les clotures recues pendant `set_warm_up` alimentent la fenetre de
# l'EWMA, si bien que la regle s'applique des la premiere barre apres le depart. La
# premiere version sortait de `on_data` avant de les ajouter : la candidate restait en
# liquidites pendant ses 31 premieres barres apres CHAQUE depart -- a chaque passage
# en ombre, qui repart de la date de gel (#24153).
from collections import deque


class _ScaledFeeModel(FeeModel):
    """Frais du modele de courtier (par defaut de Lean), mis a l'echelle."""

    def __init__(self, base, multiplier):
        super().__init__()
        self._base = base
        self._multiplier = multiplier

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class _ScaledFeeInitializer(SecurityInitializer):
    """Conserve les reglages du modele de courtier, puis substitue les frais mis a l'echelle."""

    def __init__(self, brokerage_model, security_seeder, multiplier):
        super().__init__(brokerage_model, security_seeder)
        self._multiplier = multiplier

    def initialize(self, security):
        security.set_fee_model(_ScaledFeeModel(security.fee_model, self._multiplier))


# Poids statiques des modes de reference (meme frais, meme instrumentation).
_REFERENCE_WEIGHTS = {
    "spy": {"SPY": 1.0},
    "sixty40": {"SPY": 0.6, "IEF": 0.4},
}

MODES = ("base", "hold-btc", "spy", "sixty40")


class BtcVolTargetAlgorithm(QCAlgorithm):

    def initialize(self):
        # Dates sans valeur par défaut (règle 1 du contrat d'ombre #18923) : un
        # backtest lancé sans elles échoue au lieu de tourner sur une période
        # implicite. La fenêtre du verdict est 2016-01-01 -> 2026-09-30.
        start = self.get_parameter("start")
        end = self.get_parameter("end")
        if not start or not end:
            raise ValueError("parameters start and end are required (ISO dates)")
        self.set_start_date(*map(int, start.split("-")))
        self.set_end_date(*map(int, end.split("-")))
        self.set_account_currency("USD")
        self.set_cash(100000)
        self.start_value = 100000.0

        self.mode = self.get_parameter("mode") or "base"
        if self.mode not in MODES:
            raise ValueError(f"mode inconnu : {self.mode}")
        # Brokerage par mode, mesure sur la sonde 2016-Q1 : sous IBKR les ordres
        # crypto sont rejetes (courbe plate malgre 62 ordres) -- BTC-ETH-Rotation
        # (#20189) trade le crypto sous BITFINEX/CASH ; les modes equity gardent
        # IBKR pour leurs jambs SPY/IEF (l'architecture de BitcoinRegimeGate #19929).
        if self.mode in ("base", "hold-btc"):
            self.set_brokerage_model(BrokerageName.BITFINEX, AccountType.CASH)
        else:
            self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.fee_mult != 1.0:
            self.set_security_initializer(_ScaledFeeInitializer(
                self.brokerage_model, FuncSecuritySeeder(self.get_last_known_prices), self.fee_mult))

        self.sigma_etoile = float(self.get_parameter("sigma_etoile") or 30) / 100.0
        self.vol_span = int(self.get_parameter("vol_span") or 30)
        self.trade_band = float(self.get_parameter("trade_band") or 0.05)
        if self.vol_span < 2 or not (0.0 < self.sigma_etoile) or not (0.0 < self.trade_band <= 1.0):
            raise ValueError("parametres de regle invalides")

        self.btc = self.add_crypto("BTCUSD", Resolution.DAILY, market=Market.BITFINEX,
                                   fill_forward=False).symbol
        self.set_benchmark(self.btc)

        self.ref_symbols = {}
        if self.mode in _REFERENCE_WEIGHTS:
            for ticker in _REFERENCE_WEIGHTS[self.mode]:
                self.ref_symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol

        self.set_warm_up(self.vol_span + 5, Resolution.DAILY)

        # Fenetre des clotures pour l'EWMA manuelle (rendements journaliers).
        self._closes = deque(maxlen=self.vol_span + 1)

        # Compteurs de mesure (#21143).
        self.target = None          # derniere cible w calculee (mode base)
        self.w_bar_num = 0.0        # somme des expositions BTC realisees
        self.w_bar_days = 0         # barres comptees
        self.orders_sent = 0
        self.orders_invalid = 0
        self.trades = 0             # passages la bande de trading
        self.last_month = None
        self.btc_bars = 0
        self.equity_bars = 0
        self.traded = 0.0           # rotation cumulee, en fraction du portefeuille

    def _plot_costs(self):
        """Couts du contrat d'ombre, a la meme date que la valeur du portefeuille."""
        self.plot("shadow", "fees", float(self.portfolio.total_fees) / self.start_value)
        self.plot("shadow", "turnover", self.traded)

    def _plot_shadow(self):
        """Trace le contrat d'ombre avant toute decision de la barre."""
        k = self.btc_bars % 5
        self.plot("shadow", f"e{k}", self.portfolio.total_portfolio_value)
        self._plot_costs()

    def on_order_event(self, event):
        if event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(float(event.fill_quantity) * float(event.fill_price))
                            / float(self.portfolio.total_portfolio_value))

    def _ewma_vol(self):
        """Volatilite annualisee (racine de 365) des rendements journaliers BTC, EWMA span vol_span."""
        if len(self._closes) < self.vol_span + 1:
            return None
        alpha = 2.0 / (self.vol_span + 1.0)
        var = 0.0
        prev = self._closes[0]
        for close in list(self._closes)[1:]:
            r = float(close) / float(prev) - 1.0
            var = (1.0 - alpha) * var + alpha * r * r
            prev = close
        return math.sqrt(var * 365.0)

    def _buy_sized_to_cash(self, symbol, target_value):
        """Achat borne par les liquidites disponibles -- mecanisme #20388 : aucun refus possible."""
        price = self.securities[symbol].price
        if price <= 0:
            return
        cash = float(self.portfolio.cash)
        held_value = float(self.securities[symbol].holdings.holdings_value)
        missing = target_value - held_value
        if missing <= 0:
            return
        budget = min(missing, cash * 0.995)
        if budget <= 0:
            return
        qty = math.floor(budget / price)
        if qty > 0:
            ticket = self.market_order(symbol, qty)
            self.orders_sent += 1
            if ticket.status == OrderStatus.INVALID:
                self.orders_invalid += 1

    def _trim_to_target(self, symbol, target_value):
        """Vente de l'excedent au-dela de la cible."""
        price = self.securities[symbol].price
        if price <= 0:
            return
        excess = float(self.securities[symbol].holdings.holdings_value) - target_value
        if excess <= 0:
            return
        qty = math.floor(excess / price)
        if qty > 0:
            ticket = self.market_order(symbol, -qty)
            self.orders_sent += 1
            if ticket.status == OrderStatus.INVALID:
                self.orders_invalid += 1

    def on_data(self, data):
        has_btc = data.bars.contains_key(self.btc)
        # La fenetre de l'EWMA se remplit pendant le prechauffage (#24153).
        if has_btc:
            self._closes.append(data.bars[self.btc].close)
        if self.is_warming_up:
            return

        if has_btc:
            self.btc_bars += 1
            self._plot_shadow()
        elif any(data.bars.contains_key(s) for s in self.ref_symbols.values()):
            self.equity_bars += 1
            k = self.equity_bars % 5
            self.plot("shadow", f"e{k}", self.portfolio.total_portfolio_value)
            self._plot_costs()

        tpv = float(self.portfolio.total_portfolio_value)

        # Exposition realisee moyenne (tous modes : ce que la poche a reellement tenu).
        btc_value = float(self.securities[self.btc].holdings.holdings_value)
        self.w_bar_num += btc_value / tpv
        self.w_bar_days += 1

        if self.mode in _REFERENCE_WEIGHTS:
            weights = _REFERENCE_WEIGHTS[self.mode]
            month = (self.time.year, self.time.month)
            first_of_month = self.last_month != month
            self.last_month = month
            # spy : un seul achat, jamais de vente. sixty40 : rebal mensuel, ventes d'abord.
            for sym in weights:
                if self.mode == "spy":
                    if not self.portfolio[sym].invested:
                        self._buy_sized_to_cash(sym, tpv * weights[sym])
                elif first_of_month:
                    self._trim_to_target(sym, tpv * weights[sym])
            for sym in weights:
                if self.mode == "sixty40" and first_of_month:
                    self._buy_sized_to_cash(sym, tpv * weights[sym])
            return

        if self.mode == "hold-btc":
            if not self.portfolio[self.btc].invested:
                self._buy_sized_to_cash(self.btc, tpv * 0.995)
            return

        # mode "base" : vol targeting.
        sigma_hat = self._ewma_vol()
        if sigma_hat is None:
            return
        if sigma_hat > 0:
            w = self.sigma_etoile / sigma_hat
            self.target = max(0.0, min(1.0, w))
        if self.target is None:
            return
        current_w = btc_value / tpv
        if abs(self.target - current_w) < self.trade_band:
            return
        self.trades += 1
        # Vente d'abord, puis achat borne aux liquidites (regle pre-enregistree).
        self._trim_to_target(self.btc, tpv * self.target)
        self._buy_sized_to_cash(self.btc, tpv * self.target)

    def on_end_of_algorithm(self):
        self.debug(
            f"mode={self.mode} bars_btc={self.btc_bars} w_bar={self.w_bar_num / max(1, self.w_bar_days):.4f} "
            f"trades={self.trades} orders={self.orders_sent} invalid={self.orders_invalid}"
        )
