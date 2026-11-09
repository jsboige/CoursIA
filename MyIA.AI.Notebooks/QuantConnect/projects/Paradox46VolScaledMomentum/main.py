# TheOmniscientParadox (fiche Strategy Explorer 46, v2.0.1 du 31/01/2026,
# auteur affiche : Naitik Gupta, Desenyon Trade Club) -- reimplementation
# declaree. Sous-titre de la fiche : "Volatility-Scaled Daily Momentum ETF
# Rotation".
#
# Le projet source (27869458) n'est pas lisible par le compte de la flotte :
# cette implementation suit la description publique de la fiche. La fiche dit
# que l'univers est "domine par des ETF sectoriels et indiciels a effet de
# levier" sans le lister : l'univers ci-dessous est DECLARE, et la question de
# l'issue #18906 -- "ce qu'il reste sans le levier" -- se joue sur la paire
# levier / equivalent 1x, meme logique, memes parametres.
#
# Regles (description publiee) :
#   - rotation quotidienne vers UN SEUL ETF ;
#   - score = momentum composite (variations court / moyen / intermediaire
#     terme) divise par la volatilite recente ;
#   - filtre de tendance : cloture au-dessus de sa moyenne 50 jours ;
#   - penalite RSI (surachat) appliquee au score ;
#   - passage en liquidites quand le momentum se degrade.
#
# Univers declare (mode "leveraged") et equivalent 1x (mode "unlevered" --
# le verdict de #18906 porte sur la version SANS levier, point 3) :
#   UPRO 3x S&P500     -> SPY
#   TQQQ 3x Nasdaq-100 -> QQQ
#   UDOW 3x Dow30      -> DIA
#   TECL 3x Technologie-> XLK
#   SOXL 3x Semis      -> SMH
#   USD  2x Semis (ProShares Ultra Semiconductors, et non un 3x financier :
#        ecart connu, voir le README) -> XLF
#
# Choix fixes AVANT tout calcul (protocole #18906, point 5) :
#   fenetres momentum court/moyen/intermediaire : 21/63/126 jours (base) ;
#     variantes de grille : 10/42/84 (rapide), 42/126/189 (lente)
#   volatilite : ecart-type des rendements quotidiens sur 20 jours
#   composite : moyenne simple des trois rendements par fenetre
#   tendance : SMA 50 jours (variantes 100 / 200)
#   penalite RSI : score /= 1 + max(0, RSI14 - 70) / 20
#     (chaque tranche de 20 points de RSI au-dessus de 70 divise le score
#     par environ deux -- forme declaree, la fiche ne donne pas la sienne)
#   eligibilite : cloture > SMA ET score > 0 ; sinon liquidites
#   allocation : 98 % sur l'argmax du score ajuste (2 % en liquide, voir
#     ci-dessous), revue quotidienne 30 minutes apres l'ouverture
#   fee_mult : multiplicateur des frais IBKR (1.0 = identite ; 2.0 = test de
#     sensibilite du point 4)
#   start_date / end_date : fenetre (defauts 2018-01-01 / 2026-09-25)
#
# Rotation (#20388) : set_holdings(cible, 1.0) ne vendait pas la ligne
# precedente. Sur le compte marge par defaut (levier 2), l'achat etait finance a
# credit, puis refuse faute de marge, et seuls les appels de marge vendaient :
# jusqu'a trois lignes detenues a la fois, 174 achats refuses et 192 ordres
# d'appel de marge sur 2018-2026 en univers "leveraged". _rotate_to vend les
# autres lignes d'abord, vise 98 % et plafonne l'achat a la marge libre a
# l'envoi. Les ordres refuses et les ordres d'appel de marge sont publies en
# statistiques d'execution "refused" et "margin_calls".

from AlgorithmImports import *

import numpy as np


class _ScaledFeeModel(FeeModel):
    """Frais IBKR mis a l'echelle (test de sensibilite, point 4 du protocole).

    A multiplicateur 1.0, le fee de base est retourne tel quel (identite
    stricte : la comparabilite avec le run de base et les runs de grille est
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


UNIVERSES = {
    "leveraged": ["UPRO", "TQQQ", "UDOW", "TECL", "SOXL", "USD"],
    "unlevered": ["SPY", "QQQ", "DIA", "XLK", "SMH", "XLF"],
}

# Part du portefeuille visee par une rotation, et seuil sous lequel une ligne
# deja detenue est completee (#20388, meme modele que LeveragedETFMomentum-QC).
TARGET_WEIGHT = 0.98
TOP_UP_BELOW = 0.97


class Paradox46VolScaledMomentum(QCAlgorithm):

    def initialize(self):
        start = self.get_parameter("start_date", "2018-01-01").split("-")
        end = self.get_parameter("end_date", "2026-09-25").split("-")
        self.set_start_date(int(start[0]), int(start[1]), int(start[2]))
        self.set_end_date(int(end[0]), int(end[1]), int(end[2]))
        self.set_cash(100000)

        # Modele de frais Interactive Brokers (protocole #18906, point 2).
        self.set_security_initializer(self._ibkr_fees)

        # --- parametres de la grille, fixes avant tout calcul ---
        self.universe_mode = self.get_parameter("universe_mode", "leveraged")
        self.w_short = int(self.get_parameter("w_short", "21"))
        self.w_medium = int(self.get_parameter("w_medium", "63"))
        self.w_inter = int(self.get_parameter("w_inter", "126"))
        self.vol_window = int(self.get_parameter("vol_window", "20"))
        self.sma_days = int(self.get_parameter("sma_days", "50"))
        self.rsi_days = int(self.get_parameter("rsi_days", "14"))
        self.rsi_cap = float(self.get_parameter("rsi_cap", "70"))
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))

        tickers = UNIVERSES[self.universe_mode]
        self._symbols = [self.add_equity(t, Resolution.DAILY).symbol
                        for t in tickers]
        self._bench = self.add_equity("SPY", Resolution.DAILY).symbol
        self.set_benchmark(self._bench)

        # Profondeur d'historique : la fenetre la plus lente de la grille
        # (189 j) + SMA 200 j au maximum + marge de jours non bourses.
        self.lookback_days = max(self.w_inter, self.sma_days) + 10

        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.after_market_open(self._bench, 30),
            self._rebalance,
        )

        self._target = None
        self._n_rotations = 0

    def _ibkr_fees(self, security):
        security.set_fee_model(_ScaledFeeModel(self.fee_mult))

    # --- indicateurs, recalcules depuis l'historique a chaque revue ---------
    # Volonte : chaque decision ne depend QUE de donnees fermees anterieures,
    # sans etat d'indicateur cumule -- transparent pour l'audit du protocole.

    def _stats(self, symbol):
        """RSI de Wilder et rendements par fenetre, ou None si donnees courtes."""
        bars = self.history(symbol, self.lookback_days, Resolution.DAILY)
        closes = bars["close"].to_numpy()[::-1]  # plus recent en tete
        if len(closes) < max(self.w_inter, 1) + 1:
            return None

        # Rendement du jour = recent / veille (plus recent en tete : element i
        # sur element i+1). closes[1:]/closes[:-1] donnait veille/recent, signe
        # inverse (RSI nul sur hausse monotone, vol et penalite de surachat
        # mesures a l'envers -- reserve adjoint #19082, temoin 2).
        rets = closes[:-1] / closes[1:] - 1.0

        def window_return(n):
            if len(closes) < n + 1:
                return None
            # Plus recent en tete : la cloture d'il y a n seances est a
            # l'indice n. closes[-1-n] designait la (n+1)-ieme plus ANCIENNE
            # de l'historique : la fenetre dependait de la profondeur
            # demandee, pas de n (reserve adjoint #19082, temoin 1).
            return closes[0] / closes[n] - 1.0

        r_s = window_return(self.w_short)
        r_m = window_return(self.w_medium)
        r_i = window_return(self.w_inter)
        if r_s is None or r_m is None or r_i is None:
            return None

        vol = float(np.std(rets[: self.vol_window])) if len(rets) >= self.vol_window else None
        if not vol or vol <= 0:
            return None

        # RSI de Wilder sur rsi_days : les rsi_days+1 rendements les plus
        # RECENTS, remis en ordre chronologique pour la recursion.
        if len(rets) < self.rsi_days + 1:
            rsi = None
        else:
            r = rets[: self.rsi_days + 1][::-1]
            gains = np.where(r > 0, r, 0.0)
            losses = np.where(r < 0, -r, 0.0)
            avg_g = gains[: self.rsi_days].mean()
            avg_l = losses[: self.rsi_days].mean()
            for k in range(self.rsi_days, len(r)):
                avg_g = (avg_g * (self.rsi_days - 1) + gains[k]) / self.rsi_days
                avg_l = (avg_l * (self.rsi_days - 1) + losses[k]) / self.rsi_days
            rsi = 100.0 - 100.0 / (1.0 + avg_g / avg_l) if avg_l > 0 else 100.0

        sma = float(closes[: self.sma_days].mean()) if len(closes) >= self.sma_days else None

        composite = (r_s + r_m + r_i) / 3.0
        return {"close": float(closes[0]), "sma": sma, "vol": vol,
                "rsi": rsi, "score": composite / vol}

    def _rebalance(self):
        best_symbol, best_score = None, float("-inf")
        for symbol in self._symbols:
            st = self._stats(symbol)
            if st is None:
                continue
            # Filtre de tendance : il faut la donnee ET la cloture au-dessus.
            if st["sma"] is None or st["close"] <= st["sma"]:
                continue
            score = st["score"]
            # Penalite RSI : le surachat degrade le score (forme declaree).
            if st["rsi"] is not None and st["rsi"] > self.rsi_cap:
                score = score / (1.0 + (st["rsi"] - self.rsi_cap) / 20.0)
            # Momentum degrade -> pas eligible.
            if score <= 0:
                continue
            if score > best_score:
                best_symbol, best_score = symbol, score

        target = best_symbol if best_symbol is not None else None
        if target != self._target:
            self._n_rotations += 1
            self._target = target
            if target is None:
                self.liquidate()
                self.log(f"{self.time.date()} -> CASH (aucun eligible)")
            else:
                self.log(f"{self.time.date()} -> {target} (score={best_score:.4f})")
        if target is not None:
            self._rotate_to(target)

    # --- execution (#20388) -------------------------------------------------

    def _open_quantity(self, symbol):
        return sum(t.quantity - t.quantity_filled
                   for t in self.transactions.get_open_order_tickets(symbol))

    def _rotate_to(self, target):
        # Detient `target` seul a 98 % du portefeuille. La revue tourne en
        # seance sur des donnees journalieres : les ordres partent en
        # MarketOnClose et sont remplis a la cloture, dans l'ordre d'envoi. La
        # quantite est calculee avant les ventes, les ventes partent d'abord, et
        # les 2 % laisses en liquide couvrent le controle de marge a l'envoi.
        # Appelee a chaque revue : sans ordre quand la cible est deja seule et a
        # 97 % au moins. Un ordre reste ouvert (cloture sans barre) est deduit
        # plutot que renvoye.
        pending = {s: self._open_quantity(s) for s in self._symbols}
        sells = {s: -self.portfolio[s].quantity - pending[s]
                 for s in self._symbols if s != target}
        sells = {s: q for s, q in sells.items() if q != 0}
        if not sells and self.portfolio[target].quantity + pending[target] > 0:
            held = (self.portfolio[target].holdings_value
                    + pending[target] * self.securities[target].price)
            if held >= TOP_UP_BELOW * self.portfolio.total_portfolio_value:
                return
        # La revue est planifiee, pas declenchee par une barre : a la premiere
        # seance, aucune barre n'est encore arrivee et le prix vaut 0. L'achat
        # attend alors la revue suivante.
        security = self.securities[target]
        quantity = 0
        if security.price > 0:
            quantity = self.calculate_order_quantity(target, TARGET_WEIGHT) - pending[target]
            # Plafond de marge a l'envoi : les ventes ne liberent leur marge
            # qu'a leur remplissage. La quantite est calculee sur la cloture de
            # la veille et remplie a celle du jour : sur un ETF x3, une hausse
            # de plus de 2 % dans la seance porte la ligne au-dela de 100 % du
            # portefeuille, et l'achat suivant entier serait refuse. Il est
            # plafonne a la marge libre, frais compris, et complete a la revue
            # suivante.
            room = 0.97 * self.portfolio.margin_remaining * security.leverage
            quantity = min(quantity, int(room / security.price))
        for symbol, q in sells.items():
            self.market_order(symbol, q)
        if quantity > 0:
            self.market_order(target, quantity)

    def on_end_of_algorithm(self):
        years = (self.end_date - self.start_date).days / 365.25
        orders = list(self.transactions.get_orders())
        refused = sum(1 for o in orders if o.status == OrderStatus.INVALID)
        margin_calls = sum(1 for o in orders if "margin call" in (o.tag or "").lower())
        self.set_runtime_statistic("refused", str(refused))
        self.set_runtime_statistic("margin_calls", str(margin_calls))
        self.log(f"rotations={self._n_rotations} fenetre={years:.1f} ans "
                 f"univers={self.universe_mode} refused={refused} "
                 f"margin_calls={margin_calls}")
