# region imports
from AlgorithmImports import *
# endregion
# Reimplementation declaree de la strategie 774 du Strategy Explorer QuantConnect,
# « Four-Sleeve Adaptive Growth Strategy - Cash account » (auteur : sanchari,
# v1.0.1 du 28/09/2026). Le code source du projet publie n'est pas lisible depuis
# ce depot : tout ce qui suit est ecrit d'apres la description publique de la
# fiche et de la discussion 21464. Chaque point que la description laisse ouvert
# est un choix declare (README.md, table « Choix declares »), pas une lecture du
# code d'origine. Evaluation : issue #18904.
#
# Contrat du rejeu en ombre (#18923, shadow/README.md) : dates par les parametres
# `start` et `end` sans valeur par defaut ; a chaque cloture, valeur du
# portefeuille dans le graphique `shadow` (series e0..e4 a tour de role), plus
# `fees` et `turnover` cumules.

from datetime import datetime

import numpy as np
import pandas as pd

GROSS = 0.98          # exposition brute visee
SIZE = 0.95           # reserve de liquidites de 5 % appliquee au dimensionnement
NAME_CAP = 0.30       # plafond par ligne (hors ligne de bons du Tresor)
DRIFT = 0.25          # coupe une ligne quand son poids depasse sa cible de 25 %
MIN_ORDER = 0.002     # ordre minimal : 0,2 % du portefeuille
BUDGETS = {1: 0.35, 2: 0.25, 3: 0.25, 4: 0.15}
TBILL = "BIL"


class _ScaledFeeModel(FeeModel):
    """Frais du courtier (modele par defaut de Lean), mis a l'echelle (identite a 1.0)."""

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class _Initializer(BrokerageModelSecurityInitializer):
    """Modeles du courtier, prix amorce a l'ajout, frais mis a l'echelle, reglement T+1."""

    def __init__(self, brokerage_model, seeder, fee_mult):
        super().__init__(brokerage_model, seeder)
        self._fee_mult = fee_mult

    def initialize(self, security):
        super().initialize(security)
        security.set_fee_model(_ScaledFeeModel(self._fee_mult))
        if security.type == SecurityType.EQUITY:
            security.set_settlement_model(DelayedSettlementModel(1, timedelta(hours=8)))


def _adx(high, low, close, n=14):
    """ADX de Wilder, colonne par colonne (une colonne par titre)."""
    up = high.diff()
    down = -low.diff()
    plus_dm = up.where((up > down) & (up > 0), 0.0)
    minus_dm = down.where((down > up) & (down > 0), 0.0)
    prev = close.shift()
    tr = np.maximum(np.maximum((high - low).values, (high - prev).abs().values),
                    (low - prev).abs().values)
    tr = pd.DataFrame(tr, index=close.index, columns=close.columns)
    alpha = 1.0 / n
    atr = tr.ewm(alpha=alpha, adjust=False).mean()
    pdi = 100 * plus_dm.ewm(alpha=alpha, adjust=False).mean() / atr
    mdi = 100 * minus_dm.ewm(alpha=alpha, adjust=False).mean() / atr
    dx = 100 * (pdi - mdi).abs() / (pdi + mdi)
    return dx.ewm(alpha=alpha, adjust=False).mean()


class FourSleeve774(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100000)
        self.start_value = 100000.0

        # Parametres de la grille pre-enregistree (#18904) ; valeurs par defaut = fiche.
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))
        self.ema_len = int(self.get_parameter("ema", "189"))
        self.adx_max = float(self.get_parameter("adx_max", "35"))
        self.stress_max = float(self.get_parameter("stress_max", "0.45"))
        self.sizing = self.get_parameter("sizing", "invvol")      # invvol | equal
        sleeve = self.get_parameter("sleeve", "all")              # all | 1 | 2 | 3 | 4
        if sleeve == "all":
            self.budgets = dict(BUDGETS)
            self.name_cap = NAME_CAP
        else:
            # Une poche seule recoit tout le portefeuille ; le plafond par ligne suit le
            # meme facteur, pour que la poche garde la composition qu'elle a dans l'ensemble.
            self.budgets = {k: (1.0 if str(k) == sleeve else 0.0) for k in BUDGETS}
            self.name_cap = NAME_CAP / BUDGETS[int(sleeve)]

        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.CASH)
        self.set_security_initializer(_Initializer(
            self.brokerage_model, FuncSecuritySeeder(self.get_last_known_prices), self.fee_mult))
        self.settings.automatic_indicator_warm_up = True

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.etf = {t: self.add_equity(t, Resolution.DAILY).symbol
                    for t in ("QQQ", "TLT", "GLD", "PSQ", TBILL)}
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol
        qqq = self.etf["QQQ"]
        self.spy_sma200 = self.sma(self.spy, 200, Resolution.DAILY)
        self.qqq_rsi = self.rsi(qqq, 10, MovingAverageType.WILDERS, Resolution.DAILY)
        self.qqq_sma20 = self.sma(qqq, 20, Resolution.DAILY)
        self.qqq_sma100 = self.sma(qqq, 100, Resolution.DAILY)
        self.tlt_roc = self.roc(self.etf["TLT"], 21, Resolution.DAILY)
        self.gld_roc = self.roc(self.etf["GLD"], 21, Resolution.DAILY)

        # Univers d'actions choisi une fois par mois (premiere seance).
        self.broad, self.top100, self.big = [], [], set()
        if any(self.budgets[k] > 0 for k in (1, 2, 3)):
            self.universe_settings.resolution = Resolution.DAILY
            self.universe_settings.schedule.on(self.date_rules.month_start(self.spy))
            self.add_universe(self._select)

        self.stock_targets = {}   # poches 1-3, recalculees chaque mois
        self.etf_targets = {}     # poche 4, recalculee chaque seance
        self.targets = {}
        self.dirty = set()        # lignes dont la cible a change et n'est pas encore atteinte
        self.stock_month = None

        # Signal sur barres closes, ordres au marche a l'ouverture de la seance suivante.
        self.schedule.on(self.date_rules.every_day(self.spy),
                         self.time_rules.before_market_open(self.spy, 20), self._session)

        self.closes = 0
        self.traded = 0.0

    # ---------------------------------------------------------------- univers

    def _select(self, fundamental):
        eligible = [f for f in fundamental
                    if f.has_fundamental_data and f.price > 5 and f.market_cap > 0
                    and f.dollar_volume > 5e6]
        eligible.sort(key=lambda f: f.market_cap, reverse=True)
        eligible = eligible[:500]
        self.broad = [f.symbol for f in eligible]
        self.top100 = self.broad[:100]
        self.big = {f.symbol for f in eligible if f.market_cap >= 5e9}
        return self.broad

    # ---------------------------------------------------------------- poches 1 a 3

    def _sleeve_weights(self, picks, vol, budget):
        """Poids dans le portefeuille d'une poche : inverse de la volatilite ou poids egaux."""
        if not picks or budget <= 0:
            return {}
        if self.sizing == "equal":
            raw = {s: 1.0 for s in picks}
        else:
            raw = {s: 1.0 / max(float(vol[s]), 1e-4) for s in picks}
        total = sum(raw.values())
        return {s: budget * v / total for s, v in raw.items()}

    def _stock_sleeves(self):
        symbols = list(self.broad)
        if not symbols:
            return None
        h = self.history(symbols, 400, Resolution.DAILY)
        if h is None or h.empty:
            return None
        close = h["close"].unstack(level=0)
        high = h["high"].unstack(level=0)
        low = h["low"].unstack(level=0)
        ok = close.iloc[-260:].notna().all() & close.iloc[-1].notna()
        close, high, low = close.loc[:, ok], high.loc[:, ok], low.loc[:, ok]
        if close.shape[1] < 50:
            return None

        last = close.iloc[-1]
        ema = close.ewm(span=self.ema_len, adjust=False).mean().iloc[-1]
        adx = _adx(high, low, close).iloc[-1]
        above = last > ema
        stress = 1.0 - float(above.mean())          # part des titres sous leur EMA
        trend_ok = above & (adx < self.adx_max)
        vol = np.log(close).diff().iloc[-63:].std()

        b1, b2, b3 = (GROSS * self.budgets[k] for k in (1, 2, 3))
        targets, tbill = {}, 0.0

        # Poche 1 : retour a la moyenne court terme, 100 plus grandes capitalisations,
        # les 10 titres les plus proches de leur plus bas des 20 dernieres seances.
        pool1 = [s for s in self.top100 if s in close.columns]
        dist = (last[pool1] / low[pool1].iloc[-20:].min() - 1.0).dropna()
        picks1 = list(dist.nsmallest(10).index)
        sleeve1 = self._sleeve_weights(picks1, vol, b1)

        # Poche 2 : momentum filtre par la tendance (au-dessus de l'EMA, ADX sous le
        # seuil), moyenne des rendements 3, 6 et 12 mois ; bons du Tresor si la part
        # des titres sous leur EMA depasse le seuil.
        sleeve2 = {}
        if stress > self.stress_max:
            tbill += b2
        else:
            score2 = ((last / close.iloc[-64] - 1) + (last / close.iloc[-127] - 1)
                      + (last / close.iloc[-253] - 1)) / 3.0
            cand2 = score2[trend_ok].dropna()
            picks2 = list(cand2.nlargest(10).index)
            sleeve2 = self._sleeve_weights(picks2, vol, b2 * len(picks2) / 10.0)
            tbill += b2 * (10 - len(picks2)) / 10.0

        # Poche 3 : momentum des grandes capitalisations (>= 5 Md$), 12 mois sauf le
        # dernier ; 10 lignes, 5 quand la part des titres sous leur EMA depasse le seuil
        # (la moitie de la poche passe alors en bons du Tresor).
        pool3 = [s for s in close.columns if s in self.big]
        score3 = (close[pool3].iloc[-22] / close[pool3].iloc[-253] - 1)[trend_ok[pool3]]
        n3 = 5 if stress > self.stress_max else 10
        picks3 = list(score3.dropna().nlargest(n3).index)
        sleeve3 = self._sleeve_weights(picks3, vol, b3 * len(picks3) / 10.0)
        tbill += b3 * (10 - len(picks3)) / 10.0

        for part in (sleeve1, sleeve2, sleeve3):
            for s, w in part.items():
                targets[s] = targets.get(s, 0.0) + w
        if tbill > 0:
            targets[self.etf[TBILL]] = targets.get(self.etf[TBILL], 0.0) + tbill
        self.log(f"stocks {self.time.date()} stress={stress:.2f} n1={len(picks1)} "
                 f"n2={len(sleeve2)} n3={len(picks3)} tbill={tbill:.3f}")
        return targets

    # ---------------------------------------------------------------- poche 4

    def _etf_sleeve(self):
        b4 = GROSS * self.budgets[4]
        if b4 <= 0:
            return {}
        e = self.etf

        def price(s):
            return float(self.securities[s].price)

        rot, trend = 0.70 * b4, 0.30 * b4
        targets = {}

        # Rotation (70 %) : actions, obligations, or, inverse.
        if price(self.spy) > self.spy_sma200.current.value:
            pick = e[TBILL] if self.qqq_rsi.current.value > 80 else e["QQQ"]
        elif self.qqq_rsi.current.value < 30:
            pick = e["QQQ"]
        elif price(e["QQQ"]) < self.qqq_sma20.current.value:
            pick = e["PSQ"]
        else:
            best = max(("TLT", "GLD"),
                       key=lambda t: (self.tlt_roc if t == "TLT" else self.gld_roc).current.value)
            roc = (self.tlt_roc if best == "TLT" else self.gld_roc).current.value
            pick = e[best] if roc > 0 else e[TBILL]
        targets[pick] = rot

        # Regime de tendance Nasdaq (30 %), echelle VIX par paliers de 0,25.
        vix = price(self.vix)
        scale = min(1.0, 20.0 / vix) if vix > 0 else 1.0
        scale = np.floor(scale * 4) / 4
        on = price(e["QQQ"]) > self.qqq_sma100.current.value
        w_qqq = trend * scale if on else 0.0
        if w_qqq > 0:
            targets[e["QQQ"]] = targets.get(e["QQQ"], 0.0) + w_qqq
        if trend - w_qqq > 0:
            targets[e[TBILL]] = targets.get(e[TBILL], 0.0) + trend - w_qqq
        return targets

    # ---------------------------------------------------------------- seance

    def _session(self):
        month = (self.time.year, self.time.month)
        if month != self.stock_month:
            if any(self.budgets[k] > 0 for k in (1, 2, 3)):
                new = self._stock_sleeves()
                if new is not None:
                    self._mark(self.stock_targets, new)
                    self.stock_targets = new
                    self.stock_month = month
            else:
                self.stock_month = month
        new_etf = self._etf_sleeve()
        self._mark(self.etf_targets, new_etf)
        self.etf_targets = new_etf

        combined = dict(self.stock_targets)
        for s, w in self.etf_targets.items():
            combined[s] = combined.get(s, 0.0) + w
        tbill = self.etf[TBILL]
        self.targets = {s: (w if s == tbill else min(w, self.name_cap))
                        for s, w in combined.items()}
        self._trade()

    def _mark(self, old, new):
        for s in set(old) | set(new):
            if abs(old.get(s, 0.0) - new.get(s, 0.0)) > 1e-9:
                self.dirty.add(s)

    def _trade(self):
        """Ordres a l'ouverture : ventes d'abord, achats dans la limite des liquidites reglees.

        Un achat qui ne tient pas dans les liquidites est reduit et sa ligne reste a
        completer : il repart a la seance suivante (ventes reglees en T+1)."""
        tpv = float(self.portfolio.total_portfolio_value)
        if tpv <= 0:
            return
        self.transactions.cancel_open_orders()
        held = {s for s, h in self.portfolio.items() if h.invested}
        sells, buys = [], []
        for s in set(self.targets) | held:
            price = float(self.securities[s].price)
            if price <= 0:
                continue
            qty = float(self.portfolio[s].quantity)
            w = self.targets.get(s, 0.0)
            if w <= 0:
                if qty > 0:
                    sells.append((s, -qty))
                self.dirty.discard(s)
                continue
            cur = qty * price / tpv
            if s not in self.dirty and cur <= w * (1 + DRIFT):
                continue
            want = int(w * tpv * SIZE / price)
            delta = want - qty
            if abs(delta) * price < MIN_ORDER * tpv:
                self.dirty.discard(s)
                continue
            if delta < 0:
                sells.append((s, delta))
                self.dirty.discard(s)
            elif s in self.dirty:
                buys.append((s, delta, price))
        for s, q in sells:
            self.market_on_open_order(s, int(q))
        cash = float(self.portfolio.cash_book["USD"].amount)
        need = sum(q * p for _, q, p in buys)
        scale = min(1.0, max(0.0, 0.97 * cash / need)) if need > 0 else 0.0
        for s, q, p in buys:
            n = int(q * scale)
            if n > 0 and n * p >= MIN_ORDER * tpv:
                self.market_on_open_order(s, n)
            if n == int(q):
                self.dirty.discard(s)

    # ---------------------------------------------------------------- contrat ombre

    def on_order_event(self, event):
        if event.status == OrderStatus.INVALID:
            self.dirty.add(event.symbol)    # ordre refuse : la ligne repart a la seance suivante
            return
        if event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(event.fill_quantity * event.fill_price)
                            / self.portfolio.total_portfolio_value)

    def on_data(self, data):
        if not data.bars.contains_key(self.spy):
            return
        self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
        self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
        self.plot("shadow", "turnover", self.traded)
        self.closes += 1
