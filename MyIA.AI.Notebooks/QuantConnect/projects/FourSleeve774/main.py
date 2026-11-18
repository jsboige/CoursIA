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
# Parametre `layout=775` : reimplementation declaree de la strategie 775 du meme
# auteur, « Adaptive ETF and Stock Momentum » (v1.0.1 du 28/09/2026, discussion
# 21465), qui recombine les briques de la 774 : poche d'ETF tactiques (45 %) avec
# ETF a levier x3 et inverses, poche de momentum des grandes capitalisations (55 %)
# avec sortie de largeur. Choix declares et regle de verdict : issue #20168.
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
# 775 : poche actions (cle 3) et poche ETF (cle 4) ; les poches 1 et 2 sont vides.
BUDGETS_775 = {1: 0.0, 2: 0.0, 3: 0.55, 4: 0.45}
TBILL_775 = "SHV"
ETF_775 = ("QQQ", "TLT", "IEF", "BSV", "GLD", "SHV", "SMH", "TQQQ", "SQQQ", "SOXL", "PSQ")
X3 = ("TQQQ", "SOXL", "SQQQ")
# lev=1 : chaque ETF x3 execute par son equivalent x1 (le signal ne change pas).
LEV1 = {"TQQQ": "QQQ", "SOXL": "SMH", "SQQQ": "PSQ"}
BAND_WINDOW = 200     # seances du rang centile du stress (indice de bande, 775)
OUT_DAYS = 180        # retour d'office apres une sortie de largeur (775)


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
        self.layout = self.get_parameter("layout", "774")         # 774 | 775
        if self.layout not in ("774", "775"):
            raise ValueError(f"layout inconnu : {self.layout}")
        base = BUDGETS if self.layout == "774" else BUDGETS_775
        sleeve = self.get_parameter("sleeve", "all")              # 774 : all | 1 | 2 | 3 | 4
        if self.layout == "775":                                  # 775 : all | stock | etf
            sleeve = {"all": "all", "stock": "3", "etf": "4"}[sleeve]
        lev = self.get_parameter("lev", "3")                      # 775 : 3 | 1
        if lev not in ("3", "1"):
            raise ValueError(f"lev inconnu : {lev}")
        self.exec_map = LEV1 if lev == "1" else {}
        if sleeve == "all":
            self.budgets = dict(base)
            self.name_cap = NAME_CAP
        else:
            # Une poche seule recoit tout le portefeuille ; le plafond par ligne suit le
            # meme facteur, pour que la poche garde la composition qu'elle a dans l'ensemble.
            self.budgets = {k: (1.0 if str(k) == sleeve else 0.0) for k in base}
            self.name_cap = NAME_CAP / base[int(sleeve)]

        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.CASH)
        self.set_security_initializer(_Initializer(
            self.brokerage_model, FuncSecuritySeeder(self.get_last_known_prices), self.fee_mult))
        self.settings.automatic_indicator_warm_up = True

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        tickers = ("QQQ", "TLT", "GLD", "PSQ", TBILL) if self.layout == "774" else ETF_775
        self.etf = {t: self.add_equity(t, Resolution.DAILY).symbol for t in tickers}
        self.tbill = self.etf[TBILL if self.layout == "774" else TBILL_775]
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol
        qqq = self.etf["QQQ"]
        self.spy_sma200 = self.sma(self.spy, 200, Resolution.DAILY)
        self.qqq_rsi = self.rsi(qqq, 10, MovingAverageType.WILDERS, Resolution.DAILY)
        self.qqq_sma20 = self.sma(qqq, 20, Resolution.DAILY)
        self.qqq_sma100 = self.sma(qqq, 100, Resolution.DAILY)
        self.tlt_roc = self.roc(self.etf["TLT"], 21, Resolution.DAILY)
        self.gld_roc = self.roc(self.etf["GLD"], 21, Resolution.DAILY)
        if self.layout == "775":
            e = self.etf
            self.smh_rsi = self.rsi(e["SMH"], 10, MovingAverageType.WILDERS, Resolution.DAILY)
            self.sqqq_rsi = self.rsi(e["SQQQ"], 10, MovingAverageType.WILDERS, Resolution.DAILY)
            self.bsv_rsi = self.rsi(e["BSV"], 10, MovingAverageType.WILDERS, Resolution.DAILY)
            self.ief_roc = self.roc(e["IEF"], 21, Resolution.DAILY)
            self.vix_sma20 = self.sma(self.vix, 20, Resolution.DAILY)
        self.breadth_out = None   # 775 : date de la sortie de largeur en cours
        self.days = self.days_x3 = self.days_out = 0

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
        h = self.history(symbols, 400 if self.layout == "774" else 600, Resolution.DAILY)
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
        ema_full = close.ewm(span=self.ema_len, adjust=False).mean()
        ema = ema_full.iloc[-1]
        adx = _adx(high, low, close).iloc[-1]
        above = last > ema
        stress = 1.0 - float(above.mean())          # part des titres sous leur EMA
        trend_ok = above & (adx < self.adx_max)
        vol = np.log(close).diff().iloc[-63:].std()
        if self.layout == "775":
            return self._stock_775(close, last, ema_full, trend_ok, stress)

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
            targets[self.tbill] = targets.get(self.tbill, 0.0) + tbill
        self.log(f"stocks {self.time.date()} stress={stress:.2f} n1={len(picks1)} "
                 f"n2={len(sleeve2)} n3={len(picks3)} tbill={tbill:.3f}")
        return targets

    def _stock_775(self, close, last, ema_full, trend_ok, stress):
        """Poche actions de la 775 (#20168) : momentum des grandes capitalisations,
        mis a l'echelle par l'indice de bande, sortie de largeur avec retour d'office."""
        b = GROSS * self.budgets[3]
        # Indice de bande : rang centile du stress du jour parmi les stress quotidiens
        # des BAND_WINDOW dernieres seances.
        hist = close.lt(ema_full).iloc[-BAND_WINDOW:].mean(axis=1)
        band = float((hist <= stress + 1e-12).mean())

        today = self.time.date()
        if self.breadth_out is None:
            if stress > self.stress_max:
                self.breadth_out = today
        elif stress <= self.stress_max or (today - self.breadth_out).days >= OUT_DAYS:
            self.breadth_out = None
        if self.breadth_out is not None:
            self.log(f"stocks775 {today} stress={stress:.2f} band={band:.2f} out")
            return {self.tbill: b}

        n = 5 if band >= 0.5 else 10
        pool = [s for s in close.columns if s in self.big]
        score = ((last[pool] / close[pool].iloc[-64] - 1)
                 + (last[pool] / close[pool].iloc[-127] - 1)
                 + (last[pool] / close[pool].iloc[-253] - 1)) / 3.0
        cand = score[trend_ok[pool]].dropna()
        picks = cand[cand > 0].nlargest(n)
        filled = b * (1.0 - band / 2.0) * len(picks) / n
        targets = ({s: filled * float(v) / float(picks.sum()) for s, v in picks.items()}
                   if len(picks) else {})
        if b - filled > 0:
            targets[self.tbill] = targets.get(self.tbill, 0.0) + b - filled
        self.log(f"stocks775 {today} stress={stress:.2f} band={band:.2f} "
                 f"n={len(picks)}/{n} tbill={b - filled:.3f}")
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

    def _etf_775(self):
        """Poche ETF de la 775 (#20168) : rotation (70 %) et tendance Nasdaq (30 %)."""
        b4 = GROSS * self.budgets[4]
        if b4 <= 0:
            return {}
        e = self.etf

        def price(s):
            return float(self.securities[s].price)

        targets = {}

        def add(ticker, w):
            if w > 0:
                s = e[self.exec_map.get(ticker, ticker)]
                targets[s] = targets.get(s, 0.0) + w

        rot, trend = 0.70 * b4, 0.30 * b4

        # Rotation (70 %).
        qrsi = self.qqq_rsi.current.value
        if price(self.spy) > self.spy_sma200.current.value:
            pick = TBILL_775 if qrsi > 79 else "TQQQ"
        elif qrsi < 30:
            pick = "TQQQ"
        elif self.smh_rsi.current.value < 30:
            pick = "SOXL"
        elif price(e["QQQ"]) < self.qqq_sma20.current.value:
            pick = "SQQQ" if self.sqqq_rsi.current.value > self.bsv_rsi.current.value else "BSV"
        else:
            rocs = {"TLT": self.tlt_roc.current.value, "IEF": self.ief_roc.current.value,
                    "GLD": self.gld_roc.current.value}
            best = max(rocs, key=rocs.get)
            pick = best if rocs[best] > 0 else TBILL_775
        add(pick, rot)

        # Tendance Nasdaq (30 %) : echelle VIX par paliers de 0,25, ratio VIX / moyenne 20 j.
        vix = price(self.vix)
        scale = np.floor(min(1.0, 20.0 / vix) * 4) / 4 if vix > 0 else 1.0
        vsma = self.vix_sma20.current.value
        ratio = vix / vsma if vsma > 0 else 1.0
        q = price(e["QQQ"])
        w = 0.0
        if q > self.qqq_sma100.current.value:
            w = trend * scale
            add("TQQQ", w)
        elif q > self.qqq_sma20.current.value and ratio < 1.0:
            w = trend * scale                      # motif de retournement
            add("QQQ", w)
        elif ratio > 1.2:
            w = trend * 0.25
            add("SQQQ", w)
        add(TBILL_775, trend - w)
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
        new_etf = self._etf_775() if self.layout == "775" else self._etf_sleeve()
        self._mark(self.etf_targets, new_etf)
        self.etf_targets = new_etf

        combined = dict(self.stock_targets)
        for s, w in self.etf_targets.items():
            combined[s] = combined.get(s, 0.0) + w
        tbill = self.tbill
        self.targets = {s: (w if s == tbill else min(w, self.name_cap))
                        for s, w in combined.items()}
        if self.layout == "775":
            x3 = {self.etf[t] for t in X3 if t not in self.exec_map}
            self.days += 1
            self.days_x3 += any(self.targets.get(s, 0.0) > 0 for s in x3)
            self.days_out += self.breadth_out is not None
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

    def on_end_of_algorithm(self):
        if self.layout == "775" and self.days:
            self.set_runtime_statistic("days_x3", f"{self.days_x3 / self.days:.4f}")
            self.set_runtime_statistic("days_out", f"{self.days_out / self.days:.4f}")
