# Correlations hebdomadaires : strategie 46 sans levier (reimplementation)
# vs paniers ETF des allocations du depot (issue #18906, point 4).
#
# - l'algorithme embarque EST la strategie 46 en mode "unlevered" (meme logique
#   que Paradox46VolScaledMomentum) : sa serie de retours hebdo est son equity ;
# - chaque panier d'allocation est suivi en portefeuille OMBRE (poids cibles du
#   depot, rebalance mensuel), separe du portefeuille reel :
#     * VT2 : SPY/QQQ/IEF/GLD poids egaux (proxy declare de la variante 2
#       ERC de Cloud-VolTargeting) ;
#     * AW  : SPY 0.30 / IEF 0.30 / GLD 0.30 / XLP 0.10 (AllWeather v5.0) ;
#     * TW  : sleeve AllWeather seul (SPY 0.30 / IEF 0.30 / GLD 0.30 / XLP
#       0.10) -- la jambe 75 % stock-picking de Framework_Composite_TrendWeather
#       n'est PAS repliquee (declare) ;
# - retours hebdo echantillonnes le vendredi ; correlations de Pearson in fine
#   sur la periode pleine et par annee civile ;
# - sorties : ObjectStore JSON + log.
#
# Fenetre par defaut : 2018-01-01 -> 2024-12-31 = fenetre commune aux trois
# allocations du depot (VT2 2018-2025, AW 2015-2024, TW 2015-2025).

from AlgorithmImports import *

import json

import numpy as np


class _ScaledFeeModel(FeeModel):
    """Frais IBKR mis a l'echelle (identite a 1.0, cf #18906 point 4)."""

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


class Paradox46Correlation(QCAlgorithm):

    def initialize(self):
        start = self.get_parameter("start_date", "2018-01-01").split("-")
        end = self.get_parameter("end_date", "2024-12-31").split("-")
        self.set_start_date(int(start[0]), int(start[1]), int(start[2]))
        self.set_end_date(int(end[0]), int(end[1]), int(end[2]))
        self.set_cash(100000)

        self.set_security_initializer(self._ibkr_fees)

        # --- parametres strategie 46 (identiques au projet principal) ---
        self.universe_mode = self.get_parameter("universe_mode", "unlevered")
        self.w_short = int(self.get_parameter("w_short", "21"))
        self.w_medium = int(self.get_parameter("w_medium", "63"))
        self.w_inter = int(self.get_parameter("w_inter", "126"))
        self.vol_window = int(self.get_parameter("vol_window", "20"))
        self.sma_days = int(self.get_parameter("sma_days", "50"))
        self.rsi_days = int(self.get_parameter("rsi_days", "14"))
        self.rsi_cap = float(self.get_parameter("rsi_cap", "70"))
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))

        self._symbols = [self.add_equity(t, Resolution.DAILY).symbol
                        for t in UNIVERSES[self.universe_mode]]
        self._bench = self.add_equity("SPY", Resolution.DAILY).symbol
        self.set_benchmark(self._bench)
        self.lookback_days = max(self.w_inter, self.sma_days) + 10

        # --- paniers ombre (meme convention que ThreeZone781Correlation) ---
        self.baskets = {
            "VT2": {"SPY": 0.25, "QQQ": 0.25, "IEF": 0.25, "GLD": 0.25},
            "AW": {"SPY": 0.30, "IEF": 0.30, "GLD": 0.30, "XLP": 0.10},
            "TW": {"SPY": 0.30, "IEF": 0.30, "GLD": 0.30, "XLP": 0.10},
        }
        etf_tickers = sorted({t for w in self.baskets.values() for t in w})
        self.etf_symbols = {t: self.add_equity(t, Resolution.DAILY).symbol
                            for t in etf_tickers}

        # series hebdo : panier ombre en ALLOCATIONS DE CAPITAL. Au rebalance
        # mensuel, les quantites sont fixees aux prix du jour (w_i * notional /
        # prix_i) ; entre deux rebalances la valeur est chainee de vendredi en
        # vendredi -- le rendement ne s'efface pas au franchissement de mois
        # (reserve adjoint #19082, temoin 3).
        self.basket_notional = 1_000_000.0  # base arbitraire, seuls les ratios comptent
        self._basket_qty = {}  # {panier: {ticker: quantite}} au rebalance mensuel
        self._basket_prev = {}  # {panier: valeur au vendredi precedent}
        self._last_equity = None
        self._weekly = []  # {date, <panier>: ret, "P46": ret}

        self._target = None

        # Rotation quotidienne de la strategie 46.
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.after_market_open(self._bench, 30),
            self._rebalance,
        )
        # Rebasage mensuel des paniers ombre (rebalance mensuel exact).
        self.schedule.on(
            self.date_rules.month_start(self._bench),
            self.time_rules.after_market_open(self._bench, 45),
            self._reset_baskets,
        )
        # Echantillonnage hebdo le vendredi avant cloture (garde weekday).
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.before_market_close(self._bench, 1),
            self._sample_week,
        )

    def _ibkr_fees(self, security):
        security.set_fee_model(_ScaledFeeModel(self.fee_mult))

    # --- jambe strategie 46 (copie conforme du projet principal) ------------

    def _stats(self, symbol):
        bars = self.history(symbol, self.lookback_days, Resolution.DAILY)
        closes = bars["close"].to_numpy()[::-1]  # plus recent en tete
        if len(closes) < self.w_inter + 1:
            return None

        # Rendement du jour = recent / veille (plus recent en tete : element i
        # sur element i+1). Signe inverse dans l'ancienne forme -- reserve
        # adjoint #19082, temoin 2.
        rets = closes[:-1] / closes[1:] - 1.0

        def window_return(n):
            if len(closes) < n + 1:
                return None
            # Cloture d'il y a n seances a l'indice n (plus recent en tete) ;
            # l'ancien closes[-1-n] indexait depuis la fin de l'historique
            # (reserve adjoint #19082, temoin 1).
            return closes[0] / closes[n] - 1.0

        r_s = window_return(self.w_short)
        r_m = window_return(self.w_medium)
        r_i = window_return(self.w_inter)
        if r_s is None or r_m is None or r_i is None:
            return None

        vol = float(np.std(rets[: self.vol_window])) if len(rets) >= self.vol_window else None
        if not vol or vol <= 0:
            return None

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
            if st["sma"] is None or st["close"] <= st["sma"]:
                continue
            score = st["score"]
            if st["rsi"] is not None and st["rsi"] > self.rsi_cap:
                score = score / (1.0 + (st["rsi"] - self.rsi_cap) / 20.0)
            if score <= 0:
                continue
            if score > best_score:
                best_symbol, best_score = symbol, score

        target = best_symbol if best_symbol is not None else None
        if target != self._target:
            self._target = target
            if target is None:
                self.liquidate()
            else:
                self.set_holdings(target, 1.0)

    # --- paniers ombre -------------------------------------------------------

    def _basket_value(self, closes, qty):
        return sum(q * closes.get(t, 0.0) for t, q in qty.items())

    def _reset_baskets(self):
        closes = self._current_closes()
        if not closes:
            return
        for name, weights in self.baskets.items():
            # Allocation de capital : chaque poids w_i alloue w_i du notional
            # en titres au prix de rebalance. Entre deux rebalances les poids
            # derivent avec les prix (portefeuille ombre achete-au-rebalance,
            # pas poids x prix remesures chaque semaine).
            self._basket_qty[name] = {
                t: w * self.basket_notional / closes[t]
                for t, w in weights.items() if t in closes and closes[t] > 0
            }

    def _current_closes(self):
        closes = {}
        for t, symbol in self.etf_symbols.items():
            if symbol in self.securities and self.securities[symbol].price:
                closes[t] = float(self.securities[symbol].price)
        return closes

    def _sample_week(self):
        if self.time.weekday() != 4:  # vendredi
            return
        closes = self._current_closes()
        if not closes or not self._basket_qty:
            return

        row = {"date": str(self.time.date())}
        for name, qty in self._basket_qty.items():
            # Rendement vendredi-a-vendredi de la valeur chainee : le
            # rebalance mensuel change les quantites, jamais la chaine --
            # meme convention que la jambe P46 (equity / equity du vendredi
            # precedent).
            value = self._basket_value(closes, qty)
            prev = self._basket_prev.get(name)
            if prev:
                row[name] = value / prev - 1.0
            self._basket_prev[name] = value
        equity = float(self.portfolio.total_portfolio_value)
        if self._last_equity:
            row["P46"] = equity / self._last_equity - 1.0
        self._last_equity = equity
        self._weekly.append(row)

    def on_end_of_algorithm(self):
        # Correlations de Pearson : periode pleine puis par annee civile.
        def pearson(xs, ys):
            if len(xs) < 3:
                return None
            xa, ya = np.array(xs), np.array(ys)
            if xa.std() == 0 or ya.std() == 0:
                return None
            return float(np.corrcoef(xa, ya)[0, 1])

        out = {"full": {}, "by_year": {}}
        valid = [r for r in self._weekly if "P46" in r and all(k in r for k in self.baskets)]
        for name in self.baskets:
            out["full"][name] = pearson(
                [r["P46"] for r in valid], [r[name] for r in valid]
            )
        years = sorted({r["date"][:4] for r in valid})
        for y in years:
            rows = [r for r in valid if r["date"].startswith(y)]
            out["by_year"][y] = {
                name: pearson([r["P46"] for r in rows], [r[name] for r in rows])
                for name in self.baskets
            }
        self.log("CORRELATIONS " + json.dumps(out))
        try:
            self.object_store.save_bytes(
                "paradox46_correlations.json",
                json.dumps(out, indent=1).encode("utf-8"),
            )
        except Exception as exc:  # ObjectStore indisponible : le log reste la trace
            self.log(f"ObjectStore indisponible ({exc}) -- correlations dans le log")
