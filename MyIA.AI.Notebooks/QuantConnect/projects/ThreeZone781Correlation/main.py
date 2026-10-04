# Correlations hebdomadaires : strategie 781 (reimplementation) vs paniers ETF
# des allocations du depot (issue #18905, point 3).
#
# - l'algorithme principal EST la 781 (meme logique que
#   ThreeZoneSPYDrawdownRotation) : sa serie de retours hebdo est son equity ;
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
# - sorties : set_summary_statistic (si disponible) + ObjectStore JSON + log.
#
# Fenetre par defaut : 2018-01-01 -> 2024-12-31 = fenetre commune aux trois
# allocations du depot (VT2 2018-2025, AW 2015-2024, TW 2015-2025).

from AlgorithmImports import *

import json


class _ScaledFeeModel(FeeModel):
    """Frais IBKR mis a l'echelle (identite a 1.0, cf #18905 point 4)."""

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class ThreeZone781Correlation(QCAlgorithm):

    def initialize(self):
        start = self.get_parameter("start_date", "2018-01-01").split("-")
        end = self.get_parameter("end_date", "2024-12-31").split("-")
        self.set_start_date(int(start[0]), int(start[1]), int(start[2]))
        self.set_end_date(int(end[0]), int(end[1]), int(end[2]))
        self.set_cash(100000)

        self.set_security_initializer(self._ibkr_fees)

        # --- parametres 781 (identiques au projet principal) ---
        self.zone1_dd = float(self.get_parameter("zone1_dd", "0.05"))
        self.zone2_dd = float(self.get_parameter("zone2_dd", "0.10"))
        self.top_n = int(self.get_parameter("top_n", "20"))
        self.min_yield = float(self.get_parameter("min_yield", "0.03"))
        self.payout_min = float(self.get_parameter("payout_min", "0.05"))
        self.payout_max = float(self.get_parameter("payout_max", "0.80"))
        self.div_hist_years = int(self.get_parameter("div_hist_years", "10"))
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # --- paniers ombre ---
        self.baskets = {
            "VT2": {"SPY": 0.25, "QQQ": 0.25, "IEF": 0.25, "GLD": 0.25},
            "AW": {"SPY": 0.30, "IEF": 0.30, "GLD": 0.30, "XLP": 0.10},
            "TW": {"SPY": 0.30, "IEF": 0.30, "GLD": 0.30, "XLP": 0.10},
        }
        etf_tickers = sorted({t for w in self.baskets.values() for t in w})
        self.etf_symbols = {}
        for t in etf_tickers:
            self.etf_symbols[t] = self.add_equity(t, Resolution.DAILY).symbol

        # series hebdo : valeur de panier ombre (base 1.0) + closes ETF
        self._basket_value = {name: 1.0 for name in self.baskets}
        self._last_close = {}
        self._weekly = []  # (date iso, {name: ret, "781": ret})

        # --- 781 ---
        self._fine_selected = []
        self._div_cache = {}
        self._div_cache_month = None
        self._zone = None

        self.universe_settings.resolution = Resolution.DAILY
        self.add_universe(self._select_coarse, self._select_fine)

        self.schedule.on(
            self.date_rules.week_start(self.spy),
            self.time_rules.after_market_open(self.spy, 30),
            self._rebalance,
        )
        # Echantillonnage hebdo le vendredi (cloture, garde weekday).
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.before_market_close(self.spy, 1),
            self._sample_week,
        )

    def _ibkr_fees(self, security):
        security.set_fee_model(_ScaledFeeModel(self.fee_mult))

    # --- 781 : univers, dividende, rotation (identiques au projet principal) ---

    def _select_coarse(self, coarse):
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
            if not pe or pe <= 0:
                continue
            payout = dy * pe
            if not (self.payout_min <= payout <= self.payout_max):
                continue
            if f.market_cap < 2e9:
                continue
            picked.append((f.symbol, dy))
        picked.sort(key=lambda x: x[1], reverse=True)
        self._fine_selected = [s for s, _ in picked[:40]]
        return self._fine_selected

    def _dividend_history_ok(self, symbol):
        if symbol in self._div_cache:
            return self._div_cache[symbol]
        try:
            # Type de donnees Dividend (la classe, pas une instance) : la forme
            # self.history(self.dividends, ...) leve une AttributeError sur
            # QCAlgorithm (Lean master 18155) et rejettait TOUT titre.
            df = self.history(
                Dividend, symbol,
                timedelta(days=365 * (self.div_hist_years + 1)),
            )
        except Exception as exc:
            self.debug(f"dividend history error {symbol}: {exc}")
            self._div_cache[symbol] = False
            return False
        if df is None or df.empty:
            self._div_cache[symbol] = False
            return False
        index = df.index
        if hasattr(index, "levels"):
            times = index.get_level_values(-1)
        else:
            times = index
        years = {t.year for t in times}
        this_year = self.time.year
        span = {y for y in years
                if this_year - self.div_hist_years <= y < this_year}
        ok = len(span) >= self.div_hist_years - 2
        self._div_cache[symbol] = ok
        return ok

    def _refresh_div_cache_monthly(self):
        key = (self.time.year, self.time.month)
        if key != self._div_cache_month:
            self._div_cache_month = key
            self._div_cache = {}

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

        targets = [PortfolioTarget(s, 0.0)
                   for s, h in self.portfolio.items()
                   if h.invested and s not in weights]
        targets += [PortfolioTarget(s, w) for s, w in weights.items()]
        if targets:
            self.set_holdings(targets, True)

    def on_securities_changed(self, changes):
        for r in changes.removed_securities:
            if r.symbol != self.spy and self.portfolio[r.symbol].invested:
                self.liquidate(r.symbol)

    # --- echantillonnage hebdo ---

    def _sample_week(self):
        # vendredi uniquement (weekday(): lundi=0 ... vendredi=4).
        if self.time.weekday() != 4:
            return
        # Close courant des ETF (deja dans le carnet) ; retours hebdo par titre.
        rets = {}
        for t, sym in self.etf_symbols.items():
            px = float(self.securities[sym].close)
            prev = self._last_close.get(t)
            self._last_close[t] = px
            if prev and prev > 0:
                rets[t] = px / prev - 1.0
        if not rets:
            return

        # Retour de chaque panier ombre (poids cibles, drift intra-mois ignore).
        for name, w in self.baskets.items():
            r = sum(w[t] * rets.get(t, 0.0) for t in w)
            self._basket_value[name] *= (1.0 + r)

        # Retour hebdo de la 781 = variation de son equity.
        eq = float(self.portfolio.total_portfolio_value)
        prev_eq = getattr(self, "_last_equity", None)
        self._last_equity = eq
        if prev_eq and prev_eq > 0:
            self._weekly.append((str(self.time.date()),
                                 {**{n: self._basket_value[n] for n in self.baskets},
                                  "781": eq / prev_eq - 1.0}))
        # Rebalance mensuel des paniers ombre : les valeurs restent base 1.0,
        # les poids cibles sont appliques au calcul lineaire ci-dessus chaque
        # semaine (approximation declaree : drift intra-mois ignore).

    @staticmethod
    def _pearson(xs, ys):
        n = len(xs)
        if n < 3:
            return None
        mx = sum(xs) / n
        my = sum(ys) / n
        sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        sxx = sum((x - mx) ** 2 for x in xs)
        syy = sum((y - my) ** 2 for y in ys)
        if sxx <= 0 or syy <= 0:
            return None
        return sxy / (sxx ** 0.5 * syy ** 0.5)

    def on_end_of_algorithm(self):
        # Series de retours hebdo des paniers (variation de valeur ombre).
        result = {"window": f"{self.start_date.date()}..{self.end_date.date()}",
                  "weeks": len(self._weekly), "corr": {}, "corr_by_year": {}}
        if len(self._weekly) >= 4:
            r781 = [w["781"] for _, w in self._weekly]
            for name in self.baskets:
                rb = []
                prev = None
                for _, w in self._weekly:
                    cur = w[name]
                    rb.append(cur / prev - 1.0 if prev else 0.0)
                    prev = cur
                result["corr"][name] = self._pearson(r781, rb)
            # par annee civile
            years = sorted({d[:4] for d, _ in self._weekly})
            for y in years:
                idx = [i for i, (d, _) in enumerate(self._weekly)
                       if d.startswith(y)]
                if len(idx) < 10:
                    continue
                r781y = [self._weekly[i][1]["781"] for i in idx]
                for name in self.baskets:
                    prev = None
                    rby = []
                    for i in idx:
                        cur = self._weekly[i][1][name]
                        rby.append(cur / prev - 1.0 if prev else 0.0)
                        prev = cur
                    c = self._pearson(r781y, rby)
                    result["corr_by_year"].setdefault(name, {})[y] = c

        payload = json.dumps(result, indent=1, default=str)
        self.log(f"CORR-RESULT {payload}")
        try:
            self.object_store.save("781_corr.json", payload)
        except Exception as exc:
            self.debug(f"object store save failed: {exc}")
        # statistiques custom (best effort, selon disponibilite de l'API)
        try:
            for name, c in (result["corr"] or {}).items():
                if c is not None:
                    self.set_summary_statistic(f"corr_{name}", f"{c:.4f}")
        except Exception as exc:
            self.debug(f"summary statistic failed: {exc}")