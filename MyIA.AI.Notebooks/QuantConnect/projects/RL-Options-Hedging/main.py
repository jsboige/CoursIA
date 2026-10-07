# RL Options Hedging (Ch07-01) - couverture d'une short call par RL vs delta BS
# Portage du chapitre 07-01 de Hands-On AI Trading - issue #18902.
#
# Double comptabilite : le livre "delta" (h = delta_BS chaque seance) et le
# livre "rl" (h = a(etat) * delta_BS, politique PPO du notebook research.ipynb,
# exportee dans rl_policy.py) couvrent LA MEME position courte d'un call ATM
# ~30 jours sur SPY. La difference entre les deux livres vient uniquement du
# chemin de couverture ; les frais y sont comptes par livre, comme dans le
# notebook (pas de fee model QC : la comptabilite par livre fait foi).
#
# Tout se joue sur la cloture quotidienne (bar DAILY), meme convention que le
# notebook : P&L de couverture du jour = h detenue * (close - close_veille).

from AlgorithmImports import *

from rl_policy import RLPolicy  # genere depuis research.ipynb (section 8)

from scipy.stats import norm


def bs_delta_gamma(S, K, sigma, tau):
    """Delta et gamma BS (r=0, q=0), memes formules que research.ipynb."""
    tau = max(tau, 1e-8)
    sig = max(sigma, 1e-8)
    d1 = (np.log(S / K) + 0.5 * sig * sig * tau) / (sig * np.sqrt(tau))
    delta = norm.cdf(d1)
    gamma = norm.pdf(d1) / (S * sig * np.sqrt(tau))
    return delta, gamma


class RLOptionsHedgingAlgorithm(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start", "2018-01-01"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end", "2024-12-31"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(1_000_000)

        self.fee_bps = float(self.get_parameter("fee_bps", "5"))
        self.sigma_lookback = int(self.get_parameter("sigma_lookback", "30"))
        self.dte_target = int(self.get_parameter("dte_target", "30"))

        self.underlying = self.add_equity("SPY", Resolution.DAILY).symbol
        self.option = self.add_option("SPY", Resolution.DAILY)
        self.option.set_filter(-1, +1, timedelta(20), timedelta(45))
        self.option_symbol = self.option.symbol

        self.contracts = 1          # short 1 call = 100 actions de notionnel
        self.multiplier = 100
        self.rets = []
        self.last_close = None

        # Livres de comptabilite par voie de couverture.
        self.books = {name: {"pnl": 0.0, "h": 0.0, "series": []}
                      for name in ("delta", "rl")}
        self.current_option = None

        self.set_warm_up(timedelta(45))

    # ---------------------------------------------------------------- donnees
    def on_data(self, data):
        bar = data.bars.get(self.underlying)
        if bar is None:
            return
        close = float(bar.close)
        if self.is_warming_up:
            # Le warm-up remplit la fenetre de vol (sinon le premier cycle
            # ouvrirait non couvert pendant sigma_lookback seances).
            self._record_close(close)
            return

        # 1) P&L de couverture du jour (h detenue hier, variation du jour).
        if self.last_close is not None:
            for book in self.books.values():
                book["pnl"] += book["h"] * (close - self.last_close)

        # 2) Reglement si l'option tenue est echue.
        if self.current_option is not None and self.time.date() >= self.current_option.id.date:
            payoff = max(close - float(self.current_option.id.strike_price), 0.0)
            payoff *= self.multiplier * self.contracts
            for book in self.books.values():
                book["pnl"] -= payoff
                book["h"] = 0.0
            self.liquidate()
            self.current_option = None

        # 3) Fenetre de rendements -> vol realisee.
        self._record_close(close)

        # 4) Nouveau cycle si aucun en cours.
        if self.current_option is None:
            self.open_cycle(data, close)

        # 5) Couverture des deux livres.
        self.rebalance(close)

        for name, book in self.books.items():
            book["series"].append(book["pnl"])

    def _record_close(self, close):
        if self.last_close:
            self.rets.append(close / self.last_close - 1.0)
            self.rets = self.rets[-self.sigma_lookback:]
        self.last_close = close

    # --------------------------------------------------------------- cycle
    def open_cycle(self, data, spot):
        """Vend le call ~30 DTM le plus proche de l'ATM."""
        chain = data.option_chains.get(self.option_symbol)
        if chain is None:
            return
        calls = [c for c in chain
                 if c.right == OptionRight.CALL
                 and (c.symbol.id.date - self.time).days >= 7
                 and c.ask > 0]
        if not calls:
            return
        # ATM d'abord, puis DTM le plus proche de la cible.
        best = min(calls, key=lambda c: (abs(c.strike_price - spot),
                                         abs((c.symbol.id.date - self.time).days - self.dte_target)))
        self.sell(best.symbol, self.contracts)
        self.current_option = best.symbol
        premium = float(best.ask) * self.multiplier * self.contracts
        for book in self.books.values():
            book["pnl"] += premium

    # ------------------------------------------------------------ couverture
    def rebalance(self, spot):
        if self.current_option is None or len(self.rets) < self.sigma_lookback:
            return
        sigma = float(np.std(self.rets, ddof=1)) * np.sqrt(252.0)
        K = float(self.current_option.id.strike_price)
        dte = max((self.current_option.id.date - self.time).days, 1)
        tau = dte / 365.0

        delta, gamma = bs_delta_gamma(spot, K, sigma, tau)
        state = np.array([spot / K - 1.0, tau, delta, 100.0 * gamma,
                          self.books["rl"]["h"] / (self.multiplier * self.contracts)])
        ratio = float(np.clip(RLPolicy.act(state), 0.0, 1.0))

        targets = {"delta": delta, "rl": ratio * delta}
        total_shares = 0.0
        for name, h_ratio in targets.items():
            book = self.books[name]
            h_new = h_ratio * self.multiplier * self.contracts
            traded = abs(h_new - book["h"]) * spot
            book["pnl"] -= traded * self.fee_bps / 10_000.0
            book["h"] = h_new
            total_shares += h_new
        self.plot("Couverture", "h_delta", targets["delta"])
        self.plot("Couverture", "h_rl", targets["rl"])

        # Une seule position reelle = somme des deux livres.
        held = float(self.portfolio[self.underlying].quantity)
        diff = total_shares - held
        if abs(diff) >= 1.0:
            if diff > 0:
                self.buy(self.underlying, int(diff))
            else:
                self.sell(self.underlying, int(-diff))

    # ------------------------------------------------------------- final
    def on_end_of_algorithm(self):
        for name, book in self.books.items():
            series = [p for p in book["series"]]
            if len(series) < 2:
                self.log(f"LIVRE {name}: serie trop courte")
                continue
            daily = np.diff(np.array(series))
            var = float(np.var(daily))
            k = max(1, int(np.ceil(0.05 * len(daily))))
            cvar = float(np.mean(np.sort(daily)[:k]))
            self.log(f"LIVRE {name}: pnl_total={series[-1]:,.0f}  "
                     f"var_daily={var:,.0f}  cvar95_daily={cvar:,.0f}")
