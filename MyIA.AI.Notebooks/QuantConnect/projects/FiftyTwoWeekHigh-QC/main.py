from AlgorithmImports import *
from datetime import date

# Fixed universe of liquid US large-caps, liquid across the whole
# 2015-2026 window. The coarse/fine fundamental universe service and the
# run_daily scheduler are not available in this Lean image, so the
# tradable pool is a fixed set of large, liquid names and the monthly
# rebalance is gated on a month change inside the OnData event.
UNIVERSE = [
    "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", "META",
    "JPM", "V", "JNJ", "WMT", "PG", "KO",
    "PEP", "MCD", "XOM", "CVX", "UNH", "LLY",
    "ABBV", "PFE", "MRK", "ADBE", "ORCL", "CRM",
    "CSCO", "QCOM", "TXN", "AMGN", "BMY", "DIS",
]

# Mesure de ligue, brique 3 (#28535, protocole #22828 / #26329) : parametre
# `mode`. `strategy` (defaut) = code inchange, decision inchangee ; `spy` et
# `6040` = references detenues, reequilibrees au meme rebalancement mensuel ;
# `ew30` = les 30 valeurs de l'univers a poids egal (diagnostic).
# Trace en ombre (contrat #18923) : chart `shadow` (e0..e4) avant 2025-01-01
# (fenetre F1), chart `shadow2` (e0..e4) ensuite (fenetre F2).
MODES = ("strategy", "spy", "6040", "ew30")
F1_END = date(2025, 1, 1)


class FiftyTwoWeekHighAlgorithm(QCAlgorithm):
    """
    52-week-high momentum (O'Neil "glory" signal).

    Each month, among a fixed universe of liquid US large-caps, rank them
    by proximity to their trailing 52-week high (last close / 52-week high)
    and hold the 10 closest to their high, equal-weight.

    League measurement (EPIC #19821, brique 3): one continuous pass over
    2015-01-01 to 2026-11-18. The `mode` parameter selects the strategy
    (default, decision unchanged) or a held reference measured on the same
    history: `spy`, `6040` (SPY 60 % / BND 40 %), or `ew30` (the fixed
    universe equal-weight, diagnostic). Every mode traces the portfolio
    value once per session, in `shadow` before 2025-01-01 and `shadow2`
    after.
    """

    N = 10  # number of holdings

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 11, 18)
        self.set_cash(100_000)  # USD by default
        self.set_benchmark("SPY")
        # Le mode est lu avant les abonnements : `6040` ajoute BND, les
        # autres modes n'y touchent pas.
        self.mode = self.get_parameter("mode", "strategy")
        if self.mode not in MODES:
            raise ValueError(f"unknown mode {self.mode!r}")
        # Transaction costs: no custom brokerage model is set, so Lean's
        # default equity brokerage model (per-share commission + slippage)
        # is in force on every liquidate()/set_holdings() below and on the
        # benchmark's single initial buy.
        self._symbols = {}
        for sym in UNIVERSE:
            self._symbols[sym] = self.add_equity(sym, Resolution.Daily).Symbol
        if self.mode in ("spy", "6040"):
            # SPY n'appartient pas a UNIVERSE : il n'est abonne que pour les
            # modes de reference, comme BND ne l'est que pour 6040.
            self._symbols["SPY"] = self.add_equity("SPY", Resolution.Daily).Symbol
        if self.mode == "6040":
            # 40 % d'obligations agregees : actif abonne pour ce seul mode,
            # hors de l'univers note.
            self._symbols["BND"] = self.add_equity("BND", Resolution.Daily).Symbol
        self._rebal_month = None
        self._trace_date = None
        self._shadow_bars = 0
        self._shadow2_bars = 0

    def _trace(self):
        """Trace en ombre : une valeur par seance, seance k dans e{k % 5}."""
        today = self.Time.date()
        if today == self._trace_date:
            return
        self._trace_date = today
        if today < F1_END:
            self.plot("shadow", f"e{self._shadow_bars % 5}",
                      self.Portfolio.TotalPortfolioValue)
            self._shadow_bars += 1
        else:
            self.plot("shadow2", f"e{self._shadow2_bars % 5}",
                      self.Portfolio.TotalPortfolioValue)
            self._shadow2_bars += 1

    def _reference_weights(self):
        """Poids du mode de reference, ou None pour le chemin strategie."""
        if self.mode == "spy":
            return {"SPY": 1.0}
        if self.mode == "6040":
            return {"SPY": 0.6, "BND": 0.4}
        if self.mode == "ew30":
            return {sym: 1.0 / len(UNIVERSE) for sym in UNIVERSE}
        return None

    def OnData(self, slice):
        self._trace()
        month = self.Time.month
        if month == self._rebal_month:
            return
        self._rebal_month = month
        weights = self._reference_weights()
        if weights is not None:
            for ticker, w in weights.items():
                self.set_holdings(self._symbols[ticker], w)
            return
        scores = []
        for sym in UNIVERSE:
            # 365 daily closes, read straight off the TradeBar series. Two
            # Lean-image gotchas are both load-bearing: (1) the explicit
            # Resolution.Daily, else the int 365 is read as *seconds* (a
            # handful of Minute bars) and the warmup guard below silently
            # disables the strategy; (2) a SINGLE Symbol plus a Resolution
            # returns an IEnumerable[TradeBar] here, and the list-DataFrame
            # overload indexes its columns through a PandasMapper that does
            # not accept a bare symbol key (df["AAPL"] -> KeyError). So we
            # iterate the bars and take .Close directly -- no DataFrame
            # column indexing at all.
            closes = [tb.Close for tb in self.history(sym, 365, Resolution.Daily)]
            if len(closes) < 120:
                continue
            high52 = max(closes)
            if high52 <= 0:
                continue
            scores.append((closes[-1] / high52, sym))
        if len(scores) < self.N:
            return
        scores.sort(key=lambda x: x[0], reverse=True)
        selected = {sym for _, sym in scores[:self.N]}
        # Liquidate every universe name not kept. Liquidating a symbol we
        # do not hold is a no-op, and our holdings are always a subset of
        # UNIVERSE, so this covers every open position without needing to
        # introspect the PositionGroupKey type of this Lean image.
        for sym in UNIVERSE:
            if sym not in selected:
                self.liquidate(sym)
        for sym in selected:
            self.set_holdings(sym, 1.0 / self.N)