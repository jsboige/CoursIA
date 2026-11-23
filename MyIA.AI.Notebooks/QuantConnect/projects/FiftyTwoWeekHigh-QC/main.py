from AlgorithmImports import *

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


class FiftyTwoWeekHighAlgorithm(QCAlgorithm):
    """
    52-week-high momentum (O'Neil "glory" signal).

    Each month, among a fixed universe of liquid US large-caps, rank them
    by proximity to their trailing 52-week high (last close / 52-week high)
    and hold the 10 closest to their high, equal-weight.

    League measurement (EPIC #19821, brique 3): single backtest over
    2015-01-01 to 2026-11-18, benchmark SPY (buy & hold). Verdict =
    strategy vs SPY.
    """

    N = 10  # number of holdings

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 11, 18)
        self.set_cash(100_000)  # USD by default
        self.set_benchmark("SPY")
        # Transaction costs: no custom brokerage model is set, so Lean's
        # default equity brokerage model (per-share commission + slippage)
        # is in force on every liquidate()/set_holdings() below and on the
        # benchmark's single initial buy.
        for sym in UNIVERSE:
            self.add_equity(sym, Resolution.Daily)
        self._rebal_month = None

    def OnData(self, slice):
        month = self.Time.month
        if month == self._rebal_month:
            return
        self._rebal_month = month
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
