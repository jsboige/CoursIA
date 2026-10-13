from AlgorithmImports import *

# Derive de Framework_Composite_TrendWeather/alpha_models.py (evaluation #19393).
# TrendStocksAlpha garde la regle d'origine (SMA200, EMA20 > EMA50, poids par le taux de
# variation sur 63 seances, emission mensuelle). Ce qui change :
# - les titres sont suivis par Symbol, et la liste des membres peut etre fixe (`tickers`,
#   regle d'origine) ou fournie chaque mois par la selection de l'algorithme (`tickers=None`) ;
# - un titre detenu qui n'est plus membre recoit un signal plat ;
# - `weighting="equal"` remplace les poids par le taux de variation par des poids egaux ;
# - `warm_new=True` initialise les indicateurs d'un titre entrant sur son historique.
# AllWeatherAlpha est inchange.


class TrendStocksAlpha(AlphaModel):
    """
    Alpha Model: Trend Stocks Lite signal with momentum weighting.

    Per stock: Price > SMA200 AND EMA20 > EMA50 -> UP insight.
    Otherwise -> FLAT insight (exit position).

    Monthly emission.
    """

    def __init__(self, tickers=None, exclude=(), weighting="momentum", warm_new=False):
        super().__init__()
        self.name = "TrendStocks"
        self.tickers = list(tickers) if tickers is not None else None
        self.exclude = set(exclude)
        self.weighting = weighting
        self.warm_new = warm_new
        self.members = []  # Symbols, mis a jour par la selection quand tickers=None
        self.symbols = {}  # ticker -> Symbol, liste fixe
        self.sma200 = {}
        self.ema20 = {}
        self.ema50 = {}
        self.roc63 = {}  # 3-month momentum
        self._last_month = -1

    def _current_members(self):
        if self.tickers is not None:
            return [self.symbols[t] for t in self.tickers if t in self.symbols]
        return list(self.members)

    def _ready(self, symbol):
        return all(
            ind is not None and ind.is_ready
            for ind in [self.sma200.get(symbol), self.ema20.get(symbol), self.ema50.get(symbol)]
        )

    def update(self, algorithm, data):
        # Monthly emission (first trading day of month)
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month

        if algorithm.is_warming_up:
            return []

        members = self._current_members()

        # First pass: members with ready indicators, then bullish ones and their momentum
        ready = []
        bullish = []
        for symbol in members:
            if not self._ready(symbol):
                continue
            if not algorithm.securities.contains_key(symbol):
                continue
            price = algorithm.securities[symbol].price
            if price <= 0:
                continue
            ready.append(symbol)
            in_uptrend = (
                price > self.sma200[symbol].current.value
                and self.ema20[symbol].current.value > self.ema50[symbol].current.value
            )
            if in_uptrend:
                roc = self.roc63.get(symbol)
                mom = roc.current.value if (roc and roc.is_ready) else 0
                bullish.append((symbol, max(mom, 0.001)))

        # Normalized weights
        weights = {}
        if bullish:
            if self.weighting == "equal":
                weights = {s: 1.0 / len(bullish) for s, _ in bullish}
            else:
                total_mom = sum(m for _, m in bullish)
                weights = {s: m / total_mom for s, m in bullish}

        # Second pass: emit insights
        insights = []
        period = timedelta(days=31)
        for symbol in ready:
            if symbol in weights:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    weight=weights[symbol],
                    source_model=self.name
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        # Held stocks that left the membership: flat
        member_set = set(members)
        for symbol, holding in algorithm.portfolio.items():
            if (holding.invested and symbol not in member_set
                    and symbol.value not in self.exclude):
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            sym = security.symbol
            ticker = sym.value
            if self.tickers is not None:
                if ticker not in self.tickers:
                    continue
                self.symbols[ticker] = sym
            elif ticker in self.exclude:
                continue
            self.sma200[sym] = algorithm.sma(sym, 200, Resolution.DAILY)
            self.ema20[sym] = algorithm.ema(sym, 20, Resolution.DAILY)
            self.ema50[sym] = algorithm.ema(sym, 50, Resolution.DAILY)
            self.roc63[sym] = algorithm.roc(sym, 63, Resolution.DAILY)
            if self.warm_new:
                for ind in (self.sma200[sym], self.ema20[sym], self.ema50[sym], self.roc63[sym]):
                    algorithm.warm_up_indicator(sym, ind, Resolution.DAILY)


class AllWeatherAlpha(AlphaModel):
    """
    Alpha Model: All Weather static allocation signal.

    Always emits UP insights for SPY/IEF/GLD/XLP with weight hints
    matching the target allocation (30/30/30/10).
    Monthly emission (low turnover strategy).
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "AllWeather"
        self.tickers = tickers
        self.target_weights = {
            "SPY": 0.30,
            "IEF": 0.30,
            "GLD": 0.30,
            "XLP": 0.10,
        }
        self.symbols = {}
        self._last_month = -1

    def update(self, algorithm, data):
        # Monthly emission (first trading day of month)
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month

        if algorithm.is_warming_up:
            return []

        insights = []
        period = timedelta(days=31)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            weight = self.target_weights.get(ticker, 0)
            insights.append(Insight.price(
                symbol, period, InsightDirection.UP,
                weight=weight,
                source_model=self.name
            ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                self.symbols[ticker] = security.symbol
