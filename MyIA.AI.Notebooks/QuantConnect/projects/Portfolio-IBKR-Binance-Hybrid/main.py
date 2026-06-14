# region imports
from AlgorithmImports import *
# endregion


# ===========================================================================
# Reality models: explicit transaction costs (README Phase 2 cost basis).
# The default brokerage (required because IBKR rejects Crypto securities)
# applies no meaningful fee, so without these models the backtest is
# optimistic. Mirrors the repo's SpreadSlippageModel idiom.
#   5bps equity commission + 10bps crypto commission + 5bps slippage.
# ===========================================================================

class PercentFeeModel(FeeModel):
    """Charges a fixed percent of the order notional value as commission."""

    def __init__(self, percent):
        super().__init__()
        self.percent = percent

    def get_order_fee(self, parameters):
        security = parameters.security
        order = parameters.order
        notional = abs(order.quantity) * float(security.price)
        return OrderFee(CashAmount(self.percent * notional, security.quote_currency.symbol))


class PercentSlippageModel:
    """Constant percent slippage on fill price (market-impact approximation).

    Duck-typed (no base class) to match the repo's SpreadSlippageModel style;
    QC accepts any object exposing get_slippage_approximation(asset, order).
    """

    def __init__(self, percent):
        self.percent = percent

    def get_slippage_approximation(self, asset, order):
        return self.percent * float(asset.price)


# ===========================================================================
# Portfolio Hybride IBKR (50%) + Binance (50%) - Phase 2
# ---------------------------------------------------------------------------
# Unified backtest 2018-2025 aggregating 8 sub-strategies via a direct composite
# rebalance. The 8 signal rules are transposed verbatim from the Phase 1 research
# notebook (quantbook.ipynb), which validated the proxies over 2018-2025.
#
# Design choice (direct composite, NOT the QC Alpha framework): an earlier
# Alpha-framework attempt (CompositeAlphaModel + HybridPortfolioPCM) produced
# 0 total orders across 6 backtest iterations (v1-v6) -- the Insight -> PCM
# plumbing never emitted trades. The direct composite calls set_holdings()
# explicitly each month, so it trades by construction. This is the live
# equivalent of the MultiAlphaModel aggregation in the Phase 1 bridge table
# (cell 2581bd22): each strategy contributes its within-strategy target weights,
# blended by the fixed portfolio weights.
#
# Brokerage: the DEFAULT model (no set_brokerage_model), because IBKR margin
# REJECTS Crypto ("Unsupported security type: Crypto"). The default authorizes
# both equities and crypto; explicit PercentFeeModel/PercentSlippageModel apply
# the README cost basis. Account currency USDT so the Binance sleeve settles.
#
# See #1027.
# ===========================================================================


class PortfolioHybridIBKRBinance(QCAlgorithm):
    """Phase 2 unified backtest, 8 research-faithful sub-strategies, monthly."""

    # Portfolio target weights. Include the 50/50 IBKR/Binance sleeve split:
    # IBKR sleeve (equities) sums to 50%, Binance sleeve (crypto) sums to 50%.
    PORTFOLIO_WEIGHTS = {
        # IBKR sleeve (50%)
        "TrendWeather":      0.150,
        "EMATrend":          0.125,
        "SectorMomentum":    0.100,
        "AllWeather":        0.075,
        "EMA-Cross-Alpha":   0.050,
        # Binance sleeve (50%)
        "EMA-Cross-Crypto":  0.250,
        "Crypto-MultiCanal": 0.150,
        "HAR-RV-VolTarget":  0.100,
    }

    IBKR_SECTORS = ["XLK", "XLF", "XLE", "XLV", "XLY", "XLI", "XLB", "XLU", "XLP"]
    CRYPTO_TICKERS = ["BTCUSDT", "ETHUSDT", "SOLUSDT", "ADAUSDT", "LTCUSDT", "XRPUSDT"]

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2025, 6, 1)

        # Account currency USDT so the Binance crypto sleeve (BTCUSDT, ETHUSDT)
        # settles natively. Equities (USD) auto-convert via the USD/USDT FX rate.
        # Set BEFORE set_cash (canonical order).
        self.set_account_currency("USDT")
        self.set_cash(100000)

        # DEFAULT brokerage (no set_brokerage_model): IBKR margin rejects Crypto.
        # Explicit cost models below apply the README Phase 2 cost basis.

        # IBKR sleeve (equities): 5bps commission + 5bps slippage.
        self.spy = self.add_equity("SPY", Resolution.DAILY)
        self.ief = self.add_equity("IEF", Resolution.DAILY)
        self.gld = self.add_equity("GLD", Resolution.DAILY)
        self.xlp = self.add_equity("XLP", Resolution.DAILY)
        for sec in (self.spy, self.ief, self.gld, self.xlp):
            sec.set_fee_model(PercentFeeModel(0.0005))
            sec.set_slippage_model(PercentSlippageModel(0.0005))
        self.spy, self.ief, self.gld, self.xlp = (s.symbol for s in (self.spy, self.ief, self.gld, self.xlp))

        self.sector_symbols = {}
        for ticker in self.IBKR_SECTORS:
            sec = self.add_equity(ticker, Resolution.DAILY)
            sec.set_fee_model(PercentFeeModel(0.0005))
            sec.set_slippage_model(PercentSlippageModel(0.0005))
            self.sector_symbols[ticker] = sec.symbol

        # Binance sleeve (crypto): 10bps commission + 5bps slippage.
        # Only BTCUSDT has continuous data over the full window on QC; the basket
        # rule falls back to whatever has data.
        self.crypto_symbols = {}
        for ticker in self.CRYPTO_TICKERS:
            sec = self.add_crypto(ticker, Resolution.DAILY, Market.BINANCE)
            sec.set_fee_model(PercentFeeModel(0.001))
            sec.set_slippage_model(PercentSlippageModel(0.0005))
            self.crypto_symbols[ticker] = sec.symbol

        # Warmup covers the longest signal lookback (vol-median 252 + EMA 200).
        self.set_warm_up(252, Resolution.DAILY)

        # Monthly rebalance at month start.
        self.schedule.on(
            self.date_rules.month_start(self.spy),
            self.time_rules.at(9, 31),
            self.rebalance,
        )

    # ---- data helper ----
    def _close_series(self, symbol, lookback):
        """Trailing daily close series for a single symbol, or None if no data."""
        hist = self.history(symbol, lookback, Resolution.DAILY)
        if hist is None or len(hist) == 0:
            return None
        # History(single Symbol, ...) is time-indexed; collapse any symbol level defensively.
        if getattr(hist.index, "names", None) and \
                "symbol" in [str(n).lower() for n in hist.index.names]:
            try:
                hist = hist.xs(symbol, level=0) if hist.index.nlevels > 1 else hist
            except Exception:
                pass
        if "close" not in hist.columns:
            return None
        return hist["close"].dropna()

    @staticmethod
    def _ema_last(series, span):
        return float(series.ewm(span=span, adjust=False).mean().iloc[-1])

    # ---- the 8 sub-strategy signal rules ----
    # Each returns {symbol: within-strategy weight} (sums to ~1.0 when invested, 0 when in cash).

    def _trend_weather(self):
        """SPY > SMA200 AND vol63 < 1.5 x median252 -> 70% SPY + 30% GLD ; else 60% IEF + 40% GLD."""
        spy = self._close_series(self.spy, 400)
        if spy is None or len(spy) < 316:
            return {self.ief: 0.6, self.gld: 0.4}
        rets = spy.pct_change().dropna()
        sma200 = float(spy.iloc[-200:].mean())
        vol63_series = (rets.rolling(63).std() * (252 ** 0.5)).dropna()
        vol63 = float(vol63_series.iloc[-1]) if len(vol63_series) > 0 else 0.0
        vol_med = float(vol63_series.iloc[-252:].median()) if len(vol63_series) > 0 else vol63
        risk_on = (float(spy.iloc[-1]) > sma200) and (vol_med > 0 and vol63 < vol_med * 1.5)
        if risk_on:
            return {self.spy: 0.7, self.gld: 0.3}
        return {self.ief: 0.6, self.gld: 0.4}

    def _ema_trend(self):
        """EMA50 > EMA200 on SPY -> 100% SPY ; else 100% IEF."""
        spy = self._close_series(self.spy, 400)
        if spy is None or len(spy) < 200:
            return {self.ief: 1.0}
        up = self._ema_last(spy, 50) > self._ema_last(spy, 200)
        return {self.spy: 1.0} if up else {self.ief: 1.0}

    def _sector_momentum(self):
        """Top-3 sector ETFs by 126d momentum (positive only), equal-weight ; else IEF."""
        moms = {}
        for ticker, sym in self.sector_symbols.items():
            s = self._close_series(sym, 130)
            if s is not None and len(s) >= 127:
                moms[sym] = float(s.iloc[-1] / s.iloc[-127] - 1.0)
        positive = {sym: m for sym, m in moms.items() if m > 0}
        if not positive:
            return {self.ief: 1.0}
        top = sorted(positive.items(), key=lambda kv: kv[1], reverse=True)[:3]
        n = len(top)
        return {sym: 1.0 / n for sym, _ in top}

    def _all_weather(self):
        """Static 30% SPY / 40% IEF / 15% GLD / 15% XLP."""
        return {self.spy: 0.30, self.ief: 0.40, self.gld: 0.15, self.xlp: 0.15}

    def _ema_cross_alpha(self):
        """EMA20 > EMA50 on SPY -> 100% SPY ; else cash."""
        spy = self._close_series(self.spy, 150)
        if spy is None or len(spy) < 50:
            return {}
        up = self._ema_last(spy, 20) > self._ema_last(spy, 50)
        return {self.spy: 1.0} if up else {}

    def _ema_cross_crypto(self):
        """SMA20 > SMA50 on BTC -> 100% BTC ; else cash."""
        btc = self._close_series(self.crypto_symbols["BTCUSDT"], 60)
        if btc is None or len(btc) < 50:
            return {}
        sma20 = float(btc.iloc[-20:].mean())
        sma50 = float(btc.iloc[-50:].mean())
        return {self.crypto_symbols["BTCUSDT"]: 1.0} if sma20 > sma50 else {}

    def _crypto_multicanal(self):
        """Equal-weight basket of cryptos with data."""
        out = {}
        for ticker, sym in self.crypto_symbols.items():
            s = self._close_series(sym, 5)
            if s is not None and len(s) > 0:
                out[sym] = 1.0
        n = len(out)
        if n == 0:
            return {}
        return {sym: 1.0 / n for sym in out}

    def _har_rv_voltarget(self):
        """BTC weight = clip(0.15 / RV22, 0, 1), RV22 = std(returns, 22) x sqrt(252)."""
        btc = self._close_series(self.crypto_symbols["BTCUSDT"], 30)
        if btc is None or len(btc) < 23:
            return {}
        rets = btc.pct_change().dropna()
        if len(rets) < 22:
            return {}
        rv22 = float(rets.iloc[-22:].std() * (252 ** 0.5))
        if rv22 <= 0:
            return {}
        return {self.crypto_symbols["BTCUSDT"]: min(0.15 / rv22, 1.0)}

    def rebalance(self):
        if self.is_warming_up:
            return

        signals = {
            "TrendWeather":      self._trend_weather(),
            "EMATrend":          self._ema_trend(),
            "SectorMomentum":    self._sector_momentum(),
            "AllWeather":        self._all_weather(),
            "EMA-Cross-Alpha":   self._ema_cross_alpha(),
            "EMA-Cross-Crypto":  self._ema_cross_crypto(),
            "Crypto-MultiCanal": self._crypto_multicanal(),
            "HAR-RV-VolTarget":  self._har_rv_voltarget(),
        }

        # Composite: final per-symbol weight = sum over strats of (portfolio_weight x signal).
        targets = {}
        for strat, sig in signals.items():
            strat_weight = self.PORTFOLIO_WEIGHTS[strat]
            for sym, w in sig.items():
                targets[sym] = targets.get(sym, 0.0) + strat_weight * w

        # Defensive log: confirms rebalance fires and produces targets (anti-0-orders).
        self.log("Rebalance {}: {} targets, gross {:.1%}".format(
            self.time.date(), len(targets), sum(targets.values())))

        all_symbols = set([self.spy, self.ief, self.gld, self.xlp]) \
            | set(self.sector_symbols.values()) \
            | set(self.crypto_symbols.values())

        # Liquidate anything not held this month, then apply targets. The default
        # brokerage on a cash account cannot borrow, so total gross <= 1.0 is
        # enforced by construction (portfolio weights sum to 1.0; cash-out strats
        # reduce it). Sequential set_holdings is safe for gross <= 1.0.
        for sym in all_symbols:
            if sym not in targets or targets[sym] <= 0.001:
                self.liquidate(sym)
        for sym in sorted(targets, key=lambda s: str(s)):
            w = targets[sym]
            if w > 0.001:
                self.set_holdings(sym, w)

    def on_data(self, data):
        pass
