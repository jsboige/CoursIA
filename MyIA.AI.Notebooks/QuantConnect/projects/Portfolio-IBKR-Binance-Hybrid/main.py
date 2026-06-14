# region imports
from AlgorithmImports import *
import numpy as np
# endregion

# ===========================================================================
# Portfolio Hybride IBKR (50%) + Binance (50%) - Phase 2
# ---------------------------------------------------------------------------
# Unified backtest 2018-2025 aggregating 8 sub-strategies as AlphaModels:
#   Sleeve IBKR 50%: TrendStocks 30%, EMACross 25%, SectorMomentum 20%,
#                    AllWeather 15%, EMAEquity 10%
#   Sleeve Binance 50%: EMACrypto 50%, MultiCanalProxy 30%, HarrvjProxy 20%
#
# Signal logic faithfully reproduced from the 8 source projects (see #1027),
# with two documented proxies for the event-driven/ML strategies
# (Crypto-MultiCanal channel geometry, HAR-RV-J OLS volatility forecast).
# ===========================================================================


def _resolve_equity(algorithm, ticker):
    """Return the symbol of an equity already added in Initialize().
    QC's add_equity is idempotent, but we avoid re-calling it from AlphaModels
    to keep a single source of truth for universe subscription.
    """
    symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
    if symbol not in algorithm.securities:
        algorithm.add_equity(ticker, Resolution.DAILY)
    return symbol


def _resolve_crypto(algorithm, ticker):
    """Return the symbol of a crypto pair already added in Initialize()."""
    symbol = Symbol.create(ticker, SecurityType.CRYPTO, Market.BINANCE)
    if symbol not in algorithm.securities:
        algorithm.add_crypto(ticker, Resolution.DAILY, Market.BINANCE)
    return symbol


# ---------------------------------------------------------------------------
# Reality models: explicit transaction costs (README Phase 2 cost basis).
# The default brokerage (used because IBKR rejects Crypto) applies no
# meaningful fee model, so the first backtest (Sharpe 0.765) was OPTIMISTIC.
# These models apply the cost basis the README commits to:
#   5bps equity commission + 10bps crypto commission + 5bps slippage.
# Mirrors the repo's SpreadSlippageModel idiom (TradingCosts-Optimization).
# ---------------------------------------------------------------------------

class PercentFeeModel(FeeModel):
    """Charges a fixed percent of the order notional value as commission."""

    def __init__(self, percent: float):
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

    def __init__(self, percent: float):
        self.percent = percent

    def get_slippage_approximation(self, asset, order):
        return self.percent * float(asset.price)


# ---------------------------------------------------------------------------
# Sub-strategy AlphaModels (equity sleeve)
# ---------------------------------------------------------------------------

class TrendStocksAlphaModel(AlphaModel):
    """TrendStocks: long when Price > SMA200 AND EMA20 > EMA50.
    Weighted by 3-month momentum (ROC63). Source: Framework_Composite_TrendWeather.
    """

    def __init__(self, tickers, resolution=Resolution.DAILY):
        self.tickers = tickers
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.indicators = {}

    def update(self, algorithm, data):
        insights = []
        for ticker in self.tickers:
            if ticker not in self.indicators:
                symbol = _resolve_equity(algorithm, ticker)
                self.indicators[ticker] = {
                    "symbol": symbol,
                    "sma200": algorithm.sma(symbol, 200, self.resolution),
                    "ema20": algorithm.ema(symbol, 20, self.resolution),
                    "ema50": algorithm.ema(symbol, 50, self.resolution),
                }
            ind = self.indicators[ticker]
            symbol = ind["symbol"]
            if symbol not in algorithm.securities:
                continue
            sma200, ema20, ema50 = ind["sma200"], ind["ema20"], ind["ema50"]
            if not (sma200.is_ready and ema20.is_ready and ema50.is_ready):
                continue
            price = algorithm.securities[symbol].price
            if not (price > sma200.current.value and ema20.current.value > ema50.current.value):
                insights.append(Insight.price(symbol, timedelta(days=35), InsightDirection.FLAT, source_model=self.name))
                continue
            history = algorithm.history(symbol, 63, self.resolution)
            if history.empty:
                continue
            roc = (price / float(history["close"].iloc[0])) - 1.0
            if roc <= 0:
                continue
            insights.append(Insight.price(symbol, timedelta(days=35), InsightDirection.UP, weight=roc, source_model=self.name))
        return insights


class EMACrossAlphaModel(AlphaModel):
    """EMACross + TrendStocks composite (Framework_Composite_EMATrend pattern):
    long when EMA20 > EMA50, with SMA200 trend filter. Weekly emission.
    """

    def __init__(self, tickers, resolution=Resolution.DAILY):
        self.tickers = tickers
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.indicators = {}
        self._last_emit = datetime.min

    def update(self, algorithm, data):
        if (algorithm.time - self._last_emit) < timedelta(days=6):
            return []
        self._last_emit = algorithm.time
        insights = []
        for ticker in self.tickers:
            if ticker not in self.indicators:
                symbol = _resolve_equity(algorithm, ticker)
                self.indicators[ticker] = {
                    "symbol": symbol,
                    "ema20": algorithm.ema(symbol, 20, self.resolution),
                    "ema50": algorithm.ema(symbol, 50, self.resolution),
                    "sma200": algorithm.sma(symbol, 200, self.resolution),
                }
            ind = self.indicators[ticker]
            symbol = ind["symbol"]
            if symbol not in algorithm.securities:
                continue
            ema20, ema50, sma200 = ind["ema20"], ind["ema50"], ind["sma200"]
            if not (ema20.is_ready and ema50.is_ready and sma200.is_ready):
                continue
            price = algorithm.securities[symbol].price
            if ema20.current.value > ema50.current.value and price > sma200.current.value:
                insights.append(Insight.price(symbol, timedelta(days=35), InsightDirection.UP, source_model=self.name))
            else:
                insights.append(Insight.price(symbol, timedelta(days=35), InsightDirection.FLAT, source_model=self.name))
        return insights


class SectorMomentumAlphaModel(AlphaModel):
    """Dual momentum rotation on SPY/TLT/GLD (SectorMomentum v3.2).
    Composite momentum (1m/3m/6m/12m weighted), 100% to the winner with
    SPY bull filter (price > SMA200). Monthly entry, defensive rotation.
    """

    def __init__(self, resolution=Resolution.DAILY):
        self.tickers = ["SPY", "TLT", "GLD"]
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.indicators = {}
        self.weights_mom = [0.4, 0.2, 0.2, 0.2]
        self.windows = [21, 63, 126, 252]
        self._last_rebalance = datetime.min

    def _ensure(self, algorithm):
        for ticker in self.tickers:
            if ticker not in self.indicators:
                symbol = _resolve_equity(algorithm, ticker)
                self.indicators[ticker] = {
                    "symbol": symbol,
                    "sma200": algorithm.sma(symbol, 200, self.resolution),
                }

    def update(self, algorithm, data):
        self._ensure(algorithm)
        spy_ind = self.indicators.get("SPY")
        if spy_ind is None or spy_ind["symbol"] not in algorithm.securities:
            return []
        sma200_spy = spy_ind["sma200"]
        if not sma200_spy.is_ready:
            return []

        scores = {}
        for ticker, ind in self.indicators.items():
            symbol = ind["symbol"]
            if symbol not in algorithm.securities:
                continue
            history = algorithm.history(symbol, 260, self.resolution)
            if len(history) < 252:
                continue
            closes = history["close"].values
            price_now = float(algorithm.securities[symbol].price)
            score = 0.0
            for w, window in zip(self.weights_mom, self.windows):
                if len(closes) > window:
                    score += w * ((price_now / float(closes[-window])) - 1.0)
            scores[ticker] = score
        if not scores:
            return []

        spy_symbol = spy_ind["symbol"]
        spy_price = float(algorithm.securities[spy_symbol].price)
        spy_below_sma = spy_price < sma200_spy.current.value
        spy_score = scores.get("SPY", 0.0)

        if spy_score > 0 and not spy_below_sma and spy_score >= max(
            scores.get("TLT", -1e9), scores.get("GLD", -1e9)
        ):
            winner = "SPY"
        else:
            defensive = {"TLT": scores.get("TLT", -1e9), "GLD": scores.get("GLD", -1e9)}
            winner = max(defensive, key=defensive.get)

        insights = []
        for ticker, ind in self.indicators.items():
            symbol = ind["symbol"]
            direction = InsightDirection.UP if ticker == winner else InsightDirection.FLAT
            insights.append(Insight.price(symbol, timedelta(days=35), direction, source_model=self.name))
        return insights


class AllWeatherAlphaModel(AlphaModel):
    """Static AllWeather v5: SPY 30%, IEF 30%, GLD 30%, XLP 10%. Always long.
    Source: AllWeather/main.py:63-68.
    """

    TARGET_WEIGHTS = {"SPY": 0.30, "IEF": 0.30, "GLD": 0.30, "XLP": 0.10}

    def __init__(self, resolution=Resolution.DAILY):
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.symbols = {}
        self._last_emit = datetime.min

    def update(self, algorithm, data):
        if (algorithm.time - self._last_emit) < timedelta(days=85):
            return []
        self._last_emit = algorithm.time
        insights = []
        for ticker, w in self.TARGET_WEIGHTS.items():
            if ticker not in self.symbols:
                self.symbols[ticker] = _resolve_equity(algorithm, ticker)
            insights.append(Insight.price(self.symbols[ticker], timedelta(days=95), InsightDirection.UP, weight=w, source_model=self.name))
        return insights


class EMAEquityCrossAlphaModel(AlphaModel):
    """Pure EMA20/EMA50 crossover on tech tickers. EMA-Cross-Alpha.
    Source: EMA-Cross-Alpha/alpha_models.py:43-54.
    """

    def __init__(self, tickers, resolution=Resolution.DAILY):
        self.tickers = tickers
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.indicators = {}

    def update(self, algorithm, data):
        insights = []
        for ticker in self.tickers:
            if ticker not in self.indicators:
                symbol = _resolve_equity(algorithm, ticker)
                self.indicators[ticker] = {
                    "symbol": symbol,
                    "ema20": algorithm.ema(symbol, 20, self.resolution),
                    "ema50": algorithm.ema(symbol, 50, self.resolution),
                }
            ind = self.indicators[ticker]
            symbol = ind["symbol"]
            if symbol not in algorithm.securities:
                continue
            ema20, ema50 = ind["ema20"], ind["ema50"]
            if not (ema20.is_ready and ema50.is_ready):
                continue
            direction = InsightDirection.UP if ema20.current.value > ema50.current.value else InsightDirection.FLAT
            insights.append(Insight.price(symbol, timedelta(days=7), direction, source_model=self.name))
        return insights


# ---------------------------------------------------------------------------
# Sub-strategy AlphaModels (crypto sleeve) - Binance Cash
# ---------------------------------------------------------------------------

class EMACrossCryptoAlphaModel(AlphaModel):
    """EMA-Cross-Crypto on BTC/ETH: long when EMA20>EMA50 AND price>SMA200.
    Internalizes the 10% trailing stop as a FLAT when drawdown from rolling
    peak exceeds 10%. Source: EMA-Cross-Crypto/main.py:72-100.
    """

    def __init__(self, tickers, resolution=Resolution.DAILY):
        self.tickers = tickers
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.indicators = {}
        self.peak = {}

    def update(self, algorithm, data):
        insights = []
        for ticker in self.tickers:
            if ticker not in self.indicators:
                symbol = _resolve_crypto(algorithm, ticker)
                self.indicators[ticker] = {
                    "symbol": symbol,
                    "ema20": algorithm.ema(symbol, 20, self.resolution),
                    "ema50": algorithm.ema(symbol, 50, self.resolution),
                    "sma200": algorithm.sma(symbol, 200, self.resolution),
                }
                self.peak[symbol] = 0.0
            ind = self.indicators[ticker]
            symbol = ind["symbol"]
            if symbol not in algorithm.securities:
                continue
            ema20, ema50, sma200 = ind["ema20"], ind["ema50"], ind["sma200"]
            if not (ema20.is_ready and ema50.is_ready and sma200.is_ready):
                continue
            price = float(algorithm.securities[symbol].price)
            invested = algorithm.securities[symbol].invested
            if invested and price > self.peak[symbol]:
                self.peak[symbol] = price
            direction = InsightDirection.FLAT
            if invested:
                if self.peak[symbol] > 0 and price <= self.peak[symbol] * 0.90:
                    direction = InsightDirection.FLAT
                    self.peak[symbol] = 0.0
                elif ema20.current.value < ema50.current.value:
                    direction = InsightDirection.FLAT
                    self.peak[symbol] = 0.0
                else:
                    direction = InsightDirection.UP
            else:
                if ema20.current.value > ema50.current.value and price > sma200.current.value:
                    direction = InsightDirection.UP
                    self.peak[symbol] = price
            insights.append(Insight.price(symbol, timedelta(days=7), direction, source_model=self.name))
        return insights


class CryptoMultiCanalProxyAlphaModel(AlphaModel):
    """SIMPLIFIED PROXY of Crypto-MultiCanal (channel geometry is O(n^2)
    envelope fitting + async SL/TP state, not reproducible as target weights).
    Proxy: long BTC when price > SMA50 (trend filter) AND near 20d support band
    (within 3% of 20d low). FLAT otherwise. Source: Crypto-MultiCanal/main.py:427-487.
    """

    def __init__(self, tickers, resolution=Resolution.DAILY):
        self.tickers = tickers
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.indicators = {}

    def update(self, algorithm, data):
        insights = []
        for ticker in self.tickers:
            if ticker not in self.indicators:
                symbol = _resolve_crypto(algorithm, ticker)
                self.indicators[ticker] = {
                    "symbol": symbol,
                    "sma50": algorithm.sma(symbol, 50, self.resolution),
                }
            ind = self.indicators[ticker]
            symbol = ind["symbol"]
            if symbol not in algorithm.securities:
                continue
            sma50 = ind["sma50"]
            if not sma50.is_ready:
                continue
            history = algorithm.history(symbol, 21, self.resolution)
            if len(history) < 20:
                continue
            if "low" in history:
                low20 = float(history["low"].min())
            else:
                low20 = float(history["close"].min())
            price = float(algorithm.securities[symbol].price)
            support_zone = low20 * 1.03
            direction = InsightDirection.UP if (price > sma50.current.value and price <= support_zone) else InsightDirection.FLAT
            insights.append(Insight.price(symbol, timedelta(days=7), direction, source_model=self.name))
        return insights


class HarrvjKellyProxyAlphaModel(AlphaModel):
    """SIMPLIFIED PROXY of HAR-RV-J-Kelly (the OLS volatility forecast is an
    ML model re-fit every 22d, not reproducible trivially). Proxy: rolling
    22d variance + 1/4-Kelly sizing, direction = sign(5d momentum).
    Source: HAR-RV-J-Kelly/main.py:77-131 (ML forecast replaced by rolling var).
    """

    def __init__(self, tickers, resolution=Resolution.DAILY):
        self.tickers = tickers
        self.resolution = resolution
        self.name = self.__class__.__name__
        self.symbols = {}
        self._last_emit = datetime.min

    def update(self, algorithm, data):
        if (algorithm.time - self._last_emit) < timedelta(days=6):
            return []
        self._last_emit = algorithm.time
        insights = []
        for ticker in self.tickers:
            if ticker not in self.symbols:
                self.symbols[ticker] = _resolve_crypto(algorithm, ticker)
            symbol = self.symbols[ticker]
            if symbol not in algorithm.securities:
                continue
            history = algorithm.history(symbol, 260, self.resolution)
            if len(history) < 252:
                continue
            closes = history["close"].values.astype(float)
            log_returns = np.diff(np.log(closes))
            var_forecast = float(np.var(log_returns[-22:])) * 252.0
            mu_ann = float(np.mean(log_returns[-20:])) * 252.0
            momentum5 = float(np.sum(log_returns[-5:]))
            if momentum5 <= 0 or var_forecast <= 0:
                insights.append(Insight.price(symbol, timedelta(days=8), InsightDirection.FLAT, source_model=self.name))
                continue
            kelly_full = mu_ann / var_forecast
            weight = min(max(kelly_full * 0.25, 0.0), 0.30)
            insights.append(Insight.price(symbol, timedelta(days=8), InsightDirection.UP, weight=weight, source_model=self.name))
        return insights


# ---------------------------------------------------------------------------
# Portfolio Construction Model: aggregate 8 alpha sources with sleeve weights
# ---------------------------------------------------------------------------

class HybridPortfolioPCM(PortfolioConstructionModel):
    """Aggregates 8 sub-strategy alpha models into the target sleeve weights:
    IBKR 50%: {TrendStocks 0.30, EMACross 0.25, SectorMomentum 0.20,
               AllWeather 0.15, EMAEquity 0.10}
    Binance 50%: {EMACrypto 0.50, MultiCanalProxy 0.30, HarrvjProxy 0.20}
    Each alpha's insights are scaled by (sleeve * intra-sleeve weight).
    Reuses the MultiStrategyPCM aggregation pattern from Framework_Composite_TrendWeather.
    """

    def __init__(self, alpha_weights, resolution=Resolution.DAILY):
        super().__init__()
        self.alpha_weights = alpha_weights
        self.resolution = resolution
        self._last_rebalance = datetime.min
        self._rebalance_period = timedelta(days=7)

    def determine_target_percent(self, active_insights):
        result = {}
        if not active_insights:
            return result
        by_alpha = {}
        for insight in active_insights:
            source = insight.source_model or "Unknown"
            by_alpha.setdefault(source, []).append(insight)
        for alpha_name, insights in by_alpha.items():
            capital_slice = self.alpha_weights.get(alpha_name, 0.0)
            for insight in insights:
                if insight.direction == InsightDirection.FLAT:
                    result[insight] = 0.0
            active = [i for i in insights if i.direction != InsightDirection.FLAT]
            if capital_slice <= 0 or not active:
                continue
            has_weights = all((i.weight is not None and i.weight > 0) for i in active)
            if has_weights:
                total_weight = sum(i.weight for i in active)
                for insight in active:
                    # Normalize relative weights within the alpha, scale by capital slice
                    normalized = insight.weight / total_weight
                    result[insight] = float(int(insight.direction)) * normalized * capital_slice
            else:
                per_symbol = capital_slice / len(active)
                for insight in active:
                    result[insight] = float(int(insight.direction)) * per_symbol
        return result


# ---------------------------------------------------------------------------
# Main algorithm
# ---------------------------------------------------------------------------

class PortfolioHybridIBKRBinance(QCAlgorithm):
    """Phase 2: unified backtest 2018-2025, 8 sub-strategies aggregated via
    CompositeAlphaModel + HybridPortfolioPCM. Sleeve IBKR 50% (USD) + Binance 50%.
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2025, 12, 1)

        # Account currency MUST be USDT so the Binance crypto sleeve (BTCUSDT,
        # ETHUSDT) can settle. Equities (USD) are auto-converted via the USD/USDT
        # FX rate (~1:1). set_account_currency BEFORE set_cash (canonical order).
        self.set_account_currency("USDT")
        self.set_cash(100000)

        # Brokerage: use the DEFAULT brokerage model (no set_brokerage_model).
        # IBKR margin (used in Phase 1) REJECTS Crypto securities with
        # "Unsupported security type: Crypto" — IBKR does not trade crypto spot.
        # For a unified multi-asset backtest (equities + crypto) the default
        # brokerage model authorizes both security types. The true 2-broker
        # hybrid (IBKR + Binance on separate nodes) is Phase 5.

        trend_tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        sector_tickers = ["SPY", "TLT", "GLD", "IEF", "XLP"]
        crypto_tickers = ["BTCUSDT", "ETHUSDT"]

        # IMPORTANT: add ALL securities upfront in Initialize(). QC's algorithm
        # framework needs the universe subscribed from the start; adding securities
        # lazily inside AlphaModel.Update() is unreliable (data may never feed),
        # which produced 0 tradeable dates / 0 orders in the first backtest run.
        # Apply the README Phase 2 cost basis explicitly: 5bps equity commission +
        # 5bps slippage, 10bps crypto commission + 5bps slippage. The default
        # brokerage (no set_brokerage_model, because IBKR rejects Crypto) applies
        # no meaningful fee, so without these models the Sharpe is optimistic.
        for t in trend_tickers + sector_tickers:
            sec = self.add_equity(t, Resolution.DAILY)
            sec.set_fee_model(PercentFeeModel(0.0005))
            sec.set_slippage_model(PercentSlippageModel(0.0005))
        for t in crypto_tickers:
            sec = self.add_crypto(t, Resolution.DAILY, Market.BINANCE)
            sec.set_fee_model(PercentFeeModel(0.001))
            sec.set_slippage_model(PercentSlippageModel(0.0005))

        # Build alpha models
        self.trend_stocks = TrendStocksAlphaModel(trend_tickers)
        self.ema_composite = EMACrossAlphaModel(trend_tickers)
        self.sector_mom = SectorMomentumAlphaModel()
        self.all_weather = AllWeatherAlphaModel()
        self.ema_equity = EMAEquityCrossAlphaModel(trend_tickers)
        self.ema_crypto = EMACrossCryptoAlphaModel(crypto_tickers)
        self.multic_proxy = CryptoMultiCanalProxyAlphaModel(["BTCUSDT"])
        self.harrvj_proxy = HarrvjKellyProxyAlphaModel(crypto_tickers)

        self.set_alpha(
            CompositeAlphaModel(
                self.trend_stocks,
                self.ema_composite,
                self.sector_mom,
                self.all_weather,
                self.ema_equity,
                self.ema_crypto,
                self.multic_proxy,
                self.harrvj_proxy,
            )
        )

        # Sleeve weights (IBKR 50% * intra, Binance 50% * intra)
        alpha_weights = {
            self.trend_stocks.name: 0.50 * 0.30,
            self.ema_composite.name: 0.50 * 0.25,
            self.sector_mom.name: 0.50 * 0.20,
            self.all_weather.name: 0.50 * 0.15,
            self.ema_equity.name: 0.50 * 0.10,
            self.ema_crypto.name: 0.50 * 0.50,
            self.multic_proxy.name: 0.50 * 0.30,
            self.harrvj_proxy.name: 0.50 * 0.20,
        }
        self.set_portfolio_construction(HybridPortfolioPCM(alpha_weights))

        # Transaction costs applied above via PercentFeeModel + PercentSlippageModel
        # (5bps equity / 10bps crypto commission + 5bps slippage), matching the
        # README Phase 2 cost basis. Walk-forward + multi-seed is Phase 3.

    def on_data(self, data):
        pass
