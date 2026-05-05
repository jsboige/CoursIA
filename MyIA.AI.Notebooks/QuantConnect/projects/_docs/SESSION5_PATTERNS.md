# SESSION 5 - AlphaModel Framework Patterns

**Date:** 2026-03-14
**Author:** po-2024 (Claude Code)
**Status:** Phase 1 Complete, Phase 2-4 Pending

## Overview

SESSION 5 focuses on migrating standalone strategies to QuantConnect's Algorithm Framework using AlphaModel and PortfolioConstructionModel patterns. This enables modular strategy composition and professional-grade portfolio management.

## Key Patterns

### 1. AlphaModel Pattern

AlphaModels generate insights (UP/DOWN/FLAT signals) for securities. Each alpha wraps a specific strategy logic.

```python
class MyAlpha(AlphaModel):
    def __init__(self, tickers):
        super().__init__()
        self.name = "MyAlpha"  # Used for grouping in PCM
        self.tickers = tickers
        self.lookback = 252  # 1 year
        self.resolution = Resolution.DAILY

    def update(self, algorithm, data):
        insights = []
        for symbol in self.tickers:
            # Strategy logic here
            if self._should_long(symbol, data):
                insights.append(Insight.price(
                    symbol,
                    timedelta(days=30),  # Period
                    InsightDirection.UP,   # Direction
                    weight=None,            # Optional: explicit weight
                    source_model=self.name  # CRITICAL: for PCM grouping
                ))
        return insights

    def _should_long(self, symbol, data):
        # Implement strategy logic
        return True
```

**Key Points:**
- `source_model` attribute groups insights by alpha in PortfolioConstructionModel
- `Insight.period` determines how long the signal is valid
- `Insight.weight` can provide explicit allocation hints (optional)

### 2. PortfolioConstructionModel Pattern (PCM)

PCMs convert insights to portfolio targets (percentages).

#### Equal-Weight PCM (Simple)

```python
class EqualWeightPCM(PortfolioConstructionModel):
    def determine_target_percent(self, active_insights):
        targets = {}
        active = [i for i in active_insights if i.direction != InsightDirection.FLAT]
        if active:
            weight = 1.0 / len(active)
            for insight in active:
                targets[insight] = insight.direction * weight
        return targets
```

#### Multi-Strategy PCM (Advanced)

For composite strategies combining multiple alphas:

```python
class MultiStrategyPCM(PortfolioConstructionModel):
    def __init__(self, alpha_allocations, rebalance=timedelta(days=31)):
        super().__init__()
        self.alpha_allocations = alpha_allocations  # {"AlphaName": 0.50}
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        result = {}

        # Group insights by source alpha
        by_alpha = {}
        for insight in active_insights:
            source = insight.source_model or "Unknown"
            by_alpha.setdefault(source, []).append(insight)

        for alpha_name, insights in by_alpha.items():
            capital_slice = self.alpha_allocations.get(alpha_name, 0)
            if capital_slice <= 0:
                continue

            active = [i for i in insights if i.direction != InsightDirection.FLAT]

            # Check for explicit weight hints
            has_weights = all(i.weight is not None for i in active)

            if has_weights:
                # Use explicit weights (e.g., AllWeather fixed weights)
                for insight in active:
                    result[insight] = insight.direction * insight.weight * capital_slice
            else:
                # Equal weight within alpha's slice (e.g., TrendStocks)
                per_symbol = capital_slice / len(active)
                for insight in active:
                    result[insight] = insight.direction * per_symbol

        return result
```

### 3. Composite Algorithm Pattern

Combine multiple alphas using CompositeAlphaModel:

```python
class FrameworkCompositeStrategy(QCAlgorithm):
    def initialize(self):
        # Define universes
        trend_tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        aw_tickers = ["SPY", "IEF", "GLD", "XLP"]

        # Add securities
        for ticker in trend_tickers + aw_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        # Set alpha (composite)
        self.set_alpha(CompositeAlphaModel(
            TrendStocksAlpha(trend_tickers),
            AllWeatherAlpha(aw_tickers)
        ))

        # Set portfolio construction
        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "TrendStocks": 0.75,  # 75% capital
                "AllWeather": 0.25,   # 25% capital
            },
            rebalance=timedelta(days=31)  # Monthly rebalance
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
```

## SESSION 5 Projects

### AlphaModel Implementations

| Project | ID | Description | Status |
|---------|----|-------------|--------|
| **EMA-Cross-Alpha** | 28885488 | EMA 20/50 crossover multi-stock | ✅ BuildSuccess |
| **TrendStocks-Alpha** | 28885507 | EMA 20/50 + SMA200 trend filter 15 stocks | ✅ BuildSuccess |

### Composite Implementations

| Project | ID | Alphas | Allocation | Status |
|---------|----|--------|------------|--------|
| **Framework_Composite_EMATrend** | 28911253 | EMA-Cross + TrendStocks | EMA50/Trend50 | ✅ BuildSuccess |
| **Framework_Composite_TrendWeather** | - | TrendStocks + AllWeather | T75/AW25 | ✅ v1.5 (Sharpe 1.155) |
| **Framework_Composite_FamaFrenchAllWeather** | - | FamaFrench + AllWeather | FF50/AW50 | ⏸️ Pending deployment |

## Best Practices

### 1. Monthly Emission Patterns

When AlphaModels generate insights on different schedules, set emission at month-start for consistent rebalancing:

```python
def update(self, algorithm, data):
    # Only emit insights on first trading day of month
    if algorithm.time.month != self._last_emission_month:
        self._last_emission_month = algorithm.time.month
        # Generate insights...
```

### 2. Risk-Adjusted Momentum

```python
def _risk_adjusted_momentum(self, algorithm, symbol):
    # 12-month momentum (skip 1-month)
    history = algorithm.history[symbol, TradeBar, self.lookback]
    past_price = history.iloc[-21].close   # 1 month ago
    skip_price = history.iloc[0].close      # 12 months ago
    momentum_return = (skip_price / past_price) - 1

    # Realized volatility (63-day window)
    recent_closes = history.tail(63).close
    daily_returns = recent_closes.pct_change().dropna()
    realized_vol = daily_returns.std() * np.sqrt(252)

    # Risk-adjusted momentum
    return momentum_return / realized_vol
```

### 3. Capital Slice Allocation

For composite strategies:
- Assign each alpha a capital slice (e.g., TrendStocks 75%, AllWeather 25%)
- Within each slice, either equal-weight or use explicit weight hints
- Total allocation always sums to 100%

## Performance Metrics

### Target Metrics

| Metric | Target | Description |
|--------|--------|-------------|
| **Sharpe Ratio** | > 0.5 | Risk-adjusted return (robust) |
| **CAGR** | > 10% | Compound annual growth rate |
| **Max Drawdown** | < 30% | Maximum peak-to-trough decline |
| **PSR** | > 95% | Probability Sharpe > 0 |

### Robustness Testing

- **Period:** 2015-2025 (10+ years)
- **Market Regimes:** Bull (2015-2018, 2020-2022), Bear (2018, 2022), Crisis (2020)
- **Validation:** Strategy must perform across all regimes

## Common Pitfalls

### 1. Missing `source_model` in Insights

❌ Wrong: Insights won't group correctly in MultiStrategyPCM
```python
Insight.price(symbol, timedelta(days=30), InsightDirection.UP)
```

✅ Correct:
```python
Insight.price(symbol, timedelta(days=30), InsightDirection.UP, source_model=self.name)
```

### 2. Incorrect Timedelta Usage

❌ Wrong: `Time.DAILY` doesn't exist
```python
insight_period = Time.DAILY  # AttributeError
```

✅ Correct:
```python
insight_period = timedelta(days=30)
```

### 3. Security Investability Check

❌ Wrong: `security.is_investable` doesn't exist
```python
if security.is_investable:  # AttributeError
```

✅ Correct:
```python
if security.type == SecurityType.EQUITY:
```

## Next Steps

1. **Phase 2:** Run robustness backtests (2015-2025) on all 8 priority projects
2. **Phase 3:** Deploy Composite FF+AW to QC cloud and run allocation sweep
3. **Documentation:** Create pedagogical notebooks for ESGF course

## Resources

- [QuantConnect Algorithm Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/framework-introduction)
- [AlphaModel Documentation](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework/alpha-model)
- [PortfolioConstructionModel](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework/portfolio-construction)

---

**Last Updated:** 2026-03-14
**Session:** 43cdc462-76e8-4437-bb81-c49ca84dbd66
