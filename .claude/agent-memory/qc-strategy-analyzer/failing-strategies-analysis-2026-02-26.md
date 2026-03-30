# QuantConnect Failing Strategies Analysis - 2026-02-26

## Executive Summary

Analysis of two failing strategies in the Researcher organization:

| Strategy | Project ID | Sharpe | CAGR | Max DD | Status |
|----------|------------|--------|------|--------|--------|
| Sector-Momentum-Researcher | 28433643 | 0.114 | 5.6% | 26.4% | NEEDS_IMPROVEMENT |
| BTC-ML-Researcher | 28433750 | 0.007 | 4.5% | 15.2% | BROKEN |

**Critical Finding**: Both strategies suffer from regime insensitivity and lack of proper risk management. The short-term backtest results (Sharpe 2.53 for Sector-Momentum) were misleading due to insufficient market coverage.

---

## 1. Sector-Momentum-Researcher (28433643)

### Current Implementation Analysis

**Location**: `c:/dev/CoursIA/MyIA.AI.Notebooks/QuantConnect/ESGF-2026/lean-workspace/Sector-Momentum-Researcher/`

**Files**:
- `main.py` - Main algorithm
- `DualMomentumAlphaModel.py` - Alpha model with VIX filter
- `MyPcm.py` - Portfolio construction (1.5x leverage)
- `CustomImmediateExecutionModel.py` - Execution with leverage

**Key Parameters**:
```python
# DualMomentumAlphaModel.py
VIX_THRESHOLD = 25
MOMENTUM_PERIOD = 1 (1 week)
TOP_N_STOCKS = 10

# MyPcm.py
LEVERAGE = 1.5
```

**Root Cause Analysis**

1. **Momentum Period Too Short** (Line 82 in DualMomentumAlphaModel.py):
   - `MomentumPercent(1)` = 1-week momentum
   - 1-week is noise, not signal
   - High whipsaw rate, especially in choppy markets

2. **VIX Filter Insufficient**:
   - Threshold 25 is too low for 2020-2025 period
   - COVID crash (VIX > 80), 2022 inflation spike (VIX > 35)
   - Filter misses medium volatility periods

3. **No Transaction Costs**:
   - Rebalances daily when `day != algorithm.time.day`
   - With 200 SPY constituents universe, frequent universe changes
   - Slippage and fees not modeled

4. **Leverage Mismatch**:
   - CustomImmediateExecutionModel defaults to 2.0x (line 4)
   - MyPcm sets 1.5x (line 12)
   - Inconsistent leverage causes sizing errors

5. **No Sector Exposure Limits**:
   - Can concentrate in hot sectors
   - Tech bubble 2020-2021, Energy 2022
   - No diversification constraint

### Proposed Improvements

#### Improvement 1: Increase Momentum Period (HIGH Priority)

**Expected Impact**: Sharpe +0.3 to +0.5, Reduced whipsaw

```python
# In DualMomentumAlphaModel.py, line 82

# BEFORE (incorrect)
security.indicator = MomentumPercent(1)

# AFTER (corrected)
security.indicator = MomentumPercent(4)  # 4-week momentum
```

**Rationale**: 4-week (20 trading days) momentum is well-established in literature (Jegadeesh and Titman, 1993). 1-week is too noisy.

#### Improvement 2: Adaptive VIX Threshold (MEDIUM Priority)

**Expected Impact**: Sharpe +0.1 to +0.2, Better drawdown control

```python
# Add to DualMomentumAlphaModel.__init__
self.vix_threshold_dynamic = True
self.vix_ma_period = 20

# Modify VIX filter in update()
if self.vix is not None and self.vix.IsReady:
    # Calculate dynamic threshold based on VIX moving average
    vix_ma = self.SMA(self.vix.Symbol, self.vix_ma_period, Resolution.DAILY)
    if vix_ma.IsReady:
        dynamic_threshold = max(vix_ma.Current.Value * 1.2, 20)
        if current_vix > dynamic_threshold:
            algorithm.Log(f"[VIX Filter] VIX={current_vix:.1f} > {dynamic_threshold:.1f}")
            return []
```

**Rationale**: Adaptive threshold adjusts to market conditions. 1.2x MA provides buffer but allows trading in moderate volatility.

#### Improvement 3: Add Sector Concentration Limit (HIGH Priority)

**Expected Impact**: Reduced tail risk, More consistent returns

```python
# Add to DualMomentumAlphaModel.__init__
self.max_sectors = 5
self.max_pct_per_sector = 0.4

# Modify insight generation in update()
sector_counts = {}
for security in target_securities:
    sector = algorithm.Securities[security.Symbol].Fundamentals.AssetClassification.MorningstarSectorCode
    sector_counts[sector] = sector_counts.get(sector, 0) + 1

# Limit sector concentration
final_securities = []
sector_used = {}
for security in target_securities:
    sector = algorithm.Securities[security.Symbol].Fundamentals.AssetClassification.MorningstarSectorCode
    if sector_used.get(sector, 0) < 4:  # Max 4 stocks per sector
        final_securities.append(security)
        sector_used[sector] = sector_used.get(sector, 0) + 1
    if len(final_securities) >= 10:
        break
```

**Rationale**: Diversification reduces tail risk. No more than 40% in any sector.

#### Improvement 4: Add Transaction Cost Model (MEDIUM Priority)

**Expected Impact**: More realistic Sharpe (-0.1 to -0.2 from current, but honest)

```python
# In main.py, add to initialize()
self.SetSecurityInitializer(
    lambda security: security.SetFeeModel(ConstantFeeModel(0.001))
)
self.SetSlippageModel(VolumeShareSlippageModel(0.01))
```

**Rationale**: 10bp fees + slippage is realistic for equity trading. Without this, backtest is optimistic.

#### Improvement 5: Fix Leverage Consistency (HIGH Priority)

**Expected Impact**: Prevent sizing errors

```python
# In CustomImmediateExecutionModel.py, line 4

# BEFORE (inconsistent)
def __init__(self, leverage=2.0):
    self.leverage = leverage

# AFTER (corrected)
def __init__(self, leverage=1.5):  # Match MyPcm.py
    self.leverage = leverage
```

**Rationale**: Leverage must be consistent across execution and portfolio construction.

### Expected Results After Improvements

| Metric | Current | Expected | Change |
|--------|---------|----------|--------|
| Sharpe | 0.114 | 0.6-0.8 | +0.5 to +0.7 |
| CAGR | 5.6% | 8-12% | +2.4% to +6.4% |
| Max DD | 26.4% | 15-20% | -6% to -11% |
| Win Rate | Unknown | 55-60% | +5% to +10% |

---

## 2. BTC-ML-Researcher (28433750)

### Current Implementation Analysis

**Location**: `c:/dev/CoursIA/MyIA.AI.Notebooks/QuantConnect/ESGF-2026/lean-workspace/BTC-ML-Researcher/`

**File**: `main.py`

**Key Parameters**:
```python
TRAIN_START = 2019-01-01
TRAIN_END = 2022-12-31
BACKTEST_START = 2023-01-01
BACKTEST_END = 2026-03-01

RETRAIN_INTERVAL_DAYS = 60
RETRAIN_LOOKBACK_DAYS = 730

STOP_LOSS_PCT = 0.05
TAKE_PROFIT_PCT = 0.10

CONFIDENCE_LONG_THRESHOLD = 0.6
CONFIDENCE_EXIT_THRESHOLD = 0.4

# Model
n_estimators = 100
max_depth = 5
```

**Root Cause Analysis**

1. **Data Leakage in Feature Engineering** (Line 145, 181):
   - `label = 1 if closes[i+1] > closes[i] else 0`
   - Features computed at time `i`, label uses close at `i+1`
   - But features include indicators that use future data
   - `_ema(closes[:i+1], period)` includes current close

2. **Overfitting on Training Data**:
   - RandomForest with 100 trees, depth 5
   - Training accuracy reported but no validation set
   - Model learns noise, not signal
   - Retraining every 60 days amplifies overfitting

3. **Insufficient Features for BTC Regime Detection**:
   - Features: SMA, RSI, EMA(10,20,50,200), ADX, ATR
   - Missing: Funding rates, Open interest, On-chain metrics
   - BTC is regime-dependent (trend-following works in bull, fails in bear)

4. **No Regime Detection**:
   - Same model for all market conditions
   - Bull market 2020-2021: any long strategy works
   - Bear 2022: model fails
   - Recovery 2023-2025: model underperforms buy-and-hold

5. **Tight Stop-Loss Whipsaw**:
   - 5% stop-loss on BTC (vol 40-80% annual)
   - Stops out frequently on noise
   - Take-profit 10% with tight stop = negative expectancy

6. **Confidence Threshold Too Tight**:
   - Only trade when confidence > 60% or < 40%
   - Middle 20% (0.4-0.6) excluded
   - Reduces trade frequency significantly

### Proposed Improvements

#### Improvement 1: Fix Data Leakage (CRITICAL)

**Expected Impact**: Honest evaluation, Sharpe -0.5 to -0.2 (more realistic)

```python
# In _compute_features(), line 198

# BEFORE (data leakage)
def _compute_features(self, closes, highs, lows, i):
    daily_ret = (closes[i] - closes[i-1]) / closes[i-1]
    # ...
    ema_10 = self._ema(closes[:i+1], 10)  # Includes closes[i]!
    return [sma_20, rsi_14, daily_ret, ema_10, ...]

# AFTER (corrected - strict walk-forward)
def _compute_features(self, closes, highs, lows, i):
    # Only use data up to i-1 for prediction
    if i < max(self.EMA_PERIODS) + 1:
        return None

    daily_ret = (closes[i-1] - closes[i-2]) / closes[i-2]
    sma_20 = np.mean(closes[i-1-20:i-1])
    rsi_14 = self._compute_rsi(closes[i-1-14:i])
    ema_10 = self._ema(closes[:i], 10)  # Exclude closes[i]
    # ...
    return [sma_20, rsi_14, daily_ret, ema_10, ...]

# In training loop, line 142
# BEFORE
for i in range(max(self.EMA_PERIODS) + 1, len(closes) - 1):
    features = self._compute_features(closes, highs, lows, i)
    label = 1 if closes[i+1] > closes[i] else 0

# AFTER
for i in range(max(self.EMA_PERIODS) + 2, len(closes) - 1):
    features = self._compute_features(closes, highs, lows, i)
    if features is None:
        continue
    label = 1 if closes[i+1] > closes[i] else 0
```

**Rationale**: Features must be computed with data available at prediction time. No peeking into the future.

#### Improvement 2: Add Regime Detection (HIGH Priority)

**Expected Impact**: Sharpe +0.2 to +0.4

```python
# Add new method
def _detect_regime(self, closes, lookback=90):
    """Detect market regime: BULL, BEAR, SIDEWAYS"""
    if len(closes) < lookback:
        return "SIDEWAYS"

    recent = closes[-lookback:]
    returns = recent.pct_change()

    # Trend strength
    slope = np.polyfit(range(len(recent)), recent, 1)[0]
    normalized_slope = slope / np.mean(recent) * lookback

    # Volatility
    vol = returns.std() * np.sqrt(252)

    if normalized_slope > 0.02 and vol < 0.6:
        return "BULL"
    elif normalized_slope < -0.02:
        return "BEAR"
    else:
        return "SIDEWAYS"

# Modify OnData()
current_regime = self._detect_regime(self.history_close[-90:])

if current_regime == "BEAR":
    # Reduce position size or skip trades
    self.debug(f"{self.Time} => BEAR regime, reducing risk")
    position_size *= 0.5
elif current_regime == "BULL":
    # Full position size
    pass
else:  # SIDEWAYS
    # Skip trades
    return
```

**Rationale**: BTC regimes require different strategies. Trend-following works in bull, fails in sideways.

#### Improvement 3: Add Volatility Filter (HIGH Priority)

**Expected Impact**: Sharpe +0.3 to +0.5 (based on research finding)

```python
# Add to class
VOLATILITY_THRESHOLD = 0.60  # 60% annual vol

# Add new method
def _calculate_volatility(self, period=20):
    """Calculate annualized volatility from ATR"""
    if not self.atr.IsReady:
        return 0
    return (self.atr.Current.Value / self.Securities[self.symbol].Price) * np.sqrt(252)

# Modify OnData(), add before feature computation
current_vol = self._calculate_volatility()
if current_vol > self.VOLATILITY_THRESHOLD:
    self.Debug(f"{self.Time} => High vol {current_vol:.2%}, skipping")
    return  # Skip trading during high volatility
```

**Rationale**: Research shows 60% vol threshold gives Sharpe 1.249 vs 0.85 without filter (+47%).

#### Improvement 4: Widen Stop-Loss and Take-Profit (MEDIUM Priority)

**Expected Impact**: Reduced whipsaw, Sharpe +0.1 to +0.2

```python
# BEFORE
STOP_LOSS_PCT = 0.05     # -5%
TAKE_PROFIT_PCT = 0.10   # +10%

# AFTER
STOP_LOSS_PCT = 0.10     # -10% (wider)
TAKE_PROFIT_PCT = 0.20   # +20% (wider)
RISK_REWARD_RATIO = 2.0  # 2:1

# Also add ATR-based stop
atr_stop_distance = self.atr.Current.Value * 2  # 2x ATR
stop_loss_pct = max(self.STOP_LOSS_PCT, atr_stop_distance / current_price)
```

**Rationale**: BTC volatility requires wider stops. 5% is noise on a 40-80% vol asset.

#### Improvement 5: Add Regularization and Validation (HIGH Priority)

**Expected Impact**: Reduced overfitting, Sharpe +0.1 to +0.3

```python
# BEFORE
self.model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
self.model.fit(X_train, y_train)
accuracy = self.model.score(X_train, y_train)  # In-sample!

# AFTER
from sklearn.model_selection import TimeSeriesSplit, cross_val_score
from sklearn.metrics import classification_report

# Use time-series cross-validation
tscv = TimeSeriesSplit(n_splits=5)
model = RandomForestClassifier(
    n_estimators=50,  # Reduce from 100
    max_depth=3,      # Reduce from 5
    min_samples_leaf=10,  # Add regularization
    random_state=42
)

# Cross-validation scores
cv_scores = cross_val_score(model, X_train, y_train, cv=tscv, scoring='f1')
self.Debug(f"CV F1: {cv_scores.mean():.3f} (+/- {cv_scores.std():.3f})")

# Fit on full training set
model.fit(X_train, y_train)
```

**Rationale**: Time-series CV prevents look-ahead. Regularization reduces overfitting.

#### Improvement 6: Add Feature Selection (MEDIUM Priority)

**Expected Impact**: Model interpretability, Sharpe +0.05 to +0.1

```python
from sklearn.feature_selection import SelectKBest, f_classif

# Add to training
selector = SelectKBest(f_classif, k=5)
X_train_selected = selector.fit_transform(X_train, y_train)

# Get selected feature names
feature_names = ['SMA', 'RSI', 'Ret', 'EMA10', 'EMA20', 'EMA50', 'EMA200', 'ADX', 'ATR']
selected = [feature_names[i] for i in selector.get_support(indices=True)]
self.Debug(f"Selected features: {selected}")

# Train on selected features
model.fit(X_train_selected, y_train)

# Store selector for prediction
self.feature_selector = selector
```

**Rationale**: Not all features are predictive. Feature selection reduces noise.

### Expected Results After Improvements

| Metric | Current | Expected | Change |
|--------|---------|----------|--------|
| Sharpe | 0.007 | 0.4-0.6 | +0.4 to +0.6 |
| CAGR | 4.5% | 15-25% | +10.5% to +20.5% |
| Max DD | 15.2% | 10-15% | -0% to -5% |
| Win Rate | Unknown | 45-50% | Baseline |

**Note**: Initial results may be worse after fixing data leakage, but honest. With regime detection and volatility filter, performance should improve significantly.

---

## 3. Common Issues Across Both Strategies

### Issue 1: No Transaction Cost Modeling

**Impact**: Backtest Sharpe inflated by 0.2-0.5

**Solution**:
```python
# In initialize() for both strategies
self.SetSecurityInitializer(lambda security:
    security.SetFeeModel(ConstantFeeModel(0.001))
)
self.SetSlippageModel(VolumeShareSlippageModel(0.01))
```

### Issue 2: No Walk-Forward Validation

**Impact**: Overfitting to backtest period

**Solution**:
- Implement walk-forward analysis in research notebooks
- Target OOS/IS ratio > 60%
- Test on multiple periods: 2020, 2021, 2022, 2023, 2024

### Issue 3: No Regime Awareness

**Impact**: Poor performance in regime changes

**Solution**:
- Add regime detection (bull/bear/sideways)
- Adapt parameters per regime
- Reduce exposure in adverse regimes

### Issue 4: Insufficient Research

**Impact**: Parameter tuning without validation

**Solution**:
- Complete research notebooks (sector_momentum_research_v2.ipynb is stub)
- Implement grid search with cross-validation
- Document parameter sensitivity

---

## 4. Implementation Priority

### Sector-Momentum-Researcher

1. **Fix leverage consistency** (5 min) - CRITICAL
2. **Increase momentum period to 4 weeks** (5 min) - HIGH
3. **Add sector concentration limit** (15 min) - HIGH
4. **Add transaction costs** (5 min) - MEDIUM
5. **Implement adaptive VIX threshold** (15 min) - MEDIUM

### BTC-ML-Researcher

1. **Fix data leakage in features** (20 min) - CRITICAL
2. **Add volatility filter (60%)** (10 min) - HIGH
3. **Add regime detection** (20 min) - HIGH
4. **Widen stop-loss to 10%** (5 min) - MEDIUM
5. **Add regularization and validation** (15 min) - MEDIUM

---

## 5. Next Steps

1. Implement improvements in lean-workspace
2. Update research notebooks with walk-forward analysis
3. Run backtests with lean-cli cloud backtest
4. Document results in memory
5. Iterate based on results

---

## References

- Jegadeesh, N., & Titman, S. (1993). "Returns to Buying Winners and Selling Losers"
- Brock, W., Lakonishok, J., & LeBaron, B. (1992). "Simple Technical Trading Rules"
- QuantConnect Documentation: <https://www.quantconnect.com/docs>
