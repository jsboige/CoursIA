# BTC-MachineLearning: Robustness Research Summary

**Date**: 2026-02-17
**Project**: BTC-MachineLearning (ID: 21047688)
**Status**: Research notebook created, ready for execution in QuantConnect

---

## What Was Created

### 1. research_robustness.ipynb (Main Deliverable)

A comprehensive 10-cell Jupyter notebook for QuantConnect Research environment that validates the ML strategy through:

**5 Key Analyses**:
1. **Extended Training Period**: Does 5 years (2017-2022) beat 2 years (2021-2022)?
2. **Feature Stability**: Which features matter in bull vs bear markets?
3. **Walk-Forward Validation**: The gold standard - 20+ rolling train/test windows
4. **Optimal Retraining**: Compare 30, 60, 90 day retraining frequencies
5. **ML vs HODL**: Does the strategy actually beat buy-and-hold?

**Structure**:
- **Cell 1**: Markdown introduction (ML challenges, why walk-forward matters)
- **Cell 2**: Load BTC data from 2017-01-01 to present (~3000 bars)
- **Cell 3**: Compute 9 ML features + data leakage check
- **Cell 4**: Test H1 (training period impact)
- **Cell 5**: Test H2 (feature importance by regime) with heatmap
- **Cell 6**: Walk-forward validation (730d train, 90d test, 60d retrain)
- **Cell 7**: Test H3 (retraining frequency comparison)
- **Cell 8**: Test H4 (ML vs buy-and-hold benchmark)
- **Cell 9**: Findings markdown summary
- **Cell 10**: Recommendations JSON for main.py updates

### 2. RESEARCH.md (Documentation)

Complete guide covering:
- Motivation and research questions
- Methodology (walk-forward, features, metrics)
- Execution instructions (QuantConnect + local demo)
- Expected results and success criteria
- Limitations and next steps

### 3. research_robustness_local.py (Demo Script)

Standalone Python script demonstrating the analysis with synthetic data (for local testing without QuantConnect access).

---

## Why This Matters

### Current Strategy Risks

The existing main.py has **never been backtested**:
- Training: 2021-2022 (2 years) - **arbitrary choice**
- Testing: 2023-2024 (1.5 years) - **never actually tested**
- Retraining: 30 days - **not validated**
- Expected Sharpe: **unknown**

**Without this research**:
- ❌ No idea if 2021-2022 training is optimal
- ❌ Don't know which features are stable vs noisy
- ❌ Can't tell if 30-day retraining is best
- ❌ Unknown if ML beats simple buy-and-hold
- ❌ Risk of overfitting to one lucky period

### What Walk-Forward Validation Reveals

Traditional backtesting: Train on period A, test on period B → **One data point**

Walk-forward: Train/test on 20+ rolling windows → **Robust statistical validation**

```
Window 1:  Train 2017-2019 → Test 2019-Q1
Window 2:  Train 2017-2019 → Test 2019-Q2 (retrained)
Window 3:  Train 2018-2020 → Test 2019-Q3
...
Window 20: Train 2022-2024 → Test 2024-Q4
```

**This reveals**:
- Is performance consistent or just one lucky period?
- Does the model adapt to regime changes?
- Are recent windows performing well (or degrading)?
- What's the realistic expected Sharpe (median of 20 windows)?

---

## How to Execute

### Step 1: Upload to QuantConnect

1. Go to [QuantConnect](https://www.quantconnect.com)
2. Open project **21047688** (BTC-MachineLearning)
3. Click **Research** tab
4. Upload `research_robustness.ipynb`

### Step 2: Execute Sequentially

Run cells 1-10 from top to bottom. Expected runtime: **10-15 minutes**

**Cell 2** (data loading) may take longest (~2-3 min for 3000 bars from 2017).

### Step 3: Interpret Results

#### Key Outputs to Watch

**Cell 4** (Extended Training):
```
VERDICT:
✓ H1 CONFIRMED: 5Y training improves Sharpe by X%
  Sharpe: 0.XXX (2Y) → 0.XXX (5Y)
```
→ Tells you whether to change `TRAIN_START` from 2021-01-01 to 2017-01-01

**Cell 5** (Feature Importance):
```
Feature Stability (std dev across regimes):
  ema_10      0.XXX  ← Low std = stable
  rsi         0.XXX
  adx         0.XXX  ← High std = regime-dependent
```
→ Consider removing unstable features or adding regime detection

**Cell 6** (Walk-Forward):
```
WALK-FORWARD SUMMARY
Total windows: 22
Average Sharpe: 0.XXX ± 0.XXX
Positive Sharpe windows: 15 / 22 (68%)
```
→ **This is your realistic expected Sharpe** (not the one-period backtest)

**Cell 7** (Retraining Frequency):
```
VERDICT:
✓ Optimal retraining interval: 60 days
  Mean Sharpe: 0.XXX
```
→ Tells you whether to change `RETRAIN_INTERVAL_DAYS` from 30 to 60/90

**Cell 8** (ML vs BnH):
```
VERDICT - ML vs Buy-and-Hold
✓ H4 CONFIRMED: ML strategy beats buy-and-hold on risk-adjusted basis
  ML Sharpe: 0.XXX vs BnH Sharpe: 0.XXX
```
→ Validates whether the ML complexity is worth it

### Step 4: Update main.py

Based on Cell 10 recommendations JSON, update:

```python
# Example changes
TRAIN_START = datetime(2017, 1, 1)  # If H1 confirmed
RETRAIN_INTERVAL_DAYS = 60  # If H3 suggests 60 > 30
# Remove low-importance features if identified
```

### Step 5: Compile and Backtest

```bash
# Via MCP QC (or manually in web UI)
qc compile 21047688
qc backtest 21047688  # Via web UI (API requires paid account)
```

**Validation**: Backtest Sharpe should match walk-forward mean Sharpe (±30%).

If backtest Sharpe = 1.2 but walk-forward mean = 0.4 → **overfitting detected**

---

## Expected Findings

### Realistic Expectations for Crypto ML

**Sharpe Ratios**:
- Buy-and-hold BTC (2023-2025): ~0.3-0.5 (high return, high volatility)
- Good ML strategy: 0.5-0.8 (better risk-adjusted)
- Excellent ML: > 1.0 (rare for crypto daily signals)

**Accuracy**:
- Random: 50%
- Baseline: 52-55% (directional edge)
- Good: 55-60%
- Suspicious: > 65% (possible data leakage)

**Walk-Forward Consistency**:
- Positive windows: > 60% is good
- Mean Sharpe: > 0.4 is realistic
- Std Sharpe: < 0.5 is stable

### Likely Outcomes

#### Hypothesis 1: Extended Training

**Likely**: ✓ CONFIRMED (5Y > 2Y)
- Reason: 2017-2022 includes full bull/bear cycles
- Expected improvement: 10-20% Sharpe increase
- Trade-off: Slightly lower peak performance but better stability

#### Hypothesis 2: Feature Stability

**Likely**: Features will cluster into:
- **Stable** (work in all regimes): daily_return, sma_ratio, ema_10
- **Bull-specific** (momentum): ema_20, ema_50, adx
- **Bear-specific** (mean-reversion): rsi, atr

**Action**: Consider regime detection or separate models

#### Hypothesis 3: Retraining Frequency

**Likely**: ✓ 60 days optimal
- 30 days: Too reactive, high variance
- 60 days: Sweet spot (2 months of data)
- 90 days: Too slow to adapt to crypto volatility

#### Hypothesis 4: ML vs BnH

**Likely**: ✓ CONFIRMED on Sharpe, ✗ REJECTED on total return
- ML wins on risk-adjusted (Sharpe)
- BnH wins on absolute return
- ML reduces drawdowns (key benefit)

**Why?** Crypto HODL is hard to beat on return, but ML can reduce volatility.

#### Hypothesis 5: Walk-Forward Consistency

**Likely**: ✓ CONFIRMED if mean Sharpe > 0.4 and 60%+ positive windows

**Red flags** if:
- Only first few windows positive → overfitting to old data
- Recent windows all negative → model degrading
- Huge variance between windows → unstable

---

## Next Steps After Execution

### Immediate (After Notebook Run)

1. **Fill Cell 10 recommendations JSON** with actual numbers from outputs
2. **Screenshot key results**:
   - Walk-forward Sharpe plot (Cell 6)
   - Feature importance heatmap (Cell 5)
   - Retraining comparison (Cell 7)
3. **Document findings** in project notes

### Short-term (This Week)

1. **Update main.py** based on recommendations
2. **Compile** updated strategy
3. **Backtest** via QuantConnect web UI
4. **Validate**: Compare backtest Sharpe to walk-forward mean

### Medium-term (This Month)

1. **Paper trade** if backtest validates walk-forward
2. **Monitor** live performance vs expected Sharpe
3. **Retrain schedule**: Set up automated retraining if deploying
4. **Transaction costs**: Add spread/fees to backtest

---

## Success Criteria

Research is **SUCCESSFUL** if:
- ✓ Notebook executes without errors
- ✓ Walk-forward mean Sharpe > 0.4
- ✓ > 60% positive windows
- ✓ No data leakage (training accuracy < 0.65)
- ✓ Clear recommendation on TRAIN_START and RETRAIN_INTERVAL

Research is **FAILED** if:
- ✗ All windows negative Sharpe → model broken
- ✗ Data leakage detected → features using future info
- ✗ Walk-forward Sharpe variance > 2.0 → too unstable
- ✗ Cannot beat buy-and-hold on Sharpe → not worth complexity

---

## Key Insights Expected

### What Makes a Good ML Trading Strategy?

From the notebook, you'll learn:

1. **Training Data**: How much history is needed? (2Y vs 5Y)
2. **Feature Selection**: Which features are robust vs noisy?
3. **Retraining**: How often to update the model?
4. **Realistic Expectations**: What Sharpe is achievable?
5. **Regime Awareness**: Does the model adapt to market changes?

### Red Flags to Watch For

- **Data leakage**: Training accuracy > 0.65 → features using future info
- **Lucky period**: Only 1-2 windows positive → not robust
- **Degradation**: Recent windows worse than old → model aging
- **Overfitting**: Backtest Sharpe >> walk-forward Sharpe → not generalizing

### Green Flags

- **Consistent**: 60%+ positive windows across regimes
- **Stable**: Sharpe std < 0.5 (not too volatile)
- **Adaptive**: Recent windows still positive (model working)
- **Robust**: Backtest matches walk-forward (no overfitting)

---

## Files Created

```
BTC-MachineLearning/
├── main.py (existing, 335 lines)
├── research_robustness.ipynb (NEW - 10 cells, execute in QC Research)
├── research_robustness_local.py (NEW - demo script with synthetic data)
├── RESEARCH.md (NEW - complete documentation)
└── RESEARCH_SUMMARY.md (NEW - this file)
```

---

## Questions Before Executing?

### Q: Why can't I run this locally?

**A**: The notebook uses QuantConnect's QuantBook API to load real BTC data from Binance. This API only works in QuantConnect's environment. The local script is a demo with synthetic data.

### Q: How long will it take?

**A**: 10-15 minutes total. Most time is Cell 6 (walk-forward) running 20+ train/test cycles.

### Q: What if results are bad (all negative Sharpe)?

**A**: This is valuable information! It means:
1. Current strategy assumptions are flawed
2. Features have no predictive power
3. Need to rethink approach (different features, resolution, or method)

Better to know now via walk-forward than lose money in production.

### Q: Can I modify the notebook?

**A**: Yes! You can:
- Change walk-forward parameters (train_days, test_days, retrain_interval)
- Add more retraining frequencies to test
- Test different confidence thresholds (currently 0.6)
- Add transaction cost modeling
- Try different ML models (SVM, XGBoost, etc.)

### Q: What if I don't have a paid QC account for backtesting?

**A**: Walk-forward validation IS the backtest! It's actually **more rigorous** than a single-period backtest. The notebook gives you everything you need to validate the strategy. Official QC backtest is just for final confirmation.

---

## Final Recommendation

**EXECUTE THIS NOTEBOOK BEFORE DEPLOYING THE STRATEGY LIVE.**

Current main.py has:
- ❌ Never been backtested
- ❌ Arbitrary training period (2021-2022)
- ❌ Unvalidated retraining frequency (30 days)
- ❌ Unknown expected Sharpe

After notebook execution, you'll have:
- ✓ 20+ out-of-sample test windows
- ✓ Validated optimal training period
- ✓ Optimal retraining frequency
- ✓ Realistic Sharpe expectation
- ✓ Feature importance insights
- ✓ Confidence that strategy is robust (or knowledge that it's not)

**Time investment**: 15 minutes to run notebook + 30 minutes to analyze results

**Value**: Avoid potentially deploying a broken strategy or identify clear improvements

---

**Next Action**: Upload `research_robustness.ipynb` to QuantConnect project 21047688 and execute in Research environment.
