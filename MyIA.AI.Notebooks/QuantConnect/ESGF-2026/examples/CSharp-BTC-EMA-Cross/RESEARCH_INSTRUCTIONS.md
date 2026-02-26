# Research Notebook: BTC-EMA-Cross Robustness Validation

## Project Created

**QC Project ID**: 28265073
**QC Project Name**: BTC-EMA-Cross-Robustness-Research
**Created**: 2026-02-17
**Language**: Python

## Notebook Details

**Local Path**: `c:\dev\CoursIA\MyIA.AI.Notebooks\QuantConnect\ESGF-2026\examples\CSharp-BTC-EMA-Cross\research_robustness.ipynb`

**Purpose**: Validate the robustness of the BTC-EMA-Cross strategy (Project 21193838) across extended market regimes (2019-2025).

## Research Objectives

### 1. COVID Crash Survival (H1)
- Test if EMA(18,23) survives the March 2020 COVID crash (BTC -50% in 2 days)
- Target: Sharpe > 0.5 during crash period

### 2. Extended Period Performance (H2)
- Validate strategy from 2019-01-01 to 2025-12-31 (vs current 2021-10-16 start)
- Expected Sharpe: 0.7-0.9 (vs current 1.094 on shorter period)

### 3. Walk-Forward Efficiency (H3)
- Train on 252 days, test on 63 days (rolling quarterly)
- Target efficiency: > 60%

### 4. Parameter Robustness (H4)
- Test EMA periods: (12,26), (15,20), (18,23), (21,55), (30,50)
- Validate if current (18,23) is optimal across all market regimes

## Notebook Structure

The notebook contains 8 cells:

1. **Markdown**: Research context, hypotheses, methodology
2. **Code**: Setup QuantBook + load BTCUSD daily data 2019-01-01 → now
3. **Code**: Detect market regimes (bull/bear/sideways) via 126-day returns
4. **Code**: Vectorized backtest of EMA(18,23) on full period and by regime
5. **Code**: Grid search across 5 EMA parameter pairs
6. **Code**: Walk-forward validation (252d train, 63d test)
7. **Markdown**: Results template (to be filled after execution)
8. **Code**: Export recommendations as JSON

## Execution Instructions

### Option 1: Manual Upload to QuantConnect

1. Go to https://www.quantconnect.com/research
2. Open project **BTC-EMA-Cross-Robustness-Research** (ID: 28265073)
3. Upload the notebook file: `research_robustness.ipynb`
4. Execute all cells sequentially in the Research environment
5. Download the results and `research_robustness_recommendations.json`

### Option 2: API Upload (Future)

The notebook is ready for upload via QC MCP but requires handling large JSON payloads:

```python
# Requires: mcp__qc-mcp__create_file
# Project ID: 28265073
# File name: research_robustness.ipynb
# Content: <18KB JSON string>
```

## Expected Output

After execution, the notebook will produce:

### 1. Performance Metrics by Period

- **Full Period (2019-2025)**: Sharpe, Max DD, Total Return, # Trades
- **By Regime**: Bull, Bear, Sideways performance breakdown
- **Key Periods**:
  - COVID Crash (Mar 2020)
  - Bull Market 2020-2021
  - Bear Market 2022
  - Recovery 2023-2024

### 2. Parameter Grid Search

Table showing performance of 5 EMA parameter combinations sorted by Sharpe ratio.

### 3. Walk-Forward Results

- Average train Sharpe vs test Sharpe
- Walk-forward efficiency percentage
- Comparison to benchmark (fixed 18,23 params)

### 4. Recommendations JSON

File: `research_robustness_recommendations.json`

Contains:
- Validation status for all 4 hypotheses (PASS/FAIL)
- Recommended code changes to `Main.cs` (if validation successful)
- Performance metrics summary

## Expected Recommendation

If validation passes (likely scenario based on strong current Sharpe 1.094):

```csharp
// In Main.cs, change:
SetStartDate(2021, 10, 16);  // Current
// To:
SetStartDate(2019, 1, 1);    // Extended validation period
```

This change will:
- Include 2+ additional years of data (COVID crash, 2019-2020 volatility)
- Reduce sample bias risk
- Increase confidence in strategy robustness

**Estimated new Sharpe**: 0.7-0.9 (slight degradation expected, but still strong)

## Next Steps After Execution

1. Review the completed notebook output
2. Analyze the `research_robustness_recommendations.json` file
3. If validation successful (H2 PASS, H3 PASS):
   - Update `Main.cs` in Project 21193838 with new `SetStartDate(2019, 1, 1)`
   - Compile and run cloud backtest
   - Compare results to prediction
4. If validation fails:
   - Analyze which hypothesis failed (H1-H4)
   - Consider parameter adjustments or strategy enhancements
   - Document findings in project notes

## Technical Notes

- Uses 365 days/year for Sharpe calculation (crypto markets are 24/7)
- Vectorized backtest with state machine to avoid signal flip-flop
- Includes 0.1% entry/exit margins as per current strategy
- Look-ahead bias prevented via signal.shift(1)
- Regime detection: +30% (bull), -20% (bear), else sideways over 126 days

## Files Generated

- `research_robustness.ipynb` - Main research notebook
- `research_robustness_recommendations.json` - Automated recommendations
- `RESEARCH_INSTRUCTIONS.md` - This file

## Contact

For questions about this research:
- Original Strategy: CSharp-BTC-EMA-Cross (QC Project 21193838)
- Research Project: BTC-EMA-Cross-Robustness-Research (QC Project 28265073)
- Local Path: `MyIA.AI.Notebooks/QuantConnect/ESGF-2026/examples/CSharp-BTC-EMA-Cross/`
