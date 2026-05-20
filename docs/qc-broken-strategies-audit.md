# QC Broken Strategies Audit — Root Cause Analysis

**Date**: 2026-05-08
**Author**: myia-po-2024 (Cycle 10, Track 2)
**Scope**: 5 BROKEN strategies identified from the QC Cloud catalog (118 projects)
**Methodology**: Read full source code + backtest history for each strategy, identify structural root cause.

---

## Summary Table

| # | Strategy | Project ID | Best Sharpe | Root Cause | Fix Difficulty |
|---|----------|-----------|-------------|------------|----------------|
| 1 | PairsTrading | 28693651 | -1.152 | Cointegration breakdown in ETF pairs | Hard — need fundamentally different pair selection |
| 2 | ESGF-RL-DQN-Trading | 29687000 | -0.341 | Linear Q-function too simple, undertrained | Hard — need deep Q-network or different RL algorithm |
| 3 | TrendFilteredMeanReversion | 28817422 | -0.129 | ~85% cash drag in bull market | Medium — need always-invested overlay or regime switch |
| 4 | ETF-Pairs-Researcher | 28433746 | -0.002 | Same cointegration flaw, 8 iterations confirm dead end | Hard — same as #1 |
| 5 | HandsOn-Ex19-FinBERT-Sentiment | 29936073 | 0.000 (zero trades) | FinBERT/transformers unavailable in QC Cloud | Unfixable — platform limitation |

---

## Strategy 1: PairsTrading (28693651)

### Current State
- **Sharpe**: -1.152 | **CAGR**: -0.568% | **MaxDD**: 12.4% | **Net Profit**: -3.54%
- **Pairs**: GLD/SLV, TLT/IEF, EWA/EWC (same as ETF-Pairs-Researcher)
- **Method**: OLS hedge ratio (252-day), z-score entry/exit (2.5/0.5/4.5), lookback 120

### Root Cause: Structural Cointegration Breakdown

ETF pairs do not maintain stable cointegration over multi-year periods. The OLS hedge ratio (slope from linregress of price_A on price_B over 252 days) is a rolling estimate that lags structural shifts. When cointegration breaks:

1. The spread drifts (non-stationary), generating false z-score signals
2. Positions opened on "mean reversion" converge to the wrong mean
3. The stop-zscore (4.5) is too wide — by the time it triggers, significant losses have accumulated

**Key evidence**: The same 3 pairs were tried across 2 separate projects (this one + ETF-Pairs-Researcher) with 11+ combined iterations, parameter sweeps, and framework changes. None achieved sustained positive Sharpe.

### Recommended Fix
- Replace OLS with Kalman filter for dynamic hedge ratio estimation
- Use Engle-Granger/Johansen cointegration test as real-time filter (only trade pairs with t_stat < -3.0)
- Consider intraday data (hourly) for faster mean reversion
- Alternative: switch to statistical arbitrage across sectors (many pairs, small allocation each)

---

## Strategy 2: ESGF-RL-DQN-Trading (29687000)

### Current State
- **Sharpe**: -0.341 | **CAGR**: N/A | **Net Profit**: negative
- **Method**: Linear Q-learning (numpy-only, no neural network despite the name)
- **State**: 8-dim (ROC 1/5/20, std_20, position, trend, RSI_norm, BB_position, bias)
- **Actions**: HOLD/BUY/SELL with confidence threshold 0.3

### Root Cause: Function Approximation Too Simple + Undertrained

Three compounding problems:

1. **Linear Q-function**: A linear model with 8 features + bias cannot capture the non-linear interactions between momentum, volatility, and regime. The Q(s,a) = w^T * phi(s,a) formulation assumes additive contributions of each state dimension. In reality, "high RSI + uptrend" and "high RSI + downtrend" should produce very different Q-values, but a linear model gives the same RSI coefficient regardless of trend.

2. **Undertrained**: Replay buffer of 3000, batch size 32, but the algorithm starts trading from day 1 with no pre-training period. The Q-function is essentially random for the first ~100 episodes (3000/32 batches). By the time it starts learning meaningful patterns, it has accumulated significant losses.

3. **Confidence threshold insufficient**: The 0.3 threshold was added to reduce trade frequency, but a linear model's "confidence" is just the magnitude of w^T * phi — which can be large simply because the features have large magnitudes, not because the model is confident.

### Recommended Fix
- Replace linear Q with a proper DQN (2-layer MLP, 64-128 hidden units)
- Pre-fill replay buffer with 10000 random steps before training begins
- Use target network soft update (tau=0.005) instead of hard update
- Add reward shaping: penalize drawdown, reward Sharpe-like risk-adjusted returns
- Alternative: switch to PPO or A2C for more stable policy gradient training

---

## Strategy 3: TrendFilteredMeanReversion (28817422)

### Current State
- **Sharpe**: -0.129 | **CAGR**: 3.4% | **MaxDD**: 17.5%
- **Method**: RSI(2) < 10 in bull regime (SPY > SMA200), exit on close > SMA5 or RSI(2) > 70 or 5-day stop
- **Universe**: SPY only

### Root Cause: Cash Drag in Bull Market

The strategy's own code comments document this clearly: ~85% of trading days have RSI(2) > 10 for SPY during the 2015-2026 bull market. The strategy is in cash for the vast majority of the backtest period.

**Key evidence from iteration history**:
- v1.0 (single-asset SPY): Sharpe -0.016, the best variant
- v4 (multi-asset 6 ETFs): Sharpe -0.129, worse because more assets = more cash drag

The structural ceiling: RSI(2) < 10 is an extremely rare event for broad market ETFs in a sustained uptrend. The strategy works in theory (when it trades, it profits), but the signal frequency is too low to overcome the opportunity cost of not being invested.

### Recommended Fix
- **Always-invested overlay**: Stay long SPY by default, use RSI(2) signals for sizing (e.g., 1.5x long when oversold, 0.5x when overbought)
- **Widen universe**: Apply RSI(2) signals to individual sector ETFs (11 GICS sectors) where oversold events are more frequent
- **Lower RSI threshold**: RSI(2) < 20 instead of < 10 captures more signals
- **Add short side**: Short SPY when RSI(2) > 90 in bear regime (SPY < SMA200) for mean reversion in both directions

---

## Strategy 4: ETF-Pairs-Researcher (28433746)

### Current State
- **Sharpe**: -0.002 (v4 best), -0.368 (v3), -1.165 (v4 sector) | **8 backtests**, none positive
- **Pairs**: Same 3 pairs as PairsTrading (GLD/SLV, TLT/IEF, EWA/EWC)
- **Method**: OLS hedge + z-score with wider thresholds (entry 3.0, exit 0.5, stop 5.0)

### Root Cause: Same Cointegration Flaw as Strategy 1

This project confirms the dead-end nature of ETF pairs trading with OLS:

| Iteration | Approach | Sharpe | Trades | Key Change |
|-----------|----------|--------|--------|------------|
| v1 | PearsonCorrelationPairsTradingAlphaModel | Runtime Error | 0 | Framework-based, failed |
| v2 (all modules) | Alpha+Portfolio+Risk framework | -0.706 | 3409 | Too many trades, whipsaws |
| v2b | Fixed universe | 0.000 | 0 | Zero trades (threshold too tight) |
| v3 | Single-file + sector ETFs | -0.368 | 656 | Sector pairs worse than commodity |
| v4 sector | Daily, lookback=120 | -1.165 | 915 | Worst variant |
| v4 commodity | Wider thresholds (3.0) | -0.002 | 152 | Fewest trades, nearly flat |

**Key insight**: Across all iterations, no parameter combination or framework choice produced positive Sharpe. The only way to reduce losses was to trade less (wider thresholds = fewer signals = less damage), but this also eliminates any chance of profit.

### Recommended Fix
- Same as Strategy 1 — the pairs trading approach on broad ETFs is fundamentally flawed
- If pursuing: requires Kalman filter + real-time cointegration testing + intraday data
- **More practical alternative**: Abandon pairs trading on broad ETFs, focus on sector rotation or factor momentum instead

---

## Strategy 5: HandsOn-Ex19-FinBERT-Sentiment (29936073)

### Current State
- **Original (v1)**: Sharpe 0.000, zero trades, zero everything — completely non-functional
- **v2 "fix"**: Sharpe 0.584, CAGR 22%, MaxDD 43% — but this is a price-momentum proxy, NOT FinBERT

### Root Cause: Platform Limitation — transformers Unavailable in QC Cloud

The strategy attempts to load FinBERT (`ProsusAI/finbert` via HuggingFace transformers + torch) for news sentiment analysis. In QC Cloud's Python environment:

1. `transformers` library is not pre-installed
2. `torch` (PyTorch) is not available
3. The `_load_model()` method catches the ImportError and falls back to keyword-based sentiment
4. The keyword fallback produces near-zero sentiment scores (news articles don't contain enough matching words), resulting in zero trades

**The v2 "fix" is deceptive**: it replaces FinBERT with a `_price_sentiment_proxy()` that computes 10-day momentum z-score. This works (Sharpe 0.584) but completely defeats the pedagogical purpose of the HandsOn exercise (learning to use NLP models for trading signals). The exercise should demonstrate sentiment analysis, not momentum trading.

### Recommended Fix
- **Pedagogically correct**: This exercise should use a pre-computed sentiment dataset or a lighter-weight model that CAN run in QC Cloud
- **Alternative 1**: Use QC's built-in `TiingoNews` sentiment scores directly (the `TiingoNews` data already provides sentiment, no model needed)
- **Alternative 2**: Use the `Quandl` sentiment indicator or similar pre-computed sentiment data
- **Alternative 3**: Keep the keyword-based approach but with much larger dictionaries and TF-IDF weighting
- **DO NOT**: Use the price-momentum proxy — it teaches the wrong lesson

---

## Cross-Strategy Patterns

### Pattern 1: Same Flaw, Two Projects
PairsTrading (28693651) and ETF-Pairs-Researcher (28433746) implement the same strategy with different parameter tunings. Both fail identically. **Lesson**: Parameter optimization cannot fix a structurally flawed approach.

### Pattern 2: Framework Overhead
ETF-Pairs-Researcher spent 4 iterations on framework architecture (Alpha Model, Portfolio Construction, Risk Management) before the author gave up and went single-file. The framework complexity (5 files: main.py, alpha.py, portfolio.py, risk.py, universe.py) added zero value. **Lesson**: Start simple, validate the core signal before adding framework sophistication.

### Pattern 3: "Fix by Replacement"
Two strategies were "fixed" by replacing their core signal:
- FinBERT → price-momentum proxy (works but wrong lesson)
- DQN name → linear Q-learning (doesn't work, mislabeled)

**Lesson**: If the core technology doesn't work on the platform, document the limitation rather than silently replacing it.

### Pattern 4: Cash Drag as Silent Killer
TrendFilteredMeanReversion has positive expectancy per-trade but negative Sharpe because of cash drag. The strategy "works" in isolation but fails relative to a simple buy-and-hold benchmark. **Lesson**: Always compare to an always-invested baseline; partial allocation strategies must account for the opportunity cost of being in cash.

---

## Actionable Recommendations

| Priority | Action | Impact |
|----------|--------|--------|
| High | Merge PairsTrading + ETF-Pairs-Researcher into one project (same strategy, 2 repos) | Reduce clutter |
| High | Fix Ex19 to use TiingoNews built-in sentiment instead of FinBERT | Restore pedagogical value |
| Medium | Add DQN layer to ESGF-RL-DQN (replace linear with 2-layer MLP) | Test if deep RL helps |
| Medium | Refactor TrendFilteredMeanReversion to always-invested overlay | Eliminate cash drag |
| Low | Archive ETF-Pairs-Researcher v1-v4 iterations (keep v4 as reference) | Cleanup |

---

*End of analysis. No code changes produced — document only, per Cycle 10 Track 2 directive.*
