# L5 — Vol-Targeted Trend Composite (ladder #1409, rung 5)

## Verdict: NO BEATS

Adding a 12-1 TSMOM trend filter and a 10% annualised vol-targeting overlay on top
of the S7 composite (S3 HMM regime + HAR-RV-J vol conditioning + S4 v2 Ridge
allocation + execution gate) **does not beat S4 v2 alone**.

- Mean delta Sharpe vs S4 v2: **-0.2362** (t = -2.49, significantly negative)
- Seeds positive: 1/4 (gate requires >= 3/4)
- Deflated Sharpe probability (N=10 trials): 0.074
- Stress 50bps mean delta: -0.190

## Method

- **Architecture**: RegimeDetector (S3 HMM bull/bear) -> VolConditioner (HAR-RV-J)
  -> RiskWeights (S4 v2 regime-conditional Ridge, vol-tuned alpha) -> TrendFilter
  (12-1 TSMOM, zero-out negative-momentum legs) -> VolTargeting (10% annualised
  ex-ante, 63-day covariance, leverage cap 1.0) -> ExecutionGate (skip if proposed
  turnover > 1.5x trailing average of proposed turnover)
- **Validation**: walk-forward 5-fold expanding, block bootstrap 22d, seeds [0, 1, 7, 42]
- **Costs**: 10bps per unit turnover, 50bps stress (same weight path, costs
  recomputed from recorded per-day turnover)
- **Universe**: anti-FAANG — SPY, TLT, 9 sector ETFs (XLF/XLK/XLE/XLV/XLY/XLI/XLB/XLU/XLP)
- **Baselines**: S4 v2 alone (primary gate), equal-weight (secondary)
- **Gate**: delta >= +0.10 vs S4 v2, t >= 2.0, >= 3/4 seeds positive, deflated Sharpe

## Results (4 seeds, tx 10bps)

| Arm | Mean Sharpe | vs S4 v2 |
|-----|-------------|----------|
| S4 v2 alone (baseline) | 0.849 | — |
| Equal-weight | 0.832 | -0.017 |
| **VT-only** (composite + vol-targeting, no trend) | 0.824 | -0.025 |
| **L5 full** (trend + VT + gate) | 0.613 | **-0.236** |
| no-VT (trend + gate, no vol-targeting) | 0.589 | -0.260 |

Per-seed (L5 full vs S4 v2): 0 -> -0.338 | 1 -> -0.267 | 7 -> +0.040 | 42 -> -0.380.

## Key Findings

1. **The trend filter is the killer, not the vol-targeting.** Ablation: removing
   only the trend filter (VT-only arm) recovers almost all the gap (-0.025 vs
   -0.236). The 12-1 TSMOM filter zeroes out legs that subsequently rebound —
   consistent with L1 (TSMOM NO BEATS), L2 (CS momentum NO BEATS) and L3 (trend
   long-horizon NO BEATS): trend signals do not work on this universe/period.

2. **Vol-targeting delivers its risk objective at ~zero Sharpe cost.** Realised
   L5 vol = 10.3% annualised (target 10%, vs 16.6% for S4 v2); max drawdown
   reduced (-0.281 vs -0.347 on seed 0); mean scale 0.81 with ~62% of days
   de-scaled. Sharpe impact of the overlay alone: -0.025 (noise). Vol-targeting
   is a legitimate risk-management overlay, just not an alpha source here.

3. **The execution gate halves turnover** (0.063 vs 0.111 mean daily turnover)
   with a 37% skip rate, which is why the L5 deficit *shrinks* under 50bps
   stress (-0.190 vs -0.236): cost-aware gating helps relatively when costs
   rise, but cannot rescue a negative signal.

4. **S7 had a turnover-accounting bug that invalidated its cost model.** In
   `s7_composite.py` the turnover was computed *after* assigning the new weights
   to current (`estimate_trade_cost(current, new)` with `current` already equal
   to `new`), so recorded turnover was always 0: the execution gate never fired
   (skip_rate 0.0% on every seed in `results/s7_composite/results.json`) and tx
   costs were effectively zero for both arms. L5 fixes this (turnover computed
   before assignment, real costs on both arms) and additionally excludes ^VIX
   from the tradable weight vector (s7 let Ridge allocate weight to ^VIX, then
   silently dropped it at return time). The s7 NO BEATS verdict direction is
   unchanged by the fix, but its cost/gate metrics were not meaningful.

5. **Gate-history design matters.** A first L5 implementation appended the
   *executed* turnover (0 on skipped days) to the gating history, dragging the
   trailing average toward 0 and locking the gate shut in a feedback loop (87%
   skip, frozen portfolio). The gate must compare proposed turnover against the
   trailing average of *proposed* turnover (37% skip, healthy).

## Implication for Ladder (#1409)

L5 closes the composite branch of the ladder: with L1, L2, L3, L5 all NO BEATS
and L4 (Decision Transformer, action-based) the only BEATS, the evidence says
**alpha on this universe comes from learned action policies, not from trend
overlays or vol conditioning on top of risk-based allocation**. Vol-targeting
remains worth keeping as a *risk* overlay (finding 2) for any production
candidate built on L4 or S4 v2.

## Data

- 11 symbols + ^VIX, 2373 rows, 2017-01-03 to 2026-06-11 (yfinance daily close)
- OOS observations: 1975 per seed, 5 folds
- Runtime: 153s for 4 seeds (CPU)

## Script

`scripts/L5_vol_targeted_composite.py` — outputs to
`scripts/results/l5_vol_targeted/{results.json, verdict.md}`. Reuses the S3/S4/HAR
building blocks imported from `scripts/s7_composite.py`.
