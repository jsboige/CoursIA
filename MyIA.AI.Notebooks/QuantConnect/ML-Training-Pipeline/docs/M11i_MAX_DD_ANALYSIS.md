# M11i Max-DD Analysis — Does cap=3.0 Survive on Calmar Basis?

**Date**: 2026-05-13 (Cycle 30, Track 1)
**Purpose**: M11h found edge at kelly_cap=3.0 on Sharpe (p=0.088). This analysis checks whether the edge survives risk-adjustment via Calmar ratio (Sharpe_ann / max_DD).

## Setup

Same sweep as M11h: kelly_cap in {1.0, 2.0, 3.0} x threshold in {0.00, 0.05, 0.10} x fee_bps in {10, 50, 100} x 7 coins x 5 horizons = 945 per-combo rows.

Each row now includes: max_dd_active, max_dd_buyhold, dd_ratio, calmar_ratio.

## Max-DD Distribution by Cap (fee=50bps, thr=0.00)

| Cap | Median DD | Mean DD | Max DD |
|-----|-----------|---------|--------|
| 1.0 | 57.0% | 55.9% | 72.1% |
| 2.0 | 79.1% | 78.4% | 94.2% |
| 3.0 | 87.9% | 86.8% | 99.1% |

DD increases monotonically with cap. Cap=3.0 nearly doubles DD vs cap=1.0.

## Calmar Grid (cap x threshold x fee)

| Cap | Thr | 10bps | 50bps | 100bps |
|-----|-----|-------|-------|--------|
| 1.0 | 0.00 | +0.79 (dd=52.8%) | +0.63 (dd=57.0%) | +0.44 (dd=62.5%) |
| 1.0 | 0.05 | +0.79 (dd=52.7%) | +0.63 (dd=56.7%) | +0.44 (dd=62.5%) |
| 1.0 | 0.10 | +0.79 (dd=52.2%) | +0.63 (dd=56.6%) | +0.45 (dd=62.1%) |
| 2.0 | 0.00 | +0.47 (dd=76.1%) | +0.33 (dd=79.1%) | +0.19 (dd=82.2%) |
| 2.0 | 0.05 | +0.47 (dd=76.1%) | +0.33 (dd=79.0%) | +0.19 (dd=82.2%) |
| 2.0 | 0.10 | +0.48 (dd=75.9%) | +0.33 (dd=79.0%) | +0.19 (dd=82.2%) |
| 3.0 | 0.00 | +0.36 (dd=85.6%) | +0.29 (dd=87.9%) | +0.19 (dd=90.5%) |
| 3.0 | 0.05 | +0.36 (dd=85.7%) | +0.29 (dd=87.9%) | +0.19 (dd=90.5%) |
| 3.0 | 0.10 | +0.35 (dd=85.7%) | +0.28 (dd=88.0%) | +0.19 (dd=90.4%) |

Key observation: Calmar drops monotonically with cap at every fee level. Threshold has minimal effect.

## Core Verdict: Calmar cap=3.0 vs cap=1.0

| Fee | Thr | Calmar cap3>cap1 | p-value | DD cap3>cap1 | p-value | Med Calmar 1.0→3.0 | Med DD 1.0→3.0 |
|-----|-----|------------------|---------|--------------|---------|---------------------|-----------------|
| 50bps | 0.00 | 15/35 (42.9%) | 0.845 | 35/35 (100%) | 0.000 | +0.63 → +0.29 | 0.570 → 0.879 |
| 50bps | 0.05 | 15/35 (42.9%) | 0.845 | 35/35 (100%) | 0.000 | +0.63 → +0.29 | 0.567 → 0.879 |
| 50bps | 0.10 | 14/35 (40.0%) | 0.912 | 35/35 (100%) | 0.000 | +0.63 → +0.28 | 0.566 → 0.880 |
| 100bps | 0.00 | 17/35 (48.6%) | 0.632 | 35/35 (100%) | 0.000 | +0.44 → +0.19 | 0.625 → 0.905 |
| 100bps | 0.05 | 17/35 (48.6%) | 0.632 | 35/35 (100%) | 0.000 | +0.44 → +0.19 | 0.625 → 0.905 |
| 100bps | 0.10 | 17/35 (48.6%) | 0.632 | 35/35 (100%) | 0.000 | +0.45 → +0.19 | 0.621 → 0.904 |

## Verdict: NULL CONDITIONAL

**cap=3.0 edge on Sharpe does NOT survive Calmar risk-adjustment at any fee level.**

- Calmar cap3>cap1: at most 48.6% (below 50%), p-values 0.632-0.912 (nowhere near significance)
- DD penalty: 35/35 combos at every threshold, p=0.000. DD increases ~1.5x going from cap=1.0 to cap=3.0
- Median Calmar drops from +0.63 to +0.29 at 50bps, +0.44 to +0.19 at 100bps

The M11h finding (Sharpe edge at cap=3.0, p=0.088) was a **leverage artifact**: higher leverage amplifies both returns and drawdowns, and the DD amplification dominates the Calmar ratio.

## Implication for M_NEXT_VOL

Stick with cap=1.0 (full Kelly, no leverage). The Sharpe-optimal cap=3.0 finding was real but not risk-adjusted viable. Calmar-optimal = cap=1.0 at lowest available fee.

## Files

- `scripts/m11i_max_dd_analysis.py`: Analysis script
- `results/m11i_max_dd/results.json`: 945-row per-combo results
- `results/m11i_max_dd/m11i_max_dd_grid.csv`: Summary grid
