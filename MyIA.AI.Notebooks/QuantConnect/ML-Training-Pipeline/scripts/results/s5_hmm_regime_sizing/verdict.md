# S5 HMM Regime Sizing — Verdict (robustness sweep)

Hypothesis: regime-conditional SIZING via HMM probability (continuous blend) beats S4's hard regime switch

Date: 2026-07-26 09:04

- **Robust verdict**: **ROBUST NO BEATS**
- Sweep: alpha (Ridge shrink toward equal-weight) in [0.0, 0.1, 0.5, 1.0]. alpha=0.0 = pure inverse-vol bull/bear (max blend amplitude); alpha=1.0 = S4 default.
- Robust = NO BEATS at EVERY alpha (excludes shrinkage-artefact, Hermes concern 1).

## Alpha-sweep summary

| alpha | Continuous | Hard | Equal | Delta vs hard | t | seeds pos | Verdict |
|-------|-----------|------|-------|--------------|---|-----------|---------|
| 0.0 | 0.3385 | 0.7393 | 0.7604 | -0.400799 | -2125.234 | 0/4 | NO BEATS |
| 0.1 | 0.4174 | 0.7393 | 0.7604 | -0.321921 | -1637.661 | 0/4 | NO BEATS |
| 0.5 | 0.6330 | 0.7393 | 0.7604 | -0.106339 | -425.973 | 0/4 | NO BEATS |
| 1.0 | 0.7394 | 0.7393 | 0.7604 | +0.000103 | 0.328 | 2/4 | NO BEATS |

## Per-seed detail (alpha=1.0, S4 default shrinkage)

| Seed | Continuous | Hard | Delta | Equal | InvVol | mean p_bear | frac bear days |
|------|-----------|------|-------|-------|--------|-------------|----------------|
| 0 | 0.7396 | 0.7396 | +0.0000 | 0.7604 | 0.4214 | 0.409 | 0.396 |
| 1 | 0.7397 | 0.7403 | -0.0005 | 0.7604 | 0.4214 | 0.305 | 0.263 |
| 7 | 0.7395 | 0.7396 | -0.0001 | 0.7604 | 0.4214 | 0.280 | 0.264 |
| 42 | 0.7389 | 0.7379 | +0.0010 | 0.7604 | 0.4214 | 0.319 | 0.341 |

## Methodology notes
- mean p_bear / frac bear days measured over the FULL OOS window (all folds), not just the last fold (Hermes concern 2).
- Rebalance cadence: **daily, by design** (n_rebalances approx n_obs). The HMM emits a fresh regime probability every bar; a sizing strategy re-derives the blend daily. Conservative for NO BEATS: more rebalancing = more turnover cost (Hermes concern 3).
- OOS: real expanding-window HMM refit on [0,t) every 22 days (neither S3 nor S4 do this — they fit on the test block itself). No future leak.
