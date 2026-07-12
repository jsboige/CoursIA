# L5 Vol-Targeted Trend Composite — Verdict

**Date**: 2026-06-12 13:13  
**Verdict**: **NO BEATS**  
**Gate**: delta >= +0.1 vs S4v2, t >= 2.0, >= 3/4 seeds positive

- Mean delta Sharpe vs S4 v2: **-0.2362** (t = -2.490)
- Seeds positive: 1/4
- Deflated Sharpe probability (N=10 trials): 0.0739
- Stress 50bps mean delta: -0.1904
- Mean Sharpe — L5: 0.6129 | S4v2: 0.8491 | no-VT: 0.5891 | VT-only: 0.8238 | EqW: 0.8317
- Realised L5 vol (ann): 0.1035 (target 0.1)

Per-seed:

| seed | L5 | S4v2 | delta | stress delta | vt scale | skip rate |
|------|-----|------|-------|--------------|----------|-----------|
| 0 | 0.6645 | 1.0021 | -0.3376 | -0.2649 | 0.813 | 37.4% |
| 1 | 1.4623 | 1.7288 | -0.2666 | -0.0944 | 0.845 | 37.4% |
| 7 | 0.2460 | 0.2064 | +0.0395 | +0.0884 | 0.826 | 38.5% |
| 42 | 0.0789 | 0.4589 | -0.3800 | -0.4904 | 0.777 | 35.8% |
