# S7 Composite — Verdict

Date: 2026-07-26 05:06

Universe: SPY, TLT, XLF, XLK, XLE, XLV, XLY, XLI, XLB, XLU, XLP
Architecture: RegimeDetector(HMM) -> VolConditioner(HAR-RV-J) -> RiskWeights(Ridge vol-tuned) -> ExecutionGate -> PortfolioOrders
Tx costs: 10bps per rebalance, 50bps stress
Walk-forward: 5-fold expanding, OOS 2027 strict
Multi-seed: block bootstrap (22-day), seeds [0, 1, 7, 42]

## Results

- **Verdict**: NO BEATS
- Composite Sharpe: 0.8179
- S4 v2 Sharpe: 0.8179
- EqW Sharpe: 0.8335
- Delta vs S4 v2: -0.000040 (SE=0.040140, t=-0.001)
- Delta vs EqW: -0.0156
- Seeds positive: 1/4 (p=0.9375)
- Stress delta (50bps): +0.729289
- Gate: delta >= 0.1, t >= 2.0, >= 3/4 seeds positive

## Per-seed summary

| Seed | Composite | S4 v2 | Delta vs S4v2 | EqW | Delta vs EqW | Skips | Skip% |
|------|-----------|-------|---------------|-----|-------------|-------|-------|
| 0 | 0.8902 | 0.9035 | -0.0133 | 0.9848 | -0.0945 | 1795 | 89.8% |
| 1 | 1.8457 | 1.7302 | +0.1156 | 1.6644 | +0.1813 | 1797 | 89.8% |
| 7 | 0.1659 | 0.2006 | -0.0346 | 0.2664 | -0.1004 | 1802 | 90.1% |
| 42 | 0.3696 | 0.4375 | -0.0679 | 0.4184 | -0.0488 | 1741 | 87.1% |