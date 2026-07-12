# S7 Composite — Verdict

Date: 2026-05-16 19:53

Universe: SPY, TLT, XLF, XLK, XLE, XLV, XLY, XLI, XLB, XLU, XLP
Architecture: RegimeDetector(HMM) -> VolConditioner(HAR-RV-J) -> RiskWeights(Ridge vol-tuned) -> ExecutionGate -> PortfolioOrders
Tx costs: 10bps per rebalance, 50bps stress
Walk-forward: 5-fold expanding, OOS 2027 strict
Multi-seed: block bootstrap (22-day), seeds [0, 1, 7, 42]

## Results

- **Verdict**: NO BEATS
- Composite Sharpe: 1.0473
- S4 v2 Sharpe: 1.0537
- EqW Sharpe: 0.8583
- Delta vs S4 v2: -0.006357 (SE=0.019751, t=-0.322)
- Delta vs EqW: +0.1890
- Seeds positive: 1/4 (p=0.9375)
- Stress delta (50bps): -0.006357
- Gate: delta >= 0.1, t >= 2.0, >= 3/4 seeds positive

## Per-seed summary

| Seed | Composite | S4 v2 | Delta vs S4v2 | EqW | Delta vs EqW | Skips | Skip% |
|------|-----------|-------|---------------|-----|-------------|-------|-------|
| 0 | 1.1021 | 1.1326 | -0.0305 | 0.9932 | +0.1089 | 0 | 0.0% |
| 1 | 2.1048 | 2.0565 | +0.0483 | 1.7505 | +0.3542 | 0 | 0.0% |
| 7 | 0.3271 | 0.3667 | -0.0396 | 0.2551 | +0.0721 | 0 | 0.0% |
| 42 | 0.6553 | 0.6589 | -0.0036 | 0.4345 | +0.2208 | 0 | 0.0% |