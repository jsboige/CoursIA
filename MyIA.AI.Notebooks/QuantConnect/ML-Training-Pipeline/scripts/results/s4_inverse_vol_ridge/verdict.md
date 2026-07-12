# S4 Inverse Volatility Ridge — Verdict

Date: 2026-05-16 10:14

Universe: crypto-7 (BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD)
Vol window: 20 days
Tx costs: 10bps per rebalance
Walk-forward: 5-fold expanding, OOS 2027 strict
Multi-seed: bootstrap, seeds [0, 1, 7, 42]

## Results

- **Verdict**: NO BEATS
- Ridge Sharpe: 0.1284
- Inv-Vol Sharpe: 0.1108
- Equal-Weight Sharpe: 0.1066
- Delta Ridge vs EqW: +0.021713 (SE=0.000645, t=33.682)
- Seeds positive: 4/4 (p=0.0625)
- Gate: delta > 0.10, t >= 2.0, >= 3/4 seeds positive

## Per-seed detail

| Seed | Ridge | Inv-Vol | EqW | Delta |
|------|-------|---------|-----|-------|
| 0 | 0.1292 | 0.1087 | 0.1066 | +0.0226 |
| 1 | 0.1297 | 0.1129 | 0.1066 | +0.0231 |
| 7 | 0.1272 | 0.1096 | 0.1066 | +0.0206 |
| 42 | 0.1273 | 0.1122 | 0.1066 | +0.0206 |
