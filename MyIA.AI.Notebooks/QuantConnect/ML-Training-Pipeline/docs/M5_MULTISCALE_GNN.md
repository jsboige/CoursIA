# M5 stretch — Multi-scale GNN cross-asset on log-RV (Issue #834)

**Status:** scaffold 2026-05-08, side-track ai-01 RTX 4090 (training pending).

## Why M5 (vs existing train_gnn.py / train_mtgnn.py)

The repo already has `graph_builder.py` (CryptoGraphBuilder, 10-coin panier),
`train_gnn.py` (GCN/GAT/RGCN), `train_mtgnn.py` (Wu et al. KDD 2020). These all
target **next-step direction of average panier return** — a ~50% binary noise
target on crypto (Stage 0/1/2 confirmed: 0 BEATS in 20 combinations).

M5 attacks a **different target** where HAR / GARCH actually win measurably
(M2 #837 results: HAR beats GARCH 30-65% MSE log-RV). The hypothesis:

> Multi-asset graph spillover + multi-scale HAR-style temporal aggregation
> can beat single-asset HAR on `log RV_{t+1..t+h}` because volatility
> co-moves cross-asset (well-documented spillover, e.g. Diebold-Yilmaz 2012).

If M5 doesn't beat HAR by ≥2σ cross-seed, the conclusion is honest: **HAR
single-asset is hard to beat on log-RV at h=1/5/10 even with cross-asset
graph and multi-scale aggregation**. That's a useful negative result too.

## Architecture

```
Inputs per timestep t:
  X_t : (N=3 coins, F=4 features)
        F = [log_rv_t, rv_d_t (=log_rv_{t-1}), rv_w_t (=mean log_rv last 5d),
             rv_m_t (=mean log_rv last 22d)]
  A_t : (N, N) dynamic adjacency (rolling 60d returns correlation, top-K=2)

Path daily   (1d window) ── GAT(F → hidden=32, heads=4) ── h_d : (N, hidden)
Path weekly  (5d window) ── GAT(F → hidden=32, heads=4) ── h_w : (N, hidden)
Path monthly (22d window)── GAT(F → hidden=32, heads=4) ── h_m : (N, hidden)

Fusion: concat [h_d, h_w, h_m] → MLP(3*hidden → hidden → 1) → ŷ_t : (N,)
Target: log RV_{t+1..t+h} averaged over h days, per coin.
Loss:   MSE log-RV per coin, summed over batch.
```

Note: the "multi-scale" is **temporal** (3 HAR-style paths), not "graph
multi-resolution" (which would be hierarchical pooling — overkill for N=3
nodes).

## Data

Reuses M2 pipeline (`intraday_loader.py` + `realized_variance.py`):
- BTC: Bitstamp hourly, 2278 RV days
- ETH: Binance hourly, 1495 RV days
- SOL: yfinance hourly, 725 RV days

Common-date intersection: ~720 days (SOL is the bottleneck — limits training
sample severely. M3 with pooled multi-asset has same constraint).

For training: ~720 days × 3 coins = 2160 (coin, day) observations. Walk-forward
5-fold ⇒ ~430 train / 110 test per fold. Tight but workable.

## Baselines

- **HAR** (M2 #837) — gold standard per-coin
- **GARCH(1,1) rolling** (M1 #838) — leak-free reference
- **Naive trail-30d** (M2) — sanity floor

## Evaluation

Walk-forward 5-fold:
- Expanding window training
- Refit-every = 22 days
- Multi-seed: 0, 1, 7, 42 (4 seeds, cf [feedback_multi_seed_required.md])
- Edge ≥ 2σ cross-seed required for any "BEATS HAR" claim
- Diebold-Mariano HAC test (Newey-West lag = h-1) for significance

Verdict matrix (coin × horizon × seed × baseline):

| Coin | Horizon | M5 MSE | HAR MSE | edge | DM stat | Verdict |
|------|---------|--------|---------|------|---------|---------|

(filled at training time, multi-seed mean ± std)

## Honest caveats

1. **N=3 is tiny for GNN.** Graph spillover gains saturate. Extending to
   panier 10 coins (using `graph_builder.CRYPTO_PANIER_SYMBOLS`) is
   straightforward but limited by daily OHLCV availability for some.

2. **Hourly RV is noisier than 5-min RV** (cf M2 caveats). 5-min crypto
   ingestion would unlock another 10-30% MSE reduction baseline-side.

3. **No exogenous features** (sentiment, on-chain, macro). Pure
   self-referential cross-asset RV. The literature shows external regimes
   matter — out of scope for this stretch.

4. **GAT 2-layers is conservative.** Deeper GNNs over-smooth on small graphs;
   adding skip connections (ResGCN-style) is a stretch upgrade.

5. **Stretch = no merge expectation.** This is exploratory. If M5 does not
   beat HAR by ≥2σ, the PR will be marked NO BEATS and merged as scaffold
   for future work, not as a recommended pipeline component.

## How to reproduce (when training lands)

```powershell
& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe" `
  MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\scripts\train_multiscale_gnn.py `
  --horizons 1 5 10 `
  --seeds 0 1 7 42 `
  --out-json MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\results\m5_multiscale_gnn\results.json
```

Tests:

```powershell
& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe" `
  -m pytest MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\scripts\tests\test_multiscale_gnn_features.py `
            MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\scripts\tests\test_multiscale_gnn_model.py -q
```

## References

- Corsi (2009) HAR.
- Veličković et al. (2018) "Graph Attention Networks", *ICLR*.
- Wu et al. (2020) "Connecting the Dots: Multivariate Time Series Forecasting
  with GNN", *KDD*.
- Diebold & Yılmaz (2012) "Better to give than to receive: Predictive
  directional measurement of volatility spillovers", *International Journal
  of Forecasting* 28, 57-66.
- Springer Financial Innovation 2025: multi-scale GNN crypto vol
  ([10.1186/s40854-025-00768-x](https://link.springer.com/article/10.1186/s40854-025-00768-x)).
- M2 baseline doc: [`M2_HAR_BASELINE.md`](M2_HAR_BASELINE.md)
- M1 GARCH no-leak: PR #838
