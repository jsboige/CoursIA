# QC Comparative Backtests — Baseline Aligned

**Source**: Issue #1630 — Baseline backtest + tableau comparatif
**Updated**: 2026-06-04
**Method**: API QC Cloud via `qc-mcp-lite`, backtests existants relus

## Methodology

### Periode commune

| Asset class | Periode baseline | Rationale |
|-------------|-----------------|-----------|
| US Equities | 2018-01-01 to 2025-12-31 | 7 ans, inclut COVID crash + recovery, post-2022 bear |
| Crypto | 2020-01-01 to 2025-12-31 | 5 ans, post-2017 bubble, inclut 2021 bull + 2022 bear |
| Multi-asset | 2020-01-01 to 2025-12-31 | Conserve crypto alignment |

### Limitations

- **Dates codees dans main.py**: les periodes de backtest sont specifiees dans chaque algorithme, pas parametrables via API. Les baselines #1630 ont ete creees en modifiant les dates dans chaque projet avant compilation.
- **Quelques strategies n'ont pas de baseline #1630**: ForexCarry, BTC-ML, RL-Q-Learning. Leurs resultats ci-dessous sont les backtests "latest" (periode non-alignee, marquees *).
- **totalOrders = 0** pour certaines baselines: possible bug de reporting QC Cloud ou strategie sans trades sur la periode.

## Results — Aligned Baseline (2018-2025 / 2020-2025)

### Research Tier Strategies

| # | Strategy | QC ID | Sharpe | CAGR | MaxDD | Asset | Category | Period |
|---|----------|-------|--------|------|-------|-------|----------|--------|
| 1 | TrendFollowing | 28797562 | **1.072** | 23.2% | 9.3% | Equities | Trend | 2018-2025 |
| 2 | VolTarget-Momentum | 30784745 | **0.648** | 14.7% | 21.2% | Equities | Momentum | 2018-2025 |
| 3 | Crypto-MultiCanal | 30750734 | **0.581** | 8.2% | 17.0% | Crypto | MultiSignal | 2020-2025 |
| 4 | Portfolio-IBKR-Binance | 31717642 | **0.519** | 15.7% | 16.9% | MultiAsset | Portfolio | 2020-2025 |
| 5 | TrendStocks-Alpha | 28885507 | **0.519** | 15.9% | 39.6% | Equities | Trend | 2018-2025 |
| 6 | MomentumRegime | 31243821 | 0.185 | 4.7% | 11.5% | Equities | Composite | 2018-2025 |
| 7 | EMA-Cross-Alpha | 28885488 | -0.010 | 2.8% | 14.0% | Equities | Momentum | 2018-2025 |

### Non-aligned (latest backtest, periode variable)*

| # | Strategy | QC ID | Sharpe | CAGR | MaxDD | Asset | Category | Notes |
|---|----------|-------|--------|------|-------|-------|----------|-------|
| 8 | RL-Q-Learning | 32057969 | 0.584 | 18.2% | 33.2% | Equities | RL | *non-aligned |
| 9 | BTC-ML | 29318876 | 0.106 | 5.8% | 16.2% | Crypto | ML | *non-aligned |
| 10 | ForexCarry | 28657908 | -1.107 | -0.5% | 19.2% | FX | Carry | *non-aligned |

## Key Findings

### 1. TrendFollowing est le leader indiscutable

Sharpe 1.072 sur 2018-2025 avec un MaxDD de seulement 9.3%. C'est la seule strategie "Robuste" (Sharpe > 0.5) qui maintient ses performances sur la periode aligned.

### 2. EMA-Cross-Alpha: chute dramatique

Sharpe passe de **0.996** (meilleur backtest) a **-0.010** sur la periode aligned 2018-2025. Cela confirme le pattern "backtests courts = overfitting" documente dans `docs/quantconnect.md`. La strategie depend fortement de la periode choisie.

### 3. Les composites ne bat pas les single-strategies

MomentumRegime (SectorMomentum + RegimeSwitching) obtient seulement 0.185 sur la periode aligned, confirmant le probleme de "double-defense" documente dans les lecons QC.

### 4. Crypto strategies: rendement modere mais stable

Crypto-MultiCanal (0.581) et Portfolio-IBKR-Binance (0.519) offrent une diversification interessante avec des MaxDD maitrises (17% et 16.9%).

### 5. FX Carry = perdant

Sharpe -1.107, la strategie Carry forex ne fonctionne pas sur la periode recente. Les taux d'interet bas post-COVID ont elimine l'avantage du carry trade.

## Comparison: Best-vs-Aligned

| Strategy | Best Sharpe | Aligned Sharpe | Delta | Diagnostic |
|----------|------------|----------------|-------|------------|
| EMA-Cross-Alpha | 0.996 | -0.010 | **-1.006** | Period overfitting severe |
| TrendStocks-Alpha | 0.609 | 0.519 | -0.090 | Stable, legere degradation |
| TrendFollowing | ~0.8 | 1.072 | +0.272 | Improve sur longue periode |
| Crypto-MultiCanal | ~0.6 | 0.581 | ~0 | Performance confirmee |
| VolTarget-Momentum | ~0.65 | 0.648 | ~0 | Performance confirmee |

## Backtest IDs (for verification)

| Strategy | Backtest ID | Name |
|----------|-------------|------|
| TrendFollowing | 7792ae0af2ec151207ed89ec46e0b0fd | Baseline 2018-2025 #1630 |
| EMA-Cross-Alpha | 633779d099d59344b30e85cf9bbb883c | Baseline 2018-2025 #1630 |
| TrendStocks-Alpha | 7c434dbd12ff69e514910bcf58bfa406 | Baseline 2018-2025 #1630 |
| Crypto-MultiCanal | 4e97d7dc1552ecaefab4730f24e0a5b1 | Baseline 2020-2025 #1630 |
| VolTarget-Momentum | c3223fe5f8e5d37f8bcb3730da953e5f | Baseline 2018-2025 #1630 |
| MomentumRegime | 033834d8b9092971ef8f04cf9da7e5a3 | Baseline 2018-2025 #1630 |
| Portfolio-IBKR-Binance | 4cbb9476afe2345d9a1c99ed5fa419da | Baseline 2020-2025 #1630 |

## Next Steps

1. **Run baselines for 3 missing strategies** (ForexCarry, BTC-ML, RL-Q-Learning) on aligned periods
2. **Add ESGF teaching strategies** (10 student projects) if pedagogically relevant
3. **Cross-reference with `projects/README.md`** to update the main performance table
4. **Walk-forward validation** for top 3 strategies (TrendFollowing, VolTarget, Crypto-MultiCanal)

## References

- [Strategies Catalog](qc_strategies_catalog.md) — Full 96-project catalog
- [QC Patterns](../../docs/quantconnect.md) — 20 confirmed patterns + anti-patterns
- [projects/README.md](../projects/README.md) — Main strategy listing
