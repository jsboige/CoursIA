# Framework_Composite_EMATrend

**Classe d'actifs :** Actions US (Mag7 + méga-capitalisations)
**Cloud project ID :** 28911253

## Description

Composite framework combinant EMA-Cross-Alpha (5 actions tech/Mag7, rééquilibrage
quotidien) avec TrendStocks-Alpha (15 méga-capitalisations diversifiées, rééquilibrage
hebdomadaire) via le QC Algorithm Framework. Allocation cible : EMA70/Trend30
(configuration gagnante du sweep).

Chevauchement d'univers : les 5 actions Mag7 (AAPL, MSFT, GOOGL, AMZN, NVDA) sont
présentes dans les deux stratégies ; le MultiStrategyPCM combine additivement les poids,
donnant une allocation plus élevée aux Mag7 quand les deux stratégies concordent sur la
direction.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_EMATrend"`
**QC Cloud :** Déployé comme projet 28911253 (IBKR margin, backtest direct).

## Métriques de backtest

| Métrique | Catalogue 2015-2025 | Alignée 2018-2025 |
|----------|---------------------|-------------------|
| Sharpe Ratio | 0.741 | **0.611** |
| CAGR | — | 16.670 % |
| Max Drawdown | 28.0 % | 27.9 % |
| PSR | 27.4 % | 19.8 % |

Backtest catalogue (décennie complète 2015-2025, EMA70/Trend30) = Sharpe 0.741
(la docstring annonçait 0.867 → réel 0.741, −14 %). Voir `docs/qc/qc-comparative-backtests.md`.

## Baseline alignée (2018-2025)

Vérifiée sur la fenêtre alignée cohorte (2018-01-01 → 2025-01-01, 1761 dates
tradables), même configuration gagnante EMA70/Trend30 :

- **Sharpe 0.611** (backtest `3095a263d5bd30df181ec002c0a52b72`, projet 28911253)
- CAGR 16.670 %, MaxDD 27.9 %, PSR 19.8 %

**Verdict : survit à l'alignement avec une baisse modérée** (0.741 → 0.611, −18 %) — pas
un effondrement de sur-ajustement de période. Il perd une partie du pré-ramp Mag7 2015-2017
et absorbe le drawdown Mag7 de 2022, mais le signal tendance tient. Sur la fenêtre alignée,
c'est le **backbone COMP (composite-framework) au Sharpe le plus élevé vérifié à ce jour**
(devance composite-c2-equityfactor 0.574, FamaFrenchAllWeather 0.338,
composite-c1-multiasset 0.258). Promu Tier 4 (Untested) → Tier 2 (Historique).

**Caveat de survivance Mag7 :** le sleeve EMA est 100 % Mag7, le Sharpe est donc en partie
un artefact de la surperformance Mag7 sur la décennie backtestée. Le Sharpe le plus élevé
ne se confond pas avec la constitution la plus robuste : composite-c2-equityfactor
(0.574, diversifié factoriellement sur 25 actions) est le leader COMP le plus défendable
constitution-par-constitution, tandis qu'EMATrend est celui au Sharpe le plus élevé mais
concentré Mag7. Voir Key-finding #36 dans `docs/qc/qc-comparative-backtests.md`.

## Fichiers

- `main.py` — Stratégie (composite EMA70/Trend30, alignée 2018-2025)
- `alpha_models.py` — EMACrossAlpha + TrendStocksAlpha
- `portfolio_construction.py` — MultiStrategyPCM (blend d'allocation alpha)
