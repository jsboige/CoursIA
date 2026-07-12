# HAR-RV-J-Kelly

**Classe d'actifs :** Crypto (BTCUSDT, ETHUSDT, LTCUSDT, BCHUSDT sur Binance)

**ID projet Cloud :** 31650567

## Description

HAR-RV-J (Heterogeneous Autoregressive Realized Variance with Jumps — variance réalisée autorégressive hétérogène avec sauts, Corsi 2009 + Andersen, Bollerslev & Diebold 2007) pour la prévision de la variance réalisée à 5 jours sur des actifs crypto. Étend le HAR Classic avec une composante de sauts dérivée de la variation bipuissance (bipower variation) de Huang-Tauchen. Fraction de Kelly 1/4 pour le dimensionnement des positions.

Mettre le paramètre `use_jumps=1` pour le HAR-RV-J (6 features) ou `use_jumps=0` pour le HAR Classic (3 features).

## Comment exécuter

### QC Cloud

Ouvrir le projet cloud 31650567, compiler et lancer un backtest.

## Métriques de backtest

Vérifiées sur QC Cloud (projet 31650567, Binance USDT DAILY) :

| Variante | Période | Sharpe | CAGR | Max DD | PSR |
|----------|---------|--------|------|--------|-----|
| HAR-RV-J Kelly (use_jumps=1, aligné) | 2018-01-01 → 2025-06-01 | **0.524** | 14.08 % | 37.10 % | 10.7 % |
| HAR-RV-J Kelly v2 (use_jumps=1) | 2020-01-01 → 2025-06-01 | 0.746 | 23.03 % | 48.30 % | 24.0 % |
| HAR Classic Baseline (use_jumps=0) | 2020-01-01 → 2025-06-01 | 0.642 | 27.0 % | 41.1 % | 15.8 % |

La ligne alignée 2018-2025 (backtest `df687834`, 2026-06-22) étend la fenêtre vers l'arrière : avec `train_window=500`, le modèle accumule sur ~2018-2019 avant de pouvoir prévoir, donc la période plus longue ajoute des données hors-échantillon du régime initial et abaisse le Sharpe (0.746 → 0.524) et le CAGR (23.0 % → 14.1 %) par rapport à la fenêtre 2020-2025, tout en *améliorant* le MaxDD (48.3 % → 37.1 %) — le chemin de coefficients différent à travers le bear crypto 2022 produit une exposition moins levée. PSR 10.7 % (non significatif). Promu Tier 4 (Untested) → Tier 2 (Historique) sur la fenêtre alignée ; le meilleur backbone baseline depuis GlobalMacro-Regime (0.454). See #1630.

La ligne HAR-RV-J v2 est vérifiée sous la configuration Binance USDT DAILY actuelle (2026-06-12, backtest `verify-har-rv-j-real-metrics`). La baseline HAR Classic conserve sa mesure du 2026-05-14 (configuration pré-Binance) ; un run récent `use_jumps=0` sous la configuration actuelle est en attente pour un delta apples-to-apples.

> **Note :** la colonne du nombre de trades a été retirée car la méthode MCP `read_backtest` ne parse pas le champ `totalOrders` (rapporte toujours 0). La stratégie trade activement — un CAGR de 23 % et un drawdown de 48 % ne peuvent pas provenir d'un book tout-cash. Le nombre réel d'ordres se lit sur l'interface web QC Cloud (treegrid *Backtests Results*, colonne « Orders »). Voir le README Multi-Layer-EMA pour le diagnostic complet de ce fantôme MCP (résolu dans le cadre de #2801 Lot 2).

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Prévision de volatilité HAR-RV-J avec dimensionnement par critère de Kelly sur 4 actifs crypto |

## Références

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Andersen, T.G., Bollerslev, T., & Diebold, F.X. (2007). *Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility*. Review of Economics and Statistics.
