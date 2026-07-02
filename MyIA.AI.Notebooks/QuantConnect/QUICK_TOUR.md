# QuantConnect AI Trading - Quick Tour

**95+ strategies backtested | 51 notebooks Python | 20 patterns confirmes | Composite robuste (TrendWeather Sharpe aligné 0.95)**

Cette section contient un parcours complet de trading algorithmique sur **QuantConnect LEAN**, du debutant au deploiement live. Tout est executable gratuitement sur le cloud QC.

> **Lecture vérifiée sous frais réels (#1630, 2018-2025).** Les Sharpes « catalogue » ci-dessous sont **pré-frais, fenêtres variables** ; elles ne résistent pas toutes à un backtest honnête sous frais IBKR réels sur une fenêtre alignée 2018-2025. Cas emblématique : **EMA-Cross-Alpha** passe de Sharpe catalogue **0.996 à -0.010 aligné** (PSR 0.5%) = overfitting sévère d'un backtest court, **pas** un top performer. Les vrais leaders vérifiés alignés : **LongShortHarvest 1.64** (PSR 98.7%, le plus robuste), **TrendWeather 0.948** (composite qui tient, PSR 56.6%), **EMATrend 0.611** / **composite-c2 0.574** (backbone no-ML). Catalogue complet + diagnostics par stratégie : [docs/qc/qc-comparative-backtests.md](../../docs/qc/qc-comparative-backtests.md) (See #1630).

## 5 arrets pour comprendre notre travail

1. **[Meilleure strategie](projects/Framework_Composite_TrendWeather/)** — Composite TrendStocks + AllWeather (Sharpe 1.156, CAGR 27.4%). Architecture Algorithm Framework modulaire : AlphaModel + PortfolioConstruction + Execution.

2. **[Catalogue strategies](docs/qc_strategies_catalog.md)** — 95+ projets organises par categorie (Alpha, Trend Following, ML/RL, Composites). Top performers vérifiés alignés (#1630) : Long-Short Harvest (Sharpe **1.64**, PSR 98.7%), TrendWeather Composite (**0.948**, PSR 56.6%), EMATrend (**0.611**).

3. **[Patterns confirmes](../../docs/qc/quantconnect.md)** — 20 patterns valides sur 30+ iterations (risk-adjusted momentum, skip-month, stop-loss -8/-12%, monthly rebalancing, anti-overfitting) et 10 anti-patterns critiques (SPY Parking, backtests courts, yfinance != QC cloud).

4. **[Notebooks pedagogiques](Python/)** — 51 notebooks en 8 phases progressives : fondations LEAN, universe/asset classes, risk management, Algorithm Framework, donnees alternatives, ML (RF/XGBoost), deep learning (LSTM/Transformers), RL et LLMs pour trading.

5. **[Mapping livre Jared Broad](BOOK_MAPPING.md)** — 63 exemples du livre *Hands-On AI Trading* (2025) mappes a nos notebooks et projets. 22 strategies ML du Chapitre 6 importees.

## Demarrer en 5 minutes

1. Creer un compte gratuit sur [quantconnect.com](https://www.quantconnect.com/signup)
2. Copier un `main.py` depuis [projects/](projects/) dans un nouveau projet QC Lab
3. Cliquer **Backtest** — c'est tout

> Documentation complete : [README.md](README.md) | [Guide demarrage](GETTING-STARTED.md) | [Patterns QC](../../docs/qc/quantconnect.md)
