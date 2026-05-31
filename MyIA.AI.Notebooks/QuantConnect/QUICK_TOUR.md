# QuantConnect AI Trading - Quick Tour

**95+ strategies backtested | 51 notebooks Python | 20 patterns confirmes | Framework composite Sharpe 1.16**

Cette section contient un parcours complet de trading algorithmique sur **QuantConnect LEAN**, du debutant au deploiement live. Tout est executable gratuitement sur le cloud QC.

## 5 arrets pour comprendre notre travail

1. **[Meilleure strategie](projects/Framework_Composite_TrendWeather/)** — Composite TrendStocks + AllWeather (Sharpe 1.156, CAGR 27.4%). Architecture Algorithm Framework modulaire : AlphaModel + PortfolioConstruction + Execution.

2. **[Catalogue strategies](docs/qc_strategies_catalog.md)** — 95+ projets organises par categorie (Alpha, Trend Following, ML/RL, Composites). Top performers : Long-Short Harvest (Sharpe 1.505), EMA-Cross-Alpha (0.996), TrendWeather Composite (1.156).

3. **[Patterns confirmes](../../docs/quantconnect.md)** — 20 patterns valides sur 30+ iterations (risk-adjusted momentum, skip-month, stop-loss -8/-12%, monthly rebalancing, anti-overfitting) et 10 anti-patterns critiques (SPY Parking, backtests courts, yfinance != QC cloud).

4. **[Notebooks pedagogiques](Python/)** — 51 notebooks en 8 phases progressives : fondations LEAN, universe/asset classes, risk management, Algorithm Framework, donnees alternatives, ML (RF/XGBoost), deep learning (LSTM/Transformers), RL et LLMs pour trading.

5. **[Mapping livre Jared Broad](BOOK_MAPPING.md)** — 63 exemples du livre *Hands-On AI Trading* (2025) mappes a nos notebooks et projets. 22 strategies ML du Chapitre 6 importees.

## Demarrer en 5 minutes

1. Creer un compte gratuit sur [quantconnect.com](https://www.quantconnect.com/signup)
2. Copier un `main.py` depuis [projects/](projects/) dans un nouveau projet QC Lab
3. Cliquer **Backtest** — c'est tout

> Documentation complete : [README.md](README.md) | [Guide demarrage](GETTING-STARTED.md) | [Patterns QC](../../docs/quantconnect.md)
