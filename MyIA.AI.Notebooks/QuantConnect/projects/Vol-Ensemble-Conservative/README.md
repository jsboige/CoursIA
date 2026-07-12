# Vol-Ensemble-Conservative

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**Cloud project ID :** `33248352` (voir `config.json`, local-id : `209093652`)

## Description

Ensemble conservateur de prévision de volatilité combinant les modèles GARCH(1,1) et HAR-RV sur six actifs (SPY, EFA, EEM, TLT, GLD, DBC). Utilise le maximum des deux prévisions de volatilité (approche conservatrice). Cible 8 % de volatilité annualisée (la moitié de la cible normale de 16 %). Applique un filtre de régime SMA200 avec réduction de position de 50 % en marché baissier, et une SMA50 pour la direction des trades. Rebalance hebdomadaire. La plus conservatrice des trois stratégies de volatilité.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Vol-Ensemble-Conservative/main.py
```

### QC Cloud
Ouvrir le projet cloud (project-id : `33248352`), compiler et lancer un backtest.

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Ensemble GARCH+HAR (max conservateur) | Hebdomadaire | Vol target 8 %, régime SMA200 (-50 % baissier), direction SMA50, fenêtre 500 jours |

### Baseline alignée (2018-2025)

Exécution dorsale standardisée #1630 (projet QC Cloud `33248352`, backtest `db77ae49`).

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.265 |
| CAGR | 6.142 % |
| Max Drawdown | 10.40 % |
| Probabilistic Sharpe Ratio | 13.6 % |
| Dates négociables | 1761 |

Interprétation : MaxDD 10.40 % = baseline dorsale la plus serrée à ce jour (bat Vol-GARCH-Target 10.80 %, GlobalMacro-Regime 22.8 %, HAR-RV-J-Kelly 37.1 %). Sharpe positif 0.265 mais inférieur au GARCH seul Vol-GARCH-Target (0.325) : l'overlay conservateur (prévision max-de-l'ensemble HAR+GARCH, demi vol-target 8 %, régime SMA200 -50 % baissier, direction SMA50) a serré le drawdown au prix du rendement, et la composante HAR n'a pas apporté de valeur ajustée du risque au-delà du GARCH seul. Promue Tier 4 -> 2 (Historique). totalOrders = 0 = artefact d'extraction du wrapper (CAGR 6.14 % implique des trades réels).

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Vol-targeting d'ensemble conservateur (max de GARCH + HAR) avec filtre de régime |
| `config.json` | Configuration du projet (local-id) |
| `research.ipynb` | Notebook de recherche avec comparaison des modèles d'ensemble et analyse des paramètres conservateurs |

## Références

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
