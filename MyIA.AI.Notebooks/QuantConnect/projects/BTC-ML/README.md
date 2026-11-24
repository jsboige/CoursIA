# BTC-ML

**Asset class:** Crypto (BTC)
**Cloud project ID:** 29318876 (deployed on QC Cloud)

## Description

Machine learning strategy on Bitcoin using sklearn `RandomForestClassifier` over
trend/momentum features (SMA, RSI, EMA 10/20/50/200, ADX, ATR, annualized
volatility) with strict walk-forward feature construction, periodic retraining
(60-day interval, 2-year lookback), probabilistic position sizing, volatility
filter, and risk management (stop-loss -8%, take-profit +15%). Strict train/OOS
split: training 2017-2020, out-of-sample backtest 2021-2026 (no overlap).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BTC-ML"`
**QC Cloud:** Deployed (project 29318876). Verified via backtest po2026-verify-btc-ml-oos-2021-2026 (2026-07-15): BuildSuccess, 0 compile errors.

## Backtest Metrics

> Ce tableau mesure le code d'origine, que `gate=legacy` et `features=legacy` reproduisent. Les deux défauts corrigés par #23504 et la mesure du code corrigé sont dans la section « Correction (#23504) » ci-dessous.

Verified out-of-sample backtest (2021-01-01 to 2026-03-01, Binance cash, USDT):

| Metric | Value |
|--------|-------|
| Method | RandomForestClassifier (n=50, depth=4, leaf=10) |
| Universe | BTCUSDT (Binance, daily) |
| Rebalance | Daily |
| Sharpe ratio | 0.057 |
| Probabilistic Sharpe | 1.520% |
| Compounding annual return | 3.692% |
| Max drawdown | 15.400% |
| Total net profit | +20.612% (USDT 20,612 on 100k) |
| Total orders | 13 |
| Tradeable days | 1886 |

The low Sharpe (0.057) and near-zero Probabilistic Sharpe (1.52%) indicate the
strategy's edge over this OOS window is statistically indistinguishable from
noise — i.e. **NO BEATS** vs buy-and-hold BTC over the same period. Honest
verdict: the strategy runs cleanly and is correctly structured (no compile
errors, no data leakage), but does not demonstrate alpha. Suitable as a
pedagogical reference for ML-strategy scaffolding, not as a live alpha source.

## Correction (#23504) : filtre de volatilité et features d'inférence

Le paragraphe anglais ci-dessus décrit le code d'origine comme correctement structuré. Il avait deux défauts, corrigés ici sans re-réglage : seuils, hyperparamètres de la forêt et ré-entraînement sont inchangés.

1. **Le filtre de volatilité suspendait les sorties.** Au-delà de 60 % de volatilité annualisée, `OnData` sortait par un `return` placé avant le stop-loss, la prise de bénéfice et la sortie du modèle. Pendant ce temps, une ligne détenue n'était plus surveillée. Avec `gate=entries` (défaut), le filtre ne bloque plus que les entrées et les renforcements.
2. **Le modèle n'était pas interrogé avec les features de son entraînement.** À l'entraînement, `_compute_features` calcule le vecteur, et sa colonne `adx` y est une moyenne du true range, en USDT. À l'inférence, le code prenait les indicateurs de Lean : `ADX(14)` borné à 100, RSI de Wilder, ATR, volatilité tirée de l'ATR. Avec `features=train` (défaut), l'inférence appelle `_compute_features` sur les 730 dernières barres journalières, soit la profondeur d'historique du ré-entraînement.

Paramètres :
- `gate` : `entries` ou `legacy` ;
- `features` : `train` ou `legacy` ;
- `mode` : `strategy`, ou `btc` (BTC acheté le premier jour et détenu) ;
- `start_date` et `end_date` : bornes de la fenêtre.

### Mesure

Le protocole a été écrit dans #23504 avant le premier backtest. Tous les backtests ont tourné sur QC Cloud avec le même code, et n'ont été lus qu'une fois `completed: true`.

Deux fenêtres :
- w1 va du 2021-01-01 au 2026-03-01. C'est la fenêtre publiée. Elle est indicative, car la fenêtre sur laquelle les seuils ont été réglés n'est écrite nulle part.
- w2 va du 2026-03-01 au 2026-10-01. Elle est postérieure à tout ce qui a été publié, et c'est elle qui tranche.

Le Sharpe à taux nul est annualisé par √252 et calculé par `Paradox46Benchmarks/significance.py` ; c'est le seul que lit la règle de verdict.

| Fenêtre | Bras | Sharpe QC | Sharpe à taux nul | CAGR | Drawdown max | Ordres |
|---|---|---|---|---|---|---|
| w1 | `legacy` (code d'origine) | 0.085 | 0.31 | 3.69 % | 15.4 % | 13 |
| w1 | `gate` (filtre corrigé) | -0.148 | 0.23 | 1.90 % | 17.1 % | 17 |
| w1 | `full` (filtre et features corrigés) | -0.390 | 0.02 | -0.16 % | 18.3 % | 26 |
| w1 | BTC détenu | 0.615 | 0.46 | 17.61 % | 75.8 % | 1 |
| w2 | `legacy` | 0 | non défini (aucune position) | 0 % | 0 % | 0 |
| w2 | `gate` | 0 | non défini (aucune position) | 0 % | 0 % | 0 |
| w2 | `full` | 0.557 | 0.82 | 8.37 % | 4.1 % | 1 |
| w2 | BTC détenu | 1.535 | 1.07 | 51.22 % | 28.1 % | 1 |

**Contrôle.** Sur w1, `legacy` redonne le backtest publié : même capital final au centime, mêmes 13 ordres, même CAGR et même drawdown. Seul le Sharpe de QC diffère (0.085 contre 0.057). QC retire un taux sans risque, et cet écart lui est attribué sans vérification séparée.

**Prédictions écrites avant la mesure.**
- **P1, confirmée.** Sur w1, `legacy` compte 43 clôtures au-delà du stop ou de la prise de bénéfice qui n'ont pas déclenché de sortie. Toutes tombent un jour où le filtre était actif avec une ligne détenue. Le filtre est actif 1095 jours sur 1886, dont 145 avec une ligne détenue.
- **P2, confirmée.** Avec `features=legacy`, la colonne `adx` d'inférence est, chaque jour de prédiction, sous le minimum de cette colonne au dernier entraînement, soit 1807 USDT : 791 jours sur 791 pour `legacy`, 1886 sur 1886 pour `gate`. Avec `features=train`, c'est le cas 124 jours sur 1886.
- **Sans direction prédite.** Sur w1, `full` passe 26 ordres contre 13. Son rendement journalier est non nul 1414 jours, contre 940 pour `legacy`.

### Verdict

- **w2 : NO BEATS.** Le Sharpe à taux nul de `full` est de 0.82, contre 1.07 pour BTC détenu (Ledoit-Wolf : p = 0.83 ; bootstrap stationnaire : p = 0.91). La lecture par le Sharpe de QC donne le même sens. En sept mois, `full` n'a ouvert qu'une position, encore détenue à la fin de la fenêtre. `legacy` et `gate` n'ont rien ouvert.
- **w1, à titre indicatif : NO BEATS.** 0.02 contre 0.46 (Ledoit-Wolf : p = 0.35 ; bootstrap : p = 0.42).
- **Diagnostic sur w1.** Chaque correction fait baisser le Sharpe à taux nul : 0.31, puis 0.23, puis 0.02. Aucun écart n'est significatif (p de Holm ≥ 0.79 sur les deux comparaisons à `legacy`).

**Lecture.** Les deux corrections rendent le code conforme à ce qu'il annonce, sans lui donner d'avantage. Le constat publié, NO BEATS contre BTC détenu, reste valable.

Hors périmètre, signalé dans #23504 : plusieurs colonnes sont des niveaux de prix (SMA, EMA). Elles ne sont pas stationnaires : un arbre entraîné sur des prix passés reçoit, à l'inférence, des prix hors de sa plage.

## Files

- main.py - Strategy (`MyEnhancedCryptoMlAlgorithm`)
- research.ipynb - Notebook de recherche (moteur simplifié, Sharpe 0.166) — le verdict faisant foi est le backtest QC Cloud du tableau ci-dessus (Sharpe 0.057)
- quantbook.ipynb - QuantBook exploration
