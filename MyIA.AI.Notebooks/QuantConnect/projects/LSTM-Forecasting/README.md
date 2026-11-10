# LSTM-Forecasting

**Classe d'actifs :** sept ETF américains (actions, obligations, or)
**Référence :** *Hands-On AI Trading*, chapitre 6, exemple 7

## Description

Malgré son nom, le projet n'utilise pas de LSTM. Chaque ETF a son propre perceptron multicouche (`MLPClassifier` de scikit-learn, couches cachées de 64 et 32 neurones, activation ReLU), précédé d'une standardisation (`StandardScaler`) dans un `Pipeline`. Le modèle estime la probabilité que le rendement de la séance suivante soit positif. Ses entrées sont des variables construites sur les rendements passés, qui jouent le rôle de la mémoire de séquence d'un LSTM.

## Règles de décision

- **Univers :** SPY, QQQ, IWM, EFA, TLT, GLD, IEF, en données journalières.
- **Rendements :** indicateur ROC sur une séance par ETF, amorcé au démarrage sur 342 jours calendaires d'historique (252 + 60 + 30).
- **Variables (18 par ETF) :** rendements décalés de 1, 2, 3, 5, 10 et 20 séances ; volatilités sur 5, 10 et 20 séances ; un indicateur de type RSI sur 14 séances, ramené entre 0 et 1 ; momentums cumulés sur 5, 10 et 20 séances ; autocorrélations aux décalages 1, 2 et 5 ; rendements moyens sur 5 et 10 séances.
- **Étiquette :** 1 si le rendement de la séance suivante est positif, 0 sinon.
- **Entraînement :** au premier rééquilibrage de chaque mois, un modèle par ETF sur les 252 derniers rendements (`random_state=42`, arrêt précoce sur 15 % de validation, 300 itérations au plus). Un ETF dont l'échantillon ne contient qu'une seule classe n'est pas entraîné.
- **Rééquilibrage :** chaque lundi, 30 minutes après l'ouverture.
- **Sélection :** les ETF dont la probabilité de hausse atteint 0,52, quatre au plus. Si moins de deux passent le seuil, la sélection est complétée par les mieux classés jusqu'à deux. Poids égaux ; les ETF non retenus sont vendus.
- **Graphique :** la série « MLP P(up) » trace la probabilité de chaque ETF à chaque rééquilibrage.

## Lancer

- **QC Cloud :** créer un projet Python, y copier `main.py`, compiler puis lancer un backtest. Le code ne prend aucun paramètre.
- **Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/LSTM-Forecasting"` (données locales des sept ETF requises).

## Résultats mesurés

QC Cloud, le 2026-11-05, dans l'espace ESGF_School. Fenêtre codée 2015-01-01 → 2026-01-01, capital de départ de 100 000, modèle de courtage et compte sur marge tels que codés (`set_brokerage_model`). Le code est déterministe (`random_state=42`). Le témoin détient SPY à 100 % sur la même fenêtre, avec les mêmes réglages.

| | Stratégie | SPY détenu |
|---|---|---|
| Projet QC | 38971336 | 38971340 |
| Backtest | `4bc59cadd7b457e4bd290a06629e9b08` | `d0b256afefb66651f1b5a26a943bca30` |
| Sharpe (QC, avec taux sans risque) | 0,565 | 0,537 |
| CAGR | 11,6 % | 13,4 % |
| Drawdown max | 29,9 % | 33,5 % |
| PSR (QC) | 3,2 % | 2,5 % |
| Ordres | 2110 | 1 |
| Volatilité annualisée (trace) | 11,9 % | 15,7 % |

La volatilité et le bêta sont calculés sur la trace « Strategy Equity » des backtests, en jours ouvrés : bêta de la stratégie contre SPY 0,50, corrélation 0,66. Les frais cumulés représentent 4,2 % du capital de départ.

**Verdict : NO BEATS contre SPY détenu.** La stratégie rapporte moins que SPY (1,8 point de CAGR en moins) avec un risque plus faible (volatilité, drawdown, bêta 0,50). Son avantage de Sharpe (+0,028) est mesuré sur un seul chemin, sans test de significativité : il ne suffit pas à conclure.

## Historique des mesures

- **v2.1 :** la docstring annonçait Sharpe 0,525, CAGR 11,3 % et drawdown 32,5 %, sans fenêtre ni mode de mesure.
- **2026-06-16 (#3135) :** mesure QC Cloud du même code (projet 29443476), Sharpe 0,525 et PSR 13,4 %.
- **2026-11-05 :** mesure ci-dessus. Le fichier `main.py` est identique à celui de juin, hors docstring. L'écart avec la mesure de juin n'est pas expliqué ; une cause possible, non mesurée ici, est la réécriture des prix ajustés par QC entre deux exécutions.

## Fichiers

- `main.py` : la stratégie (v2.1).
- `research.ipynb` : carnet exploratoire (Ex07) : parcours pédagogique du LSTM (portes, propagation avant manuelle, backtest simple sur données téléchargées).
