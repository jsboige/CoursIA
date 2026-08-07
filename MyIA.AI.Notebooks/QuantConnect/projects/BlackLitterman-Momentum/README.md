# BlackLitterman-Momentum

**Classe d'actifs :** Actions/ETF US (multi-actifs)
**ID projet Cloud :** 29816300

## Description

Portefeuille Black-Litterman avec vues de momentum multi-fenêtres (1M, 3M, 6M, 12M). L'optimisation BL produit les poids finaux.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BlackLitterman-Momentum"`

**QC Cloud :** Déployé en tant que projet 29816300.

## Métriques du backtest

Backtest QC Cloud (2026-08-07), période 2015-01-01 → 2026-01-01 (11 ans),
brokerage Interactive Brokers (frais réalistes), benchmark SPY,
2766 dates négociables, 2381 ordres.

| Métrique | Valeur |
|----------|--------|
| Ratio de Sharpe | 0.512 |
| CAGR | 9.982% |
| Drawdown max | 16.100% |
| PSR (Probabilistic Sharpe Ratio) | 1.989% |
| Profit net total | 184.986 % (180 804 $) |
| Rebalancement | Mensuel |

## Verdict : NO-BEATS (profil défensif, pas d'alpha)

La stratégie **ne bat pas le buy-hold SPY** sur la période : CAGR ~10 % légèrement
inférieur au SPY (≈ 11-12 % sur 2015-2026), Sharpe 0.512 en dessous du SPY, et
PSR ≈ 2 % statistiquement **non distinguable du bruit** (un PSR < 10 % signifie
que la performance observée n'est pas fiablement distinguishable d'un Sharpe
nul). Au-delà du benchmark, le PSR bas suffit à invalider tout claim d'alpha.

En revanche, le **drawdown max (16,1 %) est nettement inférieur** aux pires
drawdowns du SPY sur la même période (COVID 2020 ≈ 34 %, bear market 2022 ≈
25 %) — soit environ la moitié. La stratégie délivre donc un **profil de risque
défensif** (réduction de la profondeur des drawdowns) au prix d'une modeste
perte de rendement. Ce comportement est **cohérent avec le design** :
contrainte sectorielle (30 % max par secteur), volatilité cible (15 %) et
covariance régularisée Ledoit-Wolf amortissent structurellement l'amplitude
des mouvements, dans les deux sens.

**Lecture honnête.** Le moteur Black-Litterman — combinaison de l'équilibre de
marché (rendements implicites CAPM) et de vues momentum multi-fenêtres (1M/3M/6M/12M)
avec calibration He & Litterman de l'incertitude — ne génère pas d'alpha au-delà
de l'exposition actions US large-caps. Il offre une **diversification disciplinée**
(5 secteurs, 15 lignes, poids bornés 1-20 %) plutôt qu'un edge prédictif. Pas de
re-tuning des paramètres (TAU, SIGMOID_STEEPNESS, TARGET_VOL) : ajuster
rétrospectivement serait du surapprentissage (EPIC #9768). Le main.py est livré
tel quel, le verdict porte sur la stratégie en l'état.

## Fichiers

- main.py - Stratégie (v1.0, BL momentum)

## Références

- Black & Litterman (1992), Global Portfolio Optimization
